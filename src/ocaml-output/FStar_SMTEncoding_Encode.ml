
open Prims
let add_fuel = (fun x tl -> if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
tl
end else begin
(x)::tl
end)

let withenv = (fun c _101_28 -> (match (_101_28) with
| (a, b) -> begin
(a, b, c)
end))

let vargs = (fun args -> (FStar_List.filter (fun _101_1 -> (match (_101_1) with
| (FStar_Util.Inl (_101_32), _101_35) -> begin
false
end
| _101_38 -> begin
true
end)) args))

let subst_lcomp_opt : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.lcomp Prims.option  ->  FStar_Syntax_Syntax.lcomp Prims.option = (fun s l -> (match (l) with
| None -> begin
None
end
| Some (l) -> begin
(let _204_13 = (let _204_12 = (let _204_11 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp s _204_11))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _204_12))
in Some (_204_13))
end))

let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s '\'' '_'))

let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun lid a -> (let a = (let _101_47 = a
in (let _204_20 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _204_20; FStar_Syntax_Syntax.index = _101_47.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _101_47.FStar_Syntax_Syntax.sort}))
in (let _204_21 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str a.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (FStar_All.pipe_left escape _204_21))))

let primitive_projector_by_pos : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (let fail = (fun _101_54 -> (match (()) with
| () -> begin
(let _204_31 = (let _204_30 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" _204_30 lid.FStar_Ident.str))
in (FStar_All.failwith _204_31))
end))
in (let _101_58 = (FStar_TypeChecker_Env.lookup_datacon env lid)
in (match (_101_58) with
| (_101_56, t) -> begin
(match ((let _204_32 = (FStar_Syntax_Subst.compress t)
in _204_32.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _101_66 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_101_66) with
| (binders, _101_65) -> begin
if ((i < 0) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(let b = (FStar_List.nth binders i)
in (mk_term_projector_name lid (Prims.fst b)))
end
end))
end
| _101_69 -> begin
(fail ())
end)
end))))

let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (let _204_38 = (let _204_37 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str _204_37))
in (FStar_All.pipe_left escape _204_38)))

let mk_term_projector : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun lid a -> (let _204_44 = (let _204_43 = (mk_term_projector_name lid a)
in (_204_43, FStar_SMTEncoding_Term.Arrow ((FStar_SMTEncoding_Term.Term_sort, FStar_SMTEncoding_Term.Term_sort))))
in (FStar_SMTEncoding_Term.mkFreeV _204_44)))

let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_SMTEncoding_Term.term = (fun lid i -> (let _204_50 = (let _204_49 = (mk_term_projector_name_by_pos lid i)
in (_204_49, FStar_SMTEncoding_Term.Arrow ((FStar_SMTEncoding_Term.Term_sort, FStar_SMTEncoding_Term.Term_sort))))
in (FStar_SMTEncoding_Term.mkFreeV _204_50)))

let mk_data_tester = (fun env l x -> (FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x))

type varops_t =
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; mark : Prims.unit  ->  Prims.unit; reset_mark : Prims.unit  ->  Prims.unit; commit_mark : Prims.unit  ->  Prims.unit; new_var : FStar_Ident.ident  ->  Prims.int  ->  Prims.string; new_fvar : FStar_Ident.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_SMTEncoding_Term.term; next_id : Prims.unit  ->  Prims.int}

let is_Mkvarops_t : varops_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkvarops_t"))))

let varops : varops_t = (let initial_ctr = 10
in (let ctr = (FStar_Util.mk_ref initial_ctr)
in (let new_scope = (fun _101_93 -> (match (()) with
| () -> begin
(let _204_154 = (FStar_Util.smap_create 100)
in (let _204_153 = (FStar_Util.smap_create 100)
in (_204_154, _204_153)))
end))
in (let scopes = (let _204_156 = (let _204_155 = (new_scope ())
in (_204_155)::[])
in (FStar_Util.mk_ref _204_156))
in (let mk_unique = (fun y -> (let y = (escape y)
in (let y = (match ((let _204_160 = (FStar_ST.read scopes)
in (FStar_Util.find_map _204_160 (fun _101_101 -> (match (_101_101) with
| (names, _101_100) -> begin
(FStar_Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_101_104) -> begin
(let _101_106 = (FStar_Util.incr ctr)
in (let _204_162 = (let _204_161 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _204_161))
in (Prims.strcat (Prims.strcat y "__") _204_162)))
end)
in (let top_scope = (let _204_164 = (let _204_163 = (FStar_ST.read scopes)
in (FStar_List.hd _204_163))
in (FStar_All.pipe_left Prims.fst _204_164))
in (let _101_110 = (FStar_Util.smap_add top_scope y true)
in y)))))
in (let new_var = (fun pp rn -> (let _204_171 = (let _204_169 = (FStar_All.pipe_left mk_unique pp.FStar_Ident.idText)
in (Prims.strcat _204_169 "__"))
in (let _204_170 = (FStar_Util.string_of_int rn)
in (Prims.strcat _204_171 _204_170))))
in (let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (let next_id = (fun _101_118 -> (match (()) with
| () -> begin
(let _101_119 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end))
in (let fresh = (fun pfx -> (let _204_179 = (let _204_178 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _204_178))
in (FStar_Util.format2 "%s_%s" pfx _204_179)))
in (let string_const = (fun s -> (match ((let _204_183 = (FStar_ST.read scopes)
in (FStar_Util.find_map _204_183 (fun _101_128 -> (match (_101_128) with
| (_101_126, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))) with
| Some (f) -> begin
f
end
| None -> begin
(let id = (next_id ())
in (let f = (let _204_184 = (FStar_SMTEncoding_Term.mk_String_const id)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString _204_184))
in (let top_scope = (let _204_186 = (let _204_185 = (FStar_ST.read scopes)
in (FStar_List.hd _204_185))
in (FStar_All.pipe_left Prims.snd _204_186))
in (let _101_135 = (FStar_Util.smap_add top_scope s f)
in f))))
end))
in (let push = (fun _101_138 -> (match (()) with
| () -> begin
(let _204_191 = (let _204_190 = (new_scope ())
in (let _204_189 = (FStar_ST.read scopes)
in (_204_190)::_204_189))
in (FStar_ST.op_Colon_Equals scopes _204_191))
end))
in (let pop = (fun _101_140 -> (match (()) with
| () -> begin
(let _204_195 = (let _204_194 = (FStar_ST.read scopes)
in (FStar_List.tl _204_194))
in (FStar_ST.op_Colon_Equals scopes _204_195))
end))
in (let mark = (fun _101_142 -> (match (()) with
| () -> begin
(push ())
end))
in (let reset_mark = (fun _101_144 -> (match (()) with
| () -> begin
(pop ())
end))
in (let commit_mark = (fun _101_146 -> (match (()) with
| () -> begin
(match ((FStar_ST.read scopes)) with
| (hd1, hd2)::(next1, next2)::tl -> begin
(let _101_159 = (FStar_Util.smap_fold hd1 (fun key value v -> (FStar_Util.smap_add next1 key value)) ())
in (let _101_164 = (FStar_Util.smap_fold hd2 (fun key value v -> (FStar_Util.smap_add next2 key value)) ())
in (FStar_ST.op_Colon_Equals scopes (((next1, next2))::tl))))
end
| _101_167 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id})))))))))))))))

let unmangle : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv = (fun x -> (let _101_169 = x
in (let _204_210 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _204_210; FStar_Syntax_Syntax.index = _101_169.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _101_169.FStar_Syntax_Syntax.sort})))

type binding =
| Binding_var of (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term)
| Binding_fvar of (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option)

let is_Binding_var : binding  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Binding_var (_) -> begin
true
end
| _ -> begin
false
end))

let is_Binding_fvar : binding  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Binding_fvar (_) -> begin
true
end
| _ -> begin
false
end))

let ___Binding_var____0 : binding  ->  (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) = (fun projectee -> (match (projectee) with
| Binding_var (_101_173) -> begin
_101_173
end))

let ___Binding_fvar____0 : binding  ->  (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun projectee -> (match (projectee) with
| Binding_fvar (_101_176) -> begin
_101_176
end))

let binder_of_eithervar = (fun v -> (v, None))

type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_TypeChecker_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_SMTEncoding_Term.sort Prims.list * FStar_SMTEncoding_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}

let is_Mkenv_t : env_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_t"))))

let print_env : env_t  ->  Prims.string = (fun e -> (let _204_268 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun _101_2 -> (match (_101_2) with
| Binding_var (x, _101_191) -> begin
(FStar_Syntax_Print.bv_to_string x)
end
| Binding_fvar (l, _101_196, _101_198, _101_200) -> begin
(FStar_Syntax_Print.lid_to_string l)
end))))
in (FStar_All.pipe_right _204_268 (FStar_String.concat ", "))))

let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))

let caption_t : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.string Prims.option = (fun env t -> if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _204_278 = (FStar_Syntax_Print.term_to_string t)
in Some (_204_278))
end else begin
None
end)

let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (let xsym = (varops.fresh x)
in (let _204_283 = (FStar_SMTEncoding_Term.mkFreeV (xsym, s))
in (xsym, _204_283))))

let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (let ysym = (let _204_288 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _204_288))
in (let y = (FStar_SMTEncoding_Term.mkFreeV (ysym, FStar_SMTEncoding_Term.Term_sort))
in (ysym, y, (let _101_214 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _101_214.tcenv; warn = _101_214.warn; cache = _101_214.cache; nolabels = _101_214.nolabels; use_zfuel_name = _101_214.use_zfuel_name; encode_non_total_function_typ = _101_214.encode_non_total_function_typ})))))

let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (let y = (FStar_SMTEncoding_Term.mkApp (ysym, []))
in (ysym, y, (let _101_220 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = _101_220.depth; tcenv = _101_220.tcenv; warn = _101_220.warn; cache = _101_220.cache; nolabels = _101_220.nolabels; use_zfuel_name = _101_220.use_zfuel_name; encode_non_total_function_typ = _101_220.encode_non_total_function_typ})))))

let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (let _101_225 = env
in {bindings = (Binding_var ((x, t)))::env.bindings; depth = _101_225.depth; tcenv = _101_225.tcenv; warn = _101_225.warn; cache = _101_225.cache; nolabels = _101_225.nolabels; use_zfuel_name = _101_225.use_zfuel_name; encode_non_total_function_typ = _101_225.encode_non_total_function_typ}))

let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (match ((lookup_binding env (fun _101_3 -> (match (_101_3) with
| Binding_var (b, t) when (FStar_Syntax_Syntax.bv_eq b a) -> begin
Some ((b, t))
end
| _101_235 -> begin
None
end)))) with
| None -> begin
(let _204_305 = (let _204_304 = (FStar_Syntax_Print.bv_to_string a)
in (FStar_Util.format1 "Bound term variable not found: %s" _204_304))
in (FStar_All.failwith _204_305))
end
| Some (b, t) -> begin
t
end))

let new_term_constant_and_tok_from_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * Prims.string * env_t) = (fun env x -> (let fname = (varops.new_fvar x)
in (let ftok = (Prims.strcat fname "@tok")
in (let _204_316 = (let _101_245 = env
in (let _204_315 = (let _204_314 = (let _204_313 = (let _204_312 = (let _204_311 = (FStar_SMTEncoding_Term.mkApp (ftok, []))
in (FStar_All.pipe_left (fun _204_310 -> Some (_204_310)) _204_311))
in (x, fname, _204_312, None))
in Binding_fvar (_204_313))
in (_204_314)::env.bindings)
in {bindings = _204_315; depth = _101_245.depth; tcenv = _101_245.tcenv; warn = _101_245.warn; cache = _101_245.cache; nolabels = _101_245.nolabels; use_zfuel_name = _101_245.use_zfuel_name; encode_non_total_function_typ = _101_245.encode_non_total_function_typ}))
in (fname, ftok, _204_316)))))

let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun _101_4 -> (match (_101_4) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some ((t1, t2, t3))
end
| _101_257 -> begin
None
end))))

let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _204_327 = (let _204_326 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" _204_326))
in (FStar_All.failwith _204_327))
end
| Some (s) -> begin
s
end))

let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (let _101_267 = env
in {bindings = (Binding_fvar ((x, fname, ftok, None)))::env.bindings; depth = _101_267.depth; tcenv = _101_267.tcenv; warn = _101_267.warn; cache = _101_267.cache; nolabels = _101_267.nolabels; use_zfuel_name = _101_267.use_zfuel_name; encode_non_total_function_typ = _101_267.encode_non_total_function_typ}))

let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (let _101_276 = (lookup_lid env x)
in (match (_101_276) with
| (t1, t2, _101_275) -> begin
(let t3 = (let _204_344 = (let _204_343 = (let _204_342 = (FStar_SMTEncoding_Term.mkApp ("ZFuel", []))
in (_204_342)::[])
in (f, _204_343))
in (FStar_SMTEncoding_Term.mkApp _204_344))
in (let _101_278 = env
in {bindings = (Binding_fvar ((x, t1, t2, Some (t3))))::env.bindings; depth = _101_278.depth; tcenv = _101_278.tcenv; warn = _101_278.warn; cache = _101_278.cache; nolabels = _101_278.nolabels; use_zfuel_name = _101_278.use_zfuel_name; encode_non_total_function_typ = _101_278.encode_non_total_function_typ}))
end)))

let try_lookup_free_var : env_t  ->  FStar_Ident.lident  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env l -> (match ((try_lookup_lid env l)) with
| None -> begin
None
end
| Some (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some (f) when env.use_zfuel_name -> begin
Some (f)
end
| _101_291 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (_101_295, fuel::[]) -> begin
if (let _204_350 = (let _204_349 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right _204_349 Prims.fst))
in (FStar_Util.starts_with _204_350 "fuel")) then begin
(let _204_353 = (let _204_352 = (FStar_SMTEncoding_Term.mkFreeV (name, FStar_SMTEncoding_Term.Term_sort))
in (FStar_SMTEncoding_Term.mk_ApplyTF _204_352 fuel))
in (FStar_All.pipe_left (fun _204_351 -> Some (_204_351)) _204_353))
end else begin
Some (t)
end
end
| _101_301 -> begin
Some (t)
end)
end
| _101_303 -> begin
None
end)
end)
end))

let lookup_free_var = (fun env a -> (match ((try_lookup_free_var env a.FStar_Syntax_Syntax.v)) with
| Some (t) -> begin
t
end
| None -> begin
(let _204_357 = (let _204_356 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _204_356))
in (FStar_All.failwith _204_357))
end))

let lookup_free_var_name = (fun env a -> (let _101_316 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_101_316) with
| (x, _101_313, _101_315) -> begin
x
end)))

let lookup_free_var_sym = (fun env a -> (let _101_322 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_101_322) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.hash = _101_326; FStar_SMTEncoding_Term.freevars = _101_324}) when env.use_zfuel_name -> begin
(g, zf)
end
| _101_334 -> begin
(match (sym) with
| None -> begin
(FStar_SMTEncoding_Term.Var (name), [])
end
| Some (sym) -> begin
(match (sym.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, fuel::[]) -> begin
(g, (fuel)::[])
end
| _101_344 -> begin
(FStar_SMTEncoding_Term.Var (name), [])
end)
end)
end)
end)))

let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun _101_5 -> (match (_101_5) with
| Binding_fvar (_101_349, nm', tok, _101_353) when (nm = nm') -> begin
tok
end
| _101_357 -> begin
None
end))))

let mkForall_fuel' = (fun n _101_362 -> (match (_101_362) with
| (pats, vars, body) -> begin
(let fallback = (fun _101_364 -> (match (()) with
| () -> begin
(FStar_SMTEncoding_Term.mkForall (pats, vars, body))
end))
in if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
(fallback ())
end else begin
(let _101_367 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_101_367) with
| (fsym, fterm) -> begin
(let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Term.mkApp ("HasTypeFuel", (fterm)::args))
end
| _101_377 -> begin
p
end)))))
in (let pats = (FStar_List.map add_fuel pats)
in (let body = (match (body.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, guard::body'::[]) -> begin
(let guard = (match (guard.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, guards) -> begin
(let _204_374 = (add_fuel guards)
in (FStar_SMTEncoding_Term.mk_and_l _204_374))
end
| _101_390 -> begin
(let _204_375 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _204_375 FStar_List.hd))
end)
in (FStar_SMTEncoding_Term.mkImp (guard, body')))
end
| _101_393 -> begin
body
end)
in (let vars = ((fsym, FStar_SMTEncoding_Term.Fuel_sort))::vars
in (FStar_SMTEncoding_Term.mkForall (pats, vars, body))))))
end))
end)
end))

let mkForall_fuel : (FStar_SMTEncoding_Term.pat Prims.list Prims.list * FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (mkForall_fuel' 1)

let head_normal : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (let t = (FStar_Syntax_Util.unmeta t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) -> begin
true
end
| (FStar_Syntax_Syntax.Tm_fvar (v, _)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (v, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(let _204_381 = (FStar_TypeChecker_Env.lookup_definition FStar_TypeChecker_Env.OnlyInline env.tcenv v.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _204_381 FStar_Option.isNone))
end
| _101_438 -> begin
false
end)))

let whnf : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> if (head_normal env t) then begin
t
end else begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
end)

let norm : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t))

let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (let _204_394 = (let _204_392 = (FStar_Syntax_Syntax.null_binder t)
in (_204_392)::[])
in (let _204_393 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.true_lid FStar_Range.dummyRange)
in (FStar_Syntax_Util.abs _204_394 _204_393 None))))

let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(let _204_401 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out _204_401))
end
| s -> begin
(let _101_450 = ()
in (let _204_402 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTT out _204_402)))
end)) e)))

let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Term.mk_ApplyTT e)))

let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun _101_6 -> (match (_101_6) with
| (FStar_SMTEncoding_Term.Var ("ApplyTT")) | (FStar_SMTEncoding_Term.Var ("ApplyTF")) -> begin
true
end
| _101_460 -> begin
false
end))

let is_eta : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env vars t -> (let rec aux = (fun t xs -> (match ((t.FStar_SMTEncoding_Term.tm, xs)) with
| (FStar_SMTEncoding_Term.App (app, f::{FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.hash = _101_471; FStar_SMTEncoding_Term.freevars = _101_469}::[]), x::xs) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), _101_489) -> begin
if (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v)
end
| _101_496 -> begin
false
end)) args vars)) then begin
(tok_of_name env f)
end else begin
None
end
end
| (_101_498, []) -> begin
(let fvs = (FStar_SMTEncoding_Term.free_variables t)
in if (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (not ((FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)))))) then begin
Some (t)
end else begin
None
end)
end
| _101_504 -> begin
None
end))
in (aux t (FStar_List.rev vars))))

type label =
(FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range)

type labels =
label Prims.list

type pattern =
{pat_vars : (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.fv) Prims.list; pat_term : Prims.unit  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t); guard : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term; projections : FStar_SMTEncoding_Term.term  ->  (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) Prims.list}

let is_Mkpattern : pattern  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkpattern"))))

exception Let_rec_unencodeable

let is_Let_rec_unencodeable : Prims.exn  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Let_rec_unencodeable -> begin
true
end
| _ -> begin
false
end))

let encode_const : FStar_Const.sconst  ->  FStar_SMTEncoding_Term.term = (fun _101_7 -> (match (_101_7) with
| FStar_Const.Const_unit -> begin
FStar_SMTEncoding_Term.mk_Term_unit
end
| FStar_Const.Const_bool (true) -> begin
(FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Term.mkTrue)
end
| FStar_Const.Const_bool (false) -> begin
(FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Term.mkFalse)
end
| FStar_Const.Const_char (c) -> begin
(let _204_456 = (FStar_SMTEncoding_Term.mkInteger' (FStar_Util.int_of_char c))
in (FStar_SMTEncoding_Term.boxInt _204_456))
end
| FStar_Const.Const_uint8 (i) -> begin
(let _204_457 = (FStar_SMTEncoding_Term.mkInteger' (FStar_Util.int_of_uint8 i))
in (FStar_SMTEncoding_Term.boxInt _204_457))
end
| FStar_Const.Const_int (i) -> begin
(let _204_458 = (FStar_SMTEncoding_Term.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt _204_458))
end
| FStar_Const.Const_int32 (i) -> begin
(let _204_462 = (let _204_461 = (let _204_460 = (let _204_459 = (FStar_SMTEncoding_Term.mkInteger32 i)
in (FStar_SMTEncoding_Term.boxInt _204_459))
in (_204_460)::[])
in ("FStar.Int32.Int32", _204_461))
in (FStar_SMTEncoding_Term.mkApp _204_462))
end
| FStar_Const.Const_string (bytes, _101_526) -> begin
(let _204_463 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _204_463))
end
| c -> begin
(let _204_465 = (let _204_464 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" _204_464))
in (FStar_All.failwith _204_465))
end))

let as_function_typ : env_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (let rec aux = (fun norm t -> (let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_101_537) -> begin
t
end
| FStar_Syntax_Syntax.Tm_refine (_101_540) -> begin
(let _204_474 = (FStar_Syntax_Util.unrefine t)
in (aux true _204_474))
end
| _101_543 -> begin
if norm then begin
(let _204_475 = (whnf env t)
in (aux false _204_475))
end else begin
(let _204_478 = (let _204_477 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (let _204_476 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _204_477 _204_476)))
in (FStar_All.failwith _204_478))
end
end)))
in (aux true t0)))

let rec encode_binders : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> (let _101_547 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _204_528 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" _204_528))
end else begin
()
end
in (let _101_575 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _101_554 b -> (match (_101_554) with
| (vars, guards, env, decls, names) -> begin
(let _101_569 = (let x = (unmangle (Prims.fst b))
in (let _101_560 = (gen_term_var env x)
in (match (_101_560) with
| (xxsym, xx, env') -> begin
(let _101_563 = (let _204_531 = (norm env x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt _204_531 env xx))
in (match (_101_563) with
| (guard_x_t, decls') -> begin
((xxsym, FStar_SMTEncoding_Term.Term_sort), guard_x_t, env', decls', x)
end))
end)))
in (match (_101_569) with
| (v, g, env, decls', n) -> begin
((v)::vars, (g)::guards, env, (FStar_List.append decls decls'), (n)::names)
end))
end)) ([], [], env, [], [])))
in (match (_101_575) with
| (vars, guards, env, decls, names) -> begin
((FStar_List.rev vars), (FStar_List.rev guards), env, decls, (FStar_List.rev names))
end))))
and encode_term_pred : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (let _101_582 = (encode_term t env)
in (match (_101_582) with
| (t, decls) -> begin
(let _204_536 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t)
in (_204_536, decls))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (let _101_589 = (encode_term t env)
in (match (_101_589) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _204_541 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t)
in (_204_541, decls))
end
| Some (f) -> begin
(let _204_542 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t)
in (_204_542, decls))
end)
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (let t0 = (FStar_Syntax_Subst.compress t)
in (let _101_596 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _204_547 = (FStar_Syntax_Print.tag_of_term t)
in (let _204_546 = (FStar_Syntax_Print.tag_of_term t0)
in (let _204_545 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" _204_547 _204_546 _204_545))))
end else begin
()
end
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _204_552 = (let _204_551 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (let _204_550 = (FStar_Syntax_Print.tag_of_term t0)
in (let _204_549 = (FStar_Syntax_Print.term_to_string t0)
in (let _204_548 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _204_551 _204_550 _204_549 _204_548)))))
in (FStar_All.failwith _204_552))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _204_554 = (let _204_553 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" _204_553))
in (FStar_All.failwith _204_554))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, k, _101_607) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_meta (t, _101_612) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(let t = (lookup_term_var env x)
in (t, []))
end
| FStar_Syntax_Syntax.Tm_fvar (v, _101_620) -> begin
(let _204_555 = (lookup_free_var env v)
in (_204_555, []))
end
| FStar_Syntax_Syntax.Tm_type (_101_624) -> begin
(FStar_SMTEncoding_Term.mk_Term_type, [])
end
| FStar_Syntax_Syntax.Tm_uinst (t, _101_628) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(let _204_556 = (encode_const c)
in (_204_556, []))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(let _101_639 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_101_639) with
| (binders, res) -> begin
if ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res)) then begin
(let _101_646 = (encode_binders None binders env)
in (match (_101_646) with
| (vars, guards, env', decls, _101_645) -> begin
(let fsym = (let _204_557 = (varops.fresh "f")
in (_204_557, FStar_SMTEncoding_Term.Term_sort))
in (let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (let app = (mk_Apply f vars)
in (let _101_652 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv res)
in (match (_101_652) with
| (pre_opt, res_t) -> begin
(let _101_655 = (encode_term_pred None res_t env' app)
in (match (_101_655) with
| (res_pred, decls') -> begin
(let _101_664 = (match (pre_opt) with
| None -> begin
(let _204_558 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_204_558, decls))
end
| Some (pre) -> begin
(let _101_661 = (encode_formula pre env')
in (match (_101_661) with
| (guard, decls0) -> begin
(let _204_559 = (FStar_SMTEncoding_Term.mk_and_l ((guard)::guards))
in (_204_559, (FStar_List.append decls decls0)))
end))
end)
in (match (_101_664) with
| (guards, guard_decls) -> begin
(let t_interp = (let _204_561 = (let _204_560 = (FStar_SMTEncoding_Term.mkImp (guards, res_pred))
in (((app)::[])::[], vars, _204_560))
in (FStar_SMTEncoding_Term.mkForall _204_561))
in (let cvars = (let _204_563 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right _204_563 (FStar_List.filter (fun _101_669 -> (match (_101_669) with
| (x, _101_668) -> begin
(x <> (Prims.fst fsym))
end)))))
in (let tkey = (FStar_SMTEncoding_Term.mkForall ([], (fsym)::cvars, t_interp))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t', sorts, _101_675) -> begin
(let _204_566 = (let _204_565 = (let _204_564 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in (t', _204_564))
in (FStar_SMTEncoding_Term.mkApp _204_565))
in (_204_566, []))
end
| None -> begin
(let tsym = (varops.fresh "Tm_arrow")
in (let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (let caption = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _204_567 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in Some (_204_567))
end else begin
None
end
in (let tdecl = FStar_SMTEncoding_Term.DeclFun ((tsym, cvar_sorts, FStar_SMTEncoding_Term.Term_sort, caption))
in (let t = (let _204_569 = (let _204_568 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (tsym, _204_568))
in (FStar_SMTEncoding_Term.mkApp _204_569))
in (let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (let k_assumption = (let _204_571 = (let _204_570 = (FStar_SMTEncoding_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (_204_570, Some ((Prims.strcat tsym " kinding"))))
in FStar_SMTEncoding_Term.Assume (_204_571))
in (let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t)
in (let pre_typing = (let _204_578 = (let _204_577 = (let _204_576 = (let _204_575 = (let _204_574 = (let _204_573 = (let _204_572 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _204_572))
in (f_has_t, _204_573))
in (FStar_SMTEncoding_Term.mkImp _204_574))
in (((f_has_t)::[])::[], (fsym)::cvars, _204_575))
in (mkForall_fuel _204_576))
in (_204_577, Some ("pre-typing for functions")))
in FStar_SMTEncoding_Term.Assume (_204_578))
in (let t_interp = (let _204_582 = (let _204_581 = (let _204_580 = (let _204_579 = (FStar_SMTEncoding_Term.mkIff (f_has_t_z, t_interp))
in (((f_has_t_z)::[])::[], (fsym)::cvars, _204_579))
in (FStar_SMTEncoding_Term.mkForall _204_580))
in (_204_581, Some ((Prims.strcat tsym " interpretation"))))
in FStar_SMTEncoding_Term.Assume (_204_582))
in (let t_decls = (FStar_List.append (FStar_List.append decls decls') ((tdecl)::(k_assumption)::(pre_typing)::(t_interp)::[]))
in (let _101_691 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls))))))))))))))
end))))
end))
end))
end)))))
end))
end else begin
(let tsym = (varops.fresh "Non_total_Tm_arrow")
in (let tdecl = FStar_SMTEncoding_Term.DeclFun ((tsym, [], FStar_SMTEncoding_Term.Term_sort, None))
in (let t = (FStar_SMTEncoding_Term.mkApp (tsym, []))
in (let t_kinding = (let _204_584 = (let _204_583 = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (_204_583, None))
in FStar_SMTEncoding_Term.Assume (_204_584))
in (let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)
in (let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (let t_interp = (let _204_591 = (let _204_590 = (let _204_589 = (let _204_588 = (let _204_587 = (let _204_586 = (let _204_585 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _204_585))
in (f_has_t, _204_586))
in (FStar_SMTEncoding_Term.mkImp _204_587))
in (((f_has_t)::[])::[], (fsym)::[], _204_588))
in (mkForall_fuel _204_589))
in (_204_590, Some ("pre-typing")))
in FStar_SMTEncoding_Term.Assume (_204_591))
in (t, (tdecl)::(t_kinding)::(t_interp)::[])))))))))
end
end))
end
| FStar_Syntax_Syntax.Tm_refine (_101_702) -> begin
(let _101_722 = (match ((FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.tk = _101_709; FStar_Syntax_Syntax.pos = _101_707; FStar_Syntax_Syntax.vars = _101_705} -> begin
(let _101_717 = (FStar_Syntax_Subst.open_term (((x, None))::[]) f)
in (match (_101_717) with
| (b, f) -> begin
(let _204_593 = (let _204_592 = (FStar_List.hd b)
in (Prims.fst _204_592))
in (_204_593, f))
end))
end
| _101_719 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_101_722) with
| (x, f) -> begin
(let _101_725 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (_101_725) with
| (base_t, decls) -> begin
(let _101_729 = (gen_term_var env x)
in (match (_101_729) with
| (x, xtm, env') -> begin
(let _101_732 = (encode_formula f env')
in (match (_101_732) with
| (refinement, decls') -> begin
(let _101_735 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_101_735) with
| (fsym, fterm) -> begin
(let encoding = (let _204_595 = (let _204_594 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in (_204_594, refinement))
in (FStar_SMTEncoding_Term.mkAnd _204_595))
in (let cvars = (let _204_597 = (FStar_SMTEncoding_Term.free_variables encoding)
in (FStar_All.pipe_right _204_597 (FStar_List.filter (fun _101_740 -> (match (_101_740) with
| (y, _101_739) -> begin
((y <> x) && (y <> fsym))
end)))))
in (let xfv = (x, FStar_SMTEncoding_Term.Term_sort)
in (let ffv = (fsym, FStar_SMTEncoding_Term.Fuel_sort)
in (let tkey = (FStar_SMTEncoding_Term.mkForall ([], (ffv)::(xfv)::cvars, encoding))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _101_747, _101_749) -> begin
(let _204_600 = (let _204_599 = (let _204_598 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in (t, _204_598))
in (FStar_SMTEncoding_Term.mkApp _204_599))
in (_204_600, []))
end
| None -> begin
(let tsym = (varops.fresh "Typ_refine")
in (let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (let tdecl = FStar_SMTEncoding_Term.DeclFun ((tsym, cvar_sorts, FStar_SMTEncoding_Term.Term_sort, None))
in (let t = (let _204_602 = (let _204_601 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (tsym, _204_601))
in (FStar_SMTEncoding_Term.mkApp _204_602))
in (let x_has_t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (let t_kinding = (FStar_SMTEncoding_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (let assumption = (let _204_604 = (let _204_603 = (FStar_SMTEncoding_Term.mkIff (x_has_t, encoding))
in (((x_has_t)::[])::[], (ffv)::(xfv)::cvars, _204_603))
in (FStar_SMTEncoding_Term.mkForall _204_604))
in (let t_decls = (let _204_611 = (let _204_610 = (let _204_609 = (let _204_608 = (let _204_607 = (let _204_606 = (let _204_605 = (FStar_Syntax_Print.term_to_string t0)
in Some (_204_605))
in (assumption, _204_606))
in FStar_SMTEncoding_Term.Assume (_204_607))
in (_204_608)::[])
in (FStar_SMTEncoding_Term.Assume ((t_kinding, None)))::_204_609)
in (tdecl)::_204_610)
in (FStar_List.append (FStar_List.append decls decls') _204_611))
in (let _101_762 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls)))))))))))
end))))))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
(let ttm = (let _204_612 = (FStar_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Term.mk_Term_uvar _204_612))
in (let _101_771 = (encode_term_pred None k env ttm)
in (match (_101_771) with
| (t_has_k, decls) -> begin
(let d = FStar_SMTEncoding_Term.Assume ((t_has_k, None))
in (ttm, (d)::decls))
end)))
end
| FStar_Syntax_Syntax.Tm_app (_101_774) -> begin
(let _101_778 = (FStar_Syntax_Util.head_and_args t0)
in (match (_101_778) with
| (head, args_e) -> begin
(match ((let _204_614 = (let _204_613 = (FStar_Syntax_Subst.compress head)
in _204_613.FStar_Syntax_Syntax.n)
in (_204_614, args_e))) with
| (FStar_Syntax_Syntax.Tm_abs (_101_780), _101_783) -> begin
(let _204_615 = (whnf env t)
in (encode_term _204_615 env))
end
| ((FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (l, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _::(v1, _)::(v2, _)::[])) | ((FStar_Syntax_Syntax.Tm_fvar (l, _), _::(v1, _)::(v2, _)::[])) when (FStar_Ident.lid_equals l.FStar_Syntax_Syntax.v FStar_Syntax_Const.lexcons_lid) -> begin
(let _101_829 = (encode_term v1 env)
in (match (_101_829) with
| (v1, decls1) -> begin
(let _101_832 = (encode_term v2 env)
in (match (_101_832) with
| (v2, decls2) -> begin
(let _204_616 = (FStar_SMTEncoding_Term.mk_LexCons v1 v2)
in (_204_616, (FStar_List.append decls1 decls2)))
end))
end))
end
| _101_834 -> begin
(let _101_837 = (encode_args args_e env)
in (match (_101_837) with
| (args, decls) -> begin
(let encode_partial_app = (fun ht_opt -> (let _101_842 = (encode_term head env)
in (match (_101_842) with
| (head, decls') -> begin
(let app_tm = (mk_Apply_args head args)
in (match (ht_opt) with
| None -> begin
(app_tm, (FStar_List.append decls decls'))
end
| Some (formals, c) -> begin
(let _101_851 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (_101_851) with
| (formals, rest) -> begin
(let subst = (FStar_List.map2 (fun _101_855 _101_859 -> (match ((_101_855, _101_859)) with
| ((bv, _101_854), (a, _101_858)) -> begin
FStar_Syntax_Syntax.NT ((bv, a))
end)) formals args_e)
in (let ty = (let _204_621 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right _204_621 (FStar_Syntax_Subst.subst subst)))
in (let _101_864 = (encode_term_pred None ty env app_tm)
in (match (_101_864) with
| (has_type, decls'') -> begin
(let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (let e_typing = (let _204_623 = (let _204_622 = (FStar_SMTEncoding_Term.mkForall (((has_type)::[])::[], cvars, has_type))
in (_204_622, None))
in FStar_SMTEncoding_Term.Assume (_204_623))
in (app_tm, (FStar_List.append (FStar_List.append (FStar_List.append decls decls') decls'') ((e_typing)::[])))))
end))))
end))
end))
end)))
in (let encode_full_app = (fun fv -> (let _101_871 = (lookup_free_var_sym env fv)
in (match (_101_871) with
| (fname, fuel_args) -> begin
(let tm = (FStar_SMTEncoding_Term.mkApp' (fname, (FStar_List.append fuel_args args)))
in (tm, decls))
end)))
in (let head = (FStar_Syntax_Subst.compress head)
in (let head_type = (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (x); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (x)) -> begin
x.FStar_Syntax_Syntax.sort
end
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv, _)) -> begin
(let _204_626 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _204_626 Prims.snd))
end
| FStar_Syntax_Syntax.Tm_ascribed (_101_909, t, _101_912) -> begin
t
end
| _101_916 -> begin
(let _204_630 = (let _204_629 = (FStar_Syntax_Print.term_to_string t0)
in (let _204_628 = (FStar_Syntax_Print.tag_of_term head)
in (let _204_627 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format3 "Unexpected head of application %s is: %s, %s" _204_629 _204_628 _204_627))))
in (FStar_All.failwith _204_630))
end)
in (let head_type = (let _204_631 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine _204_631))
in (let _101_919 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _204_634 = (FStar_Syntax_Print.term_to_string head)
in (let _204_633 = (FStar_Syntax_Print.tag_of_term head)
in (let _204_632 = (FStar_Syntax_Print.term_to_string head_type)
in (FStar_Util.print3 "Recomputed type of head %s (%s) to be %s\n" _204_634 _204_633 _204_632))))
end else begin
()
end
in (let _101_923 = (FStar_Syntax_Util.arrow_formals_comp head_type)
in (match (_101_923) with
| (formals, c) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv, _)) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv)
end
| _101_945 -> begin
if ((FStar_List.length formals) > (FStar_List.length args)) then begin
(encode_partial_app (Some ((formals, c))))
end else begin
(encode_partial_app None)
end
end)
end))))))))
end))
end)
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(let _101_954 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_101_954) with
| (bs, body, opening) -> begin
(let fallback = (fun _101_956 -> (match (()) with
| () -> begin
(let f = (varops.fresh "Tm_abs")
in (let decl = FStar_SMTEncoding_Term.DeclFun ((f, [], FStar_SMTEncoding_Term.Term_sort, None))
in (let _204_637 = (FStar_SMTEncoding_Term.mkFreeV (f, FStar_SMTEncoding_Term.Term_sort))
in (_204_637, (decl)::[]))))
end))
in (match (lopt) with
| None -> begin
(let _101_960 = (let _204_639 = (let _204_638 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s" _204_638))
in (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos _204_639))
in (fallback ()))
end
| Some (lc) -> begin
if (let _204_640 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)
in (FStar_All.pipe_left Prims.op_Negation _204_640)) then begin
(fallback ())
end else begin
(let c0 = (lc.FStar_Syntax_Syntax.comp ())
in (let c = (FStar_Syntax_Subst.subst_comp opening c0)
in (let _101_972 = (encode_binders None bs env)
in (match (_101_972) with
| (vars, guards, envbody, decls, _101_971) -> begin
(let _101_975 = (encode_term body envbody)
in (match (_101_975) with
| (body, decls') -> begin
(let key_body = (let _204_644 = (let _204_643 = (let _204_642 = (let _204_641 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_204_641, body))
in (FStar_SMTEncoding_Term.mkImp _204_642))
in ([], vars, _204_643))
in (FStar_SMTEncoding_Term.mkForall _204_644))
in (let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (let tkey = (FStar_SMTEncoding_Term.mkForall ([], cvars, key_body))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _101_981, _101_983) -> begin
(let _204_647 = (let _204_646 = (let _204_645 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (t, _204_645))
in (FStar_SMTEncoding_Term.mkApp _204_646))
in (_204_647, []))
end
| None -> begin
(match ((is_eta env vars body)) with
| Some (t) -> begin
(t, [])
end
| None -> begin
(let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (let fsym = (varops.fresh "Exp_abs")
in (let fdecl = FStar_SMTEncoding_Term.DeclFun ((fsym, cvar_sorts, FStar_SMTEncoding_Term.Term_sort, None))
in (let f = (let _204_649 = (let _204_648 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (fsym, _204_648))
in (FStar_SMTEncoding_Term.mkApp _204_649))
in (let app = (mk_Apply f vars)
in (let tfun = (FStar_Syntax_Util.arrow bs c)
in (let _101_998 = (encode_term_pred None tfun env f)
in (match (_101_998) with
| (f_has_t, decls'') -> begin
(let typing_f = (let _204_651 = (let _204_650 = (FStar_SMTEncoding_Term.mkForall (((f)::[])::[], cvars, f_has_t))
in (_204_650, Some ((Prims.strcat fsym " typing"))))
in FStar_SMTEncoding_Term.Assume (_204_651))
in (let interp_f = (let _204_658 = (let _204_657 = (let _204_656 = (let _204_655 = (let _204_654 = (let _204_653 = (FStar_SMTEncoding_Term.mk_IsTyped app)
in (let _204_652 = (FStar_SMTEncoding_Term.mkEq (app, body))
in (_204_653, _204_652)))
in (FStar_SMTEncoding_Term.mkImp _204_654))
in (((app)::[])::[], (FStar_List.append vars cvars), _204_655))
in (FStar_SMTEncoding_Term.mkForall _204_656))
in (_204_657, Some ((Prims.strcat fsym " interpretation"))))
in FStar_SMTEncoding_Term.Assume (_204_658))
in (let f_decls = (FStar_List.append (FStar_List.append (FStar_List.append decls decls') ((fdecl)::decls'')) ((typing_f)::(interp_f)::[]))
in (let _101_1002 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (fsym, cvar_sorts, f_decls))
in (f, f_decls)))))
end))))))))
end)
end))))
end))
end))))
end
end))
end))
end
| FStar_Syntax_Syntax.Tm_let ((_101_1005, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_101_1017); FStar_Syntax_Syntax.lbunivs = _101_1015; FStar_Syntax_Syntax.lbtyp = _101_1013; FStar_Syntax_Syntax.lbeff = _101_1011; FStar_Syntax_Syntax.lbdef = _101_1009}::_101_1007), _101_1023) -> begin
(FStar_All.failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _101_1032; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _101_1029; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (_101_1042) -> begin
(let _101_1044 = (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (let e = (varops.fresh "let-rec")
in (let decl_e = FStar_SMTEncoding_Term.DeclFun ((e, [], FStar_SMTEncoding_Term.Term_sort, None))
in (let _204_659 = (FStar_SMTEncoding_Term.mkFreeV (e, FStar_SMTEncoding_Term.Term_sort))
in (_204_659, (decl_e)::[])))))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end))))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (let _101_1060 = (encode_term e1 env)
in (match (_101_1060) with
| (ee1, decls1) -> begin
(let _101_1063 = (FStar_Syntax_Subst.open_term (((x, None))::[]) e2)
in (match (_101_1063) with
| (xs, e2) -> begin
(let _101_1067 = (FStar_List.hd xs)
in (match (_101_1067) with
| (x, _101_1066) -> begin
(let env' = (push_term_var env x ee1)
in (let _101_1071 = (encode_term e2 env')
in (match (_101_1071) with
| (ee2, decls2) -> begin
(ee2, (FStar_List.append decls1 decls2))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (let _101_1079 = (encode_term e env)
in (match (_101_1079) with
| (scr, decls) -> begin
(let _101_1116 = (FStar_List.fold_right (fun b _101_1083 -> (match (_101_1083) with
| (else_case, decls) -> begin
(let _101_1087 = (FStar_Syntax_Subst.open_branch b)
in (match (_101_1087) with
| (p, w, br) -> begin
(let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun _101_1091 _101_1094 -> (match ((_101_1091, _101_1094)) with
| ((env0, pattern), (else_case, decls)) -> begin
(let guard = (pattern.guard scr)
in (let projections = (pattern.projections scr)
in (let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env _101_1100 -> (match (_101_1100) with
| (x, t) -> begin
(push_term_var env x t)
end)) env))
in (let _101_1110 = (match (w) with
| None -> begin
(guard, [])
end
| Some (w) -> begin
(let _101_1107 = (encode_term w env)
in (match (_101_1107) with
| (w, decls2) -> begin
(let _204_693 = (let _204_692 = (let _204_691 = (let _204_690 = (let _204_689 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Term.mkTrue)
in (w, _204_689))
in (FStar_SMTEncoding_Term.mkEq _204_690))
in (guard, _204_691))
in (FStar_SMTEncoding_Term.mkAnd _204_692))
in (_204_693, decls2))
end))
end)
in (match (_101_1110) with
| (guard, decls2) -> begin
(let _101_1113 = (encode_br br env)
in (match (_101_1113) with
| (br, decls3) -> begin
(let _204_694 = (FStar_SMTEncoding_Term.mkITE (guard, br, else_case))
in (_204_694, (FStar_List.append (FStar_List.append decls decls2) decls3)))
end))
end)))))
end)) patterns (else_case, decls)))
end))
end)) pats (default_case, decls))
in (match (_101_1116) with
| (match_tm, decls) -> begin
(match_tm, decls)
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _101_1122 -> begin
(let _204_697 = (encode_one_pat env pat)
in (_204_697)::[])
end))
and encode_one_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> (let _101_1125 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _204_700 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" _204_700))
end else begin
()
end
in (let _101_1129 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (_101_1129) with
| (vars, pat_term) -> begin
(let _101_1141 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun _101_1132 v -> (match (_101_1132) with
| (env, vars) -> begin
(let _101_1138 = (gen_term_var env v)
in (match (_101_1138) with
| (xx, _101_1136, env) -> begin
(env, ((v, (xx, FStar_SMTEncoding_Term.Term_sort)))::vars)
end))
end)) (env, [])))
in (match (_101_1141) with
| (env, vars) -> begin
(let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_101_1146) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_dot_term (_)) -> begin
FStar_SMTEncoding_Term.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _204_708 = (let _204_707 = (encode_const c)
in (scrutinee, _204_707))
in (FStar_SMTEncoding_Term.mkEq _204_708))
end
| FStar_Syntax_Syntax.Pat_cons ((f, _101_1161), args) -> begin
(let is_f = (mk_data_tester env f.FStar_Syntax_Syntax.v scrutinee)
in (let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _101_1171 -> (match (_101_1171) with
| (arg, _101_1170) -> begin
(let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.v i)
in (let _204_711 = (FStar_SMTEncoding_Term.mkApp (proj, (scrutinee)::[]))
in (mk_guard arg _204_711)))
end))))
in (FStar_SMTEncoding_Term.mk_and_l ((is_f)::sub_term_guards))))
end))
in (let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_101_1178) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _)) | (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
((x, scrutinee))::[]
end
| FStar_Syntax_Syntax.Pat_constant (_101_1188) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons ((f, _101_1192), args) -> begin
(let _204_719 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _101_1201 -> (match (_101_1201) with
| (arg, _101_1200) -> begin
(let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.v i)
in (let _204_718 = (FStar_SMTEncoding_Term.mkApp (proj, (scrutinee)::[]))
in (mk_projections arg _204_718)))
end))))
in (FStar_All.pipe_right _204_719 FStar_List.flatten))
end))
in (let pat_term = (fun _101_1204 -> (match (()) with
| () -> begin
(encode_term pat_term env)
end))
in (let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in (env, pattern)))))
end))
end))))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (let _101_1220 = (FStar_All.pipe_right l (FStar_List.fold_left (fun _101_1210 _101_1214 -> (match ((_101_1210, _101_1214)) with
| ((tms, decls), (t, _101_1213)) -> begin
(let _101_1217 = (encode_term t env)
in (match (_101_1217) with
| (t, decls') -> begin
((t)::tms, (FStar_List.append decls decls'))
end))
end)) ([], [])))
in (match (_101_1220) with
| (l, decls) -> begin
((FStar_List.rev l), decls)
end)))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (let _101_1226 = (encode_formula_with_labels phi env)
in (match (_101_1226) with
| (t, vars, decls) -> begin
(match (vars) with
| [] -> begin
(t, decls)
end
| _101_1229 -> begin
(FStar_All.failwith "Unexpected labels in formula")
end)
end)))
and encode_function_type_as_formula : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun induction_on new_pats t env -> (let rec list_elements = (fun e -> (match ((let _204_734 = (FStar_Syntax_Util.unmeta e)
in _204_734.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _101_1244); FStar_Syntax_Syntax.tk = _101_1241; FStar_Syntax_Syntax.pos = _101_1239; FStar_Syntax_Syntax.vars = _101_1237}, _101_1249) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.nil_lid) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _101_1260); FStar_Syntax_Syntax.tk = _101_1257; FStar_Syntax_Syntax.pos = _101_1255; FStar_Syntax_Syntax.vars = _101_1253}, _101_1273::(hd, _101_1270)::(tl, _101_1266)::[]) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.cons_lid) -> begin
(let _204_735 = (list_elements tl)
in (hd)::_204_735)
end
| _101_1278 -> begin
(let _101_1279 = (FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern")
in [])
end))
in (let v_or_t_pat = (fun p -> (match ((let _204_738 = (FStar_Syntax_Util.unmeta p)
in _204_738.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _101_1291); FStar_Syntax_Syntax.tk = _101_1288; FStar_Syntax_Syntax.pos = _101_1286; FStar_Syntax_Syntax.vars = _101_1284}, (_101_1300, _101_1302)::(e, _101_1297)::[]) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.smtpat_lid) -> begin
(e, None)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _101_1315); FStar_Syntax_Syntax.tk = _101_1312; FStar_Syntax_Syntax.pos = _101_1310; FStar_Syntax_Syntax.vars = _101_1308}, (t, _101_1321)::[]) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.smtpatT_lid) -> begin
(t, None)
end
| _101_1327 -> begin
(FStar_All.failwith "Unexpected pattern term")
end))
in (let lemma_pats = (fun p -> (let elts = (list_elements p)
in (match (elts) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _101_1345); FStar_Syntax_Syntax.tk = _101_1342; FStar_Syntax_Syntax.pos = _101_1340; FStar_Syntax_Syntax.vars = _101_1338}, (e, _101_1351)::[]); FStar_Syntax_Syntax.tk = _101_1336; FStar_Syntax_Syntax.pos = _101_1334; FStar_Syntax_Syntax.vars = _101_1332}::[] when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.smtpatOr_lid) -> begin
(let _204_743 = (list_elements e)
in (FStar_All.pipe_right _204_743 (FStar_List.map (fun branch -> (let _204_742 = (list_elements branch)
in (FStar_All.pipe_right _204_742 (FStar_List.map v_or_t_pat)))))))
end
| _101_1360 -> begin
(let _204_744 = (FStar_All.pipe_right elts (FStar_List.map v_or_t_pat))
in (_204_744)::[])
end)))
in (let _101_1394 = (match ((let _204_745 = (FStar_Syntax_Subst.compress t)
in _204_745.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(let _101_1367 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_101_1367) with
| (binders, c) -> begin
(let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| (pre, _101_1379)::(post, _101_1375)::(pats, _101_1371)::[] -> begin
(let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _204_746 = (lemma_pats pats')
in (binders, pre, post, _204_746)))
end
| _101_1387 -> begin
(FStar_All.failwith "impos")
end))
end))
end
| _101_1389 -> begin
(FStar_All.failwith "Impos")
end)
in (match (_101_1394) with
| (binders, pre, post, patterns) -> begin
(let _101_1401 = (encode_binders None binders env)
in (match (_101_1401) with
| (vars, guards, env, decls, _101_1400) -> begin
(let _101_1414 = (let _204_750 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (let _101_1411 = (let _204_749 = (FStar_All.pipe_right branch (FStar_List.map (fun _101_1406 -> (match (_101_1406) with
| (t, _101_1405) -> begin
(encode_term t (let _101_1407 = env
in {bindings = _101_1407.bindings; depth = _101_1407.depth; tcenv = _101_1407.tcenv; warn = _101_1407.warn; cache = _101_1407.cache; nolabels = _101_1407.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _101_1407.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _204_749 FStar_List.unzip))
in (match (_101_1411) with
| (pats, decls) -> begin
(pats, decls)
end)))))
in (FStar_All.pipe_right _204_750 FStar_List.unzip))
in (match (_101_1414) with
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
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _204_753 = (let _204_752 = (FStar_SMTEncoding_Term.mkFreeV l)
in (FStar_SMTEncoding_Term.mk_Precedes _204_752 e))
in (_204_753)::p))))
end
| _101_1424 -> begin
(let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _204_759 = (FStar_SMTEncoding_Term.mk_Precedes tl e)
in (_204_759)::p))))
end
| (x, FStar_SMTEncoding_Term.Term_sort)::vars -> begin
(let _204_761 = (let _204_760 = (FStar_SMTEncoding_Term.mkFreeV (x, FStar_SMTEncoding_Term.Term_sort))
in (FStar_SMTEncoding_Term.mk_LexCons _204_760 tl))
in (aux _204_761 vars))
end
| _101_1436 -> begin
pats
end))
in (let _204_762 = (FStar_SMTEncoding_Term.mkFreeV ("Prims.LexTop", FStar_SMTEncoding_Term.Term_sort))
in (aux _204_762 vars)))
end)
end)
in (let env = (let _101_1438 = env
in {bindings = _101_1438.bindings; depth = _101_1438.depth; tcenv = _101_1438.tcenv; warn = _101_1438.warn; cache = _101_1438.cache; nolabels = true; use_zfuel_name = _101_1438.use_zfuel_name; encode_non_total_function_typ = _101_1438.encode_non_total_function_typ})
in (let _101_1443 = (let _204_763 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula _204_763 env))
in (match (_101_1443) with
| (pre, decls'') -> begin
(let _101_1446 = (let _204_764 = (FStar_Syntax_Util.unmeta post)
in (encode_formula _204_764 env))
in (match (_101_1446) with
| (post, decls''') -> begin
(let decls = (FStar_List.append (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'') decls''')
in (let _204_769 = (let _204_768 = (let _204_767 = (let _204_766 = (let _204_765 = (FStar_SMTEncoding_Term.mk_and_l ((pre)::guards))
in (_204_765, post))
in (FStar_SMTEncoding_Term.mkImp _204_766))
in (pats, vars, _204_767))
in (FStar_SMTEncoding_Term.mkForall _204_768))
in (_204_769, decls)))
end))
end)))))
end))
end))
end))))))
and encode_formula_with_labels : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * labels * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (let enc = (fun f l -> (let _101_1460 = (FStar_Util.fold_map (fun decls x -> (let _101_1457 = (encode_term (Prims.fst x) env)
in (match (_101_1457) with
| (t, decls') -> begin
((FStar_List.append decls decls'), t)
end))) [] l)
in (match (_101_1460) with
| (decls, args) -> begin
(let _204_787 = (f args)
in (_204_787, [], decls))
end)))
in (let const_op = (fun f _101_1463 -> (f, [], []))
in (let un_op = (fun f l -> (let _204_801 = (FStar_List.hd l)
in (FStar_All.pipe_left f _204_801)))
in (let bin_op = (fun f _101_8 -> (match (_101_8) with
| t1::t2::[] -> begin
(f (t1, t2))
end
| _101_1474 -> begin
(FStar_All.failwith "Impossible")
end))
in (let enc_prop_c = (fun f l -> (let _101_1494 = (FStar_List.fold_right (fun _101_1482 _101_1486 -> (match ((_101_1482, _101_1486)) with
| ((t, _101_1481), (phis, labs, decls)) -> begin
(let _101_1490 = (encode_formula_with_labels t env)
in (match (_101_1490) with
| (phi, labs', decls') -> begin
((phi)::phis, (FStar_List.append labs' labs), (FStar_List.append decls' decls))
end))
end)) l ([], [], []))
in (match (_101_1494) with
| (phis, labs, decls) -> begin
(let _204_826 = (f phis)
in (_204_826, labs, decls))
end)))
in (let eq_op = (fun _101_9 -> (match (_101_9) with
| _101_1501::_101_1499::e1::e2::[] -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) l)
end))
in (let mk_imp = (fun _101_10 -> (match (_101_10) with
| (lhs, _101_1512)::(rhs, _101_1508)::[] -> begin
(let _101_1518 = (encode_formula_with_labels rhs env)
in (match (_101_1518) with
| (l1, labs1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _101_1521) -> begin
(l1, labs1, decls1)
end
| _101_1525 -> begin
(let _101_1529 = (encode_formula_with_labels lhs env)
in (match (_101_1529) with
| (l2, labs2, decls2) -> begin
(let _204_831 = (FStar_SMTEncoding_Term.mkImp (l2, l1))
in (_204_831, (FStar_List.append labs1 labs2), (FStar_List.append decls1 decls2)))
end))
end)
end))
end
| _101_1531 -> begin
(FStar_All.failwith "impossible")
end))
in (let mk_ite = (fun _101_11 -> (match (_101_11) with
| (guard, _101_1544)::(_then, _101_1540)::(_else, _101_1536)::[] -> begin
(let _101_1550 = (encode_formula_with_labels guard env)
in (match (_101_1550) with
| (g, labs1, decls1) -> begin
(let _101_1554 = (encode_formula_with_labels _then env)
in (match (_101_1554) with
| (t, labs2, decls2) -> begin
(let _101_1558 = (encode_formula_with_labels _else env)
in (match (_101_1558) with
| (e, labs3, decls3) -> begin
(let res = (FStar_SMTEncoding_Term.mkITE (g, t, e))
in (res, (FStar_List.append (FStar_List.append labs1 labs2) labs3), (FStar_List.append (FStar_List.append decls1 decls2) decls3)))
end))
end))
end))
end
| _101_1561 -> begin
(FStar_All.failwith "impossible")
end))
in (let unboxInt_l = (fun f l -> (let _204_843 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f _204_843)))
in (let connectives = (let _204_896 = (let _204_852 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkAnd))
in (FStar_Syntax_Const.and_lid, _204_852))
in (let _204_895 = (let _204_894 = (let _204_858 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkOr))
in (FStar_Syntax_Const.or_lid, _204_858))
in (let _204_893 = (let _204_892 = (let _204_891 = (let _204_867 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkIff))
in (FStar_Syntax_Const.iff_lid, _204_867))
in (let _204_890 = (let _204_889 = (let _204_888 = (let _204_876 = (FStar_All.pipe_left enc_prop_c (un_op FStar_SMTEncoding_Term.mkNot))
in (FStar_Syntax_Const.not_lid, _204_876))
in (_204_888)::((FStar_Syntax_Const.eq2_lid, eq_op))::((FStar_Syntax_Const.true_lid, (const_op FStar_SMTEncoding_Term.mkTrue)))::((FStar_Syntax_Const.false_lid, (const_op FStar_SMTEncoding_Term.mkFalse)))::[])
in ((FStar_Syntax_Const.ite_lid, mk_ite))::_204_889)
in (_204_891)::_204_890))
in ((FStar_Syntax_Const.imp_lid, mk_imp))::_204_892)
in (_204_894)::_204_893))
in (_204_896)::_204_895))
in (let fallback = (fun phi -> (match (phi.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(let _101_1580 = (encode_formula_with_labels phi' env)
in (match (_101_1580) with
| (phi, labs, decls) -> begin
(let _204_899 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled ((phi, msg, r))))
in (_204_899, [], decls))
end))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(let _101_1587 = (encode_match e pats FStar_SMTEncoding_Term.mkFalse env encode_formula)
in (match (_101_1587) with
| (t, decls) -> begin
(t, [], decls)
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _101_1594; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _101_1591; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(let _101_1605 = (encode_let x t1 e1 e2 env encode_formula)
in (match (_101_1605) with
| (t, decls) -> begin
(t, [], decls)
end))
end
| _101_1607 -> begin
(let _101_1610 = (encode_term phi env)
in (match (_101_1610) with
| (tt, decls) -> begin
(let _204_900 = (FStar_SMTEncoding_Term.mk_Valid tt)
in (_204_900, [], decls))
end))
end))
in (let encode_q_body = (fun env bs ps body -> (let _101_1622 = (encode_binders None bs env)
in (match (_101_1622) with
| (vars, guards, env, decls, _101_1621) -> begin
(let _101_1635 = (let _204_912 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (let _101_1632 = (let _204_911 = (FStar_All.pipe_right p (FStar_List.map (fun _101_1627 -> (match (_101_1627) with
| (t, _101_1626) -> begin
(encode_term t (let _101_1628 = env
in {bindings = _101_1628.bindings; depth = _101_1628.depth; tcenv = _101_1628.tcenv; warn = _101_1628.warn; cache = _101_1628.cache; nolabels = _101_1628.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _101_1628.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _204_911 FStar_List.unzip))
in (match (_101_1632) with
| (p, decls) -> begin
(p, (FStar_List.flatten decls))
end)))))
in (FStar_All.pipe_right _204_912 FStar_List.unzip))
in (match (_101_1635) with
| (pats, decls') -> begin
(let _101_1639 = (encode_formula_with_labels body env)
in (match (_101_1639) with
| (body, labs, decls'') -> begin
(let _204_913 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (vars, pats, _204_913, body, labs, (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'')))
end))
end))
end)))
in (let _101_1640 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _204_914 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print1 ">>>> Destructing as formula ... %s\n" _204_914))
end else begin
()
end
in (let phi = (FStar_Syntax_Subst.compress phi)
in (match ((FStar_Syntax_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _101_1652 -> (match (_101_1652) with
| (l, _101_1651) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_101_1655, f) -> begin
(f arms)
end)
end
| Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
(let _101_1665 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _204_931 = (FStar_All.pipe_right vars (FStar_Syntax_Print.binders_to_string "; "))
in (FStar_Util.print1 ">>>> Got QALL [%s]\n" _204_931))
end else begin
()
end
in (let _101_1673 = (encode_q_body env vars pats body)
in (match (_101_1673) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _204_934 = (let _204_933 = (let _204_932 = (FStar_SMTEncoding_Term.mkImp (guard, body))
in (pats, vars, _204_932))
in (FStar_SMTEncoding_Term.mkForall _204_933))
in (_204_934, labs, decls))
end)))
end
| Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
(let _101_1686 = (encode_q_body env vars pats body)
in (match (_101_1686) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _204_937 = (let _204_936 = (let _204_935 = (FStar_SMTEncoding_Term.mkAnd (guard, body))
in (pats, vars, _204_935))
in (FStar_SMTEncoding_Term.mkExists _204_936))
in (_204_937, labs, decls))
end))
end))))))))))))))))

type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.decl Prims.list; is : FStar_Ident.lident  ->  Prims.bool}

let is_Mkprims_t : prims_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkprims_t"))))

let prims : prims_t = (let _101_1692 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (_101_1692) with
| (asym, a) -> begin
(let _101_1695 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_101_1695) with
| (xsym, x) -> begin
(let _101_1698 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (_101_1698) with
| (ysym, y) -> begin
(let deffun = (fun vars body x -> (FStar_SMTEncoding_Term.DefineFun ((x, vars, FStar_SMTEncoding_Term.Term_sort, body, None)))::[])
in (let quant = (fun vars body x -> (let t1 = (let _204_980 = (let _204_979 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (x, _204_979))
in (FStar_SMTEncoding_Term.mkApp _204_980))
in (let vname_decl = (let _204_982 = (let _204_981 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (x, _204_981, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_204_982))
in (let _204_988 = (let _204_987 = (let _204_986 = (let _204_985 = (let _204_984 = (let _204_983 = (FStar_SMTEncoding_Term.mkEq (t1, body))
in (((t1)::[])::[], vars, _204_983))
in (FStar_SMTEncoding_Term.mkForall _204_984))
in (_204_985, None))
in FStar_SMTEncoding_Term.Assume (_204_986))
in (_204_987)::[])
in (vname_decl)::_204_988))))
in (let axy = ((asym, FStar_SMTEncoding_Term.Term_sort))::((xsym, FStar_SMTEncoding_Term.Term_sort))::((ysym, FStar_SMTEncoding_Term.Term_sort))::[]
in (let xy = ((xsym, FStar_SMTEncoding_Term.Term_sort))::((ysym, FStar_SMTEncoding_Term.Term_sort))::[]
in (let qx = ((xsym, FStar_SMTEncoding_Term.Term_sort))::[]
in (let prims = (let _204_1148 = (let _204_997 = (let _204_996 = (let _204_995 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _204_995))
in (quant axy _204_996))
in (FStar_Syntax_Const.op_Eq, _204_997))
in (let _204_1147 = (let _204_1146 = (let _204_1004 = (let _204_1003 = (let _204_1002 = (let _204_1001 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (FStar_SMTEncoding_Term.mkNot _204_1001))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _204_1002))
in (quant axy _204_1003))
in (FStar_Syntax_Const.op_notEq, _204_1004))
in (let _204_1145 = (let _204_1144 = (let _204_1013 = (let _204_1012 = (let _204_1011 = (let _204_1010 = (let _204_1009 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _204_1008 = (FStar_SMTEncoding_Term.unboxInt y)
in (_204_1009, _204_1008)))
in (FStar_SMTEncoding_Term.mkLT _204_1010))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _204_1011))
in (quant xy _204_1012))
in (FStar_Syntax_Const.op_LT, _204_1013))
in (let _204_1143 = (let _204_1142 = (let _204_1022 = (let _204_1021 = (let _204_1020 = (let _204_1019 = (let _204_1018 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _204_1017 = (FStar_SMTEncoding_Term.unboxInt y)
in (_204_1018, _204_1017)))
in (FStar_SMTEncoding_Term.mkLTE _204_1019))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _204_1020))
in (quant xy _204_1021))
in (FStar_Syntax_Const.op_LTE, _204_1022))
in (let _204_1141 = (let _204_1140 = (let _204_1031 = (let _204_1030 = (let _204_1029 = (let _204_1028 = (let _204_1027 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _204_1026 = (FStar_SMTEncoding_Term.unboxInt y)
in (_204_1027, _204_1026)))
in (FStar_SMTEncoding_Term.mkGT _204_1028))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _204_1029))
in (quant xy _204_1030))
in (FStar_Syntax_Const.op_GT, _204_1031))
in (let _204_1139 = (let _204_1138 = (let _204_1040 = (let _204_1039 = (let _204_1038 = (let _204_1037 = (let _204_1036 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _204_1035 = (FStar_SMTEncoding_Term.unboxInt y)
in (_204_1036, _204_1035)))
in (FStar_SMTEncoding_Term.mkGTE _204_1037))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _204_1038))
in (quant xy _204_1039))
in (FStar_Syntax_Const.op_GTE, _204_1040))
in (let _204_1137 = (let _204_1136 = (let _204_1049 = (let _204_1048 = (let _204_1047 = (let _204_1046 = (let _204_1045 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _204_1044 = (FStar_SMTEncoding_Term.unboxInt y)
in (_204_1045, _204_1044)))
in (FStar_SMTEncoding_Term.mkSub _204_1046))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _204_1047))
in (quant xy _204_1048))
in (FStar_Syntax_Const.op_Subtraction, _204_1049))
in (let _204_1135 = (let _204_1134 = (let _204_1056 = (let _204_1055 = (let _204_1054 = (let _204_1053 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Term.mkMinus _204_1053))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _204_1054))
in (quant qx _204_1055))
in (FStar_Syntax_Const.op_Minus, _204_1056))
in (let _204_1133 = (let _204_1132 = (let _204_1065 = (let _204_1064 = (let _204_1063 = (let _204_1062 = (let _204_1061 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _204_1060 = (FStar_SMTEncoding_Term.unboxInt y)
in (_204_1061, _204_1060)))
in (FStar_SMTEncoding_Term.mkAdd _204_1062))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _204_1063))
in (quant xy _204_1064))
in (FStar_Syntax_Const.op_Addition, _204_1065))
in (let _204_1131 = (let _204_1130 = (let _204_1074 = (let _204_1073 = (let _204_1072 = (let _204_1071 = (let _204_1070 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _204_1069 = (FStar_SMTEncoding_Term.unboxInt y)
in (_204_1070, _204_1069)))
in (FStar_SMTEncoding_Term.mkMul _204_1071))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _204_1072))
in (quant xy _204_1073))
in (FStar_Syntax_Const.op_Multiply, _204_1074))
in (let _204_1129 = (let _204_1128 = (let _204_1083 = (let _204_1082 = (let _204_1081 = (let _204_1080 = (let _204_1079 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _204_1078 = (FStar_SMTEncoding_Term.unboxInt y)
in (_204_1079, _204_1078)))
in (FStar_SMTEncoding_Term.mkDiv _204_1080))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _204_1081))
in (quant xy _204_1082))
in (FStar_Syntax_Const.op_Division, _204_1083))
in (let _204_1127 = (let _204_1126 = (let _204_1092 = (let _204_1091 = (let _204_1090 = (let _204_1089 = (let _204_1088 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _204_1087 = (FStar_SMTEncoding_Term.unboxInt y)
in (_204_1088, _204_1087)))
in (FStar_SMTEncoding_Term.mkMod _204_1089))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _204_1090))
in (quant xy _204_1091))
in (FStar_Syntax_Const.op_Modulus, _204_1092))
in (let _204_1125 = (let _204_1124 = (let _204_1101 = (let _204_1100 = (let _204_1099 = (let _204_1098 = (let _204_1097 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _204_1096 = (FStar_SMTEncoding_Term.unboxBool y)
in (_204_1097, _204_1096)))
in (FStar_SMTEncoding_Term.mkAnd _204_1098))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _204_1099))
in (quant xy _204_1100))
in (FStar_Syntax_Const.op_And, _204_1101))
in (let _204_1123 = (let _204_1122 = (let _204_1110 = (let _204_1109 = (let _204_1108 = (let _204_1107 = (let _204_1106 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _204_1105 = (FStar_SMTEncoding_Term.unboxBool y)
in (_204_1106, _204_1105)))
in (FStar_SMTEncoding_Term.mkOr _204_1107))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _204_1108))
in (quant xy _204_1109))
in (FStar_Syntax_Const.op_Or, _204_1110))
in (let _204_1121 = (let _204_1120 = (let _204_1117 = (let _204_1116 = (let _204_1115 = (let _204_1114 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Term.mkNot _204_1114))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _204_1115))
in (quant qx _204_1116))
in (FStar_Syntax_Const.op_Negation, _204_1117))
in (_204_1120)::[])
in (_204_1122)::_204_1121))
in (_204_1124)::_204_1123))
in (_204_1126)::_204_1125))
in (_204_1128)::_204_1127))
in (_204_1130)::_204_1129))
in (_204_1132)::_204_1131))
in (_204_1134)::_204_1133))
in (_204_1136)::_204_1135))
in (_204_1138)::_204_1137))
in (_204_1140)::_204_1139))
in (_204_1142)::_204_1141))
in (_204_1144)::_204_1143))
in (_204_1146)::_204_1145))
in (_204_1148)::_204_1147))
in (let mk = (fun l v -> (let _204_1180 = (FStar_All.pipe_right prims (FStar_List.filter (fun _101_1718 -> (match (_101_1718) with
| (l', _101_1717) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right _204_1180 (FStar_List.collect (fun _101_1722 -> (match (_101_1722) with
| (_101_1720, b) -> begin
(b v)
end))))))
in (let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _101_1728 -> (match (_101_1728) with
| (l', _101_1727) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is}))))))))
end))
end))
end))

let primitive_type_axioms : FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.decl Prims.list = (let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (let yy = ("y", FStar_SMTEncoding_Term.Term_sort)
in (let y = (FStar_SMTEncoding_Term.mkFreeV yy)
in (let mk_unit = (fun _101_1734 tt -> (let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (let _204_1212 = (let _204_1203 = (let _204_1202 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in (_204_1202, Some ("unit typing")))
in FStar_SMTEncoding_Term.Assume (_204_1203))
in (let _204_1211 = (let _204_1210 = (let _204_1209 = (let _204_1208 = (let _204_1207 = (let _204_1206 = (let _204_1205 = (let _204_1204 = (FStar_SMTEncoding_Term.mkEq (x, FStar_SMTEncoding_Term.mk_Term_unit))
in (typing_pred, _204_1204))
in (FStar_SMTEncoding_Term.mkImp _204_1205))
in (((typing_pred)::[])::[], (xx)::[], _204_1206))
in (mkForall_fuel _204_1207))
in (_204_1208, Some ("unit inversion")))
in FStar_SMTEncoding_Term.Assume (_204_1209))
in (_204_1210)::[])
in (_204_1212)::_204_1211))))
in (let mk_bool = (fun _101_1739 tt -> (let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)
in (let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _204_1233 = (let _204_1222 = (let _204_1221 = (let _204_1220 = (let _204_1219 = (let _204_1218 = (let _204_1217 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in (typing_pred, _204_1217))
in (FStar_SMTEncoding_Term.mkImp _204_1218))
in (((typing_pred)::[])::[], (xx)::[], _204_1219))
in (mkForall_fuel _204_1220))
in (_204_1221, Some ("bool inversion")))
in FStar_SMTEncoding_Term.Assume (_204_1222))
in (let _204_1232 = (let _204_1231 = (let _204_1230 = (let _204_1229 = (let _204_1228 = (let _204_1227 = (let _204_1224 = (let _204_1223 = (FStar_SMTEncoding_Term.boxBool b)
in (_204_1223)::[])
in (_204_1224)::[])
in (let _204_1226 = (let _204_1225 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType _204_1225 tt))
in (_204_1227, (bb)::[], _204_1226)))
in (FStar_SMTEncoding_Term.mkForall _204_1228))
in (_204_1229, Some ("bool typing")))
in FStar_SMTEncoding_Term.Assume (_204_1230))
in (_204_1231)::[])
in (_204_1233)::_204_1232))))))
in (let mk_int = (fun _101_1746 tt -> (let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (let typing_pred_y = (FStar_SMTEncoding_Term.mk_HasType y tt)
in (let aa = ("a", FStar_SMTEncoding_Term.Int_sort)
in (let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (let bb = ("b", FStar_SMTEncoding_Term.Int_sort)
in (let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let precedes = (let _204_1245 = (let _204_1244 = (let _204_1243 = (let _204_1242 = (let _204_1241 = (let _204_1240 = (FStar_SMTEncoding_Term.boxInt a)
in (let _204_1239 = (let _204_1238 = (FStar_SMTEncoding_Term.boxInt b)
in (_204_1238)::[])
in (_204_1240)::_204_1239))
in (tt)::_204_1241)
in (tt)::_204_1242)
in ("Prims.Precedes", _204_1243))
in (FStar_SMTEncoding_Term.mkApp _204_1244))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _204_1245))
in (let precedes_y_x = (let _204_1246 = (FStar_SMTEncoding_Term.mkApp ("Precedes", (y)::(x)::[]))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _204_1246))
in (let _204_1288 = (let _204_1252 = (let _204_1251 = (let _204_1250 = (let _204_1249 = (let _204_1248 = (let _204_1247 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in (typing_pred, _204_1247))
in (FStar_SMTEncoding_Term.mkImp _204_1248))
in (((typing_pred)::[])::[], (xx)::[], _204_1249))
in (mkForall_fuel _204_1250))
in (_204_1251, Some ("int inversion")))
in FStar_SMTEncoding_Term.Assume (_204_1252))
in (let _204_1287 = (let _204_1286 = (let _204_1260 = (let _204_1259 = (let _204_1258 = (let _204_1257 = (let _204_1254 = (let _204_1253 = (FStar_SMTEncoding_Term.boxInt b)
in (_204_1253)::[])
in (_204_1254)::[])
in (let _204_1256 = (let _204_1255 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType _204_1255 tt))
in (_204_1257, (bb)::[], _204_1256)))
in (FStar_SMTEncoding_Term.mkForall _204_1258))
in (_204_1259, Some ("int typing")))
in FStar_SMTEncoding_Term.Assume (_204_1260))
in (let _204_1285 = (let _204_1284 = (let _204_1283 = (let _204_1282 = (let _204_1281 = (let _204_1280 = (let _204_1279 = (let _204_1278 = (let _204_1277 = (let _204_1276 = (let _204_1275 = (let _204_1274 = (let _204_1263 = (let _204_1262 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _204_1261 = (FStar_SMTEncoding_Term.mkInteger' 0)
in (_204_1262, _204_1261)))
in (FStar_SMTEncoding_Term.mkGT _204_1263))
in (let _204_1273 = (let _204_1272 = (let _204_1266 = (let _204_1265 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _204_1264 = (FStar_SMTEncoding_Term.mkInteger' 0)
in (_204_1265, _204_1264)))
in (FStar_SMTEncoding_Term.mkGTE _204_1266))
in (let _204_1271 = (let _204_1270 = (let _204_1269 = (let _204_1268 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _204_1267 = (FStar_SMTEncoding_Term.unboxInt x)
in (_204_1268, _204_1267)))
in (FStar_SMTEncoding_Term.mkLT _204_1269))
in (_204_1270)::[])
in (_204_1272)::_204_1271))
in (_204_1274)::_204_1273))
in (typing_pred_y)::_204_1275)
in (typing_pred)::_204_1276)
in (FStar_SMTEncoding_Term.mk_and_l _204_1277))
in (_204_1278, precedes_y_x))
in (FStar_SMTEncoding_Term.mkImp _204_1279))
in (((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[], (xx)::(yy)::[], _204_1280))
in (mkForall_fuel _204_1281))
in (_204_1282, Some ("well-founded ordering on nat (alt)")))
in FStar_SMTEncoding_Term.Assume (_204_1283))
in (_204_1284)::[])
in (_204_1286)::_204_1285))
in (_204_1288)::_204_1287)))))))))))
in (let mk_int_alias = (fun _101_1758 tt -> (let _204_1297 = (let _204_1296 = (let _204_1295 = (let _204_1294 = (let _204_1293 = (FStar_SMTEncoding_Term.mkApp (FStar_Syntax_Const.int_lid.FStar_Ident.str, []))
in (tt, _204_1293))
in (FStar_SMTEncoding_Term.mkEq _204_1294))
in (_204_1295, Some ("mapping to int; for now")))
in FStar_SMTEncoding_Term.Assume (_204_1296))
in (_204_1297)::[]))
in (let mk_str = (fun _101_1762 tt -> (let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (let bb = ("b", FStar_SMTEncoding_Term.String_sort)
in (let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _204_1318 = (let _204_1307 = (let _204_1306 = (let _204_1305 = (let _204_1304 = (let _204_1303 = (let _204_1302 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in (typing_pred, _204_1302))
in (FStar_SMTEncoding_Term.mkImp _204_1303))
in (((typing_pred)::[])::[], (xx)::[], _204_1304))
in (mkForall_fuel _204_1305))
in (_204_1306, Some ("string inversion")))
in FStar_SMTEncoding_Term.Assume (_204_1307))
in (let _204_1317 = (let _204_1316 = (let _204_1315 = (let _204_1314 = (let _204_1313 = (let _204_1312 = (let _204_1309 = (let _204_1308 = (FStar_SMTEncoding_Term.boxString b)
in (_204_1308)::[])
in (_204_1309)::[])
in (let _204_1311 = (let _204_1310 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType _204_1310 tt))
in (_204_1312, (bb)::[], _204_1311)))
in (FStar_SMTEncoding_Term.mkForall _204_1313))
in (_204_1314, Some ("string typing")))
in FStar_SMTEncoding_Term.Assume (_204_1315))
in (_204_1316)::[])
in (_204_1318)::_204_1317))))))
in (let mk_ref = (fun reft_name _101_1770 -> (let r = ("r", FStar_SMTEncoding_Term.Ref_sort)
in (let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (let refa = (let _204_1325 = (let _204_1324 = (let _204_1323 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (_204_1323)::[])
in (reft_name, _204_1324))
in (FStar_SMTEncoding_Term.mkApp _204_1325))
in (let refb = (let _204_1328 = (let _204_1327 = (let _204_1326 = (FStar_SMTEncoding_Term.mkFreeV bb)
in (_204_1326)::[])
in (reft_name, _204_1327))
in (FStar_SMTEncoding_Term.mkApp _204_1328))
in (let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (let _204_1347 = (let _204_1334 = (let _204_1333 = (let _204_1332 = (let _204_1331 = (let _204_1330 = (let _204_1329 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in (typing_pred, _204_1329))
in (FStar_SMTEncoding_Term.mkImp _204_1330))
in (((typing_pred)::[])::[], (xx)::(aa)::[], _204_1331))
in (mkForall_fuel _204_1332))
in (_204_1333, Some ("ref inversion")))
in FStar_SMTEncoding_Term.Assume (_204_1334))
in (let _204_1346 = (let _204_1345 = (let _204_1344 = (let _204_1343 = (let _204_1342 = (let _204_1341 = (let _204_1340 = (let _204_1339 = (FStar_SMTEncoding_Term.mkAnd (typing_pred, typing_pred_b))
in (let _204_1338 = (let _204_1337 = (let _204_1336 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (let _204_1335 = (FStar_SMTEncoding_Term.mkFreeV bb)
in (_204_1336, _204_1335)))
in (FStar_SMTEncoding_Term.mkEq _204_1337))
in (_204_1339, _204_1338)))
in (FStar_SMTEncoding_Term.mkImp _204_1340))
in (((typing_pred)::(typing_pred_b)::[])::[], (xx)::(aa)::(bb)::[], _204_1341))
in (mkForall_fuel' 2 _204_1342))
in (_204_1343, Some ("ref typing is injective")))
in FStar_SMTEncoding_Term.Assume (_204_1344))
in (_204_1345)::[])
in (_204_1347)::_204_1346))))))))))
in (let mk_false_interp = (fun _101_1780 false_tm -> (let valid = (FStar_SMTEncoding_Term.mkApp ("Valid", (false_tm)::[]))
in (let _204_1354 = (let _204_1353 = (let _204_1352 = (FStar_SMTEncoding_Term.mkIff (FStar_SMTEncoding_Term.mkFalse, valid))
in (_204_1352, Some ("False interpretation")))
in FStar_SMTEncoding_Term.Assume (_204_1353))
in (_204_1354)::[])))
in (let mk_and_interp = (fun conj _101_1786 -> (let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let valid = (let _204_1361 = (let _204_1360 = (let _204_1359 = (FStar_SMTEncoding_Term.mkApp (conj, (a)::(b)::[]))
in (_204_1359)::[])
in ("Valid", _204_1360))
in (FStar_SMTEncoding_Term.mkApp _204_1361))
in (let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _204_1368 = (let _204_1367 = (let _204_1366 = (let _204_1365 = (let _204_1364 = (let _204_1363 = (let _204_1362 = (FStar_SMTEncoding_Term.mkAnd (valid_a, valid_b))
in (_204_1362, valid))
in (FStar_SMTEncoding_Term.mkIff _204_1363))
in (((valid)::[])::[], (aa)::(bb)::[], _204_1364))
in (FStar_SMTEncoding_Term.mkForall _204_1365))
in (_204_1366, Some ("/\\ interpretation")))
in FStar_SMTEncoding_Term.Assume (_204_1367))
in (_204_1368)::[])))))))))
in (let mk_or_interp = (fun disj _101_1797 -> (let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let valid = (let _204_1375 = (let _204_1374 = (let _204_1373 = (FStar_SMTEncoding_Term.mkApp (disj, (a)::(b)::[]))
in (_204_1373)::[])
in ("Valid", _204_1374))
in (FStar_SMTEncoding_Term.mkApp _204_1375))
in (let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _204_1382 = (let _204_1381 = (let _204_1380 = (let _204_1379 = (let _204_1378 = (let _204_1377 = (let _204_1376 = (FStar_SMTEncoding_Term.mkOr (valid_a, valid_b))
in (_204_1376, valid))
in (FStar_SMTEncoding_Term.mkIff _204_1377))
in (((valid)::[])::[], (aa)::(bb)::[], _204_1378))
in (FStar_SMTEncoding_Term.mkForall _204_1379))
in (_204_1380, Some ("\\/ interpretation")))
in FStar_SMTEncoding_Term.Assume (_204_1381))
in (_204_1382)::[])))))))))
in (let mk_eq2_interp = (fun eq2 tt -> (let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (let yy = ("y", FStar_SMTEncoding_Term.Term_sort)
in (let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (let y = (FStar_SMTEncoding_Term.mkFreeV yy)
in (let valid = (let _204_1389 = (let _204_1388 = (let _204_1387 = (FStar_SMTEncoding_Term.mkApp (eq2, (a)::(b)::(x)::(y)::[]))
in (_204_1387)::[])
in ("Valid", _204_1388))
in (FStar_SMTEncoding_Term.mkApp _204_1389))
in (let _204_1396 = (let _204_1395 = (let _204_1394 = (let _204_1393 = (let _204_1392 = (let _204_1391 = (let _204_1390 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (_204_1390, valid))
in (FStar_SMTEncoding_Term.mkIff _204_1391))
in (((valid)::[])::[], (aa)::(bb)::(xx)::(yy)::[], _204_1392))
in (FStar_SMTEncoding_Term.mkForall _204_1393))
in (_204_1394, Some ("Eq2 interpretation")))
in FStar_SMTEncoding_Term.Assume (_204_1395))
in (_204_1396)::[])))))))))))
in (let mk_imp_interp = (fun imp tt -> (let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let valid = (let _204_1403 = (let _204_1402 = (let _204_1401 = (FStar_SMTEncoding_Term.mkApp (imp, (a)::(b)::[]))
in (_204_1401)::[])
in ("Valid", _204_1402))
in (FStar_SMTEncoding_Term.mkApp _204_1403))
in (let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _204_1410 = (let _204_1409 = (let _204_1408 = (let _204_1407 = (let _204_1406 = (let _204_1405 = (let _204_1404 = (FStar_SMTEncoding_Term.mkImp (valid_a, valid_b))
in (_204_1404, valid))
in (FStar_SMTEncoding_Term.mkIff _204_1405))
in (((valid)::[])::[], (aa)::(bb)::[], _204_1406))
in (FStar_SMTEncoding_Term.mkForall _204_1407))
in (_204_1408, Some ("==> interpretation")))
in FStar_SMTEncoding_Term.Assume (_204_1409))
in (_204_1410)::[])))))))))
in (let mk_iff_interp = (fun iff tt -> (let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let valid = (let _204_1417 = (let _204_1416 = (let _204_1415 = (FStar_SMTEncoding_Term.mkApp (iff, (a)::(b)::[]))
in (_204_1415)::[])
in ("Valid", _204_1416))
in (FStar_SMTEncoding_Term.mkApp _204_1417))
in (let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _204_1424 = (let _204_1423 = (let _204_1422 = (let _204_1421 = (let _204_1420 = (let _204_1419 = (let _204_1418 = (FStar_SMTEncoding_Term.mkIff (valid_a, valid_b))
in (_204_1418, valid))
in (FStar_SMTEncoding_Term.mkIff _204_1419))
in (((valid)::[])::[], (aa)::(bb)::[], _204_1420))
in (FStar_SMTEncoding_Term.mkForall _204_1421))
in (_204_1422, Some ("<==> interpretation")))
in FStar_SMTEncoding_Term.Assume (_204_1423))
in (_204_1424)::[])))))))))
in (let mk_forall_interp = (fun for_all tt -> (let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (let valid = (let _204_1431 = (let _204_1430 = (let _204_1429 = (FStar_SMTEncoding_Term.mkApp (for_all, (a)::(b)::[]))
in (_204_1429)::[])
in ("Valid", _204_1430))
in (FStar_SMTEncoding_Term.mkApp _204_1431))
in (let valid_b_x = (let _204_1434 = (let _204_1433 = (let _204_1432 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_204_1432)::[])
in ("Valid", _204_1433))
in (FStar_SMTEncoding_Term.mkApp _204_1434))
in (let _204_1448 = (let _204_1447 = (let _204_1446 = (let _204_1445 = (let _204_1444 = (let _204_1443 = (let _204_1442 = (let _204_1441 = (let _204_1440 = (let _204_1436 = (let _204_1435 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_204_1435)::[])
in (_204_1436)::[])
in (let _204_1439 = (let _204_1438 = (let _204_1437 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_204_1437, valid_b_x))
in (FStar_SMTEncoding_Term.mkImp _204_1438))
in (_204_1440, (xx)::[], _204_1439)))
in (FStar_SMTEncoding_Term.mkForall _204_1441))
in (_204_1442, valid))
in (FStar_SMTEncoding_Term.mkIff _204_1443))
in (((valid)::[])::[], (aa)::(bb)::[], _204_1444))
in (FStar_SMTEncoding_Term.mkForall _204_1445))
in (_204_1446, Some ("forall interpretation")))
in FStar_SMTEncoding_Term.Assume (_204_1447))
in (_204_1448)::[]))))))))))
in (let mk_exists_interp = (fun for_all tt -> (let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (let valid = (let _204_1455 = (let _204_1454 = (let _204_1453 = (FStar_SMTEncoding_Term.mkApp (for_all, (a)::(b)::[]))
in (_204_1453)::[])
in ("Valid", _204_1454))
in (FStar_SMTEncoding_Term.mkApp _204_1455))
in (let valid_b_x = (let _204_1458 = (let _204_1457 = (let _204_1456 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_204_1456)::[])
in ("Valid", _204_1457))
in (FStar_SMTEncoding_Term.mkApp _204_1458))
in (let _204_1472 = (let _204_1471 = (let _204_1470 = (let _204_1469 = (let _204_1468 = (let _204_1467 = (let _204_1466 = (let _204_1465 = (let _204_1464 = (let _204_1460 = (let _204_1459 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_204_1459)::[])
in (_204_1460)::[])
in (let _204_1463 = (let _204_1462 = (let _204_1461 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_204_1461, valid_b_x))
in (FStar_SMTEncoding_Term.mkImp _204_1462))
in (_204_1464, (xx)::[], _204_1463)))
in (FStar_SMTEncoding_Term.mkExists _204_1465))
in (_204_1466, valid))
in (FStar_SMTEncoding_Term.mkIff _204_1467))
in (((valid)::[])::[], (aa)::(bb)::[], _204_1468))
in (FStar_SMTEncoding_Term.mkForall _204_1469))
in (_204_1470, Some ("exists interpretation")))
in FStar_SMTEncoding_Term.Assume (_204_1471))
in (_204_1472)::[]))))))))))
in (let prims = ((FStar_Syntax_Const.unit_lid, mk_unit))::((FStar_Syntax_Const.bool_lid, mk_bool))::((FStar_Syntax_Const.int_lid, mk_int))::((FStar_Syntax_Const.string_lid, mk_str))::((FStar_Syntax_Const.ref_lid, mk_ref))::((FStar_Syntax_Const.char_lid, mk_int_alias))::((FStar_Syntax_Const.uint8_lid, mk_int_alias))::((FStar_Syntax_Const.false_lid, mk_false_interp))::((FStar_Syntax_Const.and_lid, mk_and_interp))::((FStar_Syntax_Const.or_lid, mk_or_interp))::((FStar_Syntax_Const.eq2_lid, mk_eq2_interp))::((FStar_Syntax_Const.imp_lid, mk_imp_interp))::((FStar_Syntax_Const.iff_lid, mk_iff_interp))::((FStar_Syntax_Const.forall_lid, mk_forall_interp))::((FStar_Syntax_Const.exists_lid, mk_exists_interp))::[]
in (fun t s tt -> (match ((FStar_Util.find_opt (fun _101_1868 -> (match (_101_1868) with
| (l, _101_1867) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_101_1871, f) -> begin
(f s tt)
end)))))))))))))))))))))

let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (let _101_1877 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _204_1615 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _204_1615))
end else begin
()
end
in (let nm = (match ((FStar_Syntax_Util.lid_of_sigelt se)) with
| None -> begin
""
end
| Some (l) -> begin
l.FStar_Ident.str
end)
in (let _101_1885 = (encode_sigelt' env se)
in (match (_101_1885) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _204_1618 = (let _204_1617 = (let _204_1616 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (_204_1616))
in (_204_1617)::[])
in (_204_1618, e))
end
| _101_1888 -> begin
(let _204_1625 = (let _204_1624 = (let _204_1620 = (let _204_1619 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_204_1619))
in (_204_1620)::g)
in (let _204_1623 = (let _204_1622 = (let _204_1621 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_204_1621))
in (_204_1622)::[])
in (FStar_List.append _204_1624 _204_1623)))
in (_204_1625, e))
end)
end)))))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (let should_skip = (fun l -> false)
in (let encode_top_level_val = (fun env lid t quals -> (let tt = (whnf env t)
in (let _101_1901 = (encode_free_var env lid t tt quals)
in (match (_101_1901) with
| (decls, env) -> begin
if (FStar_Syntax_Util.is_smt_lemma t) then begin
(let _204_1639 = (let _204_1638 = (encode_smt_lemma env lid t)
in (FStar_List.append decls _204_1638))
in (_204_1639, env))
end else begin
(decls, env)
end
end))))
in (let encode_top_level_vals = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _101_1908 lb -> (match (_101_1908) with
| (decls, env) -> begin
(let _101_1912 = (let _204_1648 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env _204_1648 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (_101_1912) with
| (decls', env) -> begin
((FStar_List.append decls decls'), env)
end))
end)) ([], env))))
in (match (se) with
| (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _101_1930, _101_1932, _101_1934, _101_1936) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid) -> begin
(let _101_1942 = (new_term_constant_and_tok_from_lid env lid)
in (match (_101_1942) with
| (tname, ttok, env) -> begin
([], env)
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _101_1945, t, quals, _101_1949) -> begin
if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _101_12 -> (match (_101_12) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _101_1961 -> begin
false
end)))) || env.tcenv.FStar_TypeChecker_Env.is_iface) then begin
(let _101_1964 = (encode_top_level_val env lid t quals)
in (match (_101_1964) with
| (decls, env) -> begin
(let tname = lid.FStar_Ident.str
in (let tsym = (FStar_SMTEncoding_Term.mkFreeV (tname, FStar_SMTEncoding_Term.Term_sort))
in (let _204_1651 = (let _204_1650 = (primitive_type_axioms lid tname tsym)
in (FStar_List.append decls _204_1650))
in (_204_1651, env))))
end))
end else begin
([], env)
end
end
| FStar_Syntax_Syntax.Sig_assume (l, f, _101_1970, _101_1972) -> begin
(let _101_1977 = (encode_formula f env)
in (match (_101_1977) with
| (f, decls) -> begin
(let g = (let _204_1656 = (let _204_1655 = (let _204_1654 = (let _204_1653 = (let _204_1652 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" _204_1652))
in Some (_204_1653))
in (f, _204_1654))
in FStar_SMTEncoding_Term.Assume (_204_1655))
in (_204_1656)::[])
in ((FStar_List.append decls g), env))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _101_1982, _101_1984) when (FStar_All.pipe_right (Prims.snd lbs) (FStar_Util.for_some (fun lb -> (let _204_1658 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (should_skip _204_1658))))) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_let ((_101_1989, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t); FStar_Syntax_Syntax.lbunivs = _101_1997; FStar_Syntax_Syntax.lbtyp = _101_1995; FStar_Syntax_Syntax.lbeff = _101_1993; FStar_Syntax_Syntax.lbdef = _101_1991}::[]), _101_2004, _101_2006, _101_2008) when (FStar_Ident.lid_equals b2t FStar_Syntax_Const.b2t_lid) -> begin
(let _101_2014 = (new_term_constant_and_tok_from_lid env b2t)
in (match (_101_2014) with
| (tname, ttok, env) -> begin
(let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (let valid_b2t_x = (let _204_1661 = (let _204_1660 = (let _204_1659 = (FStar_SMTEncoding_Term.mkApp ("Prims.b2t", (x)::[]))
in (_204_1659)::[])
in ("Valid", _204_1660))
in (FStar_SMTEncoding_Term.mkApp _204_1661))
in (let decls = (let _204_1669 = (let _204_1668 = (let _204_1667 = (let _204_1666 = (let _204_1665 = (let _204_1664 = (let _204_1663 = (let _204_1662 = (FStar_SMTEncoding_Term.mkApp ("BoxBool_proj_0", (x)::[]))
in (valid_b2t_x, _204_1662))
in (FStar_SMTEncoding_Term.mkEq _204_1663))
in (((valid_b2t_x)::[])::[], (xx)::[], _204_1664))
in (FStar_SMTEncoding_Term.mkForall _204_1665))
in (_204_1666, Some ("b2t def")))
in FStar_SMTEncoding_Term.Assume (_204_1667))
in (_204_1668)::[])
in (FStar_SMTEncoding_Term.DeclFun ((tname, (FStar_SMTEncoding_Term.Term_sort)::[], FStar_SMTEncoding_Term.Term_sort, None)))::_204_1669)
in (decls, env)))))
end))
end
| FStar_Syntax_Syntax.Sig_let (_101_2020, _101_2022, _101_2024, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _101_13 -> (match (_101_13) with
| (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _101_2034 -> begin
false
end)))) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_let ((false, lb::[]), _101_2040, _101_2042, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _101_14 -> (match (_101_14) with
| FStar_Syntax_Syntax.Projector (_101_2048) -> begin
true
end
| _101_2051 -> begin
false
end)))) -> begin
(let l = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (match ((try_lookup_free_var env l)) with
| Some (_101_2054) -> begin
([], env)
end
| None -> begin
(let se = FStar_Syntax_Syntax.Sig_declare_typ ((l, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, quals, (FStar_Ident.range_of_lid l)))
in (encode_sigelt env se))
end))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), _101_2062, _101_2064, quals) -> begin
(let eta_expand = (fun binders formals body t -> (let nbinders = (FStar_List.length binders)
in (let _101_2076 = (FStar_Util.first_N nbinders formals)
in (match (_101_2076) with
| (formals, extra_formals) -> begin
(let subst = (FStar_List.map2 (fun _101_2080 _101_2084 -> (match ((_101_2080, _101_2084)) with
| ((formal, _101_2079), (binder, _101_2083)) -> begin
(let _204_1683 = (let _204_1682 = (FStar_Syntax_Syntax.bv_to_name binder)
in (formal, _204_1682))
in FStar_Syntax_Syntax.NT (_204_1683))
end)) formals binders)
in (let extra_formals = (let _204_1687 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun _101_2088 -> (match (_101_2088) with
| (x, i) -> begin
(let _204_1686 = (let _101_2089 = x
in (let _204_1685 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _101_2089.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _101_2089.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _204_1685}))
in (_204_1686, i))
end))))
in (FStar_All.pipe_right _204_1687 FStar_Syntax_Util.name_binders))
in (let body = (let _204_1694 = (FStar_Syntax_Subst.compress body)
in (let _204_1693 = (let _204_1688 = (FStar_Syntax_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _204_1688))
in (let _204_1692 = (let _204_1691 = (let _204_1690 = (FStar_Syntax_Subst.subst subst t)
in _204_1690.FStar_Syntax_Syntax.n)
in (FStar_All.pipe_left (fun _204_1689 -> Some (_204_1689)) _204_1691))
in (FStar_Syntax_Syntax.extend_app_n _204_1694 _204_1693 _204_1692 body.FStar_Syntax_Syntax.pos))))
in ((FStar_List.append binders extra_formals), body))))
end))))
in (let rec destruct_bound_function = (fun flid t_norm e -> (match ((let _204_1701 = (FStar_Syntax_Util.unascribe e)
in _204_1701.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, lopt) -> begin
(let _101_2105 = (FStar_Syntax_Subst.open_term' binders body)
in (match (_101_2105) with
| (binders, body, opening) -> begin
(match ((let _204_1702 = (FStar_Syntax_Subst.compress t_norm)
in _204_1702.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(let _101_2112 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_101_2112) with
| (formals, c) -> begin
(let nformals = (FStar_List.length formals)
in (let nbinders = (FStar_List.length binders)
in (let tres = (FStar_Syntax_Util.comp_result c)
in if ((nformals < nbinders) && (FStar_Syntax_Util.is_total_comp c)) then begin
(let lopt = (subst_lcomp_opt opening lopt)
in (let _101_2119 = (FStar_Util.first_N nformals binders)
in (match (_101_2119) with
| (bs0, rest) -> begin
(let c = (let subst = (FStar_List.map2 (fun _101_2123 _101_2127 -> (match ((_101_2123, _101_2127)) with
| ((b, _101_2122), (x, _101_2126)) -> begin
(let _204_1706 = (let _204_1705 = (FStar_Syntax_Syntax.bv_to_name x)
in (b, _204_1705))
in FStar_Syntax_Syntax.NT (_204_1706))
end)) bs0 formals)
in (FStar_Syntax_Subst.subst_comp subst c))
in (let body = (FStar_Syntax_Util.abs rest body lopt)
in (bs0, body, bs0, (FStar_Syntax_Util.comp_result c))))
end)))
end else begin
if (nformals > nbinders) then begin
(let _101_2133 = (eta_expand binders formals body tres)
in (match (_101_2133) with
| (binders, body) -> begin
(binders, body, formals, tres)
end))
end else begin
(binders, body, formals, tres)
end
end)))
end))
end
| _101_2135 -> begin
(let _204_1709 = (let _204_1708 = (FStar_Syntax_Print.term_to_string e)
in (let _204_1707 = (FStar_Syntax_Print.term_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str _204_1708 _204_1707)))
in (FStar_All.failwith _204_1709))
end)
end))
end
| _101_2137 -> begin
(match ((let _204_1710 = (FStar_Syntax_Subst.compress t_norm)
in _204_1710.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(let _101_2144 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_101_2144) with
| (formals, c) -> begin
(let tres = (FStar_Syntax_Util.comp_result c)
in (let _101_2148 = (eta_expand [] formals e tres)
in (match (_101_2148) with
| (binders, body) -> begin
(binders, body, formals, tres)
end)))
end))
end
| _101_2150 -> begin
([], e, [], t_norm)
end)
end))
in (FStar_All.try_with (fun _101_2152 -> (match (()) with
| () -> begin
if (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp)))) then begin
(encode_top_level_vals env bindings quals)
end else begin
(let _101_2178 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _101_2165 lb -> (match (_101_2165) with
| (toks, typs, decls, env) -> begin
(let _101_2167 = if (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) then begin
(Prims.raise Let_rec_unencodeable)
end else begin
()
end
in (let t_norm = (whnf env lb.FStar_Syntax_Syntax.lbtyp)
in (let _101_2173 = (let _204_1715 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env _204_1715 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (_101_2173) with
| (tok, decl, env) -> begin
(let _204_1718 = (let _204_1717 = (let _204_1716 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (_204_1716, tok))
in (_204_1717)::toks)
in (_204_1718, (t_norm)::typs, (decl)::decls, env))
end))))
end)) ([], [], [], env)))
in (match (_101_2178) with
| (toks, typs, decls, env) -> begin
(let toks = (FStar_List.rev toks)
in (let decls = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (let typs = (FStar_List.rev typs)
in if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _101_15 -> (match (_101_15) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| _101_2185 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> (let _204_1721 = (FStar_Syntax_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _204_1721)))))) then begin
(decls, env)
end else begin
if (not (is_rec)) then begin
(match ((bindings, typs, toks)) with
| ({FStar_Syntax_Syntax.lbname = _101_2195; FStar_Syntax_Syntax.lbunivs = _101_2193; FStar_Syntax_Syntax.lbtyp = _101_2191; FStar_Syntax_Syntax.lbeff = _101_2189; FStar_Syntax_Syntax.lbdef = e}::[], t_norm::[], (flid, (f, ftok))::[]) -> begin
(let e = (FStar_Syntax_Subst.compress e)
in (let _101_2214 = (destruct_bound_function flid t_norm e)
in (match (_101_2214) with
| (binders, body, _101_2211, _101_2213) -> begin
(let _101_2221 = (encode_binders None binders env)
in (match (_101_2221) with
| (vars, guards, env', binder_decls, _101_2220) -> begin
(let app = (match (vars) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV (f, FStar_SMTEncoding_Term.Term_sort))
end
| _101_2224 -> begin
(let _204_1723 = (let _204_1722 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (f, _204_1722))
in (FStar_SMTEncoding_Term.mkApp _204_1723))
end)
in (let _101_2230 = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic)) then begin
(let _204_1725 = (FStar_SMTEncoding_Term.mk_Valid app)
in (let _204_1724 = (encode_formula body env')
in (_204_1725, _204_1724)))
end else begin
(let _204_1726 = (encode_term body env')
in (app, _204_1726))
end
in (match (_101_2230) with
| (app, (body, decls2)) -> begin
(let eqn = (let _204_1735 = (let _204_1734 = (let _204_1731 = (let _204_1730 = (let _204_1729 = (let _204_1728 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (let _204_1727 = (FStar_SMTEncoding_Term.mkEq (app, body))
in (_204_1728, _204_1727)))
in (FStar_SMTEncoding_Term.mkImp _204_1729))
in (((app)::[])::[], vars, _204_1730))
in (FStar_SMTEncoding_Term.mkForall _204_1731))
in (let _204_1733 = (let _204_1732 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (_204_1732))
in (_204_1734, _204_1733)))
in FStar_SMTEncoding_Term.Assume (_204_1735))
in ((FStar_List.append (FStar_List.append (FStar_List.append decls binder_decls) decls2) ((eqn)::[])), env))
end)))
end))
end)))
end
| _101_2233 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(let fuel = (let _204_1736 = (varops.fresh "fuel")
in (_204_1736, FStar_SMTEncoding_Term.Fuel_sort))
in (let fuel_tm = (FStar_SMTEncoding_Term.mkFreeV fuel)
in (let env0 = env
in (let _101_2250 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _101_2239 _101_2244 -> (match ((_101_2239, _101_2244)) with
| ((gtoks, env), (flid, (f, ftok))) -> begin
(let g = (varops.new_fvar flid)
in (let gtok = (varops.new_fvar flid)
in (let env = (let _204_1741 = (let _204_1740 = (FStar_SMTEncoding_Term.mkApp (g, (fuel_tm)::[]))
in (FStar_All.pipe_left (fun _204_1739 -> Some (_204_1739)) _204_1740))
in (push_free_var env flid gtok _204_1741))
in (((flid, f, ftok, g, gtok))::gtoks, env))))
end)) ([], env)))
in (match (_101_2250) with
| (gtoks, env) -> begin
(let gtoks = (FStar_List.rev gtoks)
in (let encode_one_binding = (fun env0 _101_2259 t_norm _101_2270 -> (match ((_101_2259, _101_2270)) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = _101_2269; FStar_Syntax_Syntax.lbunivs = _101_2267; FStar_Syntax_Syntax.lbtyp = _101_2265; FStar_Syntax_Syntax.lbeff = _101_2263; FStar_Syntax_Syntax.lbdef = e}) -> begin
(let _101_2275 = (destruct_bound_function flid t_norm e)
in (match (_101_2275) with
| (binders, body, formals, tres) -> begin
(let _101_2282 = (encode_binders None binders env)
in (match (_101_2282) with
| (vars, guards, env', binder_decls, _101_2281) -> begin
(let decl_g = (let _204_1752 = (let _204_1751 = (let _204_1750 = (FStar_List.map Prims.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::_204_1750)
in (g, _204_1751, FStar_SMTEncoding_Term.Term_sort, Some ("Fuel-instrumented function name")))
in FStar_SMTEncoding_Term.DeclFun (_204_1752))
in (let env0 = (push_zfuel_name env0 flid g)
in (let decl_g_tok = FStar_SMTEncoding_Term.DeclFun ((gtok, [], FStar_SMTEncoding_Term.Term_sort, Some ("Token for fuel-instrumented partial applications")))
in (let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (let app = (FStar_SMTEncoding_Term.mkApp (f, vars_tm))
in (let gsapp = (let _204_1755 = (let _204_1754 = (let _204_1753 = (FStar_SMTEncoding_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (_204_1753)::vars_tm)
in (g, _204_1754))
in (FStar_SMTEncoding_Term.mkApp _204_1755))
in (let gmax = (let _204_1758 = (let _204_1757 = (let _204_1756 = (FStar_SMTEncoding_Term.mkApp ("MaxFuel", []))
in (_204_1756)::vars_tm)
in (g, _204_1757))
in (FStar_SMTEncoding_Term.mkApp _204_1758))
in (let _101_2292 = (encode_term body env')
in (match (_101_2292) with
| (body_tm, decls2) -> begin
(let eqn_g = (let _204_1767 = (let _204_1766 = (let _204_1763 = (let _204_1762 = (let _204_1761 = (let _204_1760 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (let _204_1759 = (FStar_SMTEncoding_Term.mkEq (gsapp, body_tm))
in (_204_1760, _204_1759)))
in (FStar_SMTEncoding_Term.mkImp _204_1761))
in (((gsapp)::[])::[], (fuel)::vars, _204_1762))
in (FStar_SMTEncoding_Term.mkForall _204_1763))
in (let _204_1765 = (let _204_1764 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (_204_1764))
in (_204_1766, _204_1765)))
in FStar_SMTEncoding_Term.Assume (_204_1767))
in (let eqn_f = (let _204_1771 = (let _204_1770 = (let _204_1769 = (let _204_1768 = (FStar_SMTEncoding_Term.mkEq (app, gmax))
in (((app)::[])::[], vars, _204_1768))
in (FStar_SMTEncoding_Term.mkForall _204_1769))
in (_204_1770, Some ("Correspondence of recursive function to instrumented version")))
in FStar_SMTEncoding_Term.Assume (_204_1771))
in (let eqn_g' = (let _204_1780 = (let _204_1779 = (let _204_1778 = (let _204_1777 = (let _204_1776 = (let _204_1775 = (let _204_1774 = (let _204_1773 = (let _204_1772 = (FStar_SMTEncoding_Term.n_fuel 0)
in (_204_1772)::vars_tm)
in (g, _204_1773))
in (FStar_SMTEncoding_Term.mkApp _204_1774))
in (gsapp, _204_1775))
in (FStar_SMTEncoding_Term.mkEq _204_1776))
in (((gsapp)::[])::[], (fuel)::vars, _204_1777))
in (FStar_SMTEncoding_Term.mkForall _204_1778))
in (_204_1779, Some ("Fuel irrelevance")))
in FStar_SMTEncoding_Term.Assume (_204_1780))
in (let _101_2315 = (let _101_2302 = (encode_binders None formals env0)
in (match (_101_2302) with
| (vars, v_guards, env, binder_decls, _101_2301) -> begin
(let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (let gapp = (FStar_SMTEncoding_Term.mkApp (g, (fuel_tm)::vars_tm))
in (let tok_corr = (let tok_app = (let _204_1781 = (FStar_SMTEncoding_Term.mkFreeV (gtok, FStar_SMTEncoding_Term.Term_sort))
in (mk_Apply _204_1781 ((fuel)::vars)))
in (let _204_1785 = (let _204_1784 = (let _204_1783 = (let _204_1782 = (FStar_SMTEncoding_Term.mkEq (tok_app, gapp))
in (((tok_app)::[])::[], (fuel)::vars, _204_1782))
in (FStar_SMTEncoding_Term.mkForall _204_1783))
in (_204_1784, Some ("Fuel token correspondence")))
in FStar_SMTEncoding_Term.Assume (_204_1785)))
in (let _101_2312 = (let _101_2309 = (encode_term_pred None tres env gapp)
in (match (_101_2309) with
| (g_typing, d3) -> begin
(let _204_1793 = (let _204_1792 = (let _204_1791 = (let _204_1790 = (let _204_1789 = (let _204_1788 = (let _204_1787 = (let _204_1786 = (FStar_SMTEncoding_Term.mk_and_l v_guards)
in (_204_1786, g_typing))
in (FStar_SMTEncoding_Term.mkImp _204_1787))
in (((gapp)::[])::[], (fuel)::vars, _204_1788))
in (FStar_SMTEncoding_Term.mkForall _204_1789))
in (_204_1790, None))
in FStar_SMTEncoding_Term.Assume (_204_1791))
in (_204_1792)::[])
in (d3, _204_1793))
end))
in (match (_101_2312) with
| (aux_decls, typing_corr) -> begin
((FStar_List.append binder_decls aux_decls), (FStar_List.append typing_corr ((tok_corr)::[])))
end)))))
end))
in (match (_101_2315) with
| (aux_decls, g_typing) -> begin
((FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) aux_decls) ((decl_g)::(decl_g_tok)::[])), (FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing), env0)
end)))))
end)))))))))
end))
end))
end))
in (let _101_2331 = (let _204_1796 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _101_2319 _101_2323 -> (match ((_101_2319, _101_2323)) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(let _101_2327 = (encode_one_binding env0 gtok ty bs)
in (match (_101_2327) with
| (decls', eqns', env0) -> begin
((decls')::decls, (FStar_List.append eqns' eqns), env0)
end))
end)) ((decls)::[], [], env0) _204_1796))
in (match (_101_2331) with
| (decls, eqns, env0) -> begin
(let _101_2340 = (let _204_1798 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _204_1798 (FStar_List.partition (fun _101_16 -> (match (_101_16) with
| FStar_SMTEncoding_Term.DeclFun (_101_2334) -> begin
true
end
| _101_2337 -> begin
false
end)))))
in (match (_101_2340) with
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
end)) (fun _101_2151 -> (match (_101_2151) with
| Let_rec_unencodeable -> begin
(let msg = (let _204_1801 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _204_1801 (FStar_String.concat " and ")))
in (let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in ((decl)::[], env)))
end)))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _101_2344, _101_2346, _101_2348) -> begin
(let _101_2353 = (encode_signature env ses)
in (match (_101_2353) with
| (g, env) -> begin
(let _101_2365 = (FStar_All.pipe_right g (FStar_List.partition (fun _101_17 -> (match (_101_17) with
| FStar_SMTEncoding_Term.Assume (_101_2356, Some ("inversion axiom")) -> begin
false
end
| _101_2362 -> begin
true
end))))
in (match (_101_2365) with
| (g', inversions) -> begin
(let _101_2374 = (FStar_All.pipe_right g' (FStar_List.partition (fun _101_18 -> (match (_101_18) with
| FStar_SMTEncoding_Term.DeclFun (_101_2368) -> begin
true
end
| _101_2371 -> begin
false
end))))
in (match (_101_2374) with
| (decls, rest) -> begin
((FStar_List.append (FStar_List.append decls rest) inversions), env)
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, _101_2377, tps, k, _101_2381, datas, quals, _101_2385) -> begin
(let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _101_19 -> (match (_101_19) with
| (FStar_Syntax_Syntax.Logic) | (FStar_Syntax_Syntax.Assumption) -> begin
true
end
| _101_2392 -> begin
false
end))))
in (let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(let _101_2402 = c
in (match (_101_2402) with
| (name, args, _101_2399, _101_2401) -> begin
(let _204_1809 = (let _204_1808 = (let _204_1807 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in (name, _204_1807, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_204_1808))
in (_204_1809)::[])
end))
end else begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end)
in (let inversion_axioms = (fun tapp vars -> if (((FStar_List.length datas) = 0) || (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _204_1815 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right _204_1815 FStar_Option.isNone)))))) then begin
[]
end else begin
(let _101_2409 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_101_2409) with
| (xxsym, xx) -> begin
(let _101_2445 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _101_2412 l -> (match (_101_2412) with
| (out, decls) -> begin
(let _101_2417 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (_101_2417) with
| (_101_2415, data_t) -> begin
(let _101_2420 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (_101_2420) with
| (args, res) -> begin
(let indices = (match ((let _204_1818 = (FStar_Syntax_Subst.compress res)
in _204_1818.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_101_2422, indices) -> begin
indices
end
| _101_2427 -> begin
[]
end)
in (let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env _101_2433 -> (match (_101_2433) with
| (x, _101_2432) -> begin
(let _204_1823 = (let _204_1822 = (let _204_1821 = (mk_term_projector_name l x)
in (_204_1821, (xx)::[]))
in (FStar_SMTEncoding_Term.mkApp _204_1822))
in (push_term_var env x _204_1823))
end)) env))
in (let _101_2437 = (encode_args indices env)
in (match (_101_2437) with
| (indices, decls') -> begin
(let _101_2438 = if ((FStar_List.length indices) <> (FStar_List.length vars)) then begin
(FStar_All.failwith "Impossible")
end else begin
()
end
in (let eqs = (let _204_1828 = (FStar_List.map2 (fun v a -> (let _204_1827 = (let _204_1826 = (FStar_SMTEncoding_Term.mkFreeV v)
in (_204_1826, a))
in (FStar_SMTEncoding_Term.mkEq _204_1827))) vars indices)
in (FStar_All.pipe_right _204_1828 FStar_SMTEncoding_Term.mk_and_l))
in (let _204_1833 = (let _204_1832 = (let _204_1831 = (let _204_1830 = (let _204_1829 = (mk_data_tester env l xx)
in (_204_1829, eqs))
in (FStar_SMTEncoding_Term.mkAnd _204_1830))
in (out, _204_1831))
in (FStar_SMTEncoding_Term.mkOr _204_1832))
in (_204_1833, (FStar_List.append decls decls')))))
end))))
end))
end))
end)) (FStar_SMTEncoding_Term.mkFalse, [])))
in (match (_101_2445) with
| (data_ax, decls) -> begin
(let _101_2448 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_101_2448) with
| (ffsym, ff) -> begin
(let xx_has_type = (let _204_1834 = (FStar_SMTEncoding_Term.mkApp ("SFuel", (ff)::[]))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel _204_1834 xx tapp))
in (let _204_1841 = (let _204_1840 = (let _204_1839 = (let _204_1838 = (let _204_1837 = (let _204_1836 = (add_fuel (ffsym, FStar_SMTEncoding_Term.Fuel_sort) (((xxsym, FStar_SMTEncoding_Term.Term_sort))::vars))
in (let _204_1835 = (FStar_SMTEncoding_Term.mkImp (xx_has_type, data_ax))
in (((xx_has_type)::[])::[], _204_1836, _204_1835)))
in (FStar_SMTEncoding_Term.mkForall _204_1837))
in (_204_1838, Some ("inversion axiom")))
in FStar_SMTEncoding_Term.Assume (_204_1839))
in (_204_1840)::[])
in (FStar_List.append decls _204_1841)))
end))
end))
end))
end)
in (let _101_2458 = (match ((let _204_1842 = (FStar_Syntax_Subst.compress k)
in _204_1842.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
((FStar_List.append tps formals), (FStar_Syntax_Util.comp_result kres))
end
| _101_2455 -> begin
(tps, k)
end)
in (match (_101_2458) with
| (formals, res) -> begin
(let _101_2461 = (FStar_Syntax_Subst.open_term formals res)
in (match (_101_2461) with
| (formals, res) -> begin
(let _101_2468 = (encode_binders None formals env)
in (match (_101_2468) with
| (vars, guards, env', binder_decls, _101_2467) -> begin
(let pretype_axioms = (fun tapp vars -> (let _101_2474 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_101_2474) with
| (xxsym, xx) -> begin
(let _101_2477 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_101_2477) with
| (ffsym, ff) -> begin
(let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (let _204_1855 = (let _204_1854 = (let _204_1853 = (let _204_1852 = (let _204_1851 = (let _204_1850 = (let _204_1849 = (let _204_1848 = (let _204_1847 = (FStar_SMTEncoding_Term.mkApp ("PreType", (xx)::[]))
in (tapp, _204_1847))
in (FStar_SMTEncoding_Term.mkEq _204_1848))
in (xx_has_type, _204_1849))
in (FStar_SMTEncoding_Term.mkImp _204_1850))
in (((xx_has_type)::[])::[], ((xxsym, FStar_SMTEncoding_Term.Term_sort))::((ffsym, FStar_SMTEncoding_Term.Fuel_sort))::vars, _204_1851))
in (FStar_SMTEncoding_Term.mkForall _204_1852))
in (_204_1853, Some ("pretyping")))
in FStar_SMTEncoding_Term.Assume (_204_1854))
in (_204_1855)::[]))
end))
end)))
in (let _101_2482 = (new_term_constant_and_tok_from_lid env t)
in (match (_101_2482) with
| (tname, ttok, env) -> begin
(let ttok_tm = (FStar_SMTEncoding_Term.mkApp (ttok, []))
in (let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (let tapp = (let _204_1857 = (let _204_1856 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (tname, _204_1856))
in (FStar_SMTEncoding_Term.mkApp _204_1857))
in (let _101_2503 = (let tname_decl = (let _204_1861 = (let _204_1860 = (FStar_All.pipe_right vars (FStar_List.map (fun _101_2488 -> (match (_101_2488) with
| (n, s) -> begin
((Prims.strcat tname n), s)
end))))
in (let _204_1859 = (varops.next_id ())
in (tname, _204_1860, FStar_SMTEncoding_Term.Term_sort, _204_1859)))
in (constructor_or_logic_type_decl _204_1861))
in (let _101_2500 = (match (vars) with
| [] -> begin
(let _204_1865 = (let _204_1864 = (let _204_1863 = (FStar_SMTEncoding_Term.mkApp (tname, []))
in (FStar_All.pipe_left (fun _204_1862 -> Some (_204_1862)) _204_1863))
in (push_free_var env t tname _204_1864))
in ([], _204_1865))
end
| _101_2492 -> begin
(let ttok_decl = FStar_SMTEncoding_Term.DeclFun ((ttok, [], FStar_SMTEncoding_Term.Term_sort, Some ("token")))
in (let ttok_fresh = (let _204_1866 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (ttok, FStar_SMTEncoding_Term.Term_sort) _204_1866))
in (let ttok_app = (mk_Apply ttok_tm vars)
in (let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (let name_tok_corr = (let _204_1870 = (let _204_1869 = (let _204_1868 = (let _204_1867 = (FStar_SMTEncoding_Term.mkEq (ttok_app, tapp))
in (pats, None, vars, _204_1867))
in (FStar_SMTEncoding_Term.mkForall' _204_1868))
in (_204_1869, Some ("name-token correspondence")))
in FStar_SMTEncoding_Term.Assume (_204_1870))
in ((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[], env))))))
end)
in (match (_101_2500) with
| (tok_decls, env) -> begin
((FStar_List.append tname_decl tok_decls), env)
end)))
in (match (_101_2503) with
| (decls, env) -> begin
(let kindingAx = (let _101_2506 = (encode_term_pred None res env' tapp)
in (match (_101_2506) with
| (k, decls) -> begin
(let karr = if ((FStar_List.length formals) > 0) then begin
(let _204_1874 = (let _204_1873 = (let _204_1872 = (let _204_1871 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _204_1871))
in (_204_1872, Some ("kinding")))
in FStar_SMTEncoding_Term.Assume (_204_1873))
in (_204_1874)::[])
end else begin
[]
end
in (let _204_1880 = (let _204_1879 = (let _204_1878 = (let _204_1877 = (let _204_1876 = (let _204_1875 = (FStar_SMTEncoding_Term.mkImp (guard, k))
in (((tapp)::[])::[], vars, _204_1875))
in (FStar_SMTEncoding_Term.mkForall _204_1876))
in (_204_1877, Some ("kinding")))
in FStar_SMTEncoding_Term.Assume (_204_1878))
in (_204_1879)::[])
in (FStar_List.append (FStar_List.append decls karr) _204_1880)))
end))
in (let aux = (let _204_1883 = (let _204_1881 = (inversion_axioms tapp vars)
in (FStar_List.append kindingAx _204_1881))
in (let _204_1882 = (pretype_axioms tapp vars)
in (FStar_List.append _204_1883 _204_1882)))
in (let g = (FStar_List.append (FStar_List.append decls binder_decls) aux)
in (g, env))))
end)))))
end)))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, _101_2513, _101_2515, _101_2517, _101_2519, _101_2521, _101_2523, _101_2525) when (FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_datacon (d, _101_2530, t, _101_2533, n_tps, quals, _101_2537, drange) -> begin
(let _101_2544 = (new_term_constant_and_tok_from_lid env d)
in (match (_101_2544) with
| (ddconstrsym, ddtok, env) -> begin
(let ddtok_tm = (FStar_SMTEncoding_Term.mkApp (ddtok, []))
in (let _101_2548 = (FStar_Syntax_Util.arrow_formals t)
in (match (_101_2548) with
| (formals, t_res) -> begin
(let _101_2551 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_101_2551) with
| (fuel_var, fuel_tm) -> begin
(let s_fuel_tm = (FStar_SMTEncoding_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (let _101_2558 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_101_2558) with
| (vars, guards, env', binder_decls, names) -> begin
(let projectors = (FStar_All.pipe_right names (FStar_List.map (fun x -> (let _204_1885 = (mk_term_projector_name d x)
in (_204_1885, FStar_SMTEncoding_Term.Term_sort)))))
in (let datacons = (let _204_1887 = (let _204_1886 = (varops.next_id ())
in (ddconstrsym, projectors, FStar_SMTEncoding_Term.Term_sort, _204_1886))
in (FStar_All.pipe_right _204_1887 FStar_SMTEncoding_Term.constructor_to_decl))
in (let app = (mk_Apply ddtok_tm vars)
in (let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (let _101_2568 = (encode_term_pred None t env ddtok_tm)
in (match (_101_2568) with
| (tok_typing, decls3) -> begin
(let _101_2575 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_101_2575) with
| (vars', guards', env'', decls_formals, _101_2574) -> begin
(let _101_2580 = (let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars')
in (let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (encode_term_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_101_2580) with
| (ty_pred', decls_pred) -> begin
(let guard' = (FStar_SMTEncoding_Term.mk_and_l guards')
in (let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _101_2584 -> begin
(let _204_1889 = (let _204_1888 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (ddtok, FStar_SMTEncoding_Term.Term_sort) _204_1888))
in (_204_1889)::[])
end)
in (let encode_elim = (fun _101_2587 -> (match (()) with
| () -> begin
(let _101_2590 = (FStar_Syntax_Util.head_and_args t_res)
in (match (_101_2590) with
| (head, args) -> begin
(match ((let _204_1892 = (FStar_Syntax_Subst.compress head)
in _204_1892.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv, _)) -> begin
(let encoded_head = (lookup_free_var_name env' fv)
in (let _101_2614 = (encode_args args env')
in (match (_101_2614) with
| (encoded_args, arg_decls) -> begin
(let _101_2629 = (FStar_List.fold_left (fun _101_2618 arg -> (match (_101_2618) with
| (env, arg_vars, eqns) -> begin
(let _101_2624 = (let _204_1895 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in (gen_term_var env _204_1895))
in (match (_101_2624) with
| (_101_2621, xv, env) -> begin
(let _204_1897 = (let _204_1896 = (FStar_SMTEncoding_Term.mkEq (arg, xv))
in (_204_1896)::eqns)
in (env, (xv)::arg_vars, _204_1897))
end))
end)) (env', [], []) encoded_args)
in (match (_101_2629) with
| (_101_2626, arg_vars, eqns) -> begin
(let arg_vars = (FStar_List.rev arg_vars)
in (let ty = (FStar_SMTEncoding_Term.mkApp (encoded_head, arg_vars))
in (let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (let ty_pred = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp ty)
in (let arg_binders = (FStar_List.map FStar_SMTEncoding_Term.fv_of_term arg_vars)
in (let typing_inversion = (let _204_1904 = (let _204_1903 = (let _204_1902 = (let _204_1901 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _204_1900 = (let _204_1899 = (let _204_1898 = (FStar_SMTEncoding_Term.mk_and_l (FStar_List.append eqns guards))
in (ty_pred, _204_1898))
in (FStar_SMTEncoding_Term.mkImp _204_1899))
in (((ty_pred)::[])::[], _204_1901, _204_1900)))
in (FStar_SMTEncoding_Term.mkForall _204_1902))
in (_204_1903, Some ("data constructor typing elim")))
in FStar_SMTEncoding_Term.Assume (_204_1904))
in (let subterm_ordering = if (FStar_Ident.lid_equals d FStar_Syntax_Const.lextop_lid) then begin
(let x = (let _204_1905 = (varops.fresh "x")
in (_204_1905, FStar_SMTEncoding_Term.Term_sort))
in (let xtm = (FStar_SMTEncoding_Term.mkFreeV x)
in (let _204_1915 = (let _204_1914 = (let _204_1913 = (let _204_1912 = (let _204_1907 = (let _204_1906 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in (_204_1906)::[])
in (_204_1907)::[])
in (let _204_1911 = (let _204_1910 = (let _204_1909 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (let _204_1908 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in (_204_1909, _204_1908)))
in (FStar_SMTEncoding_Term.mkImp _204_1910))
in (_204_1912, (x)::[], _204_1911)))
in (FStar_SMTEncoding_Term.mkForall _204_1913))
in (_204_1914, Some ("lextop is top")))
in FStar_SMTEncoding_Term.Assume (_204_1915))))
end else begin
(let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
[]
end
| FStar_SMTEncoding_Term.Term_sort -> begin
(let _204_1918 = (let _204_1917 = (FStar_SMTEncoding_Term.mkFreeV v)
in (FStar_SMTEncoding_Term.mk_Precedes _204_1917 dapp))
in (_204_1918)::[])
end
| _101_2643 -> begin
(FStar_All.failwith "unexpected sort")
end))))
in (let _204_1925 = (let _204_1924 = (let _204_1923 = (let _204_1922 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _204_1921 = (let _204_1920 = (let _204_1919 = (FStar_SMTEncoding_Term.mk_and_l prec)
in (ty_pred, _204_1919))
in (FStar_SMTEncoding_Term.mkImp _204_1920))
in (((ty_pred)::[])::[], _204_1922, _204_1921)))
in (FStar_SMTEncoding_Term.mkForall _204_1923))
in (_204_1924, Some ("subterm ordering")))
in FStar_SMTEncoding_Term.Assume (_204_1925)))
end
in (arg_decls, (typing_inversion)::(subterm_ordering)::[])))))))))
end))
end)))
end
| _101_2647 -> begin
(let _101_2648 = (let _204_1928 = (let _204_1927 = (FStar_Syntax_Print.lid_to_string d)
in (let _204_1926 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _204_1927 _204_1926)))
in (FStar_TypeChecker_Errors.warn drange _204_1928))
in ([], []))
end)
end))
end))
in (let _101_2652 = (encode_elim ())
in (match (_101_2652) with
| (decls2, elim) -> begin
(let g = (let _204_1953 = (let _204_1952 = (let _204_1937 = (let _204_1936 = (let _204_1935 = (let _204_1934 = (let _204_1933 = (let _204_1932 = (let _204_1931 = (let _204_1930 = (let _204_1929 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" _204_1929))
in Some (_204_1930))
in (ddtok, [], FStar_SMTEncoding_Term.Term_sort, _204_1931))
in FStar_SMTEncoding_Term.DeclFun (_204_1932))
in (_204_1933)::[])
in (FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) decls3) _204_1934))
in (FStar_List.append _204_1935 proxy_fresh))
in (FStar_List.append _204_1936 decls_formals))
in (FStar_List.append _204_1937 decls_pred))
in (let _204_1951 = (let _204_1950 = (let _204_1949 = (let _204_1941 = (let _204_1940 = (let _204_1939 = (let _204_1938 = (FStar_SMTEncoding_Term.mkEq (app, dapp))
in (((app)::[])::[], vars, _204_1938))
in (FStar_SMTEncoding_Term.mkForall _204_1939))
in (_204_1940, Some ("equality for proxy")))
in FStar_SMTEncoding_Term.Assume (_204_1941))
in (let _204_1948 = (let _204_1947 = (let _204_1946 = (let _204_1945 = (let _204_1944 = (let _204_1943 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) vars')
in (let _204_1942 = (FStar_SMTEncoding_Term.mkImp (guard', ty_pred'))
in (((ty_pred')::[])::[], _204_1943, _204_1942)))
in (FStar_SMTEncoding_Term.mkForall _204_1944))
in (_204_1945, Some ("data constructor typing intro")))
in FStar_SMTEncoding_Term.Assume (_204_1946))
in (_204_1947)::[])
in (_204_1949)::_204_1948))
in (FStar_SMTEncoding_Term.Assume ((tok_typing, Some ("typing for data constructor proxy"))))::_204_1950)
in (FStar_List.append _204_1952 _204_1951)))
in (FStar_List.append _204_1953 elim))
in ((FStar_List.append datacons g), env))
end)))))
end))
end))
end))))))))
end)))
end))
end)))
end))
end)))))
and declare_top_level_let : env_t  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  ((Prims.string * FStar_SMTEncoding_Term.term Prims.option) * FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env x t t_norm -> (match ((try_lookup_lid env x)) with
| None -> begin
(let _101_2661 = (encode_free_var env x t t_norm [])
in (match (_101_2661) with
| (decls, env) -> begin
(let _101_2666 = (lookup_lid env x)
in (match (_101_2666) with
| (n, x', _101_2665) -> begin
((n, x'), decls, env)
end))
end))
end
| Some (n, x, _101_2670) -> begin
((n, x), [], env)
end))
and encode_smt_lemma : env_t  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env lid t -> (let _101_2678 = (encode_function_type_as_formula None None t env)
in (match (_101_2678) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_SMTEncoding_Term.Assume ((form, Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str)))))::[]))
end)))
and encode_free_var : env_t  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env lid tt t_norm quals -> if ((let _204_1966 = (FStar_Syntax_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _204_1966)) || (FStar_Syntax_Util.is_lemma t_norm)) then begin
(let _101_2687 = (new_term_constant_and_tok_from_lid env lid)
in (match (_101_2687) with
| (vname, vtok, env) -> begin
(let arg_sorts = (match ((let _204_1967 = (FStar_Syntax_Subst.compress t_norm)
in _204_1967.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _101_2690) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun _101_2693 -> FStar_SMTEncoding_Term.Term_sort)))
end
| _101_2696 -> begin
[]
end)
in (let d = FStar_SMTEncoding_Term.DeclFun ((vname, arg_sorts, FStar_SMTEncoding_Term.Term_sort, Some ("Uninterpreted function symbol for impure function")))
in (let dd = FStar_SMTEncoding_Term.DeclFun ((vtok, [], FStar_SMTEncoding_Term.Term_sort, Some ("Uninterpreted name for impure function")))
in ((d)::(dd)::[], env))))
end))
end else begin
if (prims.is lid) then begin
(let vname = (varops.new_fvar lid)
in (let definition = (prims.mk lid vname)
in (let env = (push_free_var env lid vname None)
in (definition, env))))
end else begin
(let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (let _101_2711 = (let _101_2706 = (FStar_Syntax_Util.arrow_formals_comp t_norm)
in (match (_101_2706) with
| (args, comp) -> begin
if encode_non_total_function_typ then begin
(let _204_1969 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in (args, _204_1969))
end else begin
(args, (None, (FStar_Syntax_Util.comp_result comp)))
end
end))
in (match (_101_2711) with
| (formals, (pre_opt, res_t)) -> begin
(let _101_2715 = (new_term_constant_and_tok_from_lid env lid)
in (match (_101_2715) with
| (vname, vtok, env) -> begin
(let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV (vname, FStar_SMTEncoding_Term.Term_sort))
end
| _101_2718 -> begin
(FStar_SMTEncoding_Term.mkApp (vtok, []))
end)
in (let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun _101_20 -> (match (_101_20) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(let _101_2734 = (FStar_Util.prefix vars)
in (match (_101_2734) with
| (_101_2729, (xxsym, _101_2732)) -> begin
(let xx = (FStar_SMTEncoding_Term.mkFreeV (xxsym, FStar_SMTEncoding_Term.Term_sort))
in (let _204_1986 = (let _204_1985 = (let _204_1984 = (let _204_1983 = (let _204_1982 = (let _204_1981 = (let _204_1980 = (let _204_1979 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _204_1979))
in (vapp, _204_1980))
in (FStar_SMTEncoding_Term.mkEq _204_1981))
in (((vapp)::[])::[], vars, _204_1982))
in (FStar_SMTEncoding_Term.mkForall _204_1983))
in (_204_1984, Some ("Discriminator equation")))
in FStar_SMTEncoding_Term.Assume (_204_1985))
in (_204_1986)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(let _101_2746 = (FStar_Util.prefix vars)
in (match (_101_2746) with
| (_101_2741, (xxsym, _101_2744)) -> begin
(let xx = (FStar_SMTEncoding_Term.mkFreeV (xxsym, FStar_SMTEncoding_Term.Term_sort))
in (let f = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = 0; FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (let prim_app = (let _204_1988 = (let _204_1987 = (mk_term_projector_name d f)
in (_204_1987, (xx)::[]))
in (FStar_SMTEncoding_Term.mkApp _204_1988))
in (let _204_1993 = (let _204_1992 = (let _204_1991 = (let _204_1990 = (let _204_1989 = (FStar_SMTEncoding_Term.mkEq (vapp, prim_app))
in (((vapp)::[])::[], vars, _204_1989))
in (FStar_SMTEncoding_Term.mkForall _204_1990))
in (_204_1991, Some ("Projector equation")))
in FStar_SMTEncoding_Term.Assume (_204_1992))
in (_204_1993)::[]))))
end))
end
| _101_2751 -> begin
[]
end)))))
in (let _101_2758 = (encode_binders None formals env)
in (match (_101_2758) with
| (vars, guards, env', decls1, _101_2757) -> begin
(let _101_2767 = (match (pre_opt) with
| None -> begin
(let _204_1994 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_204_1994, decls1))
end
| Some (p) -> begin
(let _101_2764 = (encode_formula p env')
in (match (_101_2764) with
| (g, ds) -> begin
(let _204_1995 = (FStar_SMTEncoding_Term.mk_and_l ((g)::guards))
in (_204_1995, (FStar_List.append decls1 ds)))
end))
end)
in (match (_101_2767) with
| (guard, decls1) -> begin
(let vtok_app = (mk_Apply vtok_tm vars)
in (let vapp = (let _204_1997 = (let _204_1996 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (vname, _204_1996))
in (FStar_SMTEncoding_Term.mkApp _204_1997))
in (let _101_2791 = (let vname_decl = (let _204_2000 = (let _204_1999 = (FStar_All.pipe_right formals (FStar_List.map (fun _101_2770 -> FStar_SMTEncoding_Term.Term_sort)))
in (vname, _204_1999, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_204_2000))
in (let _101_2778 = (let env = (let _101_2773 = env
in {bindings = _101_2773.bindings; depth = _101_2773.depth; tcenv = _101_2773.tcenv; warn = _101_2773.warn; cache = _101_2773.cache; nolabels = _101_2773.nolabels; use_zfuel_name = _101_2773.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in if (not ((head_normal env tt))) then begin
(encode_term_pred None tt env vtok_tm)
end else begin
(encode_term_pred None t_norm env vtok_tm)
end)
in (match (_101_2778) with
| (tok_typing, decls2) -> begin
(let tok_typing = FStar_SMTEncoding_Term.Assume ((tok_typing, Some ("function token typing")))
in (let _101_2788 = (match (formals) with
| [] -> begin
(let _204_2004 = (let _204_2003 = (let _204_2002 = (FStar_SMTEncoding_Term.mkFreeV (vname, FStar_SMTEncoding_Term.Term_sort))
in (FStar_All.pipe_left (fun _204_2001 -> Some (_204_2001)) _204_2002))
in (push_free_var env lid vname _204_2003))
in ((FStar_List.append decls2 ((tok_typing)::[])), _204_2004))
end
| _101_2782 -> begin
(let vtok_decl = FStar_SMTEncoding_Term.DeclFun ((vtok, [], FStar_SMTEncoding_Term.Term_sort, None))
in (let vtok_fresh = (let _204_2005 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (vtok, FStar_SMTEncoding_Term.Term_sort) _204_2005))
in (let name_tok_corr = (let _204_2009 = (let _204_2008 = (let _204_2007 = (let _204_2006 = (FStar_SMTEncoding_Term.mkEq (vtok_app, vapp))
in (((vtok_app)::[])::[], vars, _204_2006))
in (FStar_SMTEncoding_Term.mkForall _204_2007))
in (_204_2008, None))
in FStar_SMTEncoding_Term.Assume (_204_2009))
in ((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[])), env))))
end)
in (match (_101_2788) with
| (tok_decl, env) -> begin
((vname_decl)::tok_decl, env)
end)))
end)))
in (match (_101_2791) with
| (decls2, env) -> begin
(let _101_2799 = (let res_t = (FStar_Syntax_Subst.compress res_t)
in (let _101_2795 = (encode_term res_t env')
in (match (_101_2795) with
| (encoded_res_t, decls) -> begin
(let _204_2010 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in (encoded_res_t, _204_2010, decls))
end)))
in (match (_101_2799) with
| (encoded_res_t, ty_pred, decls3) -> begin
(let typingAx = (let _204_2014 = (let _204_2013 = (let _204_2012 = (let _204_2011 = (FStar_SMTEncoding_Term.mkImp (guard, ty_pred))
in (((vapp)::[])::[], vars, _204_2011))
in (FStar_SMTEncoding_Term.mkForall _204_2012))
in (_204_2013, Some ("free var typing")))
in FStar_SMTEncoding_Term.Assume (_204_2014))
in (let g = (let _204_2016 = (let _204_2015 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_204_2015)
in (FStar_List.append (FStar_List.append (FStar_List.append decls1 decls2) decls3) _204_2016))
in (g, env)))
end))
end))))
end))
end))))
end))
end)))
end
end)
and encode_signature : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _101_2806 se -> (match (_101_2806) with
| (g, env) -> begin
(let _101_2810 = (encode_sigelt env se)
in (match (_101_2810) with
| (g', env) -> begin
((FStar_List.append g g'), env)
end))
end)) ([], env))))

let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings -> (let encode_binding = (fun b _101_2817 -> (match (_101_2817) with
| (decls, env) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (_101_2819) -> begin
([], env)
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(let _101_2826 = (new_term_constant env x)
in (match (_101_2826) with
| (xxsym, xx, env') -> begin
(let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (let _101_2828 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _204_2031 = (FStar_Syntax_Print.bv_to_string x)
in (let _204_2030 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _204_2029 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" _204_2031 _204_2030 _204_2029))))
end else begin
()
end
in (let _101_2832 = (encode_term_pred None t1 env xx)
in (match (_101_2832) with
| (t, decls') -> begin
(let caption = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _204_2035 = (let _204_2034 = (FStar_Syntax_Print.bv_to_string x)
in (let _204_2033 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _204_2032 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _204_2034 _204_2033 _204_2032))))
in Some (_204_2035))
end else begin
None
end
in (let g = (FStar_List.append (FStar_List.append ((FStar_SMTEncoding_Term.DeclFun ((xxsym, [], FStar_SMTEncoding_Term.Term_sort, caption)))::[]) decls') ((FStar_SMTEncoding_Term.Assume ((t, None)))::[]))
in ((FStar_List.append decls g), env')))
end))))
end))
end
| FStar_TypeChecker_Env.Binding_lid (x, (_101_2837, t)) -> begin
(let t_norm = (whnf env t)
in (let _101_2845 = (encode_free_var env x t t_norm [])
in (match (_101_2845) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end)))
end
| (FStar_TypeChecker_Env.Binding_sig_inst (_, se, _)) | (FStar_TypeChecker_Env.Binding_sig (_, se)) -> begin
(let _101_2859 = (encode_sigelt env se)
in (match (_101_2859) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end))
end)
end))
in (FStar_List.fold_right encode_binding bindings ([], env))))

let encode_labels = (fun labs -> (let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _101_2866 -> (match (_101_2866) with
| (l, _101_2863, _101_2865) -> begin
FStar_SMTEncoding_Term.DeclFun (((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))
end))))
in (let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _101_2873 -> (match (_101_2873) with
| (l, _101_2870, _101_2872) -> begin
(let _204_2043 = (FStar_All.pipe_left (fun _204_2039 -> FStar_SMTEncoding_Term.Echo (_204_2039)) (Prims.fst l))
in (let _204_2042 = (let _204_2041 = (let _204_2040 = (FStar_SMTEncoding_Term.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (_204_2040))
in (_204_2041)::[])
in (_204_2043)::_204_2042))
end))))
in (prefix, suffix))))

let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (let _204_2048 = (let _204_2047 = (let _204_2046 = (FStar_Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _204_2046; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_204_2047)::[])
in (FStar_ST.op_Colon_Equals last_env _204_2048)))

let get_env : FStar_TypeChecker_Env.env  ->  env_t = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "No env; call init first!")
end
| e::_101_2879 -> begin
(let _101_2882 = e
in {bindings = _101_2882.bindings; depth = _101_2882.depth; tcenv = tcenv; warn = _101_2882.warn; cache = _101_2882.cache; nolabels = _101_2882.nolabels; use_zfuel_name = _101_2882.use_zfuel_name; encode_non_total_function_typ = _101_2882.encode_non_total_function_typ})
end))

let set_env : env_t  ->  Prims.unit = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| _101_2888::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))

let push_env : Prims.unit  ->  Prims.unit = (fun _101_2890 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| hd::tl -> begin
(let refs = (FStar_Util.smap_copy hd.cache)
in (let top = (let _101_2896 = hd
in {bindings = _101_2896.bindings; depth = _101_2896.depth; tcenv = _101_2896.tcenv; warn = _101_2896.warn; cache = refs; nolabels = _101_2896.nolabels; use_zfuel_name = _101_2896.use_zfuel_name; encode_non_total_function_typ = _101_2896.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))

let pop_env : Prims.unit  ->  Prims.unit = (fun _101_2899 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Popping an empty stack")
end
| _101_2903::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))

let mark_env : Prims.unit  ->  Prims.unit = (fun _101_2905 -> (match (()) with
| () -> begin
(push_env ())
end))

let reset_mark_env : Prims.unit  ->  Prims.unit = (fun _101_2906 -> (match (()) with
| () -> begin
(pop_env ())
end))

let commit_mark_env : Prims.unit  ->  Prims.unit = (fun _101_2907 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| hd::_101_2910::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _101_2915 -> begin
(FStar_All.failwith "Impossible")
end)
end))

let init : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (let _101_2917 = (init_env tcenv)
in (let _101_2919 = (FStar_SMTEncoding_Z3.init ())
in (FStar_SMTEncoding_Z3.giveZ3 ((FStar_SMTEncoding_Term.DefPrelude)::[])))))

let push : Prims.string  ->  Prims.unit = (fun msg -> (let _101_2922 = (push_env ())
in (let _101_2924 = (varops.push ())
in (FStar_SMTEncoding_Z3.push msg))))

let pop : Prims.string  ->  Prims.unit = (fun msg -> (let _101_2927 = (let _204_2069 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _204_2069))
in (let _101_2929 = (varops.pop ())
in (FStar_SMTEncoding_Z3.pop msg))))

let mark : Prims.string  ->  Prims.unit = (fun msg -> (let _101_2932 = (mark_env ())
in (let _101_2934 = (varops.mark ())
in (FStar_SMTEncoding_Z3.mark msg))))

let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (let _101_2937 = (reset_mark_env ())
in (let _101_2939 = (varops.reset_mark ())
in (FStar_SMTEncoding_Z3.reset_mark msg))))

let commit_mark = (fun msg -> (let _101_2942 = (commit_mark_env ())
in (let _101_2944 = (varops.commit_mark ())
in (FStar_SMTEncoding_Z3.commit_mark msg))))

let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (let caption = (fun decls -> if (FStar_ST.read FStar_Options.logQueries) then begin
(let _204_2085 = (let _204_2084 = (let _204_2083 = (let _204_2082 = (let _204_2081 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _204_2081 (FStar_List.map FStar_Syntax_Print.lid_to_string)))
in (FStar_All.pipe_right _204_2082 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " _204_2083))
in FStar_SMTEncoding_Term.Caption (_204_2084))
in (_204_2085)::decls)
end else begin
decls
end)
in (let env = (get_env tcenv)
in (let _101_2953 = (encode_sigelt env se)
in (match (_101_2953) with
| (decls, env) -> begin
(let _101_2954 = (set_env env)
in (let _204_2086 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 _204_2086)))
end)))))

let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (let _101_2959 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(let _204_2091 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name _204_2091))
end else begin
()
end
in (let env = (get_env tcenv)
in (let _101_2966 = (encode_signature (let _101_2962 = env
in {bindings = _101_2962.bindings; depth = _101_2962.depth; tcenv = _101_2962.tcenv; warn = false; cache = _101_2962.cache; nolabels = _101_2962.nolabels; use_zfuel_name = _101_2962.use_zfuel_name; encode_non_total_function_typ = _101_2962.encode_non_total_function_typ}) modul.FStar_Syntax_Syntax.exports)
in (match (_101_2966) with
| (decls, env) -> begin
(let caption = (fun decls -> if (FStar_ST.read FStar_Options.logQueries) then begin
(let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::decls) ((FStar_SMTEncoding_Term.Caption ((Prims.strcat "End " msg)))::[])))
end else begin
decls
end)
in (let _101_2972 = (set_env (let _101_2970 = env
in {bindings = _101_2970.bindings; depth = _101_2970.depth; tcenv = _101_2970.tcenv; warn = true; cache = _101_2970.cache; nolabels = _101_2970.nolabels; use_zfuel_name = _101_2970.use_zfuel_name; encode_non_total_function_typ = _101_2970.encode_non_total_function_typ}))
in (let _101_2974 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end else begin
()
end
in (let decls = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls)))))
end))))))

let solve : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun tcenv q -> (let _101_2979 = (let _204_2100 = (let _204_2099 = (let _204_2098 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _204_2098))
in (FStar_Util.format1 "Starting query at %s" _204_2099))
in (push _204_2100))
in (let pop = (fun _101_2982 -> (match (()) with
| () -> begin
(let _204_2105 = (let _204_2104 = (let _204_2103 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _204_2103))
in (FStar_Util.format1 "Ending query at %s" _204_2104))
in (pop _204_2105))
end))
in (let _101_3036 = (let env = (get_env tcenv)
in (let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (let _101_3006 = (let rec aux = (fun bindings -> (match (bindings) with
| FStar_TypeChecker_Env.Binding_var (x)::rest -> begin
(let _101_2995 = (aux rest)
in (match (_101_2995) with
| (out, rest) -> begin
(let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (let _204_2111 = (let _204_2110 = (FStar_Syntax_Syntax.mk_binder (let _101_2997 = x
in {FStar_Syntax_Syntax.ppname = _101_2997.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _101_2997.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_204_2110)::out)
in (_204_2111, rest)))
end))
end
| _101_3000 -> begin
([], bindings)
end))
in (let _101_3003 = (aux bindings)
in (match (_101_3003) with
| (closing, bindings) -> begin
(let _204_2112 = (FStar_Syntax_Util.close_forall (FStar_List.rev closing) q)
in (_204_2112, bindings))
end)))
in (match (_101_3006) with
| (q, bindings) -> begin
(let _101_3015 = (let _204_2114 = (FStar_List.filter (fun _101_21 -> (match (_101_21) with
| FStar_TypeChecker_Env.Binding_sig (_101_3009) -> begin
false
end
| _101_3012 -> begin
true
end)) bindings)
in (encode_env_bindings env _204_2114))
in (match (_101_3015) with
| (env_decls, env) -> begin
(let _101_3016 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(let _204_2115 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" _204_2115))
end else begin
()
end
in (let _101_3020 = (encode_formula q env)
in (match (_101_3020) with
| (phi, qdecls) -> begin
(let _101_3025 = (FStar_SMTEncoding_ErrorReporting.label_goals [] phi [])
in (match (_101_3025) with
| (phi, labels, _101_3024) -> begin
(let _101_3028 = (encode_labels labels)
in (match (_101_3028) with
| (label_prefix, label_suffix) -> begin
(let query_prelude = (FStar_List.append (FStar_List.append env_decls label_prefix) qdecls)
in (let qry = (let _204_2117 = (let _204_2116 = (FStar_SMTEncoding_Term.mkNot phi)
in (_204_2116, Some ("query")))
in FStar_SMTEncoding_Term.Assume (_204_2117))
in (let suffix = (FStar_List.append label_suffix ((FStar_SMTEncoding_Term.Echo ("Done!"))::[]))
in (query_prelude, labels, qry, suffix))))
end))
end))
end)))
end))
end))))
in (match (_101_3036) with
| (prefix, labels, qry, suffix) -> begin
(match (qry) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.False, _101_3043); FStar_SMTEncoding_Term.hash = _101_3040; FStar_SMTEncoding_Term.freevars = _101_3038}, _101_3048) -> begin
(let _101_3051 = (pop ())
in ())
end
| _101_3054 when tcenv.FStar_TypeChecker_Env.admit -> begin
(let _101_3055 = (pop ())
in ())
end
| FStar_SMTEncoding_Term.Assume (q, _101_3059) -> begin
(let fresh = ((FStar_String.length q.FStar_SMTEncoding_Term.hash) >= 2048)
in (let _101_3063 = (FStar_SMTEncoding_Z3.giveZ3 prefix)
in (let with_fuel = (fun p _101_3069 -> (match (_101_3069) with
| (n, i) -> begin
(let _204_2140 = (let _204_2139 = (let _204_2124 = (let _204_2123 = (FStar_Util.string_of_int n)
in (let _204_2122 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _204_2123 _204_2122)))
in FStar_SMTEncoding_Term.Caption (_204_2124))
in (let _204_2138 = (let _204_2137 = (let _204_2129 = (let _204_2128 = (let _204_2127 = (let _204_2126 = (FStar_SMTEncoding_Term.mkApp ("MaxFuel", []))
in (let _204_2125 = (FStar_SMTEncoding_Term.n_fuel n)
in (_204_2126, _204_2125)))
in (FStar_SMTEncoding_Term.mkEq _204_2127))
in (_204_2128, None))
in FStar_SMTEncoding_Term.Assume (_204_2129))
in (let _204_2136 = (let _204_2135 = (let _204_2134 = (let _204_2133 = (let _204_2132 = (let _204_2131 = (FStar_SMTEncoding_Term.mkApp ("MaxIFuel", []))
in (let _204_2130 = (FStar_SMTEncoding_Term.n_fuel i)
in (_204_2131, _204_2130)))
in (FStar_SMTEncoding_Term.mkEq _204_2132))
in (_204_2133, None))
in FStar_SMTEncoding_Term.Assume (_204_2134))
in (_204_2135)::(p)::(FStar_SMTEncoding_Term.CheckSat)::[])
in (_204_2137)::_204_2136))
in (_204_2139)::_204_2138))
in (FStar_List.append _204_2140 suffix))
end))
in (let check = (fun p -> (let initial_config = (let _204_2144 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _204_2143 = (FStar_ST.read FStar_Options.initial_ifuel)
in (_204_2144, _204_2143)))
in (let alt_configs = (let _204_2163 = (let _204_2162 = if ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel)) then begin
(let _204_2147 = (let _204_2146 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _204_2145 = (FStar_ST.read FStar_Options.max_ifuel)
in (_204_2146, _204_2145)))
in (_204_2147)::[])
end else begin
[]
end
in (let _204_2161 = (let _204_2160 = if (((FStar_ST.read FStar_Options.max_fuel) / 2) > (FStar_ST.read FStar_Options.initial_fuel)) then begin
(let _204_2150 = (let _204_2149 = ((FStar_ST.read FStar_Options.max_fuel) / 2)
in (let _204_2148 = (FStar_ST.read FStar_Options.max_ifuel)
in (_204_2149, _204_2148)))
in (_204_2150)::[])
end else begin
[]
end
in (let _204_2159 = (let _204_2158 = if (((FStar_ST.read FStar_Options.max_fuel) > (FStar_ST.read FStar_Options.initial_fuel)) && ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel))) then begin
(let _204_2153 = (let _204_2152 = (FStar_ST.read FStar_Options.max_fuel)
in (let _204_2151 = (FStar_ST.read FStar_Options.max_ifuel)
in (_204_2152, _204_2151)))
in (_204_2153)::[])
end else begin
[]
end
in (let _204_2157 = (let _204_2156 = if ((FStar_ST.read FStar_Options.min_fuel) < (FStar_ST.read FStar_Options.initial_fuel)) then begin
(let _204_2155 = (let _204_2154 = (FStar_ST.read FStar_Options.min_fuel)
in (_204_2154, 1))
in (_204_2155)::[])
end else begin
[]
end
in (_204_2156)::[])
in (_204_2158)::_204_2157))
in (_204_2160)::_204_2159))
in (_204_2162)::_204_2161))
in (FStar_List.flatten _204_2163))
in (let report = (fun errs -> (let errs = (match (errs) with
| [] -> begin
(("Unknown assertion failed", FStar_Range.dummyRange))::[]
end
| _101_3078 -> begin
errs
end)
in (let _101_3080 = if (FStar_ST.read FStar_Options.print_fuels) then begin
(let _204_2171 = (let _204_2166 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_Range.string_of_range _204_2166))
in (let _204_2170 = (let _204_2167 = (FStar_ST.read FStar_Options.max_fuel)
in (FStar_All.pipe_right _204_2167 FStar_Util.string_of_int))
in (let _204_2169 = (let _204_2168 = (FStar_ST.read FStar_Options.max_ifuel)
in (FStar_All.pipe_right _204_2168 FStar_Util.string_of_int))
in (FStar_Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _204_2171 _204_2170 _204_2169))))
end else begin
()
end
in (FStar_TypeChecker_Errors.add_errors tcenv errs))))
in (let rec try_alt_configs = (fun p errs _101_22 -> (match (_101_22) with
| [] -> begin
(report errs)
end
| mi::[] -> begin
(match (errs) with
| [] -> begin
(let _204_2182 = (with_fuel p mi)
in (FStar_SMTEncoding_Z3.ask fresh labels _204_2182 (cb mi p [])))
end
| _101_3092 -> begin
(report errs)
end)
end
| mi::tl -> begin
(let _204_2184 = (with_fuel p mi)
in (FStar_SMTEncoding_Z3.ask fresh labels _204_2184 (fun _101_3098 -> (match (_101_3098) with
| (ok, errs') -> begin
(match (errs) with
| [] -> begin
(cb mi p tl (ok, errs'))
end
| _101_3101 -> begin
(cb mi p tl (ok, errs))
end)
end))))
end))
and cb = (fun _101_3104 p alt _101_3109 -> (match ((_101_3104, _101_3109)) with
| ((prev_fuel, prev_ifuel), (ok, errs)) -> begin
if ok then begin
if (FStar_ST.read FStar_Options.print_fuels) then begin
(let _204_2192 = (let _204_2189 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_Range.string_of_range _204_2189))
in (let _204_2191 = (FStar_Util.string_of_int prev_fuel)
in (let _204_2190 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.print3 "(%s) Query succeeded with fuel %s and ifuel %s\n" _204_2192 _204_2191 _204_2190))))
end else begin
()
end
end else begin
(try_alt_configs p errs alt)
end
end))
in (let _204_2193 = (with_fuel p initial_config)
in (FStar_SMTEncoding_Z3.ask fresh labels _204_2193 (cb initial_config p alt_configs))))))))
in (let process_query = (fun q -> if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(let _101_3114 = (let _204_2199 = (FStar_ST.read FStar_Options.split_cases)
in (FStar_SMTEncoding_SplitQueryCases.can_handle_query _204_2199 q))
in (match (_101_3114) with
| (b, cb) -> begin
if b then begin
(FStar_SMTEncoding_SplitQueryCases.handle_query cb check)
end else begin
(check q)
end
end))
end else begin
(check q)
end)
in (let _101_3115 = if (FStar_ST.read FStar_Options.admit_smt_queries) then begin
()
end else begin
(process_query qry)
end
in (pop ())))))))
end
| _101_3118 -> begin
(FStar_All.failwith "Impossible")
end)
end)))))

let is_trivial : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun tcenv q -> (let env = (get_env tcenv)
in (let _101_3122 = (push "query")
in (let _101_3129 = (encode_formula_with_labels q env)
in (match (_101_3129) with
| (f, _101_3126, _101_3128) -> begin
(let _101_3130 = (pop "query")
in (match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _101_3134) -> begin
true
end
| _101_3138 -> begin
false
end))
end)))))

let solver : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = init; FStar_TypeChecker_Env.push = push; FStar_TypeChecker_Env.pop = pop; FStar_TypeChecker_Env.mark = mark; FStar_TypeChecker_Env.reset_mark = reset_mark; FStar_TypeChecker_Env.commit_mark = commit_mark; FStar_TypeChecker_Env.encode_modul = encode_modul; FStar_TypeChecker_Env.encode_sig = encode_sig; FStar_TypeChecker_Env.solve = solve; FStar_TypeChecker_Env.is_trivial = is_trivial; FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish; FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh}

let dummy : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = (fun _101_3139 -> ()); FStar_TypeChecker_Env.push = (fun _101_3141 -> ()); FStar_TypeChecker_Env.pop = (fun _101_3143 -> ()); FStar_TypeChecker_Env.mark = (fun _101_3145 -> ()); FStar_TypeChecker_Env.reset_mark = (fun _101_3147 -> ()); FStar_TypeChecker_Env.commit_mark = (fun _101_3149 -> ()); FStar_TypeChecker_Env.encode_modul = (fun _101_3151 _101_3153 -> ()); FStar_TypeChecker_Env.encode_sig = (fun _101_3155 _101_3157 -> ()); FStar_TypeChecker_Env.solve = (fun _101_3159 _101_3161 -> ()); FStar_TypeChecker_Env.is_trivial = (fun _101_3163 _101_3165 -> false); FStar_TypeChecker_Env.finish = (fun _101_3167 -> ()); FStar_TypeChecker_Env.refresh = (fun _101_3168 -> ())}




