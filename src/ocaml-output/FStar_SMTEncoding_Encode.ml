
open Prims

let add_fuel = (fun x tl -> if (FStar_Options.unthrottle_inductives ()) then begin
tl
end else begin
(x)::tl
end)


let withenv = (fun c _83_28 -> (match (_83_28) with
| (a, b) -> begin
(a, b, c)
end))


let vargs = (fun args -> (FStar_List.filter (fun _83_1 -> (match (_83_1) with
| (FStar_Util.Inl (_83_32), _83_35) -> begin
false
end
| _83_38 -> begin
true
end)) args))


let subst_lcomp_opt = (fun s l -> (match (l) with
| Some (FStar_Util.Inl (l)) -> begin
(let _172_12 = (let _172_11 = (let _172_10 = (let _172_9 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp s _172_9))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _172_10))
in FStar_Util.Inl (_172_11))
in Some (_172_12))
end
| _83_45 -> begin
l
end))


let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s '\'' '_'))


let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun lid a -> (

let a = (

let _83_49 = a
in (let _172_19 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _172_19; FStar_Syntax_Syntax.index = _83_49.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _83_49.FStar_Syntax_Syntax.sort}))
in (let _172_20 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str a.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (FStar_All.pipe_left escape _172_20))))


let primitive_projector_by_pos : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (

let fail = (fun _83_56 -> (match (()) with
| () -> begin
(let _172_30 = (let _172_29 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" _172_29 lid.FStar_Ident.str))
in (FStar_All.failwith _172_30))
end))
in (

let _83_60 = (FStar_TypeChecker_Env.lookup_datacon env lid)
in (match (_83_60) with
| (_83_58, t) -> begin
(match ((let _172_31 = (FStar_Syntax_Subst.compress t)
in _172_31.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _83_68 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_83_68) with
| (binders, _83_67) -> begin
if ((i < 0) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(

let b = (FStar_List.nth binders i)
in (mk_term_projector_name lid (Prims.fst b)))
end
end))
end
| _83_71 -> begin
(fail ())
end)
end))))


let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (let _172_37 = (let _172_36 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str _172_36))
in (FStar_All.pipe_left escape _172_37)))


let mk_term_projector : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun lid a -> (let _172_43 = (let _172_42 = (mk_term_projector_name lid a)
in (_172_42, FStar_SMTEncoding_Term.Arrow ((FStar_SMTEncoding_Term.Term_sort, FStar_SMTEncoding_Term.Term_sort))))
in (FStar_SMTEncoding_Term.mkFreeV _172_43)))


let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_SMTEncoding_Term.term = (fun lid i -> (let _172_49 = (let _172_48 = (mk_term_projector_name_by_pos lid i)
in (_172_48, FStar_SMTEncoding_Term.Arrow ((FStar_SMTEncoding_Term.Term_sort, FStar_SMTEncoding_Term.Term_sort))))
in (FStar_SMTEncoding_Term.mkFreeV _172_49)))


let mk_data_tester = (fun env l x -> (FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x))


type varops_t =
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; mark : Prims.unit  ->  Prims.unit; reset_mark : Prims.unit  ->  Prims.unit; commit_mark : Prims.unit  ->  Prims.unit; new_var : FStar_Ident.ident  ->  Prims.int  ->  Prims.string; new_fvar : FStar_Ident.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_SMTEncoding_Term.term; next_id : Prims.unit  ->  Prims.int}


let is_Mkvarops_t : varops_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkvarops_t"))))


let varops : varops_t = (

let initial_ctr = 100
in (

let ctr = (FStar_Util.mk_ref initial_ctr)
in (

let new_scope = (fun _83_95 -> (match (()) with
| () -> begin
(let _172_153 = (FStar_Util.smap_create 100)
in (let _172_152 = (FStar_Util.smap_create 100)
in (_172_153, _172_152)))
end))
in (

let scopes = (let _172_155 = (let _172_154 = (new_scope ())
in (_172_154)::[])
in (FStar_Util.mk_ref _172_155))
in (

let mk_unique = (fun y -> (

let y = (escape y)
in (

let y = (match ((let _172_159 = (FStar_ST.read scopes)
in (FStar_Util.find_map _172_159 (fun _83_103 -> (match (_83_103) with
| (names, _83_102) -> begin
(FStar_Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_83_106) -> begin
(

let _83_108 = (FStar_Util.incr ctr)
in (let _172_161 = (let _172_160 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _172_160))
in (Prims.strcat (Prims.strcat y "__") _172_161)))
end)
in (

let top_scope = (let _172_163 = (let _172_162 = (FStar_ST.read scopes)
in (FStar_List.hd _172_162))
in (FStar_All.pipe_left Prims.fst _172_163))
in (

let _83_112 = (FStar_Util.smap_add top_scope y true)
in y)))))
in (

let new_var = (fun pp rn -> (let _172_170 = (let _172_168 = (FStar_All.pipe_left mk_unique pp.FStar_Ident.idText)
in (Prims.strcat _172_168 "__"))
in (let _172_169 = (FStar_Util.string_of_int rn)
in (Prims.strcat _172_170 _172_169))))
in (

let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (

let next_id = (fun _83_120 -> (match (()) with
| () -> begin
(

let _83_121 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end))
in (

let fresh = (fun pfx -> (let _172_178 = (let _172_177 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _172_177))
in (FStar_Util.format2 "%s_%s" pfx _172_178)))
in (

let string_const = (fun s -> (match ((let _172_182 = (FStar_ST.read scopes)
in (FStar_Util.find_map _172_182 (fun _83_130 -> (match (_83_130) with
| (_83_128, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))) with
| Some (f) -> begin
f
end
| None -> begin
(

let id = (next_id ())
in (

let f = (let _172_183 = (FStar_SMTEncoding_Term.mk_String_const id)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString _172_183))
in (

let top_scope = (let _172_185 = (let _172_184 = (FStar_ST.read scopes)
in (FStar_List.hd _172_184))
in (FStar_All.pipe_left Prims.snd _172_185))
in (

let _83_137 = (FStar_Util.smap_add top_scope s f)
in f))))
end))
in (

let push = (fun _83_140 -> (match (()) with
| () -> begin
(let _172_190 = (let _172_189 = (new_scope ())
in (let _172_188 = (FStar_ST.read scopes)
in (_172_189)::_172_188))
in (FStar_ST.op_Colon_Equals scopes _172_190))
end))
in (

let pop = (fun _83_142 -> (match (()) with
| () -> begin
(let _172_194 = (let _172_193 = (FStar_ST.read scopes)
in (FStar_List.tl _172_193))
in (FStar_ST.op_Colon_Equals scopes _172_194))
end))
in (

let mark = (fun _83_144 -> (match (()) with
| () -> begin
(push ())
end))
in (

let reset_mark = (fun _83_146 -> (match (()) with
| () -> begin
(pop ())
end))
in (

let commit_mark = (fun _83_148 -> (match (()) with
| () -> begin
(match ((FStar_ST.read scopes)) with
| (hd1, hd2)::(next1, next2)::tl -> begin
(

let _83_161 = (FStar_Util.smap_fold hd1 (fun key value v -> (FStar_Util.smap_add next1 key value)) ())
in (

let _83_166 = (FStar_Util.smap_fold hd2 (fun key value v -> (FStar_Util.smap_add next2 key value)) ())
in (FStar_ST.op_Colon_Equals scopes (((next1, next2))::tl))))
end
| _83_169 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id})))))))))))))))


let unmangle : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv = (fun x -> (

let _83_171 = x
in (let _172_209 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _172_209; FStar_Syntax_Syntax.index = _83_171.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _83_171.FStar_Syntax_Syntax.sort})))


type binding =
| Binding_var of (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term)
| Binding_fvar of (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option)


let is_Binding_var = (fun _discr_ -> (match (_discr_) with
| Binding_var (_) -> begin
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


let ___Binding_var____0 = (fun projectee -> (match (projectee) with
| Binding_var (_83_175) -> begin
_83_175
end))


let ___Binding_fvar____0 = (fun projectee -> (match (projectee) with
| Binding_fvar (_83_178) -> begin
_83_178
end))


let binder_of_eithervar = (fun v -> (v, None))


type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_TypeChecker_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_SMTEncoding_Term.sort Prims.list * FStar_SMTEncoding_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}


let is_Mkenv_t : env_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_t"))))


let print_env : env_t  ->  Prims.string = (fun e -> (let _172_267 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun _83_2 -> (match (_83_2) with
| Binding_var (x, _83_193) -> begin
(FStar_Syntax_Print.bv_to_string x)
end
| Binding_fvar (l, _83_198, _83_200, _83_202) -> begin
(FStar_Syntax_Print.lid_to_string l)
end))))
in (FStar_All.pipe_right _172_267 (FStar_String.concat ", "))))


let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))


let caption_t : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.string Prims.option = (fun env t -> if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _172_277 = (FStar_Syntax_Print.term_to_string t)
in Some (_172_277))
end else begin
None
end)


let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (

let xsym = (varops.fresh x)
in (let _172_282 = (FStar_SMTEncoding_Term.mkFreeV (xsym, s))
in (xsym, _172_282))))


let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (let _172_287 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _172_287))
in (

let y = (FStar_SMTEncoding_Term.mkFreeV (ysym, FStar_SMTEncoding_Term.Term_sort))
in (ysym, y, (

let _83_216 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _83_216.tcenv; warn = _83_216.warn; cache = _83_216.cache; nolabels = _83_216.nolabels; use_zfuel_name = _83_216.use_zfuel_name; encode_non_total_function_typ = _83_216.encode_non_total_function_typ})))))


let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (

let y = (FStar_SMTEncoding_Term.mkApp (ysym, []))
in (ysym, y, (

let _83_222 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = _83_222.depth; tcenv = _83_222.tcenv; warn = _83_222.warn; cache = _83_222.cache; nolabels = _83_222.nolabels; use_zfuel_name = _83_222.use_zfuel_name; encode_non_total_function_typ = _83_222.encode_non_total_function_typ})))))


let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (

let _83_227 = env
in {bindings = (Binding_var ((x, t)))::env.bindings; depth = _83_227.depth; tcenv = _83_227.tcenv; warn = _83_227.warn; cache = _83_227.cache; nolabels = _83_227.nolabels; use_zfuel_name = _83_227.use_zfuel_name; encode_non_total_function_typ = _83_227.encode_non_total_function_typ}))


let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (match ((lookup_binding env (fun _83_3 -> (match (_83_3) with
| Binding_var (b, t) when (FStar_Syntax_Syntax.bv_eq b a) -> begin
Some ((b, t))
end
| _83_237 -> begin
None
end)))) with
| None -> begin
(let _172_304 = (let _172_303 = (FStar_Syntax_Print.bv_to_string a)
in (FStar_Util.format1 "Bound term variable not found: %s" _172_303))
in (FStar_All.failwith _172_304))
end
| Some (b, t) -> begin
t
end))


let new_term_constant_and_tok_from_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * Prims.string * env_t) = (fun env x -> (

let fname = (varops.new_fvar x)
in (

let ftok = (Prims.strcat fname "@tok")
in (let _172_315 = (

let _83_247 = env
in (let _172_314 = (let _172_313 = (let _172_312 = (let _172_311 = (let _172_310 = (FStar_SMTEncoding_Term.mkApp (ftok, []))
in (FStar_All.pipe_left (fun _172_309 -> Some (_172_309)) _172_310))
in (x, fname, _172_311, None))
in Binding_fvar (_172_312))
in (_172_313)::env.bindings)
in {bindings = _172_314; depth = _83_247.depth; tcenv = _83_247.tcenv; warn = _83_247.warn; cache = _83_247.cache; nolabels = _83_247.nolabels; use_zfuel_name = _83_247.use_zfuel_name; encode_non_total_function_typ = _83_247.encode_non_total_function_typ}))
in (fname, ftok, _172_315)))))


let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun _83_4 -> (match (_83_4) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some ((t1, t2, t3))
end
| _83_259 -> begin
None
end))))


let contains_name : env_t  ->  Prims.string  ->  Prims.bool = (fun env s -> (let _172_326 = (lookup_binding env (fun _83_5 -> (match (_83_5) with
| Binding_fvar (b, t1, t2, t3) when (b.FStar_Ident.str = s) -> begin
Some (())
end
| _83_270 -> begin
None
end)))
in (FStar_All.pipe_right _172_326 FStar_Option.isSome)))


let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _172_332 = (let _172_331 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" _172_331))
in (FStar_All.failwith _172_332))
end
| Some (s) -> begin
s
end))


let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (

let _83_280 = env
in {bindings = (Binding_fvar ((x, fname, ftok, None)))::env.bindings; depth = _83_280.depth; tcenv = _83_280.tcenv; warn = _83_280.warn; cache = _83_280.cache; nolabels = _83_280.nolabels; use_zfuel_name = _83_280.use_zfuel_name; encode_non_total_function_typ = _83_280.encode_non_total_function_typ}))


let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (

let _83_289 = (lookup_lid env x)
in (match (_83_289) with
| (t1, t2, _83_288) -> begin
(

let t3 = (let _172_349 = (let _172_348 = (let _172_347 = (FStar_SMTEncoding_Term.mkApp ("ZFuel", []))
in (_172_347)::[])
in (f, _172_348))
in (FStar_SMTEncoding_Term.mkApp _172_349))
in (

let _83_291 = env
in {bindings = (Binding_fvar ((x, t1, t2, Some (t3))))::env.bindings; depth = _83_291.depth; tcenv = _83_291.tcenv; warn = _83_291.warn; cache = _83_291.cache; nolabels = _83_291.nolabels; use_zfuel_name = _83_291.use_zfuel_name; encode_non_total_function_typ = _83_291.encode_non_total_function_typ}))
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
| _83_304 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (_83_308, fuel::[]) -> begin
if (let _172_355 = (let _172_354 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right _172_354 Prims.fst))
in (FStar_Util.starts_with _172_355 "fuel")) then begin
(let _172_358 = (let _172_357 = (FStar_SMTEncoding_Term.mkFreeV (name, FStar_SMTEncoding_Term.Term_sort))
in (FStar_SMTEncoding_Term.mk_ApplyTF _172_357 fuel))
in (FStar_All.pipe_left (fun _172_356 -> Some (_172_356)) _172_358))
end else begin
Some (t)
end
end
| _83_314 -> begin
Some (t)
end)
end
| _83_316 -> begin
None
end)
end)
end))


let lookup_free_var = (fun env a -> (match ((try_lookup_free_var env a.FStar_Syntax_Syntax.v)) with
| Some (t) -> begin
t
end
| None -> begin
(let _172_362 = (let _172_361 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _172_361))
in (FStar_All.failwith _172_362))
end))


let lookup_free_var_name = (fun env a -> (

let _83_329 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_83_329) with
| (x, _83_326, _83_328) -> begin
x
end)))


let lookup_free_var_sym = (fun env a -> (

let _83_335 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_83_335) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.hash = _83_339; FStar_SMTEncoding_Term.freevars = _83_337}) when env.use_zfuel_name -> begin
(g, zf)
end
| _83_347 -> begin
(match (sym) with
| None -> begin
(FStar_SMTEncoding_Term.Var (name), [])
end
| Some (sym) -> begin
(match (sym.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, fuel::[]) -> begin
(g, (fuel)::[])
end
| _83_357 -> begin
(FStar_SMTEncoding_Term.Var (name), [])
end)
end)
end)
end)))


let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun _83_6 -> (match (_83_6) with
| Binding_fvar (_83_362, nm', tok, _83_366) when (nm = nm') -> begin
tok
end
| _83_370 -> begin
None
end))))


let mkForall_fuel' = (fun n _83_375 -> (match (_83_375) with
| (pats, vars, body) -> begin
(

let fallback = (fun _83_377 -> (match (()) with
| () -> begin
(FStar_SMTEncoding_Term.mkForall (pats, vars, body))
end))
in if (FStar_Options.unthrottle_inductives ()) then begin
(fallback ())
end else begin
(

let _83_380 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_83_380) with
| (fsym, fterm) -> begin
(

let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Term.mkApp ("HasTypeFuel", (fterm)::args))
end
| _83_390 -> begin
p
end)))))
in (

let pats = (FStar_List.map add_fuel pats)
in (

let body = (match (body.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, guard::body'::[]) -> begin
(

let guard = (match (guard.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, guards) -> begin
(let _172_379 = (add_fuel guards)
in (FStar_SMTEncoding_Term.mk_and_l _172_379))
end
| _83_403 -> begin
(let _172_380 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _172_380 FStar_List.hd))
end)
in (FStar_SMTEncoding_Term.mkImp (guard, body')))
end
| _83_406 -> begin
body
end)
in (

let vars = ((fsym, FStar_SMTEncoding_Term.Fuel_sort))::vars
in (FStar_SMTEncoding_Term.mkForall (pats, vars, body))))))
end))
end)
end))


let mkForall_fuel : (FStar_SMTEncoding_Term.pat Prims.list Prims.list * FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (mkForall_fuel' 1)


let head_normal : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let t = (FStar_Syntax_Util.unmeta t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) -> begin
true
end
| (FStar_Syntax_Syntax.Tm_fvar (fv)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(let _172_386 = (FStar_TypeChecker_Env.lookup_definition FStar_TypeChecker_Env.OnlyInline env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _172_386 FStar_Option.isNone))
end
| _83_445 -> begin
false
end)))


let head_redex : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (match ((let _172_391 = (FStar_Syntax_Util.un_uinst t)
in _172_391.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_83_449) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(let _172_392 = (FStar_TypeChecker_Env.lookup_definition FStar_TypeChecker_Env.OnlyInline env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _172_392 FStar_Option.isSome))
end
| _83_454 -> begin
false
end))


let whnf : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> if (head_normal env t) then begin
t
end else begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
end)


let norm : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t))


let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (let _172_405 = (let _172_403 = (FStar_Syntax_Syntax.null_binder t)
in (_172_403)::[])
in (let _172_404 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Util.abs _172_405 _172_404 None))))


let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(let _172_412 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out _172_412))
end
| s -> begin
(

let _83_466 = ()
in (let _172_413 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTT out _172_413)))
end)) e)))


let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Term.mk_ApplyTT e)))


let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun _83_7 -> (match (_83_7) with
| (FStar_SMTEncoding_Term.Var ("ApplyTT")) | (FStar_SMTEncoding_Term.Var ("ApplyTF")) -> begin
true
end
| _83_476 -> begin
false
end))


let is_eta : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env vars t -> (

let rec aux = (fun t xs -> (match ((t.FStar_SMTEncoding_Term.tm, xs)) with
| (FStar_SMTEncoding_Term.App (app, f::{FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.hash = _83_487; FStar_SMTEncoding_Term.freevars = _83_485}::[]), x::xs) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), _83_505) -> begin
if (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v)
end
| _83_512 -> begin
false
end)) args vars)) then begin
(tok_of_name env f)
end else begin
None
end
end
| (_83_514, []) -> begin
(

let fvs = (FStar_SMTEncoding_Term.free_variables t)
in if (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (not ((FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)))))) then begin
Some (t)
end else begin
None
end)
end
| _83_520 -> begin
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


let is_Let_rec_unencodeable = (fun _discr_ -> (match (_discr_) with
| Let_rec_unencodeable (_) -> begin
true
end
| _ -> begin
false
end))


let encode_const : FStar_Const.sconst  ->  FStar_SMTEncoding_Term.term = (fun _83_8 -> (match (_83_8) with
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
(let _172_470 = (let _172_469 = (let _172_468 = (let _172_467 = (FStar_SMTEncoding_Term.mkInteger' (FStar_Util.int_of_char c))
in (FStar_SMTEncoding_Term.boxInt _172_467))
in (_172_468)::[])
in ("FStar.Char.Char", _172_469))
in (FStar_SMTEncoding_Term.mkApp _172_470))
end
| FStar_Const.Const_int (i, None) -> begin
(let _172_471 = (FStar_SMTEncoding_Term.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt _172_471))
end
| FStar_Const.Const_int (i, Some (q)) -> begin
(let _172_475 = (let _172_474 = (let _172_473 = (let _172_472 = (FStar_SMTEncoding_Term.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt _172_472))
in (_172_473)::[])
in ((FStar_Const.constructor_string_of_int_qualifier q), _172_474))
in (FStar_SMTEncoding_Term.mkApp _172_475))
end
| FStar_Const.Const_string (bytes, _83_545) -> begin
(let _172_476 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _172_476))
end
| FStar_Const.Const_range (r) -> begin
FStar_SMTEncoding_Term.mk_Range_const
end
| FStar_Const.Const_effect -> begin
FStar_SMTEncoding_Term.mk_Term_type
end
| c -> begin
(let _172_478 = (let _172_477 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" _172_477))
in (FStar_All.failwith _172_478))
end))


let as_function_typ : env_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (

let rec aux = (fun norm t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_83_559) -> begin
t
end
| FStar_Syntax_Syntax.Tm_refine (_83_562) -> begin
(let _172_487 = (FStar_Syntax_Util.unrefine t)
in (aux true _172_487))
end
| _83_565 -> begin
if norm then begin
(let _172_488 = (whnf env t)
in (aux false _172_488))
end else begin
(let _172_491 = (let _172_490 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (let _172_489 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _172_490 _172_489)))
in (FStar_All.failwith _172_491))
end
end)))
in (aux true t0)))


let curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun k -> (

let k = (FStar_Syntax_Subst.compress k)
in (match (k.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| _83_573 -> begin
(let _172_494 = (FStar_Syntax_Syntax.mk_Total k)
in ([], _172_494))
end)))


let rec encode_binders : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> (

let _83_577 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _172_542 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" _172_542))
end else begin
()
end
in (

let _83_605 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _83_584 b -> (match (_83_584) with
| (vars, guards, env, decls, names) -> begin
(

let _83_599 = (

let x = (unmangle (Prims.fst b))
in (

let _83_590 = (gen_term_var env x)
in (match (_83_590) with
| (xxsym, xx, env') -> begin
(

let _83_593 = (let _172_545 = (norm env x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt _172_545 env xx))
in (match (_83_593) with
| (guard_x_t, decls') -> begin
((xxsym, FStar_SMTEncoding_Term.Term_sort), guard_x_t, env', decls', x)
end))
end)))
in (match (_83_599) with
| (v, g, env, decls', n) -> begin
((v)::vars, (g)::guards, env, (FStar_List.append decls decls'), (n)::names)
end))
end)) ([], [], env, [], [])))
in (match (_83_605) with
| (vars, guards, env, decls, names) -> begin
((FStar_List.rev vars), (FStar_List.rev guards), env, decls, (FStar_List.rev names))
end))))
and encode_term_pred : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let _83_612 = (encode_term t env)
in (match (_83_612) with
| (t, decls) -> begin
(let _172_550 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t)
in (_172_550, decls))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let _83_619 = (encode_term t env)
in (match (_83_619) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _172_555 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t)
in (_172_555, decls))
end
| Some (f) -> begin
(let _172_556 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t)
in (_172_556, decls))
end)
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let t0 = (FStar_Syntax_Subst.compress t)
in (

let _83_626 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _172_561 = (FStar_Syntax_Print.tag_of_term t)
in (let _172_560 = (FStar_Syntax_Print.tag_of_term t0)
in (let _172_559 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" _172_561 _172_560 _172_559))))
end else begin
()
end
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _172_566 = (let _172_565 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (let _172_564 = (FStar_Syntax_Print.tag_of_term t0)
in (let _172_563 = (FStar_Syntax_Print.term_to_string t0)
in (let _172_562 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _172_565 _172_564 _172_563 _172_562)))))
in (FStar_All.failwith _172_566))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _172_568 = (let _172_567 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" _172_567))
in (FStar_All.failwith _172_568))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, k, _83_637) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_meta (t, _83_642) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t = (lookup_term_var env x)
in (t, []))
end
| FStar_Syntax_Syntax.Tm_fvar (v) -> begin
(let _172_569 = (lookup_free_var env v.FStar_Syntax_Syntax.fv_name)
in (_172_569, []))
end
| FStar_Syntax_Syntax.Tm_type (_83_651) -> begin
(FStar_SMTEncoding_Term.mk_Term_type, [])
end
| FStar_Syntax_Syntax.Tm_uinst (t, _83_655) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(let _172_570 = (encode_const c)
in (_172_570, []))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _83_666 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_83_666) with
| (binders, res) -> begin
if ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res)) then begin
(

let _83_673 = (encode_binders None binders env)
in (match (_83_673) with
| (vars, guards, env', decls, _83_672) -> begin
(

let fsym = (let _172_571 = (varops.fresh "f")
in (_172_571, FStar_SMTEncoding_Term.Term_sort))
in (

let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (

let app = (mk_Apply f vars)
in (

let _83_679 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv res)
in (match (_83_679) with
| (pre_opt, res_t) -> begin
(

let _83_682 = (encode_term_pred None res_t env' app)
in (match (_83_682) with
| (res_pred, decls') -> begin
(

let _83_691 = (match (pre_opt) with
| None -> begin
(let _172_572 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_172_572, []))
end
| Some (pre) -> begin
(

let _83_688 = (encode_formula pre env')
in (match (_83_688) with
| (guard, decls0) -> begin
(let _172_573 = (FStar_SMTEncoding_Term.mk_and_l ((guard)::guards))
in (_172_573, decls0))
end))
end)
in (match (_83_691) with
| (guards, guard_decls) -> begin
(

let t_interp = (let _172_575 = (let _172_574 = (FStar_SMTEncoding_Term.mkImp (guards, res_pred))
in (((app)::[])::[], vars, _172_574))
in (FStar_SMTEncoding_Term.mkForall _172_575))
in (

let cvars = (let _172_577 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right _172_577 (FStar_List.filter (fun _83_696 -> (match (_83_696) with
| (x, _83_695) -> begin
(x <> (Prims.fst fsym))
end)))))
in (

let tkey = (FStar_SMTEncoding_Term.mkForall ([], (fsym)::cvars, t_interp))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t', sorts, _83_702) -> begin
(let _172_580 = (let _172_579 = (let _172_578 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in (t', _172_578))
in (FStar_SMTEncoding_Term.mkApp _172_579))
in (_172_580, []))
end
| None -> begin
(

let tsym = (varops.fresh "Tm_arrow")
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let caption = if (FStar_Options.log_queries ()) then begin
(let _172_581 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in Some (_172_581))
end else begin
None
end
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun ((tsym, cvar_sorts, FStar_SMTEncoding_Term.Term_sort, caption))
in (

let t = (let _172_583 = (let _172_582 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (tsym, _172_582))
in (FStar_SMTEncoding_Term.mkApp _172_583))
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let k_assumption = (

let a_name = Some ((Prims.strcat "kinding_" tsym))
in (let _172_585 = (let _172_584 = (FStar_SMTEncoding_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (_172_584, a_name, a_name))
in FStar_SMTEncoding_Term.Assume (_172_585)))
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t)
in (

let pre_typing = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in (let _172_592 = (let _172_591 = (let _172_590 = (let _172_589 = (let _172_588 = (let _172_587 = (let _172_586 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _172_586))
in (f_has_t, _172_587))
in (FStar_SMTEncoding_Term.mkImp _172_588))
in (((f_has_t)::[])::[], (fsym)::cvars, _172_589))
in (mkForall_fuel _172_590))
in (_172_591, Some ("pre-typing for functions"), a_name))
in FStar_SMTEncoding_Term.Assume (_172_592)))
in (

let t_interp = (

let a_name = Some ((Prims.strcat "interpretation_" tsym))
in (let _172_596 = (let _172_595 = (let _172_594 = (let _172_593 = (FStar_SMTEncoding_Term.mkIff (f_has_t_z, t_interp))
in (((f_has_t_z)::[])::[], (fsym)::cvars, _172_593))
in (FStar_SMTEncoding_Term.mkForall _172_594))
in (_172_595, a_name, a_name))
in FStar_SMTEncoding_Term.Assume (_172_596)))
in (

let t_decls = (FStar_List.append (FStar_List.append (FStar_List.append ((tdecl)::decls) decls') guard_decls) ((k_assumption)::(pre_typing)::(t_interp)::[]))
in (

let _83_721 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls))))))))))))))
end))))
end))
end))
end)))))
end))
end else begin
(

let tsym = (varops.fresh "Non_total_Tm_arrow")
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun ((tsym, [], FStar_SMTEncoding_Term.Term_sort, None))
in (

let t = (FStar_SMTEncoding_Term.mkApp (tsym, []))
in (

let t_kinding = (

let a_name = Some ((Prims.strcat "non_total_function_typing_" tsym))
in (let _172_598 = (let _172_597 = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (_172_597, Some ("Typing for non-total arrows"), a_name))
in FStar_SMTEncoding_Term.Assume (_172_598)))
in (

let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)
in (

let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let t_interp = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in (let _172_605 = (let _172_604 = (let _172_603 = (let _172_602 = (let _172_601 = (let _172_600 = (let _172_599 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _172_599))
in (f_has_t, _172_600))
in (FStar_SMTEncoding_Term.mkImp _172_601))
in (((f_has_t)::[])::[], (fsym)::[], _172_602))
in (mkForall_fuel _172_603))
in (_172_604, a_name, a_name))
in FStar_SMTEncoding_Term.Assume (_172_605)))
in (t, (tdecl)::(t_kinding)::(t_interp)::[])))))))))
end
end))
end
| FStar_Syntax_Syntax.Tm_refine (_83_734) -> begin
(

let _83_754 = (match ((FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.tk = _83_741; FStar_Syntax_Syntax.pos = _83_739; FStar_Syntax_Syntax.vars = _83_737} -> begin
(

let _83_749 = (FStar_Syntax_Subst.open_term (((x, None))::[]) f)
in (match (_83_749) with
| (b, f) -> begin
(let _172_607 = (let _172_606 = (FStar_List.hd b)
in (Prims.fst _172_606))
in (_172_607, f))
end))
end
| _83_751 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_83_754) with
| (x, f) -> begin
(

let _83_757 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (_83_757) with
| (base_t, decls) -> begin
(

let _83_761 = (gen_term_var env x)
in (match (_83_761) with
| (x, xtm, env') -> begin
(

let _83_764 = (encode_formula f env')
in (match (_83_764) with
| (refinement, decls') -> begin
(

let _83_767 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_83_767) with
| (fsym, fterm) -> begin
(

let encoding = (let _172_609 = (let _172_608 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in (_172_608, refinement))
in (FStar_SMTEncoding_Term.mkAnd _172_609))
in (

let cvars = (let _172_611 = (FStar_SMTEncoding_Term.free_variables encoding)
in (FStar_All.pipe_right _172_611 (FStar_List.filter (fun _83_772 -> (match (_83_772) with
| (y, _83_771) -> begin
((y <> x) && (y <> fsym))
end)))))
in (

let xfv = (x, FStar_SMTEncoding_Term.Term_sort)
in (

let ffv = (fsym, FStar_SMTEncoding_Term.Fuel_sort)
in (

let tkey = (FStar_SMTEncoding_Term.mkForall ([], (ffv)::(xfv)::cvars, encoding))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _83_779, _83_781) -> begin
(let _172_614 = (let _172_613 = (let _172_612 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in (t, _172_612))
in (FStar_SMTEncoding_Term.mkApp _172_613))
in (_172_614, []))
end
| None -> begin
(

let tsym = (varops.fresh "Tm_refine")
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun ((tsym, cvar_sorts, FStar_SMTEncoding_Term.Term_sort, None))
in (

let t = (let _172_616 = (let _172_615 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (tsym, _172_615))
in (FStar_SMTEncoding_Term.mkApp _172_616))
in (

let x_has_t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let t_kinding = (let _172_618 = (let _172_617 = (FStar_SMTEncoding_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (_172_617, Some ("refinement kinding"), Some ((Prims.strcat "refinement_kinding_" tsym))))
in FStar_SMTEncoding_Term.Assume (_172_618))
in (

let t_interp = (let _172_624 = (let _172_623 = (let _172_620 = (let _172_619 = (FStar_SMTEncoding_Term.mkIff (x_has_t, encoding))
in (((x_has_t)::[])::[], (ffv)::(xfv)::cvars, _172_619))
in (FStar_SMTEncoding_Term.mkForall _172_620))
in (let _172_622 = (let _172_621 = (FStar_Syntax_Print.term_to_string t0)
in Some (_172_621))
in (_172_623, _172_622, Some ((Prims.strcat "refinement_interpretation_" tsym)))))
in FStar_SMTEncoding_Term.Assume (_172_624))
in (

let t_decls = (FStar_List.append (FStar_List.append decls decls') ((tdecl)::(t_kinding)::(t_interp)::[]))
in (

let _83_794 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls)))))))))))
end))))))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
(

let ttm = (let _172_625 = (FStar_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Term.mk_Term_uvar _172_625))
in (

let _83_803 = (encode_term_pred None k env ttm)
in (match (_83_803) with
| (t_has_k, decls) -> begin
(

let d = (let _172_631 = (let _172_630 = (let _172_629 = (let _172_628 = (let _172_627 = (let _172_626 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _172_626))
in (FStar_Util.format1 "uvar_typing_%s" _172_627))
in (varops.fresh _172_628))
in Some (_172_629))
in (t_has_k, Some ("Uvar typing"), _172_630))
in FStar_SMTEncoding_Term.Assume (_172_631))
in (ttm, (FStar_List.append decls ((d)::[]))))
end)))
end
| FStar_Syntax_Syntax.Tm_app (_83_806) -> begin
(

let _83_810 = (FStar_Syntax_Util.head_and_args t0)
in (match (_83_810) with
| (head, args_e) -> begin
(match ((let _172_633 = (let _172_632 = (FStar_Syntax_Subst.compress head)
in _172_632.FStar_Syntax_Syntax.n)
in (_172_633, args_e))) with
| (_83_812, _83_814) when (head_redex env head) -> begin
(let _172_634 = (whnf env t)
in (encode_term _172_634 env))
end
| ((FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _::(v1, _)::(v2, _)::[])) | ((FStar_Syntax_Syntax.Tm_fvar (fv), _::(v1, _)::(v2, _)::[])) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
(

let _83_854 = (encode_term v1 env)
in (match (_83_854) with
| (v1, decls1) -> begin
(

let _83_857 = (encode_term v2 env)
in (match (_83_857) with
| (v2, decls2) -> begin
(let _172_635 = (FStar_SMTEncoding_Term.mk_LexCons v1 v2)
in (_172_635, (FStar_List.append decls1 decls2)))
end))
end))
end
| _83_859 -> begin
(

let _83_862 = (encode_args args_e env)
in (match (_83_862) with
| (args, decls) -> begin
(

let encode_partial_app = (fun ht_opt -> (

let _83_867 = (encode_term head env)
in (match (_83_867) with
| (head, decls') -> begin
(

let app_tm = (mk_Apply_args head args)
in (match (ht_opt) with
| None -> begin
(app_tm, (FStar_List.append decls decls'))
end
| Some (formals, c) -> begin
(

let _83_876 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (_83_876) with
| (formals, rest) -> begin
(

let subst = (FStar_List.map2 (fun _83_880 _83_884 -> (match ((_83_880, _83_884)) with
| ((bv, _83_879), (a, _83_883)) -> begin
FStar_Syntax_Syntax.NT ((bv, a))
end)) formals args_e)
in (

let ty = (let _172_640 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right _172_640 (FStar_Syntax_Subst.subst subst)))
in (

let _83_889 = (encode_term_pred None ty env app_tm)
in (match (_83_889) with
| (has_type, decls'') -> begin
(

let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (

let e_typing = (let _172_646 = (let _172_645 = (FStar_SMTEncoding_Term.mkForall (((has_type)::[])::[], cvars, has_type))
in (let _172_644 = (let _172_643 = (let _172_642 = (let _172_641 = (varops.next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _172_641))
in (Prims.strcat "partial_app_typing_" _172_642))
in Some (_172_643))
in (_172_645, Some ("Partial app typing"), _172_644)))
in FStar_SMTEncoding_Term.Assume (_172_646))
in (app_tm, (FStar_List.append (FStar_List.append (FStar_List.append decls decls') decls'') ((e_typing)::[])))))
end))))
end))
end))
end)))
in (

let encode_full_app = (fun fv -> (

let _83_896 = (lookup_free_var_sym env fv)
in (match (_83_896) with
| (fname, fuel_args) -> begin
(

let tm = (FStar_SMTEncoding_Term.mkApp' (fname, (FStar_List.append fuel_args args)))
in (tm, decls))
end)))
in (

let head = (FStar_Syntax_Subst.compress head)
in (

let head_type = (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (x); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (x)) -> begin
Some (x.FStar_Syntax_Syntax.sort)
end
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(let _172_650 = (let _172_649 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _172_649 Prims.snd))
in Some (_172_650))
end
| FStar_Syntax_Syntax.Tm_ascribed (_83_928, FStar_Util.Inl (t), _83_932) -> begin
Some (t)
end
| FStar_Syntax_Syntax.Tm_ascribed (_83_936, FStar_Util.Inr (c), _83_940) -> begin
Some ((FStar_Syntax_Util.comp_result c))
end
| _83_944 -> begin
None
end)
in (match (head_type) with
| None -> begin
(encode_partial_app None)
end
| Some (head_type) -> begin
(

let head_type = (let _172_651 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine _172_651))
in (

let _83_952 = (curried_arrow_formals_comp head_type)
in (match (_83_952) with
| (formals, c) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| _83_968 -> begin
if ((FStar_List.length formals) > (FStar_List.length args)) then begin
(encode_partial_app (Some ((formals, c))))
end else begin
(encode_partial_app None)
end
end)
end)))
end)))))
end))
end)
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let _83_977 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_83_977) with
| (bs, body, opening) -> begin
(

let fallback = (fun _83_979 -> (match (()) with
| () -> begin
(

let f = (varops.fresh "Tm_abs")
in (

let decl = FStar_SMTEncoding_Term.DeclFun ((f, [], FStar_SMTEncoding_Term.Term_sort, Some ("Imprecise function encoding")))
in (let _172_654 = (FStar_SMTEncoding_Term.mkFreeV (f, FStar_SMTEncoding_Term.Term_sort))
in (_172_654, (decl)::[]))))
end))
in (

let is_pure_or_ghost = (fun lc_eff -> (match (lc_eff) with
| FStar_Util.Inl (lc) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)
end
| FStar_Util.Inr (eff) -> begin
((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid))
end))
in (

let codomain_eff = (fun lc -> (match (lc) with
| FStar_Util.Inl (lc) -> begin
(let _172_659 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening _172_659))
end
| FStar_Util.Inr (ef) -> begin
(let _172_661 = (let _172_660 = (FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange [] FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _172_660 Prims.fst))
in (FStar_Syntax_Syntax.mk_Total _172_661))
end))
in (match (lopt) with
| None -> begin
(

let _83_995 = (let _172_663 = (let _172_662 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s" _172_662))
in (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos _172_663))
in (fallback ()))
end
| Some (lc) -> begin
if (let _172_664 = (is_pure_or_ghost lc)
in (FStar_All.pipe_left Prims.op_Negation _172_664)) then begin
(fallback ())
end else begin
(

let c = (codomain_eff lc)
in (

let _83_1006 = (encode_binders None bs env)
in (match (_83_1006) with
| (vars, guards, envbody, decls, _83_1005) -> begin
(

let _83_1009 = (encode_term body envbody)
in (match (_83_1009) with
| (body, decls') -> begin
(

let key_body = (let _172_668 = (let _172_667 = (let _172_666 = (let _172_665 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_172_665, body))
in (FStar_SMTEncoding_Term.mkImp _172_666))
in ([], vars, _172_667))
in (FStar_SMTEncoding_Term.mkForall _172_668))
in (

let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (

let tkey = (FStar_SMTEncoding_Term.mkForall ([], cvars, key_body))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _83_1015, _83_1017) -> begin
(let _172_671 = (let _172_670 = (let _172_669 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (t, _172_669))
in (FStar_SMTEncoding_Term.mkApp _172_670))
in (_172_671, []))
end
| None -> begin
(match ((is_eta env vars body)) with
| Some (t) -> begin
(t, [])
end
| None -> begin
(

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let fsym = (varops.fresh "Exp_abs")
in (

let fdecl = FStar_SMTEncoding_Term.DeclFun ((fsym, cvar_sorts, FStar_SMTEncoding_Term.Term_sort, None))
in (

let f = (let _172_673 = (let _172_672 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (fsym, _172_672))
in (FStar_SMTEncoding_Term.mkApp _172_673))
in (

let app = (mk_Apply f vars)
in (

let tfun = (FStar_Syntax_Util.arrow bs c)
in (

let _83_1032 = (encode_term_pred None tfun env f)
in (match (_83_1032) with
| (f_has_t, decls'') -> begin
(

let typing_f = (

let a_name = Some ((Prims.strcat "typing_" fsym))
in (let _172_675 = (let _172_674 = (FStar_SMTEncoding_Term.mkForall (((f)::[])::[], cvars, f_has_t))
in (_172_674, a_name, a_name))
in FStar_SMTEncoding_Term.Assume (_172_675)))
in (

let interp_f = (

let a_name = Some ((Prims.strcat "interpretation_" fsym))
in (let _172_682 = (let _172_681 = (let _172_680 = (let _172_679 = (let _172_678 = (let _172_677 = (FStar_SMTEncoding_Term.mk_IsTyped app)
in (let _172_676 = (FStar_SMTEncoding_Term.mkEq (app, body))
in (_172_677, _172_676)))
in (FStar_SMTEncoding_Term.mkImp _172_678))
in (((app)::[])::[], (FStar_List.append vars cvars), _172_679))
in (FStar_SMTEncoding_Term.mkForall _172_680))
in (_172_681, a_name, a_name))
in FStar_SMTEncoding_Term.Assume (_172_682)))
in (

let f_decls = (FStar_List.append (FStar_List.append (FStar_List.append decls decls') ((fdecl)::decls'')) ((typing_f)::(interp_f)::[]))
in (

let _83_1038 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (fsym, cvar_sorts, f_decls))
in (f, f_decls)))))
end))))))))
end)
end))))
end))
end)))
end
end))))
end))
end
| FStar_Syntax_Syntax.Tm_let ((_83_1041, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_83_1053); FStar_Syntax_Syntax.lbunivs = _83_1051; FStar_Syntax_Syntax.lbtyp = _83_1049; FStar_Syntax_Syntax.lbeff = _83_1047; FStar_Syntax_Syntax.lbdef = _83_1045}::_83_1043), _83_1059) -> begin
(FStar_All.failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _83_1068; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _83_1065; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (_83_1078) -> begin
(

let _83_1080 = (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (

let e = (varops.fresh "let-rec")
in (

let decl_e = FStar_SMTEncoding_Term.DeclFun ((e, [], FStar_SMTEncoding_Term.Term_sort, None))
in (let _172_683 = (FStar_SMTEncoding_Term.mkFreeV (e, FStar_SMTEncoding_Term.Term_sort))
in (_172_683, (decl_e)::[])))))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end))))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (

let _83_1096 = (encode_term e1 env)
in (match (_83_1096) with
| (ee1, decls1) -> begin
(

let _83_1099 = (FStar_Syntax_Subst.open_term (((x, None))::[]) e2)
in (match (_83_1099) with
| (xs, e2) -> begin
(

let _83_1103 = (FStar_List.hd xs)
in (match (_83_1103) with
| (x, _83_1102) -> begin
(

let env' = (push_term_var env x ee1)
in (

let _83_1107 = (encode_body e2 env')
in (match (_83_1107) with
| (ee2, decls2) -> begin
(ee2, (FStar_List.append decls1 decls2))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (

let _83_1115 = (encode_term e env)
in (match (_83_1115) with
| (scr, decls) -> begin
(

let _83_1152 = (FStar_List.fold_right (fun b _83_1119 -> (match (_83_1119) with
| (else_case, decls) -> begin
(

let _83_1123 = (FStar_Syntax_Subst.open_branch b)
in (match (_83_1123) with
| (p, w, br) -> begin
(

let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun _83_1127 _83_1130 -> (match ((_83_1127, _83_1130)) with
| ((env0, pattern), (else_case, decls)) -> begin
(

let guard = (pattern.guard scr)
in (

let projections = (pattern.projections scr)
in (

let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env _83_1136 -> (match (_83_1136) with
| (x, t) -> begin
(push_term_var env x t)
end)) env))
in (

let _83_1146 = (match (w) with
| None -> begin
(guard, [])
end
| Some (w) -> begin
(

let _83_1143 = (encode_term w env)
in (match (_83_1143) with
| (w, decls2) -> begin
(let _172_717 = (let _172_716 = (let _172_715 = (let _172_714 = (let _172_713 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Term.mkTrue)
in (w, _172_713))
in (FStar_SMTEncoding_Term.mkEq _172_714))
in (guard, _172_715))
in (FStar_SMTEncoding_Term.mkAnd _172_716))
in (_172_717, decls2))
end))
end)
in (match (_83_1146) with
| (guard, decls2) -> begin
(

let _83_1149 = (encode_br br env)
in (match (_83_1149) with
| (br, decls3) -> begin
(let _172_718 = (FStar_SMTEncoding_Term.mkITE (guard, br, else_case))
in (_172_718, (FStar_List.append (FStar_List.append decls decls2) decls3)))
end))
end)))))
end)) patterns (else_case, decls)))
end))
end)) pats (default_case, decls))
in (match (_83_1152) with
| (match_tm, decls) -> begin
(match_tm, decls)
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _83_1158 -> begin
(let _172_721 = (encode_one_pat env pat)
in (_172_721)::[])
end))
and encode_one_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> (

let _83_1161 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _172_724 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" _172_724))
end else begin
()
end
in (

let _83_1165 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (_83_1165) with
| (vars, pat_term) -> begin
(

let _83_1177 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun _83_1168 v -> (match (_83_1168) with
| (env, vars) -> begin
(

let _83_1174 = (gen_term_var env v)
in (match (_83_1174) with
| (xx, _83_1172, env) -> begin
(env, ((v, (xx, FStar_SMTEncoding_Term.Term_sort)))::vars)
end))
end)) (env, [])))
in (match (_83_1177) with
| (env, vars) -> begin
(

let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_83_1182) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_dot_term (_)) -> begin
FStar_SMTEncoding_Term.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _172_732 = (let _172_731 = (encode_const c)
in (scrutinee, _172_731))
in (FStar_SMTEncoding_Term.mkEq _172_732))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let is_f = (mk_data_tester env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _83_1204 -> (match (_83_1204) with
| (arg, _83_1203) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _172_735 = (FStar_SMTEncoding_Term.mkApp (proj, (scrutinee)::[]))
in (mk_guard arg _172_735)))
end))))
in (FStar_SMTEncoding_Term.mk_and_l ((is_f)::sub_term_guards))))
end))
in (

let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_83_1211) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _)) | (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
((x, scrutinee))::[]
end
| FStar_Syntax_Syntax.Pat_constant (_83_1221) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(let _172_743 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _83_1231 -> (match (_83_1231) with
| (arg, _83_1230) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _172_742 = (FStar_SMTEncoding_Term.mkApp (proj, (scrutinee)::[]))
in (mk_projections arg _172_742)))
end))))
in (FStar_All.pipe_right _172_743 FStar_List.flatten))
end))
in (

let pat_term = (fun _83_1234 -> (match (()) with
| () -> begin
(encode_term pat_term env)
end))
in (

let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in (env, pattern)))))
end))
end))))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (

let _83_1250 = (FStar_All.pipe_right l (FStar_List.fold_left (fun _83_1240 _83_1244 -> (match ((_83_1240, _83_1244)) with
| ((tms, decls), (t, _83_1243)) -> begin
(

let _83_1247 = (encode_term t env)
in (match (_83_1247) with
| (t, decls') -> begin
((t)::tms, (FStar_List.append decls decls'))
end))
end)) ([], [])))
in (match (_83_1250) with
| (l, decls) -> begin
((FStar_List.rev l), decls)
end)))
and encode_function_type_as_formula : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun induction_on new_pats t env -> (

let rec list_elements = (fun e -> (

let _83_1259 = (let _172_756 = (FStar_Syntax_Util.unmeta e)
in (FStar_Syntax_Util.head_and_args _172_756))
in (match (_83_1259) with
| (head, args) -> begin
(match ((let _172_758 = (let _172_757 = (FStar_Syntax_Util.un_uinst head)
in _172_757.FStar_Syntax_Syntax.n)
in (_172_758, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), _83_1263) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid) -> begin
[]
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _83_1276::(hd, _83_1273)::(tl, _83_1269)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid) -> begin
(let _172_759 = (list_elements tl)
in (hd)::_172_759)
end
| _83_1280 -> begin
(

let _83_1281 = (FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern")
in [])
end)
end)))
in (

let one_pat = (fun p -> (

let _83_1287 = (let _172_762 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right _172_762 FStar_Syntax_Util.head_and_args))
in (match (_83_1287) with
| (head, args) -> begin
(match ((let _172_764 = (let _172_763 = (FStar_Syntax_Util.un_uinst head)
in _172_763.FStar_Syntax_Syntax.n)
in (_172_764, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_83_1295, _83_1297)::(e, _83_1292)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpat_lid) -> begin
(e, None)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (e, _83_1305)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatT_lid) -> begin
(e, None)
end
| _83_1310 -> begin
(FStar_All.failwith "Unexpected pattern term")
end)
end)))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements p)
in (

let smt_pat_or = (fun t -> (

let _83_1318 = (let _172_769 = (FStar_Syntax_Util.unmeta t)
in (FStar_All.pipe_right _172_769 FStar_Syntax_Util.head_and_args))
in (match (_83_1318) with
| (head, args) -> begin
(match ((let _172_771 = (let _172_770 = (FStar_Syntax_Util.un_uinst head)
in _172_770.FStar_Syntax_Syntax.n)
in (_172_771, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (e, _83_1323)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatOr_lid) -> begin
Some (e)
end
| _83_1328 -> begin
None
end)
end)))
in (match (elts) with
| t::[] -> begin
(match ((smt_pat_or t)) with
| Some (e) -> begin
(let _172_774 = (list_elements e)
in (FStar_All.pipe_right _172_774 (FStar_List.map (fun branch -> (let _172_773 = (list_elements branch)
in (FStar_All.pipe_right _172_773 (FStar_List.map one_pat)))))))
end
| _83_1335 -> begin
(let _172_775 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_172_775)::[])
end)
end
| _83_1337 -> begin
(let _172_776 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_172_776)::[])
end))))
in (

let _83_1371 = (match ((let _172_777 = (FStar_Syntax_Subst.compress t)
in _172_777.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _83_1344 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_83_1344) with
| (binders, c) -> begin
(

let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| (pre, _83_1356)::(post, _83_1352)::(pats, _83_1348)::[] -> begin
(

let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _172_778 = (lemma_pats pats')
in (binders, pre, post, _172_778)))
end
| _83_1364 -> begin
(FStar_All.failwith "impos")
end))
end))
end
| _83_1366 -> begin
(FStar_All.failwith "Impos")
end)
in (match (_83_1371) with
| (binders, pre, post, patterns) -> begin
(

let _83_1378 = (encode_binders None binders env)
in (match (_83_1378) with
| (vars, guards, env, decls, _83_1377) -> begin
(

let _83_1391 = (let _172_782 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (

let _83_1388 = (let _172_781 = (FStar_All.pipe_right branch (FStar_List.map (fun _83_1383 -> (match (_83_1383) with
| (t, _83_1382) -> begin
(encode_term t (

let _83_1384 = env
in {bindings = _83_1384.bindings; depth = _83_1384.depth; tcenv = _83_1384.tcenv; warn = _83_1384.warn; cache = _83_1384.cache; nolabels = _83_1384.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _83_1384.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _172_781 FStar_List.unzip))
in (match (_83_1388) with
| (pats, decls) -> begin
(pats, decls)
end)))))
in (FStar_All.pipe_right _172_782 FStar_List.unzip))
in (match (_83_1391) with
| (pats, decls') -> begin
(

let decls' = (FStar_List.flatten decls')
in (

let pats = (match (induction_on) with
| None -> begin
pats
end
| Some (e) -> begin
(match (vars) with
| [] -> begin
pats
end
| l::[] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _172_785 = (let _172_784 = (FStar_SMTEncoding_Term.mkFreeV l)
in (FStar_SMTEncoding_Term.mk_Precedes _172_784 e))
in (_172_785)::p))))
end
| _83_1401 -> begin
(

let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _172_791 = (FStar_SMTEncoding_Term.mk_Precedes tl e)
in (_172_791)::p))))
end
| (x, FStar_SMTEncoding_Term.Term_sort)::vars -> begin
(let _172_793 = (let _172_792 = (FStar_SMTEncoding_Term.mkFreeV (x, FStar_SMTEncoding_Term.Term_sort))
in (FStar_SMTEncoding_Term.mk_LexCons _172_792 tl))
in (aux _172_793 vars))
end
| _83_1413 -> begin
pats
end))
in (let _172_794 = (FStar_SMTEncoding_Term.mkFreeV ("Prims.LexTop", FStar_SMTEncoding_Term.Term_sort))
in (aux _172_794 vars)))
end)
end)
in (

let env = (

let _83_1415 = env
in {bindings = _83_1415.bindings; depth = _83_1415.depth; tcenv = _83_1415.tcenv; warn = _83_1415.warn; cache = _83_1415.cache; nolabels = true; use_zfuel_name = _83_1415.use_zfuel_name; encode_non_total_function_typ = _83_1415.encode_non_total_function_typ})
in (

let _83_1420 = (let _172_795 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula _172_795 env))
in (match (_83_1420) with
| (pre, decls'') -> begin
(

let _83_1423 = (let _172_796 = (FStar_Syntax_Util.unmeta post)
in (encode_formula _172_796 env))
in (match (_83_1423) with
| (post, decls''') -> begin
(

let decls = (FStar_List.append (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'') decls''')
in (let _172_801 = (let _172_800 = (let _172_799 = (let _172_798 = (let _172_797 = (FStar_SMTEncoding_Term.mk_and_l ((pre)::guards))
in (_172_797, post))
in (FStar_SMTEncoding_Term.mkImp _172_798))
in (pats, vars, _172_799))
in (FStar_SMTEncoding_Term.mkForall _172_800))
in (_172_801, decls)))
end))
end)))))
end))
end))
end))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (

let debug = (fun phi -> if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _172_807 = (FStar_Syntax_Print.tag_of_term phi)
in (let _172_806 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print2 "Formula (%s)  %s\n" _172_807 _172_806)))
end else begin
()
end)
in (

let enc = (fun f l -> (

let _83_1439 = (FStar_Util.fold_map (fun decls x -> (

let _83_1436 = (encode_term (Prims.fst x) env)
in (match (_83_1436) with
| (t, decls') -> begin
((FStar_List.append decls decls'), t)
end))) [] l)
in (match (_83_1439) with
| (decls, args) -> begin
(let _172_823 = (f args)
in (_172_823, decls))
end)))
in (

let const_op = (fun f _83_1442 -> (f, []))
in (

let un_op = (fun f l -> (let _172_837 = (FStar_List.hd l)
in (FStar_All.pipe_left f _172_837)))
in (

let bin_op = (fun f _83_9 -> (match (_83_9) with
| t1::t2::[] -> begin
(f (t1, t2))
end
| _83_1453 -> begin
(FStar_All.failwith "Impossible")
end))
in (

let enc_prop_c = (fun f l -> (

let _83_1468 = (FStar_Util.fold_map (fun decls _83_1462 -> (match (_83_1462) with
| (t, _83_1461) -> begin
(

let _83_1465 = (encode_formula t env)
in (match (_83_1465) with
| (phi, decls') -> begin
((FStar_List.append decls decls'), phi)
end))
end)) [] l)
in (match (_83_1468) with
| (decls, phis) -> begin
(let _172_862 = (f phis)
in (_172_862, decls))
end)))
in (

let eq_op = (fun _83_10 -> (match (_83_10) with
| _83_1475::_83_1473::e1::e2::[] -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) l)
end))
in (

let mk_imp = (fun _83_11 -> (match (_83_11) with
| (lhs, _83_1486)::(rhs, _83_1482)::[] -> begin
(

let _83_1491 = (encode_formula rhs env)
in (match (_83_1491) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _83_1494) -> begin
(l1, decls1)
end
| _83_1498 -> begin
(

let _83_1501 = (encode_formula lhs env)
in (match (_83_1501) with
| (l2, decls2) -> begin
(let _172_867 = (FStar_SMTEncoding_Term.mkImp (l2, l1))
in (_172_867, (FStar_List.append decls1 decls2)))
end))
end)
end))
end
| _83_1503 -> begin
(FStar_All.failwith "impossible")
end))
in (

let mk_ite = (fun _83_12 -> (match (_83_12) with
| (guard, _83_1516)::(_then, _83_1512)::(_else, _83_1508)::[] -> begin
(

let _83_1521 = (encode_formula guard env)
in (match (_83_1521) with
| (g, decls1) -> begin
(

let _83_1524 = (encode_formula _then env)
in (match (_83_1524) with
| (t, decls2) -> begin
(

let _83_1527 = (encode_formula _else env)
in (match (_83_1527) with
| (e, decls3) -> begin
(

let res = (FStar_SMTEncoding_Term.mkITE (g, t, e))
in (res, (FStar_List.append (FStar_List.append decls1 decls2) decls3)))
end))
end))
end))
end
| _83_1530 -> begin
(FStar_All.failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (let _172_879 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f _172_879)))
in (

let connectives = (let _172_932 = (let _172_888 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkAnd))
in (FStar_Syntax_Const.and_lid, _172_888))
in (let _172_931 = (let _172_930 = (let _172_894 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkOr))
in (FStar_Syntax_Const.or_lid, _172_894))
in (let _172_929 = (let _172_928 = (let _172_927 = (let _172_903 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkIff))
in (FStar_Syntax_Const.iff_lid, _172_903))
in (let _172_926 = (let _172_925 = (let _172_924 = (let _172_912 = (FStar_All.pipe_left enc_prop_c (un_op FStar_SMTEncoding_Term.mkNot))
in (FStar_Syntax_Const.not_lid, _172_912))
in (_172_924)::((FStar_Syntax_Const.eq2_lid, eq_op))::((FStar_Syntax_Const.true_lid, (const_op FStar_SMTEncoding_Term.mkTrue)))::((FStar_Syntax_Const.false_lid, (const_op FStar_SMTEncoding_Term.mkFalse)))::[])
in ((FStar_Syntax_Const.ite_lid, mk_ite))::_172_925)
in (_172_927)::_172_926))
in ((FStar_Syntax_Const.imp_lid, mk_imp))::_172_928)
in (_172_930)::_172_929))
in (_172_932)::_172_931))
in (

let rec fallback = (fun phi -> (match (phi.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(

let _83_1548 = (encode_formula phi' env)
in (match (_83_1548) with
| (phi, decls) -> begin
(let _172_935 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled ((phi, msg, r))))
in (_172_935, decls))
end))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(

let _83_1555 = (encode_match e pats FStar_SMTEncoding_Term.mkFalse env encode_formula)
in (match (_83_1555) with
| (t, decls) -> begin
(t, decls)
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _83_1562; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _83_1559; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(

let _83_1573 = (encode_let x t1 e1 e2 env encode_formula)
in (match (_83_1573) with
| (t, decls) -> begin
(t, decls)
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let head = (FStar_Syntax_Util.un_uinst head)
in (match ((head.FStar_Syntax_Syntax.n, args)) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), _83_1590::(x, _83_1587)::(t, _83_1583)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.has_type_lid) -> begin
(

let _83_1595 = (encode_term x env)
in (match (_83_1595) with
| (x, decls) -> begin
(

let _83_1598 = (encode_term t env)
in (match (_83_1598) with
| (t, decls') -> begin
(let _172_936 = (FStar_SMTEncoding_Term.mk_HasType x t)
in (_172_936, (FStar_List.append decls decls')))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (r, _83_1611)::(msg, _83_1607)::(phi, _83_1603)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.labeled_lid) -> begin
(match ((let _172_940 = (let _172_937 = (FStar_Syntax_Subst.compress r)
in _172_937.FStar_Syntax_Syntax.n)
in (let _172_939 = (let _172_938 = (FStar_Syntax_Subst.compress msg)
in _172_938.FStar_Syntax_Syntax.n)
in (_172_940, _172_939)))) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, _83_1620))) -> begin
(

let phi = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((phi, FStar_Syntax_Syntax.Meta_labeled (((FStar_Util.string_of_unicode s), r, false))))) None r)
in (fallback phi))
end
| _83_1627 -> begin
(fallback phi)
end)
end
| _83_1629 when (head_redex env head) -> begin
(let _172_941 = (whnf env phi)
in (encode_formula _172_941 env))
end
| _83_1631 -> begin
(

let _83_1634 = (encode_term phi env)
in (match (_83_1634) with
| (tt, decls) -> begin
(let _172_942 = (FStar_SMTEncoding_Term.mk_Valid tt)
in (_172_942, decls))
end))
end))
end
| _83_1636 -> begin
(

let _83_1639 = (encode_term phi env)
in (match (_83_1639) with
| (tt, decls) -> begin
(let _172_943 = (FStar_SMTEncoding_Term.mk_Valid tt)
in (_172_943, decls))
end))
end))
in (

let encode_q_body = (fun env bs ps body -> (

let _83_1651 = (encode_binders None bs env)
in (match (_83_1651) with
| (vars, guards, env, decls, _83_1650) -> begin
(

let _83_1664 = (let _172_955 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let _83_1661 = (let _172_954 = (FStar_All.pipe_right p (FStar_List.map (fun _83_1656 -> (match (_83_1656) with
| (t, _83_1655) -> begin
(encode_term t (

let _83_1657 = env
in {bindings = _83_1657.bindings; depth = _83_1657.depth; tcenv = _83_1657.tcenv; warn = _83_1657.warn; cache = _83_1657.cache; nolabels = _83_1657.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _83_1657.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _172_954 FStar_List.unzip))
in (match (_83_1661) with
| (p, decls) -> begin
(p, (FStar_List.flatten decls))
end)))))
in (FStar_All.pipe_right _172_955 FStar_List.unzip))
in (match (_83_1664) with
| (pats, decls') -> begin
(

let _83_1667 = (encode_formula body env)
in (match (_83_1667) with
| (body, decls'') -> begin
(let _172_956 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (vars, pats, _172_956, body, (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'')))
end))
end))
end)))
in (

let _83_1668 = (debug phi)
in (

let phi = (FStar_Syntax_Util.unascribe phi)
in (match ((FStar_Syntax_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _83_1680 -> (match (_83_1680) with
| (l, _83_1679) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_83_1683, f) -> begin
(f arms)
end)
end
| Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
(

let _83_1693 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _172_973 = (FStar_All.pipe_right vars (FStar_Syntax_Print.binders_to_string "; "))
in (FStar_Util.print1 ">>>> Got QALL [%s]\n" _172_973))
end else begin
()
end
in (

let _83_1700 = (encode_q_body env vars pats body)
in (match (_83_1700) with
| (vars, pats, guard, body, decls) -> begin
(

let tm = (let _172_975 = (let _172_974 = (FStar_SMTEncoding_Term.mkImp (guard, body))
in (pats, vars, _172_974))
in (FStar_SMTEncoding_Term.mkForall _172_975))
in (

let _83_1702 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _172_976 = (FStar_SMTEncoding_Term.termToSmt tm)
in (FStar_Util.print1 ">>>> Encoded QALL to %s\n" _172_976))
end else begin
()
end
in (tm, decls)))
end)))
end
| Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
(

let _83_1715 = (encode_q_body env vars pats body)
in (match (_83_1715) with
| (vars, pats, guard, body, decls) -> begin
(let _172_979 = (let _172_978 = (let _172_977 = (FStar_SMTEncoding_Term.mkAnd (guard, body))
in (pats, vars, _172_977))
in (FStar_SMTEncoding_Term.mkExists _172_978))
in (_172_979, decls))
end))
end)))))))))))))))))


type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.decl Prims.list; is : FStar_Ident.lident  ->  Prims.bool}


let is_Mkprims_t : prims_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkprims_t"))))


let prims : prims_t = (

let _83_1721 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (_83_1721) with
| (asym, a) -> begin
(

let _83_1724 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_83_1724) with
| (xsym, x) -> begin
(

let _83_1727 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (_83_1727) with
| (ysym, y) -> begin
(

let deffun = (fun vars body x -> (FStar_SMTEncoding_Term.DefineFun ((x, vars, FStar_SMTEncoding_Term.Term_sort, body, None)))::[])
in (

let quant = (fun vars body x -> (

let t1 = (let _172_1022 = (let _172_1021 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (x, _172_1021))
in (FStar_SMTEncoding_Term.mkApp _172_1022))
in (

let vname_decl = (let _172_1024 = (let _172_1023 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (x, _172_1023, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_172_1024))
in (let _172_1030 = (let _172_1029 = (let _172_1028 = (let _172_1027 = (let _172_1026 = (let _172_1025 = (FStar_SMTEncoding_Term.mkEq (t1, body))
in (((t1)::[])::[], vars, _172_1025))
in (FStar_SMTEncoding_Term.mkForall _172_1026))
in (_172_1027, None, Some ((Prims.strcat "primitive_" x))))
in FStar_SMTEncoding_Term.Assume (_172_1028))
in (_172_1029)::[])
in (vname_decl)::_172_1030))))
in (

let axy = ((asym, FStar_SMTEncoding_Term.Term_sort))::((xsym, FStar_SMTEncoding_Term.Term_sort))::((ysym, FStar_SMTEncoding_Term.Term_sort))::[]
in (

let xy = ((xsym, FStar_SMTEncoding_Term.Term_sort))::((ysym, FStar_SMTEncoding_Term.Term_sort))::[]
in (

let qx = ((xsym, FStar_SMTEncoding_Term.Term_sort))::[]
in (

let prims = (let _172_1190 = (let _172_1039 = (let _172_1038 = (let _172_1037 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _172_1037))
in (quant axy _172_1038))
in (FStar_Syntax_Const.op_Eq, _172_1039))
in (let _172_1189 = (let _172_1188 = (let _172_1046 = (let _172_1045 = (let _172_1044 = (let _172_1043 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (FStar_SMTEncoding_Term.mkNot _172_1043))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _172_1044))
in (quant axy _172_1045))
in (FStar_Syntax_Const.op_notEq, _172_1046))
in (let _172_1187 = (let _172_1186 = (let _172_1055 = (let _172_1054 = (let _172_1053 = (let _172_1052 = (let _172_1051 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _172_1050 = (FStar_SMTEncoding_Term.unboxInt y)
in (_172_1051, _172_1050)))
in (FStar_SMTEncoding_Term.mkLT _172_1052))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _172_1053))
in (quant xy _172_1054))
in (FStar_Syntax_Const.op_LT, _172_1055))
in (let _172_1185 = (let _172_1184 = (let _172_1064 = (let _172_1063 = (let _172_1062 = (let _172_1061 = (let _172_1060 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _172_1059 = (FStar_SMTEncoding_Term.unboxInt y)
in (_172_1060, _172_1059)))
in (FStar_SMTEncoding_Term.mkLTE _172_1061))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _172_1062))
in (quant xy _172_1063))
in (FStar_Syntax_Const.op_LTE, _172_1064))
in (let _172_1183 = (let _172_1182 = (let _172_1073 = (let _172_1072 = (let _172_1071 = (let _172_1070 = (let _172_1069 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _172_1068 = (FStar_SMTEncoding_Term.unboxInt y)
in (_172_1069, _172_1068)))
in (FStar_SMTEncoding_Term.mkGT _172_1070))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _172_1071))
in (quant xy _172_1072))
in (FStar_Syntax_Const.op_GT, _172_1073))
in (let _172_1181 = (let _172_1180 = (let _172_1082 = (let _172_1081 = (let _172_1080 = (let _172_1079 = (let _172_1078 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _172_1077 = (FStar_SMTEncoding_Term.unboxInt y)
in (_172_1078, _172_1077)))
in (FStar_SMTEncoding_Term.mkGTE _172_1079))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _172_1080))
in (quant xy _172_1081))
in (FStar_Syntax_Const.op_GTE, _172_1082))
in (let _172_1179 = (let _172_1178 = (let _172_1091 = (let _172_1090 = (let _172_1089 = (let _172_1088 = (let _172_1087 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _172_1086 = (FStar_SMTEncoding_Term.unboxInt y)
in (_172_1087, _172_1086)))
in (FStar_SMTEncoding_Term.mkSub _172_1088))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _172_1089))
in (quant xy _172_1090))
in (FStar_Syntax_Const.op_Subtraction, _172_1091))
in (let _172_1177 = (let _172_1176 = (let _172_1098 = (let _172_1097 = (let _172_1096 = (let _172_1095 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Term.mkMinus _172_1095))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _172_1096))
in (quant qx _172_1097))
in (FStar_Syntax_Const.op_Minus, _172_1098))
in (let _172_1175 = (let _172_1174 = (let _172_1107 = (let _172_1106 = (let _172_1105 = (let _172_1104 = (let _172_1103 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _172_1102 = (FStar_SMTEncoding_Term.unboxInt y)
in (_172_1103, _172_1102)))
in (FStar_SMTEncoding_Term.mkAdd _172_1104))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _172_1105))
in (quant xy _172_1106))
in (FStar_Syntax_Const.op_Addition, _172_1107))
in (let _172_1173 = (let _172_1172 = (let _172_1116 = (let _172_1115 = (let _172_1114 = (let _172_1113 = (let _172_1112 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _172_1111 = (FStar_SMTEncoding_Term.unboxInt y)
in (_172_1112, _172_1111)))
in (FStar_SMTEncoding_Term.mkMul _172_1113))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _172_1114))
in (quant xy _172_1115))
in (FStar_Syntax_Const.op_Multiply, _172_1116))
in (let _172_1171 = (let _172_1170 = (let _172_1125 = (let _172_1124 = (let _172_1123 = (let _172_1122 = (let _172_1121 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _172_1120 = (FStar_SMTEncoding_Term.unboxInt y)
in (_172_1121, _172_1120)))
in (FStar_SMTEncoding_Term.mkDiv _172_1122))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _172_1123))
in (quant xy _172_1124))
in (FStar_Syntax_Const.op_Division, _172_1125))
in (let _172_1169 = (let _172_1168 = (let _172_1134 = (let _172_1133 = (let _172_1132 = (let _172_1131 = (let _172_1130 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _172_1129 = (FStar_SMTEncoding_Term.unboxInt y)
in (_172_1130, _172_1129)))
in (FStar_SMTEncoding_Term.mkMod _172_1131))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _172_1132))
in (quant xy _172_1133))
in (FStar_Syntax_Const.op_Modulus, _172_1134))
in (let _172_1167 = (let _172_1166 = (let _172_1143 = (let _172_1142 = (let _172_1141 = (let _172_1140 = (let _172_1139 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _172_1138 = (FStar_SMTEncoding_Term.unboxBool y)
in (_172_1139, _172_1138)))
in (FStar_SMTEncoding_Term.mkAnd _172_1140))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _172_1141))
in (quant xy _172_1142))
in (FStar_Syntax_Const.op_And, _172_1143))
in (let _172_1165 = (let _172_1164 = (let _172_1152 = (let _172_1151 = (let _172_1150 = (let _172_1149 = (let _172_1148 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _172_1147 = (FStar_SMTEncoding_Term.unboxBool y)
in (_172_1148, _172_1147)))
in (FStar_SMTEncoding_Term.mkOr _172_1149))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _172_1150))
in (quant xy _172_1151))
in (FStar_Syntax_Const.op_Or, _172_1152))
in (let _172_1163 = (let _172_1162 = (let _172_1159 = (let _172_1158 = (let _172_1157 = (let _172_1156 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Term.mkNot _172_1156))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _172_1157))
in (quant qx _172_1158))
in (FStar_Syntax_Const.op_Negation, _172_1159))
in (_172_1162)::[])
in (_172_1164)::_172_1163))
in (_172_1166)::_172_1165))
in (_172_1168)::_172_1167))
in (_172_1170)::_172_1169))
in (_172_1172)::_172_1171))
in (_172_1174)::_172_1173))
in (_172_1176)::_172_1175))
in (_172_1178)::_172_1177))
in (_172_1180)::_172_1179))
in (_172_1182)::_172_1181))
in (_172_1184)::_172_1183))
in (_172_1186)::_172_1185))
in (_172_1188)::_172_1187))
in (_172_1190)::_172_1189))
in (

let mk = (fun l v -> (let _172_1222 = (FStar_All.pipe_right prims (FStar_List.filter (fun _83_1747 -> (match (_83_1747) with
| (l', _83_1746) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right _172_1222 (FStar_List.collect (fun _83_1751 -> (match (_83_1751) with
| (_83_1749, b) -> begin
(b v)
end))))))
in (

let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _83_1757 -> (match (_83_1757) with
| (l', _83_1756) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is}))))))))
end))
end))
end))


let pretype_axiom : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun tapp vars -> (

let _83_1763 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_83_1763) with
| (xxsym, xx) -> begin
(

let _83_1766 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_83_1766) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (let _172_1250 = (let _172_1249 = (let _172_1246 = (let _172_1245 = (let _172_1244 = (let _172_1243 = (let _172_1242 = (let _172_1241 = (FStar_SMTEncoding_Term.mkApp ("PreType", (xx)::[]))
in (tapp, _172_1241))
in (FStar_SMTEncoding_Term.mkEq _172_1242))
in (xx_has_type, _172_1243))
in (FStar_SMTEncoding_Term.mkImp _172_1244))
in (((xx_has_type)::[])::[], ((xxsym, FStar_SMTEncoding_Term.Term_sort))::((ffsym, FStar_SMTEncoding_Term.Fuel_sort))::vars, _172_1245))
in (FStar_SMTEncoding_Term.mkForall _172_1246))
in (let _172_1248 = (let _172_1247 = (varops.fresh "pretyping_")
in Some (_172_1247))
in (_172_1249, Some ("pretyping"), _172_1248)))
in FStar_SMTEncoding_Term.Assume (_172_1250)))
end))
end)))


let primitive_type_axioms : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.decl Prims.list = (

let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (

let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (

let yy = ("y", FStar_SMTEncoding_Term.Term_sort)
in (

let y = (FStar_SMTEncoding_Term.mkFreeV yy)
in (

let mk_unit = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (let _172_1271 = (let _172_1262 = (let _172_1261 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in (_172_1261, Some ("unit typing"), Some ("unit_typing")))
in FStar_SMTEncoding_Term.Assume (_172_1262))
in (let _172_1270 = (let _172_1269 = (let _172_1268 = (let _172_1267 = (let _172_1266 = (let _172_1265 = (let _172_1264 = (let _172_1263 = (FStar_SMTEncoding_Term.mkEq (x, FStar_SMTEncoding_Term.mk_Term_unit))
in (typing_pred, _172_1263))
in (FStar_SMTEncoding_Term.mkImp _172_1264))
in (((typing_pred)::[])::[], (xx)::[], _172_1265))
in (mkForall_fuel _172_1266))
in (_172_1267, Some ("unit inversion"), Some ("unit_inversion")))
in FStar_SMTEncoding_Term.Assume (_172_1268))
in (_172_1269)::[])
in (_172_1271)::_172_1270))))
in (

let mk_bool = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _172_1294 = (let _172_1285 = (let _172_1284 = (let _172_1283 = (let _172_1282 = (let _172_1279 = (let _172_1278 = (FStar_SMTEncoding_Term.boxBool b)
in (_172_1278)::[])
in (_172_1279)::[])
in (let _172_1281 = (let _172_1280 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType _172_1280 tt))
in (_172_1282, (bb)::[], _172_1281)))
in (FStar_SMTEncoding_Term.mkForall _172_1283))
in (_172_1284, Some ("bool typing"), Some ("bool_typing")))
in FStar_SMTEncoding_Term.Assume (_172_1285))
in (let _172_1293 = (let _172_1292 = (let _172_1291 = (let _172_1290 = (let _172_1289 = (let _172_1288 = (let _172_1287 = (let _172_1286 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in (typing_pred, _172_1286))
in (FStar_SMTEncoding_Term.mkImp _172_1287))
in (((typing_pred)::[])::[], (xx)::[], _172_1288))
in (mkForall_fuel _172_1289))
in (_172_1290, Some ("bool inversion"), Some ("bool_inversion")))
in FStar_SMTEncoding_Term.Assume (_172_1291))
in (_172_1292)::[])
in (_172_1294)::_172_1293))))))
in (

let mk_int = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let typing_pred_y = (FStar_SMTEncoding_Term.mk_HasType y tt)
in (

let aa = ("a", FStar_SMTEncoding_Term.Int_sort)
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let bb = ("b", FStar_SMTEncoding_Term.Int_sort)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (

let precedes = (let _172_1308 = (let _172_1307 = (let _172_1306 = (let _172_1305 = (let _172_1304 = (let _172_1303 = (FStar_SMTEncoding_Term.boxInt a)
in (let _172_1302 = (let _172_1301 = (FStar_SMTEncoding_Term.boxInt b)
in (_172_1301)::[])
in (_172_1303)::_172_1302))
in (tt)::_172_1304)
in (tt)::_172_1305)
in ("Prims.Precedes", _172_1306))
in (FStar_SMTEncoding_Term.mkApp _172_1307))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _172_1308))
in (

let precedes_y_x = (let _172_1309 = (FStar_SMTEncoding_Term.mkApp ("Precedes", (y)::(x)::[]))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _172_1309))
in (let _172_1351 = (let _172_1317 = (let _172_1316 = (let _172_1315 = (let _172_1314 = (let _172_1311 = (let _172_1310 = (FStar_SMTEncoding_Term.boxInt b)
in (_172_1310)::[])
in (_172_1311)::[])
in (let _172_1313 = (let _172_1312 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType _172_1312 tt))
in (_172_1314, (bb)::[], _172_1313)))
in (FStar_SMTEncoding_Term.mkForall _172_1315))
in (_172_1316, Some ("int typing"), Some ("int_typing")))
in FStar_SMTEncoding_Term.Assume (_172_1317))
in (let _172_1350 = (let _172_1349 = (let _172_1323 = (let _172_1322 = (let _172_1321 = (let _172_1320 = (let _172_1319 = (let _172_1318 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in (typing_pred, _172_1318))
in (FStar_SMTEncoding_Term.mkImp _172_1319))
in (((typing_pred)::[])::[], (xx)::[], _172_1320))
in (mkForall_fuel _172_1321))
in (_172_1322, Some ("int inversion"), Some ("int_inversion")))
in FStar_SMTEncoding_Term.Assume (_172_1323))
in (let _172_1348 = (let _172_1347 = (let _172_1346 = (let _172_1345 = (let _172_1344 = (let _172_1343 = (let _172_1342 = (let _172_1341 = (let _172_1340 = (let _172_1339 = (let _172_1338 = (let _172_1337 = (let _172_1326 = (let _172_1325 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _172_1324 = (FStar_SMTEncoding_Term.mkInteger' 0)
in (_172_1325, _172_1324)))
in (FStar_SMTEncoding_Term.mkGT _172_1326))
in (let _172_1336 = (let _172_1335 = (let _172_1329 = (let _172_1328 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _172_1327 = (FStar_SMTEncoding_Term.mkInteger' 0)
in (_172_1328, _172_1327)))
in (FStar_SMTEncoding_Term.mkGTE _172_1329))
in (let _172_1334 = (let _172_1333 = (let _172_1332 = (let _172_1331 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _172_1330 = (FStar_SMTEncoding_Term.unboxInt x)
in (_172_1331, _172_1330)))
in (FStar_SMTEncoding_Term.mkLT _172_1332))
in (_172_1333)::[])
in (_172_1335)::_172_1334))
in (_172_1337)::_172_1336))
in (typing_pred_y)::_172_1338)
in (typing_pred)::_172_1339)
in (FStar_SMTEncoding_Term.mk_and_l _172_1340))
in (_172_1341, precedes_y_x))
in (FStar_SMTEncoding_Term.mkImp _172_1342))
in (((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[], (xx)::(yy)::[], _172_1343))
in (mkForall_fuel _172_1344))
in (_172_1345, Some ("well-founded ordering on nat (alt)"), Some ("well-founded-ordering-on-nat")))
in FStar_SMTEncoding_Term.Assume (_172_1346))
in (_172_1347)::[])
in (_172_1349)::_172_1348))
in (_172_1351)::_172_1350)))))))))))
in (

let mk_str = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = ("b", FStar_SMTEncoding_Term.String_sort)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _172_1374 = (let _172_1365 = (let _172_1364 = (let _172_1363 = (let _172_1362 = (let _172_1359 = (let _172_1358 = (FStar_SMTEncoding_Term.boxString b)
in (_172_1358)::[])
in (_172_1359)::[])
in (let _172_1361 = (let _172_1360 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType _172_1360 tt))
in (_172_1362, (bb)::[], _172_1361)))
in (FStar_SMTEncoding_Term.mkForall _172_1363))
in (_172_1364, Some ("string typing"), Some ("string_typing")))
in FStar_SMTEncoding_Term.Assume (_172_1365))
in (let _172_1373 = (let _172_1372 = (let _172_1371 = (let _172_1370 = (let _172_1369 = (let _172_1368 = (let _172_1367 = (let _172_1366 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in (typing_pred, _172_1366))
in (FStar_SMTEncoding_Term.mkImp _172_1367))
in (((typing_pred)::[])::[], (xx)::[], _172_1368))
in (mkForall_fuel _172_1369))
in (_172_1370, Some ("string inversion"), Some ("string_inversion")))
in FStar_SMTEncoding_Term.Assume (_172_1371))
in (_172_1372)::[])
in (_172_1374)::_172_1373))))))
in (

let mk_ref = (fun env reft_name _83_1805 -> (

let r = ("r", FStar_SMTEncoding_Term.Ref_sort)
in (

let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (

let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (

let refa = (let _172_1383 = (let _172_1382 = (let _172_1381 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (_172_1381)::[])
in (reft_name, _172_1382))
in (FStar_SMTEncoding_Term.mkApp _172_1383))
in (

let refb = (let _172_1386 = (let _172_1385 = (let _172_1384 = (FStar_SMTEncoding_Term.mkFreeV bb)
in (_172_1384)::[])
in (reft_name, _172_1385))
in (FStar_SMTEncoding_Term.mkApp _172_1386))
in (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (

let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (let _172_1405 = (let _172_1392 = (let _172_1391 = (let _172_1390 = (let _172_1389 = (let _172_1388 = (let _172_1387 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in (typing_pred, _172_1387))
in (FStar_SMTEncoding_Term.mkImp _172_1388))
in (((typing_pred)::[])::[], (xx)::(aa)::[], _172_1389))
in (mkForall_fuel _172_1390))
in (_172_1391, Some ("ref inversion"), Some ("ref_inversion")))
in FStar_SMTEncoding_Term.Assume (_172_1392))
in (let _172_1404 = (let _172_1403 = (let _172_1402 = (let _172_1401 = (let _172_1400 = (let _172_1399 = (let _172_1398 = (let _172_1397 = (FStar_SMTEncoding_Term.mkAnd (typing_pred, typing_pred_b))
in (let _172_1396 = (let _172_1395 = (let _172_1394 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (let _172_1393 = (FStar_SMTEncoding_Term.mkFreeV bb)
in (_172_1394, _172_1393)))
in (FStar_SMTEncoding_Term.mkEq _172_1395))
in (_172_1397, _172_1396)))
in (FStar_SMTEncoding_Term.mkImp _172_1398))
in (((typing_pred)::(typing_pred_b)::[])::[], (xx)::(aa)::(bb)::[], _172_1399))
in (mkForall_fuel' 2 _172_1400))
in (_172_1401, Some ("ref typing is injective"), Some ("ref_injectivity")))
in FStar_SMTEncoding_Term.Assume (_172_1402))
in (_172_1403)::[])
in (_172_1405)::_172_1404))))))))))
in (

let mk_false_interp = (fun env nm false_tm -> (

let valid = (FStar_SMTEncoding_Term.mkApp ("Valid", (false_tm)::[]))
in (let _172_1414 = (let _172_1413 = (let _172_1412 = (FStar_SMTEncoding_Term.mkIff (FStar_SMTEncoding_Term.mkFalse, valid))
in (_172_1412, Some ("False interpretation"), Some ("false_interp")))
in FStar_SMTEncoding_Term.Assume (_172_1413))
in (_172_1414)::[])))
in (

let mk_and_interp = (fun env conj _83_1822 -> (

let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (

let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (

let valid = (let _172_1423 = (let _172_1422 = (let _172_1421 = (FStar_SMTEncoding_Term.mkApp (conj, (a)::(b)::[]))
in (_172_1421)::[])
in ("Valid", _172_1422))
in (FStar_SMTEncoding_Term.mkApp _172_1423))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _172_1430 = (let _172_1429 = (let _172_1428 = (let _172_1427 = (let _172_1426 = (let _172_1425 = (let _172_1424 = (FStar_SMTEncoding_Term.mkAnd (valid_a, valid_b))
in (_172_1424, valid))
in (FStar_SMTEncoding_Term.mkIff _172_1425))
in (((valid)::[])::[], (aa)::(bb)::[], _172_1426))
in (FStar_SMTEncoding_Term.mkForall _172_1427))
in (_172_1428, Some ("/\\ interpretation"), Some ("l_and-interp")))
in FStar_SMTEncoding_Term.Assume (_172_1429))
in (_172_1430)::[])))))))))
in (

let mk_or_interp = (fun env disj _83_1834 -> (

let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (

let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (

let valid = (let _172_1439 = (let _172_1438 = (let _172_1437 = (FStar_SMTEncoding_Term.mkApp (disj, (a)::(b)::[]))
in (_172_1437)::[])
in ("Valid", _172_1438))
in (FStar_SMTEncoding_Term.mkApp _172_1439))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _172_1446 = (let _172_1445 = (let _172_1444 = (let _172_1443 = (let _172_1442 = (let _172_1441 = (let _172_1440 = (FStar_SMTEncoding_Term.mkOr (valid_a, valid_b))
in (_172_1440, valid))
in (FStar_SMTEncoding_Term.mkIff _172_1441))
in (((valid)::[])::[], (aa)::(bb)::[], _172_1442))
in (FStar_SMTEncoding_Term.mkForall _172_1443))
in (_172_1444, Some ("\\/ interpretation"), Some ("l_or-interp")))
in FStar_SMTEncoding_Term.Assume (_172_1445))
in (_172_1446)::[])))))))))
in (

let mk_eq2_interp = (fun env eq2 tt -> (

let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (

let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (

let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (

let yy = ("y", FStar_SMTEncoding_Term.Term_sort)
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (

let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (

let y = (FStar_SMTEncoding_Term.mkFreeV yy)
in (

let valid = (let _172_1455 = (let _172_1454 = (let _172_1453 = (FStar_SMTEncoding_Term.mkApp (eq2, (a)::(b)::(x)::(y)::[]))
in (_172_1453)::[])
in ("Valid", _172_1454))
in (FStar_SMTEncoding_Term.mkApp _172_1455))
in (let _172_1462 = (let _172_1461 = (let _172_1460 = (let _172_1459 = (let _172_1458 = (let _172_1457 = (let _172_1456 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (_172_1456, valid))
in (FStar_SMTEncoding_Term.mkIff _172_1457))
in (((valid)::[])::[], (aa)::(bb)::(xx)::(yy)::[], _172_1458))
in (FStar_SMTEncoding_Term.mkForall _172_1459))
in (_172_1460, Some ("Eq2 interpretation"), Some ("eq2-interp")))
in FStar_SMTEncoding_Term.Assume (_172_1461))
in (_172_1462)::[])))))))))))
in (

let mk_imp_interp = (fun env imp tt -> (

let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (

let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (

let valid = (let _172_1471 = (let _172_1470 = (let _172_1469 = (FStar_SMTEncoding_Term.mkApp (imp, (a)::(b)::[]))
in (_172_1469)::[])
in ("Valid", _172_1470))
in (FStar_SMTEncoding_Term.mkApp _172_1471))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _172_1478 = (let _172_1477 = (let _172_1476 = (let _172_1475 = (let _172_1474 = (let _172_1473 = (let _172_1472 = (FStar_SMTEncoding_Term.mkImp (valid_a, valid_b))
in (_172_1472, valid))
in (FStar_SMTEncoding_Term.mkIff _172_1473))
in (((valid)::[])::[], (aa)::(bb)::[], _172_1474))
in (FStar_SMTEncoding_Term.mkForall _172_1475))
in (_172_1476, Some ("==> interpretation"), Some ("l_imp-interp")))
in FStar_SMTEncoding_Term.Assume (_172_1477))
in (_172_1478)::[])))))))))
in (

let mk_iff_interp = (fun env iff tt -> (

let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (

let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (

let valid = (let _172_1487 = (let _172_1486 = (let _172_1485 = (FStar_SMTEncoding_Term.mkApp (iff, (a)::(b)::[]))
in (_172_1485)::[])
in ("Valid", _172_1486))
in (FStar_SMTEncoding_Term.mkApp _172_1487))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _172_1494 = (let _172_1493 = (let _172_1492 = (let _172_1491 = (let _172_1490 = (let _172_1489 = (let _172_1488 = (FStar_SMTEncoding_Term.mkIff (valid_a, valid_b))
in (_172_1488, valid))
in (FStar_SMTEncoding_Term.mkIff _172_1489))
in (((valid)::[])::[], (aa)::(bb)::[], _172_1490))
in (FStar_SMTEncoding_Term.mkForall _172_1491))
in (_172_1492, Some ("<==> interpretation"), Some ("l_iff-interp")))
in FStar_SMTEncoding_Term.Assume (_172_1493))
in (_172_1494)::[])))))))))
in (

let mk_forall_interp = (fun env for_all tt -> (

let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (

let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (

let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (

let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (

let valid = (let _172_1503 = (let _172_1502 = (let _172_1501 = (FStar_SMTEncoding_Term.mkApp (for_all, (a)::(b)::[]))
in (_172_1501)::[])
in ("Valid", _172_1502))
in (FStar_SMTEncoding_Term.mkApp _172_1503))
in (

let valid_b_x = (let _172_1506 = (let _172_1505 = (let _172_1504 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_172_1504)::[])
in ("Valid", _172_1505))
in (FStar_SMTEncoding_Term.mkApp _172_1506))
in (let _172_1520 = (let _172_1519 = (let _172_1518 = (let _172_1517 = (let _172_1516 = (let _172_1515 = (let _172_1514 = (let _172_1513 = (let _172_1512 = (let _172_1508 = (let _172_1507 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_172_1507)::[])
in (_172_1508)::[])
in (let _172_1511 = (let _172_1510 = (let _172_1509 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_172_1509, valid_b_x))
in (FStar_SMTEncoding_Term.mkImp _172_1510))
in (_172_1512, (xx)::[], _172_1511)))
in (FStar_SMTEncoding_Term.mkForall _172_1513))
in (_172_1514, valid))
in (FStar_SMTEncoding_Term.mkIff _172_1515))
in (((valid)::[])::[], (aa)::(bb)::[], _172_1516))
in (FStar_SMTEncoding_Term.mkForall _172_1517))
in (_172_1518, Some ("forall interpretation"), Some ("forall-interp")))
in FStar_SMTEncoding_Term.Assume (_172_1519))
in (_172_1520)::[]))))))))))
in (

let mk_exists_interp = (fun env for_some tt -> (

let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (

let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (

let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (

let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (

let valid = (let _172_1529 = (let _172_1528 = (let _172_1527 = (FStar_SMTEncoding_Term.mkApp (for_some, (a)::(b)::[]))
in (_172_1527)::[])
in ("Valid", _172_1528))
in (FStar_SMTEncoding_Term.mkApp _172_1529))
in (

let valid_b_x = (let _172_1532 = (let _172_1531 = (let _172_1530 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_172_1530)::[])
in ("Valid", _172_1531))
in (FStar_SMTEncoding_Term.mkApp _172_1532))
in (let _172_1546 = (let _172_1545 = (let _172_1544 = (let _172_1543 = (let _172_1542 = (let _172_1541 = (let _172_1540 = (let _172_1539 = (let _172_1538 = (let _172_1534 = (let _172_1533 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_172_1533)::[])
in (_172_1534)::[])
in (let _172_1537 = (let _172_1536 = (let _172_1535 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_172_1535, valid_b_x))
in (FStar_SMTEncoding_Term.mkImp _172_1536))
in (_172_1538, (xx)::[], _172_1537)))
in (FStar_SMTEncoding_Term.mkExists _172_1539))
in (_172_1540, valid))
in (FStar_SMTEncoding_Term.mkIff _172_1541))
in (((valid)::[])::[], (aa)::(bb)::[], _172_1542))
in (FStar_SMTEncoding_Term.mkForall _172_1543))
in (_172_1544, Some ("exists interpretation"), Some ("exists-interp")))
in FStar_SMTEncoding_Term.Assume (_172_1545))
in (_172_1546)::[]))))))))))
in (

let mk_range_interp = (fun env range tt -> (

let range_ty = (FStar_SMTEncoding_Term.mkApp (range, []))
in (let _172_1557 = (let _172_1556 = (let _172_1555 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_ty)
in (let _172_1554 = (let _172_1553 = (varops.fresh "typing_range_const")
in Some (_172_1553))
in (_172_1555, Some ("Range_const typing"), _172_1554)))
in FStar_SMTEncoding_Term.Assume (_172_1556))
in (_172_1557)::[])))
in (

let prims = ((FStar_Syntax_Const.unit_lid, mk_unit))::((FStar_Syntax_Const.bool_lid, mk_bool))::((FStar_Syntax_Const.int_lid, mk_int))::((FStar_Syntax_Const.string_lid, mk_str))::((FStar_Syntax_Const.ref_lid, mk_ref))::((FStar_Syntax_Const.false_lid, mk_false_interp))::((FStar_Syntax_Const.and_lid, mk_and_interp))::((FStar_Syntax_Const.or_lid, mk_or_interp))::((FStar_Syntax_Const.eq2_lid, mk_eq2_interp))::((FStar_Syntax_Const.imp_lid, mk_imp_interp))::((FStar_Syntax_Const.iff_lid, mk_iff_interp))::((FStar_Syntax_Const.forall_lid, mk_forall_interp))::((FStar_Syntax_Const.exists_lid, mk_exists_interp))::((FStar_Syntax_Const.range_lid, mk_range_interp))::[]
in (fun env t s tt -> (match ((FStar_Util.find_opt (fun _83_1916 -> (match (_83_1916) with
| (l, _83_1915) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_83_1919, f) -> begin
(f env s tt)
end)))))))))))))))))))))


let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let _83_1925 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _172_1751 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _172_1751))
end else begin
()
end
in (

let nm = (match ((FStar_Syntax_Util.lid_of_sigelt se)) with
| None -> begin
""
end
| Some (l) -> begin
l.FStar_Ident.str
end)
in (

let _83_1933 = (encode_sigelt' env se)
in (match (_83_1933) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _172_1754 = (let _172_1753 = (let _172_1752 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (_172_1752))
in (_172_1753)::[])
in (_172_1754, e))
end
| _83_1936 -> begin
(let _172_1761 = (let _172_1760 = (let _172_1756 = (let _172_1755 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_172_1755))
in (_172_1756)::g)
in (let _172_1759 = (let _172_1758 = (let _172_1757 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_172_1757))
in (_172_1758)::[])
in (FStar_List.append _172_1760 _172_1759)))
in (_172_1761, e))
end)
end)))))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let should_skip = (fun l -> false)
in (

let encode_top_level_val = (fun env lid t quals -> (

let tt = (norm env t)
in (

let _83_1949 = (encode_free_var env lid t tt quals)
in (match (_83_1949) with
| (decls, env) -> begin
if (FStar_Syntax_Util.is_smt_lemma t) then begin
(let _172_1775 = (let _172_1774 = (encode_smt_lemma env lid tt)
in (FStar_List.append decls _172_1774))
in (_172_1775, env))
end else begin
(decls, env)
end
end))))
in (

let encode_top_level_vals = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _83_1956 lb -> (match (_83_1956) with
| (decls, env) -> begin
(

let _83_1960 = (let _172_1784 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env _172_1784 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (_83_1960) with
| (decls', env) -> begin
((FStar_List.append decls decls'), env)
end))
end)) ([], env))))
in (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_83_1962) -> begin
(FStar_All.failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _83_1981, _83_1983, _83_1985, _83_1987) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid) -> begin
(

let _83_1993 = (new_term_constant_and_tok_from_lid env lid)
in (match (_83_1993) with
| (tname, ttok, env) -> begin
([], env)
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _83_1996, t, quals, _83_2000) -> begin
(

let will_encode_definition = (not ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _83_13 -> (match (_83_13) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Irreducible) -> begin
true
end
| _83_2013 -> begin
false
end))))))
in if will_encode_definition then begin
([], env)
end else begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (

let _83_2018 = (encode_top_level_val env fv t quals)
in (match (_83_2018) with
| (decls, env) -> begin
(

let tname = lid.FStar_Ident.str
in (

let tsym = (FStar_SMTEncoding_Term.mkFreeV (tname, FStar_SMTEncoding_Term.Term_sort))
in (let _172_1787 = (let _172_1786 = (primitive_type_axioms env.tcenv lid tname tsym)
in (FStar_List.append decls _172_1786))
in (_172_1787, env))))
end)))
end)
end
| FStar_Syntax_Syntax.Sig_assume (l, f, _83_2024, _83_2026) -> begin
(

let _83_2031 = (encode_formula f env)
in (match (_83_2031) with
| (f, decls) -> begin
(

let g = (let _172_1794 = (let _172_1793 = (let _172_1792 = (let _172_1789 = (let _172_1788 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" _172_1788))
in Some (_172_1789))
in (let _172_1791 = (let _172_1790 = (varops.fresh (Prims.strcat "assumption_" l.FStar_Ident.str))
in Some (_172_1790))
in (f, _172_1792, _172_1791)))
in FStar_SMTEncoding_Term.Assume (_172_1793))
in (_172_1794)::[])
in ((FStar_List.append decls g), env))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _83_2036, quals) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) -> begin
(

let _83_2049 = (FStar_Util.fold_map (fun env lb -> (

let lid = (let _172_1798 = (let _172_1797 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _172_1797.FStar_Syntax_Syntax.fv_name)
in _172_1798.FStar_Syntax_Syntax.v)
in if (let _172_1799 = (FStar_TypeChecker_Env.try_lookup_val_decl env.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone _172_1799)) then begin
(

let val_decl = FStar_Syntax_Syntax.Sig_declare_typ ((lid, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, quals, r))
in (

let _83_2046 = (encode_sigelt' env val_decl)
in (match (_83_2046) with
| (decls, env) -> begin
(env, decls)
end)))
end else begin
(env, [])
end)) env (Prims.snd lbs))
in (match (_83_2049) with
| (env, decls) -> begin
((FStar_List.flatten decls), env)
end))
end
| FStar_Syntax_Syntax.Sig_let ((_83_2051, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t); FStar_Syntax_Syntax.lbunivs = _83_2059; FStar_Syntax_Syntax.lbtyp = _83_2057; FStar_Syntax_Syntax.lbeff = _83_2055; FStar_Syntax_Syntax.lbdef = _83_2053}::[]), _83_2066, _83_2068, _83_2070) when (FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Syntax_Const.b2t_lid) -> begin
(

let _83_2076 = (new_term_constant_and_tok_from_lid env b2t.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_83_2076) with
| (tname, ttok, env) -> begin
(

let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (

let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (

let valid_b2t_x = (let _172_1802 = (let _172_1801 = (let _172_1800 = (FStar_SMTEncoding_Term.mkApp ("Prims.b2t", (x)::[]))
in (_172_1800)::[])
in ("Valid", _172_1801))
in (FStar_SMTEncoding_Term.mkApp _172_1802))
in (

let decls = (let _172_1810 = (let _172_1809 = (let _172_1808 = (let _172_1807 = (let _172_1806 = (let _172_1805 = (let _172_1804 = (let _172_1803 = (FStar_SMTEncoding_Term.mkApp ("BoxBool_proj_0", (x)::[]))
in (valid_b2t_x, _172_1803))
in (FStar_SMTEncoding_Term.mkEq _172_1804))
in (((valid_b2t_x)::[])::[], (xx)::[], _172_1805))
in (FStar_SMTEncoding_Term.mkForall _172_1806))
in (_172_1807, Some ("b2t def"), Some ("b2t_def")))
in FStar_SMTEncoding_Term.Assume (_172_1808))
in (_172_1809)::[])
in (FStar_SMTEncoding_Term.DeclFun ((tname, (FStar_SMTEncoding_Term.Term_sort)::[], FStar_SMTEncoding_Term.Term_sort, None)))::_172_1810)
in (decls, env)))))
end))
end
| FStar_Syntax_Syntax.Sig_let (_83_2082, _83_2084, _83_2086, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _83_14 -> (match (_83_14) with
| (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _83_2096 -> begin
false
end)))) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_let ((false, lb::[]), _83_2102, _83_2104, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _83_15 -> (match (_83_15) with
| FStar_Syntax_Syntax.Projector (_83_2110) -> begin
true
end
| _83_2113 -> begin
false
end)))) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((try_lookup_free_var env l)) with
| Some (_83_2117) -> begin
([], env)
end
| None -> begin
(

let se = FStar_Syntax_Syntax.Sig_declare_typ ((l, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, quals, (FStar_Ident.range_of_lid l)))
in (encode_sigelt env se))
end)))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), _83_2125, _83_2127, quals) -> begin
(

let eta_expand = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let _83_2139 = (FStar_Util.first_N nbinders formals)
in (match (_83_2139) with
| (formals, extra_formals) -> begin
(

let subst = (FStar_List.map2 (fun _83_2143 _83_2147 -> (match ((_83_2143, _83_2147)) with
| ((formal, _83_2142), (binder, _83_2146)) -> begin
(let _172_1824 = (let _172_1823 = (FStar_Syntax_Syntax.bv_to_name binder)
in (formal, _172_1823))
in FStar_Syntax_Syntax.NT (_172_1824))
end)) formals binders)
in (

let extra_formals = (let _172_1828 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun _83_2151 -> (match (_83_2151) with
| (x, i) -> begin
(let _172_1827 = (

let _83_2152 = x
in (let _172_1826 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _83_2152.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _83_2152.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _172_1826}))
in (_172_1827, i))
end))))
in (FStar_All.pipe_right _172_1828 FStar_Syntax_Util.name_binders))
in (

let body = (let _172_1835 = (FStar_Syntax_Subst.compress body)
in (let _172_1834 = (let _172_1829 = (FStar_Syntax_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _172_1829))
in (let _172_1833 = (let _172_1832 = (let _172_1831 = (FStar_Syntax_Subst.subst subst t)
in _172_1831.FStar_Syntax_Syntax.n)
in (FStar_All.pipe_left (fun _172_1830 -> Some (_172_1830)) _172_1832))
in (FStar_Syntax_Syntax.extend_app_n _172_1835 _172_1834 _172_1833 body.FStar_Syntax_Syntax.pos))))
in ((FStar_List.append binders extra_formals), body))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (

let rec aux = (fun norm t_norm -> (match ((let _172_1846 = (FStar_Syntax_Util.unascribe e)
in _172_1846.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, lopt) -> begin
(

let _83_2171 = (FStar_Syntax_Subst.open_term' binders body)
in (match (_83_2171) with
| (binders, body, opening) -> begin
(match ((let _172_1847 = (FStar_Syntax_Subst.compress t_norm)
in _172_1847.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let _83_2178 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_83_2178) with
| (formals, c) -> begin
(

let nformals = (FStar_List.length formals)
in (

let nbinders = (FStar_List.length binders)
in (

let tres = (FStar_Syntax_Util.comp_result c)
in if ((nformals < nbinders) && (FStar_Syntax_Util.is_total_comp c)) then begin
(

let lopt = (subst_lcomp_opt opening lopt)
in (

let _83_2185 = (FStar_Util.first_N nformals binders)
in (match (_83_2185) with
| (bs0, rest) -> begin
(

let c = (

let subst = (FStar_List.map2 (fun _83_2189 _83_2193 -> (match ((_83_2189, _83_2193)) with
| ((b, _83_2188), (x, _83_2192)) -> begin
(let _172_1851 = (let _172_1850 = (FStar_Syntax_Syntax.bv_to_name x)
in (b, _172_1850))
in FStar_Syntax_Syntax.NT (_172_1851))
end)) bs0 formals)
in (FStar_Syntax_Subst.subst_comp subst c))
in (

let body = (FStar_Syntax_Util.abs rest body lopt)
in (bs0, body, bs0, (FStar_Syntax_Util.comp_result c))))
end)))
end else begin
if (nformals > nbinders) then begin
(

let _83_2199 = (eta_expand binders formals body tres)
in (match (_83_2199) with
| (binders, body) -> begin
(binders, body, formals, tres)
end))
end else begin
(binders, body, formals, tres)
end
end)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, _83_2202) -> begin
(aux true x.FStar_Syntax_Syntax.sort)
end
| _83_2206 when (not (norm)) -> begin
(

let t_norm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm)
in (aux true t_norm))
end
| _83_2209 -> begin
(let _172_1854 = (let _172_1853 = (FStar_Syntax_Print.term_to_string e)
in (let _172_1852 = (FStar_Syntax_Print.term_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str _172_1853 _172_1852)))
in (FStar_All.failwith _172_1854))
end)
end))
end
| _83_2211 -> begin
(match ((let _172_1855 = (FStar_Syntax_Subst.compress t_norm)
in _172_1855.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let _83_2218 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_83_2218) with
| (formals, c) -> begin
(

let tres = (FStar_Syntax_Util.comp_result c)
in (

let _83_2222 = (eta_expand [] formals e tres)
in (match (_83_2222) with
| (binders, body) -> begin
(binders, body, formals, tres)
end)))
end))
end
| _83_2224 -> begin
([], e, [], t_norm)
end)
end))
in (aux false t_norm)))
in try
(match (()) with
| () -> begin
if (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp)))) then begin
(encode_top_level_vals env bindings quals)
end else begin
(

let _83_2252 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _83_2239 lb -> (match (_83_2239) with
| (toks, typs, decls, env) -> begin
(

let _83_2241 = if (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) then begin
(Prims.raise Let_rec_unencodeable)
end else begin
()
end
in (

let t_norm = (whnf env lb.FStar_Syntax_Syntax.lbtyp)
in (

let _83_2247 = (let _172_1860 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env _172_1860 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (_83_2247) with
| (tok, decl, env) -> begin
(let _172_1863 = (let _172_1862 = (let _172_1861 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (_172_1861, tok))
in (_172_1862)::toks)
in (_172_1863, (t_norm)::typs, (decl)::decls, env))
end))))
end)) ([], [], [], env)))
in (match (_83_2252) with
| (toks, typs, decls, env) -> begin
(

let toks = (FStar_List.rev toks)
in (

let decls = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (

let typs = (FStar_List.rev typs)
in if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _83_16 -> (match (_83_16) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| _83_2259 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> (let _172_1866 = (FStar_Syntax_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _172_1866)))))) then begin
(decls, env)
end else begin
if (not (is_rec)) then begin
(match ((bindings, typs, toks)) with
| ({FStar_Syntax_Syntax.lbname = _83_2269; FStar_Syntax_Syntax.lbunivs = _83_2267; FStar_Syntax_Syntax.lbtyp = _83_2265; FStar_Syntax_Syntax.lbeff = _83_2263; FStar_Syntax_Syntax.lbdef = e}::[], t_norm::[], (flid_fv, (f, ftok))::[]) -> begin
(

let e = (FStar_Syntax_Subst.compress e)
in (

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let _83_2289 = (destruct_bound_function flid t_norm e)
in (match (_83_2289) with
| (binders, body, _83_2286, _83_2288) -> begin
(

let _83_2296 = (encode_binders None binders env)
in (match (_83_2296) with
| (vars, guards, env', binder_decls, _83_2295) -> begin
(

let app = (match (vars) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV (f, FStar_SMTEncoding_Term.Term_sort))
end
| _83_2299 -> begin
(let _172_1868 = (let _172_1867 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (f, _172_1867))
in (FStar_SMTEncoding_Term.mkApp _172_1868))
end)
in (

let _83_2305 = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic)) then begin
(let _172_1870 = (FStar_SMTEncoding_Term.mk_Valid app)
in (let _172_1869 = (encode_formula body env')
in (_172_1870, _172_1869)))
end else begin
(let _172_1871 = (encode_term body env')
in (app, _172_1871))
end
in (match (_83_2305) with
| (app, (body, decls2)) -> begin
(

let eqn = (let _172_1877 = (let _172_1876 = (let _172_1873 = (let _172_1872 = (FStar_SMTEncoding_Term.mkEq (app, body))
in (((app)::[])::[], vars, _172_1872))
in (FStar_SMTEncoding_Term.mkForall _172_1873))
in (let _172_1875 = (let _172_1874 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (_172_1874))
in (_172_1876, _172_1875, Some ((Prims.strcat "equation_" f)))))
in FStar_SMTEncoding_Term.Assume (_172_1877))
in (let _172_1879 = (let _172_1878 = (primitive_type_axioms env.tcenv flid f app)
in (FStar_List.append (FStar_List.append (FStar_List.append (FStar_List.append decls binder_decls) decls2) ((eqn)::[])) _172_1878))
in (_172_1879, env)))
end)))
end))
end))))
end
| _83_2308 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(

let fuel = (let _172_1880 = (varops.fresh "fuel")
in (_172_1880, FStar_SMTEncoding_Term.Fuel_sort))
in (

let fuel_tm = (FStar_SMTEncoding_Term.mkFreeV fuel)
in (

let env0 = env
in (

let _83_2326 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _83_2314 _83_2319 -> (match ((_83_2314, _83_2319)) with
| ((gtoks, env), (flid_fv, (f, ftok))) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let g = (varops.new_fvar flid)
in (

let gtok = (varops.new_fvar flid)
in (

let env = (let _172_1885 = (let _172_1884 = (FStar_SMTEncoding_Term.mkApp (g, (fuel_tm)::[]))
in (FStar_All.pipe_left (fun _172_1883 -> Some (_172_1883)) _172_1884))
in (push_free_var env flid gtok _172_1885))
in (((flid, f, ftok, g, gtok))::gtoks, env)))))
end)) ([], env)))
in (match (_83_2326) with
| (gtoks, env) -> begin
(

let gtoks = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env0 _83_2335 t_norm _83_2346 -> (match ((_83_2335, _83_2346)) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = _83_2345; FStar_Syntax_Syntax.lbunivs = _83_2343; FStar_Syntax_Syntax.lbtyp = _83_2341; FStar_Syntax_Syntax.lbeff = _83_2339; FStar_Syntax_Syntax.lbdef = e}) -> begin
(

let _83_2351 = (destruct_bound_function flid t_norm e)
in (match (_83_2351) with
| (binders, body, formals, tres) -> begin
(

let _83_2358 = (encode_binders None binders env)
in (match (_83_2358) with
| (vars, guards, env', binder_decls, _83_2357) -> begin
(

let decl_g = (let _172_1896 = (let _172_1895 = (let _172_1894 = (FStar_List.map Prims.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::_172_1894)
in (g, _172_1895, FStar_SMTEncoding_Term.Term_sort, Some ("Fuel-instrumented function name")))
in FStar_SMTEncoding_Term.DeclFun (_172_1896))
in (

let env0 = (push_zfuel_name env0 flid g)
in (

let decl_g_tok = FStar_SMTEncoding_Term.DeclFun ((gtok, [], FStar_SMTEncoding_Term.Term_sort, Some ("Token for fuel-instrumented partial applications")))
in (

let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (

let app = (FStar_SMTEncoding_Term.mkApp (f, vars_tm))
in (

let gsapp = (let _172_1899 = (let _172_1898 = (let _172_1897 = (FStar_SMTEncoding_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (_172_1897)::vars_tm)
in (g, _172_1898))
in (FStar_SMTEncoding_Term.mkApp _172_1899))
in (

let gmax = (let _172_1902 = (let _172_1901 = (let _172_1900 = (FStar_SMTEncoding_Term.mkApp ("MaxFuel", []))
in (_172_1900)::vars_tm)
in (g, _172_1901))
in (FStar_SMTEncoding_Term.mkApp _172_1902))
in (

let _83_2368 = (encode_term body env')
in (match (_83_2368) with
| (body_tm, decls2) -> begin
(

let eqn_g = (let _172_1908 = (let _172_1907 = (let _172_1904 = (let _172_1903 = (FStar_SMTEncoding_Term.mkEq (gsapp, body_tm))
in (((gsapp)::[])::[], (fuel)::vars, _172_1903))
in (FStar_SMTEncoding_Term.mkForall _172_1904))
in (let _172_1906 = (let _172_1905 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (_172_1905))
in (_172_1907, _172_1906, Some ((Prims.strcat "equation_with_fuel_" g)))))
in FStar_SMTEncoding_Term.Assume (_172_1908))
in (

let eqn_f = (let _172_1912 = (let _172_1911 = (let _172_1910 = (let _172_1909 = (FStar_SMTEncoding_Term.mkEq (app, gmax))
in (((app)::[])::[], vars, _172_1909))
in (FStar_SMTEncoding_Term.mkForall _172_1910))
in (_172_1911, Some ("Correspondence of recursive function to instrumented version"), Some ((Prims.strcat "fuel_correspondence_" g))))
in FStar_SMTEncoding_Term.Assume (_172_1912))
in (

let eqn_g' = (let _172_1921 = (let _172_1920 = (let _172_1919 = (let _172_1918 = (let _172_1917 = (let _172_1916 = (let _172_1915 = (let _172_1914 = (let _172_1913 = (FStar_SMTEncoding_Term.n_fuel 0)
in (_172_1913)::vars_tm)
in (g, _172_1914))
in (FStar_SMTEncoding_Term.mkApp _172_1915))
in (gsapp, _172_1916))
in (FStar_SMTEncoding_Term.mkEq _172_1917))
in (((gsapp)::[])::[], (fuel)::vars, _172_1918))
in (FStar_SMTEncoding_Term.mkForall _172_1919))
in (_172_1920, Some ("Fuel irrelevance"), Some ((Prims.strcat "fuel_irrelevance_" g))))
in FStar_SMTEncoding_Term.Assume (_172_1921))
in (

let _83_2391 = (

let _83_2378 = (encode_binders None formals env0)
in (match (_83_2378) with
| (vars, v_guards, env, binder_decls, _83_2377) -> begin
(

let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (

let gapp = (FStar_SMTEncoding_Term.mkApp (g, (fuel_tm)::vars_tm))
in (

let tok_corr = (

let tok_app = (let _172_1922 = (FStar_SMTEncoding_Term.mkFreeV (gtok, FStar_SMTEncoding_Term.Term_sort))
in (mk_Apply _172_1922 ((fuel)::vars)))
in (let _172_1926 = (let _172_1925 = (let _172_1924 = (let _172_1923 = (FStar_SMTEncoding_Term.mkEq (tok_app, gapp))
in (((tok_app)::[])::[], (fuel)::vars, _172_1923))
in (FStar_SMTEncoding_Term.mkForall _172_1924))
in (_172_1925, Some ("Fuel token correspondence"), Some ((Prims.strcat "fuel_tokem_correspondence_" gtok))))
in FStar_SMTEncoding_Term.Assume (_172_1926)))
in (

let _83_2388 = (

let _83_2385 = (encode_term_pred None tres env gapp)
in (match (_83_2385) with
| (g_typing, d3) -> begin
(let _172_1934 = (let _172_1933 = (let _172_1932 = (let _172_1931 = (let _172_1930 = (let _172_1929 = (let _172_1928 = (let _172_1927 = (FStar_SMTEncoding_Term.mk_and_l v_guards)
in (_172_1927, g_typing))
in (FStar_SMTEncoding_Term.mkImp _172_1928))
in (((gapp)::[])::[], (fuel)::vars, _172_1929))
in (FStar_SMTEncoding_Term.mkForall _172_1930))
in (_172_1931, Some ("Typing correspondence of token to term"), Some ((Prims.strcat "token_correspondence_" g))))
in FStar_SMTEncoding_Term.Assume (_172_1932))
in (_172_1933)::[])
in (d3, _172_1934))
end))
in (match (_83_2388) with
| (aux_decls, typing_corr) -> begin
((FStar_List.append binder_decls aux_decls), (FStar_List.append typing_corr ((tok_corr)::[])))
end)))))
end))
in (match (_83_2391) with
| (aux_decls, g_typing) -> begin
((FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) aux_decls) ((decl_g)::(decl_g_tok)::[])), (FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing), env0)
end)))))
end)))))))))
end))
end))
end))
in (

let _83_2407 = (let _172_1937 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _83_2395 _83_2399 -> (match ((_83_2395, _83_2399)) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(

let _83_2403 = (encode_one_binding env0 gtok ty bs)
in (match (_83_2403) with
| (decls', eqns', env0) -> begin
((decls')::decls, (FStar_List.append eqns' eqns), env0)
end))
end)) ((decls)::[], [], env0) _172_1937))
in (match (_83_2407) with
| (decls, eqns, env0) -> begin
(

let _83_2416 = (let _172_1939 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _172_1939 (FStar_List.partition (fun _83_17 -> (match (_83_17) with
| FStar_SMTEncoding_Term.DeclFun (_83_2410) -> begin
true
end
| _83_2413 -> begin
false
end)))))
in (match (_83_2416) with
| (prefix_decls, rest) -> begin
(

let eqns = (FStar_List.rev eqns)
in ((FStar_List.append (FStar_List.append prefix_decls rest) eqns), env0))
end))
end))))
end)))))
end
end)))
end))
end
end)
with
| Let_rec_unencodeable -> begin
(

let msg = (let _172_1942 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _172_1942 (FStar_String.concat " and ")))
in (

let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in ((decl)::[], env)))
end))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _83_2420, _83_2422, _83_2424) -> begin
(

let _83_2429 = (encode_signature env ses)
in (match (_83_2429) with
| (g, env) -> begin
(

let _83_2443 = (FStar_All.pipe_right g (FStar_List.partition (fun _83_18 -> (match (_83_18) with
| FStar_SMTEncoding_Term.Assume (_83_2432, Some ("inversion axiom"), _83_2436) -> begin
false
end
| _83_2440 -> begin
true
end))))
in (match (_83_2443) with
| (g', inversions) -> begin
(

let _83_2452 = (FStar_All.pipe_right g' (FStar_List.partition (fun _83_19 -> (match (_83_19) with
| FStar_SMTEncoding_Term.DeclFun (_83_2446) -> begin
true
end
| _83_2449 -> begin
false
end))))
in (match (_83_2452) with
| (decls, rest) -> begin
((FStar_List.append (FStar_List.append decls rest) inversions), env)
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, _83_2455, tps, k, _83_2459, datas, quals, _83_2463) -> begin
(

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _83_20 -> (match (_83_20) with
| (FStar_Syntax_Syntax.Logic) | (FStar_Syntax_Syntax.Assumption) -> begin
true
end
| _83_2470 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(

let _83_2482 = c
in (match (_83_2482) with
| (name, args, _83_2477, _83_2479, _83_2481) -> begin
(let _172_1950 = (let _172_1949 = (let _172_1948 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in (name, _172_1948, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_172_1949))
in (_172_1950)::[])
end))
end else begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end)
in (

let inversion_axioms = (fun tapp vars -> if (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _172_1956 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right _172_1956 FStar_Option.isNone))))) then begin
[]
end else begin
(

let _83_2489 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_83_2489) with
| (xxsym, xx) -> begin
(

let _83_2525 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _83_2492 l -> (match (_83_2492) with
| (out, decls) -> begin
(

let _83_2497 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (_83_2497) with
| (_83_2495, data_t) -> begin
(

let _83_2500 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (_83_2500) with
| (args, res) -> begin
(

let indices = (match ((let _172_1959 = (FStar_Syntax_Subst.compress res)
in _172_1959.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_83_2502, indices) -> begin
indices
end
| _83_2507 -> begin
[]
end)
in (

let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env _83_2513 -> (match (_83_2513) with
| (x, _83_2512) -> begin
(let _172_1964 = (let _172_1963 = (let _172_1962 = (mk_term_projector_name l x)
in (_172_1962, (xx)::[]))
in (FStar_SMTEncoding_Term.mkApp _172_1963))
in (push_term_var env x _172_1964))
end)) env))
in (

let _83_2517 = (encode_args indices env)
in (match (_83_2517) with
| (indices, decls') -> begin
(

let _83_2518 = if ((FStar_List.length indices) <> (FStar_List.length vars)) then begin
(FStar_All.failwith "Impossible")
end else begin
()
end
in (

let eqs = (let _172_1969 = (FStar_List.map2 (fun v a -> (let _172_1968 = (let _172_1967 = (FStar_SMTEncoding_Term.mkFreeV v)
in (_172_1967, a))
in (FStar_SMTEncoding_Term.mkEq _172_1968))) vars indices)
in (FStar_All.pipe_right _172_1969 FStar_SMTEncoding_Term.mk_and_l))
in (let _172_1974 = (let _172_1973 = (let _172_1972 = (let _172_1971 = (let _172_1970 = (mk_data_tester env l xx)
in (_172_1970, eqs))
in (FStar_SMTEncoding_Term.mkAnd _172_1971))
in (out, _172_1972))
in (FStar_SMTEncoding_Term.mkOr _172_1973))
in (_172_1974, (FStar_List.append decls decls')))))
end))))
end))
end))
end)) (FStar_SMTEncoding_Term.mkFalse, [])))
in (match (_83_2525) with
| (data_ax, decls) -> begin
(

let _83_2528 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_83_2528) with
| (ffsym, ff) -> begin
(

let fuel_guarded_inversion = (

let xx_has_type_sfuel = if ((FStar_List.length datas) > 1) then begin
(let _172_1975 = (FStar_SMTEncoding_Term.mkApp ("SFuel", (ff)::[]))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel _172_1975 xx tapp))
end else begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end
in (let _172_1982 = (let _172_1981 = (let _172_1978 = (let _172_1977 = (add_fuel (ffsym, FStar_SMTEncoding_Term.Fuel_sort) (((xxsym, FStar_SMTEncoding_Term.Term_sort))::vars))
in (let _172_1976 = (FStar_SMTEncoding_Term.mkImp (xx_has_type_sfuel, data_ax))
in (((xx_has_type_sfuel)::[])::[], _172_1977, _172_1976)))
in (FStar_SMTEncoding_Term.mkForall _172_1978))
in (let _172_1980 = (let _172_1979 = (varops.fresh (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str))
in Some (_172_1979))
in (_172_1981, Some ("inversion axiom"), _172_1980)))
in FStar_SMTEncoding_Term.Assume (_172_1982)))
in (

let pattern_guarded_inversion = if ((contains_name env "Prims.inversion") && ((FStar_List.length datas) > 1)) then begin
(

let xx_has_type_fuel = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let pattern_guard = (FStar_SMTEncoding_Term.mkApp ("Prims.inversion", (tapp)::[]))
in (let _172_1990 = (let _172_1989 = (let _172_1988 = (let _172_1985 = (let _172_1984 = (add_fuel (ffsym, FStar_SMTEncoding_Term.Fuel_sort) (((xxsym, FStar_SMTEncoding_Term.Term_sort))::vars))
in (let _172_1983 = (FStar_SMTEncoding_Term.mkImp (xx_has_type_fuel, data_ax))
in (((xx_has_type_fuel)::(pattern_guard)::[])::[], _172_1984, _172_1983)))
in (FStar_SMTEncoding_Term.mkForall _172_1985))
in (let _172_1987 = (let _172_1986 = (varops.fresh (Prims.strcat "pattern_guarded_inversion_" t.FStar_Ident.str))
in Some (_172_1986))
in (_172_1988, Some ("inversion axiom"), _172_1987)))
in FStar_SMTEncoding_Term.Assume (_172_1989))
in (_172_1990)::[])))
end else begin
[]
end
in (FStar_List.append (FStar_List.append decls ((fuel_guarded_inversion)::[])) pattern_guarded_inversion)))
end))
end))
end))
end)
in (

let _83_2542 = (match ((let _172_1991 = (FStar_Syntax_Subst.compress k)
in _172_1991.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
((FStar_List.append tps formals), (FStar_Syntax_Util.comp_result kres))
end
| _83_2539 -> begin
(tps, k)
end)
in (match (_83_2542) with
| (formals, res) -> begin
(

let _83_2545 = (FStar_Syntax_Subst.open_term formals res)
in (match (_83_2545) with
| (formals, res) -> begin
(

let _83_2552 = (encode_binders None formals env)
in (match (_83_2552) with
| (vars, guards, env', binder_decls, _83_2551) -> begin
(

let _83_2556 = (new_term_constant_and_tok_from_lid env t)
in (match (_83_2556) with
| (tname, ttok, env) -> begin
(

let ttok_tm = (FStar_SMTEncoding_Term.mkApp (ttok, []))
in (

let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (

let tapp = (let _172_1993 = (let _172_1992 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (tname, _172_1992))
in (FStar_SMTEncoding_Term.mkApp _172_1993))
in (

let _83_2577 = (

let tname_decl = (let _172_1997 = (let _172_1996 = (FStar_All.pipe_right vars (FStar_List.map (fun _83_2562 -> (match (_83_2562) with
| (n, s) -> begin
((Prims.strcat tname n), s)
end))))
in (let _172_1995 = (varops.next_id ())
in (tname, _172_1996, FStar_SMTEncoding_Term.Term_sort, _172_1995, false)))
in (constructor_or_logic_type_decl _172_1997))
in (

let _83_2574 = (match (vars) with
| [] -> begin
(let _172_2001 = (let _172_2000 = (let _172_1999 = (FStar_SMTEncoding_Term.mkApp (tname, []))
in (FStar_All.pipe_left (fun _172_1998 -> Some (_172_1998)) _172_1999))
in (push_free_var env t tname _172_2000))
in ([], _172_2001))
end
| _83_2566 -> begin
(

let ttok_decl = FStar_SMTEncoding_Term.DeclFun ((ttok, [], FStar_SMTEncoding_Term.Term_sort, Some ("token")))
in (

let ttok_fresh = (let _172_2002 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (ttok, FStar_SMTEncoding_Term.Term_sort) _172_2002))
in (

let ttok_app = (mk_Apply ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (let _172_2006 = (let _172_2005 = (let _172_2004 = (let _172_2003 = (FStar_SMTEncoding_Term.mkEq (ttok_app, tapp))
in (pats, None, vars, _172_2003))
in (FStar_SMTEncoding_Term.mkForall' _172_2004))
in (_172_2005, Some ("name-token correspondence"), Some ((Prims.strcat "token_correspondence_" ttok))))
in FStar_SMTEncoding_Term.Assume (_172_2006))
in ((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[], env))))))
end)
in (match (_83_2574) with
| (tok_decls, env) -> begin
((FStar_List.append tname_decl tok_decls), env)
end)))
in (match (_83_2577) with
| (decls, env) -> begin
(

let kindingAx = (

let _83_2580 = (encode_term_pred None res env' tapp)
in (match (_83_2580) with
| (k, decls) -> begin
(

let karr = if ((FStar_List.length formals) > 0) then begin
(let _172_2010 = (let _172_2009 = (let _172_2008 = (let _172_2007 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _172_2007))
in (_172_2008, Some ("kinding"), Some ((Prims.strcat "pre_kinding_" ttok))))
in FStar_SMTEncoding_Term.Assume (_172_2009))
in (_172_2010)::[])
end else begin
[]
end
in (let _172_2016 = (let _172_2015 = (let _172_2014 = (let _172_2013 = (let _172_2012 = (let _172_2011 = (FStar_SMTEncoding_Term.mkImp (guard, k))
in (((tapp)::[])::[], vars, _172_2011))
in (FStar_SMTEncoding_Term.mkForall _172_2012))
in (_172_2013, None, Some ((Prims.strcat "kinding_" ttok))))
in FStar_SMTEncoding_Term.Assume (_172_2014))
in (_172_2015)::[])
in (FStar_List.append (FStar_List.append decls karr) _172_2016)))
end))
in (

let aux = (let _172_2020 = (let _172_2017 = (inversion_axioms tapp vars)
in (FStar_List.append kindingAx _172_2017))
in (let _172_2019 = (let _172_2018 = (pretype_axiom tapp vars)
in (_172_2018)::[])
in (FStar_List.append _172_2020 _172_2019)))
in (

let g = (FStar_List.append (FStar_List.append decls binder_decls) aux)
in (g, env))))
end)))))
end))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, _83_2587, _83_2589, _83_2591, _83_2593, _83_2595, _83_2597, _83_2599) when (FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_datacon (d, _83_2604, t, _83_2607, n_tps, quals, _83_2611, drange) -> begin
(

let _83_2618 = (new_term_constant_and_tok_from_lid env d)
in (match (_83_2618) with
| (ddconstrsym, ddtok, env) -> begin
(

let ddtok_tm = (FStar_SMTEncoding_Term.mkApp (ddtok, []))
in (

let _83_2622 = (FStar_Syntax_Util.arrow_formals t)
in (match (_83_2622) with
| (formals, t_res) -> begin
(

let _83_2625 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_83_2625) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_SMTEncoding_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (

let _83_2632 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_83_2632) with
| (vars, guards, env', binder_decls, names) -> begin
(

let projectors = (FStar_All.pipe_right names (FStar_List.map (fun x -> (let _172_2022 = (mk_term_projector_name d x)
in (_172_2022, FStar_SMTEncoding_Term.Term_sort)))))
in (

let datacons = (let _172_2024 = (let _172_2023 = (varops.next_id ())
in (ddconstrsym, projectors, FStar_SMTEncoding_Term.Term_sort, _172_2023, true))
in (FStar_All.pipe_right _172_2024 FStar_SMTEncoding_Term.constructor_to_decl))
in (

let app = (mk_Apply ddtok_tm vars)
in (

let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (

let _83_2642 = (encode_term_pred None t env ddtok_tm)
in (match (_83_2642) with
| (tok_typing, decls3) -> begin
(

let _83_2649 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_83_2649) with
| (vars', guards', env'', decls_formals, _83_2648) -> begin
(

let _83_2654 = (

let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars')
in (

let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (encode_term_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_83_2654) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_SMTEncoding_Term.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _83_2658 -> begin
(let _172_2026 = (let _172_2025 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (ddtok, FStar_SMTEncoding_Term.Term_sort) _172_2025))
in (_172_2026)::[])
end)
in (

let encode_elim = (fun _83_2661 -> (match (()) with
| () -> begin
(

let _83_2664 = (FStar_Syntax_Util.head_and_args t_res)
in (match (_83_2664) with
| (head, args) -> begin
(match ((let _172_2029 = (FStar_Syntax_Subst.compress head)
in _172_2029.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let _83_2682 = (encode_args args env')
in (match (_83_2682) with
| (encoded_args, arg_decls) -> begin
(

let _83_2697 = (FStar_List.fold_left (fun _83_2686 arg -> (match (_83_2686) with
| (env, arg_vars, eqns) -> begin
(

let _83_2692 = (let _172_2032 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in (gen_term_var env _172_2032))
in (match (_83_2692) with
| (_83_2689, xv, env) -> begin
(let _172_2034 = (let _172_2033 = (FStar_SMTEncoding_Term.mkEq (arg, xv))
in (_172_2033)::eqns)
in (env, (xv)::arg_vars, _172_2034))
end))
end)) (env', [], []) encoded_args)
in (match (_83_2697) with
| (_83_2694, arg_vars, eqns) -> begin
(

let arg_vars = (FStar_List.rev arg_vars)
in (

let ty = (FStar_SMTEncoding_Term.mkApp (encoded_head, arg_vars))
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (

let ty_pred = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp ty)
in (

let arg_binders = (FStar_List.map FStar_SMTEncoding_Term.fv_of_term arg_vars)
in (

let typing_inversion = (let _172_2041 = (let _172_2040 = (let _172_2039 = (let _172_2038 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _172_2037 = (let _172_2036 = (let _172_2035 = (FStar_SMTEncoding_Term.mk_and_l (FStar_List.append eqns guards))
in (ty_pred, _172_2035))
in (FStar_SMTEncoding_Term.mkImp _172_2036))
in (((ty_pred)::[])::[], _172_2038, _172_2037)))
in (FStar_SMTEncoding_Term.mkForall _172_2039))
in (_172_2040, Some ("data constructor typing elim"), Some ((Prims.strcat "data_elim_" ddconstrsym))))
in FStar_SMTEncoding_Term.Assume (_172_2041))
in (

let subterm_ordering = if (FStar_Ident.lid_equals d FStar_Syntax_Const.lextop_lid) then begin
(

let x = (let _172_2042 = (varops.fresh "x")
in (_172_2042, FStar_SMTEncoding_Term.Term_sort))
in (

let xtm = (FStar_SMTEncoding_Term.mkFreeV x)
in (let _172_2054 = (let _172_2053 = (let _172_2050 = (let _172_2049 = (let _172_2044 = (let _172_2043 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in (_172_2043)::[])
in (_172_2044)::[])
in (let _172_2048 = (let _172_2047 = (let _172_2046 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (let _172_2045 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in (_172_2046, _172_2045)))
in (FStar_SMTEncoding_Term.mkImp _172_2047))
in (_172_2049, (x)::[], _172_2048)))
in (FStar_SMTEncoding_Term.mkForall _172_2050))
in (let _172_2052 = (let _172_2051 = (varops.fresh "lextop")
in Some (_172_2051))
in (_172_2053, Some ("lextop is top"), _172_2052)))
in FStar_SMTEncoding_Term.Assume (_172_2054))))
end else begin
(

let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
[]
end
| FStar_SMTEncoding_Term.Term_sort -> begin
(let _172_2057 = (let _172_2056 = (FStar_SMTEncoding_Term.mkFreeV v)
in (FStar_SMTEncoding_Term.mk_Precedes _172_2056 dapp))
in (_172_2057)::[])
end
| _83_2711 -> begin
(FStar_All.failwith "unexpected sort")
end))))
in (let _172_2064 = (let _172_2063 = (let _172_2062 = (let _172_2061 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _172_2060 = (let _172_2059 = (let _172_2058 = (FStar_SMTEncoding_Term.mk_and_l prec)
in (ty_pred, _172_2058))
in (FStar_SMTEncoding_Term.mkImp _172_2059))
in (((ty_pred)::[])::[], _172_2061, _172_2060)))
in (FStar_SMTEncoding_Term.mkForall _172_2062))
in (_172_2063, Some ("subterm ordering"), Some ((Prims.strcat "subterm_ordering_" ddconstrsym))))
in FStar_SMTEncoding_Term.Assume (_172_2064)))
end
in (arg_decls, (typing_inversion)::(subterm_ordering)::[])))))))))
end))
end)))
end
| _83_2715 -> begin
(

let _83_2716 = (let _172_2067 = (let _172_2066 = (FStar_Syntax_Print.lid_to_string d)
in (let _172_2065 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _172_2066 _172_2065)))
in (FStar_TypeChecker_Errors.warn drange _172_2067))
in ([], []))
end)
end))
end))
in (

let _83_2720 = (encode_elim ())
in (match (_83_2720) with
| (decls2, elim) -> begin
(

let g = (let _172_2092 = (let _172_2091 = (let _172_2076 = (let _172_2075 = (let _172_2074 = (let _172_2073 = (let _172_2072 = (let _172_2071 = (let _172_2070 = (let _172_2069 = (let _172_2068 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" _172_2068))
in Some (_172_2069))
in (ddtok, [], FStar_SMTEncoding_Term.Term_sort, _172_2070))
in FStar_SMTEncoding_Term.DeclFun (_172_2071))
in (_172_2072)::[])
in (FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) decls3) _172_2073))
in (FStar_List.append _172_2074 proxy_fresh))
in (FStar_List.append _172_2075 decls_formals))
in (FStar_List.append _172_2076 decls_pred))
in (let _172_2090 = (let _172_2089 = (let _172_2088 = (let _172_2080 = (let _172_2079 = (let _172_2078 = (let _172_2077 = (FStar_SMTEncoding_Term.mkEq (app, dapp))
in (((app)::[])::[], vars, _172_2077))
in (FStar_SMTEncoding_Term.mkForall _172_2078))
in (_172_2079, Some ("equality for proxy"), Some ((Prims.strcat "equality_tok_" ddtok))))
in FStar_SMTEncoding_Term.Assume (_172_2080))
in (let _172_2087 = (let _172_2086 = (let _172_2085 = (let _172_2084 = (let _172_2083 = (let _172_2082 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) vars')
in (let _172_2081 = (FStar_SMTEncoding_Term.mkImp (guard', ty_pred'))
in (((ty_pred')::[])::[], _172_2082, _172_2081)))
in (FStar_SMTEncoding_Term.mkForall _172_2083))
in (_172_2084, Some ("data constructor typing intro"), Some ((Prims.strcat "data_tping_intro_" ddtok))))
in FStar_SMTEncoding_Term.Assume (_172_2085))
in (_172_2086)::[])
in (_172_2088)::_172_2087))
in (FStar_SMTEncoding_Term.Assume ((tok_typing, Some ("typing for data constructor proxy"), Some ((Prims.strcat "typing_tok_" ddtok)))))::_172_2089)
in (FStar_List.append _172_2091 _172_2090)))
in (FStar_List.append _172_2092 elim))
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
and declare_top_level_let : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  ((Prims.string * FStar_SMTEncoding_Term.term Prims.option) * FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env x t t_norm -> (match ((try_lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
(

let _83_2729 = (encode_free_var env x t t_norm [])
in (match (_83_2729) with
| (decls, env) -> begin
(

let _83_2734 = (lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_83_2734) with
| (n, x', _83_2733) -> begin
((n, x'), decls, env)
end))
end))
end
| Some (n, x, _83_2738) -> begin
((n, x), [], env)
end))
and encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let _83_2747 = (encode_function_type_as_formula None None t env)
in (match (_83_2747) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_SMTEncoding_Term.Assume ((form, Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str)), Some ((Prims.strcat "lemma_" lid.FStar_Ident.str)))))::[]))
end))))
and encode_free_var : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env fv tt t_norm quals -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if ((let _172_2105 = (FStar_Syntax_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _172_2105)) || (FStar_Syntax_Util.is_lemma t_norm)) then begin
(

let _83_2757 = (new_term_constant_and_tok_from_lid env lid)
in (match (_83_2757) with
| (vname, vtok, env) -> begin
(

let arg_sorts = (match ((let _172_2106 = (FStar_Syntax_Subst.compress t_norm)
in _172_2106.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _83_2760) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun _83_2763 -> FStar_SMTEncoding_Term.Term_sort)))
end
| _83_2766 -> begin
[]
end)
in (

let d = FStar_SMTEncoding_Term.DeclFun ((vname, arg_sorts, FStar_SMTEncoding_Term.Term_sort, Some ("Uninterpreted function symbol for impure function")))
in (

let dd = FStar_SMTEncoding_Term.DeclFun ((vtok, [], FStar_SMTEncoding_Term.Term_sort, Some ("Uninterpreted name for impure function")))
in ((d)::(dd)::[], env))))
end))
end else begin
if (prims.is lid) then begin
(

let vname = (varops.new_fvar lid)
in (

let definition = (prims.mk lid vname)
in (

let env = (push_free_var env lid vname None)
in (definition, env))))
end else begin
(

let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (

let _83_2781 = (

let _83_2776 = (curried_arrow_formals_comp t_norm)
in (match (_83_2776) with
| (args, comp) -> begin
if encode_non_total_function_typ then begin
(let _172_2108 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in (args, _172_2108))
end else begin
(args, (None, (FStar_Syntax_Util.comp_result comp)))
end
end))
in (match (_83_2781) with
| (formals, (pre_opt, res_t)) -> begin
(

let _83_2785 = (new_term_constant_and_tok_from_lid env lid)
in (match (_83_2785) with
| (vname, vtok, env) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV (vname, FStar_SMTEncoding_Term.Term_sort))
end
| _83_2788 -> begin
(FStar_SMTEncoding_Term.mkApp (vtok, []))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun _83_21 -> (match (_83_21) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(

let _83_2804 = (FStar_Util.prefix vars)
in (match (_83_2804) with
| (_83_2799, (xxsym, _83_2802)) -> begin
(

let xx = (FStar_SMTEncoding_Term.mkFreeV (xxsym, FStar_SMTEncoding_Term.Term_sort))
in (let _172_2125 = (let _172_2124 = (let _172_2123 = (let _172_2122 = (let _172_2121 = (let _172_2120 = (let _172_2119 = (let _172_2118 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _172_2118))
in (vapp, _172_2119))
in (FStar_SMTEncoding_Term.mkEq _172_2120))
in (((vapp)::[])::[], vars, _172_2121))
in (FStar_SMTEncoding_Term.mkForall _172_2122))
in (_172_2123, Some ("Discriminator equation"), Some ((Prims.strcat "disc_equation_" (escape d.FStar_Ident.str)))))
in FStar_SMTEncoding_Term.Assume (_172_2124))
in (_172_2125)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(

let _83_2816 = (FStar_Util.prefix vars)
in (match (_83_2816) with
| (_83_2811, (xxsym, _83_2814)) -> begin
(

let xx = (FStar_SMTEncoding_Term.mkFreeV (xxsym, FStar_SMTEncoding_Term.Term_sort))
in (

let f = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = 0; FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (

let tp_name = (mk_term_projector_name d f)
in (

let prim_app = (FStar_SMTEncoding_Term.mkApp (tp_name, (xx)::[]))
in (let _172_2130 = (let _172_2129 = (let _172_2128 = (let _172_2127 = (let _172_2126 = (FStar_SMTEncoding_Term.mkEq (vapp, prim_app))
in (((vapp)::[])::[], vars, _172_2126))
in (FStar_SMTEncoding_Term.mkForall _172_2127))
in (_172_2128, Some ("Projector equation"), Some ((Prims.strcat "proj_equation_" tp_name))))
in FStar_SMTEncoding_Term.Assume (_172_2129))
in (_172_2130)::[])))))
end))
end
| _83_2822 -> begin
[]
end)))))
in (

let _83_2829 = (encode_binders None formals env)
in (match (_83_2829) with
| (vars, guards, env', decls1, _83_2828) -> begin
(

let _83_2838 = (match (pre_opt) with
| None -> begin
(let _172_2131 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_172_2131, decls1))
end
| Some (p) -> begin
(

let _83_2835 = (encode_formula p env')
in (match (_83_2835) with
| (g, ds) -> begin
(let _172_2132 = (FStar_SMTEncoding_Term.mk_and_l ((g)::guards))
in (_172_2132, (FStar_List.append decls1 ds)))
end))
end)
in (match (_83_2838) with
| (guard, decls1) -> begin
(

let vtok_app = (mk_Apply vtok_tm vars)
in (

let vapp = (let _172_2134 = (let _172_2133 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (vname, _172_2133))
in (FStar_SMTEncoding_Term.mkApp _172_2134))
in (

let _83_2862 = (

let vname_decl = (let _172_2137 = (let _172_2136 = (FStar_All.pipe_right formals (FStar_List.map (fun _83_2841 -> FStar_SMTEncoding_Term.Term_sort)))
in (vname, _172_2136, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_172_2137))
in (

let _83_2849 = (

let env = (

let _83_2844 = env
in {bindings = _83_2844.bindings; depth = _83_2844.depth; tcenv = _83_2844.tcenv; warn = _83_2844.warn; cache = _83_2844.cache; nolabels = _83_2844.nolabels; use_zfuel_name = _83_2844.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in if (not ((head_normal env tt))) then begin
(encode_term_pred None tt env vtok_tm)
end else begin
(encode_term_pred None t_norm env vtok_tm)
end)
in (match (_83_2849) with
| (tok_typing, decls2) -> begin
(

let tok_typing = FStar_SMTEncoding_Term.Assume ((tok_typing, Some ("function token typing"), Some ((Prims.strcat "function_token_typing_" vname))))
in (

let _83_2859 = (match (formals) with
| [] -> begin
(let _172_2141 = (let _172_2140 = (let _172_2139 = (FStar_SMTEncoding_Term.mkFreeV (vname, FStar_SMTEncoding_Term.Term_sort))
in (FStar_All.pipe_left (fun _172_2138 -> Some (_172_2138)) _172_2139))
in (push_free_var env lid vname _172_2140))
in ((FStar_List.append decls2 ((tok_typing)::[])), _172_2141))
end
| _83_2853 -> begin
(

let vtok_decl = FStar_SMTEncoding_Term.DeclFun ((vtok, [], FStar_SMTEncoding_Term.Term_sort, None))
in (

let vtok_fresh = (let _172_2142 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (vtok, FStar_SMTEncoding_Term.Term_sort) _172_2142))
in (

let name_tok_corr = (let _172_2146 = (let _172_2145 = (let _172_2144 = (let _172_2143 = (FStar_SMTEncoding_Term.mkEq (vtok_app, vapp))
in (((vtok_app)::[])::[], vars, _172_2143))
in (FStar_SMTEncoding_Term.mkForall _172_2144))
in (_172_2145, Some ("Name-token correspondence"), Some ((Prims.strcat "token_correspondence_" vname))))
in FStar_SMTEncoding_Term.Assume (_172_2146))
in ((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[])), env))))
end)
in (match (_83_2859) with
| (tok_decl, env) -> begin
((vname_decl)::tok_decl, env)
end)))
end)))
in (match (_83_2862) with
| (decls2, env) -> begin
(

let _83_2870 = (

let res_t = (FStar_Syntax_Subst.compress res_t)
in (

let _83_2866 = (encode_term res_t env')
in (match (_83_2866) with
| (encoded_res_t, decls) -> begin
(let _172_2147 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in (encoded_res_t, _172_2147, decls))
end)))
in (match (_83_2870) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (let _172_2151 = (let _172_2150 = (let _172_2149 = (let _172_2148 = (FStar_SMTEncoding_Term.mkImp (guard, ty_pred))
in (((vapp)::[])::[], vars, _172_2148))
in (FStar_SMTEncoding_Term.mkForall _172_2149))
in (_172_2150, Some ("free var typing"), Some ((Prims.strcat "typing_" vname))))
in FStar_SMTEncoding_Term.Assume (_172_2151))
in (

let freshness = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New)) then begin
(let _172_2157 = (let _172_2154 = (let _172_2153 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (let _172_2152 = (varops.next_id ())
in (vname, _172_2153, FStar_SMTEncoding_Term.Term_sort, _172_2152)))
in (FStar_SMTEncoding_Term.fresh_constructor _172_2154))
in (let _172_2156 = (let _172_2155 = (pretype_axiom vapp vars)
in (_172_2155)::[])
in (_172_2157)::_172_2156))
end else begin
[]
end
in (

let g = (let _172_2159 = (let _172_2158 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_172_2158)
in (FStar_List.append (FStar_List.append (FStar_List.append (FStar_List.append decls1 decls2) decls3) freshness) _172_2159))
in (g, env))))
end))
end))))
end))
end))))
end))
end)))
end
end))
and encode_signature : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _83_2878 se -> (match (_83_2878) with
| (g, env) -> begin
(

let _83_2882 = (encode_sigelt env se)
in (match (_83_2882) with
| (g', env) -> begin
((FStar_List.append g g'), env)
end))
end)) ([], env))))


let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings -> (

let encode_binding = (fun b _83_2889 -> (match (_83_2889) with
| (decls, env) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (_83_2891) -> begin
([], env)
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(

let _83_2898 = (new_term_constant env x)
in (match (_83_2898) with
| (xxsym, xx, env') -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (

let _83_2900 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _172_2174 = (FStar_Syntax_Print.bv_to_string x)
in (let _172_2173 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _172_2172 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" _172_2174 _172_2173 _172_2172))))
end else begin
()
end
in (

let _83_2904 = (encode_term_pred None t1 env xx)
in (match (_83_2904) with
| (t, decls') -> begin
(

let caption = if (FStar_Options.log_queries ()) then begin
(let _172_2178 = (let _172_2177 = (FStar_Syntax_Print.bv_to_string x)
in (let _172_2176 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _172_2175 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _172_2177 _172_2176 _172_2175))))
in Some (_172_2178))
end else begin
None
end
in (

let ax = (

let a_name = Some ((Prims.strcat "binder_" xxsym))
in FStar_SMTEncoding_Term.Assume ((t, a_name, a_name)))
in (

let g = (FStar_List.append (FStar_List.append ((FStar_SMTEncoding_Term.DeclFun ((xxsym, [], FStar_SMTEncoding_Term.Term_sort, caption)))::[]) decls') ((ax)::[]))
in ((FStar_List.append decls g), env'))))
end))))
end))
end
| FStar_TypeChecker_Env.Binding_lid (x, (_83_2911, t)) -> begin
(

let t_norm = (whnf env t)
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant None)
in (

let _83_2920 = (encode_free_var env fv t t_norm [])
in (match (_83_2920) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end))))
end
| (FStar_TypeChecker_Env.Binding_sig_inst (_, se, _)) | (FStar_TypeChecker_Env.Binding_sig (_, se)) -> begin
(

let _83_2934 = (encode_sigelt env se)
in (match (_83_2934) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end))
end)
end))
in (FStar_List.fold_right encode_binding bindings ([], env))))


let encode_labels = (fun labs -> (

let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _83_2941 -> (match (_83_2941) with
| (l, _83_2938, _83_2940) -> begin
FStar_SMTEncoding_Term.DeclFun (((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _83_2948 -> (match (_83_2948) with
| (l, _83_2945, _83_2947) -> begin
(let _172_2186 = (FStar_All.pipe_left (fun _172_2182 -> FStar_SMTEncoding_Term.Echo (_172_2182)) (Prims.fst l))
in (let _172_2185 = (let _172_2184 = (let _172_2183 = (FStar_SMTEncoding_Term.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (_172_2183))
in (_172_2184)::[])
in (_172_2186)::_172_2185))
end))))
in (prefix, suffix))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (let _172_2191 = (let _172_2190 = (let _172_2189 = (FStar_Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _172_2189; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_172_2190)::[])
in (FStar_ST.op_Colon_Equals last_env _172_2191)))


let get_env : FStar_TypeChecker_Env.env  ->  env_t = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "No env; call init first!")
end
| e::_83_2954 -> begin
(

let _83_2957 = e
in {bindings = _83_2957.bindings; depth = _83_2957.depth; tcenv = tcenv; warn = _83_2957.warn; cache = _83_2957.cache; nolabels = _83_2957.nolabels; use_zfuel_name = _83_2957.use_zfuel_name; encode_non_total_function_typ = _83_2957.encode_non_total_function_typ})
end))


let set_env : env_t  ->  Prims.unit = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| _83_2963::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))


let push_env : Prims.unit  ->  Prims.unit = (fun _83_2965 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| hd::tl -> begin
(

let refs = (FStar_Util.smap_copy hd.cache)
in (

let top = (

let _83_2971 = hd
in {bindings = _83_2971.bindings; depth = _83_2971.depth; tcenv = _83_2971.tcenv; warn = _83_2971.warn; cache = refs; nolabels = _83_2971.nolabels; use_zfuel_name = _83_2971.use_zfuel_name; encode_non_total_function_typ = _83_2971.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))


let pop_env : Prims.unit  ->  Prims.unit = (fun _83_2974 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Popping an empty stack")
end
| _83_2978::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))


let mark_env : Prims.unit  ->  Prims.unit = (fun _83_2980 -> (match (()) with
| () -> begin
(push_env ())
end))


let reset_mark_env : Prims.unit  ->  Prims.unit = (fun _83_2981 -> (match (()) with
| () -> begin
(pop_env ())
end))


let commit_mark_env : Prims.unit  ->  Prims.unit = (fun _83_2982 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| hd::_83_2985::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _83_2990 -> begin
(FStar_All.failwith "Impossible")
end)
end))


let init : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (

let _83_2992 = (init_env tcenv)
in (

let _83_2994 = (FStar_SMTEncoding_Z3.init ())
in (FStar_SMTEncoding_Z3.giveZ3 ((FStar_SMTEncoding_Term.DefPrelude)::[])))))


let push : Prims.string  ->  Prims.unit = (fun msg -> (

let _83_2997 = (push_env ())
in (

let _83_2999 = (varops.push ())
in (FStar_SMTEncoding_Z3.push msg))))


let pop : Prims.string  ->  Prims.unit = (fun msg -> (

let _83_3002 = (let _172_2212 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _172_2212))
in (

let _83_3004 = (varops.pop ())
in (FStar_SMTEncoding_Z3.pop msg))))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _83_3007 = (mark_env ())
in (

let _83_3009 = (varops.mark ())
in (FStar_SMTEncoding_Z3.mark msg))))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _83_3012 = (reset_mark_env ())
in (

let _83_3014 = (varops.reset_mark ())
in (FStar_SMTEncoding_Z3.reset_mark msg))))


let commit_mark = (fun msg -> (

let _83_3017 = (commit_mark_env ())
in (

let _83_3019 = (varops.commit_mark ())
in (FStar_SMTEncoding_Z3.commit_mark msg))))


let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (

let caption = (fun decls -> if (FStar_Options.log_queries ()) then begin
(let _172_2228 = (let _172_2227 = (let _172_2226 = (let _172_2225 = (let _172_2224 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _172_2224 (FStar_List.map FStar_Syntax_Print.lid_to_string)))
in (FStar_All.pipe_right _172_2225 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " _172_2226))
in FStar_SMTEncoding_Term.Caption (_172_2227))
in (_172_2228)::decls)
end else begin
decls
end)
in (

let env = (get_env tcenv)
in (

let _83_3028 = (encode_sigelt env se)
in (match (_83_3028) with
| (decls, env) -> begin
(

let _83_3029 = (set_env env)
in (let _172_2229 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 _172_2229)))
end)))))


let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let _83_3034 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(let _172_2234 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name _172_2234))
end else begin
()
end
in (

let env = (get_env tcenv)
in (

let _83_3041 = (encode_signature (

let _83_3037 = env
in {bindings = _83_3037.bindings; depth = _83_3037.depth; tcenv = _83_3037.tcenv; warn = false; cache = _83_3037.cache; nolabels = _83_3037.nolabels; use_zfuel_name = _83_3037.use_zfuel_name; encode_non_total_function_typ = _83_3037.encode_non_total_function_typ}) modul.FStar_Syntax_Syntax.exports)
in (match (_83_3041) with
| (decls, env) -> begin
(

let caption = (fun decls -> if (FStar_Options.log_queries ()) then begin
(

let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::decls) ((FStar_SMTEncoding_Term.Caption ((Prims.strcat "End " msg)))::[])))
end else begin
decls
end)
in (

let _83_3047 = (set_env (

let _83_3045 = env
in {bindings = _83_3045.bindings; depth = _83_3045.depth; tcenv = _83_3045.tcenv; warn = true; cache = _83_3045.cache; nolabels = _83_3045.nolabels; use_zfuel_name = _83_3045.use_zfuel_name; encode_non_total_function_typ = _83_3045.encode_non_total_function_typ}))
in (

let _83_3049 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end else begin
()
end
in (

let decls = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls)))))
end))))))


let solve : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun use_env_msg tcenv q -> (

let _83_3055 = (let _172_2253 = (let _172_2252 = (let _172_2251 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _172_2251))
in (FStar_Util.format1 "Starting query at %s" _172_2252))
in (push _172_2253))
in (

let pop = (fun _83_3058 -> (match (()) with
| () -> begin
(let _172_2258 = (let _172_2257 = (let _172_2256 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _172_2256))
in (FStar_Util.format1 "Ending query at %s" _172_2257))
in (pop _172_2258))
end))
in (

let _83_3112 = (

let env = (get_env tcenv)
in (

let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (

let _83_3082 = (

let rec aux = (fun bindings -> (match (bindings) with
| FStar_TypeChecker_Env.Binding_var (x)::rest -> begin
(

let _83_3071 = (aux rest)
in (match (_83_3071) with
| (out, rest) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (let _172_2264 = (let _172_2263 = (FStar_Syntax_Syntax.mk_binder (

let _83_3073 = x
in {FStar_Syntax_Syntax.ppname = _83_3073.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _83_3073.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_172_2263)::out)
in (_172_2264, rest)))
end))
end
| _83_3076 -> begin
([], bindings)
end))
in (

let _83_3079 = (aux bindings)
in (match (_83_3079) with
| (closing, bindings) -> begin
(let _172_2265 = (FStar_Syntax_Util.close_forall (FStar_List.rev closing) q)
in (_172_2265, bindings))
end)))
in (match (_83_3082) with
| (q, bindings) -> begin
(

let _83_3091 = (let _172_2267 = (FStar_List.filter (fun _83_22 -> (match (_83_22) with
| FStar_TypeChecker_Env.Binding_sig (_83_3085) -> begin
false
end
| _83_3088 -> begin
true
end)) bindings)
in (encode_env_bindings env _172_2267))
in (match (_83_3091) with
| (env_decls, env) -> begin
(

let _83_3092 = if ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) then begin
(let _172_2268 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" _172_2268))
end else begin
()
end
in (

let _83_3096 = (encode_formula q env)
in (match (_83_3096) with
| (phi, qdecls) -> begin
(

let _83_3101 = (let _172_2269 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg _172_2269 phi))
in (match (_83_3101) with
| (phi, labels, _83_3100) -> begin
(

let _83_3104 = (encode_labels labels)
in (match (_83_3104) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append (FStar_List.append env_decls label_prefix) qdecls)
in (

let qry = (let _172_2273 = (let _172_2272 = (FStar_SMTEncoding_Term.mkNot phi)
in (let _172_2271 = (let _172_2270 = (varops.fresh "query")
in Some (_172_2270))
in (_172_2272, Some ("query"), _172_2271)))
in FStar_SMTEncoding_Term.Assume (_172_2273))
in (

let suffix = (FStar_List.append label_suffix ((FStar_SMTEncoding_Term.Echo ("Done!"))::[]))
in (query_prelude, labels, qry, suffix))))
end))
end))
end)))
end))
end))))
in (match (_83_3112) with
| (prefix, labels, qry, suffix) -> begin
(match (qry) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.False, _83_3119); FStar_SMTEncoding_Term.hash = _83_3116; FStar_SMTEncoding_Term.freevars = _83_3114}, _83_3124, _83_3126) -> begin
(

let _83_3129 = (pop ())
in ())
end
| _83_3132 when tcenv.FStar_TypeChecker_Env.admit -> begin
(

let _83_3133 = (pop ())
in ())
end
| FStar_SMTEncoding_Term.Assume (q, _83_3137, _83_3139) -> begin
(

let fresh = ((FStar_String.length q.FStar_SMTEncoding_Term.hash) >= 2048)
in (

let _83_3143 = (FStar_SMTEncoding_ErrorReporting.askZ3_and_report_errors tcenv fresh labels prefix qry suffix)
in (pop ())))
end
| _83_3146 -> begin
(FStar_All.failwith "Impossible")
end)
end)))))


let is_trivial : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun tcenv q -> (

let env = (get_env tcenv)
in (

let _83_3150 = (push "query")
in (

let _83_3155 = (encode_formula q env)
in (match (_83_3155) with
| (f, _83_3154) -> begin
(

let _83_3156 = (pop "query")
in (match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _83_3160) -> begin
true
end
| _83_3164 -> begin
false
end))
end)))))


let solver : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = init; FStar_TypeChecker_Env.push = push; FStar_TypeChecker_Env.pop = pop; FStar_TypeChecker_Env.mark = mark; FStar_TypeChecker_Env.reset_mark = reset_mark; FStar_TypeChecker_Env.commit_mark = commit_mark; FStar_TypeChecker_Env.encode_modul = encode_modul; FStar_TypeChecker_Env.encode_sig = encode_sig; FStar_TypeChecker_Env.solve = solve; FStar_TypeChecker_Env.is_trivial = is_trivial; FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish; FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh}


let dummy : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = (fun _83_3165 -> ()); FStar_TypeChecker_Env.push = (fun _83_3167 -> ()); FStar_TypeChecker_Env.pop = (fun _83_3169 -> ()); FStar_TypeChecker_Env.mark = (fun _83_3171 -> ()); FStar_TypeChecker_Env.reset_mark = (fun _83_3173 -> ()); FStar_TypeChecker_Env.commit_mark = (fun _83_3175 -> ()); FStar_TypeChecker_Env.encode_modul = (fun _83_3177 _83_3179 -> ()); FStar_TypeChecker_Env.encode_sig = (fun _83_3181 _83_3183 -> ()); FStar_TypeChecker_Env.solve = (fun _83_3185 _83_3187 _83_3189 -> ()); FStar_TypeChecker_Env.is_trivial = (fun _83_3191 _83_3193 -> false); FStar_TypeChecker_Env.finish = (fun _83_3195 -> ()); FStar_TypeChecker_Env.refresh = (fun _83_3196 -> ())}




