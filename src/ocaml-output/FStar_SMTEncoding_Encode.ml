
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
(let _173_12 = (let _173_11 = (let _173_10 = (let _173_9 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp s _173_9))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _173_10))
in FStar_Util.Inl (_173_11))
in Some (_173_12))
end
| _83_45 -> begin
l
end))


let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s '\'' '_'))


let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun lid a -> (

let a = (

let _83_49 = a
in (let _173_19 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _173_19; FStar_Syntax_Syntax.index = _83_49.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _83_49.FStar_Syntax_Syntax.sort}))
in (let _173_20 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str a.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (FStar_All.pipe_left escape _173_20))))


let primitive_projector_by_pos : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (

let fail = (fun _83_56 -> (match (()) with
| () -> begin
(let _173_30 = (let _173_29 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" _173_29 lid.FStar_Ident.str))
in (FStar_All.failwith _173_30))
end))
in (

let _83_60 = (FStar_TypeChecker_Env.lookup_datacon env lid)
in (match (_83_60) with
| (_83_58, t) -> begin
(match ((let _173_31 = (FStar_Syntax_Subst.compress t)
in _173_31.FStar_Syntax_Syntax.n)) with
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


let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (let _173_37 = (let _173_36 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str _173_36))
in (FStar_All.pipe_left escape _173_37)))


let mk_term_projector : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun lid a -> (let _173_43 = (let _173_42 = (mk_term_projector_name lid a)
in (_173_42, FStar_SMTEncoding_Term.Arrow ((FStar_SMTEncoding_Term.Term_sort, FStar_SMTEncoding_Term.Term_sort))))
in (FStar_SMTEncoding_Term.mkFreeV _173_43)))


let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_SMTEncoding_Term.term = (fun lid i -> (let _173_49 = (let _173_48 = (mk_term_projector_name_by_pos lid i)
in (_173_48, FStar_SMTEncoding_Term.Arrow ((FStar_SMTEncoding_Term.Term_sort, FStar_SMTEncoding_Term.Term_sort))))
in (FStar_SMTEncoding_Term.mkFreeV _173_49)))


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
(let _173_153 = (FStar_Util.smap_create 100)
in (let _173_152 = (FStar_Util.smap_create 100)
in (_173_153, _173_152)))
end))
in (

let scopes = (let _173_155 = (let _173_154 = (new_scope ())
in (_173_154)::[])
in (FStar_Util.mk_ref _173_155))
in (

let mk_unique = (fun y -> (

let y = (escape y)
in (

let y = (match ((let _173_159 = (FStar_ST.read scopes)
in (FStar_Util.find_map _173_159 (fun _83_103 -> (match (_83_103) with
| (names, _83_102) -> begin
(FStar_Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_83_106) -> begin
(

let _83_108 = (FStar_Util.incr ctr)
in (let _173_161 = (let _173_160 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _173_160))
in (Prims.strcat (Prims.strcat y "__") _173_161)))
end)
in (

let top_scope = (let _173_163 = (let _173_162 = (FStar_ST.read scopes)
in (FStar_List.hd _173_162))
in (FStar_All.pipe_left Prims.fst _173_163))
in (

let _83_112 = (FStar_Util.smap_add top_scope y true)
in y)))))
in (

let new_var = (fun pp rn -> (let _173_170 = (let _173_168 = (FStar_All.pipe_left mk_unique pp.FStar_Ident.idText)
in (Prims.strcat _173_168 "__"))
in (let _173_169 = (FStar_Util.string_of_int rn)
in (Prims.strcat _173_170 _173_169))))
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

let fresh = (fun pfx -> (let _173_178 = (let _173_177 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _173_177))
in (FStar_Util.format2 "%s_%s" pfx _173_178)))
in (

let string_const = (fun s -> (match ((let _173_182 = (FStar_ST.read scopes)
in (FStar_Util.find_map _173_182 (fun _83_130 -> (match (_83_130) with
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

let f = (let _173_183 = (FStar_SMTEncoding_Term.mk_String_const id)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString _173_183))
in (

let top_scope = (let _173_185 = (let _173_184 = (FStar_ST.read scopes)
in (FStar_List.hd _173_184))
in (FStar_All.pipe_left Prims.snd _173_185))
in (

let _83_137 = (FStar_Util.smap_add top_scope s f)
in f))))
end))
in (

let push = (fun _83_140 -> (match (()) with
| () -> begin
(let _173_190 = (let _173_189 = (new_scope ())
in (let _173_188 = (FStar_ST.read scopes)
in (_173_189)::_173_188))
in (FStar_ST.op_Colon_Equals scopes _173_190))
end))
in (

let pop = (fun _83_142 -> (match (()) with
| () -> begin
(let _173_194 = (let _173_193 = (FStar_ST.read scopes)
in (FStar_List.tl _173_193))
in (FStar_ST.op_Colon_Equals scopes _173_194))
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
| ((hd1, hd2))::((next1, next2))::tl -> begin
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
in (let _173_209 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _173_209; FStar_Syntax_Syntax.index = _83_171.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _83_171.FStar_Syntax_Syntax.sort})))


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


let print_env : env_t  ->  Prims.string = (fun e -> (let _173_267 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun _83_2 -> (match (_83_2) with
| Binding_var (x, _83_193) -> begin
(FStar_Syntax_Print.bv_to_string x)
end
| Binding_fvar (l, _83_198, _83_200, _83_202) -> begin
(FStar_Syntax_Print.lid_to_string l)
end))))
in (FStar_All.pipe_right _173_267 (FStar_String.concat ", "))))


let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))


let caption_t : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.string Prims.option = (fun env t -> if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _173_277 = (FStar_Syntax_Print.term_to_string t)
in Some (_173_277))
end else begin
None
end)


let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (

let xsym = (varops.fresh x)
in (let _173_282 = (FStar_SMTEncoding_Term.mkFreeV (xsym, s))
in (xsym, _173_282))))


let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (let _173_287 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _173_287))
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
(let _173_304 = (let _173_303 = (FStar_Syntax_Print.bv_to_string a)
in (FStar_Util.format1 "Bound term variable not found: %s" _173_303))
in (FStar_All.failwith _173_304))
end
| Some (b, t) -> begin
t
end))


let new_term_constant_and_tok_from_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * Prims.string * env_t) = (fun env x -> (

let fname = (varops.new_fvar x)
in (

let ftok = (Prims.strcat fname "@tok")
in (let _173_315 = (

let _83_247 = env
in (let _173_314 = (let _173_313 = (let _173_312 = (let _173_311 = (let _173_310 = (FStar_SMTEncoding_Term.mkApp (ftok, []))
in (FStar_All.pipe_left (fun _173_309 -> Some (_173_309)) _173_310))
in (x, fname, _173_311, None))
in Binding_fvar (_173_312))
in (_173_313)::env.bindings)
in {bindings = _173_314; depth = _83_247.depth; tcenv = _83_247.tcenv; warn = _83_247.warn; cache = _83_247.cache; nolabels = _83_247.nolabels; use_zfuel_name = _83_247.use_zfuel_name; encode_non_total_function_typ = _83_247.encode_non_total_function_typ}))
in (fname, ftok, _173_315)))))


let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun _83_4 -> (match (_83_4) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some ((t1, t2, t3))
end
| _83_259 -> begin
None
end))))


let contains_name : env_t  ->  Prims.string  ->  Prims.bool = (fun env s -> (let _173_326 = (lookup_binding env (fun _83_5 -> (match (_83_5) with
| Binding_fvar (b, t1, t2, t3) when (b.FStar_Ident.str = s) -> begin
Some (())
end
| _83_270 -> begin
None
end)))
in (FStar_All.pipe_right _173_326 FStar_Option.isSome)))


let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _173_332 = (let _173_331 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" _173_331))
in (FStar_All.failwith _173_332))
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

let t3 = (let _173_349 = (let _173_348 = (let _173_347 = (FStar_SMTEncoding_Term.mkApp ("ZFuel", []))
in (_173_347)::[])
in (f, _173_348))
in (FStar_SMTEncoding_Term.mkApp _173_349))
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
| FStar_SMTEncoding_Term.App (_83_308, (fuel)::[]) -> begin
if (let _173_355 = (let _173_354 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right _173_354 Prims.fst))
in (FStar_Util.starts_with _173_355 "fuel")) then begin
(let _173_358 = (let _173_357 = (FStar_SMTEncoding_Term.mkFreeV (name, FStar_SMTEncoding_Term.Term_sort))
in (FStar_SMTEncoding_Term.mk_ApplyTF _173_357 fuel))
in (FStar_All.pipe_left (fun _173_356 -> Some (_173_356)) _173_358))
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
(let _173_362 = (let _173_361 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _173_361))
in (FStar_All.failwith _173_362))
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
| FStar_SMTEncoding_Term.App (g, (fuel)::[]) -> begin
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
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (guard)::(body')::[]) -> begin
(

let guard = (match (guard.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, guards) -> begin
(let _173_379 = (add_fuel guards)
in (FStar_SMTEncoding_Term.mk_and_l _173_379))
end
| _83_403 -> begin
(let _173_380 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _173_380 FStar_List.hd))
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
(let _173_386 = (FStar_TypeChecker_Env.lookup_definition FStar_TypeChecker_Env.OnlyInline env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _173_386 FStar_Option.isNone))
end
| _83_445 -> begin
false
end)))


let head_redex : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (match ((let _173_391 = (FStar_Syntax_Util.un_uinst t)
in _173_391.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_83_449) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(let _173_392 = (FStar_TypeChecker_Env.lookup_definition FStar_TypeChecker_Env.OnlyInline env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _173_392 FStar_Option.isSome))
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


let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (let _173_405 = (let _173_403 = (FStar_Syntax_Syntax.null_binder t)
in (_173_403)::[])
in (let _173_404 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Util.abs _173_405 _173_404 None))))


let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(let _173_412 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out _173_412))
end
| s -> begin
(

let _83_466 = ()
in (let _173_413 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTT out _173_413)))
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
| (FStar_SMTEncoding_Term.App (app, (f)::({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.hash = _83_487; FStar_SMTEncoding_Term.freevars = _83_485})::[]), (x)::xs) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
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
(let _173_470 = (let _173_469 = (let _173_468 = (let _173_467 = (FStar_SMTEncoding_Term.mkInteger' (FStar_Util.int_of_char c))
in (FStar_SMTEncoding_Term.boxInt _173_467))
in (_173_468)::[])
in ("FStar.Char.Char", _173_469))
in (FStar_SMTEncoding_Term.mkApp _173_470))
end
| FStar_Const.Const_int (i, None) -> begin
(let _173_471 = (FStar_SMTEncoding_Term.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt _173_471))
end
| FStar_Const.Const_int (i, Some (q)) -> begin
(let _173_475 = (let _173_474 = (let _173_473 = (let _173_472 = (FStar_SMTEncoding_Term.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt _173_472))
in (_173_473)::[])
in ((FStar_Const.constructor_string_of_int_qualifier q), _173_474))
in (FStar_SMTEncoding_Term.mkApp _173_475))
end
| FStar_Const.Const_string (bytes, _83_545) -> begin
(let _173_476 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _173_476))
end
| FStar_Const.Const_range (r) -> begin
FStar_SMTEncoding_Term.mk_Range_const
end
| FStar_Const.Const_effect -> begin
FStar_SMTEncoding_Term.mk_Term_type
end
| c -> begin
(let _173_478 = (let _173_477 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" _173_477))
in (FStar_All.failwith _173_478))
end))


let as_function_typ : env_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (

let rec aux = (fun norm t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_83_559) -> begin
t
end
| FStar_Syntax_Syntax.Tm_refine (_83_562) -> begin
(let _173_487 = (FStar_Syntax_Util.unrefine t)
in (aux true _173_487))
end
| _83_565 -> begin
if norm then begin
(let _173_488 = (whnf env t)
in (aux false _173_488))
end else begin
(let _173_491 = (let _173_490 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (let _173_489 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _173_490 _173_489)))
in (FStar_All.failwith _173_491))
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
(let _173_494 = (FStar_Syntax_Syntax.mk_Total k)
in ([], _173_494))
end)))


let rec encode_binders : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> (

let _83_577 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _173_542 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" _173_542))
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

let _83_593 = (let _173_545 = (norm env x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt _173_545 env xx))
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
(let _173_550 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t)
in (_173_550, decls))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let _83_619 = (encode_term t env)
in (match (_83_619) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _173_555 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t)
in (_173_555, decls))
end
| Some (f) -> begin
(let _173_556 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t)
in (_173_556, decls))
end)
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let t0 = (FStar_Syntax_Subst.compress t)
in (

let _83_626 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _173_561 = (FStar_Syntax_Print.tag_of_term t)
in (let _173_560 = (FStar_Syntax_Print.tag_of_term t0)
in (let _173_559 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" _173_561 _173_560 _173_559))))
end else begin
()
end
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _173_566 = (let _173_565 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (let _173_564 = (FStar_Syntax_Print.tag_of_term t0)
in (let _173_563 = (FStar_Syntax_Print.term_to_string t0)
in (let _173_562 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _173_565 _173_564 _173_563 _173_562)))))
in (FStar_All.failwith _173_566))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _173_568 = (let _173_567 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" _173_567))
in (FStar_All.failwith _173_568))
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
(let _173_569 = (lookup_free_var env v.FStar_Syntax_Syntax.fv_name)
in (_173_569, []))
end
| FStar_Syntax_Syntax.Tm_type (_83_651) -> begin
(FStar_SMTEncoding_Term.mk_Term_type, [])
end
| FStar_Syntax_Syntax.Tm_uinst (t, _83_655) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(let _173_570 = (encode_const c)
in (_173_570, []))
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

let fsym = (let _173_571 = (varops.fresh "f")
in (_173_571, FStar_SMTEncoding_Term.Term_sort))
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
(let _173_572 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_173_572, []))
end
| Some (pre) -> begin
(

let _83_688 = (encode_formula pre env')
in (match (_83_688) with
| (guard, decls0) -> begin
(let _173_573 = (FStar_SMTEncoding_Term.mk_and_l ((guard)::guards))
in (_173_573, decls0))
end))
end)
in (match (_83_691) with
| (guards, guard_decls) -> begin
(

let t_interp = (let _173_575 = (let _173_574 = (FStar_SMTEncoding_Term.mkImp (guards, res_pred))
in (((app)::[])::[], vars, _173_574))
in (FStar_SMTEncoding_Term.mkForall _173_575))
in (

let cvars = (let _173_577 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right _173_577 (FStar_List.filter (fun _83_696 -> (match (_83_696) with
| (x, _83_695) -> begin
(x <> (Prims.fst fsym))
end)))))
in (

let tkey = (FStar_SMTEncoding_Term.mkForall ([], (fsym)::cvars, t_interp))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t', sorts, _83_702) -> begin
(let _173_580 = (let _173_579 = (let _173_578 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in (t', _173_578))
in (FStar_SMTEncoding_Term.mkApp _173_579))
in (_173_580, []))
end
| None -> begin
(

let tsym = (varops.fresh "Tm_arrow")
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let caption = if (FStar_Options.log_queries ()) then begin
(let _173_581 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in Some (_173_581))
end else begin
None
end
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun ((tsym, cvar_sorts, FStar_SMTEncoding_Term.Term_sort, caption))
in (

let t = (let _173_583 = (let _173_582 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (tsym, _173_582))
in (FStar_SMTEncoding_Term.mkApp _173_583))
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let k_assumption = (

let a_name = Some ((Prims.strcat "kinding_" tsym))
in (let _173_585 = (let _173_584 = (FStar_SMTEncoding_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (_173_584, a_name, a_name))
in FStar_SMTEncoding_Term.Assume (_173_585)))
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t)
in (

let pre_typing = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in (let _173_592 = (let _173_591 = (let _173_590 = (let _173_589 = (let _173_588 = (let _173_587 = (let _173_586 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _173_586))
in (f_has_t, _173_587))
in (FStar_SMTEncoding_Term.mkImp _173_588))
in (((f_has_t)::[])::[], (fsym)::cvars, _173_589))
in (mkForall_fuel _173_590))
in (_173_591, Some ("pre-typing for functions"), a_name))
in FStar_SMTEncoding_Term.Assume (_173_592)))
in (

let t_interp = (

let a_name = Some ((Prims.strcat "interpretation_" tsym))
in (let _173_596 = (let _173_595 = (let _173_594 = (let _173_593 = (FStar_SMTEncoding_Term.mkIff (f_has_t_z, t_interp))
in (((f_has_t_z)::[])::[], (fsym)::cvars, _173_593))
in (FStar_SMTEncoding_Term.mkForall _173_594))
in (_173_595, a_name, a_name))
in FStar_SMTEncoding_Term.Assume (_173_596)))
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
in (let _173_598 = (let _173_597 = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (_173_597, Some ("Typing for non-total arrows"), a_name))
in FStar_SMTEncoding_Term.Assume (_173_598)))
in (

let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)
in (

let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let t_interp = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in (let _173_605 = (let _173_604 = (let _173_603 = (let _173_602 = (let _173_601 = (let _173_600 = (let _173_599 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _173_599))
in (f_has_t, _173_600))
in (FStar_SMTEncoding_Term.mkImp _173_601))
in (((f_has_t)::[])::[], (fsym)::[], _173_602))
in (mkForall_fuel _173_603))
in (_173_604, a_name, a_name))
in FStar_SMTEncoding_Term.Assume (_173_605)))
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
(let _173_607 = (let _173_606 = (FStar_List.hd b)
in (Prims.fst _173_606))
in (_173_607, f))
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

let encoding = (let _173_609 = (let _173_608 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in (_173_608, refinement))
in (FStar_SMTEncoding_Term.mkAnd _173_609))
in (

let cvars = (let _173_611 = (FStar_SMTEncoding_Term.free_variables encoding)
in (FStar_All.pipe_right _173_611 (FStar_List.filter (fun _83_772 -> (match (_83_772) with
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
(let _173_614 = (let _173_613 = (let _173_612 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in (t, _173_612))
in (FStar_SMTEncoding_Term.mkApp _173_613))
in (_173_614, []))
end
| None -> begin
(

let tsym = (varops.fresh "Tm_refine")
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun ((tsym, cvar_sorts, FStar_SMTEncoding_Term.Term_sort, None))
in (

let t = (let _173_616 = (let _173_615 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (tsym, _173_615))
in (FStar_SMTEncoding_Term.mkApp _173_616))
in (

let x_has_t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let t_kinding = (let _173_618 = (let _173_617 = (FStar_SMTEncoding_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (_173_617, Some ("refinement kinding"), Some ((Prims.strcat "refinement_kinding_" tsym))))
in FStar_SMTEncoding_Term.Assume (_173_618))
in (

let t_interp = (let _173_624 = (let _173_623 = (let _173_620 = (let _173_619 = (FStar_SMTEncoding_Term.mkIff (x_has_t, encoding))
in (((x_has_t)::[])::[], (ffv)::(xfv)::cvars, _173_619))
in (FStar_SMTEncoding_Term.mkForall _173_620))
in (let _173_622 = (let _173_621 = (FStar_Syntax_Print.term_to_string t0)
in Some (_173_621))
in (_173_623, _173_622, Some ((Prims.strcat "refinement_interpretation_" tsym)))))
in FStar_SMTEncoding_Term.Assume (_173_624))
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

let ttm = (let _173_625 = (FStar_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Term.mk_Term_uvar _173_625))
in (

let _83_803 = (encode_term_pred None k env ttm)
in (match (_83_803) with
| (t_has_k, decls) -> begin
(

let d = (let _173_631 = (let _173_630 = (let _173_629 = (let _173_628 = (let _173_627 = (let _173_626 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _173_626))
in (FStar_Util.format1 "@uvar_typing_%s" _173_627))
in (varops.fresh _173_628))
in Some (_173_629))
in (t_has_k, Some ("Uvar typing"), _173_630))
in FStar_SMTEncoding_Term.Assume (_173_631))
in (ttm, (FStar_List.append decls ((d)::[]))))
end)))
end
| FStar_Syntax_Syntax.Tm_app (_83_806) -> begin
(

let _83_810 = (FStar_Syntax_Util.head_and_args t0)
in (match (_83_810) with
| (head, args_e) -> begin
(match ((let _173_633 = (let _173_632 = (FStar_Syntax_Subst.compress head)
in _173_632.FStar_Syntax_Syntax.n)
in (_173_633, args_e))) with
| (_83_812, _83_814) when (head_redex env head) -> begin
(let _173_634 = (whnf env t)
in (encode_term _173_634 env))
end
| ((FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), (_)::((v1, _))::((v2, _))::[])) | ((FStar_Syntax_Syntax.Tm_fvar (fv), (_)::((v1, _))::((v2, _))::[])) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
(

let _83_854 = (encode_term v1 env)
in (match (_83_854) with
| (v1, decls1) -> begin
(

let _83_857 = (encode_term v2 env)
in (match (_83_857) with
| (v2, decls2) -> begin
(let _173_635 = (FStar_SMTEncoding_Term.mk_LexCons v1 v2)
in (_173_635, (FStar_List.append decls1 decls2)))
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

let ty = (let _173_640 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right _173_640 (FStar_Syntax_Subst.subst subst)))
in (

let _83_889 = (encode_term_pred None ty env app_tm)
in (match (_83_889) with
| (has_type, decls'') -> begin
(

let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (

let e_typing = (let _173_644 = (let _173_643 = (FStar_SMTEncoding_Term.mkForall (((has_type)::[])::[], cvars, has_type))
in (let _173_642 = (let _173_641 = (varops.fresh "@partial_app_typing_")
in Some (_173_641))
in (_173_643, Some ("Partial app typing"), _173_642)))
in FStar_SMTEncoding_Term.Assume (_173_644))
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
(let _173_648 = (let _173_647 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _173_647 Prims.snd))
in Some (_173_648))
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

let head_type = (let _173_649 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine _173_649))
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
in (let _173_652 = (FStar_SMTEncoding_Term.mkFreeV (f, FStar_SMTEncoding_Term.Term_sort))
in (_173_652, (decl)::[]))))
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
(let _173_657 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening _173_657))
end
| FStar_Util.Inr (ef) -> begin
(let _173_659 = (let _173_658 = (FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange [] FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _173_658 Prims.fst))
in (FStar_Syntax_Syntax.mk_Total _173_659))
end))
in (match (lopt) with
| None -> begin
(

let _83_995 = (let _173_661 = (let _173_660 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s" _173_660))
in (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos _173_661))
in (fallback ()))
end
| Some (lc) -> begin
if (let _173_662 = (is_pure_or_ghost lc)
in (FStar_All.pipe_left Prims.op_Negation _173_662)) then begin
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

let key_body = (let _173_666 = (let _173_665 = (let _173_664 = (let _173_663 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_173_663, body))
in (FStar_SMTEncoding_Term.mkImp _173_664))
in ([], vars, _173_665))
in (FStar_SMTEncoding_Term.mkForall _173_666))
in (

let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (

let tkey = (FStar_SMTEncoding_Term.mkForall ([], cvars, key_body))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _83_1015, _83_1017) -> begin
(let _173_669 = (let _173_668 = (let _173_667 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (t, _173_667))
in (FStar_SMTEncoding_Term.mkApp _173_668))
in (_173_669, []))
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

let f = (let _173_671 = (let _173_670 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (fsym, _173_670))
in (FStar_SMTEncoding_Term.mkApp _173_671))
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
in (let _173_673 = (let _173_672 = (FStar_SMTEncoding_Term.mkForall (((f)::[])::[], cvars, f_has_t))
in (_173_672, a_name, a_name))
in FStar_SMTEncoding_Term.Assume (_173_673)))
in (

let interp_f = (

let a_name = Some ((Prims.strcat "interpretation_" fsym))
in (let _173_680 = (let _173_679 = (let _173_678 = (let _173_677 = (let _173_676 = (let _173_675 = (FStar_SMTEncoding_Term.mk_IsTyped app)
in (let _173_674 = (FStar_SMTEncoding_Term.mkEq (app, body))
in (_173_675, _173_674)))
in (FStar_SMTEncoding_Term.mkImp _173_676))
in (((app)::[])::[], (FStar_List.append vars cvars), _173_677))
in (FStar_SMTEncoding_Term.mkForall _173_678))
in (_173_679, a_name, a_name))
in FStar_SMTEncoding_Term.Assume (_173_680)))
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
| FStar_Syntax_Syntax.Tm_let ((_83_1041, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_83_1053); FStar_Syntax_Syntax.lbunivs = _83_1051; FStar_Syntax_Syntax.lbtyp = _83_1049; FStar_Syntax_Syntax.lbeff = _83_1047; FStar_Syntax_Syntax.lbdef = _83_1045})::_83_1043), _83_1059) -> begin
(FStar_All.failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _83_1068; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _83_1065; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (_83_1078) -> begin
(

let _83_1080 = (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (

let e = (varops.fresh "let-rec")
in (

let decl_e = FStar_SMTEncoding_Term.DeclFun ((e, [], FStar_SMTEncoding_Term.Term_sort, None))
in (let _173_681 = (FStar_SMTEncoding_Term.mkFreeV (e, FStar_SMTEncoding_Term.Term_sort))
in (_173_681, (decl_e)::[])))))
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
(let _173_715 = (let _173_714 = (let _173_713 = (let _173_712 = (let _173_711 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Term.mkTrue)
in (w, _173_711))
in (FStar_SMTEncoding_Term.mkEq _173_712))
in (guard, _173_713))
in (FStar_SMTEncoding_Term.mkAnd _173_714))
in (_173_715, decls2))
end))
end)
in (match (_83_1146) with
| (guard, decls2) -> begin
(

let _83_1149 = (encode_br br env)
in (match (_83_1149) with
| (br, decls3) -> begin
(let _173_716 = (FStar_SMTEncoding_Term.mkITE (guard, br, else_case))
in (_173_716, (FStar_List.append (FStar_List.append decls decls2) decls3)))
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
(let _173_719 = (encode_one_pat env pat)
in (_173_719)::[])
end))
and encode_one_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> (

let _83_1161 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _173_722 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" _173_722))
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
(let _173_730 = (let _173_729 = (encode_const c)
in (scrutinee, _173_729))
in (FStar_SMTEncoding_Term.mkEq _173_730))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let is_f = (mk_data_tester env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _83_1204 -> (match (_83_1204) with
| (arg, _83_1203) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _173_733 = (FStar_SMTEncoding_Term.mkApp (proj, (scrutinee)::[]))
in (mk_guard arg _173_733)))
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
(let _173_741 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _83_1231 -> (match (_83_1231) with
| (arg, _83_1230) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _173_740 = (FStar_SMTEncoding_Term.mkApp (proj, (scrutinee)::[]))
in (mk_projections arg _173_740)))
end))))
in (FStar_All.pipe_right _173_741 FStar_List.flatten))
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

let _83_1259 = (let _173_754 = (FStar_Syntax_Util.unmeta e)
in (FStar_Syntax_Util.head_and_args _173_754))
in (match (_83_1259) with
| (head, args) -> begin
(match ((let _173_756 = (let _173_755 = (FStar_Syntax_Util.un_uinst head)
in _173_755.FStar_Syntax_Syntax.n)
in (_173_756, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), _83_1263) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid) -> begin
[]
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_83_1276)::((hd, _83_1273))::((tl, _83_1269))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid) -> begin
(let _173_757 = (list_elements tl)
in (hd)::_173_757)
end
| _83_1280 -> begin
(

let _83_1281 = (FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern")
in [])
end)
end)))
in (

let one_pat = (fun p -> (

let _83_1287 = (let _173_760 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right _173_760 FStar_Syntax_Util.head_and_args))
in (match (_83_1287) with
| (head, args) -> begin
(match ((let _173_762 = (let _173_761 = (FStar_Syntax_Util.un_uinst head)
in _173_761.FStar_Syntax_Syntax.n)
in (_173_762, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((_83_1295, _83_1297))::((e, _83_1292))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpat_lid) -> begin
(e, None)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, _83_1305))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatT_lid) -> begin
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

let _83_1318 = (let _173_767 = (FStar_Syntax_Util.unmeta t)
in (FStar_All.pipe_right _173_767 FStar_Syntax_Util.head_and_args))
in (match (_83_1318) with
| (head, args) -> begin
(match ((let _173_769 = (let _173_768 = (FStar_Syntax_Util.un_uinst head)
in _173_768.FStar_Syntax_Syntax.n)
in (_173_769, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, _83_1323))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatOr_lid) -> begin
Some (e)
end
| _83_1328 -> begin
None
end)
end)))
in (match (elts) with
| (t)::[] -> begin
(match ((smt_pat_or t)) with
| Some (e) -> begin
(let _173_772 = (list_elements e)
in (FStar_All.pipe_right _173_772 (FStar_List.map (fun branch -> (let _173_771 = (list_elements branch)
in (FStar_All.pipe_right _173_771 (FStar_List.map one_pat)))))))
end
| _83_1335 -> begin
(let _173_773 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_173_773)::[])
end)
end
| _83_1337 -> begin
(let _173_774 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_173_774)::[])
end))))
in (

let _83_1371 = (match ((let _173_775 = (FStar_Syntax_Subst.compress t)
in _173_775.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _83_1344 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_83_1344) with
| (binders, c) -> begin
(

let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| ((pre, _83_1356))::((post, _83_1352))::((pats, _83_1348))::[] -> begin
(

let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _173_776 = (lemma_pats pats')
in (binders, pre, post, _173_776)))
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

let _83_1391 = (let _173_780 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (

let _83_1388 = (let _173_779 = (FStar_All.pipe_right branch (FStar_List.map (fun _83_1383 -> (match (_83_1383) with
| (t, _83_1382) -> begin
(encode_term t (

let _83_1384 = env
in {bindings = _83_1384.bindings; depth = _83_1384.depth; tcenv = _83_1384.tcenv; warn = _83_1384.warn; cache = _83_1384.cache; nolabels = _83_1384.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _83_1384.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _173_779 FStar_List.unzip))
in (match (_83_1388) with
| (pats, decls) -> begin
(pats, decls)
end)))))
in (FStar_All.pipe_right _173_780 FStar_List.unzip))
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
| (l)::[] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _173_783 = (let _173_782 = (FStar_SMTEncoding_Term.mkFreeV l)
in (FStar_SMTEncoding_Term.mk_Precedes _173_782 e))
in (_173_783)::p))))
end
| _83_1401 -> begin
(

let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _173_789 = (FStar_SMTEncoding_Term.mk_Precedes tl e)
in (_173_789)::p))))
end
| ((x, FStar_SMTEncoding_Term.Term_sort))::vars -> begin
(let _173_791 = (let _173_790 = (FStar_SMTEncoding_Term.mkFreeV (x, FStar_SMTEncoding_Term.Term_sort))
in (FStar_SMTEncoding_Term.mk_LexCons _173_790 tl))
in (aux _173_791 vars))
end
| _83_1413 -> begin
pats
end))
in (let _173_792 = (FStar_SMTEncoding_Term.mkFreeV ("Prims.LexTop", FStar_SMTEncoding_Term.Term_sort))
in (aux _173_792 vars)))
end)
end)
in (

let env = (

let _83_1415 = env
in {bindings = _83_1415.bindings; depth = _83_1415.depth; tcenv = _83_1415.tcenv; warn = _83_1415.warn; cache = _83_1415.cache; nolabels = true; use_zfuel_name = _83_1415.use_zfuel_name; encode_non_total_function_typ = _83_1415.encode_non_total_function_typ})
in (

let _83_1420 = (let _173_793 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula _173_793 env))
in (match (_83_1420) with
| (pre, decls'') -> begin
(

let _83_1423 = (let _173_794 = (FStar_Syntax_Util.unmeta post)
in (encode_formula _173_794 env))
in (match (_83_1423) with
| (post, decls''') -> begin
(

let decls = (FStar_List.append (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'') decls''')
in (let _173_799 = (let _173_798 = (let _173_797 = (let _173_796 = (let _173_795 = (FStar_SMTEncoding_Term.mk_and_l ((pre)::guards))
in (_173_795, post))
in (FStar_SMTEncoding_Term.mkImp _173_796))
in (pats, vars, _173_797))
in (FStar_SMTEncoding_Term.mkForall _173_798))
in (_173_799, decls)))
end))
end)))))
end))
end))
end))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (

let debug = (fun phi -> if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _173_805 = (FStar_Syntax_Print.tag_of_term phi)
in (let _173_804 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print2 "Formula (%s)  %s\n" _173_805 _173_804)))
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
(let _173_821 = (f args)
in (_173_821, decls))
end)))
in (

let const_op = (fun f _83_1442 -> (f, []))
in (

let un_op = (fun f l -> (let _173_835 = (FStar_List.hd l)
in (FStar_All.pipe_left f _173_835)))
in (

let bin_op = (fun f _83_9 -> (match (_83_9) with
| (t1)::(t2)::[] -> begin
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
(let _173_860 = (f phis)
in (_173_860, decls))
end)))
in (

let eq_op = (fun _83_10 -> (match (_83_10) with
| (_83_1475)::(_83_1473)::(e1)::(e2)::[] -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) l)
end))
in (

let mk_imp = (fun _83_11 -> (match (_83_11) with
| ((lhs, _83_1486))::((rhs, _83_1482))::[] -> begin
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
(let _173_865 = (FStar_SMTEncoding_Term.mkImp (l2, l1))
in (_173_865, (FStar_List.append decls1 decls2)))
end))
end)
end))
end
| _83_1503 -> begin
(FStar_All.failwith "impossible")
end))
in (

let mk_ite = (fun _83_12 -> (match (_83_12) with
| ((guard, _83_1516))::((_then, _83_1512))::((_else, _83_1508))::[] -> begin
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

let unboxInt_l = (fun f l -> (let _173_877 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f _173_877)))
in (

let connectives = (let _173_930 = (let _173_886 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkAnd))
in (FStar_Syntax_Const.and_lid, _173_886))
in (let _173_929 = (let _173_928 = (let _173_892 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkOr))
in (FStar_Syntax_Const.or_lid, _173_892))
in (let _173_927 = (let _173_926 = (let _173_925 = (let _173_901 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkIff))
in (FStar_Syntax_Const.iff_lid, _173_901))
in (let _173_924 = (let _173_923 = (let _173_922 = (let _173_910 = (FStar_All.pipe_left enc_prop_c (un_op FStar_SMTEncoding_Term.mkNot))
in (FStar_Syntax_Const.not_lid, _173_910))
in (_173_922)::((FStar_Syntax_Const.eq2_lid, eq_op))::((FStar_Syntax_Const.true_lid, (const_op FStar_SMTEncoding_Term.mkTrue)))::((FStar_Syntax_Const.false_lid, (const_op FStar_SMTEncoding_Term.mkFalse)))::[])
in ((FStar_Syntax_Const.ite_lid, mk_ite))::_173_923)
in (_173_925)::_173_924))
in ((FStar_Syntax_Const.imp_lid, mk_imp))::_173_926)
in (_173_928)::_173_927))
in (_173_930)::_173_929))
in (

let rec fallback = (fun phi -> (match (phi.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(

let _83_1548 = (encode_formula phi' env)
in (match (_83_1548) with
| (phi, decls) -> begin
(let _173_933 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled ((phi, msg, r))))
in (_173_933, decls))
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
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _83_1562; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _83_1559; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
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
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_83_1590)::((x, _83_1587))::((t, _83_1583))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.has_type_lid) -> begin
(

let _83_1595 = (encode_term x env)
in (match (_83_1595) with
| (x, decls) -> begin
(

let _83_1598 = (encode_term t env)
in (match (_83_1598) with
| (t, decls') -> begin
(let _173_934 = (FStar_SMTEncoding_Term.mk_HasType x t)
in (_173_934, (FStar_List.append decls decls')))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((r, _83_1611))::((msg, _83_1607))::((phi, _83_1603))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.labeled_lid) -> begin
(match ((let _173_938 = (let _173_935 = (FStar_Syntax_Subst.compress r)
in _173_935.FStar_Syntax_Syntax.n)
in (let _173_937 = (let _173_936 = (FStar_Syntax_Subst.compress msg)
in _173_936.FStar_Syntax_Syntax.n)
in (_173_938, _173_937)))) with
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
(let _173_939 = (whnf env phi)
in (encode_formula _173_939 env))
end
| _83_1631 -> begin
(

let _83_1634 = (encode_term phi env)
in (match (_83_1634) with
| (tt, decls) -> begin
(let _173_940 = (FStar_SMTEncoding_Term.mk_Valid tt)
in (_173_940, decls))
end))
end))
end
| _83_1636 -> begin
(

let _83_1639 = (encode_term phi env)
in (match (_83_1639) with
| (tt, decls) -> begin
(let _173_941 = (FStar_SMTEncoding_Term.mk_Valid tt)
in (_173_941, decls))
end))
end))
in (

let encode_q_body = (fun env bs ps body -> (

let _83_1651 = (encode_binders None bs env)
in (match (_83_1651) with
| (vars, guards, env, decls, _83_1650) -> begin
(

let _83_1664 = (let _173_953 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let _83_1661 = (let _173_952 = (FStar_All.pipe_right p (FStar_List.map (fun _83_1656 -> (match (_83_1656) with
| (t, _83_1655) -> begin
(encode_term t (

let _83_1657 = env
in {bindings = _83_1657.bindings; depth = _83_1657.depth; tcenv = _83_1657.tcenv; warn = _83_1657.warn; cache = _83_1657.cache; nolabels = _83_1657.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _83_1657.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _173_952 FStar_List.unzip))
in (match (_83_1661) with
| (p, decls) -> begin
(p, (FStar_List.flatten decls))
end)))))
in (FStar_All.pipe_right _173_953 FStar_List.unzip))
in (match (_83_1664) with
| (pats, decls') -> begin
(

let _83_1667 = (encode_formula body env)
in (match (_83_1667) with
| (body, decls'') -> begin
(

let guards = (match (pats) with
| (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.hash = _83_1671; FStar_SMTEncoding_Term.freevars = _83_1669})::[])::[] -> begin
[]
end
| _83_1682 -> begin
guards
end)
in (let _173_954 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (vars, pats, _173_954, body, (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls''))))
end))
end))
end)))
in (

let _83_1684 = (debug phi)
in (

let phi = (FStar_Syntax_Util.unascribe phi)
in (match ((FStar_Syntax_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _83_1696 -> (match (_83_1696) with
| (l, _83_1695) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_83_1699, f) -> begin
(f arms)
end)
end
| Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
(

let _83_1709 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _173_971 = (FStar_All.pipe_right vars (FStar_Syntax_Print.binders_to_string "; "))
in (FStar_Util.print1 ">>>> Got QALL [%s]\n" _173_971))
end else begin
()
end
in (

let _83_1716 = (encode_q_body env vars pats body)
in (match (_83_1716) with
| (vars, pats, guard, body, decls) -> begin
(

let tm = (let _173_973 = (let _173_972 = (FStar_SMTEncoding_Term.mkImp (guard, body))
in (pats, vars, _173_972))
in (FStar_SMTEncoding_Term.mkForall _173_973))
in (

let _83_1718 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _173_974 = (FStar_SMTEncoding_Term.termToSmt tm)
in (FStar_Util.print1 ">>>> Encoded QALL to %s\n" _173_974))
end else begin
()
end
in (tm, decls)))
end)))
end
| Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
(

let _83_1731 = (encode_q_body env vars pats body)
in (match (_83_1731) with
| (vars, pats, guard, body, decls) -> begin
(let _173_977 = (let _173_976 = (let _173_975 = (FStar_SMTEncoding_Term.mkAnd (guard, body))
in (pats, vars, _173_975))
in (FStar_SMTEncoding_Term.mkExists _173_976))
in (_173_977, decls))
end))
end)))))))))))))))))


type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.decl Prims.list; is : FStar_Ident.lident  ->  Prims.bool}


let is_Mkprims_t : prims_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkprims_t"))))


let prims : prims_t = (

let _83_1737 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (_83_1737) with
| (asym, a) -> begin
(

let _83_1740 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_83_1740) with
| (xsym, x) -> begin
(

let _83_1743 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (_83_1743) with
| (ysym, y) -> begin
(

let deffun = (fun vars body x -> (FStar_SMTEncoding_Term.DefineFun ((x, vars, FStar_SMTEncoding_Term.Term_sort, body, None)))::[])
in (

let quant = (fun vars body x -> (

let t1 = (let _173_1020 = (let _173_1019 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (x, _173_1019))
in (FStar_SMTEncoding_Term.mkApp _173_1020))
in (

let vname_decl = (let _173_1022 = (let _173_1021 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (x, _173_1021, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_173_1022))
in (let _173_1028 = (let _173_1027 = (let _173_1026 = (let _173_1025 = (let _173_1024 = (let _173_1023 = (FStar_SMTEncoding_Term.mkEq (t1, body))
in (((t1)::[])::[], vars, _173_1023))
in (FStar_SMTEncoding_Term.mkForall _173_1024))
in (_173_1025, None, Some ((Prims.strcat "primitive_" x))))
in FStar_SMTEncoding_Term.Assume (_173_1026))
in (_173_1027)::[])
in (vname_decl)::_173_1028))))
in (

let axy = ((asym, FStar_SMTEncoding_Term.Term_sort))::((xsym, FStar_SMTEncoding_Term.Term_sort))::((ysym, FStar_SMTEncoding_Term.Term_sort))::[]
in (

let xy = ((xsym, FStar_SMTEncoding_Term.Term_sort))::((ysym, FStar_SMTEncoding_Term.Term_sort))::[]
in (

let qx = ((xsym, FStar_SMTEncoding_Term.Term_sort))::[]
in (

let prims = (let _173_1188 = (let _173_1037 = (let _173_1036 = (let _173_1035 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _173_1035))
in (quant axy _173_1036))
in (FStar_Syntax_Const.op_Eq, _173_1037))
in (let _173_1187 = (let _173_1186 = (let _173_1044 = (let _173_1043 = (let _173_1042 = (let _173_1041 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (FStar_SMTEncoding_Term.mkNot _173_1041))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _173_1042))
in (quant axy _173_1043))
in (FStar_Syntax_Const.op_notEq, _173_1044))
in (let _173_1185 = (let _173_1184 = (let _173_1053 = (let _173_1052 = (let _173_1051 = (let _173_1050 = (let _173_1049 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _173_1048 = (FStar_SMTEncoding_Term.unboxInt y)
in (_173_1049, _173_1048)))
in (FStar_SMTEncoding_Term.mkLT _173_1050))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _173_1051))
in (quant xy _173_1052))
in (FStar_Syntax_Const.op_LT, _173_1053))
in (let _173_1183 = (let _173_1182 = (let _173_1062 = (let _173_1061 = (let _173_1060 = (let _173_1059 = (let _173_1058 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _173_1057 = (FStar_SMTEncoding_Term.unboxInt y)
in (_173_1058, _173_1057)))
in (FStar_SMTEncoding_Term.mkLTE _173_1059))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _173_1060))
in (quant xy _173_1061))
in (FStar_Syntax_Const.op_LTE, _173_1062))
in (let _173_1181 = (let _173_1180 = (let _173_1071 = (let _173_1070 = (let _173_1069 = (let _173_1068 = (let _173_1067 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _173_1066 = (FStar_SMTEncoding_Term.unboxInt y)
in (_173_1067, _173_1066)))
in (FStar_SMTEncoding_Term.mkGT _173_1068))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _173_1069))
in (quant xy _173_1070))
in (FStar_Syntax_Const.op_GT, _173_1071))
in (let _173_1179 = (let _173_1178 = (let _173_1080 = (let _173_1079 = (let _173_1078 = (let _173_1077 = (let _173_1076 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _173_1075 = (FStar_SMTEncoding_Term.unboxInt y)
in (_173_1076, _173_1075)))
in (FStar_SMTEncoding_Term.mkGTE _173_1077))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _173_1078))
in (quant xy _173_1079))
in (FStar_Syntax_Const.op_GTE, _173_1080))
in (let _173_1177 = (let _173_1176 = (let _173_1089 = (let _173_1088 = (let _173_1087 = (let _173_1086 = (let _173_1085 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _173_1084 = (FStar_SMTEncoding_Term.unboxInt y)
in (_173_1085, _173_1084)))
in (FStar_SMTEncoding_Term.mkSub _173_1086))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _173_1087))
in (quant xy _173_1088))
in (FStar_Syntax_Const.op_Subtraction, _173_1089))
in (let _173_1175 = (let _173_1174 = (let _173_1096 = (let _173_1095 = (let _173_1094 = (let _173_1093 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Term.mkMinus _173_1093))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _173_1094))
in (quant qx _173_1095))
in (FStar_Syntax_Const.op_Minus, _173_1096))
in (let _173_1173 = (let _173_1172 = (let _173_1105 = (let _173_1104 = (let _173_1103 = (let _173_1102 = (let _173_1101 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _173_1100 = (FStar_SMTEncoding_Term.unboxInt y)
in (_173_1101, _173_1100)))
in (FStar_SMTEncoding_Term.mkAdd _173_1102))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _173_1103))
in (quant xy _173_1104))
in (FStar_Syntax_Const.op_Addition, _173_1105))
in (let _173_1171 = (let _173_1170 = (let _173_1114 = (let _173_1113 = (let _173_1112 = (let _173_1111 = (let _173_1110 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _173_1109 = (FStar_SMTEncoding_Term.unboxInt y)
in (_173_1110, _173_1109)))
in (FStar_SMTEncoding_Term.mkMul _173_1111))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _173_1112))
in (quant xy _173_1113))
in (FStar_Syntax_Const.op_Multiply, _173_1114))
in (let _173_1169 = (let _173_1168 = (let _173_1123 = (let _173_1122 = (let _173_1121 = (let _173_1120 = (let _173_1119 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _173_1118 = (FStar_SMTEncoding_Term.unboxInt y)
in (_173_1119, _173_1118)))
in (FStar_SMTEncoding_Term.mkDiv _173_1120))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _173_1121))
in (quant xy _173_1122))
in (FStar_Syntax_Const.op_Division, _173_1123))
in (let _173_1167 = (let _173_1166 = (let _173_1132 = (let _173_1131 = (let _173_1130 = (let _173_1129 = (let _173_1128 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _173_1127 = (FStar_SMTEncoding_Term.unboxInt y)
in (_173_1128, _173_1127)))
in (FStar_SMTEncoding_Term.mkMod _173_1129))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _173_1130))
in (quant xy _173_1131))
in (FStar_Syntax_Const.op_Modulus, _173_1132))
in (let _173_1165 = (let _173_1164 = (let _173_1141 = (let _173_1140 = (let _173_1139 = (let _173_1138 = (let _173_1137 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _173_1136 = (FStar_SMTEncoding_Term.unboxBool y)
in (_173_1137, _173_1136)))
in (FStar_SMTEncoding_Term.mkAnd _173_1138))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _173_1139))
in (quant xy _173_1140))
in (FStar_Syntax_Const.op_And, _173_1141))
in (let _173_1163 = (let _173_1162 = (let _173_1150 = (let _173_1149 = (let _173_1148 = (let _173_1147 = (let _173_1146 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _173_1145 = (FStar_SMTEncoding_Term.unboxBool y)
in (_173_1146, _173_1145)))
in (FStar_SMTEncoding_Term.mkOr _173_1147))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _173_1148))
in (quant xy _173_1149))
in (FStar_Syntax_Const.op_Or, _173_1150))
in (let _173_1161 = (let _173_1160 = (let _173_1157 = (let _173_1156 = (let _173_1155 = (let _173_1154 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Term.mkNot _173_1154))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _173_1155))
in (quant qx _173_1156))
in (FStar_Syntax_Const.op_Negation, _173_1157))
in (_173_1160)::[])
in (_173_1162)::_173_1161))
in (_173_1164)::_173_1163))
in (_173_1166)::_173_1165))
in (_173_1168)::_173_1167))
in (_173_1170)::_173_1169))
in (_173_1172)::_173_1171))
in (_173_1174)::_173_1173))
in (_173_1176)::_173_1175))
in (_173_1178)::_173_1177))
in (_173_1180)::_173_1179))
in (_173_1182)::_173_1181))
in (_173_1184)::_173_1183))
in (_173_1186)::_173_1185))
in (_173_1188)::_173_1187))
in (

let mk = (fun l v -> (let _173_1220 = (FStar_All.pipe_right prims (FStar_List.filter (fun _83_1763 -> (match (_83_1763) with
| (l', _83_1762) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right _173_1220 (FStar_List.collect (fun _83_1767 -> (match (_83_1767) with
| (_83_1765, b) -> begin
(b v)
end))))))
in (

let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _83_1773 -> (match (_83_1773) with
| (l', _83_1772) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is}))))))))
end))
end))
end))


let pretype_axiom : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun tapp vars -> (

let _83_1779 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_83_1779) with
| (xxsym, xx) -> begin
(

let _83_1782 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_83_1782) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (let _173_1248 = (let _173_1247 = (let _173_1244 = (let _173_1243 = (let _173_1242 = (let _173_1241 = (let _173_1240 = (let _173_1239 = (FStar_SMTEncoding_Term.mkApp ("PreType", (xx)::[]))
in (tapp, _173_1239))
in (FStar_SMTEncoding_Term.mkEq _173_1240))
in (xx_has_type, _173_1241))
in (FStar_SMTEncoding_Term.mkImp _173_1242))
in (((xx_has_type)::[])::[], ((xxsym, FStar_SMTEncoding_Term.Term_sort))::((ffsym, FStar_SMTEncoding_Term.Fuel_sort))::vars, _173_1243))
in (FStar_SMTEncoding_Term.mkForall _173_1244))
in (let _173_1246 = (let _173_1245 = (varops.fresh "@pretyping_")
in Some (_173_1245))
in (_173_1247, Some ("pretyping"), _173_1246)))
in FStar_SMTEncoding_Term.Assume (_173_1248)))
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
in (let _173_1269 = (let _173_1260 = (let _173_1259 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in (_173_1259, Some ("unit typing"), Some ("unit_typing")))
in FStar_SMTEncoding_Term.Assume (_173_1260))
in (let _173_1268 = (let _173_1267 = (let _173_1266 = (let _173_1265 = (let _173_1264 = (let _173_1263 = (let _173_1262 = (let _173_1261 = (FStar_SMTEncoding_Term.mkEq (x, FStar_SMTEncoding_Term.mk_Term_unit))
in (typing_pred, _173_1261))
in (FStar_SMTEncoding_Term.mkImp _173_1262))
in (((typing_pred)::[])::[], (xx)::[], _173_1263))
in (mkForall_fuel _173_1264))
in (_173_1265, Some ("unit inversion"), Some ("unit_inversion")))
in FStar_SMTEncoding_Term.Assume (_173_1266))
in (_173_1267)::[])
in (_173_1269)::_173_1268))))
in (

let mk_bool = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _173_1292 = (let _173_1283 = (let _173_1282 = (let _173_1281 = (let _173_1280 = (let _173_1277 = (let _173_1276 = (FStar_SMTEncoding_Term.boxBool b)
in (_173_1276)::[])
in (_173_1277)::[])
in (let _173_1279 = (let _173_1278 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType _173_1278 tt))
in (_173_1280, (bb)::[], _173_1279)))
in (FStar_SMTEncoding_Term.mkForall _173_1281))
in (_173_1282, Some ("bool typing"), Some ("bool_typing")))
in FStar_SMTEncoding_Term.Assume (_173_1283))
in (let _173_1291 = (let _173_1290 = (let _173_1289 = (let _173_1288 = (let _173_1287 = (let _173_1286 = (let _173_1285 = (let _173_1284 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in (typing_pred, _173_1284))
in (FStar_SMTEncoding_Term.mkImp _173_1285))
in (((typing_pred)::[])::[], (xx)::[], _173_1286))
in (mkForall_fuel _173_1287))
in (_173_1288, Some ("bool inversion"), Some ("bool_inversion")))
in FStar_SMTEncoding_Term.Assume (_173_1289))
in (_173_1290)::[])
in (_173_1292)::_173_1291))))))
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

let precedes = (let _173_1306 = (let _173_1305 = (let _173_1304 = (let _173_1303 = (let _173_1302 = (let _173_1301 = (FStar_SMTEncoding_Term.boxInt a)
in (let _173_1300 = (let _173_1299 = (FStar_SMTEncoding_Term.boxInt b)
in (_173_1299)::[])
in (_173_1301)::_173_1300))
in (tt)::_173_1302)
in (tt)::_173_1303)
in ("Prims.Precedes", _173_1304))
in (FStar_SMTEncoding_Term.mkApp _173_1305))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _173_1306))
in (

let precedes_y_x = (let _173_1307 = (FStar_SMTEncoding_Term.mkApp ("Precedes", (y)::(x)::[]))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _173_1307))
in (let _173_1349 = (let _173_1315 = (let _173_1314 = (let _173_1313 = (let _173_1312 = (let _173_1309 = (let _173_1308 = (FStar_SMTEncoding_Term.boxInt b)
in (_173_1308)::[])
in (_173_1309)::[])
in (let _173_1311 = (let _173_1310 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType _173_1310 tt))
in (_173_1312, (bb)::[], _173_1311)))
in (FStar_SMTEncoding_Term.mkForall _173_1313))
in (_173_1314, Some ("int typing"), Some ("int_typing")))
in FStar_SMTEncoding_Term.Assume (_173_1315))
in (let _173_1348 = (let _173_1347 = (let _173_1321 = (let _173_1320 = (let _173_1319 = (let _173_1318 = (let _173_1317 = (let _173_1316 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in (typing_pred, _173_1316))
in (FStar_SMTEncoding_Term.mkImp _173_1317))
in (((typing_pred)::[])::[], (xx)::[], _173_1318))
in (mkForall_fuel _173_1319))
in (_173_1320, Some ("int inversion"), Some ("int_inversion")))
in FStar_SMTEncoding_Term.Assume (_173_1321))
in (let _173_1346 = (let _173_1345 = (let _173_1344 = (let _173_1343 = (let _173_1342 = (let _173_1341 = (let _173_1340 = (let _173_1339 = (let _173_1338 = (let _173_1337 = (let _173_1336 = (let _173_1335 = (let _173_1324 = (let _173_1323 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _173_1322 = (FStar_SMTEncoding_Term.mkInteger' 0)
in (_173_1323, _173_1322)))
in (FStar_SMTEncoding_Term.mkGT _173_1324))
in (let _173_1334 = (let _173_1333 = (let _173_1327 = (let _173_1326 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _173_1325 = (FStar_SMTEncoding_Term.mkInteger' 0)
in (_173_1326, _173_1325)))
in (FStar_SMTEncoding_Term.mkGTE _173_1327))
in (let _173_1332 = (let _173_1331 = (let _173_1330 = (let _173_1329 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _173_1328 = (FStar_SMTEncoding_Term.unboxInt x)
in (_173_1329, _173_1328)))
in (FStar_SMTEncoding_Term.mkLT _173_1330))
in (_173_1331)::[])
in (_173_1333)::_173_1332))
in (_173_1335)::_173_1334))
in (typing_pred_y)::_173_1336)
in (typing_pred)::_173_1337)
in (FStar_SMTEncoding_Term.mk_and_l _173_1338))
in (_173_1339, precedes_y_x))
in (FStar_SMTEncoding_Term.mkImp _173_1340))
in (((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[], (xx)::(yy)::[], _173_1341))
in (mkForall_fuel _173_1342))
in (_173_1343, Some ("well-founded ordering on nat (alt)"), Some ("well-founded-ordering-on-nat")))
in FStar_SMTEncoding_Term.Assume (_173_1344))
in (_173_1345)::[])
in (_173_1347)::_173_1346))
in (_173_1349)::_173_1348)))))))))))
in (

let mk_str = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = ("b", FStar_SMTEncoding_Term.String_sort)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _173_1372 = (let _173_1363 = (let _173_1362 = (let _173_1361 = (let _173_1360 = (let _173_1357 = (let _173_1356 = (FStar_SMTEncoding_Term.boxString b)
in (_173_1356)::[])
in (_173_1357)::[])
in (let _173_1359 = (let _173_1358 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType _173_1358 tt))
in (_173_1360, (bb)::[], _173_1359)))
in (FStar_SMTEncoding_Term.mkForall _173_1361))
in (_173_1362, Some ("string typing"), Some ("string_typing")))
in FStar_SMTEncoding_Term.Assume (_173_1363))
in (let _173_1371 = (let _173_1370 = (let _173_1369 = (let _173_1368 = (let _173_1367 = (let _173_1366 = (let _173_1365 = (let _173_1364 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in (typing_pred, _173_1364))
in (FStar_SMTEncoding_Term.mkImp _173_1365))
in (((typing_pred)::[])::[], (xx)::[], _173_1366))
in (mkForall_fuel _173_1367))
in (_173_1368, Some ("string inversion"), Some ("string_inversion")))
in FStar_SMTEncoding_Term.Assume (_173_1369))
in (_173_1370)::[])
in (_173_1372)::_173_1371))))))
in (

let mk_ref = (fun env reft_name _83_1821 -> (

let r = ("r", FStar_SMTEncoding_Term.Ref_sort)
in (

let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (

let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (

let refa = (let _173_1381 = (let _173_1380 = (let _173_1379 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (_173_1379)::[])
in (reft_name, _173_1380))
in (FStar_SMTEncoding_Term.mkApp _173_1381))
in (

let refb = (let _173_1384 = (let _173_1383 = (let _173_1382 = (FStar_SMTEncoding_Term.mkFreeV bb)
in (_173_1382)::[])
in (reft_name, _173_1383))
in (FStar_SMTEncoding_Term.mkApp _173_1384))
in (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (

let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (let _173_1403 = (let _173_1390 = (let _173_1389 = (let _173_1388 = (let _173_1387 = (let _173_1386 = (let _173_1385 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in (typing_pred, _173_1385))
in (FStar_SMTEncoding_Term.mkImp _173_1386))
in (((typing_pred)::[])::[], (xx)::(aa)::[], _173_1387))
in (mkForall_fuel _173_1388))
in (_173_1389, Some ("ref inversion"), Some ("ref_inversion")))
in FStar_SMTEncoding_Term.Assume (_173_1390))
in (let _173_1402 = (let _173_1401 = (let _173_1400 = (let _173_1399 = (let _173_1398 = (let _173_1397 = (let _173_1396 = (let _173_1395 = (FStar_SMTEncoding_Term.mkAnd (typing_pred, typing_pred_b))
in (let _173_1394 = (let _173_1393 = (let _173_1392 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (let _173_1391 = (FStar_SMTEncoding_Term.mkFreeV bb)
in (_173_1392, _173_1391)))
in (FStar_SMTEncoding_Term.mkEq _173_1393))
in (_173_1395, _173_1394)))
in (FStar_SMTEncoding_Term.mkImp _173_1396))
in (((typing_pred)::(typing_pred_b)::[])::[], (xx)::(aa)::(bb)::[], _173_1397))
in (mkForall_fuel' 2 _173_1398))
in (_173_1399, Some ("ref typing is injective"), Some ("ref_injectivity")))
in FStar_SMTEncoding_Term.Assume (_173_1400))
in (_173_1401)::[])
in (_173_1403)::_173_1402))))))))))
in (

let mk_false_interp = (fun env nm false_tm -> (

let valid = (FStar_SMTEncoding_Term.mkApp ("Valid", (false_tm)::[]))
in (let _173_1412 = (let _173_1411 = (let _173_1410 = (FStar_SMTEncoding_Term.mkIff (FStar_SMTEncoding_Term.mkFalse, valid))
in (_173_1410, Some ("False interpretation"), Some ("false_interp")))
in FStar_SMTEncoding_Term.Assume (_173_1411))
in (_173_1412)::[])))
in (

let mk_and_interp = (fun env conj _83_1838 -> (

let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (

let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (

let valid = (let _173_1421 = (let _173_1420 = (let _173_1419 = (FStar_SMTEncoding_Term.mkApp (conj, (a)::(b)::[]))
in (_173_1419)::[])
in ("Valid", _173_1420))
in (FStar_SMTEncoding_Term.mkApp _173_1421))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _173_1428 = (let _173_1427 = (let _173_1426 = (let _173_1425 = (let _173_1424 = (let _173_1423 = (let _173_1422 = (FStar_SMTEncoding_Term.mkAnd (valid_a, valid_b))
in (_173_1422, valid))
in (FStar_SMTEncoding_Term.mkIff _173_1423))
in (((valid)::[])::[], (aa)::(bb)::[], _173_1424))
in (FStar_SMTEncoding_Term.mkForall _173_1425))
in (_173_1426, Some ("/\\ interpretation"), Some ("l_and-interp")))
in FStar_SMTEncoding_Term.Assume (_173_1427))
in (_173_1428)::[])))))))))
in (

let mk_or_interp = (fun env disj _83_1850 -> (

let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (

let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (

let valid = (let _173_1437 = (let _173_1436 = (let _173_1435 = (FStar_SMTEncoding_Term.mkApp (disj, (a)::(b)::[]))
in (_173_1435)::[])
in ("Valid", _173_1436))
in (FStar_SMTEncoding_Term.mkApp _173_1437))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _173_1444 = (let _173_1443 = (let _173_1442 = (let _173_1441 = (let _173_1440 = (let _173_1439 = (let _173_1438 = (FStar_SMTEncoding_Term.mkOr (valid_a, valid_b))
in (_173_1438, valid))
in (FStar_SMTEncoding_Term.mkIff _173_1439))
in (((valid)::[])::[], (aa)::(bb)::[], _173_1440))
in (FStar_SMTEncoding_Term.mkForall _173_1441))
in (_173_1442, Some ("\\/ interpretation"), Some ("l_or-interp")))
in FStar_SMTEncoding_Term.Assume (_173_1443))
in (_173_1444)::[])))))))))
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

let valid = (let _173_1453 = (let _173_1452 = (let _173_1451 = (FStar_SMTEncoding_Term.mkApp (eq2, (a)::(b)::(x)::(y)::[]))
in (_173_1451)::[])
in ("Valid", _173_1452))
in (FStar_SMTEncoding_Term.mkApp _173_1453))
in (let _173_1460 = (let _173_1459 = (let _173_1458 = (let _173_1457 = (let _173_1456 = (let _173_1455 = (let _173_1454 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (_173_1454, valid))
in (FStar_SMTEncoding_Term.mkIff _173_1455))
in (((valid)::[])::[], (aa)::(bb)::(xx)::(yy)::[], _173_1456))
in (FStar_SMTEncoding_Term.mkForall _173_1457))
in (_173_1458, Some ("Eq2 interpretation"), Some ("eq2-interp")))
in FStar_SMTEncoding_Term.Assume (_173_1459))
in (_173_1460)::[])))))))))))
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

let valid = (let _173_1469 = (let _173_1468 = (let _173_1467 = (FStar_SMTEncoding_Term.mkApp (imp, (a)::(b)::[]))
in (_173_1467)::[])
in ("Valid", _173_1468))
in (FStar_SMTEncoding_Term.mkApp _173_1469))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _173_1476 = (let _173_1475 = (let _173_1474 = (let _173_1473 = (let _173_1472 = (let _173_1471 = (let _173_1470 = (FStar_SMTEncoding_Term.mkImp (valid_a, valid_b))
in (_173_1470, valid))
in (FStar_SMTEncoding_Term.mkIff _173_1471))
in (((valid)::[])::[], (aa)::(bb)::[], _173_1472))
in (FStar_SMTEncoding_Term.mkForall _173_1473))
in (_173_1474, Some ("==> interpretation"), Some ("l_imp-interp")))
in FStar_SMTEncoding_Term.Assume (_173_1475))
in (_173_1476)::[])))))))))
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

let valid = (let _173_1485 = (let _173_1484 = (let _173_1483 = (FStar_SMTEncoding_Term.mkApp (iff, (a)::(b)::[]))
in (_173_1483)::[])
in ("Valid", _173_1484))
in (FStar_SMTEncoding_Term.mkApp _173_1485))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _173_1492 = (let _173_1491 = (let _173_1490 = (let _173_1489 = (let _173_1488 = (let _173_1487 = (let _173_1486 = (FStar_SMTEncoding_Term.mkIff (valid_a, valid_b))
in (_173_1486, valid))
in (FStar_SMTEncoding_Term.mkIff _173_1487))
in (((valid)::[])::[], (aa)::(bb)::[], _173_1488))
in (FStar_SMTEncoding_Term.mkForall _173_1489))
in (_173_1490, Some ("<==> interpretation"), Some ("l_iff-interp")))
in FStar_SMTEncoding_Term.Assume (_173_1491))
in (_173_1492)::[])))))))))
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

let valid = (let _173_1501 = (let _173_1500 = (let _173_1499 = (FStar_SMTEncoding_Term.mkApp (for_all, (a)::(b)::[]))
in (_173_1499)::[])
in ("Valid", _173_1500))
in (FStar_SMTEncoding_Term.mkApp _173_1501))
in (

let valid_b_x = (let _173_1504 = (let _173_1503 = (let _173_1502 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_173_1502)::[])
in ("Valid", _173_1503))
in (FStar_SMTEncoding_Term.mkApp _173_1504))
in (let _173_1518 = (let _173_1517 = (let _173_1516 = (let _173_1515 = (let _173_1514 = (let _173_1513 = (let _173_1512 = (let _173_1511 = (let _173_1510 = (let _173_1506 = (let _173_1505 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_173_1505)::[])
in (_173_1506)::[])
in (let _173_1509 = (let _173_1508 = (let _173_1507 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_173_1507, valid_b_x))
in (FStar_SMTEncoding_Term.mkImp _173_1508))
in (_173_1510, (xx)::[], _173_1509)))
in (FStar_SMTEncoding_Term.mkForall _173_1511))
in (_173_1512, valid))
in (FStar_SMTEncoding_Term.mkIff _173_1513))
in (((valid)::[])::[], (aa)::(bb)::[], _173_1514))
in (FStar_SMTEncoding_Term.mkForall _173_1515))
in (_173_1516, Some ("forall interpretation"), Some ("forall-interp")))
in FStar_SMTEncoding_Term.Assume (_173_1517))
in (_173_1518)::[]))))))))))
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

let valid = (let _173_1527 = (let _173_1526 = (let _173_1525 = (FStar_SMTEncoding_Term.mkApp (for_some, (a)::(b)::[]))
in (_173_1525)::[])
in ("Valid", _173_1526))
in (FStar_SMTEncoding_Term.mkApp _173_1527))
in (

let valid_b_x = (let _173_1530 = (let _173_1529 = (let _173_1528 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_173_1528)::[])
in ("Valid", _173_1529))
in (FStar_SMTEncoding_Term.mkApp _173_1530))
in (let _173_1544 = (let _173_1543 = (let _173_1542 = (let _173_1541 = (let _173_1540 = (let _173_1539 = (let _173_1538 = (let _173_1537 = (let _173_1536 = (let _173_1532 = (let _173_1531 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_173_1531)::[])
in (_173_1532)::[])
in (let _173_1535 = (let _173_1534 = (let _173_1533 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_173_1533, valid_b_x))
in (FStar_SMTEncoding_Term.mkImp _173_1534))
in (_173_1536, (xx)::[], _173_1535)))
in (FStar_SMTEncoding_Term.mkExists _173_1537))
in (_173_1538, valid))
in (FStar_SMTEncoding_Term.mkIff _173_1539))
in (((valid)::[])::[], (aa)::(bb)::[], _173_1540))
in (FStar_SMTEncoding_Term.mkForall _173_1541))
in (_173_1542, Some ("exists interpretation"), Some ("exists-interp")))
in FStar_SMTEncoding_Term.Assume (_173_1543))
in (_173_1544)::[]))))))))))
in (

let mk_range_interp = (fun env range tt -> (

let range_ty = (FStar_SMTEncoding_Term.mkApp (range, []))
in (let _173_1555 = (let _173_1554 = (let _173_1553 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_ty)
in (let _173_1552 = (let _173_1551 = (varops.fresh "typing_range_const")
in Some (_173_1551))
in (_173_1553, Some ("Range_const typing"), _173_1552)))
in FStar_SMTEncoding_Term.Assume (_173_1554))
in (_173_1555)::[])))
in (

let prims = ((FStar_Syntax_Const.unit_lid, mk_unit))::((FStar_Syntax_Const.bool_lid, mk_bool))::((FStar_Syntax_Const.int_lid, mk_int))::((FStar_Syntax_Const.string_lid, mk_str))::((FStar_Syntax_Const.ref_lid, mk_ref))::((FStar_Syntax_Const.false_lid, mk_false_interp))::((FStar_Syntax_Const.and_lid, mk_and_interp))::((FStar_Syntax_Const.or_lid, mk_or_interp))::((FStar_Syntax_Const.eq2_lid, mk_eq2_interp))::((FStar_Syntax_Const.imp_lid, mk_imp_interp))::((FStar_Syntax_Const.iff_lid, mk_iff_interp))::((FStar_Syntax_Const.forall_lid, mk_forall_interp))::((FStar_Syntax_Const.exists_lid, mk_exists_interp))::((FStar_Syntax_Const.range_lid, mk_range_interp))::[]
in (fun env t s tt -> (match ((FStar_Util.find_opt (fun _83_1932 -> (match (_83_1932) with
| (l, _83_1931) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_83_1935, f) -> begin
(f env s tt)
end)))))))))))))))))))))


let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let _83_1941 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _173_1749 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _173_1749))
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

let _83_1949 = (encode_sigelt' env se)
in (match (_83_1949) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _173_1752 = (let _173_1751 = (let _173_1750 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (_173_1750))
in (_173_1751)::[])
in (_173_1752, e))
end
| _83_1952 -> begin
(let _173_1759 = (let _173_1758 = (let _173_1754 = (let _173_1753 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_173_1753))
in (_173_1754)::g)
in (let _173_1757 = (let _173_1756 = (let _173_1755 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_173_1755))
in (_173_1756)::[])
in (FStar_List.append _173_1758 _173_1757)))
in (_173_1759, e))
end)
end)))))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let should_skip = (fun l -> false)
in (

let encode_top_level_val = (fun env lid t quals -> (

let tt = (norm env t)
in (

let _83_1965 = (encode_free_var env lid t tt quals)
in (match (_83_1965) with
| (decls, env) -> begin
if (FStar_Syntax_Util.is_smt_lemma t) then begin
(let _173_1773 = (let _173_1772 = (encode_smt_lemma env lid tt)
in (FStar_List.append decls _173_1772))
in (_173_1773, env))
end else begin
(decls, env)
end
end))))
in (

let encode_top_level_vals = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _83_1972 lb -> (match (_83_1972) with
| (decls, env) -> begin
(

let _83_1976 = (let _173_1782 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env _173_1782 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (_83_1976) with
| (decls', env) -> begin
((FStar_List.append decls decls'), env)
end))
end)) ([], env))))
in (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_83_1978) -> begin
(FStar_All.failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _83_1997, _83_1999, _83_2001, _83_2003) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid) -> begin
(

let _83_2009 = (new_term_constant_and_tok_from_lid env lid)
in (match (_83_2009) with
| (tname, ttok, env) -> begin
([], env)
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _83_2012, t, quals, _83_2016) -> begin
(

let will_encode_definition = (not ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _83_13 -> (match (_83_13) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Irreducible) -> begin
true
end
| _83_2029 -> begin
false
end))))))
in if will_encode_definition then begin
([], env)
end else begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (

let _83_2034 = (encode_top_level_val env fv t quals)
in (match (_83_2034) with
| (decls, env) -> begin
(

let tname = lid.FStar_Ident.str
in (

let tsym = (FStar_SMTEncoding_Term.mkFreeV (tname, FStar_SMTEncoding_Term.Term_sort))
in (let _173_1785 = (let _173_1784 = (primitive_type_axioms env.tcenv lid tname tsym)
in (FStar_List.append decls _173_1784))
in (_173_1785, env))))
end)))
end)
end
| FStar_Syntax_Syntax.Sig_assume (l, f, _83_2040, _83_2042) -> begin
(

let _83_2047 = (encode_formula f env)
in (match (_83_2047) with
| (f, decls) -> begin
(

let g = (let _173_1792 = (let _173_1791 = (let _173_1790 = (let _173_1787 = (let _173_1786 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" _173_1786))
in Some (_173_1787))
in (let _173_1789 = (let _173_1788 = (varops.fresh (Prims.strcat "assumption_" l.FStar_Ident.str))
in Some (_173_1788))
in (f, _173_1790, _173_1789)))
in FStar_SMTEncoding_Term.Assume (_173_1791))
in (_173_1792)::[])
in ((FStar_List.append decls g), env))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _83_2052, quals) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) -> begin
(

let _83_2065 = (FStar_Util.fold_map (fun env lb -> (

let lid = (let _173_1796 = (let _173_1795 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _173_1795.FStar_Syntax_Syntax.fv_name)
in _173_1796.FStar_Syntax_Syntax.v)
in if (let _173_1797 = (FStar_TypeChecker_Env.try_lookup_val_decl env.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone _173_1797)) then begin
(

let val_decl = FStar_Syntax_Syntax.Sig_declare_typ ((lid, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, quals, r))
in (

let _83_2062 = (encode_sigelt' env val_decl)
in (match (_83_2062) with
| (decls, env) -> begin
(env, decls)
end)))
end else begin
(env, [])
end)) env (Prims.snd lbs))
in (match (_83_2065) with
| (env, decls) -> begin
((FStar_List.flatten decls), env)
end))
end
| FStar_Syntax_Syntax.Sig_let ((_83_2067, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t); FStar_Syntax_Syntax.lbunivs = _83_2075; FStar_Syntax_Syntax.lbtyp = _83_2073; FStar_Syntax_Syntax.lbeff = _83_2071; FStar_Syntax_Syntax.lbdef = _83_2069})::[]), _83_2082, _83_2084, _83_2086) when (FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Syntax_Const.b2t_lid) -> begin
(

let _83_2092 = (new_term_constant_and_tok_from_lid env b2t.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_83_2092) with
| (tname, ttok, env) -> begin
(

let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (

let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (

let valid_b2t_x = (let _173_1800 = (let _173_1799 = (let _173_1798 = (FStar_SMTEncoding_Term.mkApp ("Prims.b2t", (x)::[]))
in (_173_1798)::[])
in ("Valid", _173_1799))
in (FStar_SMTEncoding_Term.mkApp _173_1800))
in (

let decls = (let _173_1808 = (let _173_1807 = (let _173_1806 = (let _173_1805 = (let _173_1804 = (let _173_1803 = (let _173_1802 = (let _173_1801 = (FStar_SMTEncoding_Term.mkApp ("BoxBool_proj_0", (x)::[]))
in (valid_b2t_x, _173_1801))
in (FStar_SMTEncoding_Term.mkEq _173_1802))
in (((valid_b2t_x)::[])::[], (xx)::[], _173_1803))
in (FStar_SMTEncoding_Term.mkForall _173_1804))
in (_173_1805, Some ("b2t def"), Some ("b2t_def")))
in FStar_SMTEncoding_Term.Assume (_173_1806))
in (_173_1807)::[])
in (FStar_SMTEncoding_Term.DeclFun ((tname, (FStar_SMTEncoding_Term.Term_sort)::[], FStar_SMTEncoding_Term.Term_sort, None)))::_173_1808)
in (decls, env)))))
end))
end
| FStar_Syntax_Syntax.Sig_let (_83_2098, _83_2100, _83_2102, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _83_14 -> (match (_83_14) with
| (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _83_2112 -> begin
false
end)))) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _83_2118, _83_2120, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _83_15 -> (match (_83_15) with
| FStar_Syntax_Syntax.Projector (_83_2126) -> begin
true
end
| _83_2129 -> begin
false
end)))) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((try_lookup_free_var env l)) with
| Some (_83_2133) -> begin
([], env)
end
| None -> begin
(

let se = FStar_Syntax_Syntax.Sig_declare_typ ((l, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, quals, (FStar_Ident.range_of_lid l)))
in (encode_sigelt env se))
end)))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), _83_2141, _83_2143, quals) -> begin
(

let eta_expand = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let _83_2155 = (FStar_Util.first_N nbinders formals)
in (match (_83_2155) with
| (formals, extra_formals) -> begin
(

let subst = (FStar_List.map2 (fun _83_2159 _83_2163 -> (match ((_83_2159, _83_2163)) with
| ((formal, _83_2158), (binder, _83_2162)) -> begin
(let _173_1822 = (let _173_1821 = (FStar_Syntax_Syntax.bv_to_name binder)
in (formal, _173_1821))
in FStar_Syntax_Syntax.NT (_173_1822))
end)) formals binders)
in (

let extra_formals = (let _173_1826 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun _83_2167 -> (match (_83_2167) with
| (x, i) -> begin
(let _173_1825 = (

let _83_2168 = x
in (let _173_1824 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _83_2168.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _83_2168.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _173_1824}))
in (_173_1825, i))
end))))
in (FStar_All.pipe_right _173_1826 FStar_Syntax_Util.name_binders))
in (

let body = (let _173_1833 = (FStar_Syntax_Subst.compress body)
in (let _173_1832 = (let _173_1827 = (FStar_Syntax_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _173_1827))
in (let _173_1831 = (let _173_1830 = (let _173_1829 = (FStar_Syntax_Subst.subst subst t)
in _173_1829.FStar_Syntax_Syntax.n)
in (FStar_All.pipe_left (fun _173_1828 -> Some (_173_1828)) _173_1830))
in (FStar_Syntax_Syntax.extend_app_n _173_1833 _173_1832 _173_1831 body.FStar_Syntax_Syntax.pos))))
in ((FStar_List.append binders extra_formals), body))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (

let rec aux = (fun norm t_norm -> (match ((let _173_1844 = (FStar_Syntax_Util.unascribe e)
in _173_1844.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, lopt) -> begin
(

let _83_2187 = (FStar_Syntax_Subst.open_term' binders body)
in (match (_83_2187) with
| (binders, body, opening) -> begin
(match ((let _173_1845 = (FStar_Syntax_Subst.compress t_norm)
in _173_1845.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let _83_2194 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_83_2194) with
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

let _83_2201 = (FStar_Util.first_N nformals binders)
in (match (_83_2201) with
| (bs0, rest) -> begin
(

let c = (

let subst = (FStar_List.map2 (fun _83_2205 _83_2209 -> (match ((_83_2205, _83_2209)) with
| ((b, _83_2204), (x, _83_2208)) -> begin
(let _173_1849 = (let _173_1848 = (FStar_Syntax_Syntax.bv_to_name x)
in (b, _173_1848))
in FStar_Syntax_Syntax.NT (_173_1849))
end)) bs0 formals)
in (FStar_Syntax_Subst.subst_comp subst c))
in (

let body = (FStar_Syntax_Util.abs rest body lopt)
in (bs0, body, bs0, (FStar_Syntax_Util.comp_result c))))
end)))
end else begin
if (nformals > nbinders) then begin
(

let _83_2215 = (eta_expand binders formals body tres)
in (match (_83_2215) with
| (binders, body) -> begin
(binders, body, formals, tres)
end))
end else begin
(binders, body, formals, tres)
end
end)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, _83_2218) -> begin
(aux true x.FStar_Syntax_Syntax.sort)
end
| _83_2222 when (not (norm)) -> begin
(

let t_norm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm)
in (aux true t_norm))
end
| _83_2225 -> begin
(let _173_1852 = (let _173_1851 = (FStar_Syntax_Print.term_to_string e)
in (let _173_1850 = (FStar_Syntax_Print.term_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str _173_1851 _173_1850)))
in (FStar_All.failwith _173_1852))
end)
end))
end
| _83_2227 -> begin
(match ((let _173_1853 = (FStar_Syntax_Subst.compress t_norm)
in _173_1853.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let _83_2234 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_83_2234) with
| (formals, c) -> begin
(

let tres = (FStar_Syntax_Util.comp_result c)
in (

let _83_2238 = (eta_expand [] formals e tres)
in (match (_83_2238) with
| (binders, body) -> begin
(binders, body, formals, tres)
end)))
end))
end
| _83_2240 -> begin
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

let _83_2268 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _83_2255 lb -> (match (_83_2255) with
| (toks, typs, decls, env) -> begin
(

let _83_2257 = if (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) then begin
(Prims.raise Let_rec_unencodeable)
end else begin
()
end
in (

let t_norm = (whnf env lb.FStar_Syntax_Syntax.lbtyp)
in (

let _83_2263 = (let _173_1858 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env _173_1858 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (_83_2263) with
| (tok, decl, env) -> begin
(let _173_1861 = (let _173_1860 = (let _173_1859 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (_173_1859, tok))
in (_173_1860)::toks)
in (_173_1861, (t_norm)::typs, (decl)::decls, env))
end))))
end)) ([], [], [], env)))
in (match (_83_2268) with
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
| _83_2275 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> (let _173_1864 = (FStar_Syntax_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _173_1864)))))) then begin
(decls, env)
end else begin
if (not (is_rec)) then begin
(match ((bindings, typs, toks)) with
| (({FStar_Syntax_Syntax.lbname = _83_2285; FStar_Syntax_Syntax.lbunivs = _83_2283; FStar_Syntax_Syntax.lbtyp = _83_2281; FStar_Syntax_Syntax.lbeff = _83_2279; FStar_Syntax_Syntax.lbdef = e})::[], (t_norm)::[], ((flid_fv, (f, ftok)))::[]) -> begin
(

let e = (FStar_Syntax_Subst.compress e)
in (

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let _83_2305 = (destruct_bound_function flid t_norm e)
in (match (_83_2305) with
| (binders, body, _83_2302, _83_2304) -> begin
(

let _83_2312 = (encode_binders None binders env)
in (match (_83_2312) with
| (vars, guards, env', binder_decls, _83_2311) -> begin
(

let app = (match (vars) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV (f, FStar_SMTEncoding_Term.Term_sort))
end
| _83_2315 -> begin
(let _173_1866 = (let _173_1865 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (f, _173_1865))
in (FStar_SMTEncoding_Term.mkApp _173_1866))
end)
in (

let _83_2321 = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic)) then begin
(let _173_1868 = (FStar_SMTEncoding_Term.mk_Valid app)
in (let _173_1867 = (encode_formula body env')
in (_173_1868, _173_1867)))
end else begin
(let _173_1869 = (encode_term body env')
in (app, _173_1869))
end
in (match (_83_2321) with
| (app, (body, decls2)) -> begin
(

let eqn = (let _173_1875 = (let _173_1874 = (let _173_1871 = (let _173_1870 = (FStar_SMTEncoding_Term.mkEq (app, body))
in (((app)::[])::[], vars, _173_1870))
in (FStar_SMTEncoding_Term.mkForall _173_1871))
in (let _173_1873 = (let _173_1872 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (_173_1872))
in (_173_1874, _173_1873, Some ((Prims.strcat "equation_" f)))))
in FStar_SMTEncoding_Term.Assume (_173_1875))
in (let _173_1877 = (let _173_1876 = (primitive_type_axioms env.tcenv flid f app)
in (FStar_List.append (FStar_List.append (FStar_List.append (FStar_List.append decls binder_decls) decls2) ((eqn)::[])) _173_1876))
in (_173_1877, env)))
end)))
end))
end))))
end
| _83_2324 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(

let fuel = (let _173_1878 = (varops.fresh "fuel")
in (_173_1878, FStar_SMTEncoding_Term.Fuel_sort))
in (

let fuel_tm = (FStar_SMTEncoding_Term.mkFreeV fuel)
in (

let env0 = env
in (

let _83_2342 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _83_2330 _83_2335 -> (match ((_83_2330, _83_2335)) with
| ((gtoks, env), (flid_fv, (f, ftok))) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let g = (varops.new_fvar flid)
in (

let gtok = (varops.new_fvar flid)
in (

let env = (let _173_1883 = (let _173_1882 = (FStar_SMTEncoding_Term.mkApp (g, (fuel_tm)::[]))
in (FStar_All.pipe_left (fun _173_1881 -> Some (_173_1881)) _173_1882))
in (push_free_var env flid gtok _173_1883))
in (((flid, f, ftok, g, gtok))::gtoks, env)))))
end)) ([], env)))
in (match (_83_2342) with
| (gtoks, env) -> begin
(

let gtoks = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env0 _83_2351 t_norm _83_2362 -> (match ((_83_2351, _83_2362)) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = _83_2361; FStar_Syntax_Syntax.lbunivs = _83_2359; FStar_Syntax_Syntax.lbtyp = _83_2357; FStar_Syntax_Syntax.lbeff = _83_2355; FStar_Syntax_Syntax.lbdef = e}) -> begin
(

let _83_2367 = (destruct_bound_function flid t_norm e)
in (match (_83_2367) with
| (binders, body, formals, tres) -> begin
(

let _83_2374 = (encode_binders None binders env)
in (match (_83_2374) with
| (vars, guards, env', binder_decls, _83_2373) -> begin
(

let decl_g = (let _173_1894 = (let _173_1893 = (let _173_1892 = (FStar_List.map Prims.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::_173_1892)
in (g, _173_1893, FStar_SMTEncoding_Term.Term_sort, Some ("Fuel-instrumented function name")))
in FStar_SMTEncoding_Term.DeclFun (_173_1894))
in (

let env0 = (push_zfuel_name env0 flid g)
in (

let decl_g_tok = FStar_SMTEncoding_Term.DeclFun ((gtok, [], FStar_SMTEncoding_Term.Term_sort, Some ("Token for fuel-instrumented partial applications")))
in (

let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (

let app = (FStar_SMTEncoding_Term.mkApp (f, vars_tm))
in (

let gsapp = (let _173_1897 = (let _173_1896 = (let _173_1895 = (FStar_SMTEncoding_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (_173_1895)::vars_tm)
in (g, _173_1896))
in (FStar_SMTEncoding_Term.mkApp _173_1897))
in (

let gmax = (let _173_1900 = (let _173_1899 = (let _173_1898 = (FStar_SMTEncoding_Term.mkApp ("MaxFuel", []))
in (_173_1898)::vars_tm)
in (g, _173_1899))
in (FStar_SMTEncoding_Term.mkApp _173_1900))
in (

let _83_2384 = (encode_term body env')
in (match (_83_2384) with
| (body_tm, decls2) -> begin
(

let eqn_g = (let _173_1906 = (let _173_1905 = (let _173_1902 = (let _173_1901 = (FStar_SMTEncoding_Term.mkEq (gsapp, body_tm))
in (((gsapp)::[])::[], (fuel)::vars, _173_1901))
in (FStar_SMTEncoding_Term.mkForall _173_1902))
in (let _173_1904 = (let _173_1903 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (_173_1903))
in (_173_1905, _173_1904, Some ((Prims.strcat "equation_with_fuel_" g)))))
in FStar_SMTEncoding_Term.Assume (_173_1906))
in (

let eqn_f = (let _173_1910 = (let _173_1909 = (let _173_1908 = (let _173_1907 = (FStar_SMTEncoding_Term.mkEq (app, gmax))
in (((app)::[])::[], vars, _173_1907))
in (FStar_SMTEncoding_Term.mkForall _173_1908))
in (_173_1909, Some ("Correspondence of recursive function to instrumented version"), Some ((Prims.strcat "fuel_correspondence_" g))))
in FStar_SMTEncoding_Term.Assume (_173_1910))
in (

let eqn_g' = (let _173_1919 = (let _173_1918 = (let _173_1917 = (let _173_1916 = (let _173_1915 = (let _173_1914 = (let _173_1913 = (let _173_1912 = (let _173_1911 = (FStar_SMTEncoding_Term.n_fuel 0)
in (_173_1911)::vars_tm)
in (g, _173_1912))
in (FStar_SMTEncoding_Term.mkApp _173_1913))
in (gsapp, _173_1914))
in (FStar_SMTEncoding_Term.mkEq _173_1915))
in (((gsapp)::[])::[], (fuel)::vars, _173_1916))
in (FStar_SMTEncoding_Term.mkForall _173_1917))
in (_173_1918, Some ("Fuel irrelevance"), Some ((Prims.strcat "fuel_irrelevance_" g))))
in FStar_SMTEncoding_Term.Assume (_173_1919))
in (

let _83_2407 = (

let _83_2394 = (encode_binders None formals env0)
in (match (_83_2394) with
| (vars, v_guards, env, binder_decls, _83_2393) -> begin
(

let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (

let gapp = (FStar_SMTEncoding_Term.mkApp (g, (fuel_tm)::vars_tm))
in (

let tok_corr = (

let tok_app = (let _173_1920 = (FStar_SMTEncoding_Term.mkFreeV (gtok, FStar_SMTEncoding_Term.Term_sort))
in (mk_Apply _173_1920 ((fuel)::vars)))
in (let _173_1924 = (let _173_1923 = (let _173_1922 = (let _173_1921 = (FStar_SMTEncoding_Term.mkEq (tok_app, gapp))
in (((tok_app)::[])::[], (fuel)::vars, _173_1921))
in (FStar_SMTEncoding_Term.mkForall _173_1922))
in (_173_1923, Some ("Fuel token correspondence"), Some ((Prims.strcat "fuel_tokem_correspondence_" gtok))))
in FStar_SMTEncoding_Term.Assume (_173_1924)))
in (

let _83_2404 = (

let _83_2401 = (encode_term_pred None tres env gapp)
in (match (_83_2401) with
| (g_typing, d3) -> begin
(let _173_1932 = (let _173_1931 = (let _173_1930 = (let _173_1929 = (let _173_1928 = (let _173_1927 = (let _173_1926 = (let _173_1925 = (FStar_SMTEncoding_Term.mk_and_l v_guards)
in (_173_1925, g_typing))
in (FStar_SMTEncoding_Term.mkImp _173_1926))
in (((gapp)::[])::[], (fuel)::vars, _173_1927))
in (FStar_SMTEncoding_Term.mkForall _173_1928))
in (_173_1929, Some ("Typing correspondence of token to term"), Some ((Prims.strcat "token_correspondence_" g))))
in FStar_SMTEncoding_Term.Assume (_173_1930))
in (_173_1931)::[])
in (d3, _173_1932))
end))
in (match (_83_2404) with
| (aux_decls, typing_corr) -> begin
((FStar_List.append binder_decls aux_decls), (FStar_List.append typing_corr ((tok_corr)::[])))
end)))))
end))
in (match (_83_2407) with
| (aux_decls, g_typing) -> begin
((FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) aux_decls) ((decl_g)::(decl_g_tok)::[])), (FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing), env0)
end)))))
end)))))))))
end))
end))
end))
in (

let _83_2423 = (let _173_1935 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _83_2411 _83_2415 -> (match ((_83_2411, _83_2415)) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(

let _83_2419 = (encode_one_binding env0 gtok ty bs)
in (match (_83_2419) with
| (decls', eqns', env0) -> begin
((decls')::decls, (FStar_List.append eqns' eqns), env0)
end))
end)) ((decls)::[], [], env0) _173_1935))
in (match (_83_2423) with
| (decls, eqns, env0) -> begin
(

let _83_2432 = (let _173_1937 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _173_1937 (FStar_List.partition (fun _83_17 -> (match (_83_17) with
| FStar_SMTEncoding_Term.DeclFun (_83_2426) -> begin
true
end
| _83_2429 -> begin
false
end)))))
in (match (_83_2432) with
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

let msg = (let _173_1940 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _173_1940 (FStar_String.concat " and ")))
in (

let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in ((decl)::[], env)))
end))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _83_2436, _83_2438, _83_2440) -> begin
(

let _83_2445 = (encode_signature env ses)
in (match (_83_2445) with
| (g, env) -> begin
(

let _83_2459 = (FStar_All.pipe_right g (FStar_List.partition (fun _83_18 -> (match (_83_18) with
| FStar_SMTEncoding_Term.Assume (_83_2448, Some ("inversion axiom"), _83_2452) -> begin
false
end
| _83_2456 -> begin
true
end))))
in (match (_83_2459) with
| (g', inversions) -> begin
(

let _83_2468 = (FStar_All.pipe_right g' (FStar_List.partition (fun _83_19 -> (match (_83_19) with
| FStar_SMTEncoding_Term.DeclFun (_83_2462) -> begin
true
end
| _83_2465 -> begin
false
end))))
in (match (_83_2468) with
| (decls, rest) -> begin
((FStar_List.append (FStar_List.append decls rest) inversions), env)
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, _83_2471, tps, k, _83_2475, datas, quals, _83_2479) -> begin
(

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _83_20 -> (match (_83_20) with
| (FStar_Syntax_Syntax.Logic) | (FStar_Syntax_Syntax.Assumption) -> begin
true
end
| _83_2486 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(

let _83_2498 = c
in (match (_83_2498) with
| (name, args, _83_2493, _83_2495, _83_2497) -> begin
(let _173_1948 = (let _173_1947 = (let _173_1946 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in (name, _173_1946, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_173_1947))
in (_173_1948)::[])
end))
end else begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end)
in (

let inversion_axioms = (fun tapp vars -> if (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _173_1954 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right _173_1954 FStar_Option.isNone))))) then begin
[]
end else begin
(

let _83_2505 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_83_2505) with
| (xxsym, xx) -> begin
(

let _83_2541 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _83_2508 l -> (match (_83_2508) with
| (out, decls) -> begin
(

let _83_2513 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (_83_2513) with
| (_83_2511, data_t) -> begin
(

let _83_2516 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (_83_2516) with
| (args, res) -> begin
(

let indices = (match ((let _173_1957 = (FStar_Syntax_Subst.compress res)
in _173_1957.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_83_2518, indices) -> begin
indices
end
| _83_2523 -> begin
[]
end)
in (

let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env _83_2529 -> (match (_83_2529) with
| (x, _83_2528) -> begin
(let _173_1962 = (let _173_1961 = (let _173_1960 = (mk_term_projector_name l x)
in (_173_1960, (xx)::[]))
in (FStar_SMTEncoding_Term.mkApp _173_1961))
in (push_term_var env x _173_1962))
end)) env))
in (

let _83_2533 = (encode_args indices env)
in (match (_83_2533) with
| (indices, decls') -> begin
(

let _83_2534 = if ((FStar_List.length indices) <> (FStar_List.length vars)) then begin
(FStar_All.failwith "Impossible")
end else begin
()
end
in (

let eqs = (let _173_1967 = (FStar_List.map2 (fun v a -> (let _173_1966 = (let _173_1965 = (FStar_SMTEncoding_Term.mkFreeV v)
in (_173_1965, a))
in (FStar_SMTEncoding_Term.mkEq _173_1966))) vars indices)
in (FStar_All.pipe_right _173_1967 FStar_SMTEncoding_Term.mk_and_l))
in (let _173_1972 = (let _173_1971 = (let _173_1970 = (let _173_1969 = (let _173_1968 = (mk_data_tester env l xx)
in (_173_1968, eqs))
in (FStar_SMTEncoding_Term.mkAnd _173_1969))
in (out, _173_1970))
in (FStar_SMTEncoding_Term.mkOr _173_1971))
in (_173_1972, (FStar_List.append decls decls')))))
end))))
end))
end))
end)) (FStar_SMTEncoding_Term.mkFalse, [])))
in (match (_83_2541) with
| (data_ax, decls) -> begin
(

let _83_2544 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_83_2544) with
| (ffsym, ff) -> begin
(

let fuel_guarded_inversion = (

let xx_has_type_sfuel = if ((FStar_List.length datas) > 1) then begin
(let _173_1973 = (FStar_SMTEncoding_Term.mkApp ("SFuel", (ff)::[]))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel _173_1973 xx tapp))
end else begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end
in (let _173_1980 = (let _173_1979 = (let _173_1976 = (let _173_1975 = (add_fuel (ffsym, FStar_SMTEncoding_Term.Fuel_sort) (((xxsym, FStar_SMTEncoding_Term.Term_sort))::vars))
in (let _173_1974 = (FStar_SMTEncoding_Term.mkImp (xx_has_type_sfuel, data_ax))
in (((xx_has_type_sfuel)::[])::[], _173_1975, _173_1974)))
in (FStar_SMTEncoding_Term.mkForall _173_1976))
in (let _173_1978 = (let _173_1977 = (varops.fresh (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str))
in Some (_173_1977))
in (_173_1979, Some ("inversion axiom"), _173_1978)))
in FStar_SMTEncoding_Term.Assume (_173_1980)))
in (

let pattern_guarded_inversion = if ((contains_name env "Prims.inversion") && ((FStar_List.length datas) > 1)) then begin
(

let xx_has_type_fuel = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let pattern_guard = (FStar_SMTEncoding_Term.mkApp ("Prims.inversion", (tapp)::[]))
in (let _173_1988 = (let _173_1987 = (let _173_1986 = (let _173_1983 = (let _173_1982 = (add_fuel (ffsym, FStar_SMTEncoding_Term.Fuel_sort) (((xxsym, FStar_SMTEncoding_Term.Term_sort))::vars))
in (let _173_1981 = (FStar_SMTEncoding_Term.mkImp (xx_has_type_fuel, data_ax))
in (((xx_has_type_fuel)::(pattern_guard)::[])::[], _173_1982, _173_1981)))
in (FStar_SMTEncoding_Term.mkForall _173_1983))
in (let _173_1985 = (let _173_1984 = (varops.fresh (Prims.strcat "pattern_guarded_inversion_" t.FStar_Ident.str))
in Some (_173_1984))
in (_173_1986, Some ("inversion axiom"), _173_1985)))
in FStar_SMTEncoding_Term.Assume (_173_1987))
in (_173_1988)::[])))
end else begin
[]
end
in (FStar_List.append (FStar_List.append decls ((fuel_guarded_inversion)::[])) pattern_guarded_inversion)))
end))
end))
end))
end)
in (

let _83_2558 = (match ((let _173_1989 = (FStar_Syntax_Subst.compress k)
in _173_1989.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
((FStar_List.append tps formals), (FStar_Syntax_Util.comp_result kres))
end
| _83_2555 -> begin
(tps, k)
end)
in (match (_83_2558) with
| (formals, res) -> begin
(

let _83_2561 = (FStar_Syntax_Subst.open_term formals res)
in (match (_83_2561) with
| (formals, res) -> begin
(

let _83_2568 = (encode_binders None formals env)
in (match (_83_2568) with
| (vars, guards, env', binder_decls, _83_2567) -> begin
(

let _83_2572 = (new_term_constant_and_tok_from_lid env t)
in (match (_83_2572) with
| (tname, ttok, env) -> begin
(

let ttok_tm = (FStar_SMTEncoding_Term.mkApp (ttok, []))
in (

let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (

let tapp = (let _173_1991 = (let _173_1990 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (tname, _173_1990))
in (FStar_SMTEncoding_Term.mkApp _173_1991))
in (

let _83_2593 = (

let tname_decl = (let _173_1995 = (let _173_1994 = (FStar_All.pipe_right vars (FStar_List.map (fun _83_2578 -> (match (_83_2578) with
| (n, s) -> begin
((Prims.strcat tname n), s)
end))))
in (let _173_1993 = (varops.next_id ())
in (tname, _173_1994, FStar_SMTEncoding_Term.Term_sort, _173_1993, false)))
in (constructor_or_logic_type_decl _173_1995))
in (

let _83_2590 = (match (vars) with
| [] -> begin
(let _173_1999 = (let _173_1998 = (let _173_1997 = (FStar_SMTEncoding_Term.mkApp (tname, []))
in (FStar_All.pipe_left (fun _173_1996 -> Some (_173_1996)) _173_1997))
in (push_free_var env t tname _173_1998))
in ([], _173_1999))
end
| _83_2582 -> begin
(

let ttok_decl = FStar_SMTEncoding_Term.DeclFun ((ttok, [], FStar_SMTEncoding_Term.Term_sort, Some ("token")))
in (

let ttok_fresh = (let _173_2000 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (ttok, FStar_SMTEncoding_Term.Term_sort) _173_2000))
in (

let ttok_app = (mk_Apply ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (let _173_2004 = (let _173_2003 = (let _173_2002 = (let _173_2001 = (FStar_SMTEncoding_Term.mkEq (ttok_app, tapp))
in (pats, None, vars, _173_2001))
in (FStar_SMTEncoding_Term.mkForall' _173_2002))
in (_173_2003, Some ("name-token correspondence"), Some ((Prims.strcat "token_correspondence_" ttok))))
in FStar_SMTEncoding_Term.Assume (_173_2004))
in ((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[], env))))))
end)
in (match (_83_2590) with
| (tok_decls, env) -> begin
((FStar_List.append tname_decl tok_decls), env)
end)))
in (match (_83_2593) with
| (decls, env) -> begin
(

let kindingAx = (

let _83_2596 = (encode_term_pred None res env' tapp)
in (match (_83_2596) with
| (k, decls) -> begin
(

let karr = if ((FStar_List.length formals) > 0) then begin
(let _173_2008 = (let _173_2007 = (let _173_2006 = (let _173_2005 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _173_2005))
in (_173_2006, Some ("kinding"), Some ((Prims.strcat "pre_kinding_" ttok))))
in FStar_SMTEncoding_Term.Assume (_173_2007))
in (_173_2008)::[])
end else begin
[]
end
in (let _173_2014 = (let _173_2013 = (let _173_2012 = (let _173_2011 = (let _173_2010 = (let _173_2009 = (FStar_SMTEncoding_Term.mkImp (guard, k))
in (((tapp)::[])::[], vars, _173_2009))
in (FStar_SMTEncoding_Term.mkForall _173_2010))
in (_173_2011, None, Some ((Prims.strcat "kinding_" ttok))))
in FStar_SMTEncoding_Term.Assume (_173_2012))
in (_173_2013)::[])
in (FStar_List.append (FStar_List.append decls karr) _173_2014)))
end))
in (

let aux = (let _173_2018 = (let _173_2015 = (inversion_axioms tapp vars)
in (FStar_List.append kindingAx _173_2015))
in (let _173_2017 = (let _173_2016 = (pretype_axiom tapp vars)
in (_173_2016)::[])
in (FStar_List.append _173_2018 _173_2017)))
in (

let g = (FStar_List.append (FStar_List.append decls binder_decls) aux)
in (g, env))))
end)))))
end))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, _83_2603, _83_2605, _83_2607, _83_2609, _83_2611, _83_2613, _83_2615) when (FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_datacon (d, _83_2620, t, _83_2623, n_tps, quals, _83_2627, drange) -> begin
(

let _83_2634 = (new_term_constant_and_tok_from_lid env d)
in (match (_83_2634) with
| (ddconstrsym, ddtok, env) -> begin
(

let ddtok_tm = (FStar_SMTEncoding_Term.mkApp (ddtok, []))
in (

let _83_2638 = (FStar_Syntax_Util.arrow_formals t)
in (match (_83_2638) with
| (formals, t_res) -> begin
(

let _83_2641 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_83_2641) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_SMTEncoding_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (

let _83_2648 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_83_2648) with
| (vars, guards, env', binder_decls, names) -> begin
(

let projectors = (FStar_All.pipe_right names (FStar_List.map (fun x -> (let _173_2020 = (mk_term_projector_name d x)
in (_173_2020, FStar_SMTEncoding_Term.Term_sort)))))
in (

let datacons = (let _173_2022 = (let _173_2021 = (varops.next_id ())
in (ddconstrsym, projectors, FStar_SMTEncoding_Term.Term_sort, _173_2021, true))
in (FStar_All.pipe_right _173_2022 FStar_SMTEncoding_Term.constructor_to_decl))
in (

let app = (mk_Apply ddtok_tm vars)
in (

let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (

let _83_2658 = (encode_term_pred None t env ddtok_tm)
in (match (_83_2658) with
| (tok_typing, decls3) -> begin
(

let _83_2665 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_83_2665) with
| (vars', guards', env'', decls_formals, _83_2664) -> begin
(

let _83_2670 = (

let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars')
in (

let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (encode_term_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_83_2670) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_SMTEncoding_Term.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _83_2674 -> begin
(let _173_2024 = (let _173_2023 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (ddtok, FStar_SMTEncoding_Term.Term_sort) _173_2023))
in (_173_2024)::[])
end)
in (

let encode_elim = (fun _83_2677 -> (match (()) with
| () -> begin
(

let _83_2680 = (FStar_Syntax_Util.head_and_args t_res)
in (match (_83_2680) with
| (head, args) -> begin
(match ((let _173_2027 = (FStar_Syntax_Subst.compress head)
in _173_2027.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let _83_2698 = (encode_args args env')
in (match (_83_2698) with
| (encoded_args, arg_decls) -> begin
(

let _83_2713 = (FStar_List.fold_left (fun _83_2702 arg -> (match (_83_2702) with
| (env, arg_vars, eqns) -> begin
(

let _83_2708 = (let _173_2030 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in (gen_term_var env _173_2030))
in (match (_83_2708) with
| (_83_2705, xv, env) -> begin
(let _173_2032 = (let _173_2031 = (FStar_SMTEncoding_Term.mkEq (arg, xv))
in (_173_2031)::eqns)
in (env, (xv)::arg_vars, _173_2032))
end))
end)) (env', [], []) encoded_args)
in (match (_83_2713) with
| (_83_2710, arg_vars, eqns) -> begin
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

let typing_inversion = (let _173_2039 = (let _173_2038 = (let _173_2037 = (let _173_2036 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _173_2035 = (let _173_2034 = (let _173_2033 = (FStar_SMTEncoding_Term.mk_and_l (FStar_List.append eqns guards))
in (ty_pred, _173_2033))
in (FStar_SMTEncoding_Term.mkImp _173_2034))
in (((ty_pred)::[])::[], _173_2036, _173_2035)))
in (FStar_SMTEncoding_Term.mkForall _173_2037))
in (_173_2038, Some ("data constructor typing elim"), Some ((Prims.strcat "data_elim_" ddconstrsym))))
in FStar_SMTEncoding_Term.Assume (_173_2039))
in (

let subterm_ordering = if (FStar_Ident.lid_equals d FStar_Syntax_Const.lextop_lid) then begin
(

let x = (let _173_2040 = (varops.fresh "x")
in (_173_2040, FStar_SMTEncoding_Term.Term_sort))
in (

let xtm = (FStar_SMTEncoding_Term.mkFreeV x)
in (let _173_2052 = (let _173_2051 = (let _173_2048 = (let _173_2047 = (let _173_2042 = (let _173_2041 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in (_173_2041)::[])
in (_173_2042)::[])
in (let _173_2046 = (let _173_2045 = (let _173_2044 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (let _173_2043 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in (_173_2044, _173_2043)))
in (FStar_SMTEncoding_Term.mkImp _173_2045))
in (_173_2047, (x)::[], _173_2046)))
in (FStar_SMTEncoding_Term.mkForall _173_2048))
in (let _173_2050 = (let _173_2049 = (varops.fresh "lextop")
in Some (_173_2049))
in (_173_2051, Some ("lextop is top"), _173_2050)))
in FStar_SMTEncoding_Term.Assume (_173_2052))))
end else begin
(

let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
[]
end
| FStar_SMTEncoding_Term.Term_sort -> begin
(let _173_2055 = (let _173_2054 = (FStar_SMTEncoding_Term.mkFreeV v)
in (FStar_SMTEncoding_Term.mk_Precedes _173_2054 dapp))
in (_173_2055)::[])
end
| _83_2727 -> begin
(FStar_All.failwith "unexpected sort")
end))))
in (let _173_2062 = (let _173_2061 = (let _173_2060 = (let _173_2059 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _173_2058 = (let _173_2057 = (let _173_2056 = (FStar_SMTEncoding_Term.mk_and_l prec)
in (ty_pred, _173_2056))
in (FStar_SMTEncoding_Term.mkImp _173_2057))
in (((ty_pred)::[])::[], _173_2059, _173_2058)))
in (FStar_SMTEncoding_Term.mkForall _173_2060))
in (_173_2061, Some ("subterm ordering"), Some ((Prims.strcat "subterm_ordering_" ddconstrsym))))
in FStar_SMTEncoding_Term.Assume (_173_2062)))
end
in (arg_decls, (typing_inversion)::(subterm_ordering)::[])))))))))
end))
end)))
end
| _83_2731 -> begin
(

let _83_2732 = (let _173_2065 = (let _173_2064 = (FStar_Syntax_Print.lid_to_string d)
in (let _173_2063 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _173_2064 _173_2063)))
in (FStar_TypeChecker_Errors.warn drange _173_2065))
in ([], []))
end)
end))
end))
in (

let _83_2736 = (encode_elim ())
in (match (_83_2736) with
| (decls2, elim) -> begin
(

let g = (let _173_2090 = (let _173_2089 = (let _173_2074 = (let _173_2073 = (let _173_2072 = (let _173_2071 = (let _173_2070 = (let _173_2069 = (let _173_2068 = (let _173_2067 = (let _173_2066 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" _173_2066))
in Some (_173_2067))
in (ddtok, [], FStar_SMTEncoding_Term.Term_sort, _173_2068))
in FStar_SMTEncoding_Term.DeclFun (_173_2069))
in (_173_2070)::[])
in (FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) decls3) _173_2071))
in (FStar_List.append _173_2072 proxy_fresh))
in (FStar_List.append _173_2073 decls_formals))
in (FStar_List.append _173_2074 decls_pred))
in (let _173_2088 = (let _173_2087 = (let _173_2086 = (let _173_2078 = (let _173_2077 = (let _173_2076 = (let _173_2075 = (FStar_SMTEncoding_Term.mkEq (app, dapp))
in (((app)::[])::[], vars, _173_2075))
in (FStar_SMTEncoding_Term.mkForall _173_2076))
in (_173_2077, Some ("equality for proxy"), Some ((Prims.strcat "equality_tok_" ddtok))))
in FStar_SMTEncoding_Term.Assume (_173_2078))
in (let _173_2085 = (let _173_2084 = (let _173_2083 = (let _173_2082 = (let _173_2081 = (let _173_2080 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) vars')
in (let _173_2079 = (FStar_SMTEncoding_Term.mkImp (guard', ty_pred'))
in (((ty_pred')::[])::[], _173_2080, _173_2079)))
in (FStar_SMTEncoding_Term.mkForall _173_2081))
in (_173_2082, Some ("data constructor typing intro"), Some ((Prims.strcat "data_typing_intro_" ddtok))))
in FStar_SMTEncoding_Term.Assume (_173_2083))
in (_173_2084)::[])
in (_173_2086)::_173_2085))
in (FStar_SMTEncoding_Term.Assume ((tok_typing, Some ("typing for data constructor proxy"), Some ((Prims.strcat "typing_tok_" ddtok)))))::_173_2087)
in (FStar_List.append _173_2089 _173_2088)))
in (FStar_List.append _173_2090 elim))
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

let _83_2745 = (encode_free_var env x t t_norm [])
in (match (_83_2745) with
| (decls, env) -> begin
(

let _83_2750 = (lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_83_2750) with
| (n, x', _83_2749) -> begin
((n, x'), decls, env)
end))
end))
end
| Some (n, x, _83_2754) -> begin
((n, x), [], env)
end))
and encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let _83_2763 = (encode_function_type_as_formula None None t env)
in (match (_83_2763) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_SMTEncoding_Term.Assume ((form, Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str)), Some ((Prims.strcat "lemma_" lid.FStar_Ident.str)))))::[]))
end))))
and encode_free_var : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env fv tt t_norm quals -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if ((let _173_2103 = (FStar_Syntax_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _173_2103)) || (FStar_Syntax_Util.is_lemma t_norm)) then begin
(

let _83_2773 = (new_term_constant_and_tok_from_lid env lid)
in (match (_83_2773) with
| (vname, vtok, env) -> begin
(

let arg_sorts = (match ((let _173_2104 = (FStar_Syntax_Subst.compress t_norm)
in _173_2104.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _83_2776) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun _83_2779 -> FStar_SMTEncoding_Term.Term_sort)))
end
| _83_2782 -> begin
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

let _83_2797 = (

let _83_2792 = (curried_arrow_formals_comp t_norm)
in (match (_83_2792) with
| (args, comp) -> begin
if encode_non_total_function_typ then begin
(let _173_2106 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in (args, _173_2106))
end else begin
(args, (None, (FStar_Syntax_Util.comp_result comp)))
end
end))
in (match (_83_2797) with
| (formals, (pre_opt, res_t)) -> begin
(

let _83_2801 = (new_term_constant_and_tok_from_lid env lid)
in (match (_83_2801) with
| (vname, vtok, env) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV (vname, FStar_SMTEncoding_Term.Term_sort))
end
| _83_2804 -> begin
(FStar_SMTEncoding_Term.mkApp (vtok, []))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun _83_21 -> (match (_83_21) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(

let _83_2820 = (FStar_Util.prefix vars)
in (match (_83_2820) with
| (_83_2815, (xxsym, _83_2818)) -> begin
(

let xx = (FStar_SMTEncoding_Term.mkFreeV (xxsym, FStar_SMTEncoding_Term.Term_sort))
in (let _173_2123 = (let _173_2122 = (let _173_2121 = (let _173_2120 = (let _173_2119 = (let _173_2118 = (let _173_2117 = (let _173_2116 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _173_2116))
in (vapp, _173_2117))
in (FStar_SMTEncoding_Term.mkEq _173_2118))
in (((vapp)::[])::[], vars, _173_2119))
in (FStar_SMTEncoding_Term.mkForall _173_2120))
in (_173_2121, Some ("Discriminator equation"), Some ((Prims.strcat "disc_equation_" (escape d.FStar_Ident.str)))))
in FStar_SMTEncoding_Term.Assume (_173_2122))
in (_173_2123)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(

let _83_2832 = (FStar_Util.prefix vars)
in (match (_83_2832) with
| (_83_2827, (xxsym, _83_2830)) -> begin
(

let xx = (FStar_SMTEncoding_Term.mkFreeV (xxsym, FStar_SMTEncoding_Term.Term_sort))
in (

let f = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = 0; FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (

let tp_name = (mk_term_projector_name d f)
in (

let prim_app = (FStar_SMTEncoding_Term.mkApp (tp_name, (xx)::[]))
in (let _173_2128 = (let _173_2127 = (let _173_2126 = (let _173_2125 = (let _173_2124 = (FStar_SMTEncoding_Term.mkEq (vapp, prim_app))
in (((vapp)::[])::[], vars, _173_2124))
in (FStar_SMTEncoding_Term.mkForall _173_2125))
in (_173_2126, Some ("Projector equation"), Some ((Prims.strcat "proj_equation_" tp_name))))
in FStar_SMTEncoding_Term.Assume (_173_2127))
in (_173_2128)::[])))))
end))
end
| _83_2838 -> begin
[]
end)))))
in (

let _83_2845 = (encode_binders None formals env)
in (match (_83_2845) with
| (vars, guards, env', decls1, _83_2844) -> begin
(

let _83_2854 = (match (pre_opt) with
| None -> begin
(let _173_2129 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_173_2129, decls1))
end
| Some (p) -> begin
(

let _83_2851 = (encode_formula p env')
in (match (_83_2851) with
| (g, ds) -> begin
(let _173_2130 = (FStar_SMTEncoding_Term.mk_and_l ((g)::guards))
in (_173_2130, (FStar_List.append decls1 ds)))
end))
end)
in (match (_83_2854) with
| (guard, decls1) -> begin
(

let vtok_app = (mk_Apply vtok_tm vars)
in (

let vapp = (let _173_2132 = (let _173_2131 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (vname, _173_2131))
in (FStar_SMTEncoding_Term.mkApp _173_2132))
in (

let _83_2878 = (

let vname_decl = (let _173_2135 = (let _173_2134 = (FStar_All.pipe_right formals (FStar_List.map (fun _83_2857 -> FStar_SMTEncoding_Term.Term_sort)))
in (vname, _173_2134, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_173_2135))
in (

let _83_2865 = (

let env = (

let _83_2860 = env
in {bindings = _83_2860.bindings; depth = _83_2860.depth; tcenv = _83_2860.tcenv; warn = _83_2860.warn; cache = _83_2860.cache; nolabels = _83_2860.nolabels; use_zfuel_name = _83_2860.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in if (not ((head_normal env tt))) then begin
(encode_term_pred None tt env vtok_tm)
end else begin
(encode_term_pred None t_norm env vtok_tm)
end)
in (match (_83_2865) with
| (tok_typing, decls2) -> begin
(

let tok_typing = FStar_SMTEncoding_Term.Assume ((tok_typing, Some ("function token typing"), Some ((Prims.strcat "function_token_typing_" vname))))
in (

let _83_2875 = (match (formals) with
| [] -> begin
(let _173_2139 = (let _173_2138 = (let _173_2137 = (FStar_SMTEncoding_Term.mkFreeV (vname, FStar_SMTEncoding_Term.Term_sort))
in (FStar_All.pipe_left (fun _173_2136 -> Some (_173_2136)) _173_2137))
in (push_free_var env lid vname _173_2138))
in ((FStar_List.append decls2 ((tok_typing)::[])), _173_2139))
end
| _83_2869 -> begin
(

let vtok_decl = FStar_SMTEncoding_Term.DeclFun ((vtok, [], FStar_SMTEncoding_Term.Term_sort, None))
in (

let vtok_fresh = (let _173_2140 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (vtok, FStar_SMTEncoding_Term.Term_sort) _173_2140))
in (

let name_tok_corr = (let _173_2144 = (let _173_2143 = (let _173_2142 = (let _173_2141 = (FStar_SMTEncoding_Term.mkEq (vtok_app, vapp))
in (((vtok_app)::[])::[], vars, _173_2141))
in (FStar_SMTEncoding_Term.mkForall _173_2142))
in (_173_2143, Some ("Name-token correspondence"), Some ((Prims.strcat "token_correspondence_" vname))))
in FStar_SMTEncoding_Term.Assume (_173_2144))
in ((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[])), env))))
end)
in (match (_83_2875) with
| (tok_decl, env) -> begin
((vname_decl)::tok_decl, env)
end)))
end)))
in (match (_83_2878) with
| (decls2, env) -> begin
(

let _83_2886 = (

let res_t = (FStar_Syntax_Subst.compress res_t)
in (

let _83_2882 = (encode_term res_t env')
in (match (_83_2882) with
| (encoded_res_t, decls) -> begin
(let _173_2145 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in (encoded_res_t, _173_2145, decls))
end)))
in (match (_83_2886) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (let _173_2149 = (let _173_2148 = (let _173_2147 = (let _173_2146 = (FStar_SMTEncoding_Term.mkImp (guard, ty_pred))
in (((vapp)::[])::[], vars, _173_2146))
in (FStar_SMTEncoding_Term.mkForall _173_2147))
in (_173_2148, Some ("free var typing"), Some ((Prims.strcat "typing_" vname))))
in FStar_SMTEncoding_Term.Assume (_173_2149))
in (

let freshness = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New)) then begin
(let _173_2155 = (let _173_2152 = (let _173_2151 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (let _173_2150 = (varops.next_id ())
in (vname, _173_2151, FStar_SMTEncoding_Term.Term_sort, _173_2150)))
in (FStar_SMTEncoding_Term.fresh_constructor _173_2152))
in (let _173_2154 = (let _173_2153 = (pretype_axiom vapp vars)
in (_173_2153)::[])
in (_173_2155)::_173_2154))
end else begin
[]
end
in (

let g = (let _173_2157 = (let _173_2156 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_173_2156)
in (FStar_List.append (FStar_List.append (FStar_List.append (FStar_List.append decls1 decls2) decls3) freshness) _173_2157))
in (g, env))))
end))
end))))
end))
end))))
end))
end)))
end
end))
and encode_signature : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _83_2894 se -> (match (_83_2894) with
| (g, env) -> begin
(

let _83_2898 = (encode_sigelt env se)
in (match (_83_2898) with
| (g', env) -> begin
((FStar_List.append g g'), env)
end))
end)) ([], env))))


let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings -> (

let encode_binding = (fun b _83_2905 -> (match (_83_2905) with
| (decls, env) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (_83_2907) -> begin
([], env)
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(

let _83_2914 = (new_term_constant env x)
in (match (_83_2914) with
| (xxsym, xx, env') -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (

let _83_2916 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _173_2172 = (FStar_Syntax_Print.bv_to_string x)
in (let _173_2171 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _173_2170 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" _173_2172 _173_2171 _173_2170))))
end else begin
()
end
in (

let _83_2920 = (encode_term_pred None t1 env xx)
in (match (_83_2920) with
| (t, decls') -> begin
(

let caption = if (FStar_Options.log_queries ()) then begin
(let _173_2176 = (let _173_2175 = (FStar_Syntax_Print.bv_to_string x)
in (let _173_2174 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _173_2173 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _173_2175 _173_2174 _173_2173))))
in Some (_173_2176))
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
| FStar_TypeChecker_Env.Binding_lid (x, (_83_2927, t)) -> begin
(

let t_norm = (whnf env t)
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant None)
in (

let _83_2936 = (encode_free_var env fv t t_norm [])
in (match (_83_2936) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end))))
end
| (FStar_TypeChecker_Env.Binding_sig_inst (_, se, _)) | (FStar_TypeChecker_Env.Binding_sig (_, se)) -> begin
(

let _83_2950 = (encode_sigelt env se)
in (match (_83_2950) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end))
end)
end))
in (FStar_List.fold_right encode_binding bindings ([], env))))


let encode_labels = (fun labs -> (

let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _83_2957 -> (match (_83_2957) with
| (l, _83_2954, _83_2956) -> begin
FStar_SMTEncoding_Term.DeclFun (((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _83_2964 -> (match (_83_2964) with
| (l, _83_2961, _83_2963) -> begin
(let _173_2184 = (FStar_All.pipe_left (fun _173_2180 -> FStar_SMTEncoding_Term.Echo (_173_2180)) (Prims.fst l))
in (let _173_2183 = (let _173_2182 = (let _173_2181 = (FStar_SMTEncoding_Term.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (_173_2181))
in (_173_2182)::[])
in (_173_2184)::_173_2183))
end))))
in (prefix, suffix))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (let _173_2189 = (let _173_2188 = (let _173_2187 = (FStar_Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _173_2187; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_173_2188)::[])
in (FStar_ST.op_Colon_Equals last_env _173_2189)))


let get_env : FStar_TypeChecker_Env.env  ->  env_t = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "No env; call init first!")
end
| (e)::_83_2970 -> begin
(

let _83_2973 = e
in {bindings = _83_2973.bindings; depth = _83_2973.depth; tcenv = tcenv; warn = _83_2973.warn; cache = _83_2973.cache; nolabels = _83_2973.nolabels; use_zfuel_name = _83_2973.use_zfuel_name; encode_non_total_function_typ = _83_2973.encode_non_total_function_typ})
end))


let set_env : env_t  ->  Prims.unit = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| (_83_2979)::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))


let push_env : Prims.unit  ->  Prims.unit = (fun _83_2981 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| (hd)::tl -> begin
(

let refs = (FStar_Util.smap_copy hd.cache)
in (

let top = (

let _83_2987 = hd
in {bindings = _83_2987.bindings; depth = _83_2987.depth; tcenv = _83_2987.tcenv; warn = _83_2987.warn; cache = refs; nolabels = _83_2987.nolabels; use_zfuel_name = _83_2987.use_zfuel_name; encode_non_total_function_typ = _83_2987.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))


let pop_env : Prims.unit  ->  Prims.unit = (fun _83_2990 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Popping an empty stack")
end
| (_83_2994)::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))


let mark_env : Prims.unit  ->  Prims.unit = (fun _83_2996 -> (match (()) with
| () -> begin
(push_env ())
end))


let reset_mark_env : Prims.unit  ->  Prims.unit = (fun _83_2997 -> (match (()) with
| () -> begin
(pop_env ())
end))


let commit_mark_env : Prims.unit  ->  Prims.unit = (fun _83_2998 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| (hd)::(_83_3001)::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _83_3006 -> begin
(FStar_All.failwith "Impossible")
end)
end))


let init : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (

let _83_3008 = (init_env tcenv)
in (

let _83_3010 = (FStar_SMTEncoding_Z3.init ())
in (FStar_SMTEncoding_Z3.giveZ3 ((FStar_SMTEncoding_Term.DefPrelude)::[])))))


let push : Prims.string  ->  Prims.unit = (fun msg -> (

let _83_3013 = (push_env ())
in (

let _83_3015 = (varops.push ())
in (FStar_SMTEncoding_Z3.push msg))))


let pop : Prims.string  ->  Prims.unit = (fun msg -> (

let _83_3018 = (let _173_2210 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _173_2210))
in (

let _83_3020 = (varops.pop ())
in (FStar_SMTEncoding_Z3.pop msg))))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _83_3023 = (mark_env ())
in (

let _83_3025 = (varops.mark ())
in (FStar_SMTEncoding_Z3.mark msg))))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _83_3028 = (reset_mark_env ())
in (

let _83_3030 = (varops.reset_mark ())
in (FStar_SMTEncoding_Z3.reset_mark msg))))


let commit_mark = (fun msg -> (

let _83_3033 = (commit_mark_env ())
in (

let _83_3035 = (varops.commit_mark ())
in (FStar_SMTEncoding_Z3.commit_mark msg))))


let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (

let caption = (fun decls -> if (FStar_Options.log_queries ()) then begin
(let _173_2226 = (let _173_2225 = (let _173_2224 = (let _173_2223 = (let _173_2222 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _173_2222 (FStar_List.map FStar_Syntax_Print.lid_to_string)))
in (FStar_All.pipe_right _173_2223 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " _173_2224))
in FStar_SMTEncoding_Term.Caption (_173_2225))
in (_173_2226)::decls)
end else begin
decls
end)
in (

let env = (get_env tcenv)
in (

let _83_3044 = (encode_sigelt env se)
in (match (_83_3044) with
| (decls, env) -> begin
(

let _83_3045 = (set_env env)
in (let _173_2227 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 _173_2227)))
end)))))


let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let _83_3050 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(let _173_2232 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name _173_2232))
end else begin
()
end
in (

let env = (get_env tcenv)
in (

let _83_3057 = (encode_signature (

let _83_3053 = env
in {bindings = _83_3053.bindings; depth = _83_3053.depth; tcenv = _83_3053.tcenv; warn = false; cache = _83_3053.cache; nolabels = _83_3053.nolabels; use_zfuel_name = _83_3053.use_zfuel_name; encode_non_total_function_typ = _83_3053.encode_non_total_function_typ}) modul.FStar_Syntax_Syntax.exports)
in (match (_83_3057) with
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

let _83_3063 = (set_env (

let _83_3061 = env
in {bindings = _83_3061.bindings; depth = _83_3061.depth; tcenv = _83_3061.tcenv; warn = true; cache = _83_3061.cache; nolabels = _83_3061.nolabels; use_zfuel_name = _83_3061.use_zfuel_name; encode_non_total_function_typ = _83_3061.encode_non_total_function_typ}))
in (

let _83_3065 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end else begin
()
end
in (

let decls = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls)))))
end))))))


let encode_query : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_SMTEncoding_Term.decl Prims.list * label Prims.list * FStar_SMTEncoding_Term.decl * FStar_SMTEncoding_Term.decl Prims.list) = (fun use_env_msg tcenv q -> (

let env = (get_env tcenv)
in (

let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (

let _83_3094 = (

let rec aux = (fun bindings -> (match (bindings) with
| (FStar_TypeChecker_Env.Binding_var (x))::rest -> begin
(

let _83_3083 = (aux rest)
in (match (_83_3083) with
| (out, rest) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (let _173_2254 = (let _173_2253 = (FStar_Syntax_Syntax.mk_binder (

let _83_3085 = x
in {FStar_Syntax_Syntax.ppname = _83_3085.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _83_3085.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_173_2253)::out)
in (_173_2254, rest)))
end))
end
| _83_3088 -> begin
([], bindings)
end))
in (

let _83_3091 = (aux bindings)
in (match (_83_3091) with
| (closing, bindings) -> begin
(let _173_2255 = (FStar_Syntax_Util.close_forall (FStar_List.rev closing) q)
in (_173_2255, bindings))
end)))
in (match (_83_3094) with
| (q, bindings) -> begin
(

let _83_3103 = (let _173_2257 = (FStar_List.filter (fun _83_22 -> (match (_83_22) with
| FStar_TypeChecker_Env.Binding_sig (_83_3097) -> begin
false
end
| _83_3100 -> begin
true
end)) bindings)
in (encode_env_bindings env _173_2257))
in (match (_83_3103) with
| (env_decls, env) -> begin
(

let _83_3104 = if ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) then begin
(let _173_2258 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" _173_2258))
end else begin
()
end
in (

let _83_3108 = (encode_formula q env)
in (match (_83_3108) with
| (phi, qdecls) -> begin
(

let _83_3113 = (let _173_2259 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg _173_2259 phi))
in (match (_83_3113) with
| (phi, labels, _83_3112) -> begin
(

let _83_3116 = (encode_labels labels)
in (match (_83_3116) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append (FStar_List.append env_decls label_prefix) qdecls)
in (

let qry = (let _173_2263 = (let _173_2262 = (FStar_SMTEncoding_Term.mkNot phi)
in (let _173_2261 = (let _173_2260 = (varops.fresh "@query")
in Some (_173_2260))
in (_173_2262, Some ("query"), _173_2261)))
in FStar_SMTEncoding_Term.Assume (_173_2263))
in (

let suffix = (FStar_List.append label_suffix ((FStar_SMTEncoding_Term.Echo ("Done!"))::[]))
in (query_prelude, labels, qry, suffix))))
end))
end))
end)))
end))
end)))))


let is_trivial : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun tcenv q -> (

let env = (get_env tcenv)
in (

let _83_3123 = (push "query")
in (

let _83_3128 = (encode_formula q env)
in (match (_83_3128) with
| (f, _83_3127) -> begin
(

let _83_3129 = (pop "query")
in (match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _83_3133) -> begin
true
end
| _83_3137 -> begin
false
end))
end)))))




