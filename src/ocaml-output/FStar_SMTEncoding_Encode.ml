
open Prims

let add_fuel = (fun x tl -> if (FStar_Options.unthrottle_inductives ()) then begin
tl
end else begin
(x)::tl
end)


let withenv = (fun c _84_30 -> (match (_84_30) with
| (a, b) -> begin
(a, b, c)
end))


let vargs = (fun args -> (FStar_List.filter (fun _84_1 -> (match (_84_1) with
| (FStar_Util.Inl (_84_34), _84_37) -> begin
false
end
| _84_40 -> begin
true
end)) args))


let subst_lcomp_opt = (fun s l -> (match (l) with
| Some (FStar_Util.Inl (l)) -> begin
(let _175_12 = (let _175_11 = (let _175_10 = (let _175_9 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp s _175_9))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _175_10))
in FStar_Util.Inl (_175_11))
in Some (_175_12))
end
| _84_47 -> begin
l
end))


let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s '\'' '_'))


let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun lid a -> (

let a = (

let _84_51 = a
in (let _175_19 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _175_19; FStar_Syntax_Syntax.index = _84_51.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _84_51.FStar_Syntax_Syntax.sort}))
in (let _175_20 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str a.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (FStar_All.pipe_left escape _175_20))))


let primitive_projector_by_pos : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (

let fail = (fun _84_58 -> (match (()) with
| () -> begin
(let _175_30 = (let _175_29 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" _175_29 lid.FStar_Ident.str))
in (FStar_All.failwith _175_30))
end))
in (

let _84_62 = (FStar_TypeChecker_Env.lookup_datacon env lid)
in (match (_84_62) with
| (_84_60, t) -> begin
(match ((let _175_31 = (FStar_Syntax_Subst.compress t)
in _175_31.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _84_70 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_84_70) with
| (binders, _84_69) -> begin
if ((i < 0) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(

let b = (FStar_List.nth binders i)
in (mk_term_projector_name lid (Prims.fst b)))
end
end))
end
| _84_73 -> begin
(fail ())
end)
end))))


let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (let _175_37 = (let _175_36 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str _175_36))
in (FStar_All.pipe_left escape _175_37)))


let mk_term_projector : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun lid a -> (let _175_43 = (let _175_42 = (mk_term_projector_name lid a)
in (_175_42, FStar_SMTEncoding_Term.Arrow ((FStar_SMTEncoding_Term.Term_sort, FStar_SMTEncoding_Term.Term_sort))))
in (FStar_SMTEncoding_Term.mkFreeV _175_43)))


let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_SMTEncoding_Term.term = (fun lid i -> (let _175_49 = (let _175_48 = (mk_term_projector_name_by_pos lid i)
in (_175_48, FStar_SMTEncoding_Term.Arrow ((FStar_SMTEncoding_Term.Term_sort, FStar_SMTEncoding_Term.Term_sort))))
in (FStar_SMTEncoding_Term.mkFreeV _175_49)))


let mk_data_tester = (fun env l x -> (FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x))


type varops_t =
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; mark : Prims.unit  ->  Prims.unit; reset_mark : Prims.unit  ->  Prims.unit; commit_mark : Prims.unit  ->  Prims.unit; new_var : FStar_Ident.ident  ->  Prims.int  ->  Prims.string; new_fvar : FStar_Ident.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_SMTEncoding_Term.term; next_id : Prims.unit  ->  Prims.int}


let is_Mkvarops_t : varops_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkvarops_t"))))


let varops : varops_t = (

let initial_ctr = 100
in (

let ctr = (FStar_Util.mk_ref initial_ctr)
in (

let new_scope = (fun _84_97 -> (match (()) with
| () -> begin
(let _175_153 = (FStar_Util.smap_create 100)
in (let _175_152 = (FStar_Util.smap_create 100)
in (_175_153, _175_152)))
end))
in (

let scopes = (let _175_155 = (let _175_154 = (new_scope ())
in (_175_154)::[])
in (FStar_Util.mk_ref _175_155))
in (

let mk_unique = (fun y -> (

let y = (escape y)
in (

let y = (match ((let _175_159 = (FStar_ST.read scopes)
in (FStar_Util.find_map _175_159 (fun _84_105 -> (match (_84_105) with
| (names, _84_104) -> begin
(FStar_Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_84_108) -> begin
(

let _84_110 = (FStar_Util.incr ctr)
in (let _175_161 = (let _175_160 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _175_160))
in (Prims.strcat (Prims.strcat y "__") _175_161)))
end)
in (

let top_scope = (let _175_163 = (let _175_162 = (FStar_ST.read scopes)
in (FStar_List.hd _175_162))
in (FStar_All.pipe_left Prims.fst _175_163))
in (

let _84_114 = (FStar_Util.smap_add top_scope y true)
in y)))))
in (

let new_var = (fun pp rn -> (let _175_170 = (let _175_168 = (FStar_All.pipe_left mk_unique pp.FStar_Ident.idText)
in (Prims.strcat _175_168 "__"))
in (let _175_169 = (FStar_Util.string_of_int rn)
in (Prims.strcat _175_170 _175_169))))
in (

let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (

let next_id = (fun _84_122 -> (match (()) with
| () -> begin
(

let _84_123 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end))
in (

let fresh = (fun pfx -> (let _175_178 = (let _175_177 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _175_177))
in (FStar_Util.format2 "%s_%s" pfx _175_178)))
in (

let string_const = (fun s -> (match ((let _175_182 = (FStar_ST.read scopes)
in (FStar_Util.find_map _175_182 (fun _84_132 -> (match (_84_132) with
| (_84_130, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))) with
| Some (f) -> begin
f
end
| None -> begin
(

let id = (next_id ())
in (

let f = (let _175_183 = (FStar_SMTEncoding_Term.mk_String_const id)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString _175_183))
in (

let top_scope = (let _175_185 = (let _175_184 = (FStar_ST.read scopes)
in (FStar_List.hd _175_184))
in (FStar_All.pipe_left Prims.snd _175_185))
in (

let _84_139 = (FStar_Util.smap_add top_scope s f)
in f))))
end))
in (

let push = (fun _84_142 -> (match (()) with
| () -> begin
(let _175_190 = (let _175_189 = (new_scope ())
in (let _175_188 = (FStar_ST.read scopes)
in (_175_189)::_175_188))
in (FStar_ST.op_Colon_Equals scopes _175_190))
end))
in (

let pop = (fun _84_144 -> (match (()) with
| () -> begin
(let _175_194 = (let _175_193 = (FStar_ST.read scopes)
in (FStar_List.tl _175_193))
in (FStar_ST.op_Colon_Equals scopes _175_194))
end))
in (

let mark = (fun _84_146 -> (match (()) with
| () -> begin
(push ())
end))
in (

let reset_mark = (fun _84_148 -> (match (()) with
| () -> begin
(pop ())
end))
in (

let commit_mark = (fun _84_150 -> (match (()) with
| () -> begin
(match ((FStar_ST.read scopes)) with
| ((hd1, hd2))::((next1, next2))::tl -> begin
(

let _84_163 = (FStar_Util.smap_fold hd1 (fun key value v -> (FStar_Util.smap_add next1 key value)) ())
in (

let _84_168 = (FStar_Util.smap_fold hd2 (fun key value v -> (FStar_Util.smap_add next2 key value)) ())
in (FStar_ST.op_Colon_Equals scopes (((next1, next2))::tl))))
end
| _84_171 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id})))))))))))))))


let unmangle : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv = (fun x -> (

let _84_173 = x
in (let _175_209 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _175_209; FStar_Syntax_Syntax.index = _84_173.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _84_173.FStar_Syntax_Syntax.sort})))


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
| Binding_var (_84_177) -> begin
_84_177
end))


let ___Binding_fvar____0 = (fun projectee -> (match (projectee) with
| Binding_fvar (_84_180) -> begin
_84_180
end))


let binder_of_eithervar = (fun v -> (v, None))


type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_TypeChecker_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_SMTEncoding_Term.sort Prims.list * FStar_SMTEncoding_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}


let is_Mkenv_t : env_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_t"))))


let print_env : env_t  ->  Prims.string = (fun e -> (let _175_267 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun _84_2 -> (match (_84_2) with
| Binding_var (x, _84_195) -> begin
(FStar_Syntax_Print.bv_to_string x)
end
| Binding_fvar (l, _84_200, _84_202, _84_204) -> begin
(FStar_Syntax_Print.lid_to_string l)
end))))
in (FStar_All.pipe_right _175_267 (FStar_String.concat ", "))))


let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))


let caption_t : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.string Prims.option = (fun env t -> if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _175_277 = (FStar_Syntax_Print.term_to_string t)
in Some (_175_277))
end else begin
None
end)


let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (

let xsym = (varops.fresh x)
in (let _175_282 = (FStar_SMTEncoding_Term.mkFreeV (xsym, s))
in (xsym, _175_282))))


let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (let _175_287 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _175_287))
in (

let y = (FStar_SMTEncoding_Term.mkFreeV (ysym, FStar_SMTEncoding_Term.Term_sort))
in (ysym, y, (

let _84_218 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _84_218.tcenv; warn = _84_218.warn; cache = _84_218.cache; nolabels = _84_218.nolabels; use_zfuel_name = _84_218.use_zfuel_name; encode_non_total_function_typ = _84_218.encode_non_total_function_typ})))))


let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (

let y = (FStar_SMTEncoding_Term.mkApp (ysym, []))
in (ysym, y, (

let _84_224 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = _84_224.depth; tcenv = _84_224.tcenv; warn = _84_224.warn; cache = _84_224.cache; nolabels = _84_224.nolabels; use_zfuel_name = _84_224.use_zfuel_name; encode_non_total_function_typ = _84_224.encode_non_total_function_typ})))))


let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (

let _84_229 = env
in {bindings = (Binding_var ((x, t)))::env.bindings; depth = _84_229.depth; tcenv = _84_229.tcenv; warn = _84_229.warn; cache = _84_229.cache; nolabels = _84_229.nolabels; use_zfuel_name = _84_229.use_zfuel_name; encode_non_total_function_typ = _84_229.encode_non_total_function_typ}))


let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (match ((lookup_binding env (fun _84_3 -> (match (_84_3) with
| Binding_var (b, t) when (FStar_Syntax_Syntax.bv_eq b a) -> begin
Some ((b, t))
end
| _84_239 -> begin
None
end)))) with
| None -> begin
(let _175_304 = (let _175_303 = (FStar_Syntax_Print.bv_to_string a)
in (FStar_Util.format1 "Bound term variable not found: %s" _175_303))
in (FStar_All.failwith _175_304))
end
| Some (b, t) -> begin
t
end))


let new_term_constant_and_tok_from_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * Prims.string * env_t) = (fun env x -> (

let fname = (varops.new_fvar x)
in (

let ftok = (Prims.strcat fname "@tok")
in (let _175_315 = (

let _84_249 = env
in (let _175_314 = (let _175_313 = (let _175_312 = (let _175_311 = (let _175_310 = (FStar_SMTEncoding_Term.mkApp (ftok, []))
in (FStar_All.pipe_left (fun _175_309 -> Some (_175_309)) _175_310))
in (x, fname, _175_311, None))
in Binding_fvar (_175_312))
in (_175_313)::env.bindings)
in {bindings = _175_314; depth = _84_249.depth; tcenv = _84_249.tcenv; warn = _84_249.warn; cache = _84_249.cache; nolabels = _84_249.nolabels; use_zfuel_name = _84_249.use_zfuel_name; encode_non_total_function_typ = _84_249.encode_non_total_function_typ}))
in (fname, ftok, _175_315)))))


let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun _84_4 -> (match (_84_4) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some ((t1, t2, t3))
end
| _84_261 -> begin
None
end))))


let contains_name : env_t  ->  Prims.string  ->  Prims.bool = (fun env s -> (let _175_326 = (lookup_binding env (fun _84_5 -> (match (_84_5) with
| Binding_fvar (b, t1, t2, t3) when (b.FStar_Ident.str = s) -> begin
Some (())
end
| _84_272 -> begin
None
end)))
in (FStar_All.pipe_right _175_326 FStar_Option.isSome)))


let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _175_332 = (let _175_331 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" _175_331))
in (FStar_All.failwith _175_332))
end
| Some (s) -> begin
s
end))


let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (

let _84_282 = env
in {bindings = (Binding_fvar ((x, fname, ftok, None)))::env.bindings; depth = _84_282.depth; tcenv = _84_282.tcenv; warn = _84_282.warn; cache = _84_282.cache; nolabels = _84_282.nolabels; use_zfuel_name = _84_282.use_zfuel_name; encode_non_total_function_typ = _84_282.encode_non_total_function_typ}))


let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (

let _84_291 = (lookup_lid env x)
in (match (_84_291) with
| (t1, t2, _84_290) -> begin
(

let t3 = (let _175_349 = (let _175_348 = (let _175_347 = (FStar_SMTEncoding_Term.mkApp ("ZFuel", []))
in (_175_347)::[])
in (f, _175_348))
in (FStar_SMTEncoding_Term.mkApp _175_349))
in (

let _84_293 = env
in {bindings = (Binding_fvar ((x, t1, t2, Some (t3))))::env.bindings; depth = _84_293.depth; tcenv = _84_293.tcenv; warn = _84_293.warn; cache = _84_293.cache; nolabels = _84_293.nolabels; use_zfuel_name = _84_293.use_zfuel_name; encode_non_total_function_typ = _84_293.encode_non_total_function_typ}))
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
| _84_306 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (_84_310, (fuel)::[]) -> begin
if (let _175_355 = (let _175_354 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right _175_354 Prims.fst))
in (FStar_Util.starts_with _175_355 "fuel")) then begin
(let _175_358 = (let _175_357 = (FStar_SMTEncoding_Term.mkFreeV (name, FStar_SMTEncoding_Term.Term_sort))
in (FStar_SMTEncoding_Term.mk_ApplyTF _175_357 fuel))
in (FStar_All.pipe_left (fun _175_356 -> Some (_175_356)) _175_358))
end else begin
Some (t)
end
end
| _84_316 -> begin
Some (t)
end)
end
| _84_318 -> begin
None
end)
end)
end))


let lookup_free_var = (fun env a -> (match ((try_lookup_free_var env a.FStar_Syntax_Syntax.v)) with
| Some (t) -> begin
t
end
| None -> begin
(let _175_362 = (let _175_361 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _175_361))
in (FStar_All.failwith _175_362))
end))


let lookup_free_var_name = (fun env a -> (

let _84_331 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_84_331) with
| (x, _84_328, _84_330) -> begin
x
end)))


let lookup_free_var_sym = (fun env a -> (

let _84_337 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_84_337) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.hash = _84_341; FStar_SMTEncoding_Term.freevars = _84_339}) when env.use_zfuel_name -> begin
(g, zf)
end
| _84_349 -> begin
(match (sym) with
| None -> begin
(FStar_SMTEncoding_Term.Var (name), [])
end
| Some (sym) -> begin
(match (sym.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, (fuel)::[]) -> begin
(g, (fuel)::[])
end
| _84_359 -> begin
(FStar_SMTEncoding_Term.Var (name), [])
end)
end)
end)
end)))


let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun _84_6 -> (match (_84_6) with
| Binding_fvar (_84_364, nm', tok, _84_368) when (nm = nm') -> begin
tok
end
| _84_372 -> begin
None
end))))


let mkForall_fuel' = (fun n _84_377 -> (match (_84_377) with
| (pats, vars, body) -> begin
(

let fallback = (fun _84_379 -> (match (()) with
| () -> begin
(FStar_SMTEncoding_Term.mkForall (pats, vars, body))
end))
in if (FStar_Options.unthrottle_inductives ()) then begin
(fallback ())
end else begin
(

let _84_382 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_84_382) with
| (fsym, fterm) -> begin
(

let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Term.mkApp ("HasTypeFuel", (fterm)::args))
end
| _84_392 -> begin
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
(let _175_379 = (add_fuel guards)
in (FStar_SMTEncoding_Term.mk_and_l _175_379))
end
| _84_405 -> begin
(let _175_380 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _175_380 FStar_List.hd))
end)
in (FStar_SMTEncoding_Term.mkImp (guard, body')))
end
| _84_408 -> begin
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
(let _175_386 = (FStar_TypeChecker_Env.lookup_definition FStar_TypeChecker_Env.OnlyInline env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _175_386 FStar_Option.isNone))
end
| _84_447 -> begin
false
end)))


let head_redex : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (match ((let _175_391 = (FStar_Syntax_Util.un_uinst t)
in _175_391.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_84_451) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(let _175_392 = (FStar_TypeChecker_Env.lookup_definition FStar_TypeChecker_Env.OnlyInline env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _175_392 FStar_Option.isSome))
end
| _84_456 -> begin
false
end))


let whnf : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> if (head_normal env t) then begin
t
end else begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
end)


let norm : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t))


let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (let _175_405 = (let _175_403 = (FStar_Syntax_Syntax.null_binder t)
in (_175_403)::[])
in (let _175_404 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Util.abs _175_405 _175_404 None))))


let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(let _175_412 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out _175_412))
end
| s -> begin
(

let _84_468 = ()
in (let _175_413 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTT out _175_413)))
end)) e)))


let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Term.mk_ApplyTT e)))


let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun _84_7 -> (match (_84_7) with
| (FStar_SMTEncoding_Term.Var ("ApplyTT")) | (FStar_SMTEncoding_Term.Var ("ApplyTF")) -> begin
true
end
| _84_478 -> begin
false
end))


let is_eta : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env vars t -> (

let rec aux = (fun t xs -> (match ((t.FStar_SMTEncoding_Term.tm, xs)) with
| (FStar_SMTEncoding_Term.App (app, (f)::({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.hash = _84_489; FStar_SMTEncoding_Term.freevars = _84_487})::[]), (x)::xs) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), _84_507) -> begin
if (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v)
end
| _84_514 -> begin
false
end)) args vars)) then begin
(tok_of_name env f)
end else begin
None
end
end
| (_84_516, []) -> begin
(

let fvs = (FStar_SMTEncoding_Term.free_variables t)
in if (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (not ((FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)))))) then begin
Some (t)
end else begin
None
end)
end
| _84_522 -> begin
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


let encode_const : FStar_Const.sconst  ->  FStar_SMTEncoding_Term.term = (fun _84_8 -> (match (_84_8) with
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
(let _175_470 = (let _175_469 = (let _175_468 = (let _175_467 = (FStar_SMTEncoding_Term.mkInteger' (FStar_Util.int_of_char c))
in (FStar_SMTEncoding_Term.boxInt _175_467))
in (_175_468)::[])
in ("FStar.Char.Char", _175_469))
in (FStar_SMTEncoding_Term.mkApp _175_470))
end
| FStar_Const.Const_int (i, None) -> begin
(let _175_471 = (FStar_SMTEncoding_Term.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt _175_471))
end
| FStar_Const.Const_int (i, Some (_84_542)) -> begin
(FStar_All.failwith "Machine integers should be desugared")
end
| FStar_Const.Const_string (bytes, _84_548) -> begin
(let _175_472 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _175_472))
end
| FStar_Const.Const_range (r) -> begin
FStar_SMTEncoding_Term.mk_Range_const
end
| FStar_Const.Const_effect -> begin
FStar_SMTEncoding_Term.mk_Term_type
end
| c -> begin
(let _175_474 = (let _175_473 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" _175_473))
in (FStar_All.failwith _175_474))
end))


let as_function_typ : env_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (

let rec aux = (fun norm t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_84_562) -> begin
t
end
| FStar_Syntax_Syntax.Tm_refine (_84_565) -> begin
(let _175_483 = (FStar_Syntax_Util.unrefine t)
in (aux true _175_483))
end
| _84_568 -> begin
if norm then begin
(let _175_484 = (whnf env t)
in (aux false _175_484))
end else begin
(let _175_487 = (let _175_486 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (let _175_485 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _175_486 _175_485)))
in (FStar_All.failwith _175_487))
end
end)))
in (aux true t0)))


let curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun k -> (

let k = (FStar_Syntax_Subst.compress k)
in (match (k.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| _84_576 -> begin
(let _175_490 = (FStar_Syntax_Syntax.mk_Total k)
in ([], _175_490))
end)))


let rec encode_binders : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> (

let _84_580 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _175_538 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" _175_538))
end else begin
()
end
in (

let _84_608 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _84_587 b -> (match (_84_587) with
| (vars, guards, env, decls, names) -> begin
(

let _84_602 = (

let x = (unmangle (Prims.fst b))
in (

let _84_593 = (gen_term_var env x)
in (match (_84_593) with
| (xxsym, xx, env') -> begin
(

let _84_596 = (let _175_541 = (norm env x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt _175_541 env xx))
in (match (_84_596) with
| (guard_x_t, decls') -> begin
((xxsym, FStar_SMTEncoding_Term.Term_sort), guard_x_t, env', decls', x)
end))
end)))
in (match (_84_602) with
| (v, g, env, decls', n) -> begin
((v)::vars, (g)::guards, env, (FStar_List.append decls decls'), (n)::names)
end))
end)) ([], [], env, [], [])))
in (match (_84_608) with
| (vars, guards, env, decls, names) -> begin
((FStar_List.rev vars), (FStar_List.rev guards), env, decls, (FStar_List.rev names))
end))))
and encode_term_pred : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let _84_615 = (encode_term t env)
in (match (_84_615) with
| (t, decls) -> begin
(let _175_546 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t)
in (_175_546, decls))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let _84_622 = (encode_term t env)
in (match (_84_622) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _175_551 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t)
in (_175_551, decls))
end
| Some (f) -> begin
(let _175_552 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t)
in (_175_552, decls))
end)
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let t0 = (FStar_Syntax_Subst.compress t)
in (

let _84_629 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _175_557 = (FStar_Syntax_Print.tag_of_term t)
in (let _175_556 = (FStar_Syntax_Print.tag_of_term t0)
in (let _175_555 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" _175_557 _175_556 _175_555))))
end else begin
()
end
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _175_562 = (let _175_561 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (let _175_560 = (FStar_Syntax_Print.tag_of_term t0)
in (let _175_559 = (FStar_Syntax_Print.term_to_string t0)
in (let _175_558 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _175_561 _175_560 _175_559 _175_558)))))
in (FStar_All.failwith _175_562))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _175_564 = (let _175_563 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" _175_563))
in (FStar_All.failwith _175_564))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, k, _84_640) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_meta (t, _84_645) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t = (lookup_term_var env x)
in (t, []))
end
| FStar_Syntax_Syntax.Tm_fvar (v) -> begin
(let _175_565 = (lookup_free_var env v.FStar_Syntax_Syntax.fv_name)
in (_175_565, []))
end
| FStar_Syntax_Syntax.Tm_type (_84_654) -> begin
(FStar_SMTEncoding_Term.mk_Term_type, [])
end
| FStar_Syntax_Syntax.Tm_uinst (t, _84_658) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(let _175_566 = (encode_const c)
in (_175_566, []))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _84_669 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_84_669) with
| (binders, res) -> begin
if ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res)) then begin
(

let _84_676 = (encode_binders None binders env)
in (match (_84_676) with
| (vars, guards, env', decls, _84_675) -> begin
(

let fsym = (let _175_567 = (varops.fresh "f")
in (_175_567, FStar_SMTEncoding_Term.Term_sort))
in (

let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (

let app = (mk_Apply f vars)
in (

let _84_682 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv res)
in (match (_84_682) with
| (pre_opt, res_t) -> begin
(

let _84_685 = (encode_term_pred None res_t env' app)
in (match (_84_685) with
| (res_pred, decls') -> begin
(

let _84_694 = (match (pre_opt) with
| None -> begin
(let _175_568 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_175_568, []))
end
| Some (pre) -> begin
(

let _84_691 = (encode_formula pre env')
in (match (_84_691) with
| (guard, decls0) -> begin
(let _175_569 = (FStar_SMTEncoding_Term.mk_and_l ((guard)::guards))
in (_175_569, decls0))
end))
end)
in (match (_84_694) with
| (guards, guard_decls) -> begin
(

let t_interp = (let _175_571 = (let _175_570 = (FStar_SMTEncoding_Term.mkImp (guards, res_pred))
in (((app)::[])::[], vars, _175_570))
in (FStar_SMTEncoding_Term.mkForall _175_571))
in (

let cvars = (let _175_573 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right _175_573 (FStar_List.filter (fun _84_699 -> (match (_84_699) with
| (x, _84_698) -> begin
(x <> (Prims.fst fsym))
end)))))
in (

let tkey = (FStar_SMTEncoding_Term.mkForall ([], (fsym)::cvars, t_interp))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t', sorts, _84_705) -> begin
(let _175_576 = (let _175_575 = (let _175_574 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in (t', _175_574))
in (FStar_SMTEncoding_Term.mkApp _175_575))
in (_175_576, []))
end
| None -> begin
(

let tsym = (varops.fresh "Tm_arrow")
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let caption = if (FStar_Options.log_queries ()) then begin
(let _175_577 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in Some (_175_577))
end else begin
None
end
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun ((tsym, cvar_sorts, FStar_SMTEncoding_Term.Term_sort, caption))
in (

let t = (let _175_579 = (let _175_578 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (tsym, _175_578))
in (FStar_SMTEncoding_Term.mkApp _175_579))
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let k_assumption = (

let a_name = Some ((Prims.strcat "kinding_" tsym))
in (let _175_581 = (let _175_580 = (FStar_SMTEncoding_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (_175_580, a_name, a_name))
in FStar_SMTEncoding_Term.Assume (_175_581)))
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t)
in (

let pre_typing = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in (let _175_588 = (let _175_587 = (let _175_586 = (let _175_585 = (let _175_584 = (let _175_583 = (let _175_582 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _175_582))
in (f_has_t, _175_583))
in (FStar_SMTEncoding_Term.mkImp _175_584))
in (((f_has_t)::[])::[], (fsym)::cvars, _175_585))
in (mkForall_fuel _175_586))
in (_175_587, Some ("pre-typing for functions"), a_name))
in FStar_SMTEncoding_Term.Assume (_175_588)))
in (

let t_interp = (

let a_name = Some ((Prims.strcat "interpretation_" tsym))
in (let _175_592 = (let _175_591 = (let _175_590 = (let _175_589 = (FStar_SMTEncoding_Term.mkIff (f_has_t_z, t_interp))
in (((f_has_t_z)::[])::[], (fsym)::cvars, _175_589))
in (FStar_SMTEncoding_Term.mkForall _175_590))
in (_175_591, a_name, a_name))
in FStar_SMTEncoding_Term.Assume (_175_592)))
in (

let t_decls = (FStar_List.append (FStar_List.append (FStar_List.append ((tdecl)::decls) decls') guard_decls) ((k_assumption)::(pre_typing)::(t_interp)::[]))
in (

let _84_724 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (tsym, cvar_sorts, t_decls))
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
in (let _175_594 = (let _175_593 = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (_175_593, Some ("Typing for non-total arrows"), a_name))
in FStar_SMTEncoding_Term.Assume (_175_594)))
in (

let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)
in (

let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let t_interp = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in (let _175_601 = (let _175_600 = (let _175_599 = (let _175_598 = (let _175_597 = (let _175_596 = (let _175_595 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _175_595))
in (f_has_t, _175_596))
in (FStar_SMTEncoding_Term.mkImp _175_597))
in (((f_has_t)::[])::[], (fsym)::[], _175_598))
in (mkForall_fuel _175_599))
in (_175_600, a_name, a_name))
in FStar_SMTEncoding_Term.Assume (_175_601)))
in (t, (tdecl)::(t_kinding)::(t_interp)::[])))))))))
end
end))
end
| FStar_Syntax_Syntax.Tm_refine (_84_737) -> begin
(

let _84_757 = (match ((FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.tk = _84_744; FStar_Syntax_Syntax.pos = _84_742; FStar_Syntax_Syntax.vars = _84_740} -> begin
(

let _84_752 = (FStar_Syntax_Subst.open_term (((x, None))::[]) f)
in (match (_84_752) with
| (b, f) -> begin
(let _175_603 = (let _175_602 = (FStar_List.hd b)
in (Prims.fst _175_602))
in (_175_603, f))
end))
end
| _84_754 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_84_757) with
| (x, f) -> begin
(

let _84_760 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (_84_760) with
| (base_t, decls) -> begin
(

let _84_764 = (gen_term_var env x)
in (match (_84_764) with
| (x, xtm, env') -> begin
(

let _84_767 = (encode_formula f env')
in (match (_84_767) with
| (refinement, decls') -> begin
(

let _84_770 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_84_770) with
| (fsym, fterm) -> begin
(

let encoding = (let _175_605 = (let _175_604 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in (_175_604, refinement))
in (FStar_SMTEncoding_Term.mkAnd _175_605))
in (

let cvars = (let _175_607 = (FStar_SMTEncoding_Term.free_variables encoding)
in (FStar_All.pipe_right _175_607 (FStar_List.filter (fun _84_775 -> (match (_84_775) with
| (y, _84_774) -> begin
((y <> x) && (y <> fsym))
end)))))
in (

let xfv = (x, FStar_SMTEncoding_Term.Term_sort)
in (

let ffv = (fsym, FStar_SMTEncoding_Term.Fuel_sort)
in (

let tkey = (FStar_SMTEncoding_Term.mkForall ([], (ffv)::(xfv)::cvars, encoding))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _84_782, _84_784) -> begin
(let _175_610 = (let _175_609 = (let _175_608 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in (t, _175_608))
in (FStar_SMTEncoding_Term.mkApp _175_609))
in (_175_610, []))
end
| None -> begin
(

let tsym = (varops.fresh "Tm_refine")
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun ((tsym, cvar_sorts, FStar_SMTEncoding_Term.Term_sort, None))
in (

let t = (let _175_612 = (let _175_611 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (tsym, _175_611))
in (FStar_SMTEncoding_Term.mkApp _175_612))
in (

let x_has_t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let t_kinding = (let _175_614 = (let _175_613 = (FStar_SMTEncoding_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (_175_613, Some ("refinement kinding"), Some ((Prims.strcat "refinement_kinding_" tsym))))
in FStar_SMTEncoding_Term.Assume (_175_614))
in (

let t_interp = (let _175_620 = (let _175_619 = (let _175_616 = (let _175_615 = (FStar_SMTEncoding_Term.mkIff (x_has_t, encoding))
in (((x_has_t)::[])::[], (ffv)::(xfv)::cvars, _175_615))
in (FStar_SMTEncoding_Term.mkForall _175_616))
in (let _175_618 = (let _175_617 = (FStar_Syntax_Print.term_to_string t0)
in Some (_175_617))
in (_175_619, _175_618, Some ((Prims.strcat "refinement_interpretation_" tsym)))))
in FStar_SMTEncoding_Term.Assume (_175_620))
in (

let t_decls = (FStar_List.append (FStar_List.append decls decls') ((tdecl)::(t_kinding)::(t_interp)::[]))
in (

let _84_797 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (tsym, cvar_sorts, t_decls))
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

let ttm = (let _175_621 = (FStar_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Term.mk_Term_uvar _175_621))
in (

let _84_806 = (encode_term_pred None k env ttm)
in (match (_84_806) with
| (t_has_k, decls) -> begin
(

let d = (let _175_627 = (let _175_626 = (let _175_625 = (let _175_624 = (let _175_623 = (let _175_622 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _175_622))
in (FStar_Util.format1 "@uvar_typing_%s" _175_623))
in (varops.fresh _175_624))
in Some (_175_625))
in (t_has_k, Some ("Uvar typing"), _175_626))
in FStar_SMTEncoding_Term.Assume (_175_627))
in (ttm, (FStar_List.append decls ((d)::[]))))
end)))
end
| FStar_Syntax_Syntax.Tm_app (_84_809) -> begin
(

let _84_813 = (FStar_Syntax_Util.head_and_args t0)
in (match (_84_813) with
| (head, args_e) -> begin
(match ((let _175_629 = (let _175_628 = (FStar_Syntax_Subst.compress head)
in _175_628.FStar_Syntax_Syntax.n)
in (_175_629, args_e))) with
| (_84_815, _84_817) when (head_redex env head) -> begin
(let _175_630 = (whnf env t)
in (encode_term _175_630 env))
end
| ((FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), (_)::((v1, _))::((v2, _))::[])) | ((FStar_Syntax_Syntax.Tm_fvar (fv), (_)::((v1, _))::((v2, _))::[])) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
(

let _84_857 = (encode_term v1 env)
in (match (_84_857) with
| (v1, decls1) -> begin
(

let _84_860 = (encode_term v2 env)
in (match (_84_860) with
| (v2, decls2) -> begin
(let _175_631 = (FStar_SMTEncoding_Term.mk_LexCons v1 v2)
in (_175_631, (FStar_List.append decls1 decls2)))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), (_84_869)::(_84_866)::_84_864) -> begin
(

let e0 = (let _175_635 = (let _175_634 = (let _175_633 = (let _175_632 = (FStar_List.hd args_e)
in (_175_632)::[])
in (head, _175_633))
in FStar_Syntax_Syntax.Tm_app (_175_634))
in (FStar_Syntax_Syntax.mk _175_635 None head.FStar_Syntax_Syntax.pos))
in (

let e = (let _175_638 = (let _175_637 = (let _175_636 = (FStar_List.tl args_e)
in (e0, _175_636))
in FStar_Syntax_Syntax.Tm_app (_175_637))
in (FStar_Syntax_Syntax.mk _175_638 None t0.FStar_Syntax_Syntax.pos))
in (encode_term e env)))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), ((arg, _84_878))::[]) -> begin
(

let _84_884 = (encode_term arg env)
in (match (_84_884) with
| (tm, decls) -> begin
(let _175_639 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App ((FStar_SMTEncoding_Term.Var ("Reify"), (tm)::[]))))
in (_175_639, decls))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (_84_886)), ((arg, _84_891))::[]) -> begin
(encode_term arg env)
end
| _84_896 -> begin
(

let _84_899 = (encode_args args_e env)
in (match (_84_899) with
| (args, decls) -> begin
(

let encode_partial_app = (fun ht_opt -> (

let _84_904 = (encode_term head env)
in (match (_84_904) with
| (head, decls') -> begin
(

let app_tm = (mk_Apply_args head args)
in (match (ht_opt) with
| None -> begin
(app_tm, (FStar_List.append decls decls'))
end
| Some (formals, c) -> begin
(

let _84_913 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (_84_913) with
| (formals, rest) -> begin
(

let subst = (FStar_List.map2 (fun _84_917 _84_921 -> (match ((_84_917, _84_921)) with
| ((bv, _84_916), (a, _84_920)) -> begin
FStar_Syntax_Syntax.NT ((bv, a))
end)) formals args_e)
in (

let ty = (let _175_644 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right _175_644 (FStar_Syntax_Subst.subst subst)))
in (

let _84_926 = (encode_term_pred None ty env app_tm)
in (match (_84_926) with
| (has_type, decls'') -> begin
(

let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (

let e_typing = (let _175_648 = (let _175_647 = (FStar_SMTEncoding_Term.mkForall (((has_type)::[])::[], cvars, has_type))
in (let _175_646 = (let _175_645 = (varops.fresh "@partial_app_typing_")
in Some (_175_645))
in (_175_647, Some ("Partial app typing"), _175_646)))
in FStar_SMTEncoding_Term.Assume (_175_648))
in (app_tm, (FStar_List.append (FStar_List.append (FStar_List.append decls decls') decls'') ((e_typing)::[])))))
end))))
end))
end))
end)))
in (

let encode_full_app = (fun fv -> (

let _84_933 = (lookup_free_var_sym env fv)
in (match (_84_933) with
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
(let _175_652 = (let _175_651 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _175_651 Prims.snd))
in Some (_175_652))
end
| FStar_Syntax_Syntax.Tm_ascribed (_84_965, FStar_Util.Inl (t), _84_969) -> begin
Some (t)
end
| FStar_Syntax_Syntax.Tm_ascribed (_84_973, FStar_Util.Inr (c), _84_977) -> begin
Some ((FStar_Syntax_Util.comp_result c))
end
| _84_981 -> begin
None
end)
in (match (head_type) with
| None -> begin
(encode_partial_app None)
end
| Some (head_type) -> begin
(

let head_type = (let _175_653 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine _175_653))
in (

let _84_989 = (curried_arrow_formals_comp head_type)
in (match (_84_989) with
| (formals, c) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| _84_1005 -> begin
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

let _84_1014 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_84_1014) with
| (bs, body, opening) -> begin
(

let fallback = (fun _84_1016 -> (match (()) with
| () -> begin
(

let f = (varops.fresh "Tm_abs")
in (

let decl = FStar_SMTEncoding_Term.DeclFun ((f, [], FStar_SMTEncoding_Term.Term_sort, Some ("Imprecise function encoding")))
in (let _175_656 = (FStar_SMTEncoding_Term.mkFreeV (f, FStar_SMTEncoding_Term.Term_sort))
in (_175_656, (decl)::[]))))
end))
in (

let is_impure = (fun _84_9 -> (match (_84_9) with
| FStar_Util.Inl (lc) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)))
end
| FStar_Util.Inr (eff) -> begin
(let _175_659 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv eff)
in (FStar_All.pipe_right _175_659 Prims.op_Negation))
end))
in (

let codomain_eff = (fun lc -> (match (lc) with
| FStar_Util.Inl (lc) -> begin
(let _175_664 = (let _175_662 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening _175_662))
in (FStar_All.pipe_right _175_664 (fun _175_663 -> Some (_175_663))))
end
| FStar_Util.Inr (eff) -> begin
(

let new_uvar = (fun _84_1032 -> (match (()) with
| () -> begin
(let _175_667 = (FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange [] FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _175_667 Prims.fst))
end))
in if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid) then begin
(let _175_670 = (let _175_668 = (new_uvar ())
in (FStar_Syntax_Syntax.mk_Total _175_668))
in (FStar_All.pipe_right _175_670 (fun _175_669 -> Some (_175_669))))
end else begin
if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid) then begin
(let _175_673 = (let _175_671 = (new_uvar ())
in (FStar_Syntax_Syntax.mk_GTotal _175_671))
in (FStar_All.pipe_right _175_673 (fun _175_672 -> Some (_175_672))))
end else begin
None
end
end)
end))
in (match (lopt) with
| None -> begin
(

let _84_1034 = (let _175_675 = (let _175_674 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s" _175_674))
in (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos _175_675))
in (fallback ()))
end
| Some (lc) -> begin
if (is_impure lc) then begin
(fallback ())
end else begin
(

let _84_1044 = (encode_binders None bs env)
in (match (_84_1044) with
| (vars, guards, envbody, decls, _84_1043) -> begin
(

let _84_1047 = (encode_term body envbody)
in (match (_84_1047) with
| (body, decls') -> begin
(

let key_body = (let _175_679 = (let _175_678 = (let _175_677 = (let _175_676 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_175_676, body))
in (FStar_SMTEncoding_Term.mkImp _175_677))
in ([], vars, _175_678))
in (FStar_SMTEncoding_Term.mkForall _175_679))
in (

let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (

let tkey = (FStar_SMTEncoding_Term.mkForall ([], cvars, key_body))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _84_1053, _84_1055) -> begin
(let _175_682 = (let _175_681 = (let _175_680 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (t, _175_680))
in (FStar_SMTEncoding_Term.mkApp _175_681))
in (_175_682, []))
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

let f = (let _175_684 = (let _175_683 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (fsym, _175_683))
in (FStar_SMTEncoding_Term.mkApp _175_684))
in (

let app = (mk_Apply f vars)
in (

let typing_f = (match ((codomain_eff lc)) with
| None -> begin
[]
end
| Some (c) -> begin
(

let tfun = (FStar_Syntax_Util.arrow bs c)
in (

let _84_1073 = (encode_term_pred None tfun env f)
in (match (_84_1073) with
| (f_has_t, decls'') -> begin
(

let a_name = Some ((Prims.strcat "typing_" fsym))
in (let _175_688 = (let _175_687 = (let _175_686 = (let _175_685 = (FStar_SMTEncoding_Term.mkForall (((f)::[])::[], cvars, f_has_t))
in (_175_685, a_name, a_name))
in FStar_SMTEncoding_Term.Assume (_175_686))
in (_175_687)::[])
in (FStar_List.append decls'' _175_688)))
end)))
end)
in (

let interp_f = (

let a_name = Some ((Prims.strcat "interpretation_" fsym))
in (let _175_692 = (let _175_691 = (let _175_690 = (let _175_689 = (FStar_SMTEncoding_Term.mkEq (app, body))
in (((app)::[])::[], (FStar_List.append vars cvars), _175_689))
in (FStar_SMTEncoding_Term.mkForall _175_690))
in (_175_691, a_name, a_name))
in FStar_SMTEncoding_Term.Assume (_175_692)))
in (

let f_decls = (FStar_List.append (FStar_List.append (FStar_List.append decls decls') ((fdecl)::typing_f)) ((interp_f)::[]))
in (

let _84_1079 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (fsym, cvar_sorts, f_decls))
in (f, f_decls))))))))))
end)
end))))
end))
end))
end
end))))
end))
end
| FStar_Syntax_Syntax.Tm_let ((_84_1082, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_84_1094); FStar_Syntax_Syntax.lbunivs = _84_1092; FStar_Syntax_Syntax.lbtyp = _84_1090; FStar_Syntax_Syntax.lbeff = _84_1088; FStar_Syntax_Syntax.lbdef = _84_1086})::_84_1084), _84_1100) -> begin
(FStar_All.failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _84_1109; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _84_1106; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (_84_1119) -> begin
(

let _84_1121 = (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (

let e = (varops.fresh "let-rec")
in (

let decl_e = FStar_SMTEncoding_Term.DeclFun ((e, [], FStar_SMTEncoding_Term.Term_sort, None))
in (let _175_693 = (FStar_SMTEncoding_Term.mkFreeV (e, FStar_SMTEncoding_Term.Term_sort))
in (_175_693, (decl_e)::[])))))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end))))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (

let _84_1137 = (encode_term e1 env)
in (match (_84_1137) with
| (ee1, decls1) -> begin
(

let _84_1140 = (FStar_Syntax_Subst.open_term (((x, None))::[]) e2)
in (match (_84_1140) with
| (xs, e2) -> begin
(

let _84_1144 = (FStar_List.hd xs)
in (match (_84_1144) with
| (x, _84_1143) -> begin
(

let env' = (push_term_var env x ee1)
in (

let _84_1148 = (encode_body e2 env')
in (match (_84_1148) with
| (ee2, decls2) -> begin
(ee2, (FStar_List.append decls1 decls2))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (

let _84_1156 = (encode_term e env)
in (match (_84_1156) with
| (scr, decls) -> begin
(

let _84_1193 = (FStar_List.fold_right (fun b _84_1160 -> (match (_84_1160) with
| (else_case, decls) -> begin
(

let _84_1164 = (FStar_Syntax_Subst.open_branch b)
in (match (_84_1164) with
| (p, w, br) -> begin
(

let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun _84_1168 _84_1171 -> (match ((_84_1168, _84_1171)) with
| ((env0, pattern), (else_case, decls)) -> begin
(

let guard = (pattern.guard scr)
in (

let projections = (pattern.projections scr)
in (

let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env _84_1177 -> (match (_84_1177) with
| (x, t) -> begin
(push_term_var env x t)
end)) env))
in (

let _84_1187 = (match (w) with
| None -> begin
(guard, [])
end
| Some (w) -> begin
(

let _84_1184 = (encode_term w env)
in (match (_84_1184) with
| (w, decls2) -> begin
(let _175_727 = (let _175_726 = (let _175_725 = (let _175_724 = (let _175_723 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Term.mkTrue)
in (w, _175_723))
in (FStar_SMTEncoding_Term.mkEq _175_724))
in (guard, _175_725))
in (FStar_SMTEncoding_Term.mkAnd _175_726))
in (_175_727, decls2))
end))
end)
in (match (_84_1187) with
| (guard, decls2) -> begin
(

let _84_1190 = (encode_br br env)
in (match (_84_1190) with
| (br, decls3) -> begin
(let _175_728 = (FStar_SMTEncoding_Term.mkITE (guard, br, else_case))
in (_175_728, (FStar_List.append (FStar_List.append decls decls2) decls3)))
end))
end)))))
end)) patterns (else_case, decls)))
end))
end)) pats (default_case, decls))
in (match (_84_1193) with
| (match_tm, decls) -> begin
(match_tm, decls)
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _84_1199 -> begin
(let _175_731 = (encode_one_pat env pat)
in (_175_731)::[])
end))
and encode_one_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> (

let _84_1202 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _175_734 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" _175_734))
end else begin
()
end
in (

let _84_1206 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (_84_1206) with
| (vars, pat_term) -> begin
(

let _84_1218 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun _84_1209 v -> (match (_84_1209) with
| (env, vars) -> begin
(

let _84_1215 = (gen_term_var env v)
in (match (_84_1215) with
| (xx, _84_1213, env) -> begin
(env, ((v, (xx, FStar_SMTEncoding_Term.Term_sort)))::vars)
end))
end)) (env, [])))
in (match (_84_1218) with
| (env, vars) -> begin
(

let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_84_1223) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_dot_term (_)) -> begin
FStar_SMTEncoding_Term.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _175_742 = (let _175_741 = (encode_const c)
in (scrutinee, _175_741))
in (FStar_SMTEncoding_Term.mkEq _175_742))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let is_f = (mk_data_tester env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _84_1245 -> (match (_84_1245) with
| (arg, _84_1244) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _175_745 = (FStar_SMTEncoding_Term.mkApp (proj, (scrutinee)::[]))
in (mk_guard arg _175_745)))
end))))
in (FStar_SMTEncoding_Term.mk_and_l ((is_f)::sub_term_guards))))
end))
in (

let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_84_1252) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _)) | (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
((x, scrutinee))::[]
end
| FStar_Syntax_Syntax.Pat_constant (_84_1262) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(let _175_753 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _84_1272 -> (match (_84_1272) with
| (arg, _84_1271) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _175_752 = (FStar_SMTEncoding_Term.mkApp (proj, (scrutinee)::[]))
in (mk_projections arg _175_752)))
end))))
in (FStar_All.pipe_right _175_753 FStar_List.flatten))
end))
in (

let pat_term = (fun _84_1275 -> (match (()) with
| () -> begin
(encode_term pat_term env)
end))
in (

let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in (env, pattern)))))
end))
end))))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (

let _84_1291 = (FStar_All.pipe_right l (FStar_List.fold_left (fun _84_1281 _84_1285 -> (match ((_84_1281, _84_1285)) with
| ((tms, decls), (t, _84_1284)) -> begin
(

let _84_1288 = (encode_term t env)
in (match (_84_1288) with
| (t, decls') -> begin
((t)::tms, (FStar_List.append decls decls'))
end))
end)) ([], [])))
in (match (_84_1291) with
| (l, decls) -> begin
((FStar_List.rev l), decls)
end)))
and encode_function_type_as_formula : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun induction_on new_pats t env -> (

let rec list_elements = (fun e -> (

let _84_1300 = (let _175_766 = (FStar_Syntax_Util.unmeta e)
in (FStar_Syntax_Util.head_and_args _175_766))
in (match (_84_1300) with
| (head, args) -> begin
(match ((let _175_768 = (let _175_767 = (FStar_Syntax_Util.un_uinst head)
in _175_767.FStar_Syntax_Syntax.n)
in (_175_768, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), _84_1304) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid) -> begin
[]
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_84_1317)::((hd, _84_1314))::((tl, _84_1310))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid) -> begin
(let _175_769 = (list_elements tl)
in (hd)::_175_769)
end
| _84_1321 -> begin
(

let _84_1322 = (FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern")
in [])
end)
end)))
in (

let one_pat = (fun p -> (

let _84_1328 = (let _175_772 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right _175_772 FStar_Syntax_Util.head_and_args))
in (match (_84_1328) with
| (head, args) -> begin
(match ((let _175_774 = (let _175_773 = (FStar_Syntax_Util.un_uinst head)
in _175_773.FStar_Syntax_Syntax.n)
in (_175_774, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((_84_1336, _84_1338))::((e, _84_1333))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpat_lid) -> begin
(e, None)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, _84_1346))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatT_lid) -> begin
(e, None)
end
| _84_1351 -> begin
(FStar_All.failwith "Unexpected pattern term")
end)
end)))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements p)
in (

let smt_pat_or = (fun t -> (

let _84_1359 = (let _175_779 = (FStar_Syntax_Util.unmeta t)
in (FStar_All.pipe_right _175_779 FStar_Syntax_Util.head_and_args))
in (match (_84_1359) with
| (head, args) -> begin
(match ((let _175_781 = (let _175_780 = (FStar_Syntax_Util.un_uinst head)
in _175_780.FStar_Syntax_Syntax.n)
in (_175_781, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, _84_1364))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatOr_lid) -> begin
Some (e)
end
| _84_1369 -> begin
None
end)
end)))
in (match (elts) with
| (t)::[] -> begin
(match ((smt_pat_or t)) with
| Some (e) -> begin
(let _175_784 = (list_elements e)
in (FStar_All.pipe_right _175_784 (FStar_List.map (fun branch -> (let _175_783 = (list_elements branch)
in (FStar_All.pipe_right _175_783 (FStar_List.map one_pat)))))))
end
| _84_1376 -> begin
(let _175_785 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_175_785)::[])
end)
end
| _84_1378 -> begin
(let _175_786 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_175_786)::[])
end))))
in (

let _84_1412 = (match ((let _175_787 = (FStar_Syntax_Subst.compress t)
in _175_787.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _84_1385 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_84_1385) with
| (binders, c) -> begin
(

let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| ((pre, _84_1397))::((post, _84_1393))::((pats, _84_1389))::[] -> begin
(

let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _175_788 = (lemma_pats pats')
in (binders, pre, post, _175_788)))
end
| _84_1405 -> begin
(FStar_All.failwith "impos")
end))
end))
end
| _84_1407 -> begin
(FStar_All.failwith "Impos")
end)
in (match (_84_1412) with
| (binders, pre, post, patterns) -> begin
(

let _84_1419 = (encode_binders None binders env)
in (match (_84_1419) with
| (vars, guards, env, decls, _84_1418) -> begin
(

let _84_1432 = (let _175_792 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (

let _84_1429 = (let _175_791 = (FStar_All.pipe_right branch (FStar_List.map (fun _84_1424 -> (match (_84_1424) with
| (t, _84_1423) -> begin
(encode_term t (

let _84_1425 = env
in {bindings = _84_1425.bindings; depth = _84_1425.depth; tcenv = _84_1425.tcenv; warn = _84_1425.warn; cache = _84_1425.cache; nolabels = _84_1425.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _84_1425.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _175_791 FStar_List.unzip))
in (match (_84_1429) with
| (pats, decls) -> begin
(pats, decls)
end)))))
in (FStar_All.pipe_right _175_792 FStar_List.unzip))
in (match (_84_1432) with
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
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _175_795 = (let _175_794 = (FStar_SMTEncoding_Term.mkFreeV l)
in (FStar_SMTEncoding_Term.mk_Precedes _175_794 e))
in (_175_795)::p))))
end
| _84_1442 -> begin
(

let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _175_801 = (FStar_SMTEncoding_Term.mk_Precedes tl e)
in (_175_801)::p))))
end
| ((x, FStar_SMTEncoding_Term.Term_sort))::vars -> begin
(let _175_803 = (let _175_802 = (FStar_SMTEncoding_Term.mkFreeV (x, FStar_SMTEncoding_Term.Term_sort))
in (FStar_SMTEncoding_Term.mk_LexCons _175_802 tl))
in (aux _175_803 vars))
end
| _84_1454 -> begin
pats
end))
in (let _175_804 = (FStar_SMTEncoding_Term.mkFreeV ("Prims.LexTop", FStar_SMTEncoding_Term.Term_sort))
in (aux _175_804 vars)))
end)
end)
in (

let env = (

let _84_1456 = env
in {bindings = _84_1456.bindings; depth = _84_1456.depth; tcenv = _84_1456.tcenv; warn = _84_1456.warn; cache = _84_1456.cache; nolabels = true; use_zfuel_name = _84_1456.use_zfuel_name; encode_non_total_function_typ = _84_1456.encode_non_total_function_typ})
in (

let _84_1461 = (let _175_805 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula _175_805 env))
in (match (_84_1461) with
| (pre, decls'') -> begin
(

let _84_1464 = (let _175_806 = (FStar_Syntax_Util.unmeta post)
in (encode_formula _175_806 env))
in (match (_84_1464) with
| (post, decls''') -> begin
(

let decls = (FStar_List.append (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'') decls''')
in (let _175_811 = (let _175_810 = (let _175_809 = (let _175_808 = (let _175_807 = (FStar_SMTEncoding_Term.mk_and_l ((pre)::guards))
in (_175_807, post))
in (FStar_SMTEncoding_Term.mkImp _175_808))
in (pats, vars, _175_809))
in (FStar_SMTEncoding_Term.mkForall _175_810))
in (_175_811, decls)))
end))
end)))))
end))
end))
end))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (

let debug = (fun phi -> if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _175_817 = (FStar_Syntax_Print.tag_of_term phi)
in (let _175_816 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print2 "Formula (%s)  %s\n" _175_817 _175_816)))
end else begin
()
end)
in (

let enc = (fun f l -> (

let _84_1480 = (FStar_Util.fold_map (fun decls x -> (

let _84_1477 = (encode_term (Prims.fst x) env)
in (match (_84_1477) with
| (t, decls') -> begin
((FStar_List.append decls decls'), t)
end))) [] l)
in (match (_84_1480) with
| (decls, args) -> begin
(let _175_833 = (f args)
in (_175_833, decls))
end)))
in (

let const_op = (fun f _84_1483 -> (f, []))
in (

let un_op = (fun f l -> (let _175_847 = (FStar_List.hd l)
in (FStar_All.pipe_left f _175_847)))
in (

let bin_op = (fun f _84_10 -> (match (_84_10) with
| (t1)::(t2)::[] -> begin
(f (t1, t2))
end
| _84_1494 -> begin
(FStar_All.failwith "Impossible")
end))
in (

let enc_prop_c = (fun f l -> (

let _84_1509 = (FStar_Util.fold_map (fun decls _84_1503 -> (match (_84_1503) with
| (t, _84_1502) -> begin
(

let _84_1506 = (encode_formula t env)
in (match (_84_1506) with
| (phi, decls') -> begin
((FStar_List.append decls decls'), phi)
end))
end)) [] l)
in (match (_84_1509) with
| (decls, phis) -> begin
(let _175_872 = (f phis)
in (_175_872, decls))
end)))
in (

let eq_op = (fun _84_11 -> (match (_84_11) with
| (_84_1516)::(_84_1514)::(e1)::(e2)::[] -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) l)
end))
in (

let mk_imp = (fun _84_12 -> (match (_84_12) with
| ((lhs, _84_1527))::((rhs, _84_1523))::[] -> begin
(

let _84_1532 = (encode_formula rhs env)
in (match (_84_1532) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _84_1535) -> begin
(l1, decls1)
end
| _84_1539 -> begin
(

let _84_1542 = (encode_formula lhs env)
in (match (_84_1542) with
| (l2, decls2) -> begin
(let _175_877 = (FStar_SMTEncoding_Term.mkImp (l2, l1))
in (_175_877, (FStar_List.append decls1 decls2)))
end))
end)
end))
end
| _84_1544 -> begin
(FStar_All.failwith "impossible")
end))
in (

let mk_ite = (fun _84_13 -> (match (_84_13) with
| ((guard, _84_1557))::((_then, _84_1553))::((_else, _84_1549))::[] -> begin
(

let _84_1562 = (encode_formula guard env)
in (match (_84_1562) with
| (g, decls1) -> begin
(

let _84_1565 = (encode_formula _then env)
in (match (_84_1565) with
| (t, decls2) -> begin
(

let _84_1568 = (encode_formula _else env)
in (match (_84_1568) with
| (e, decls3) -> begin
(

let res = (FStar_SMTEncoding_Term.mkITE (g, t, e))
in (res, (FStar_List.append (FStar_List.append decls1 decls2) decls3)))
end))
end))
end))
end
| _84_1571 -> begin
(FStar_All.failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (let _175_889 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f _175_889)))
in (

let connectives = (let _175_942 = (let _175_898 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkAnd))
in (FStar_Syntax_Const.and_lid, _175_898))
in (let _175_941 = (let _175_940 = (let _175_904 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkOr))
in (FStar_Syntax_Const.or_lid, _175_904))
in (let _175_939 = (let _175_938 = (let _175_937 = (let _175_913 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkIff))
in (FStar_Syntax_Const.iff_lid, _175_913))
in (let _175_936 = (let _175_935 = (let _175_934 = (let _175_922 = (FStar_All.pipe_left enc_prop_c (un_op FStar_SMTEncoding_Term.mkNot))
in (FStar_Syntax_Const.not_lid, _175_922))
in (_175_934)::((FStar_Syntax_Const.eq2_lid, eq_op))::((FStar_Syntax_Const.true_lid, (const_op FStar_SMTEncoding_Term.mkTrue)))::((FStar_Syntax_Const.false_lid, (const_op FStar_SMTEncoding_Term.mkFalse)))::[])
in ((FStar_Syntax_Const.ite_lid, mk_ite))::_175_935)
in (_175_937)::_175_936))
in ((FStar_Syntax_Const.imp_lid, mk_imp))::_175_938)
in (_175_940)::_175_939))
in (_175_942)::_175_941))
in (

let rec fallback = (fun phi -> (match (phi.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(

let _84_1589 = (encode_formula phi' env)
in (match (_84_1589) with
| (phi, decls) -> begin
(let _175_945 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled ((phi, msg, r))))
in (_175_945, decls))
end))
end
| FStar_Syntax_Syntax.Tm_meta (_84_1591) -> begin
(let _175_946 = (FStar_Syntax_Util.unmeta phi)
in (encode_formula _175_946 env))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(

let _84_1599 = (encode_match e pats FStar_SMTEncoding_Term.mkFalse env encode_formula)
in (match (_84_1599) with
| (t, decls) -> begin
(t, decls)
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _84_1606; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _84_1603; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _84_1617 = (encode_let x t1 e1 e2 env encode_formula)
in (match (_84_1617) with
| (t, decls) -> begin
(t, decls)
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let head = (FStar_Syntax_Util.un_uinst head)
in (match ((head.FStar_Syntax_Syntax.n, args)) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_84_1634)::((x, _84_1631))::((t, _84_1627))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.has_type_lid) -> begin
(

let _84_1639 = (encode_term x env)
in (match (_84_1639) with
| (x, decls) -> begin
(

let _84_1642 = (encode_term t env)
in (match (_84_1642) with
| (t, decls') -> begin
(let _175_947 = (FStar_SMTEncoding_Term.mk_HasType x t)
in (_175_947, (FStar_List.append decls decls')))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((r, _84_1655))::((msg, _84_1651))::((phi, _84_1647))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.labeled_lid) -> begin
(match ((let _175_951 = (let _175_948 = (FStar_Syntax_Subst.compress r)
in _175_948.FStar_Syntax_Syntax.n)
in (let _175_950 = (let _175_949 = (FStar_Syntax_Subst.compress msg)
in _175_949.FStar_Syntax_Syntax.n)
in (_175_951, _175_950)))) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, _84_1664))) -> begin
(

let phi = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((phi, FStar_Syntax_Syntax.Meta_labeled (((FStar_Util.string_of_unicode s), r, false))))) None r)
in (fallback phi))
end
| _84_1671 -> begin
(fallback phi)
end)
end
| _84_1673 when (head_redex env head) -> begin
(let _175_952 = (whnf env phi)
in (encode_formula _175_952 env))
end
| _84_1675 -> begin
(

let _84_1678 = (encode_term phi env)
in (match (_84_1678) with
| (tt, decls) -> begin
(let _175_953 = (FStar_SMTEncoding_Term.mk_Valid tt)
in (_175_953, decls))
end))
end))
end
| _84_1680 -> begin
(

let _84_1683 = (encode_term phi env)
in (match (_84_1683) with
| (tt, decls) -> begin
(let _175_954 = (FStar_SMTEncoding_Term.mk_Valid tt)
in (_175_954, decls))
end))
end))
in (

let encode_q_body = (fun env bs ps body -> (

let _84_1695 = (encode_binders None bs env)
in (match (_84_1695) with
| (vars, guards, env, decls, _84_1694) -> begin
(

let _84_1708 = (let _175_966 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let _84_1705 = (let _175_965 = (FStar_All.pipe_right p (FStar_List.map (fun _84_1700 -> (match (_84_1700) with
| (t, _84_1699) -> begin
(encode_term t (

let _84_1701 = env
in {bindings = _84_1701.bindings; depth = _84_1701.depth; tcenv = _84_1701.tcenv; warn = _84_1701.warn; cache = _84_1701.cache; nolabels = _84_1701.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _84_1701.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _175_965 FStar_List.unzip))
in (match (_84_1705) with
| (p, decls) -> begin
(p, (FStar_List.flatten decls))
end)))))
in (FStar_All.pipe_right _175_966 FStar_List.unzip))
in (match (_84_1708) with
| (pats, decls') -> begin
(

let _84_1711 = (encode_formula body env)
in (match (_84_1711) with
| (body, decls'') -> begin
(

let guards = (match (pats) with
| (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.hash = _84_1715; FStar_SMTEncoding_Term.freevars = _84_1713})::[])::[] -> begin
[]
end
| _84_1726 -> begin
guards
end)
in (let _175_967 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (vars, pats, _175_967, body, (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls''))))
end))
end))
end)))
in (

let _84_1728 = (debug phi)
in (

let phi = (FStar_Syntax_Util.unascribe phi)
in (match ((FStar_Syntax_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _84_1740 -> (match (_84_1740) with
| (l, _84_1739) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_84_1743, f) -> begin
(f arms)
end)
end
| Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
(

let _84_1753 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _175_984 = (FStar_All.pipe_right vars (FStar_Syntax_Print.binders_to_string "; "))
in (FStar_Util.print1 ">>>> Got QALL [%s]\n" _175_984))
end else begin
()
end
in (

let _84_1760 = (encode_q_body env vars pats body)
in (match (_84_1760) with
| (vars, pats, guard, body, decls) -> begin
(

let tm = (let _175_986 = (let _175_985 = (FStar_SMTEncoding_Term.mkImp (guard, body))
in (pats, vars, _175_985))
in (FStar_SMTEncoding_Term.mkForall _175_986))
in (

let _84_1762 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _175_987 = (FStar_SMTEncoding_Term.termToSmt tm)
in (FStar_Util.print1 ">>>> Encoded QALL to %s\n" _175_987))
end else begin
()
end
in (tm, decls)))
end)))
end
| Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
(

let _84_1775 = (encode_q_body env vars pats body)
in (match (_84_1775) with
| (vars, pats, guard, body, decls) -> begin
(let _175_990 = (let _175_989 = (let _175_988 = (FStar_SMTEncoding_Term.mkAnd (guard, body))
in (pats, vars, _175_988))
in (FStar_SMTEncoding_Term.mkExists _175_989))
in (_175_990, decls))
end))
end)))))))))))))))))


type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.decl Prims.list; is : FStar_Ident.lident  ->  Prims.bool}


let is_Mkprims_t : prims_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkprims_t"))))


let prims : prims_t = (

let _84_1781 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (_84_1781) with
| (asym, a) -> begin
(

let _84_1784 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_84_1784) with
| (xsym, x) -> begin
(

let _84_1787 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (_84_1787) with
| (ysym, y) -> begin
(

let deffun = (fun vars body x -> (FStar_SMTEncoding_Term.DefineFun ((x, vars, FStar_SMTEncoding_Term.Term_sort, body, None)))::[])
in (

let quant = (fun vars body x -> (

let t1 = (let _175_1033 = (let _175_1032 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (x, _175_1032))
in (FStar_SMTEncoding_Term.mkApp _175_1033))
in (

let vname_decl = (let _175_1035 = (let _175_1034 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (x, _175_1034, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_175_1035))
in (let _175_1041 = (let _175_1040 = (let _175_1039 = (let _175_1038 = (let _175_1037 = (let _175_1036 = (FStar_SMTEncoding_Term.mkEq (t1, body))
in (((t1)::[])::[], vars, _175_1036))
in (FStar_SMTEncoding_Term.mkForall _175_1037))
in (_175_1038, None, Some ((Prims.strcat "primitive_" x))))
in FStar_SMTEncoding_Term.Assume (_175_1039))
in (_175_1040)::[])
in (vname_decl)::_175_1041))))
in (

let axy = ((asym, FStar_SMTEncoding_Term.Term_sort))::((xsym, FStar_SMTEncoding_Term.Term_sort))::((ysym, FStar_SMTEncoding_Term.Term_sort))::[]
in (

let xy = ((xsym, FStar_SMTEncoding_Term.Term_sort))::((ysym, FStar_SMTEncoding_Term.Term_sort))::[]
in (

let qx = ((xsym, FStar_SMTEncoding_Term.Term_sort))::[]
in (

let prims = (let _175_1201 = (let _175_1050 = (let _175_1049 = (let _175_1048 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _175_1048))
in (quant axy _175_1049))
in (FStar_Syntax_Const.op_Eq, _175_1050))
in (let _175_1200 = (let _175_1199 = (let _175_1057 = (let _175_1056 = (let _175_1055 = (let _175_1054 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (FStar_SMTEncoding_Term.mkNot _175_1054))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _175_1055))
in (quant axy _175_1056))
in (FStar_Syntax_Const.op_notEq, _175_1057))
in (let _175_1198 = (let _175_1197 = (let _175_1066 = (let _175_1065 = (let _175_1064 = (let _175_1063 = (let _175_1062 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _175_1061 = (FStar_SMTEncoding_Term.unboxInt y)
in (_175_1062, _175_1061)))
in (FStar_SMTEncoding_Term.mkLT _175_1063))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _175_1064))
in (quant xy _175_1065))
in (FStar_Syntax_Const.op_LT, _175_1066))
in (let _175_1196 = (let _175_1195 = (let _175_1075 = (let _175_1074 = (let _175_1073 = (let _175_1072 = (let _175_1071 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _175_1070 = (FStar_SMTEncoding_Term.unboxInt y)
in (_175_1071, _175_1070)))
in (FStar_SMTEncoding_Term.mkLTE _175_1072))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _175_1073))
in (quant xy _175_1074))
in (FStar_Syntax_Const.op_LTE, _175_1075))
in (let _175_1194 = (let _175_1193 = (let _175_1084 = (let _175_1083 = (let _175_1082 = (let _175_1081 = (let _175_1080 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _175_1079 = (FStar_SMTEncoding_Term.unboxInt y)
in (_175_1080, _175_1079)))
in (FStar_SMTEncoding_Term.mkGT _175_1081))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _175_1082))
in (quant xy _175_1083))
in (FStar_Syntax_Const.op_GT, _175_1084))
in (let _175_1192 = (let _175_1191 = (let _175_1093 = (let _175_1092 = (let _175_1091 = (let _175_1090 = (let _175_1089 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _175_1088 = (FStar_SMTEncoding_Term.unboxInt y)
in (_175_1089, _175_1088)))
in (FStar_SMTEncoding_Term.mkGTE _175_1090))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _175_1091))
in (quant xy _175_1092))
in (FStar_Syntax_Const.op_GTE, _175_1093))
in (let _175_1190 = (let _175_1189 = (let _175_1102 = (let _175_1101 = (let _175_1100 = (let _175_1099 = (let _175_1098 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _175_1097 = (FStar_SMTEncoding_Term.unboxInt y)
in (_175_1098, _175_1097)))
in (FStar_SMTEncoding_Term.mkSub _175_1099))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _175_1100))
in (quant xy _175_1101))
in (FStar_Syntax_Const.op_Subtraction, _175_1102))
in (let _175_1188 = (let _175_1187 = (let _175_1109 = (let _175_1108 = (let _175_1107 = (let _175_1106 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Term.mkMinus _175_1106))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _175_1107))
in (quant qx _175_1108))
in (FStar_Syntax_Const.op_Minus, _175_1109))
in (let _175_1186 = (let _175_1185 = (let _175_1118 = (let _175_1117 = (let _175_1116 = (let _175_1115 = (let _175_1114 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _175_1113 = (FStar_SMTEncoding_Term.unboxInt y)
in (_175_1114, _175_1113)))
in (FStar_SMTEncoding_Term.mkAdd _175_1115))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _175_1116))
in (quant xy _175_1117))
in (FStar_Syntax_Const.op_Addition, _175_1118))
in (let _175_1184 = (let _175_1183 = (let _175_1127 = (let _175_1126 = (let _175_1125 = (let _175_1124 = (let _175_1123 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _175_1122 = (FStar_SMTEncoding_Term.unboxInt y)
in (_175_1123, _175_1122)))
in (FStar_SMTEncoding_Term.mkMul _175_1124))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _175_1125))
in (quant xy _175_1126))
in (FStar_Syntax_Const.op_Multiply, _175_1127))
in (let _175_1182 = (let _175_1181 = (let _175_1136 = (let _175_1135 = (let _175_1134 = (let _175_1133 = (let _175_1132 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _175_1131 = (FStar_SMTEncoding_Term.unboxInt y)
in (_175_1132, _175_1131)))
in (FStar_SMTEncoding_Term.mkDiv _175_1133))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _175_1134))
in (quant xy _175_1135))
in (FStar_Syntax_Const.op_Division, _175_1136))
in (let _175_1180 = (let _175_1179 = (let _175_1145 = (let _175_1144 = (let _175_1143 = (let _175_1142 = (let _175_1141 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _175_1140 = (FStar_SMTEncoding_Term.unboxInt y)
in (_175_1141, _175_1140)))
in (FStar_SMTEncoding_Term.mkMod _175_1142))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _175_1143))
in (quant xy _175_1144))
in (FStar_Syntax_Const.op_Modulus, _175_1145))
in (let _175_1178 = (let _175_1177 = (let _175_1154 = (let _175_1153 = (let _175_1152 = (let _175_1151 = (let _175_1150 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _175_1149 = (FStar_SMTEncoding_Term.unboxBool y)
in (_175_1150, _175_1149)))
in (FStar_SMTEncoding_Term.mkAnd _175_1151))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _175_1152))
in (quant xy _175_1153))
in (FStar_Syntax_Const.op_And, _175_1154))
in (let _175_1176 = (let _175_1175 = (let _175_1163 = (let _175_1162 = (let _175_1161 = (let _175_1160 = (let _175_1159 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _175_1158 = (FStar_SMTEncoding_Term.unboxBool y)
in (_175_1159, _175_1158)))
in (FStar_SMTEncoding_Term.mkOr _175_1160))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _175_1161))
in (quant xy _175_1162))
in (FStar_Syntax_Const.op_Or, _175_1163))
in (let _175_1174 = (let _175_1173 = (let _175_1170 = (let _175_1169 = (let _175_1168 = (let _175_1167 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Term.mkNot _175_1167))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _175_1168))
in (quant qx _175_1169))
in (FStar_Syntax_Const.op_Negation, _175_1170))
in (_175_1173)::[])
in (_175_1175)::_175_1174))
in (_175_1177)::_175_1176))
in (_175_1179)::_175_1178))
in (_175_1181)::_175_1180))
in (_175_1183)::_175_1182))
in (_175_1185)::_175_1184))
in (_175_1187)::_175_1186))
in (_175_1189)::_175_1188))
in (_175_1191)::_175_1190))
in (_175_1193)::_175_1192))
in (_175_1195)::_175_1194))
in (_175_1197)::_175_1196))
in (_175_1199)::_175_1198))
in (_175_1201)::_175_1200))
in (

let mk = (fun l v -> (let _175_1233 = (FStar_All.pipe_right prims (FStar_List.filter (fun _84_1807 -> (match (_84_1807) with
| (l', _84_1806) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right _175_1233 (FStar_List.collect (fun _84_1811 -> (match (_84_1811) with
| (_84_1809, b) -> begin
(b v)
end))))))
in (

let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _84_1817 -> (match (_84_1817) with
| (l', _84_1816) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is}))))))))
end))
end))
end))


let pretype_axiom : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun tapp vars -> (

let _84_1823 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_84_1823) with
| (xxsym, xx) -> begin
(

let _84_1826 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_84_1826) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (let _175_1261 = (let _175_1260 = (let _175_1257 = (let _175_1256 = (let _175_1255 = (let _175_1254 = (let _175_1253 = (let _175_1252 = (FStar_SMTEncoding_Term.mkApp ("PreType", (xx)::[]))
in (tapp, _175_1252))
in (FStar_SMTEncoding_Term.mkEq _175_1253))
in (xx_has_type, _175_1254))
in (FStar_SMTEncoding_Term.mkImp _175_1255))
in (((xx_has_type)::[])::[], ((xxsym, FStar_SMTEncoding_Term.Term_sort))::((ffsym, FStar_SMTEncoding_Term.Fuel_sort))::vars, _175_1256))
in (FStar_SMTEncoding_Term.mkForall _175_1257))
in (let _175_1259 = (let _175_1258 = (varops.fresh "@pretyping_")
in Some (_175_1258))
in (_175_1260, Some ("pretyping"), _175_1259)))
in FStar_SMTEncoding_Term.Assume (_175_1261)))
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
in (let _175_1282 = (let _175_1273 = (let _175_1272 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in (_175_1272, Some ("unit typing"), Some ("unit_typing")))
in FStar_SMTEncoding_Term.Assume (_175_1273))
in (let _175_1281 = (let _175_1280 = (let _175_1279 = (let _175_1278 = (let _175_1277 = (let _175_1276 = (let _175_1275 = (let _175_1274 = (FStar_SMTEncoding_Term.mkEq (x, FStar_SMTEncoding_Term.mk_Term_unit))
in (typing_pred, _175_1274))
in (FStar_SMTEncoding_Term.mkImp _175_1275))
in (((typing_pred)::[])::[], (xx)::[], _175_1276))
in (mkForall_fuel _175_1277))
in (_175_1278, Some ("unit inversion"), Some ("unit_inversion")))
in FStar_SMTEncoding_Term.Assume (_175_1279))
in (_175_1280)::[])
in (_175_1282)::_175_1281))))
in (

let mk_bool = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _175_1305 = (let _175_1296 = (let _175_1295 = (let _175_1294 = (let _175_1293 = (let _175_1290 = (let _175_1289 = (FStar_SMTEncoding_Term.boxBool b)
in (_175_1289)::[])
in (_175_1290)::[])
in (let _175_1292 = (let _175_1291 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType _175_1291 tt))
in (_175_1293, (bb)::[], _175_1292)))
in (FStar_SMTEncoding_Term.mkForall _175_1294))
in (_175_1295, Some ("bool typing"), Some ("bool_typing")))
in FStar_SMTEncoding_Term.Assume (_175_1296))
in (let _175_1304 = (let _175_1303 = (let _175_1302 = (let _175_1301 = (let _175_1300 = (let _175_1299 = (let _175_1298 = (let _175_1297 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in (typing_pred, _175_1297))
in (FStar_SMTEncoding_Term.mkImp _175_1298))
in (((typing_pred)::[])::[], (xx)::[], _175_1299))
in (mkForall_fuel _175_1300))
in (_175_1301, Some ("bool inversion"), Some ("bool_inversion")))
in FStar_SMTEncoding_Term.Assume (_175_1302))
in (_175_1303)::[])
in (_175_1305)::_175_1304))))))
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

let precedes = (let _175_1319 = (let _175_1318 = (let _175_1317 = (let _175_1316 = (let _175_1315 = (let _175_1314 = (FStar_SMTEncoding_Term.boxInt a)
in (let _175_1313 = (let _175_1312 = (FStar_SMTEncoding_Term.boxInt b)
in (_175_1312)::[])
in (_175_1314)::_175_1313))
in (tt)::_175_1315)
in (tt)::_175_1316)
in ("Prims.Precedes", _175_1317))
in (FStar_SMTEncoding_Term.mkApp _175_1318))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _175_1319))
in (

let precedes_y_x = (let _175_1320 = (FStar_SMTEncoding_Term.mkApp ("Precedes", (y)::(x)::[]))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _175_1320))
in (let _175_1362 = (let _175_1328 = (let _175_1327 = (let _175_1326 = (let _175_1325 = (let _175_1322 = (let _175_1321 = (FStar_SMTEncoding_Term.boxInt b)
in (_175_1321)::[])
in (_175_1322)::[])
in (let _175_1324 = (let _175_1323 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType _175_1323 tt))
in (_175_1325, (bb)::[], _175_1324)))
in (FStar_SMTEncoding_Term.mkForall _175_1326))
in (_175_1327, Some ("int typing"), Some ("int_typing")))
in FStar_SMTEncoding_Term.Assume (_175_1328))
in (let _175_1361 = (let _175_1360 = (let _175_1334 = (let _175_1333 = (let _175_1332 = (let _175_1331 = (let _175_1330 = (let _175_1329 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in (typing_pred, _175_1329))
in (FStar_SMTEncoding_Term.mkImp _175_1330))
in (((typing_pred)::[])::[], (xx)::[], _175_1331))
in (mkForall_fuel _175_1332))
in (_175_1333, Some ("int inversion"), Some ("int_inversion")))
in FStar_SMTEncoding_Term.Assume (_175_1334))
in (let _175_1359 = (let _175_1358 = (let _175_1357 = (let _175_1356 = (let _175_1355 = (let _175_1354 = (let _175_1353 = (let _175_1352 = (let _175_1351 = (let _175_1350 = (let _175_1349 = (let _175_1348 = (let _175_1337 = (let _175_1336 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _175_1335 = (FStar_SMTEncoding_Term.mkInteger' 0)
in (_175_1336, _175_1335)))
in (FStar_SMTEncoding_Term.mkGT _175_1337))
in (let _175_1347 = (let _175_1346 = (let _175_1340 = (let _175_1339 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _175_1338 = (FStar_SMTEncoding_Term.mkInteger' 0)
in (_175_1339, _175_1338)))
in (FStar_SMTEncoding_Term.mkGTE _175_1340))
in (let _175_1345 = (let _175_1344 = (let _175_1343 = (let _175_1342 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _175_1341 = (FStar_SMTEncoding_Term.unboxInt x)
in (_175_1342, _175_1341)))
in (FStar_SMTEncoding_Term.mkLT _175_1343))
in (_175_1344)::[])
in (_175_1346)::_175_1345))
in (_175_1348)::_175_1347))
in (typing_pred_y)::_175_1349)
in (typing_pred)::_175_1350)
in (FStar_SMTEncoding_Term.mk_and_l _175_1351))
in (_175_1352, precedes_y_x))
in (FStar_SMTEncoding_Term.mkImp _175_1353))
in (((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[], (xx)::(yy)::[], _175_1354))
in (mkForall_fuel _175_1355))
in (_175_1356, Some ("well-founded ordering on nat (alt)"), Some ("well-founded-ordering-on-nat")))
in FStar_SMTEncoding_Term.Assume (_175_1357))
in (_175_1358)::[])
in (_175_1360)::_175_1359))
in (_175_1362)::_175_1361)))))))))))
in (

let mk_str = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = ("b", FStar_SMTEncoding_Term.String_sort)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _175_1385 = (let _175_1376 = (let _175_1375 = (let _175_1374 = (let _175_1373 = (let _175_1370 = (let _175_1369 = (FStar_SMTEncoding_Term.boxString b)
in (_175_1369)::[])
in (_175_1370)::[])
in (let _175_1372 = (let _175_1371 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType _175_1371 tt))
in (_175_1373, (bb)::[], _175_1372)))
in (FStar_SMTEncoding_Term.mkForall _175_1374))
in (_175_1375, Some ("string typing"), Some ("string_typing")))
in FStar_SMTEncoding_Term.Assume (_175_1376))
in (let _175_1384 = (let _175_1383 = (let _175_1382 = (let _175_1381 = (let _175_1380 = (let _175_1379 = (let _175_1378 = (let _175_1377 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in (typing_pred, _175_1377))
in (FStar_SMTEncoding_Term.mkImp _175_1378))
in (((typing_pred)::[])::[], (xx)::[], _175_1379))
in (mkForall_fuel _175_1380))
in (_175_1381, Some ("string inversion"), Some ("string_inversion")))
in FStar_SMTEncoding_Term.Assume (_175_1382))
in (_175_1383)::[])
in (_175_1385)::_175_1384))))))
in (

let mk_ref = (fun env reft_name _84_1865 -> (

let r = ("r", FStar_SMTEncoding_Term.Ref_sort)
in (

let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (

let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (

let refa = (let _175_1394 = (let _175_1393 = (let _175_1392 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (_175_1392)::[])
in (reft_name, _175_1393))
in (FStar_SMTEncoding_Term.mkApp _175_1394))
in (

let refb = (let _175_1397 = (let _175_1396 = (let _175_1395 = (FStar_SMTEncoding_Term.mkFreeV bb)
in (_175_1395)::[])
in (reft_name, _175_1396))
in (FStar_SMTEncoding_Term.mkApp _175_1397))
in (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (

let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (let _175_1416 = (let _175_1403 = (let _175_1402 = (let _175_1401 = (let _175_1400 = (let _175_1399 = (let _175_1398 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in (typing_pred, _175_1398))
in (FStar_SMTEncoding_Term.mkImp _175_1399))
in (((typing_pred)::[])::[], (xx)::(aa)::[], _175_1400))
in (mkForall_fuel _175_1401))
in (_175_1402, Some ("ref inversion"), Some ("ref_inversion")))
in FStar_SMTEncoding_Term.Assume (_175_1403))
in (let _175_1415 = (let _175_1414 = (let _175_1413 = (let _175_1412 = (let _175_1411 = (let _175_1410 = (let _175_1409 = (let _175_1408 = (FStar_SMTEncoding_Term.mkAnd (typing_pred, typing_pred_b))
in (let _175_1407 = (let _175_1406 = (let _175_1405 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (let _175_1404 = (FStar_SMTEncoding_Term.mkFreeV bb)
in (_175_1405, _175_1404)))
in (FStar_SMTEncoding_Term.mkEq _175_1406))
in (_175_1408, _175_1407)))
in (FStar_SMTEncoding_Term.mkImp _175_1409))
in (((typing_pred)::(typing_pred_b)::[])::[], (xx)::(aa)::(bb)::[], _175_1410))
in (mkForall_fuel' 2 _175_1411))
in (_175_1412, Some ("ref typing is injective"), Some ("ref_injectivity")))
in FStar_SMTEncoding_Term.Assume (_175_1413))
in (_175_1414)::[])
in (_175_1416)::_175_1415))))))))))
in (

let mk_false_interp = (fun env nm false_tm -> (

let valid = (FStar_SMTEncoding_Term.mkApp ("Valid", (false_tm)::[]))
in (let _175_1425 = (let _175_1424 = (let _175_1423 = (FStar_SMTEncoding_Term.mkIff (FStar_SMTEncoding_Term.mkFalse, valid))
in (_175_1423, Some ("False interpretation"), Some ("false_interp")))
in FStar_SMTEncoding_Term.Assume (_175_1424))
in (_175_1425)::[])))
in (

let mk_and_interp = (fun env conj _84_1882 -> (

let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (

let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (

let valid = (let _175_1434 = (let _175_1433 = (let _175_1432 = (FStar_SMTEncoding_Term.mkApp (conj, (a)::(b)::[]))
in (_175_1432)::[])
in ("Valid", _175_1433))
in (FStar_SMTEncoding_Term.mkApp _175_1434))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _175_1441 = (let _175_1440 = (let _175_1439 = (let _175_1438 = (let _175_1437 = (let _175_1436 = (let _175_1435 = (FStar_SMTEncoding_Term.mkAnd (valid_a, valid_b))
in (_175_1435, valid))
in (FStar_SMTEncoding_Term.mkIff _175_1436))
in (((valid)::[])::[], (aa)::(bb)::[], _175_1437))
in (FStar_SMTEncoding_Term.mkForall _175_1438))
in (_175_1439, Some ("/\\ interpretation"), Some ("l_and-interp")))
in FStar_SMTEncoding_Term.Assume (_175_1440))
in (_175_1441)::[])))))))))
in (

let mk_or_interp = (fun env disj _84_1894 -> (

let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (

let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (

let valid = (let _175_1450 = (let _175_1449 = (let _175_1448 = (FStar_SMTEncoding_Term.mkApp (disj, (a)::(b)::[]))
in (_175_1448)::[])
in ("Valid", _175_1449))
in (FStar_SMTEncoding_Term.mkApp _175_1450))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _175_1457 = (let _175_1456 = (let _175_1455 = (let _175_1454 = (let _175_1453 = (let _175_1452 = (let _175_1451 = (FStar_SMTEncoding_Term.mkOr (valid_a, valid_b))
in (_175_1451, valid))
in (FStar_SMTEncoding_Term.mkIff _175_1452))
in (((valid)::[])::[], (aa)::(bb)::[], _175_1453))
in (FStar_SMTEncoding_Term.mkForall _175_1454))
in (_175_1455, Some ("\\/ interpretation"), Some ("l_or-interp")))
in FStar_SMTEncoding_Term.Assume (_175_1456))
in (_175_1457)::[])))))))))
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

let valid = (let _175_1466 = (let _175_1465 = (let _175_1464 = (FStar_SMTEncoding_Term.mkApp (eq2, (a)::(b)::(x)::(y)::[]))
in (_175_1464)::[])
in ("Valid", _175_1465))
in (FStar_SMTEncoding_Term.mkApp _175_1466))
in (let _175_1473 = (let _175_1472 = (let _175_1471 = (let _175_1470 = (let _175_1469 = (let _175_1468 = (let _175_1467 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (_175_1467, valid))
in (FStar_SMTEncoding_Term.mkIff _175_1468))
in (((valid)::[])::[], (aa)::(bb)::(xx)::(yy)::[], _175_1469))
in (FStar_SMTEncoding_Term.mkForall _175_1470))
in (_175_1471, Some ("Eq2 interpretation"), Some ("eq2-interp")))
in FStar_SMTEncoding_Term.Assume (_175_1472))
in (_175_1473)::[])))))))))))
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

let valid = (let _175_1482 = (let _175_1481 = (let _175_1480 = (FStar_SMTEncoding_Term.mkApp (imp, (a)::(b)::[]))
in (_175_1480)::[])
in ("Valid", _175_1481))
in (FStar_SMTEncoding_Term.mkApp _175_1482))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _175_1489 = (let _175_1488 = (let _175_1487 = (let _175_1486 = (let _175_1485 = (let _175_1484 = (let _175_1483 = (FStar_SMTEncoding_Term.mkImp (valid_a, valid_b))
in (_175_1483, valid))
in (FStar_SMTEncoding_Term.mkIff _175_1484))
in (((valid)::[])::[], (aa)::(bb)::[], _175_1485))
in (FStar_SMTEncoding_Term.mkForall _175_1486))
in (_175_1487, Some ("==> interpretation"), Some ("l_imp-interp")))
in FStar_SMTEncoding_Term.Assume (_175_1488))
in (_175_1489)::[])))))))))
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

let valid = (let _175_1498 = (let _175_1497 = (let _175_1496 = (FStar_SMTEncoding_Term.mkApp (iff, (a)::(b)::[]))
in (_175_1496)::[])
in ("Valid", _175_1497))
in (FStar_SMTEncoding_Term.mkApp _175_1498))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _175_1505 = (let _175_1504 = (let _175_1503 = (let _175_1502 = (let _175_1501 = (let _175_1500 = (let _175_1499 = (FStar_SMTEncoding_Term.mkIff (valid_a, valid_b))
in (_175_1499, valid))
in (FStar_SMTEncoding_Term.mkIff _175_1500))
in (((valid)::[])::[], (aa)::(bb)::[], _175_1501))
in (FStar_SMTEncoding_Term.mkForall _175_1502))
in (_175_1503, Some ("<==> interpretation"), Some ("l_iff-interp")))
in FStar_SMTEncoding_Term.Assume (_175_1504))
in (_175_1505)::[])))))))))
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

let valid = (let _175_1514 = (let _175_1513 = (let _175_1512 = (FStar_SMTEncoding_Term.mkApp (for_all, (a)::(b)::[]))
in (_175_1512)::[])
in ("Valid", _175_1513))
in (FStar_SMTEncoding_Term.mkApp _175_1514))
in (

let valid_b_x = (let _175_1517 = (let _175_1516 = (let _175_1515 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_175_1515)::[])
in ("Valid", _175_1516))
in (FStar_SMTEncoding_Term.mkApp _175_1517))
in (let _175_1531 = (let _175_1530 = (let _175_1529 = (let _175_1528 = (let _175_1527 = (let _175_1526 = (let _175_1525 = (let _175_1524 = (let _175_1523 = (let _175_1519 = (let _175_1518 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_175_1518)::[])
in (_175_1519)::[])
in (let _175_1522 = (let _175_1521 = (let _175_1520 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_175_1520, valid_b_x))
in (FStar_SMTEncoding_Term.mkImp _175_1521))
in (_175_1523, (xx)::[], _175_1522)))
in (FStar_SMTEncoding_Term.mkForall _175_1524))
in (_175_1525, valid))
in (FStar_SMTEncoding_Term.mkIff _175_1526))
in (((valid)::[])::[], (aa)::(bb)::[], _175_1527))
in (FStar_SMTEncoding_Term.mkForall _175_1528))
in (_175_1529, Some ("forall interpretation"), Some ("forall-interp")))
in FStar_SMTEncoding_Term.Assume (_175_1530))
in (_175_1531)::[]))))))))))
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

let valid = (let _175_1540 = (let _175_1539 = (let _175_1538 = (FStar_SMTEncoding_Term.mkApp (for_some, (a)::(b)::[]))
in (_175_1538)::[])
in ("Valid", _175_1539))
in (FStar_SMTEncoding_Term.mkApp _175_1540))
in (

let valid_b_x = (let _175_1543 = (let _175_1542 = (let _175_1541 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_175_1541)::[])
in ("Valid", _175_1542))
in (FStar_SMTEncoding_Term.mkApp _175_1543))
in (let _175_1557 = (let _175_1556 = (let _175_1555 = (let _175_1554 = (let _175_1553 = (let _175_1552 = (let _175_1551 = (let _175_1550 = (let _175_1549 = (let _175_1545 = (let _175_1544 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_175_1544)::[])
in (_175_1545)::[])
in (let _175_1548 = (let _175_1547 = (let _175_1546 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_175_1546, valid_b_x))
in (FStar_SMTEncoding_Term.mkImp _175_1547))
in (_175_1549, (xx)::[], _175_1548)))
in (FStar_SMTEncoding_Term.mkExists _175_1550))
in (_175_1551, valid))
in (FStar_SMTEncoding_Term.mkIff _175_1552))
in (((valid)::[])::[], (aa)::(bb)::[], _175_1553))
in (FStar_SMTEncoding_Term.mkForall _175_1554))
in (_175_1555, Some ("exists interpretation"), Some ("exists-interp")))
in FStar_SMTEncoding_Term.Assume (_175_1556))
in (_175_1557)::[]))))))))))
in (

let mk_range_interp = (fun env range tt -> (

let range_ty = (FStar_SMTEncoding_Term.mkApp (range, []))
in (let _175_1568 = (let _175_1567 = (let _175_1566 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_ty)
in (let _175_1565 = (let _175_1564 = (varops.fresh "typing_range_const")
in Some (_175_1564))
in (_175_1566, Some ("Range_const typing"), _175_1565)))
in FStar_SMTEncoding_Term.Assume (_175_1567))
in (_175_1568)::[])))
in (

let prims = ((FStar_Syntax_Const.unit_lid, mk_unit))::((FStar_Syntax_Const.bool_lid, mk_bool))::((FStar_Syntax_Const.int_lid, mk_int))::((FStar_Syntax_Const.string_lid, mk_str))::((FStar_Syntax_Const.ref_lid, mk_ref))::((FStar_Syntax_Const.false_lid, mk_false_interp))::((FStar_Syntax_Const.and_lid, mk_and_interp))::((FStar_Syntax_Const.or_lid, mk_or_interp))::((FStar_Syntax_Const.eq2_lid, mk_eq2_interp))::((FStar_Syntax_Const.imp_lid, mk_imp_interp))::((FStar_Syntax_Const.iff_lid, mk_iff_interp))::((FStar_Syntax_Const.forall_lid, mk_forall_interp))::((FStar_Syntax_Const.exists_lid, mk_exists_interp))::((FStar_Syntax_Const.range_lid, mk_range_interp))::[]
in (fun env t s tt -> (match ((FStar_Util.find_opt (fun _84_1976 -> (match (_84_1976) with
| (l, _84_1975) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_84_1979, f) -> begin
(f env s tt)
end)))))))))))))))))))))


let encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let _84_1989 = (encode_function_type_as_formula None None t env)
in (match (_84_1989) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_SMTEncoding_Term.Assume ((form, Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str)), Some ((Prims.strcat "lemma_" lid.FStar_Ident.str)))))::[]))
end))))


let encode_free_var : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env fv tt t_norm quals -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if ((let _175_1758 = (FStar_Syntax_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _175_1758)) || (FStar_Syntax_Util.is_lemma t_norm)) then begin
(

let _84_1999 = (new_term_constant_and_tok_from_lid env lid)
in (match (_84_1999) with
| (vname, vtok, env) -> begin
(

let arg_sorts = (match ((let _175_1759 = (FStar_Syntax_Subst.compress t_norm)
in _175_1759.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _84_2002) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun _84_2005 -> FStar_SMTEncoding_Term.Term_sort)))
end
| _84_2008 -> begin
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

let _84_2023 = (

let _84_2018 = (curried_arrow_formals_comp t_norm)
in (match (_84_2018) with
| (args, comp) -> begin
if encode_non_total_function_typ then begin
(let _175_1761 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in (args, _175_1761))
end else begin
(args, (None, (FStar_Syntax_Util.comp_result comp)))
end
end))
in (match (_84_2023) with
| (formals, (pre_opt, res_t)) -> begin
(

let _84_2027 = (new_term_constant_and_tok_from_lid env lid)
in (match (_84_2027) with
| (vname, vtok, env) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV (vname, FStar_SMTEncoding_Term.Term_sort))
end
| _84_2030 -> begin
(FStar_SMTEncoding_Term.mkApp (vtok, []))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun _84_14 -> (match (_84_14) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(

let _84_2046 = (FStar_Util.prefix vars)
in (match (_84_2046) with
| (_84_2041, (xxsym, _84_2044)) -> begin
(

let xx = (FStar_SMTEncoding_Term.mkFreeV (xxsym, FStar_SMTEncoding_Term.Term_sort))
in (let _175_1778 = (let _175_1777 = (let _175_1776 = (let _175_1775 = (let _175_1774 = (let _175_1773 = (let _175_1772 = (let _175_1771 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _175_1771))
in (vapp, _175_1772))
in (FStar_SMTEncoding_Term.mkEq _175_1773))
in (((vapp)::[])::[], vars, _175_1774))
in (FStar_SMTEncoding_Term.mkForall _175_1775))
in (_175_1776, Some ("Discriminator equation"), Some ((Prims.strcat "disc_equation_" (escape d.FStar_Ident.str)))))
in FStar_SMTEncoding_Term.Assume (_175_1777))
in (_175_1778)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(

let _84_2058 = (FStar_Util.prefix vars)
in (match (_84_2058) with
| (_84_2053, (xxsym, _84_2056)) -> begin
(

let xx = (FStar_SMTEncoding_Term.mkFreeV (xxsym, FStar_SMTEncoding_Term.Term_sort))
in (

let f = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = 0; FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (

let tp_name = (mk_term_projector_name d f)
in (

let prim_app = (FStar_SMTEncoding_Term.mkApp (tp_name, (xx)::[]))
in (let _175_1783 = (let _175_1782 = (let _175_1781 = (let _175_1780 = (let _175_1779 = (FStar_SMTEncoding_Term.mkEq (vapp, prim_app))
in (((vapp)::[])::[], vars, _175_1779))
in (FStar_SMTEncoding_Term.mkForall _175_1780))
in (_175_1781, Some ("Projector equation"), Some ((Prims.strcat "proj_equation_" tp_name))))
in FStar_SMTEncoding_Term.Assume (_175_1782))
in (_175_1783)::[])))))
end))
end
| _84_2064 -> begin
[]
end)))))
in (

let _84_2071 = (encode_binders None formals env)
in (match (_84_2071) with
| (vars, guards, env', decls1, _84_2070) -> begin
(

let _84_2080 = (match (pre_opt) with
| None -> begin
(let _175_1784 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_175_1784, decls1))
end
| Some (p) -> begin
(

let _84_2077 = (encode_formula p env')
in (match (_84_2077) with
| (g, ds) -> begin
(let _175_1785 = (FStar_SMTEncoding_Term.mk_and_l ((g)::guards))
in (_175_1785, (FStar_List.append decls1 ds)))
end))
end)
in (match (_84_2080) with
| (guard, decls1) -> begin
(

let vtok_app = (mk_Apply vtok_tm vars)
in (

let vapp = (let _175_1787 = (let _175_1786 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (vname, _175_1786))
in (FStar_SMTEncoding_Term.mkApp _175_1787))
in (

let _84_2104 = (

let vname_decl = (let _175_1790 = (let _175_1789 = (FStar_All.pipe_right formals (FStar_List.map (fun _84_2083 -> FStar_SMTEncoding_Term.Term_sort)))
in (vname, _175_1789, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_175_1790))
in (

let _84_2091 = (

let env = (

let _84_2086 = env
in {bindings = _84_2086.bindings; depth = _84_2086.depth; tcenv = _84_2086.tcenv; warn = _84_2086.warn; cache = _84_2086.cache; nolabels = _84_2086.nolabels; use_zfuel_name = _84_2086.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in if (not ((head_normal env tt))) then begin
(encode_term_pred None tt env vtok_tm)
end else begin
(encode_term_pred None t_norm env vtok_tm)
end)
in (match (_84_2091) with
| (tok_typing, decls2) -> begin
(

let tok_typing = FStar_SMTEncoding_Term.Assume ((tok_typing, Some ("function token typing"), Some ((Prims.strcat "function_token_typing_" vname))))
in (

let _84_2101 = (match (formals) with
| [] -> begin
(let _175_1794 = (let _175_1793 = (let _175_1792 = (FStar_SMTEncoding_Term.mkFreeV (vname, FStar_SMTEncoding_Term.Term_sort))
in (FStar_All.pipe_left (fun _175_1791 -> Some (_175_1791)) _175_1792))
in (push_free_var env lid vname _175_1793))
in ((FStar_List.append decls2 ((tok_typing)::[])), _175_1794))
end
| _84_2095 -> begin
(

let vtok_decl = FStar_SMTEncoding_Term.DeclFun ((vtok, [], FStar_SMTEncoding_Term.Term_sort, None))
in (

let vtok_fresh = (let _175_1795 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (vtok, FStar_SMTEncoding_Term.Term_sort) _175_1795))
in (

let name_tok_corr = (let _175_1799 = (let _175_1798 = (let _175_1797 = (let _175_1796 = (FStar_SMTEncoding_Term.mkEq (vtok_app, vapp))
in (((vtok_app)::[])::[], vars, _175_1796))
in (FStar_SMTEncoding_Term.mkForall _175_1797))
in (_175_1798, Some ("Name-token correspondence"), Some ((Prims.strcat "token_correspondence_" vname))))
in FStar_SMTEncoding_Term.Assume (_175_1799))
in ((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[])), env))))
end)
in (match (_84_2101) with
| (tok_decl, env) -> begin
((vname_decl)::tok_decl, env)
end)))
end)))
in (match (_84_2104) with
| (decls2, env) -> begin
(

let _84_2112 = (

let res_t = (FStar_Syntax_Subst.compress res_t)
in (

let _84_2108 = (encode_term res_t env')
in (match (_84_2108) with
| (encoded_res_t, decls) -> begin
(let _175_1800 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in (encoded_res_t, _175_1800, decls))
end)))
in (match (_84_2112) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (let _175_1804 = (let _175_1803 = (let _175_1802 = (let _175_1801 = (FStar_SMTEncoding_Term.mkImp (guard, ty_pred))
in (((vapp)::[])::[], vars, _175_1801))
in (FStar_SMTEncoding_Term.mkForall _175_1802))
in (_175_1803, Some ("free var typing"), Some ((Prims.strcat "typing_" vname))))
in FStar_SMTEncoding_Term.Assume (_175_1804))
in (

let freshness = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New)) then begin
(let _175_1810 = (let _175_1807 = (let _175_1806 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (let _175_1805 = (varops.next_id ())
in (vname, _175_1806, FStar_SMTEncoding_Term.Term_sort, _175_1805)))
in (FStar_SMTEncoding_Term.fresh_constructor _175_1807))
in (let _175_1809 = (let _175_1808 = (pretype_axiom vapp vars)
in (_175_1808)::[])
in (_175_1810)::_175_1809))
end else begin
[]
end
in (

let g = (let _175_1812 = (let _175_1811 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_175_1811)
in (FStar_List.append (FStar_List.append (FStar_List.append (FStar_List.append decls1 decls2) decls3) freshness) _175_1812))
in (g, env))))
end))
end))))
end))
end))))
end))
end)))
end
end))


let declare_top_level_let : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  ((Prims.string * FStar_SMTEncoding_Term.term Prims.option) * FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env x t t_norm -> (match ((try_lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
(

let _84_2123 = (encode_free_var env x t t_norm [])
in (match (_84_2123) with
| (decls, env) -> begin
(

let _84_2128 = (lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_84_2128) with
| (n, x', _84_2127) -> begin
((n, x'), decls, env)
end))
end))
end
| Some (n, x, _84_2132) -> begin
((n, x), [], env)
end))


let encode_top_level_val : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env lid t quals -> (

let tt = (norm env t)
in (

let _84_2142 = (encode_free_var env lid t tt quals)
in (match (_84_2142) with
| (decls, env) -> begin
if (FStar_Syntax_Util.is_smt_lemma t) then begin
(let _175_1830 = (let _175_1829 = (encode_smt_lemma env lid tt)
in (FStar_List.append decls _175_1829))
in (_175_1830, env))
end else begin
(decls, env)
end
end))))


let encode_top_level_vals : env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _84_2148 lb -> (match (_84_2148) with
| (decls, env) -> begin
(

let _84_2152 = (let _175_1839 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env _175_1839 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (_84_2152) with
| (decls', env) -> begin
((FStar_List.append decls decls'), env)
end))
end)) ([], env))))


let encode_top_level_let : env_t  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env _84_2156 quals -> (match (_84_2156) with
| (is_rec, bindings) -> begin
(

let eta_expand = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let _84_2166 = (FStar_Util.first_N nbinders formals)
in (match (_84_2166) with
| (formals, extra_formals) -> begin
(

let subst = (FStar_List.map2 (fun _84_2170 _84_2174 -> (match ((_84_2170, _84_2174)) with
| ((formal, _84_2169), (binder, _84_2173)) -> begin
(let _175_1857 = (let _175_1856 = (FStar_Syntax_Syntax.bv_to_name binder)
in (formal, _175_1856))
in FStar_Syntax_Syntax.NT (_175_1857))
end)) formals binders)
in (

let extra_formals = (let _175_1861 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun _84_2178 -> (match (_84_2178) with
| (x, i) -> begin
(let _175_1860 = (

let _84_2179 = x
in (let _175_1859 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _84_2179.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _84_2179.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _175_1859}))
in (_175_1860, i))
end))))
in (FStar_All.pipe_right _175_1861 FStar_Syntax_Util.name_binders))
in (

let body = (let _175_1868 = (FStar_Syntax_Subst.compress body)
in (let _175_1867 = (let _175_1862 = (FStar_Syntax_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _175_1862))
in (let _175_1866 = (let _175_1865 = (let _175_1864 = (FStar_Syntax_Subst.subst subst t)
in _175_1864.FStar_Syntax_Syntax.n)
in (FStar_All.pipe_left (fun _175_1863 -> Some (_175_1863)) _175_1865))
in (FStar_Syntax_Syntax.extend_app_n _175_1868 _175_1867 _175_1866 body.FStar_Syntax_Syntax.pos))))
in ((FStar_List.append binders extra_formals), body))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (

let rec aux = (fun norm t_norm -> (match ((let _175_1879 = (FStar_Syntax_Util.unascribe e)
in _175_1879.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, lopt) -> begin
(

let _84_2198 = (FStar_Syntax_Subst.open_term' binders body)
in (match (_84_2198) with
| (binders, body, opening) -> begin
(match ((let _175_1880 = (FStar_Syntax_Subst.compress t_norm)
in _175_1880.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let _84_2205 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_84_2205) with
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

let _84_2212 = (FStar_Util.first_N nformals binders)
in (match (_84_2212) with
| (bs0, rest) -> begin
(

let c = (

let subst = (FStar_List.map2 (fun _84_2216 _84_2220 -> (match ((_84_2216, _84_2220)) with
| ((b, _84_2215), (x, _84_2219)) -> begin
(let _175_1884 = (let _175_1883 = (FStar_Syntax_Syntax.bv_to_name x)
in (b, _175_1883))
in FStar_Syntax_Syntax.NT (_175_1884))
end)) bs0 formals)
in (FStar_Syntax_Subst.subst_comp subst c))
in (

let body = (FStar_Syntax_Util.abs rest body lopt)
in (bs0, body, bs0, (FStar_Syntax_Util.comp_result c))))
end)))
end else begin
if (nformals > nbinders) then begin
(

let _84_2226 = (eta_expand binders formals body tres)
in (match (_84_2226) with
| (binders, body) -> begin
(binders, body, formals, tres)
end))
end else begin
(binders, body, formals, tres)
end
end)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, _84_2229) -> begin
(aux norm x.FStar_Syntax_Syntax.sort)
end
| _84_2233 when (not (norm)) -> begin
(

let t_norm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm)
in (aux true t_norm))
end
| _84_2236 -> begin
(let _175_1887 = (let _175_1886 = (FStar_Syntax_Print.term_to_string e)
in (let _175_1885 = (FStar_Syntax_Print.term_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str _175_1886 _175_1885)))
in (FStar_All.failwith _175_1887))
end)
end))
end
| _84_2238 -> begin
(match ((let _175_1888 = (FStar_Syntax_Subst.compress t_norm)
in _175_1888.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let _84_2245 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_84_2245) with
| (formals, c) -> begin
(

let tres = (FStar_Syntax_Util.comp_result c)
in (

let _84_2249 = (eta_expand [] formals e tres)
in (match (_84_2249) with
| (binders, body) -> begin
(binders, body, formals, tres)
end)))
end))
end
| _84_2251 -> begin
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

let _84_2279 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _84_2266 lb -> (match (_84_2266) with
| (toks, typs, decls, env) -> begin
(

let _84_2268 = if (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) then begin
(Prims.raise Let_rec_unencodeable)
end else begin
()
end
in (

let t_norm = (whnf env lb.FStar_Syntax_Syntax.lbtyp)
in (

let _84_2274 = (let _175_1893 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env _175_1893 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (_84_2274) with
| (tok, decl, env) -> begin
(let _175_1896 = (let _175_1895 = (let _175_1894 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (_175_1894, tok))
in (_175_1895)::toks)
in (_175_1896, (t_norm)::typs, (decl)::decls, env))
end))))
end)) ([], [], [], env)))
in (match (_84_2279) with
| (toks, typs, decls, env) -> begin
(

let toks = (FStar_List.rev toks)
in (

let decls = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (

let typs = (FStar_List.rev typs)
in if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _84_15 -> (match (_84_15) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| _84_2286 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> (let _175_1899 = (FStar_Syntax_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _175_1899)))))) then begin
(decls, env)
end else begin
if (not (is_rec)) then begin
(match ((bindings, typs, toks)) with
| (({FStar_Syntax_Syntax.lbname = _84_2296; FStar_Syntax_Syntax.lbunivs = _84_2294; FStar_Syntax_Syntax.lbtyp = _84_2292; FStar_Syntax_Syntax.lbeff = _84_2290; FStar_Syntax_Syntax.lbdef = e})::[], (t_norm)::[], ((flid_fv, (f, ftok)))::[]) -> begin
(

let e = (FStar_Syntax_Subst.compress e)
in (

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let _84_2316 = (destruct_bound_function flid t_norm e)
in (match (_84_2316) with
| (binders, body, _84_2313, _84_2315) -> begin
(

let _84_2323 = (encode_binders None binders env)
in (match (_84_2323) with
| (vars, guards, env', binder_decls, _84_2322) -> begin
(

let app = (match (vars) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV (f, FStar_SMTEncoding_Term.Term_sort))
end
| _84_2326 -> begin
(let _175_1901 = (let _175_1900 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (f, _175_1900))
in (FStar_SMTEncoding_Term.mkApp _175_1901))
end)
in (

let _84_2332 = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic)) then begin
(let _175_1903 = (FStar_SMTEncoding_Term.mk_Valid app)
in (let _175_1902 = (encode_formula body env')
in (_175_1903, _175_1902)))
end else begin
(let _175_1904 = (encode_term body env')
in (app, _175_1904))
end
in (match (_84_2332) with
| (app, (body, decls2)) -> begin
(

let eqn = (let _175_1910 = (let _175_1909 = (let _175_1906 = (let _175_1905 = (FStar_SMTEncoding_Term.mkEq (app, body))
in (((app)::[])::[], vars, _175_1905))
in (FStar_SMTEncoding_Term.mkForall _175_1906))
in (let _175_1908 = (let _175_1907 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (_175_1907))
in (_175_1909, _175_1908, Some ((Prims.strcat "equation_" f)))))
in FStar_SMTEncoding_Term.Assume (_175_1910))
in (let _175_1912 = (let _175_1911 = (primitive_type_axioms env.tcenv flid f app)
in (FStar_List.append (FStar_List.append (FStar_List.append (FStar_List.append decls binder_decls) decls2) ((eqn)::[])) _175_1911))
in (_175_1912, env)))
end)))
end))
end))))
end
| _84_2335 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(

let fuel = (let _175_1913 = (varops.fresh "fuel")
in (_175_1913, FStar_SMTEncoding_Term.Fuel_sort))
in (

let fuel_tm = (FStar_SMTEncoding_Term.mkFreeV fuel)
in (

let env0 = env
in (

let _84_2353 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _84_2341 _84_2346 -> (match ((_84_2341, _84_2346)) with
| ((gtoks, env), (flid_fv, (f, ftok))) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let g = (varops.new_fvar flid)
in (

let gtok = (varops.new_fvar flid)
in (

let env = (let _175_1918 = (let _175_1917 = (FStar_SMTEncoding_Term.mkApp (g, (fuel_tm)::[]))
in (FStar_All.pipe_left (fun _175_1916 -> Some (_175_1916)) _175_1917))
in (push_free_var env flid gtok _175_1918))
in (((flid, f, ftok, g, gtok))::gtoks, env)))))
end)) ([], env)))
in (match (_84_2353) with
| (gtoks, env) -> begin
(

let gtoks = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env0 _84_2362 t_norm _84_2373 -> (match ((_84_2362, _84_2373)) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = _84_2372; FStar_Syntax_Syntax.lbunivs = _84_2370; FStar_Syntax_Syntax.lbtyp = _84_2368; FStar_Syntax_Syntax.lbeff = _84_2366; FStar_Syntax_Syntax.lbdef = e}) -> begin
(

let _84_2378 = (destruct_bound_function flid t_norm e)
in (match (_84_2378) with
| (binders, body, formals, tres) -> begin
(

let _84_2385 = (encode_binders None binders env)
in (match (_84_2385) with
| (vars, guards, env', binder_decls, _84_2384) -> begin
(

let decl_g = (let _175_1929 = (let _175_1928 = (let _175_1927 = (FStar_List.map Prims.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::_175_1927)
in (g, _175_1928, FStar_SMTEncoding_Term.Term_sort, Some ("Fuel-instrumented function name")))
in FStar_SMTEncoding_Term.DeclFun (_175_1929))
in (

let env0 = (push_zfuel_name env0 flid g)
in (

let decl_g_tok = FStar_SMTEncoding_Term.DeclFun ((gtok, [], FStar_SMTEncoding_Term.Term_sort, Some ("Token for fuel-instrumented partial applications")))
in (

let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (

let app = (FStar_SMTEncoding_Term.mkApp (f, vars_tm))
in (

let gsapp = (let _175_1932 = (let _175_1931 = (let _175_1930 = (FStar_SMTEncoding_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (_175_1930)::vars_tm)
in (g, _175_1931))
in (FStar_SMTEncoding_Term.mkApp _175_1932))
in (

let gmax = (let _175_1935 = (let _175_1934 = (let _175_1933 = (FStar_SMTEncoding_Term.mkApp ("MaxFuel", []))
in (_175_1933)::vars_tm)
in (g, _175_1934))
in (FStar_SMTEncoding_Term.mkApp _175_1935))
in (

let _84_2395 = (encode_term body env')
in (match (_84_2395) with
| (body_tm, decls2) -> begin
(

let eqn_g = (let _175_1941 = (let _175_1940 = (let _175_1937 = (let _175_1936 = (FStar_SMTEncoding_Term.mkEq (gsapp, body_tm))
in (((gsapp)::[])::[], (fuel)::vars, _175_1936))
in (FStar_SMTEncoding_Term.mkForall _175_1937))
in (let _175_1939 = (let _175_1938 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (_175_1938))
in (_175_1940, _175_1939, Some ((Prims.strcat "equation_with_fuel_" g)))))
in FStar_SMTEncoding_Term.Assume (_175_1941))
in (

let eqn_f = (let _175_1945 = (let _175_1944 = (let _175_1943 = (let _175_1942 = (FStar_SMTEncoding_Term.mkEq (app, gmax))
in (((app)::[])::[], vars, _175_1942))
in (FStar_SMTEncoding_Term.mkForall _175_1943))
in (_175_1944, Some ("Correspondence of recursive function to instrumented version"), Some ((Prims.strcat "fuel_correspondence_" g))))
in FStar_SMTEncoding_Term.Assume (_175_1945))
in (

let eqn_g' = (let _175_1954 = (let _175_1953 = (let _175_1952 = (let _175_1951 = (let _175_1950 = (let _175_1949 = (let _175_1948 = (let _175_1947 = (let _175_1946 = (FStar_SMTEncoding_Term.n_fuel 0)
in (_175_1946)::vars_tm)
in (g, _175_1947))
in (FStar_SMTEncoding_Term.mkApp _175_1948))
in (gsapp, _175_1949))
in (FStar_SMTEncoding_Term.mkEq _175_1950))
in (((gsapp)::[])::[], (fuel)::vars, _175_1951))
in (FStar_SMTEncoding_Term.mkForall _175_1952))
in (_175_1953, Some ("Fuel irrelevance"), Some ((Prims.strcat "fuel_irrelevance_" g))))
in FStar_SMTEncoding_Term.Assume (_175_1954))
in (

let _84_2418 = (

let _84_2405 = (encode_binders None formals env0)
in (match (_84_2405) with
| (vars, v_guards, env, binder_decls, _84_2404) -> begin
(

let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (

let gapp = (FStar_SMTEncoding_Term.mkApp (g, (fuel_tm)::vars_tm))
in (

let tok_corr = (

let tok_app = (let _175_1955 = (FStar_SMTEncoding_Term.mkFreeV (gtok, FStar_SMTEncoding_Term.Term_sort))
in (mk_Apply _175_1955 ((fuel)::vars)))
in (let _175_1959 = (let _175_1958 = (let _175_1957 = (let _175_1956 = (FStar_SMTEncoding_Term.mkEq (tok_app, gapp))
in (((tok_app)::[])::[], (fuel)::vars, _175_1956))
in (FStar_SMTEncoding_Term.mkForall _175_1957))
in (_175_1958, Some ("Fuel token correspondence"), Some ((Prims.strcat "fuel_tokem_correspondence_" gtok))))
in FStar_SMTEncoding_Term.Assume (_175_1959)))
in (

let _84_2415 = (

let _84_2412 = (encode_term_pred None tres env gapp)
in (match (_84_2412) with
| (g_typing, d3) -> begin
(let _175_1967 = (let _175_1966 = (let _175_1965 = (let _175_1964 = (let _175_1963 = (let _175_1962 = (let _175_1961 = (let _175_1960 = (FStar_SMTEncoding_Term.mk_and_l v_guards)
in (_175_1960, g_typing))
in (FStar_SMTEncoding_Term.mkImp _175_1961))
in (((gapp)::[])::[], (fuel)::vars, _175_1962))
in (FStar_SMTEncoding_Term.mkForall _175_1963))
in (_175_1964, Some ("Typing correspondence of token to term"), Some ((Prims.strcat "token_correspondence_" g))))
in FStar_SMTEncoding_Term.Assume (_175_1965))
in (_175_1966)::[])
in (d3, _175_1967))
end))
in (match (_84_2415) with
| (aux_decls, typing_corr) -> begin
((FStar_List.append binder_decls aux_decls), (FStar_List.append typing_corr ((tok_corr)::[])))
end)))))
end))
in (match (_84_2418) with
| (aux_decls, g_typing) -> begin
((FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) aux_decls) ((decl_g)::(decl_g_tok)::[])), (FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing), env0)
end)))))
end)))))))))
end))
end))
end))
in (

let _84_2434 = (let _175_1970 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _84_2422 _84_2426 -> (match ((_84_2422, _84_2426)) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(

let _84_2430 = (encode_one_binding env0 gtok ty bs)
in (match (_84_2430) with
| (decls', eqns', env0) -> begin
((decls')::decls, (FStar_List.append eqns' eqns), env0)
end))
end)) ((decls)::[], [], env0) _175_1970))
in (match (_84_2434) with
| (decls, eqns, env0) -> begin
(

let _84_2443 = (let _175_1972 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _175_1972 (FStar_List.partition (fun _84_16 -> (match (_84_16) with
| FStar_SMTEncoding_Term.DeclFun (_84_2437) -> begin
true
end
| _84_2440 -> begin
false
end)))))
in (match (_84_2443) with
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

let msg = (let _175_1975 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _175_1975 (FStar_String.concat " and ")))
in (

let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in ((decl)::[], env)))
end))
end))


let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let _84_2447 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _175_1984 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _175_1984))
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

let _84_2455 = (encode_sigelt' env se)
in (match (_84_2455) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _175_1987 = (let _175_1986 = (let _175_1985 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (_175_1985))
in (_175_1986)::[])
in (_175_1987, e))
end
| _84_2458 -> begin
(let _175_1994 = (let _175_1993 = (let _175_1989 = (let _175_1988 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_175_1988))
in (_175_1989)::g)
in (let _175_1992 = (let _175_1991 = (let _175_1990 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_175_1990))
in (_175_1991)::[])
in (FStar_List.append _175_1993 _175_1992)))
in (_175_1994, e))
end)
end)))))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let should_skip = (fun l -> false)
in (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_84_2464) -> begin
(FStar_All.failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _84_2480) -> begin
if (let _175_1999 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right _175_1999 Prims.op_Negation)) then begin
([], env)
end else begin
(

let encode_monad_op = (fun tm name env -> (

let repr_name = (fun ed -> (FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid ed.FStar_Syntax_Syntax.mname) (((FStar_Ident.id_of_text (Prims.strcat name "_repr")))::[]))))
in (

let _84_2493 = (let _175_2008 = (repr_name ed)
in (new_term_constant_and_tok_from_lid env _175_2008))
in (match (_84_2493) with
| (br_name, _84_2491, env) -> begin
(

let _84_2496 = (encode_term (Prims.snd tm) env)
in (match (_84_2496) with
| (tm, decls) -> begin
(

let xs = if (name = "bind") then begin
(("@x0", FStar_SMTEncoding_Term.Term_sort))::(("@x1", FStar_SMTEncoding_Term.Term_sort))::(("@x2", FStar_SMTEncoding_Term.Term_sort))::(("@x3", FStar_SMTEncoding_Term.Term_sort))::(("@x4", FStar_SMTEncoding_Term.Term_sort))::(("@x5", FStar_SMTEncoding_Term.Term_sort))::[]
end else begin
(("@x0", FStar_SMTEncoding_Term.Term_sort))::(("@x1", FStar_SMTEncoding_Term.Term_sort))::(("@x2", FStar_SMTEncoding_Term.Term_sort))::[]
end
in (

let m_decl = (let _175_2010 = (let _175_2009 = (FStar_All.pipe_right xs (FStar_List.map Prims.snd))
in (br_name, _175_2009, FStar_SMTEncoding_Term.Term_sort, Some (name)))
in FStar_SMTEncoding_Term.DeclFun (_175_2010))
in (

let eqn = (

let app = (let _175_2013 = (let _175_2012 = (let _175_2011 = (FStar_All.pipe_right xs (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in (FStar_SMTEncoding_Term.Var (br_name), _175_2011))
in FStar_SMTEncoding_Term.App (_175_2012))
in (FStar_SMTEncoding_Term.mk _175_2013))
in (let _175_2019 = (let _175_2018 = (let _175_2017 = (let _175_2016 = (let _175_2015 = (let _175_2014 = (mk_Apply tm xs)
in (app, _175_2014))
in (FStar_SMTEncoding_Term.mkEq _175_2015))
in (((app)::[])::[], xs, _175_2016))
in (FStar_SMTEncoding_Term.mkForall _175_2017))
in (_175_2018, Some ((Prims.strcat name " equality")), Some ((Prims.strcat br_name "_equality"))))
in FStar_SMTEncoding_Term.Assume (_175_2019)))
in (env, (m_decl)::(eqn)::[]))))
end))
end))))
in (

let encode_action = (fun env a -> (

let _84_2507 = (new_term_constant_and_tok_from_lid env a.FStar_Syntax_Syntax.action_name)
in (match (_84_2507) with
| (aname, atok, env) -> begin
(

let _84_2511 = (FStar_Syntax_Util.arrow_formals_comp a.FStar_Syntax_Syntax.action_typ)
in (match (_84_2511) with
| (formals, _84_2510) -> begin
(

let _84_2514 = (encode_term a.FStar_Syntax_Syntax.action_defn env)
in (match (_84_2514) with
| (tm, decls) -> begin
(

let a_decls = (let _175_2027 = (let _175_2026 = (let _175_2025 = (FStar_All.pipe_right formals (FStar_List.map (fun _84_2515 -> FStar_SMTEncoding_Term.Term_sort)))
in (aname, _175_2025, FStar_SMTEncoding_Term.Term_sort, Some ("Action")))
in FStar_SMTEncoding_Term.DeclFun (_175_2026))
in (_175_2027)::(FStar_SMTEncoding_Term.DeclFun ((atok, [], FStar_SMTEncoding_Term.Term_sort, Some ("Action token"))))::[])
in (

let _84_2529 = (let _175_2029 = (FStar_All.pipe_right formals (FStar_List.map (fun _84_2521 -> (match (_84_2521) with
| (bv, _84_2520) -> begin
(

let _84_2526 = (gen_term_var env bv)
in (match (_84_2526) with
| (xxsym, xx, _84_2525) -> begin
((xxsym, FStar_SMTEncoding_Term.Term_sort), xx)
end))
end))))
in (FStar_All.pipe_right _175_2029 FStar_List.split))
in (match (_84_2529) with
| (xs_sorts, xs) -> begin
(

let app = (let _175_2033 = (let _175_2032 = (let _175_2031 = (let _175_2030 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App ((FStar_SMTEncoding_Term.Var (aname), xs))))
in (_175_2030)::[])
in (FStar_SMTEncoding_Term.Var ("Reify"), _175_2031))
in FStar_SMTEncoding_Term.App (_175_2032))
in (FStar_All.pipe_right _175_2033 FStar_SMTEncoding_Term.mk))
in (

let a_eq = (let _175_2039 = (let _175_2038 = (let _175_2037 = (let _175_2036 = (let _175_2035 = (let _175_2034 = (mk_Apply tm xs_sorts)
in (app, _175_2034))
in (FStar_SMTEncoding_Term.mkEq _175_2035))
in (((app)::[])::[], xs_sorts, _175_2036))
in (FStar_SMTEncoding_Term.mkForall _175_2037))
in (_175_2038, Some ("Action equality"), Some ((Prims.strcat aname "_equality"))))
in FStar_SMTEncoding_Term.Assume (_175_2039))
in (

let tok_correspondence = (

let tok_term = (FStar_SMTEncoding_Term.mkFreeV (atok, FStar_SMTEncoding_Term.Term_sort))
in (

let tok_app = (mk_Apply tok_term xs_sorts)
in (let _175_2043 = (let _175_2042 = (let _175_2041 = (let _175_2040 = (FStar_SMTEncoding_Term.mkEq (tok_app, app))
in (((tok_app)::[])::[], xs_sorts, _175_2040))
in (FStar_SMTEncoding_Term.mkForall _175_2041))
in (_175_2042, Some ("Action token correspondence"), Some ((Prims.strcat aname "_token_correspondence"))))
in FStar_SMTEncoding_Term.Assume (_175_2043))))
in (env, (FStar_List.append (FStar_List.append decls a_decls) ((a_eq)::(tok_correspondence)::[]))))))
end)))
end))
end))
end)))
in (

let _84_2537 = (encode_monad_op ed.FStar_Syntax_Syntax.bind_repr "bind" env)
in (match (_84_2537) with
| (env, decls0) -> begin
(

let _84_2540 = (encode_monad_op ed.FStar_Syntax_Syntax.return_repr "return" env)
in (match (_84_2540) with
| (env, decls1) -> begin
(

let _84_2543 = (FStar_Util.fold_map encode_action env ed.FStar_Syntax_Syntax.actions)
in (match (_84_2543) with
| (env, decls2) -> begin
((FStar_List.append (FStar_List.append decls0 decls1) (FStar_List.flatten decls2)), env)
end))
end))
end))))
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _84_2546, _84_2548, _84_2550, _84_2552) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid) -> begin
(

let _84_2558 = (new_term_constant_and_tok_from_lid env lid)
in (match (_84_2558) with
| (tname, ttok, env) -> begin
([], env)
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _84_2561, t, quals, _84_2565) -> begin
(

let will_encode_definition = (not ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _84_17 -> (match (_84_17) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Irreducible) -> begin
true
end
| _84_2578 -> begin
false
end))))))
in if will_encode_definition then begin
([], env)
end else begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (

let _84_2583 = (encode_top_level_val env fv t quals)
in (match (_84_2583) with
| (decls, env) -> begin
(

let tname = lid.FStar_Ident.str
in (

let tsym = (FStar_SMTEncoding_Term.mkFreeV (tname, FStar_SMTEncoding_Term.Term_sort))
in (let _175_2046 = (let _175_2045 = (primitive_type_axioms env.tcenv lid tname tsym)
in (FStar_List.append decls _175_2045))
in (_175_2046, env))))
end)))
end)
end
| FStar_Syntax_Syntax.Sig_assume (l, f, _84_2589, _84_2591) -> begin
(

let _84_2596 = (encode_formula f env)
in (match (_84_2596) with
| (f, decls) -> begin
(

let g = (let _175_2053 = (let _175_2052 = (let _175_2051 = (let _175_2048 = (let _175_2047 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" _175_2047))
in Some (_175_2048))
in (let _175_2050 = (let _175_2049 = (varops.fresh (Prims.strcat "assumption_" l.FStar_Ident.str))
in Some (_175_2049))
in (f, _175_2051, _175_2050)))
in FStar_SMTEncoding_Term.Assume (_175_2052))
in (_175_2053)::[])
in ((FStar_List.append decls g), env))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _84_2601, quals) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) -> begin
(

let _84_2614 = (FStar_Util.fold_map (fun env lb -> (

let lid = (let _175_2057 = (let _175_2056 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _175_2056.FStar_Syntax_Syntax.fv_name)
in _175_2057.FStar_Syntax_Syntax.v)
in if (let _175_2058 = (FStar_TypeChecker_Env.try_lookup_val_decl env.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone _175_2058)) then begin
(

let val_decl = FStar_Syntax_Syntax.Sig_declare_typ ((lid, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, quals, r))
in (

let _84_2611 = (encode_sigelt' env val_decl)
in (match (_84_2611) with
| (decls, env) -> begin
(env, decls)
end)))
end else begin
(env, [])
end)) env (Prims.snd lbs))
in (match (_84_2614) with
| (env, decls) -> begin
((FStar_List.flatten decls), env)
end))
end
| FStar_Syntax_Syntax.Sig_let ((_84_2616, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t); FStar_Syntax_Syntax.lbunivs = _84_2624; FStar_Syntax_Syntax.lbtyp = _84_2622; FStar_Syntax_Syntax.lbeff = _84_2620; FStar_Syntax_Syntax.lbdef = _84_2618})::[]), _84_2631, _84_2633, _84_2635) when (FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Syntax_Const.b2t_lid) -> begin
(

let _84_2641 = (new_term_constant_and_tok_from_lid env b2t.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_84_2641) with
| (tname, ttok, env) -> begin
(

let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (

let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (

let valid_b2t_x = (let _175_2061 = (let _175_2060 = (let _175_2059 = (FStar_SMTEncoding_Term.mkApp ("Prims.b2t", (x)::[]))
in (_175_2059)::[])
in ("Valid", _175_2060))
in (FStar_SMTEncoding_Term.mkApp _175_2061))
in (

let decls = (let _175_2069 = (let _175_2068 = (let _175_2067 = (let _175_2066 = (let _175_2065 = (let _175_2064 = (let _175_2063 = (let _175_2062 = (FStar_SMTEncoding_Term.mkApp ("BoxBool_proj_0", (x)::[]))
in (valid_b2t_x, _175_2062))
in (FStar_SMTEncoding_Term.mkEq _175_2063))
in (((valid_b2t_x)::[])::[], (xx)::[], _175_2064))
in (FStar_SMTEncoding_Term.mkForall _175_2065))
in (_175_2066, Some ("b2t def"), Some ("b2t_def")))
in FStar_SMTEncoding_Term.Assume (_175_2067))
in (_175_2068)::[])
in (FStar_SMTEncoding_Term.DeclFun ((tname, (FStar_SMTEncoding_Term.Term_sort)::[], FStar_SMTEncoding_Term.Term_sort, None)))::_175_2069)
in (decls, env)))))
end))
end
| FStar_Syntax_Syntax.Sig_let (_84_2647, _84_2649, _84_2651, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _84_18 -> (match (_84_18) with
| FStar_Syntax_Syntax.Discriminator (_84_2657) -> begin
true
end
| _84_2660 -> begin
false
end)))) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_let (_84_2662, _84_2664, lids, quals) when ((FStar_All.pipe_right lids (FStar_Util.for_some (fun l -> ((let _175_2072 = (FStar_List.hd l.FStar_Ident.ns)
in _175_2072.FStar_Ident.idText) = "Prims")))) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun _84_19 -> (match (_84_19) with
| FStar_Syntax_Syntax.Inline -> begin
true
end
| _84_2673 -> begin
false
end))))) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _84_2679, _84_2681, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _84_20 -> (match (_84_20) with
| FStar_Syntax_Syntax.Projector (_84_2687) -> begin
true
end
| _84_2690 -> begin
false
end)))) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((try_lookup_free_var env l)) with
| Some (_84_2694) -> begin
([], env)
end
| None -> begin
(

let se = FStar_Syntax_Syntax.Sig_declare_typ ((l, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, quals, (FStar_Ident.range_of_lid l)))
in (encode_sigelt env se))
end)))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _84_2703, _84_2705, quals) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) -> begin
(match ((let _175_2075 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef)
in _175_2075.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, _84_2712) -> begin
(

let body = (FStar_Syntax_Util.mk_reify body)
in (

let tm = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs ((bs, body, None))) None lb.FStar_Syntax_Syntax.lbdef.FStar_Syntax_Syntax.pos)
in (

let tm' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env.tcenv tm)
in (

let lb_typ = (

let _84_2720 = (FStar_Syntax_Util.arrow_formals_comp lb.FStar_Syntax_Syntax.lbtyp)
in (match (_84_2720) with
| (formals, comp) -> begin
(

let reified_typ = (FStar_TypeChecker_Util.reify_comp env.tcenv (FStar_Syntax_Util.lcomp_of_comp comp) FStar_Syntax_Syntax.U_unknown)
in (let _175_2076 = (FStar_Syntax_Syntax.mk_Total reified_typ)
in (FStar_Syntax_Util.arrow formals _175_2076)))
end))
in (

let lb = (

let _84_2723 = lb
in {FStar_Syntax_Syntax.lbname = _84_2723.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _84_2723.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lb_typ; FStar_Syntax_Syntax.lbeff = _84_2723.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = tm'})
in (encode_top_level_let env (false, (lb)::[]) quals))))))
end
| _84_2727 -> begin
([], env)
end)
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), _84_2732, _84_2734, quals) -> begin
(encode_top_level_let env (is_rec, bindings) quals)
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _84_2740, _84_2742, _84_2744) -> begin
(

let _84_2749 = (encode_signature env ses)
in (match (_84_2749) with
| (g, env) -> begin
(

let _84_2763 = (FStar_All.pipe_right g (FStar_List.partition (fun _84_21 -> (match (_84_21) with
| FStar_SMTEncoding_Term.Assume (_84_2752, Some ("inversion axiom"), _84_2756) -> begin
false
end
| _84_2760 -> begin
true
end))))
in (match (_84_2763) with
| (g', inversions) -> begin
(

let _84_2772 = (FStar_All.pipe_right g' (FStar_List.partition (fun _84_22 -> (match (_84_22) with
| FStar_SMTEncoding_Term.DeclFun (_84_2766) -> begin
true
end
| _84_2769 -> begin
false
end))))
in (match (_84_2772) with
| (decls, rest) -> begin
((FStar_List.append (FStar_List.append decls rest) inversions), env)
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, _84_2775, tps, k, _84_2779, datas, quals, _84_2783) -> begin
(

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _84_23 -> (match (_84_23) with
| (FStar_Syntax_Syntax.Logic) | (FStar_Syntax_Syntax.Assumption) -> begin
true
end
| _84_2790 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(

let _84_2802 = c
in (match (_84_2802) with
| (name, args, _84_2797, _84_2799, _84_2801) -> begin
(let _175_2084 = (let _175_2083 = (let _175_2082 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in (name, _175_2082, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_175_2083))
in (_175_2084)::[])
end))
end else begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end)
in (

let inversion_axioms = (fun tapp vars -> if (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _175_2090 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right _175_2090 FStar_Option.isNone))))) then begin
[]
end else begin
(

let _84_2809 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_84_2809) with
| (xxsym, xx) -> begin
(

let _84_2845 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _84_2812 l -> (match (_84_2812) with
| (out, decls) -> begin
(

let _84_2817 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (_84_2817) with
| (_84_2815, data_t) -> begin
(

let _84_2820 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (_84_2820) with
| (args, res) -> begin
(

let indices = (match ((let _175_2093 = (FStar_Syntax_Subst.compress res)
in _175_2093.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_84_2822, indices) -> begin
indices
end
| _84_2827 -> begin
[]
end)
in (

let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env _84_2833 -> (match (_84_2833) with
| (x, _84_2832) -> begin
(let _175_2098 = (let _175_2097 = (let _175_2096 = (mk_term_projector_name l x)
in (_175_2096, (xx)::[]))
in (FStar_SMTEncoding_Term.mkApp _175_2097))
in (push_term_var env x _175_2098))
end)) env))
in (

let _84_2837 = (encode_args indices env)
in (match (_84_2837) with
| (indices, decls') -> begin
(

let _84_2838 = if ((FStar_List.length indices) <> (FStar_List.length vars)) then begin
(FStar_All.failwith "Impossible")
end else begin
()
end
in (

let eqs = (let _175_2103 = (FStar_List.map2 (fun v a -> (let _175_2102 = (let _175_2101 = (FStar_SMTEncoding_Term.mkFreeV v)
in (_175_2101, a))
in (FStar_SMTEncoding_Term.mkEq _175_2102))) vars indices)
in (FStar_All.pipe_right _175_2103 FStar_SMTEncoding_Term.mk_and_l))
in (let _175_2108 = (let _175_2107 = (let _175_2106 = (let _175_2105 = (let _175_2104 = (mk_data_tester env l xx)
in (_175_2104, eqs))
in (FStar_SMTEncoding_Term.mkAnd _175_2105))
in (out, _175_2106))
in (FStar_SMTEncoding_Term.mkOr _175_2107))
in (_175_2108, (FStar_List.append decls decls')))))
end))))
end))
end))
end)) (FStar_SMTEncoding_Term.mkFalse, [])))
in (match (_84_2845) with
| (data_ax, decls) -> begin
(

let _84_2848 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_84_2848) with
| (ffsym, ff) -> begin
(

let fuel_guarded_inversion = (

let xx_has_type_sfuel = if ((FStar_List.length datas) > 1) then begin
(let _175_2109 = (FStar_SMTEncoding_Term.mkApp ("SFuel", (ff)::[]))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel _175_2109 xx tapp))
end else begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end
in (let _175_2116 = (let _175_2115 = (let _175_2112 = (let _175_2111 = (add_fuel (ffsym, FStar_SMTEncoding_Term.Fuel_sort) (((xxsym, FStar_SMTEncoding_Term.Term_sort))::vars))
in (let _175_2110 = (FStar_SMTEncoding_Term.mkImp (xx_has_type_sfuel, data_ax))
in (((xx_has_type_sfuel)::[])::[], _175_2111, _175_2110)))
in (FStar_SMTEncoding_Term.mkForall _175_2112))
in (let _175_2114 = (let _175_2113 = (varops.fresh (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str))
in Some (_175_2113))
in (_175_2115, Some ("inversion axiom"), _175_2114)))
in FStar_SMTEncoding_Term.Assume (_175_2116)))
in (

let pattern_guarded_inversion = if ((contains_name env "Prims.inversion") && ((FStar_List.length datas) > 1)) then begin
(

let xx_has_type_fuel = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let pattern_guard = (FStar_SMTEncoding_Term.mkApp ("Prims.inversion", (tapp)::[]))
in (let _175_2124 = (let _175_2123 = (let _175_2122 = (let _175_2119 = (let _175_2118 = (add_fuel (ffsym, FStar_SMTEncoding_Term.Fuel_sort) (((xxsym, FStar_SMTEncoding_Term.Term_sort))::vars))
in (let _175_2117 = (FStar_SMTEncoding_Term.mkImp (xx_has_type_fuel, data_ax))
in (((xx_has_type_fuel)::(pattern_guard)::[])::[], _175_2118, _175_2117)))
in (FStar_SMTEncoding_Term.mkForall _175_2119))
in (let _175_2121 = (let _175_2120 = (varops.fresh (Prims.strcat "pattern_guarded_inversion_" t.FStar_Ident.str))
in Some (_175_2120))
in (_175_2122, Some ("inversion axiom"), _175_2121)))
in FStar_SMTEncoding_Term.Assume (_175_2123))
in (_175_2124)::[])))
end else begin
[]
end
in (FStar_List.append (FStar_List.append decls ((fuel_guarded_inversion)::[])) pattern_guarded_inversion)))
end))
end))
end))
end)
in (

let _84_2862 = (match ((let _175_2125 = (FStar_Syntax_Subst.compress k)
in _175_2125.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
((FStar_List.append tps formals), (FStar_Syntax_Util.comp_result kres))
end
| _84_2859 -> begin
(tps, k)
end)
in (match (_84_2862) with
| (formals, res) -> begin
(

let _84_2865 = (FStar_Syntax_Subst.open_term formals res)
in (match (_84_2865) with
| (formals, res) -> begin
(

let _84_2872 = (encode_binders None formals env)
in (match (_84_2872) with
| (vars, guards, env', binder_decls, _84_2871) -> begin
(

let _84_2876 = (new_term_constant_and_tok_from_lid env t)
in (match (_84_2876) with
| (tname, ttok, env) -> begin
(

let ttok_tm = (FStar_SMTEncoding_Term.mkApp (ttok, []))
in (

let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (

let tapp = (let _175_2127 = (let _175_2126 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (tname, _175_2126))
in (FStar_SMTEncoding_Term.mkApp _175_2127))
in (

let _84_2897 = (

let tname_decl = (let _175_2131 = (let _175_2130 = (FStar_All.pipe_right vars (FStar_List.map (fun _84_2882 -> (match (_84_2882) with
| (n, s) -> begin
((Prims.strcat tname n), s)
end))))
in (let _175_2129 = (varops.next_id ())
in (tname, _175_2130, FStar_SMTEncoding_Term.Term_sort, _175_2129, false)))
in (constructor_or_logic_type_decl _175_2131))
in (

let _84_2894 = (match (vars) with
| [] -> begin
(let _175_2135 = (let _175_2134 = (let _175_2133 = (FStar_SMTEncoding_Term.mkApp (tname, []))
in (FStar_All.pipe_left (fun _175_2132 -> Some (_175_2132)) _175_2133))
in (push_free_var env t tname _175_2134))
in ([], _175_2135))
end
| _84_2886 -> begin
(

let ttok_decl = FStar_SMTEncoding_Term.DeclFun ((ttok, [], FStar_SMTEncoding_Term.Term_sort, Some ("token")))
in (

let ttok_fresh = (let _175_2136 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (ttok, FStar_SMTEncoding_Term.Term_sort) _175_2136))
in (

let ttok_app = (mk_Apply ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (let _175_2140 = (let _175_2139 = (let _175_2138 = (let _175_2137 = (FStar_SMTEncoding_Term.mkEq (ttok_app, tapp))
in (pats, None, vars, _175_2137))
in (FStar_SMTEncoding_Term.mkForall' _175_2138))
in (_175_2139, Some ("name-token correspondence"), Some ((Prims.strcat "token_correspondence_" ttok))))
in FStar_SMTEncoding_Term.Assume (_175_2140))
in ((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[], env))))))
end)
in (match (_84_2894) with
| (tok_decls, env) -> begin
((FStar_List.append tname_decl tok_decls), env)
end)))
in (match (_84_2897) with
| (decls, env) -> begin
(

let kindingAx = (

let _84_2900 = (encode_term_pred None res env' tapp)
in (match (_84_2900) with
| (k, decls) -> begin
(

let karr = if ((FStar_List.length formals) > 0) then begin
(let _175_2144 = (let _175_2143 = (let _175_2142 = (let _175_2141 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _175_2141))
in (_175_2142, Some ("kinding"), Some ((Prims.strcat "pre_kinding_" ttok))))
in FStar_SMTEncoding_Term.Assume (_175_2143))
in (_175_2144)::[])
end else begin
[]
end
in (let _175_2150 = (let _175_2149 = (let _175_2148 = (let _175_2147 = (let _175_2146 = (let _175_2145 = (FStar_SMTEncoding_Term.mkImp (guard, k))
in (((tapp)::[])::[], vars, _175_2145))
in (FStar_SMTEncoding_Term.mkForall _175_2146))
in (_175_2147, None, Some ((Prims.strcat "kinding_" ttok))))
in FStar_SMTEncoding_Term.Assume (_175_2148))
in (_175_2149)::[])
in (FStar_List.append (FStar_List.append decls karr) _175_2150)))
end))
in (

let aux = (let _175_2154 = (let _175_2151 = (inversion_axioms tapp vars)
in (FStar_List.append kindingAx _175_2151))
in (let _175_2153 = (let _175_2152 = (pretype_axiom tapp vars)
in (_175_2152)::[])
in (FStar_List.append _175_2154 _175_2153)))
in (

let g = (FStar_List.append (FStar_List.append decls binder_decls) aux)
in (g, env))))
end)))))
end))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, _84_2907, _84_2909, _84_2911, _84_2913, _84_2915, _84_2917, _84_2919) when (FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_datacon (d, _84_2924, t, _84_2927, n_tps, quals, _84_2931, drange) -> begin
(

let _84_2938 = (new_term_constant_and_tok_from_lid env d)
in (match (_84_2938) with
| (ddconstrsym, ddtok, env) -> begin
(

let ddtok_tm = (FStar_SMTEncoding_Term.mkApp (ddtok, []))
in (

let _84_2942 = (FStar_Syntax_Util.arrow_formals t)
in (match (_84_2942) with
| (formals, t_res) -> begin
(

let _84_2945 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_84_2945) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_SMTEncoding_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (

let _84_2952 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_84_2952) with
| (vars, guards, env', binder_decls, names) -> begin
(

let projectors = (FStar_All.pipe_right names (FStar_List.map (fun x -> (let _175_2156 = (mk_term_projector_name d x)
in (_175_2156, FStar_SMTEncoding_Term.Term_sort)))))
in (

let datacons = (let _175_2158 = (let _175_2157 = (varops.next_id ())
in (ddconstrsym, projectors, FStar_SMTEncoding_Term.Term_sort, _175_2157, true))
in (FStar_All.pipe_right _175_2158 FStar_SMTEncoding_Term.constructor_to_decl))
in (

let app = (mk_Apply ddtok_tm vars)
in (

let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (

let _84_2962 = (encode_term_pred None t env ddtok_tm)
in (match (_84_2962) with
| (tok_typing, decls3) -> begin
(

let _84_2969 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_84_2969) with
| (vars', guards', env'', decls_formals, _84_2968) -> begin
(

let _84_2974 = (

let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars')
in (

let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (encode_term_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_84_2974) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_SMTEncoding_Term.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _84_2978 -> begin
(let _175_2160 = (let _175_2159 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (ddtok, FStar_SMTEncoding_Term.Term_sort) _175_2159))
in (_175_2160)::[])
end)
in (

let encode_elim = (fun _84_2981 -> (match (()) with
| () -> begin
(

let _84_2984 = (FStar_Syntax_Util.head_and_args t_res)
in (match (_84_2984) with
| (head, args) -> begin
(match ((let _175_2163 = (FStar_Syntax_Subst.compress head)
in _175_2163.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let _84_3002 = (encode_args args env')
in (match (_84_3002) with
| (encoded_args, arg_decls) -> begin
(

let _84_3017 = (FStar_List.fold_left (fun _84_3006 arg -> (match (_84_3006) with
| (env, arg_vars, eqns) -> begin
(

let _84_3012 = (let _175_2166 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in (gen_term_var env _175_2166))
in (match (_84_3012) with
| (_84_3009, xv, env) -> begin
(let _175_2168 = (let _175_2167 = (FStar_SMTEncoding_Term.mkEq (arg, xv))
in (_175_2167)::eqns)
in (env, (xv)::arg_vars, _175_2168))
end))
end)) (env', [], []) encoded_args)
in (match (_84_3017) with
| (_84_3014, arg_vars, eqns) -> begin
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

let typing_inversion = (let _175_2175 = (let _175_2174 = (let _175_2173 = (let _175_2172 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _175_2171 = (let _175_2170 = (let _175_2169 = (FStar_SMTEncoding_Term.mk_and_l (FStar_List.append eqns guards))
in (ty_pred, _175_2169))
in (FStar_SMTEncoding_Term.mkImp _175_2170))
in (((ty_pred)::[])::[], _175_2172, _175_2171)))
in (FStar_SMTEncoding_Term.mkForall _175_2173))
in (_175_2174, Some ("data constructor typing elim"), Some ((Prims.strcat "data_elim_" ddconstrsym))))
in FStar_SMTEncoding_Term.Assume (_175_2175))
in (

let subterm_ordering = if (FStar_Ident.lid_equals d FStar_Syntax_Const.lextop_lid) then begin
(

let x = (let _175_2176 = (varops.fresh "x")
in (_175_2176, FStar_SMTEncoding_Term.Term_sort))
in (

let xtm = (FStar_SMTEncoding_Term.mkFreeV x)
in (let _175_2188 = (let _175_2187 = (let _175_2184 = (let _175_2183 = (let _175_2178 = (let _175_2177 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in (_175_2177)::[])
in (_175_2178)::[])
in (let _175_2182 = (let _175_2181 = (let _175_2180 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (let _175_2179 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in (_175_2180, _175_2179)))
in (FStar_SMTEncoding_Term.mkImp _175_2181))
in (_175_2183, (x)::[], _175_2182)))
in (FStar_SMTEncoding_Term.mkForall _175_2184))
in (let _175_2186 = (let _175_2185 = (varops.fresh "lextop")
in Some (_175_2185))
in (_175_2187, Some ("lextop is top"), _175_2186)))
in FStar_SMTEncoding_Term.Assume (_175_2188))))
end else begin
(

let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
[]
end
| FStar_SMTEncoding_Term.Term_sort -> begin
(let _175_2191 = (let _175_2190 = (FStar_SMTEncoding_Term.mkFreeV v)
in (FStar_SMTEncoding_Term.mk_Precedes _175_2190 dapp))
in (_175_2191)::[])
end
| _84_3031 -> begin
(FStar_All.failwith "unexpected sort")
end))))
in (let _175_2198 = (let _175_2197 = (let _175_2196 = (let _175_2195 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _175_2194 = (let _175_2193 = (let _175_2192 = (FStar_SMTEncoding_Term.mk_and_l prec)
in (ty_pred, _175_2192))
in (FStar_SMTEncoding_Term.mkImp _175_2193))
in (((ty_pred)::[])::[], _175_2195, _175_2194)))
in (FStar_SMTEncoding_Term.mkForall _175_2196))
in (_175_2197, Some ("subterm ordering"), Some ((Prims.strcat "subterm_ordering_" ddconstrsym))))
in FStar_SMTEncoding_Term.Assume (_175_2198)))
end
in (arg_decls, (typing_inversion)::(subterm_ordering)::[])))))))))
end))
end)))
end
| _84_3035 -> begin
(

let _84_3036 = (let _175_2201 = (let _175_2200 = (FStar_Syntax_Print.lid_to_string d)
in (let _175_2199 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _175_2200 _175_2199)))
in (FStar_TypeChecker_Errors.warn drange _175_2201))
in ([], []))
end)
end))
end))
in (

let _84_3040 = (encode_elim ())
in (match (_84_3040) with
| (decls2, elim) -> begin
(

let g = (let _175_2226 = (let _175_2225 = (let _175_2210 = (let _175_2209 = (let _175_2208 = (let _175_2207 = (let _175_2206 = (let _175_2205 = (let _175_2204 = (let _175_2203 = (let _175_2202 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" _175_2202))
in Some (_175_2203))
in (ddtok, [], FStar_SMTEncoding_Term.Term_sort, _175_2204))
in FStar_SMTEncoding_Term.DeclFun (_175_2205))
in (_175_2206)::[])
in (FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) decls3) _175_2207))
in (FStar_List.append _175_2208 proxy_fresh))
in (FStar_List.append _175_2209 decls_formals))
in (FStar_List.append _175_2210 decls_pred))
in (let _175_2224 = (let _175_2223 = (let _175_2222 = (let _175_2214 = (let _175_2213 = (let _175_2212 = (let _175_2211 = (FStar_SMTEncoding_Term.mkEq (app, dapp))
in (((app)::[])::[], vars, _175_2211))
in (FStar_SMTEncoding_Term.mkForall _175_2212))
in (_175_2213, Some ("equality for proxy"), Some ((Prims.strcat "equality_tok_" ddtok))))
in FStar_SMTEncoding_Term.Assume (_175_2214))
in (let _175_2221 = (let _175_2220 = (let _175_2219 = (let _175_2218 = (let _175_2217 = (let _175_2216 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) vars')
in (let _175_2215 = (FStar_SMTEncoding_Term.mkImp (guard', ty_pred'))
in (((ty_pred')::[])::[], _175_2216, _175_2215)))
in (FStar_SMTEncoding_Term.mkForall _175_2217))
in (_175_2218, Some ("data constructor typing intro"), Some ((Prims.strcat "data_typing_intro_" ddtok))))
in FStar_SMTEncoding_Term.Assume (_175_2219))
in (_175_2220)::[])
in (_175_2222)::_175_2221))
in (FStar_SMTEncoding_Term.Assume ((tok_typing, Some ("typing for data constructor proxy"), Some ((Prims.strcat "typing_tok_" ddtok)))))::_175_2223)
in (FStar_List.append _175_2225 _175_2224)))
in (FStar_List.append _175_2226 elim))
in ((FStar_List.append datacons g), env))
end)))))
end))
end))
end))))))))
end)))
end))
end)))
end))
end)))
and encode_signature : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _84_3046 se -> (match (_84_3046) with
| (g, env) -> begin
(

let _84_3050 = (encode_sigelt env se)
in (match (_84_3050) with
| (g', env) -> begin
((FStar_List.append g g'), env)
end))
end)) ([], env))))


let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings -> (

let encode_binding = (fun b _84_3057 -> (match (_84_3057) with
| (decls, env) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (_84_3059) -> begin
([], env)
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(

let _84_3066 = (new_term_constant env x)
in (match (_84_3066) with
| (xxsym, xx, env') -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (

let _84_3068 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _175_2241 = (FStar_Syntax_Print.bv_to_string x)
in (let _175_2240 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _175_2239 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" _175_2241 _175_2240 _175_2239))))
end else begin
()
end
in (

let _84_3072 = (encode_term_pred None t1 env xx)
in (match (_84_3072) with
| (t, decls') -> begin
(

let caption = if (FStar_Options.log_queries ()) then begin
(let _175_2245 = (let _175_2244 = (FStar_Syntax_Print.bv_to_string x)
in (let _175_2243 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _175_2242 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _175_2244 _175_2243 _175_2242))))
in Some (_175_2245))
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
| FStar_TypeChecker_Env.Binding_lid (x, (_84_3079, t)) -> begin
(

let t_norm = (whnf env t)
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant None)
in (

let _84_3088 = (encode_free_var env fv t t_norm [])
in (match (_84_3088) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end))))
end
| (FStar_TypeChecker_Env.Binding_sig_inst (_, se, _)) | (FStar_TypeChecker_Env.Binding_sig (_, se)) -> begin
(

let _84_3102 = (encode_sigelt env se)
in (match (_84_3102) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end))
end)
end))
in (FStar_List.fold_right encode_binding bindings ([], env))))


let encode_labels = (fun labs -> (

let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _84_3109 -> (match (_84_3109) with
| (l, _84_3106, _84_3108) -> begin
FStar_SMTEncoding_Term.DeclFun (((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _84_3116 -> (match (_84_3116) with
| (l, _84_3113, _84_3115) -> begin
(let _175_2253 = (FStar_All.pipe_left (fun _175_2249 -> FStar_SMTEncoding_Term.Echo (_175_2249)) (Prims.fst l))
in (let _175_2252 = (let _175_2251 = (let _175_2250 = (FStar_SMTEncoding_Term.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (_175_2250))
in (_175_2251)::[])
in (_175_2253)::_175_2252))
end))))
in (prefix, suffix))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (let _175_2258 = (let _175_2257 = (let _175_2256 = (FStar_Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _175_2256; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_175_2257)::[])
in (FStar_ST.op_Colon_Equals last_env _175_2258)))


let get_env : FStar_TypeChecker_Env.env  ->  env_t = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "No env; call init first!")
end
| (e)::_84_3122 -> begin
(

let _84_3125 = e
in {bindings = _84_3125.bindings; depth = _84_3125.depth; tcenv = tcenv; warn = _84_3125.warn; cache = _84_3125.cache; nolabels = _84_3125.nolabels; use_zfuel_name = _84_3125.use_zfuel_name; encode_non_total_function_typ = _84_3125.encode_non_total_function_typ})
end))


let set_env : env_t  ->  Prims.unit = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| (_84_3131)::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))


let push_env : Prims.unit  ->  Prims.unit = (fun _84_3133 -> (match (()) with
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

let _84_3139 = hd
in {bindings = _84_3139.bindings; depth = _84_3139.depth; tcenv = _84_3139.tcenv; warn = _84_3139.warn; cache = refs; nolabels = _84_3139.nolabels; use_zfuel_name = _84_3139.use_zfuel_name; encode_non_total_function_typ = _84_3139.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))


let pop_env : Prims.unit  ->  Prims.unit = (fun _84_3142 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Popping an empty stack")
end
| (_84_3146)::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))


let mark_env : Prims.unit  ->  Prims.unit = (fun _84_3148 -> (match (()) with
| () -> begin
(push_env ())
end))


let reset_mark_env : Prims.unit  ->  Prims.unit = (fun _84_3149 -> (match (()) with
| () -> begin
(pop_env ())
end))


let commit_mark_env : Prims.unit  ->  Prims.unit = (fun _84_3150 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| (hd)::(_84_3153)::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _84_3158 -> begin
(FStar_All.failwith "Impossible")
end)
end))


let init : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (

let _84_3160 = (init_env tcenv)
in (

let _84_3162 = (FStar_SMTEncoding_Z3.init ())
in (FStar_SMTEncoding_Z3.giveZ3 ((FStar_SMTEncoding_Term.DefPrelude)::[])))))


let push : Prims.string  ->  Prims.unit = (fun msg -> (

let _84_3165 = (push_env ())
in (

let _84_3167 = (varops.push ())
in (FStar_SMTEncoding_Z3.push msg))))


let pop : Prims.string  ->  Prims.unit = (fun msg -> (

let _84_3170 = (let _175_2279 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _175_2279))
in (

let _84_3172 = (varops.pop ())
in (FStar_SMTEncoding_Z3.pop msg))))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _84_3175 = (mark_env ())
in (

let _84_3177 = (varops.mark ())
in (FStar_SMTEncoding_Z3.mark msg))))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _84_3180 = (reset_mark_env ())
in (

let _84_3182 = (varops.reset_mark ())
in (FStar_SMTEncoding_Z3.reset_mark msg))))


let commit_mark = (fun msg -> (

let _84_3185 = (commit_mark_env ())
in (

let _84_3187 = (varops.commit_mark ())
in (FStar_SMTEncoding_Z3.commit_mark msg))))


let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (

let caption = (fun decls -> if (FStar_Options.log_queries ()) then begin
(let _175_2295 = (let _175_2294 = (let _175_2293 = (let _175_2292 = (let _175_2291 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _175_2291 (FStar_List.map FStar_Syntax_Print.lid_to_string)))
in (FStar_All.pipe_right _175_2292 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " _175_2293))
in FStar_SMTEncoding_Term.Caption (_175_2294))
in (_175_2295)::decls)
end else begin
decls
end)
in (

let env = (get_env tcenv)
in (

let _84_3196 = (encode_sigelt env se)
in (match (_84_3196) with
| (decls, env) -> begin
(

let _84_3197 = (set_env env)
in (let _175_2296 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 _175_2296)))
end)))))


let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let _84_3202 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(let _175_2301 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name _175_2301))
end else begin
()
end
in (

let env = (get_env tcenv)
in (

let _84_3209 = (encode_signature (

let _84_3205 = env
in {bindings = _84_3205.bindings; depth = _84_3205.depth; tcenv = _84_3205.tcenv; warn = false; cache = _84_3205.cache; nolabels = _84_3205.nolabels; use_zfuel_name = _84_3205.use_zfuel_name; encode_non_total_function_typ = _84_3205.encode_non_total_function_typ}) modul.FStar_Syntax_Syntax.exports)
in (match (_84_3209) with
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

let _84_3215 = (set_env (

let _84_3213 = env
in {bindings = _84_3213.bindings; depth = _84_3213.depth; tcenv = _84_3213.tcenv; warn = true; cache = _84_3213.cache; nolabels = _84_3213.nolabels; use_zfuel_name = _84_3213.use_zfuel_name; encode_non_total_function_typ = _84_3213.encode_non_total_function_typ}))
in (

let _84_3217 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
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

let _84_3246 = (

let rec aux = (fun bindings -> (match (bindings) with
| (FStar_TypeChecker_Env.Binding_var (x))::rest -> begin
(

let _84_3235 = (aux rest)
in (match (_84_3235) with
| (out, rest) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (let _175_2323 = (let _175_2322 = (FStar_Syntax_Syntax.mk_binder (

let _84_3237 = x
in {FStar_Syntax_Syntax.ppname = _84_3237.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _84_3237.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_175_2322)::out)
in (_175_2323, rest)))
end))
end
| _84_3240 -> begin
([], bindings)
end))
in (

let _84_3243 = (aux bindings)
in (match (_84_3243) with
| (closing, bindings) -> begin
(let _175_2324 = (FStar_Syntax_Util.close_forall (FStar_List.rev closing) q)
in (_175_2324, bindings))
end)))
in (match (_84_3246) with
| (q, bindings) -> begin
(

let _84_3255 = (let _175_2326 = (FStar_List.filter (fun _84_24 -> (match (_84_24) with
| FStar_TypeChecker_Env.Binding_sig (_84_3249) -> begin
false
end
| _84_3252 -> begin
true
end)) bindings)
in (encode_env_bindings env _175_2326))
in (match (_84_3255) with
| (env_decls, env) -> begin
(

let _84_3256 = if (((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTQuery")))) then begin
(let _175_2327 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" _175_2327))
end else begin
()
end
in (

let _84_3260 = (encode_formula q env)
in (match (_84_3260) with
| (phi, qdecls) -> begin
(

let _84_3265 = (let _175_2328 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg _175_2328 phi))
in (match (_84_3265) with
| (phi, labels, _84_3264) -> begin
(

let _84_3268 = (encode_labels labels)
in (match (_84_3268) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append (FStar_List.append env_decls label_prefix) qdecls)
in (

let qry = (let _175_2332 = (let _175_2331 = (FStar_SMTEncoding_Term.mkNot phi)
in (let _175_2330 = (let _175_2329 = (varops.fresh "@query")
in Some (_175_2329))
in (_175_2331, Some ("query"), _175_2330)))
in FStar_SMTEncoding_Term.Assume (_175_2332))
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

let _84_3275 = (push "query")
in (

let _84_3280 = (encode_formula q env)
in (match (_84_3280) with
| (f, _84_3279) -> begin
(

let _84_3281 = (pop "query")
in (match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _84_3285) -> begin
true
end
| _84_3289 -> begin
false
end))
end)))))




