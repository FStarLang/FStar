
open Prims

let add_fuel = (fun x tl -> if (FStar_Options.unthrottle_inductives ()) then begin
tl
end else begin
(x)::tl
end)


let withenv = (fun c _85_30 -> (match (_85_30) with
| (a, b) -> begin
((a), (b), (c))
end))


let vargs = (fun args -> (FStar_List.filter (fun _85_1 -> (match (_85_1) with
| (FStar_Util.Inl (_85_34), _85_37) -> begin
false
end
| _85_40 -> begin
true
end)) args))


let subst_lcomp_opt = (fun s l -> (match (l) with
| Some (FStar_Util.Inl (l)) -> begin
(let _177_12 = (let _177_11 = (let _177_10 = (let _177_9 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp s _177_9))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _177_10))
in FStar_Util.Inl (_177_11))
in Some (_177_12))
end
| _85_47 -> begin
l
end))


let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s '\'' '_'))


let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun lid a -> (

let a = (

let _85_51 = a
in (let _177_19 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _177_19; FStar_Syntax_Syntax.index = _85_51.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _85_51.FStar_Syntax_Syntax.sort}))
in (let _177_20 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str a.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (FStar_All.pipe_left escape _177_20))))


let primitive_projector_by_pos : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (

let fail = (fun _85_58 -> (match (()) with
| () -> begin
(let _177_30 = (let _177_29 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" _177_29 lid.FStar_Ident.str))
in (FStar_All.failwith _177_30))
end))
in (

let _85_62 = (FStar_TypeChecker_Env.lookup_datacon env lid)
in (match (_85_62) with
| (_85_60, t) -> begin
(match ((let _177_31 = (FStar_Syntax_Subst.compress t)
in _177_31.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _85_70 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_85_70) with
| (binders, _85_69) -> begin
if ((i < 0) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(

let b = (FStar_List.nth binders i)
in (mk_term_projector_name lid (Prims.fst b)))
end
end))
end
| _85_73 -> begin
(fail ())
end)
end))))


let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (let _177_37 = (let _177_36 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str _177_36))
in (FStar_All.pipe_left escape _177_37)))


let mk_term_projector : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun lid a -> (let _177_43 = (let _177_42 = (mk_term_projector_name lid a)
in ((_177_42), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Term.mkFreeV _177_43)))


let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_SMTEncoding_Term.term = (fun lid i -> (let _177_49 = (let _177_48 = (mk_term_projector_name_by_pos lid i)
in ((_177_48), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Term.mkFreeV _177_49)))


let mk_data_tester = (fun env l x -> (FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x))


type varops_t =
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; mark : Prims.unit  ->  Prims.unit; reset_mark : Prims.unit  ->  Prims.unit; commit_mark : Prims.unit  ->  Prims.unit; new_var : FStar_Ident.ident  ->  Prims.int  ->  Prims.string; new_fvar : FStar_Ident.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_SMTEncoding_Term.term; next_id : Prims.unit  ->  Prims.int}


let is_Mkvarops_t : varops_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkvarops_t"))))


let varops : varops_t = (

let initial_ctr = 100
in (

let ctr = (FStar_Util.mk_ref initial_ctr)
in (

let new_scope = (fun _85_97 -> (match (()) with
| () -> begin
(let _177_153 = (FStar_Util.smap_create 100)
in (let _177_152 = (FStar_Util.smap_create 100)
in ((_177_153), (_177_152))))
end))
in (

let scopes = (let _177_155 = (let _177_154 = (new_scope ())
in (_177_154)::[])
in (FStar_Util.mk_ref _177_155))
in (

let mk_unique = (fun y -> (

let y = (escape y)
in (

let y = (match ((let _177_159 = (FStar_ST.read scopes)
in (FStar_Util.find_map _177_159 (fun _85_105 -> (match (_85_105) with
| (names, _85_104) -> begin
(FStar_Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_85_108) -> begin
(

let _85_110 = (FStar_Util.incr ctr)
in (let _177_161 = (let _177_160 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _177_160))
in (Prims.strcat (Prims.strcat y "__") _177_161)))
end)
in (

let top_scope = (let _177_163 = (let _177_162 = (FStar_ST.read scopes)
in (FStar_List.hd _177_162))
in (FStar_All.pipe_left Prims.fst _177_163))
in (

let _85_114 = (FStar_Util.smap_add top_scope y true)
in y)))))
in (

let new_var = (fun pp rn -> (let _177_170 = (let _177_168 = (FStar_All.pipe_left mk_unique pp.FStar_Ident.idText)
in (Prims.strcat _177_168 "__"))
in (let _177_169 = (FStar_Util.string_of_int rn)
in (Prims.strcat _177_170 _177_169))))
in (

let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (

let next_id = (fun _85_122 -> (match (()) with
| () -> begin
(

let _85_123 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end))
in (

let fresh = (fun pfx -> (let _177_178 = (let _177_177 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _177_177))
in (FStar_Util.format2 "%s_%s" pfx _177_178)))
in (

let string_const = (fun s -> (match ((let _177_182 = (FStar_ST.read scopes)
in (FStar_Util.find_map _177_182 (fun _85_132 -> (match (_85_132) with
| (_85_130, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))) with
| Some (f) -> begin
f
end
| None -> begin
(

let id = (next_id ())
in (

let f = (let _177_183 = (FStar_SMTEncoding_Term.mk_String_const id)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString _177_183))
in (

let top_scope = (let _177_185 = (let _177_184 = (FStar_ST.read scopes)
in (FStar_List.hd _177_184))
in (FStar_All.pipe_left Prims.snd _177_185))
in (

let _85_139 = (FStar_Util.smap_add top_scope s f)
in f))))
end))
in (

let push = (fun _85_142 -> (match (()) with
| () -> begin
(let _177_190 = (let _177_189 = (new_scope ())
in (let _177_188 = (FStar_ST.read scopes)
in (_177_189)::_177_188))
in (FStar_ST.op_Colon_Equals scopes _177_190))
end))
in (

let pop = (fun _85_144 -> (match (()) with
| () -> begin
(let _177_194 = (let _177_193 = (FStar_ST.read scopes)
in (FStar_List.tl _177_193))
in (FStar_ST.op_Colon_Equals scopes _177_194))
end))
in (

let mark = (fun _85_146 -> (match (()) with
| () -> begin
(push ())
end))
in (

let reset_mark = (fun _85_148 -> (match (()) with
| () -> begin
(pop ())
end))
in (

let commit_mark = (fun _85_150 -> (match (()) with
| () -> begin
(match ((FStar_ST.read scopes)) with
| ((hd1, hd2))::((next1, next2))::tl -> begin
(

let _85_163 = (FStar_Util.smap_fold hd1 (fun key value v -> (FStar_Util.smap_add next1 key value)) ())
in (

let _85_168 = (FStar_Util.smap_fold hd2 (fun key value v -> (FStar_Util.smap_add next2 key value)) ())
in (FStar_ST.op_Colon_Equals scopes ((((next1), (next2)))::tl))))
end
| _85_171 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id})))))))))))))))


let unmangle : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv = (fun x -> (

let _85_173 = x
in (let _177_209 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _177_209; FStar_Syntax_Syntax.index = _85_173.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _85_173.FStar_Syntax_Syntax.sort})))


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
| Binding_var (_85_177) -> begin
_85_177
end))


let ___Binding_fvar____0 = (fun projectee -> (match (projectee) with
| Binding_fvar (_85_180) -> begin
_85_180
end))


let binder_of_eithervar = (fun v -> ((v), (None)))


type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_TypeChecker_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_SMTEncoding_Term.sort Prims.list * FStar_SMTEncoding_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}


let is_Mkenv_t : env_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_t"))))


let print_env : env_t  ->  Prims.string = (fun e -> (let _177_267 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun _85_2 -> (match (_85_2) with
| Binding_var (x, _85_195) -> begin
(FStar_Syntax_Print.bv_to_string x)
end
| Binding_fvar (l, _85_200, _85_202, _85_204) -> begin
(FStar_Syntax_Print.lid_to_string l)
end))))
in (FStar_All.pipe_right _177_267 (FStar_String.concat ", "))))


let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))


let caption_t : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.string Prims.option = (fun env t -> if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _177_277 = (FStar_Syntax_Print.term_to_string t)
in Some (_177_277))
end else begin
None
end)


let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (

let xsym = (varops.fresh x)
in (let _177_282 = (FStar_SMTEncoding_Term.mkFreeV ((xsym), (s)))
in ((xsym), (_177_282)))))


let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (let _177_287 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _177_287))
in (

let y = (FStar_SMTEncoding_Term.mkFreeV ((ysym), (FStar_SMTEncoding_Term.Term_sort)))
in ((ysym), (y), ((

let _85_218 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = (env.depth + 1); tcenv = _85_218.tcenv; warn = _85_218.warn; cache = _85_218.cache; nolabels = _85_218.nolabels; use_zfuel_name = _85_218.use_zfuel_name; encode_non_total_function_typ = _85_218.encode_non_total_function_typ}))))))


let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (

let y = (FStar_SMTEncoding_Term.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let _85_224 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = _85_224.depth; tcenv = _85_224.tcenv; warn = _85_224.warn; cache = _85_224.cache; nolabels = _85_224.nolabels; use_zfuel_name = _85_224.use_zfuel_name; encode_non_total_function_typ = _85_224.encode_non_total_function_typ}))))))


let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (

let _85_229 = env
in {bindings = (Binding_var (((x), (t))))::env.bindings; depth = _85_229.depth; tcenv = _85_229.tcenv; warn = _85_229.warn; cache = _85_229.cache; nolabels = _85_229.nolabels; use_zfuel_name = _85_229.use_zfuel_name; encode_non_total_function_typ = _85_229.encode_non_total_function_typ}))


let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (match ((lookup_binding env (fun _85_3 -> (match (_85_3) with
| Binding_var (b, t) when (FStar_Syntax_Syntax.bv_eq b a) -> begin
Some (((b), (t)))
end
| _85_239 -> begin
None
end)))) with
| None -> begin
(let _177_304 = (let _177_303 = (FStar_Syntax_Print.bv_to_string a)
in (FStar_Util.format1 "Bound term variable not found: %s" _177_303))
in (FStar_All.failwith _177_304))
end
| Some (b, t) -> begin
t
end))


let new_term_constant_and_tok_from_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * Prims.string * env_t) = (fun env x -> (

let fname = (varops.new_fvar x)
in (

let ftok = (Prims.strcat fname "@tok")
in (let _177_315 = (

let _85_249 = env
in (let _177_314 = (let _177_313 = (let _177_312 = (let _177_311 = (let _177_310 = (FStar_SMTEncoding_Term.mkApp ((ftok), ([])))
in (FStar_All.pipe_left (fun _177_309 -> Some (_177_309)) _177_310))
in ((x), (fname), (_177_311), (None)))
in Binding_fvar (_177_312))
in (_177_313)::env.bindings)
in {bindings = _177_314; depth = _85_249.depth; tcenv = _85_249.tcenv; warn = _85_249.warn; cache = _85_249.cache; nolabels = _85_249.nolabels; use_zfuel_name = _85_249.use_zfuel_name; encode_non_total_function_typ = _85_249.encode_non_total_function_typ}))
in ((fname), (ftok), (_177_315))))))


let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun _85_4 -> (match (_85_4) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some (((t1), (t2), (t3)))
end
| _85_261 -> begin
None
end))))


let contains_name : env_t  ->  Prims.string  ->  Prims.bool = (fun env s -> (let _177_326 = (lookup_binding env (fun _85_5 -> (match (_85_5) with
| Binding_fvar (b, t1, t2, t3) when (b.FStar_Ident.str = s) -> begin
Some (())
end
| _85_272 -> begin
None
end)))
in (FStar_All.pipe_right _177_326 FStar_Option.isSome)))


let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _177_332 = (let _177_331 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" _177_331))
in (FStar_All.failwith _177_332))
end
| Some (s) -> begin
s
end))


let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (

let _85_282 = env
in {bindings = (Binding_fvar (((x), (fname), (ftok), (None))))::env.bindings; depth = _85_282.depth; tcenv = _85_282.tcenv; warn = _85_282.warn; cache = _85_282.cache; nolabels = _85_282.nolabels; use_zfuel_name = _85_282.use_zfuel_name; encode_non_total_function_typ = _85_282.encode_non_total_function_typ}))


let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (

let _85_291 = (lookup_lid env x)
in (match (_85_291) with
| (t1, t2, _85_290) -> begin
(

let t3 = (let _177_349 = (let _177_348 = (let _177_347 = (FStar_SMTEncoding_Term.mkApp (("ZFuel"), ([])))
in (_177_347)::[])
in ((f), (_177_348)))
in (FStar_SMTEncoding_Term.mkApp _177_349))
in (

let _85_293 = env
in {bindings = (Binding_fvar (((x), (t1), (t2), (Some (t3)))))::env.bindings; depth = _85_293.depth; tcenv = _85_293.tcenv; warn = _85_293.warn; cache = _85_293.cache; nolabels = _85_293.nolabels; use_zfuel_name = _85_293.use_zfuel_name; encode_non_total_function_typ = _85_293.encode_non_total_function_typ}))
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
| _85_306 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (_85_310, (fuel)::[]) -> begin
if (let _177_355 = (let _177_354 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right _177_354 Prims.fst))
in (FStar_Util.starts_with _177_355 "fuel")) then begin
(let _177_358 = (let _177_357 = (FStar_SMTEncoding_Term.mkFreeV ((name), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_ApplyTF _177_357 fuel))
in (FStar_All.pipe_left (fun _177_356 -> Some (_177_356)) _177_358))
end else begin
Some (t)
end
end
| _85_316 -> begin
Some (t)
end)
end
| _85_318 -> begin
None
end)
end)
end))


let lookup_free_var = (fun env a -> (match ((try_lookup_free_var env a.FStar_Syntax_Syntax.v)) with
| Some (t) -> begin
t
end
| None -> begin
(let _177_362 = (let _177_361 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _177_361))
in (FStar_All.failwith _177_362))
end))


let lookup_free_var_name = (fun env a -> (

let _85_331 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_85_331) with
| (x, _85_328, _85_330) -> begin
x
end)))


let lookup_free_var_sym = (fun env a -> (

let _85_337 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_85_337) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.hash = _85_341; FStar_SMTEncoding_Term.freevars = _85_339}) when env.use_zfuel_name -> begin
((g), (zf))
end
| _85_349 -> begin
(match (sym) with
| None -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end
| Some (sym) -> begin
(match (sym.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, (fuel)::[]) -> begin
((g), ((fuel)::[]))
end
| _85_359 -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end)
end)
end)
end)))


let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun _85_6 -> (match (_85_6) with
| Binding_fvar (_85_364, nm', tok, _85_368) when (nm = nm') -> begin
tok
end
| _85_372 -> begin
None
end))))


let mkForall_fuel' = (fun n _85_377 -> (match (_85_377) with
| (pats, vars, body) -> begin
(

let fallback = (fun _85_379 -> (match (()) with
| () -> begin
(FStar_SMTEncoding_Term.mkForall ((pats), (vars), (body)))
end))
in if (FStar_Options.unthrottle_inductives ()) then begin
(fallback ())
end else begin
(

let _85_382 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_85_382) with
| (fsym, fterm) -> begin
(

let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Term.mkApp (("HasTypeFuel"), ((fterm)::args)))
end
| _85_392 -> begin
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
(let _177_379 = (add_fuel guards)
in (FStar_SMTEncoding_Term.mk_and_l _177_379))
end
| _85_405 -> begin
(let _177_380 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _177_380 FStar_List.hd))
end)
in (FStar_SMTEncoding_Term.mkImp ((guard), (body'))))
end
| _85_408 -> begin
body
end)
in (

let vars = (((fsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars
in (FStar_SMTEncoding_Term.mkForall ((pats), (vars), (body)))))))
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
(let _177_386 = (FStar_TypeChecker_Env.lookup_definition FStar_TypeChecker_Env.OnlyInline env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _177_386 FStar_Option.isNone))
end
| _85_447 -> begin
false
end)))


let head_redex : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (match ((let _177_391 = (FStar_Syntax_Util.un_uinst t)
in _177_391.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_85_451) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(let _177_392 = (FStar_TypeChecker_Env.lookup_definition FStar_TypeChecker_Env.OnlyInline env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _177_392 FStar_Option.isSome))
end
| _85_456 -> begin
false
end))


let whnf : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> if (head_normal env t) then begin
t
end else begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
end)


let norm : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t))


let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (let _177_405 = (let _177_403 = (FStar_Syntax_Syntax.null_binder t)
in (_177_403)::[])
in (let _177_404 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Util.abs _177_405 _177_404 None))))


let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(let _177_412 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out _177_412))
end
| s -> begin
(

let _85_468 = ()
in (let _177_413 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTT out _177_413)))
end)) e)))


let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Term.mk_ApplyTT e)))


let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun _85_7 -> (match (_85_7) with
| (FStar_SMTEncoding_Term.Var ("ApplyTT")) | (FStar_SMTEncoding_Term.Var ("ApplyTF")) -> begin
true
end
| _85_478 -> begin
false
end))


let is_eta : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env vars t -> (

let rec aux = (fun t xs -> (match (((t.FStar_SMTEncoding_Term.tm), (xs))) with
| (FStar_SMTEncoding_Term.App (app, (f)::({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.hash = _85_489; FStar_SMTEncoding_Term.freevars = _85_487})::[]), (x)::xs) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), _85_507) -> begin
if (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v)
end
| _85_514 -> begin
false
end)) args vars)) then begin
(tok_of_name env f)
end else begin
None
end
end
| (_85_516, []) -> begin
(

let fvs = (FStar_SMTEncoding_Term.free_variables t)
in if (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (not ((FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)))))) then begin
Some (t)
end else begin
None
end)
end
| _85_522 -> begin
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


let encode_const : FStar_Const.sconst  ->  FStar_SMTEncoding_Term.term = (fun _85_8 -> (match (_85_8) with
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
(let _177_470 = (let _177_469 = (let _177_468 = (let _177_467 = (FStar_SMTEncoding_Term.mkInteger' (FStar_Util.int_of_char c))
in (FStar_SMTEncoding_Term.boxInt _177_467))
in (_177_468)::[])
in (("FStar.Char.Char"), (_177_469)))
in (FStar_SMTEncoding_Term.mkApp _177_470))
end
| FStar_Const.Const_int (i, None) -> begin
(let _177_471 = (FStar_SMTEncoding_Term.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt _177_471))
end
| FStar_Const.Const_int (i, Some (_85_542)) -> begin
(FStar_All.failwith "Machine integers should be desugared")
end
| FStar_Const.Const_string (bytes, _85_548) -> begin
(let _177_472 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _177_472))
end
| FStar_Const.Const_range (r) -> begin
FStar_SMTEncoding_Term.mk_Range_const
end
| FStar_Const.Const_effect -> begin
FStar_SMTEncoding_Term.mk_Term_type
end
| c -> begin
(let _177_474 = (let _177_473 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" _177_473))
in (FStar_All.failwith _177_474))
end))


let as_function_typ : env_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (

let rec aux = (fun norm t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_85_562) -> begin
t
end
| FStar_Syntax_Syntax.Tm_refine (_85_565) -> begin
(let _177_483 = (FStar_Syntax_Util.unrefine t)
in (aux true _177_483))
end
| _85_568 -> begin
if norm then begin
(let _177_484 = (whnf env t)
in (aux false _177_484))
end else begin
(let _177_487 = (let _177_486 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (let _177_485 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _177_486 _177_485)))
in (FStar_All.failwith _177_487))
end
end)))
in (aux true t0)))


let curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun k -> (

let k = (FStar_Syntax_Subst.compress k)
in (match (k.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| _85_576 -> begin
(let _177_490 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (_177_490)))
end)))


let rec encode_binders : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> (

let _85_580 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _177_538 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" _177_538))
end else begin
()
end
in (

let _85_608 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _85_587 b -> (match (_85_587) with
| (vars, guards, env, decls, names) -> begin
(

let _85_602 = (

let x = (unmangle (Prims.fst b))
in (

let _85_593 = (gen_term_var env x)
in (match (_85_593) with
| (xxsym, xx, env') -> begin
(

let _85_596 = (let _177_541 = (norm env x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt _177_541 env xx))
in (match (_85_596) with
| (guard_x_t, decls') -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (guard_x_t), (env'), (decls'), (x))
end))
end)))
in (match (_85_602) with
| (v, g, env, decls', n) -> begin
(((v)::vars), ((g)::guards), (env), ((FStar_List.append decls decls')), ((n)::names))
end))
end)) (([]), ([]), (env), ([]), ([]))))
in (match (_85_608) with
| (vars, guards, env, decls, names) -> begin
(((FStar_List.rev vars)), ((FStar_List.rev guards)), (env), (decls), ((FStar_List.rev names)))
end))))
and encode_term_pred : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let _85_615 = (encode_term t env)
in (match (_85_615) with
| (t, decls) -> begin
(let _177_546 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t)
in ((_177_546), (decls)))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let _85_622 = (encode_term t env)
in (match (_85_622) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _177_551 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t)
in ((_177_551), (decls)))
end
| Some (f) -> begin
(let _177_552 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t)
in ((_177_552), (decls)))
end)
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let t0 = (FStar_Syntax_Subst.compress t)
in (

let _85_629 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _177_557 = (FStar_Syntax_Print.tag_of_term t)
in (let _177_556 = (FStar_Syntax_Print.tag_of_term t0)
in (let _177_555 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" _177_557 _177_556 _177_555))))
end else begin
()
end
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _177_562 = (let _177_561 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (let _177_560 = (FStar_Syntax_Print.tag_of_term t0)
in (let _177_559 = (FStar_Syntax_Print.term_to_string t0)
in (let _177_558 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _177_561 _177_560 _177_559 _177_558)))))
in (FStar_All.failwith _177_562))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _177_564 = (let _177_563 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" _177_563))
in (FStar_All.failwith _177_564))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, k, _85_640) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_meta (t, _85_645) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t = (lookup_term_var env x)
in ((t), ([])))
end
| FStar_Syntax_Syntax.Tm_fvar (v) -> begin
(let _177_565 = (lookup_free_var env v.FStar_Syntax_Syntax.fv_name)
in ((_177_565), ([])))
end
| FStar_Syntax_Syntax.Tm_type (_85_654) -> begin
((FStar_SMTEncoding_Term.mk_Term_type), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t, _85_658) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(let _177_566 = (encode_const c)
in ((_177_566), ([])))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _85_669 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_85_669) with
| (binders, res) -> begin
if ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res)) then begin
(

let _85_676 = (encode_binders None binders env)
in (match (_85_676) with
| (vars, guards, env', decls, _85_675) -> begin
(

let fsym = (let _177_567 = (varops.fresh "f")
in ((_177_567), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (

let app = (mk_Apply f vars)
in (

let _85_682 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv res)
in (match (_85_682) with
| (pre_opt, res_t) -> begin
(

let _85_685 = (encode_term_pred None res_t env' app)
in (match (_85_685) with
| (res_pred, decls') -> begin
(

let _85_694 = (match (pre_opt) with
| None -> begin
(let _177_568 = (FStar_SMTEncoding_Term.mk_and_l guards)
in ((_177_568), ([])))
end
| Some (pre) -> begin
(

let _85_691 = (encode_formula pre env')
in (match (_85_691) with
| (guard, decls0) -> begin
(let _177_569 = (FStar_SMTEncoding_Term.mk_and_l ((guard)::guards))
in ((_177_569), (decls0)))
end))
end)
in (match (_85_694) with
| (guards, guard_decls) -> begin
(

let t_interp = (let _177_571 = (let _177_570 = (FStar_SMTEncoding_Term.mkImp ((guards), (res_pred)))
in ((((app)::[])::[]), (vars), (_177_570)))
in (FStar_SMTEncoding_Term.mkForall _177_571))
in (

let cvars = (let _177_573 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right _177_573 (FStar_List.filter (fun _85_699 -> (match (_85_699) with
| (x, _85_698) -> begin
(x <> (Prims.fst fsym))
end)))))
in (

let tkey = (FStar_SMTEncoding_Term.mkForall (([]), ((fsym)::cvars), (t_interp)))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t', sorts, _85_705) -> begin
(let _177_576 = (let _177_575 = (let _177_574 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in ((t'), (_177_574)))
in (FStar_SMTEncoding_Term.mkApp _177_575))
in ((_177_576), ([])))
end
| None -> begin
(

let tsym = (varops.fresh "Tm_arrow")
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let caption = if (FStar_Options.log_queries ()) then begin
(let _177_577 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in Some (_177_577))
end else begin
None
end
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (caption)))
in (

let t = (let _177_579 = (let _177_578 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in ((tsym), (_177_578)))
in (FStar_SMTEncoding_Term.mkApp _177_579))
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let k_assumption = (

let a_name = Some ((Prims.strcat "kinding_" tsym))
in (let _177_581 = (let _177_580 = (FStar_SMTEncoding_Term.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((_177_580), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_177_581)))
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t)
in (

let pre_typing = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in (let _177_588 = (let _177_587 = (let _177_586 = (let _177_585 = (let _177_584 = (let _177_583 = (let _177_582 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _177_582))
in ((f_has_t), (_177_583)))
in (FStar_SMTEncoding_Term.mkImp _177_584))
in ((((f_has_t)::[])::[]), ((fsym)::cvars), (_177_585)))
in (mkForall_fuel _177_586))
in ((_177_587), (Some ("pre-typing for functions")), (a_name)))
in FStar_SMTEncoding_Term.Assume (_177_588)))
in (

let t_interp = (

let a_name = Some ((Prims.strcat "interpretation_" tsym))
in (let _177_592 = (let _177_591 = (let _177_590 = (let _177_589 = (FStar_SMTEncoding_Term.mkIff ((f_has_t_z), (t_interp)))
in ((((f_has_t_z)::[])::[]), ((fsym)::cvars), (_177_589)))
in (FStar_SMTEncoding_Term.mkForall _177_590))
in ((_177_591), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_177_592)))
in (

let t_decls = (FStar_List.append (FStar_List.append (FStar_List.append ((tdecl)::decls) decls') guard_decls) ((k_assumption)::(pre_typing)::(t_interp)::[]))
in (

let _85_724 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash ((tsym), (cvar_sorts), (t_decls)))
in ((t), (t_decls)))))))))))))))
end))))
end))
end))
end)))))
end))
end else begin
(

let tsym = (varops.fresh "Non_total_Tm_arrow")
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let t = (FStar_SMTEncoding_Term.mkApp ((tsym), ([])))
in (

let t_kinding = (

let a_name = Some ((Prims.strcat "non_total_function_typing_" tsym))
in (let _177_594 = (let _177_593 = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in ((_177_593), (Some ("Typing for non-total arrows")), (a_name)))
in FStar_SMTEncoding_Term.Assume (_177_594)))
in (

let fsym = (("f"), (FStar_SMTEncoding_Term.Term_sort))
in (

let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let t_interp = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in (let _177_601 = (let _177_600 = (let _177_599 = (let _177_598 = (let _177_597 = (let _177_596 = (let _177_595 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _177_595))
in ((f_has_t), (_177_596)))
in (FStar_SMTEncoding_Term.mkImp _177_597))
in ((((f_has_t)::[])::[]), ((fsym)::[]), (_177_598)))
in (mkForall_fuel _177_599))
in ((_177_600), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_177_601)))
in ((t), ((tdecl)::(t_kinding)::(t_interp)::[]))))))))))
end
end))
end
| FStar_Syntax_Syntax.Tm_refine (_85_737) -> begin
(

let _85_757 = (match ((FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.tk = _85_744; FStar_Syntax_Syntax.pos = _85_742; FStar_Syntax_Syntax.vars = _85_740} -> begin
(

let _85_752 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) f)
in (match (_85_752) with
| (b, f) -> begin
(let _177_603 = (let _177_602 = (FStar_List.hd b)
in (Prims.fst _177_602))
in ((_177_603), (f)))
end))
end
| _85_754 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_85_757) with
| (x, f) -> begin
(

let _85_760 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (_85_760) with
| (base_t, decls) -> begin
(

let _85_764 = (gen_term_var env x)
in (match (_85_764) with
| (x, xtm, env') -> begin
(

let _85_767 = (encode_formula f env')
in (match (_85_767) with
| (refinement, decls') -> begin
(

let _85_770 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_85_770) with
| (fsym, fterm) -> begin
(

let encoding = (let _177_605 = (let _177_604 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in ((_177_604), (refinement)))
in (FStar_SMTEncoding_Term.mkAnd _177_605))
in (

let cvars = (let _177_607 = (FStar_SMTEncoding_Term.free_variables encoding)
in (FStar_All.pipe_right _177_607 (FStar_List.filter (fun _85_775 -> (match (_85_775) with
| (y, _85_774) -> begin
((y <> x) && (y <> fsym))
end)))))
in (

let xfv = ((x), (FStar_SMTEncoding_Term.Term_sort))
in (

let ffv = ((fsym), (FStar_SMTEncoding_Term.Fuel_sort))
in (

let tkey = (FStar_SMTEncoding_Term.mkForall (([]), ((ffv)::(xfv)::cvars), (encoding)))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _85_782, _85_784) -> begin
(let _177_610 = (let _177_609 = (let _177_608 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in ((t), (_177_608)))
in (FStar_SMTEncoding_Term.mkApp _177_609))
in ((_177_610), ([])))
end
| None -> begin
(

let tsym = (varops.fresh "Tm_refine")
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let t = (let _177_612 = (let _177_611 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in ((tsym), (_177_611)))
in (FStar_SMTEncoding_Term.mkApp _177_612))
in (

let x_has_t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let t_kinding = (let _177_614 = (let _177_613 = (FStar_SMTEncoding_Term.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((_177_613), (Some ("refinement kinding")), (Some ((Prims.strcat "refinement_kinding_" tsym)))))
in FStar_SMTEncoding_Term.Assume (_177_614))
in (

let t_interp = (let _177_620 = (let _177_619 = (let _177_616 = (let _177_615 = (FStar_SMTEncoding_Term.mkIff ((x_has_t), (encoding)))
in ((((x_has_t)::[])::[]), ((ffv)::(xfv)::cvars), (_177_615)))
in (FStar_SMTEncoding_Term.mkForall _177_616))
in (let _177_618 = (let _177_617 = (FStar_Syntax_Print.term_to_string t0)
in Some (_177_617))
in ((_177_619), (_177_618), (Some ((Prims.strcat "refinement_interpretation_" tsym))))))
in FStar_SMTEncoding_Term.Assume (_177_620))
in (

let t_decls = (FStar_List.append (FStar_List.append decls decls') ((tdecl)::(t_kinding)::(t_interp)::[]))
in (

let _85_797 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash ((tsym), (cvar_sorts), (t_decls)))
in ((t), (t_decls))))))))))))
end))))))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
(

let ttm = (let _177_621 = (FStar_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Term.mk_Term_uvar _177_621))
in (

let _85_806 = (encode_term_pred None k env ttm)
in (match (_85_806) with
| (t_has_k, decls) -> begin
(

let d = (let _177_627 = (let _177_626 = (let _177_625 = (let _177_624 = (let _177_623 = (let _177_622 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _177_622))
in (FStar_Util.format1 "@uvar_typing_%s" _177_623))
in (varops.fresh _177_624))
in Some (_177_625))
in ((t_has_k), (Some ("Uvar typing")), (_177_626)))
in FStar_SMTEncoding_Term.Assume (_177_627))
in ((ttm), ((FStar_List.append decls ((d)::[])))))
end)))
end
| FStar_Syntax_Syntax.Tm_app (_85_809) -> begin
(

let _85_813 = (FStar_Syntax_Util.head_and_args t0)
in (match (_85_813) with
| (head, args_e) -> begin
(match ((let _177_629 = (let _177_628 = (FStar_Syntax_Subst.compress head)
in _177_628.FStar_Syntax_Syntax.n)
in ((_177_629), (args_e)))) with
| (_85_815, _85_817) when (head_redex env head) -> begin
(let _177_630 = (whnf env t)
in (encode_term _177_630 env))
end
| ((FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), (_)::((v1, _))::((v2, _))::[])) | ((FStar_Syntax_Syntax.Tm_fvar (fv), (_)::((v1, _))::((v2, _))::[])) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
(

let _85_857 = (encode_term v1 env)
in (match (_85_857) with
| (v1, decls1) -> begin
(

let _85_860 = (encode_term v2 env)
in (match (_85_860) with
| (v2, decls2) -> begin
(let _177_631 = (FStar_SMTEncoding_Term.mk_LexCons v1 v2)
in ((_177_631), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), (_85_869)::(_85_866)::_85_864) -> begin
(

let e0 = (let _177_635 = (let _177_634 = (let _177_633 = (let _177_632 = (FStar_List.hd args_e)
in (_177_632)::[])
in ((head), (_177_633)))
in FStar_Syntax_Syntax.Tm_app (_177_634))
in (FStar_Syntax_Syntax.mk _177_635 None head.FStar_Syntax_Syntax.pos))
in (

let e = (let _177_638 = (let _177_637 = (let _177_636 = (FStar_List.tl args_e)
in ((e0), (_177_636)))
in FStar_Syntax_Syntax.Tm_app (_177_637))
in (FStar_Syntax_Syntax.mk _177_638 None t0.FStar_Syntax_Syntax.pos))
in (encode_term e env)))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), ((arg, _85_878))::[]) -> begin
(

let _85_884 = (encode_term arg env)
in (match (_85_884) with
| (tm, decls) -> begin
(let _177_639 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Var ("Reify")), ((tm)::[])))))
in ((_177_639), (decls)))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (_85_886)), ((arg, _85_891))::[]) -> begin
(encode_term arg env)
end
| _85_896 -> begin
(

let _85_899 = (encode_args args_e env)
in (match (_85_899) with
| (args, decls) -> begin
(

let encode_partial_app = (fun ht_opt -> (

let _85_904 = (encode_term head env)
in (match (_85_904) with
| (head, decls') -> begin
(

let app_tm = (mk_Apply_args head args)
in (match (ht_opt) with
| None -> begin
((app_tm), ((FStar_List.append decls decls')))
end
| Some (formals, c) -> begin
(

let _85_913 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (_85_913) with
| (formals, rest) -> begin
(

let subst = (FStar_List.map2 (fun _85_917 _85_921 -> (match (((_85_917), (_85_921))) with
| ((bv, _85_916), (a, _85_920)) -> begin
FStar_Syntax_Syntax.NT (((bv), (a)))
end)) formals args_e)
in (

let ty = (let _177_644 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right _177_644 (FStar_Syntax_Subst.subst subst)))
in (

let _85_926 = (encode_term_pred None ty env app_tm)
in (match (_85_926) with
| (has_type, decls'') -> begin
(

let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (

let e_typing = (let _177_648 = (let _177_647 = (FStar_SMTEncoding_Term.mkForall ((((has_type)::[])::[]), (cvars), (has_type)))
in (let _177_646 = (let _177_645 = (varops.fresh "@partial_app_typing_")
in Some (_177_645))
in ((_177_647), (Some ("Partial app typing")), (_177_646))))
in FStar_SMTEncoding_Term.Assume (_177_648))
in ((app_tm), ((FStar_List.append (FStar_List.append (FStar_List.append decls decls') decls'') ((e_typing)::[]))))))
end))))
end))
end))
end)))
in (

let encode_full_app = (fun fv -> (

let _85_933 = (lookup_free_var_sym env fv)
in (match (_85_933) with
| (fname, fuel_args) -> begin
(

let tm = (FStar_SMTEncoding_Term.mkApp' ((fname), ((FStar_List.append fuel_args args))))
in ((tm), (decls)))
end)))
in (

let head = (FStar_Syntax_Subst.compress head)
in (

let head_type = (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (x); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (x)) -> begin
Some (x.FStar_Syntax_Syntax.sort)
end
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(let _177_652 = (let _177_651 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _177_651 Prims.snd))
in Some (_177_652))
end
| FStar_Syntax_Syntax.Tm_ascribed (_85_965, FStar_Util.Inl (t), _85_969) -> begin
Some (t)
end
| FStar_Syntax_Syntax.Tm_ascribed (_85_973, FStar_Util.Inr (c), _85_977) -> begin
Some ((FStar_Syntax_Util.comp_result c))
end
| _85_981 -> begin
None
end)
in (match (head_type) with
| None -> begin
(encode_partial_app None)
end
| Some (head_type) -> begin
(

let head_type = (let _177_653 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine _177_653))
in (

let _85_989 = (curried_arrow_formals_comp head_type)
in (match (_85_989) with
| (formals, c) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| _85_1005 -> begin
if ((FStar_List.length formals) > (FStar_List.length args)) then begin
(encode_partial_app (Some (((formals), (c)))))
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

let _85_1014 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_85_1014) with
| (bs, body, opening) -> begin
(

let fallback = (fun _85_1016 -> (match (()) with
| () -> begin
(

let f = (varops.fresh "Tm_abs")
in (

let decl = FStar_SMTEncoding_Term.DeclFun (((f), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Imprecise function encoding"))))
in (let _177_656 = (FStar_SMTEncoding_Term.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in ((_177_656), ((decl)::[])))))
end))
in (

let is_impure = (fun _85_9 -> (match (_85_9) with
| FStar_Util.Inl (lc) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)))
end
| FStar_Util.Inr (eff) -> begin
(let _177_659 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv eff)
in (FStar_All.pipe_right _177_659 Prims.op_Negation))
end))
in (

let codomain_eff = (fun lc -> (match (lc) with
| FStar_Util.Inl (lc) -> begin
(let _177_664 = (let _177_662 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening _177_662))
in (FStar_All.pipe_right _177_664 (fun _177_663 -> Some (_177_663))))
end
| FStar_Util.Inr (eff) -> begin
(

let new_uvar = (fun _85_1032 -> (match (()) with
| () -> begin
(let _177_667 = (FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange [] FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _177_667 Prims.fst))
end))
in if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid) then begin
(let _177_670 = (let _177_668 = (new_uvar ())
in (FStar_Syntax_Syntax.mk_Total _177_668))
in (FStar_All.pipe_right _177_670 (fun _177_669 -> Some (_177_669))))
end else begin
if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid) then begin
(let _177_673 = (let _177_671 = (new_uvar ())
in (FStar_Syntax_Syntax.mk_GTotal _177_671))
in (FStar_All.pipe_right _177_673 (fun _177_672 -> Some (_177_672))))
end else begin
None
end
end)
end))
in (match (lopt) with
| None -> begin
(

let _85_1034 = (let _177_675 = (let _177_674 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s" _177_674))
in (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos _177_675))
in (fallback ()))
end
| Some (lc) -> begin
if (is_impure lc) then begin
(fallback ())
end else begin
(

let _85_1044 = (encode_binders None bs env)
in (match (_85_1044) with
| (vars, guards, envbody, decls, _85_1043) -> begin
(

let _85_1047 = (encode_term body envbody)
in (match (_85_1047) with
| (body, decls') -> begin
(

let key_body = (let _177_679 = (let _177_678 = (let _177_677 = (let _177_676 = (FStar_SMTEncoding_Term.mk_and_l guards)
in ((_177_676), (body)))
in (FStar_SMTEncoding_Term.mkImp _177_677))
in (([]), (vars), (_177_678)))
in (FStar_SMTEncoding_Term.mkForall _177_679))
in (

let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (

let tkey = (FStar_SMTEncoding_Term.mkForall (([]), (cvars), (key_body)))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _85_1053, _85_1055) -> begin
(let _177_682 = (let _177_681 = (let _177_680 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in ((t), (_177_680)))
in (FStar_SMTEncoding_Term.mkApp _177_681))
in ((_177_682), ([])))
end
| None -> begin
(match ((is_eta env vars body)) with
| Some (t) -> begin
((t), ([]))
end
| None -> begin
(

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let fsym = (varops.fresh "Exp_abs")
in (

let fdecl = FStar_SMTEncoding_Term.DeclFun (((fsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let f = (let _177_684 = (let _177_683 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in ((fsym), (_177_683)))
in (FStar_SMTEncoding_Term.mkApp _177_684))
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

let _85_1073 = (encode_term_pred None tfun env f)
in (match (_85_1073) with
| (f_has_t, decls'') -> begin
(

let a_name = Some ((Prims.strcat "typing_" fsym))
in (let _177_688 = (let _177_687 = (let _177_686 = (let _177_685 = (FStar_SMTEncoding_Term.mkForall ((((f)::[])::[]), (cvars), (f_has_t)))
in ((_177_685), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_177_686))
in (_177_687)::[])
in (FStar_List.append decls'' _177_688)))
end)))
end)
in (

let interp_f = (

let a_name = Some ((Prims.strcat "interpretation_" fsym))
in (let _177_692 = (let _177_691 = (let _177_690 = (let _177_689 = (FStar_SMTEncoding_Term.mkEq ((app), (body)))
in ((((app)::[])::[]), ((FStar_List.append vars cvars)), (_177_689)))
in (FStar_SMTEncoding_Term.mkForall _177_690))
in ((_177_691), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_177_692)))
in (

let f_decls = (FStar_List.append (FStar_List.append (FStar_List.append decls decls') ((fdecl)::typing_f)) ((interp_f)::[]))
in (

let _85_1079 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash ((fsym), (cvar_sorts), (f_decls)))
in ((f), (f_decls)))))))))))
end)
end))))
end))
end))
end
end))))
end))
end
| FStar_Syntax_Syntax.Tm_let ((_85_1082, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_85_1094); FStar_Syntax_Syntax.lbunivs = _85_1092; FStar_Syntax_Syntax.lbtyp = _85_1090; FStar_Syntax_Syntax.lbeff = _85_1088; FStar_Syntax_Syntax.lbdef = _85_1086})::_85_1084), _85_1100) -> begin
(FStar_All.failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _85_1109; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _85_1106; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (_85_1119) -> begin
(

let _85_1121 = (FStar_TypeChecker_Errors.diag t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (

let e = (varops.fresh "let-rec")
in (

let decl_e = FStar_SMTEncoding_Term.DeclFun (((e), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (let _177_693 = (FStar_SMTEncoding_Term.mkFreeV ((e), (FStar_SMTEncoding_Term.Term_sort)))
in ((_177_693), ((decl_e)::[]))))))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end))))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (

let _85_1137 = (encode_term e1 env)
in (match (_85_1137) with
| (ee1, decls1) -> begin
(

let _85_1140 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) e2)
in (match (_85_1140) with
| (xs, e2) -> begin
(

let _85_1144 = (FStar_List.hd xs)
in (match (_85_1144) with
| (x, _85_1143) -> begin
(

let env' = (push_term_var env x ee1)
in (

let _85_1148 = (encode_body e2 env')
in (match (_85_1148) with
| (ee2, decls2) -> begin
((ee2), ((FStar_List.append decls1 decls2)))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (

let _85_1156 = (encode_term e env)
in (match (_85_1156) with
| (scr, decls) -> begin
(

let _85_1193 = (FStar_List.fold_right (fun b _85_1160 -> (match (_85_1160) with
| (else_case, decls) -> begin
(

let _85_1164 = (FStar_Syntax_Subst.open_branch b)
in (match (_85_1164) with
| (p, w, br) -> begin
(

let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun _85_1168 _85_1171 -> (match (((_85_1168), (_85_1171))) with
| ((env0, pattern), (else_case, decls)) -> begin
(

let guard = (pattern.guard scr)
in (

let projections = (pattern.projections scr)
in (

let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env _85_1177 -> (match (_85_1177) with
| (x, t) -> begin
(push_term_var env x t)
end)) env))
in (

let _85_1187 = (match (w) with
| None -> begin
((guard), ([]))
end
| Some (w) -> begin
(

let _85_1184 = (encode_term w env)
in (match (_85_1184) with
| (w, decls2) -> begin
(let _177_727 = (let _177_726 = (let _177_725 = (let _177_724 = (let _177_723 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Term.mkTrue)
in ((w), (_177_723)))
in (FStar_SMTEncoding_Term.mkEq _177_724))
in ((guard), (_177_725)))
in (FStar_SMTEncoding_Term.mkAnd _177_726))
in ((_177_727), (decls2)))
end))
end)
in (match (_85_1187) with
| (guard, decls2) -> begin
(

let _85_1190 = (encode_br br env)
in (match (_85_1190) with
| (br, decls3) -> begin
(let _177_728 = (FStar_SMTEncoding_Term.mkITE ((guard), (br), (else_case)))
in ((_177_728), ((FStar_List.append (FStar_List.append decls decls2) decls3))))
end))
end)))))
end)) patterns ((else_case), (decls))))
end))
end)) pats ((default_case), (decls)))
in (match (_85_1193) with
| (match_tm, decls) -> begin
((match_tm), (decls))
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _85_1199 -> begin
(let _177_731 = (encode_one_pat env pat)
in (_177_731)::[])
end))
and encode_one_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> (

let _85_1202 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _177_734 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" _177_734))
end else begin
()
end
in (

let _85_1206 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (_85_1206) with
| (vars, pat_term) -> begin
(

let _85_1218 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun _85_1209 v -> (match (_85_1209) with
| (env, vars) -> begin
(

let _85_1215 = (gen_term_var env v)
in (match (_85_1215) with
| (xx, _85_1213, env) -> begin
((env), ((((v), (((xx), (FStar_SMTEncoding_Term.Term_sort)))))::vars))
end))
end)) ((env), ([]))))
in (match (_85_1218) with
| (env, vars) -> begin
(

let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_85_1223) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_dot_term (_)) -> begin
FStar_SMTEncoding_Term.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _177_742 = (let _177_741 = (encode_const c)
in ((scrutinee), (_177_741)))
in (FStar_SMTEncoding_Term.mkEq _177_742))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let is_f = (mk_data_tester env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _85_1245 -> (match (_85_1245) with
| (arg, _85_1244) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _177_745 = (FStar_SMTEncoding_Term.mkApp ((proj), ((scrutinee)::[])))
in (mk_guard arg _177_745)))
end))))
in (FStar_SMTEncoding_Term.mk_and_l ((is_f)::sub_term_guards))))
end))
in (

let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_85_1252) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _)) | (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_constant (_85_1262) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(let _177_753 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _85_1272 -> (match (_85_1272) with
| (arg, _85_1271) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _177_752 = (FStar_SMTEncoding_Term.mkApp ((proj), ((scrutinee)::[])))
in (mk_projections arg _177_752)))
end))))
in (FStar_All.pipe_right _177_753 FStar_List.flatten))
end))
in (

let pat_term = (fun _85_1275 -> (match (()) with
| () -> begin
(encode_term pat_term env)
end))
in (

let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in ((env), (pattern))))))
end))
end))))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (

let _85_1291 = (FStar_All.pipe_right l (FStar_List.fold_left (fun _85_1281 _85_1285 -> (match (((_85_1281), (_85_1285))) with
| ((tms, decls), (t, _85_1284)) -> begin
(

let _85_1288 = (encode_term t env)
in (match (_85_1288) with
| (t, decls') -> begin
(((t)::tms), ((FStar_List.append decls decls')))
end))
end)) (([]), ([]))))
in (match (_85_1291) with
| (l, decls) -> begin
(((FStar_List.rev l)), (decls))
end)))
and encode_function_type_as_formula : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun induction_on new_pats t env -> (

let rec list_elements = (fun e -> (

let _85_1300 = (let _177_766 = (FStar_Syntax_Util.unmeta e)
in (FStar_Syntax_Util.head_and_args _177_766))
in (match (_85_1300) with
| (head, args) -> begin
(match ((let _177_768 = (let _177_767 = (FStar_Syntax_Util.un_uinst head)
in _177_767.FStar_Syntax_Syntax.n)
in ((_177_768), (args)))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), _85_1304) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid) -> begin
[]
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_85_1317)::((hd, _85_1314))::((tl, _85_1310))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid) -> begin
(let _177_769 = (list_elements tl)
in (hd)::_177_769)
end
| _85_1321 -> begin
(

let _85_1322 = (FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern")
in [])
end)
end)))
in (

let one_pat = (fun p -> (

let _85_1328 = (let _177_772 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right _177_772 FStar_Syntax_Util.head_and_args))
in (match (_85_1328) with
| (head, args) -> begin
(match ((let _177_774 = (let _177_773 = (FStar_Syntax_Util.un_uinst head)
in _177_773.FStar_Syntax_Syntax.n)
in ((_177_774), (args)))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((_85_1336, _85_1338))::((e, _85_1333))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpat_lid) -> begin
((e), (None))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, _85_1346))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatT_lid) -> begin
((e), (None))
end
| _85_1351 -> begin
(FStar_All.failwith "Unexpected pattern term")
end)
end)))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements p)
in (

let smt_pat_or = (fun t -> (

let _85_1359 = (let _177_779 = (FStar_Syntax_Util.unmeta t)
in (FStar_All.pipe_right _177_779 FStar_Syntax_Util.head_and_args))
in (match (_85_1359) with
| (head, args) -> begin
(match ((let _177_781 = (let _177_780 = (FStar_Syntax_Util.un_uinst head)
in _177_780.FStar_Syntax_Syntax.n)
in ((_177_781), (args)))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, _85_1364))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatOr_lid) -> begin
Some (e)
end
| _85_1369 -> begin
None
end)
end)))
in (match (elts) with
| (t)::[] -> begin
(match ((smt_pat_or t)) with
| Some (e) -> begin
(let _177_784 = (list_elements e)
in (FStar_All.pipe_right _177_784 (FStar_List.map (fun branch -> (let _177_783 = (list_elements branch)
in (FStar_All.pipe_right _177_783 (FStar_List.map one_pat)))))))
end
| _85_1376 -> begin
(let _177_785 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_177_785)::[])
end)
end
| _85_1378 -> begin
(let _177_786 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_177_786)::[])
end))))
in (

let _85_1412 = (match ((let _177_787 = (FStar_Syntax_Subst.compress t)
in _177_787.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _85_1385 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_85_1385) with
| (binders, c) -> begin
(

let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| ((pre, _85_1397))::((post, _85_1393))::((pats, _85_1389))::[] -> begin
(

let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _177_788 = (lemma_pats pats')
in ((binders), (pre), (post), (_177_788))))
end
| _85_1405 -> begin
(FStar_All.failwith "impos")
end))
end))
end
| _85_1407 -> begin
(FStar_All.failwith "Impos")
end)
in (match (_85_1412) with
| (binders, pre, post, patterns) -> begin
(

let _85_1419 = (encode_binders None binders env)
in (match (_85_1419) with
| (vars, guards, env, decls, _85_1418) -> begin
(

let _85_1432 = (let _177_792 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (

let _85_1429 = (let _177_791 = (FStar_All.pipe_right branch (FStar_List.map (fun _85_1424 -> (match (_85_1424) with
| (t, _85_1423) -> begin
(encode_term t (

let _85_1425 = env
in {bindings = _85_1425.bindings; depth = _85_1425.depth; tcenv = _85_1425.tcenv; warn = _85_1425.warn; cache = _85_1425.cache; nolabels = _85_1425.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _85_1425.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _177_791 FStar_List.unzip))
in (match (_85_1429) with
| (pats, decls) -> begin
((pats), (decls))
end)))))
in (FStar_All.pipe_right _177_792 FStar_List.unzip))
in (match (_85_1432) with
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
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _177_795 = (let _177_794 = (FStar_SMTEncoding_Term.mkFreeV l)
in (FStar_SMTEncoding_Term.mk_Precedes _177_794 e))
in (_177_795)::p))))
end
| _85_1442 -> begin
(

let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _177_801 = (FStar_SMTEncoding_Term.mk_Precedes tl e)
in (_177_801)::p))))
end
| ((x, FStar_SMTEncoding_Term.Term_sort))::vars -> begin
(let _177_803 = (let _177_802 = (FStar_SMTEncoding_Term.mkFreeV ((x), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_LexCons _177_802 tl))
in (aux _177_803 vars))
end
| _85_1454 -> begin
pats
end))
in (let _177_804 = (FStar_SMTEncoding_Term.mkFreeV (("Prims.LexTop"), (FStar_SMTEncoding_Term.Term_sort)))
in (aux _177_804 vars)))
end)
end)
in (

let env = (

let _85_1456 = env
in {bindings = _85_1456.bindings; depth = _85_1456.depth; tcenv = _85_1456.tcenv; warn = _85_1456.warn; cache = _85_1456.cache; nolabels = true; use_zfuel_name = _85_1456.use_zfuel_name; encode_non_total_function_typ = _85_1456.encode_non_total_function_typ})
in (

let _85_1461 = (let _177_805 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula _177_805 env))
in (match (_85_1461) with
| (pre, decls'') -> begin
(

let _85_1464 = (let _177_806 = (FStar_Syntax_Util.unmeta post)
in (encode_formula _177_806 env))
in (match (_85_1464) with
| (post, decls''') -> begin
(

let decls = (FStar_List.append (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'') decls''')
in (let _177_811 = (let _177_810 = (let _177_809 = (let _177_808 = (let _177_807 = (FStar_SMTEncoding_Term.mk_and_l ((pre)::guards))
in ((_177_807), (post)))
in (FStar_SMTEncoding_Term.mkImp _177_808))
in ((pats), (vars), (_177_809)))
in (FStar_SMTEncoding_Term.mkForall _177_810))
in ((_177_811), (decls))))
end))
end)))))
end))
end))
end))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (

let debug = (fun phi -> if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _177_817 = (FStar_Syntax_Print.tag_of_term phi)
in (let _177_816 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print2 "Formula (%s)  %s\n" _177_817 _177_816)))
end else begin
()
end)
in (

let enc = (fun f l -> (

let _85_1480 = (FStar_Util.fold_map (fun decls x -> (

let _85_1477 = (encode_term (Prims.fst x) env)
in (match (_85_1477) with
| (t, decls') -> begin
(((FStar_List.append decls decls')), (t))
end))) [] l)
in (match (_85_1480) with
| (decls, args) -> begin
(let _177_833 = (f args)
in ((_177_833), (decls)))
end)))
in (

let const_op = (fun f _85_1483 -> ((f), ([])))
in (

let un_op = (fun f l -> (let _177_847 = (FStar_List.hd l)
in (FStar_All.pipe_left f _177_847)))
in (

let bin_op = (fun f _85_10 -> (match (_85_10) with
| (t1)::(t2)::[] -> begin
(f ((t1), (t2)))
end
| _85_1494 -> begin
(FStar_All.failwith "Impossible")
end))
in (

let enc_prop_c = (fun f l -> (

let _85_1509 = (FStar_Util.fold_map (fun decls _85_1503 -> (match (_85_1503) with
| (t, _85_1502) -> begin
(

let _85_1506 = (encode_formula t env)
in (match (_85_1506) with
| (phi, decls') -> begin
(((FStar_List.append decls decls')), (phi))
end))
end)) [] l)
in (match (_85_1509) with
| (decls, phis) -> begin
(let _177_872 = (f phis)
in ((_177_872), (decls)))
end)))
in (

let eq_op = (fun _85_11 -> (match (_85_11) with
| (_85_1516)::(_85_1514)::(e1)::(e2)::[] -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) l)
end))
in (

let mk_imp = (fun _85_12 -> (match (_85_12) with
| ((lhs, _85_1527))::((rhs, _85_1523))::[] -> begin
(

let _85_1532 = (encode_formula rhs env)
in (match (_85_1532) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _85_1535) -> begin
((l1), (decls1))
end
| _85_1539 -> begin
(

let _85_1542 = (encode_formula lhs env)
in (match (_85_1542) with
| (l2, decls2) -> begin
(let _177_877 = (FStar_SMTEncoding_Term.mkImp ((l2), (l1)))
in ((_177_877), ((FStar_List.append decls1 decls2))))
end))
end)
end))
end
| _85_1544 -> begin
(FStar_All.failwith "impossible")
end))
in (

let mk_ite = (fun _85_13 -> (match (_85_13) with
| ((guard, _85_1557))::((_then, _85_1553))::((_else, _85_1549))::[] -> begin
(

let _85_1562 = (encode_formula guard env)
in (match (_85_1562) with
| (g, decls1) -> begin
(

let _85_1565 = (encode_formula _then env)
in (match (_85_1565) with
| (t, decls2) -> begin
(

let _85_1568 = (encode_formula _else env)
in (match (_85_1568) with
| (e, decls3) -> begin
(

let res = (FStar_SMTEncoding_Term.mkITE ((g), (t), (e)))
in ((res), ((FStar_List.append (FStar_List.append decls1 decls2) decls3))))
end))
end))
end))
end
| _85_1571 -> begin
(FStar_All.failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (let _177_889 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f _177_889)))
in (

let connectives = (let _177_942 = (let _177_898 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkAnd))
in ((FStar_Syntax_Const.and_lid), (_177_898)))
in (let _177_941 = (let _177_940 = (let _177_904 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkOr))
in ((FStar_Syntax_Const.or_lid), (_177_904)))
in (let _177_939 = (let _177_938 = (let _177_937 = (let _177_913 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkIff))
in ((FStar_Syntax_Const.iff_lid), (_177_913)))
in (let _177_936 = (let _177_935 = (let _177_934 = (let _177_922 = (FStar_All.pipe_left enc_prop_c (un_op FStar_SMTEncoding_Term.mkNot))
in ((FStar_Syntax_Const.not_lid), (_177_922)))
in (_177_934)::(((FStar_Syntax_Const.eq2_lid), (eq_op)))::(((FStar_Syntax_Const.true_lid), ((const_op FStar_SMTEncoding_Term.mkTrue))))::(((FStar_Syntax_Const.false_lid), ((const_op FStar_SMTEncoding_Term.mkFalse))))::[])
in (((FStar_Syntax_Const.ite_lid), (mk_ite)))::_177_935)
in (_177_937)::_177_936))
in (((FStar_Syntax_Const.imp_lid), (mk_imp)))::_177_938)
in (_177_940)::_177_939))
in (_177_942)::_177_941))
in (

let rec fallback = (fun phi -> (match (phi.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(

let _85_1589 = (encode_formula phi' env)
in (match (_85_1589) with
| (phi, decls) -> begin
(let _177_945 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled (((phi), (msg), (r)))))
in ((_177_945), (decls)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (_85_1591) -> begin
(let _177_946 = (FStar_Syntax_Util.unmeta phi)
in (encode_formula _177_946 env))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(

let _85_1599 = (encode_match e pats FStar_SMTEncoding_Term.mkFalse env encode_formula)
in (match (_85_1599) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _85_1606; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _85_1603; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _85_1617 = (encode_let x t1 e1 e2 env encode_formula)
in (match (_85_1617) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let head = (FStar_Syntax_Util.un_uinst head)
in (match (((head.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_85_1634)::((x, _85_1631))::((t, _85_1627))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.has_type_lid) -> begin
(

let _85_1639 = (encode_term x env)
in (match (_85_1639) with
| (x, decls) -> begin
(

let _85_1642 = (encode_term t env)
in (match (_85_1642) with
| (t, decls') -> begin
(let _177_947 = (FStar_SMTEncoding_Term.mk_HasType x t)
in ((_177_947), ((FStar_List.append decls decls'))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((r, _85_1655))::((msg, _85_1651))::((phi, _85_1647))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.labeled_lid) -> begin
(match ((let _177_951 = (let _177_948 = (FStar_Syntax_Subst.compress r)
in _177_948.FStar_Syntax_Syntax.n)
in (let _177_950 = (let _177_949 = (FStar_Syntax_Subst.compress msg)
in _177_949.FStar_Syntax_Syntax.n)
in ((_177_951), (_177_950))))) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, _85_1664))) -> begin
(

let phi = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((phi), (FStar_Syntax_Syntax.Meta_labeled ((((FStar_Util.string_of_unicode s)), (r), (false))))))) None r)
in (fallback phi))
end
| _85_1671 -> begin
(fallback phi)
end)
end
| _85_1673 when (head_redex env head) -> begin
(let _177_952 = (whnf env phi)
in (encode_formula _177_952 env))
end
| _85_1675 -> begin
(

let _85_1678 = (encode_term phi env)
in (match (_85_1678) with
| (tt, decls) -> begin
(let _177_953 = (FStar_SMTEncoding_Term.mk_Valid tt)
in ((_177_953), (decls)))
end))
end))
end
| _85_1680 -> begin
(

let _85_1683 = (encode_term phi env)
in (match (_85_1683) with
| (tt, decls) -> begin
(let _177_954 = (FStar_SMTEncoding_Term.mk_Valid tt)
in ((_177_954), (decls)))
end))
end))
in (

let encode_q_body = (fun env bs ps body -> (

let _85_1695 = (encode_binders None bs env)
in (match (_85_1695) with
| (vars, guards, env, decls, _85_1694) -> begin
(

let _85_1708 = (let _177_966 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let _85_1705 = (let _177_965 = (FStar_All.pipe_right p (FStar_List.map (fun _85_1700 -> (match (_85_1700) with
| (t, _85_1699) -> begin
(encode_term t (

let _85_1701 = env
in {bindings = _85_1701.bindings; depth = _85_1701.depth; tcenv = _85_1701.tcenv; warn = _85_1701.warn; cache = _85_1701.cache; nolabels = _85_1701.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _85_1701.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _177_965 FStar_List.unzip))
in (match (_85_1705) with
| (p, decls) -> begin
((p), ((FStar_List.flatten decls)))
end)))))
in (FStar_All.pipe_right _177_966 FStar_List.unzip))
in (match (_85_1708) with
| (pats, decls') -> begin
(

let _85_1711 = (encode_formula body env)
in (match (_85_1711) with
| (body, decls'') -> begin
(

let guards = (match (pats) with
| (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.hash = _85_1715; FStar_SMTEncoding_Term.freevars = _85_1713})::[])::[] -> begin
[]
end
| _85_1726 -> begin
guards
end)
in (let _177_967 = (FStar_SMTEncoding_Term.mk_and_l guards)
in ((vars), (pats), (_177_967), (body), ((FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'')))))
end))
end))
end)))
in (

let _85_1728 = (debug phi)
in (

let phi = (FStar_Syntax_Util.unascribe phi)
in (match ((FStar_Syntax_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _85_1740 -> (match (_85_1740) with
| (l, _85_1739) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_85_1743, f) -> begin
(f arms)
end)
end
| Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
(

let _85_1753 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _177_984 = (FStar_All.pipe_right vars (FStar_Syntax_Print.binders_to_string "; "))
in (FStar_Util.print1 ">>>> Got QALL [%s]\n" _177_984))
end else begin
()
end
in (

let _85_1760 = (encode_q_body env vars pats body)
in (match (_85_1760) with
| (vars, pats, guard, body, decls) -> begin
(

let tm = (let _177_986 = (let _177_985 = (FStar_SMTEncoding_Term.mkImp ((guard), (body)))
in ((pats), (vars), (_177_985)))
in (FStar_SMTEncoding_Term.mkForall _177_986))
in (

let _85_1762 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _177_987 = (FStar_SMTEncoding_Term.termToSmt tm)
in (FStar_Util.print1 ">>>> Encoded QALL to %s\n" _177_987))
end else begin
()
end
in ((tm), (decls))))
end)))
end
| Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
(

let _85_1775 = (encode_q_body env vars pats body)
in (match (_85_1775) with
| (vars, pats, guard, body, decls) -> begin
(let _177_990 = (let _177_989 = (let _177_988 = (FStar_SMTEncoding_Term.mkAnd ((guard), (body)))
in ((pats), (vars), (_177_988)))
in (FStar_SMTEncoding_Term.mkExists _177_989))
in ((_177_990), (decls)))
end))
end)))))))))))))))))


type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.decl Prims.list; is : FStar_Ident.lident  ->  Prims.bool}


let is_Mkprims_t : prims_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkprims_t"))))


let prims : prims_t = (

let _85_1781 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (_85_1781) with
| (asym, a) -> begin
(

let _85_1784 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_85_1784) with
| (xsym, x) -> begin
(

let _85_1787 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (_85_1787) with
| (ysym, y) -> begin
(

let deffun = (fun vars body x -> (FStar_SMTEncoding_Term.DefineFun (((x), (vars), (FStar_SMTEncoding_Term.Term_sort), (body), (None))))::[])
in (

let quant = (fun vars body x -> (

let t1 = (let _177_1033 = (let _177_1032 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in ((x), (_177_1032)))
in (FStar_SMTEncoding_Term.mkApp _177_1033))
in (

let vname_decl = (let _177_1035 = (let _177_1034 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in ((x), (_177_1034), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (_177_1035))
in (let _177_1041 = (let _177_1040 = (let _177_1039 = (let _177_1038 = (let _177_1037 = (let _177_1036 = (FStar_SMTEncoding_Term.mkEq ((t1), (body)))
in ((((t1)::[])::[]), (vars), (_177_1036)))
in (FStar_SMTEncoding_Term.mkForall _177_1037))
in ((_177_1038), (None), (Some ((Prims.strcat "primitive_" x)))))
in FStar_SMTEncoding_Term.Assume (_177_1039))
in (_177_1040)::[])
in (vname_decl)::_177_1041))))
in (

let axy = (((asym), (FStar_SMTEncoding_Term.Term_sort)))::(((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let xy = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let qx = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let prims = (let _177_1201 = (let _177_1050 = (let _177_1049 = (let _177_1048 = (FStar_SMTEncoding_Term.mkEq ((x), (y)))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1048))
in (quant axy _177_1049))
in ((FStar_Syntax_Const.op_Eq), (_177_1050)))
in (let _177_1200 = (let _177_1199 = (let _177_1057 = (let _177_1056 = (let _177_1055 = (let _177_1054 = (FStar_SMTEncoding_Term.mkEq ((x), (y)))
in (FStar_SMTEncoding_Term.mkNot _177_1054))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1055))
in (quant axy _177_1056))
in ((FStar_Syntax_Const.op_notEq), (_177_1057)))
in (let _177_1198 = (let _177_1197 = (let _177_1066 = (let _177_1065 = (let _177_1064 = (let _177_1063 = (let _177_1062 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1061 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_177_1062), (_177_1061))))
in (FStar_SMTEncoding_Term.mkLT _177_1063))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1064))
in (quant xy _177_1065))
in ((FStar_Syntax_Const.op_LT), (_177_1066)))
in (let _177_1196 = (let _177_1195 = (let _177_1075 = (let _177_1074 = (let _177_1073 = (let _177_1072 = (let _177_1071 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1070 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_177_1071), (_177_1070))))
in (FStar_SMTEncoding_Term.mkLTE _177_1072))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1073))
in (quant xy _177_1074))
in ((FStar_Syntax_Const.op_LTE), (_177_1075)))
in (let _177_1194 = (let _177_1193 = (let _177_1084 = (let _177_1083 = (let _177_1082 = (let _177_1081 = (let _177_1080 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1079 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_177_1080), (_177_1079))))
in (FStar_SMTEncoding_Term.mkGT _177_1081))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1082))
in (quant xy _177_1083))
in ((FStar_Syntax_Const.op_GT), (_177_1084)))
in (let _177_1192 = (let _177_1191 = (let _177_1093 = (let _177_1092 = (let _177_1091 = (let _177_1090 = (let _177_1089 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1088 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_177_1089), (_177_1088))))
in (FStar_SMTEncoding_Term.mkGTE _177_1090))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1091))
in (quant xy _177_1092))
in ((FStar_Syntax_Const.op_GTE), (_177_1093)))
in (let _177_1190 = (let _177_1189 = (let _177_1102 = (let _177_1101 = (let _177_1100 = (let _177_1099 = (let _177_1098 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1097 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_177_1098), (_177_1097))))
in (FStar_SMTEncoding_Term.mkSub _177_1099))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _177_1100))
in (quant xy _177_1101))
in ((FStar_Syntax_Const.op_Subtraction), (_177_1102)))
in (let _177_1188 = (let _177_1187 = (let _177_1109 = (let _177_1108 = (let _177_1107 = (let _177_1106 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Term.mkMinus _177_1106))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _177_1107))
in (quant qx _177_1108))
in ((FStar_Syntax_Const.op_Minus), (_177_1109)))
in (let _177_1186 = (let _177_1185 = (let _177_1118 = (let _177_1117 = (let _177_1116 = (let _177_1115 = (let _177_1114 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1113 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_177_1114), (_177_1113))))
in (FStar_SMTEncoding_Term.mkAdd _177_1115))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _177_1116))
in (quant xy _177_1117))
in ((FStar_Syntax_Const.op_Addition), (_177_1118)))
in (let _177_1184 = (let _177_1183 = (let _177_1127 = (let _177_1126 = (let _177_1125 = (let _177_1124 = (let _177_1123 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1122 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_177_1123), (_177_1122))))
in (FStar_SMTEncoding_Term.mkMul _177_1124))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _177_1125))
in (quant xy _177_1126))
in ((FStar_Syntax_Const.op_Multiply), (_177_1127)))
in (let _177_1182 = (let _177_1181 = (let _177_1136 = (let _177_1135 = (let _177_1134 = (let _177_1133 = (let _177_1132 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1131 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_177_1132), (_177_1131))))
in (FStar_SMTEncoding_Term.mkDiv _177_1133))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _177_1134))
in (quant xy _177_1135))
in ((FStar_Syntax_Const.op_Division), (_177_1136)))
in (let _177_1180 = (let _177_1179 = (let _177_1145 = (let _177_1144 = (let _177_1143 = (let _177_1142 = (let _177_1141 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1140 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_177_1141), (_177_1140))))
in (FStar_SMTEncoding_Term.mkMod _177_1142))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _177_1143))
in (quant xy _177_1144))
in ((FStar_Syntax_Const.op_Modulus), (_177_1145)))
in (let _177_1178 = (let _177_1177 = (let _177_1154 = (let _177_1153 = (let _177_1152 = (let _177_1151 = (let _177_1150 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _177_1149 = (FStar_SMTEncoding_Term.unboxBool y)
in ((_177_1150), (_177_1149))))
in (FStar_SMTEncoding_Term.mkAnd _177_1151))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1152))
in (quant xy _177_1153))
in ((FStar_Syntax_Const.op_And), (_177_1154)))
in (let _177_1176 = (let _177_1175 = (let _177_1163 = (let _177_1162 = (let _177_1161 = (let _177_1160 = (let _177_1159 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _177_1158 = (FStar_SMTEncoding_Term.unboxBool y)
in ((_177_1159), (_177_1158))))
in (FStar_SMTEncoding_Term.mkOr _177_1160))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1161))
in (quant xy _177_1162))
in ((FStar_Syntax_Const.op_Or), (_177_1163)))
in (let _177_1174 = (let _177_1173 = (let _177_1170 = (let _177_1169 = (let _177_1168 = (let _177_1167 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Term.mkNot _177_1167))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1168))
in (quant qx _177_1169))
in ((FStar_Syntax_Const.op_Negation), (_177_1170)))
in (_177_1173)::[])
in (_177_1175)::_177_1174))
in (_177_1177)::_177_1176))
in (_177_1179)::_177_1178))
in (_177_1181)::_177_1180))
in (_177_1183)::_177_1182))
in (_177_1185)::_177_1184))
in (_177_1187)::_177_1186))
in (_177_1189)::_177_1188))
in (_177_1191)::_177_1190))
in (_177_1193)::_177_1192))
in (_177_1195)::_177_1194))
in (_177_1197)::_177_1196))
in (_177_1199)::_177_1198))
in (_177_1201)::_177_1200))
in (

let mk = (fun l v -> (let _177_1233 = (FStar_All.pipe_right prims (FStar_List.filter (fun _85_1807 -> (match (_85_1807) with
| (l', _85_1806) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right _177_1233 (FStar_List.collect (fun _85_1811 -> (match (_85_1811) with
| (_85_1809, b) -> begin
(b v)
end))))))
in (

let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _85_1817 -> (match (_85_1817) with
| (l', _85_1816) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is}))))))))
end))
end))
end))


let pretype_axiom : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun tapp vars -> (

let _85_1823 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_85_1823) with
| (xxsym, xx) -> begin
(

let _85_1826 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_85_1826) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (let _177_1261 = (let _177_1260 = (let _177_1257 = (let _177_1256 = (let _177_1255 = (let _177_1254 = (let _177_1253 = (let _177_1252 = (FStar_SMTEncoding_Term.mkApp (("PreType"), ((xx)::[])))
in ((tapp), (_177_1252)))
in (FStar_SMTEncoding_Term.mkEq _177_1253))
in ((xx_has_type), (_177_1254)))
in (FStar_SMTEncoding_Term.mkImp _177_1255))
in ((((xx_has_type)::[])::[]), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars), (_177_1256)))
in (FStar_SMTEncoding_Term.mkForall _177_1257))
in (let _177_1259 = (let _177_1258 = (varops.fresh "@pretyping_")
in Some (_177_1258))
in ((_177_1260), (Some ("pretyping")), (_177_1259))))
in FStar_SMTEncoding_Term.Assume (_177_1261)))
end))
end)))


let primitive_type_axioms : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.decl Prims.list = (

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (

let yy = (("y"), (FStar_SMTEncoding_Term.Term_sort))
in (

let y = (FStar_SMTEncoding_Term.mkFreeV yy)
in (

let mk_unit = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (let _177_1282 = (let _177_1273 = (let _177_1272 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in ((_177_1272), (Some ("unit typing")), (Some ("unit_typing"))))
in FStar_SMTEncoding_Term.Assume (_177_1273))
in (let _177_1281 = (let _177_1280 = (let _177_1279 = (let _177_1278 = (let _177_1277 = (let _177_1276 = (let _177_1275 = (let _177_1274 = (FStar_SMTEncoding_Term.mkEq ((x), (FStar_SMTEncoding_Term.mk_Term_unit)))
in ((typing_pred), (_177_1274)))
in (FStar_SMTEncoding_Term.mkImp _177_1275))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_177_1276)))
in (mkForall_fuel _177_1277))
in ((_177_1278), (Some ("unit inversion")), (Some ("unit_inversion"))))
in FStar_SMTEncoding_Term.Assume (_177_1279))
in (_177_1280)::[])
in (_177_1282)::_177_1281))))
in (

let mk_bool = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Bool_sort))
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _177_1305 = (let _177_1296 = (let _177_1295 = (let _177_1294 = (let _177_1293 = (let _177_1290 = (let _177_1289 = (FStar_SMTEncoding_Term.boxBool b)
in (_177_1289)::[])
in (_177_1290)::[])
in (let _177_1292 = (let _177_1291 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType _177_1291 tt))
in ((_177_1293), ((bb)::[]), (_177_1292))))
in (FStar_SMTEncoding_Term.mkForall _177_1294))
in ((_177_1295), (Some ("bool typing")), (Some ("bool_typing"))))
in FStar_SMTEncoding_Term.Assume (_177_1296))
in (let _177_1304 = (let _177_1303 = (let _177_1302 = (let _177_1301 = (let _177_1300 = (let _177_1299 = (let _177_1298 = (let _177_1297 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in ((typing_pred), (_177_1297)))
in (FStar_SMTEncoding_Term.mkImp _177_1298))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_177_1299)))
in (mkForall_fuel _177_1300))
in ((_177_1301), (Some ("bool inversion")), (Some ("bool_inversion"))))
in FStar_SMTEncoding_Term.Assume (_177_1302))
in (_177_1303)::[])
in (_177_1305)::_177_1304))))))
in (

let mk_int = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let typing_pred_y = (FStar_SMTEncoding_Term.mk_HasType y tt)
in (

let aa = (("a"), (FStar_SMTEncoding_Term.Int_sort))
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Int_sort))
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (

let precedes = (let _177_1319 = (let _177_1318 = (let _177_1317 = (let _177_1316 = (let _177_1315 = (let _177_1314 = (FStar_SMTEncoding_Term.boxInt a)
in (let _177_1313 = (let _177_1312 = (FStar_SMTEncoding_Term.boxInt b)
in (_177_1312)::[])
in (_177_1314)::_177_1313))
in (tt)::_177_1315)
in (tt)::_177_1316)
in (("Prims.Precedes"), (_177_1317)))
in (FStar_SMTEncoding_Term.mkApp _177_1318))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _177_1319))
in (

let precedes_y_x = (let _177_1320 = (FStar_SMTEncoding_Term.mkApp (("Precedes"), ((y)::(x)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _177_1320))
in (let _177_1362 = (let _177_1328 = (let _177_1327 = (let _177_1326 = (let _177_1325 = (let _177_1322 = (let _177_1321 = (FStar_SMTEncoding_Term.boxInt b)
in (_177_1321)::[])
in (_177_1322)::[])
in (let _177_1324 = (let _177_1323 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType _177_1323 tt))
in ((_177_1325), ((bb)::[]), (_177_1324))))
in (FStar_SMTEncoding_Term.mkForall _177_1326))
in ((_177_1327), (Some ("int typing")), (Some ("int_typing"))))
in FStar_SMTEncoding_Term.Assume (_177_1328))
in (let _177_1361 = (let _177_1360 = (let _177_1334 = (let _177_1333 = (let _177_1332 = (let _177_1331 = (let _177_1330 = (let _177_1329 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in ((typing_pred), (_177_1329)))
in (FStar_SMTEncoding_Term.mkImp _177_1330))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_177_1331)))
in (mkForall_fuel _177_1332))
in ((_177_1333), (Some ("int inversion")), (Some ("int_inversion"))))
in FStar_SMTEncoding_Term.Assume (_177_1334))
in (let _177_1359 = (let _177_1358 = (let _177_1357 = (let _177_1356 = (let _177_1355 = (let _177_1354 = (let _177_1353 = (let _177_1352 = (let _177_1351 = (let _177_1350 = (let _177_1349 = (let _177_1348 = (let _177_1337 = (let _177_1336 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1335 = (FStar_SMTEncoding_Term.mkInteger' 0)
in ((_177_1336), (_177_1335))))
in (FStar_SMTEncoding_Term.mkGT _177_1337))
in (let _177_1347 = (let _177_1346 = (let _177_1340 = (let _177_1339 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _177_1338 = (FStar_SMTEncoding_Term.mkInteger' 0)
in ((_177_1339), (_177_1338))))
in (FStar_SMTEncoding_Term.mkGTE _177_1340))
in (let _177_1345 = (let _177_1344 = (let _177_1343 = (let _177_1342 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _177_1341 = (FStar_SMTEncoding_Term.unboxInt x)
in ((_177_1342), (_177_1341))))
in (FStar_SMTEncoding_Term.mkLT _177_1343))
in (_177_1344)::[])
in (_177_1346)::_177_1345))
in (_177_1348)::_177_1347))
in (typing_pred_y)::_177_1349)
in (typing_pred)::_177_1350)
in (FStar_SMTEncoding_Term.mk_and_l _177_1351))
in ((_177_1352), (precedes_y_x)))
in (FStar_SMTEncoding_Term.mkImp _177_1353))
in ((((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[]), ((xx)::(yy)::[]), (_177_1354)))
in (mkForall_fuel _177_1355))
in ((_177_1356), (Some ("well-founded ordering on nat (alt)")), (Some ("well-founded-ordering-on-nat"))))
in FStar_SMTEncoding_Term.Assume (_177_1357))
in (_177_1358)::[])
in (_177_1360)::_177_1359))
in (_177_1362)::_177_1361)))))))))))
in (

let mk_str = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.String_sort))
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _177_1385 = (let _177_1376 = (let _177_1375 = (let _177_1374 = (let _177_1373 = (let _177_1370 = (let _177_1369 = (FStar_SMTEncoding_Term.boxString b)
in (_177_1369)::[])
in (_177_1370)::[])
in (let _177_1372 = (let _177_1371 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType _177_1371 tt))
in ((_177_1373), ((bb)::[]), (_177_1372))))
in (FStar_SMTEncoding_Term.mkForall _177_1374))
in ((_177_1375), (Some ("string typing")), (Some ("string_typing"))))
in FStar_SMTEncoding_Term.Assume (_177_1376))
in (let _177_1384 = (let _177_1383 = (let _177_1382 = (let _177_1381 = (let _177_1380 = (let _177_1379 = (let _177_1378 = (let _177_1377 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in ((typing_pred), (_177_1377)))
in (FStar_SMTEncoding_Term.mkImp _177_1378))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_177_1379)))
in (mkForall_fuel _177_1380))
in ((_177_1381), (Some ("string inversion")), (Some ("string_inversion"))))
in FStar_SMTEncoding_Term.Assume (_177_1382))
in (_177_1383)::[])
in (_177_1385)::_177_1384))))))
in (

let mk_ref = (fun env reft_name _85_1865 -> (

let r = (("r"), (FStar_SMTEncoding_Term.Ref_sort))
in (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let refa = (let _177_1394 = (let _177_1393 = (let _177_1392 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (_177_1392)::[])
in ((reft_name), (_177_1393)))
in (FStar_SMTEncoding_Term.mkApp _177_1394))
in (

let refb = (let _177_1397 = (let _177_1396 = (let _177_1395 = (FStar_SMTEncoding_Term.mkFreeV bb)
in (_177_1395)::[])
in ((reft_name), (_177_1396)))
in (FStar_SMTEncoding_Term.mkApp _177_1397))
in (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (

let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (let _177_1416 = (let _177_1403 = (let _177_1402 = (let _177_1401 = (let _177_1400 = (let _177_1399 = (let _177_1398 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in ((typing_pred), (_177_1398)))
in (FStar_SMTEncoding_Term.mkImp _177_1399))
in ((((typing_pred)::[])::[]), ((xx)::(aa)::[]), (_177_1400)))
in (mkForall_fuel _177_1401))
in ((_177_1402), (Some ("ref inversion")), (Some ("ref_inversion"))))
in FStar_SMTEncoding_Term.Assume (_177_1403))
in (let _177_1415 = (let _177_1414 = (let _177_1413 = (let _177_1412 = (let _177_1411 = (let _177_1410 = (let _177_1409 = (let _177_1408 = (FStar_SMTEncoding_Term.mkAnd ((typing_pred), (typing_pred_b)))
in (let _177_1407 = (let _177_1406 = (let _177_1405 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (let _177_1404 = (FStar_SMTEncoding_Term.mkFreeV bb)
in ((_177_1405), (_177_1404))))
in (FStar_SMTEncoding_Term.mkEq _177_1406))
in ((_177_1408), (_177_1407))))
in (FStar_SMTEncoding_Term.mkImp _177_1409))
in ((((typing_pred)::(typing_pred_b)::[])::[]), ((xx)::(aa)::(bb)::[]), (_177_1410)))
in (mkForall_fuel' 2 _177_1411))
in ((_177_1412), (Some ("ref typing is injective")), (Some ("ref_injectivity"))))
in FStar_SMTEncoding_Term.Assume (_177_1413))
in (_177_1414)::[])
in (_177_1416)::_177_1415))))))))))
in (

let mk_false_interp = (fun env nm false_tm -> (

let valid = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((false_tm)::[])))
in (let _177_1425 = (let _177_1424 = (let _177_1423 = (FStar_SMTEncoding_Term.mkIff ((FStar_SMTEncoding_Term.mkFalse), (valid)))
in ((_177_1423), (Some ("False interpretation")), (Some ("false_interp"))))
in FStar_SMTEncoding_Term.Assume (_177_1424))
in (_177_1425)::[])))
in (

let mk_and_interp = (fun env conj _85_1882 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (

let valid = (let _177_1434 = (let _177_1433 = (let _177_1432 = (FStar_SMTEncoding_Term.mkApp ((conj), ((a)::(b)::[])))
in (_177_1432)::[])
in (("Valid"), (_177_1433)))
in (FStar_SMTEncoding_Term.mkApp _177_1434))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((b)::[])))
in (let _177_1441 = (let _177_1440 = (let _177_1439 = (let _177_1438 = (let _177_1437 = (let _177_1436 = (let _177_1435 = (FStar_SMTEncoding_Term.mkAnd ((valid_a), (valid_b)))
in ((_177_1435), (valid)))
in (FStar_SMTEncoding_Term.mkIff _177_1436))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_177_1437)))
in (FStar_SMTEncoding_Term.mkForall _177_1438))
in ((_177_1439), (Some ("/\\ interpretation")), (Some ("l_and-interp"))))
in FStar_SMTEncoding_Term.Assume (_177_1440))
in (_177_1441)::[])))))))))
in (

let mk_or_interp = (fun env disj _85_1894 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (

let valid = (let _177_1450 = (let _177_1449 = (let _177_1448 = (FStar_SMTEncoding_Term.mkApp ((disj), ((a)::(b)::[])))
in (_177_1448)::[])
in (("Valid"), (_177_1449)))
in (FStar_SMTEncoding_Term.mkApp _177_1450))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((b)::[])))
in (let _177_1457 = (let _177_1456 = (let _177_1455 = (let _177_1454 = (let _177_1453 = (let _177_1452 = (let _177_1451 = (FStar_SMTEncoding_Term.mkOr ((valid_a), (valid_b)))
in ((_177_1451), (valid)))
in (FStar_SMTEncoding_Term.mkIff _177_1452))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_177_1453)))
in (FStar_SMTEncoding_Term.mkForall _177_1454))
in ((_177_1455), (Some ("\\/ interpretation")), (Some ("l_or-interp"))))
in FStar_SMTEncoding_Term.Assume (_177_1456))
in (_177_1457)::[])))))))))
in (

let mk_eq2_interp = (fun env eq2 tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let yy = (("y"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (

let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (

let y = (FStar_SMTEncoding_Term.mkFreeV yy)
in (

let valid = (let _177_1466 = (let _177_1465 = (let _177_1464 = (FStar_SMTEncoding_Term.mkApp ((eq2), ((a)::(b)::(x)::(y)::[])))
in (_177_1464)::[])
in (("Valid"), (_177_1465)))
in (FStar_SMTEncoding_Term.mkApp _177_1466))
in (let _177_1473 = (let _177_1472 = (let _177_1471 = (let _177_1470 = (let _177_1469 = (let _177_1468 = (let _177_1467 = (FStar_SMTEncoding_Term.mkEq ((x), (y)))
in ((_177_1467), (valid)))
in (FStar_SMTEncoding_Term.mkIff _177_1468))
in ((((valid)::[])::[]), ((aa)::(bb)::(xx)::(yy)::[]), (_177_1469)))
in (FStar_SMTEncoding_Term.mkForall _177_1470))
in ((_177_1471), (Some ("Eq2 interpretation")), (Some ("eq2-interp"))))
in FStar_SMTEncoding_Term.Assume (_177_1472))
in (_177_1473)::[])))))))))))
in (

let mk_imp_interp = (fun env imp tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (

let valid = (let _177_1482 = (let _177_1481 = (let _177_1480 = (FStar_SMTEncoding_Term.mkApp ((imp), ((a)::(b)::[])))
in (_177_1480)::[])
in (("Valid"), (_177_1481)))
in (FStar_SMTEncoding_Term.mkApp _177_1482))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((b)::[])))
in (let _177_1489 = (let _177_1488 = (let _177_1487 = (let _177_1486 = (let _177_1485 = (let _177_1484 = (let _177_1483 = (FStar_SMTEncoding_Term.mkImp ((valid_a), (valid_b)))
in ((_177_1483), (valid)))
in (FStar_SMTEncoding_Term.mkIff _177_1484))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_177_1485)))
in (FStar_SMTEncoding_Term.mkForall _177_1486))
in ((_177_1487), (Some ("==> interpretation")), (Some ("l_imp-interp"))))
in FStar_SMTEncoding_Term.Assume (_177_1488))
in (_177_1489)::[])))))))))
in (

let mk_iff_interp = (fun env iff tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (

let valid = (let _177_1498 = (let _177_1497 = (let _177_1496 = (FStar_SMTEncoding_Term.mkApp ((iff), ((a)::(b)::[])))
in (_177_1496)::[])
in (("Valid"), (_177_1497)))
in (FStar_SMTEncoding_Term.mkApp _177_1498))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((b)::[])))
in (let _177_1505 = (let _177_1504 = (let _177_1503 = (let _177_1502 = (let _177_1501 = (let _177_1500 = (let _177_1499 = (FStar_SMTEncoding_Term.mkIff ((valid_a), (valid_b)))
in ((_177_1499), (valid)))
in (FStar_SMTEncoding_Term.mkIff _177_1500))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_177_1501)))
in (FStar_SMTEncoding_Term.mkForall _177_1502))
in ((_177_1503), (Some ("<==> interpretation")), (Some ("l_iff-interp"))))
in FStar_SMTEncoding_Term.Assume (_177_1504))
in (_177_1505)::[])))))))))
in (

let mk_forall_interp = (fun env for_all tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (

let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (

let valid = (let _177_1514 = (let _177_1513 = (let _177_1512 = (FStar_SMTEncoding_Term.mkApp ((for_all), ((a)::(b)::[])))
in (_177_1512)::[])
in (("Valid"), (_177_1513)))
in (FStar_SMTEncoding_Term.mkApp _177_1514))
in (

let valid_b_x = (let _177_1517 = (let _177_1516 = (let _177_1515 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_177_1515)::[])
in (("Valid"), (_177_1516)))
in (FStar_SMTEncoding_Term.mkApp _177_1517))
in (let _177_1531 = (let _177_1530 = (let _177_1529 = (let _177_1528 = (let _177_1527 = (let _177_1526 = (let _177_1525 = (let _177_1524 = (let _177_1523 = (let _177_1519 = (let _177_1518 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_177_1518)::[])
in (_177_1519)::[])
in (let _177_1522 = (let _177_1521 = (let _177_1520 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((_177_1520), (valid_b_x)))
in (FStar_SMTEncoding_Term.mkImp _177_1521))
in ((_177_1523), ((xx)::[]), (_177_1522))))
in (FStar_SMTEncoding_Term.mkForall _177_1524))
in ((_177_1525), (valid)))
in (FStar_SMTEncoding_Term.mkIff _177_1526))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_177_1527)))
in (FStar_SMTEncoding_Term.mkForall _177_1528))
in ((_177_1529), (Some ("forall interpretation")), (Some ("forall-interp"))))
in FStar_SMTEncoding_Term.Assume (_177_1530))
in (_177_1531)::[]))))))))))
in (

let mk_exists_interp = (fun env for_some tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (

let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (

let valid = (let _177_1540 = (let _177_1539 = (let _177_1538 = (FStar_SMTEncoding_Term.mkApp ((for_some), ((a)::(b)::[])))
in (_177_1538)::[])
in (("Valid"), (_177_1539)))
in (FStar_SMTEncoding_Term.mkApp _177_1540))
in (

let valid_b_x = (let _177_1543 = (let _177_1542 = (let _177_1541 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_177_1541)::[])
in (("Valid"), (_177_1542)))
in (FStar_SMTEncoding_Term.mkApp _177_1543))
in (let _177_1557 = (let _177_1556 = (let _177_1555 = (let _177_1554 = (let _177_1553 = (let _177_1552 = (let _177_1551 = (let _177_1550 = (let _177_1549 = (let _177_1545 = (let _177_1544 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_177_1544)::[])
in (_177_1545)::[])
in (let _177_1548 = (let _177_1547 = (let _177_1546 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((_177_1546), (valid_b_x)))
in (FStar_SMTEncoding_Term.mkImp _177_1547))
in ((_177_1549), ((xx)::[]), (_177_1548))))
in (FStar_SMTEncoding_Term.mkExists _177_1550))
in ((_177_1551), (valid)))
in (FStar_SMTEncoding_Term.mkIff _177_1552))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_177_1553)))
in (FStar_SMTEncoding_Term.mkForall _177_1554))
in ((_177_1555), (Some ("exists interpretation")), (Some ("exists-interp"))))
in FStar_SMTEncoding_Term.Assume (_177_1556))
in (_177_1557)::[]))))))))))
in (

let mk_range_interp = (fun env range tt -> (

let range_ty = (FStar_SMTEncoding_Term.mkApp ((range), ([])))
in (let _177_1568 = (let _177_1567 = (let _177_1566 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_ty)
in (let _177_1565 = (let _177_1564 = (varops.fresh "typing_range_const")
in Some (_177_1564))
in ((_177_1566), (Some ("Range_const typing")), (_177_1565))))
in FStar_SMTEncoding_Term.Assume (_177_1567))
in (_177_1568)::[])))
in (

let prims = (((FStar_Syntax_Const.unit_lid), (mk_unit)))::(((FStar_Syntax_Const.bool_lid), (mk_bool)))::(((FStar_Syntax_Const.int_lid), (mk_int)))::(((FStar_Syntax_Const.string_lid), (mk_str)))::(((FStar_Syntax_Const.ref_lid), (mk_ref)))::(((FStar_Syntax_Const.false_lid), (mk_false_interp)))::(((FStar_Syntax_Const.and_lid), (mk_and_interp)))::(((FStar_Syntax_Const.or_lid), (mk_or_interp)))::(((FStar_Syntax_Const.eq2_lid), (mk_eq2_interp)))::(((FStar_Syntax_Const.imp_lid), (mk_imp_interp)))::(((FStar_Syntax_Const.iff_lid), (mk_iff_interp)))::(((FStar_Syntax_Const.forall_lid), (mk_forall_interp)))::(((FStar_Syntax_Const.exists_lid), (mk_exists_interp)))::(((FStar_Syntax_Const.range_lid), (mk_range_interp)))::[]
in (fun env t s tt -> (match ((FStar_Util.find_opt (fun _85_1976 -> (match (_85_1976) with
| (l, _85_1975) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_85_1979, f) -> begin
(f env s tt)
end)))))))))))))))))))))


let encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let _85_1989 = (encode_function_type_as_formula None None t env)
in (match (_85_1989) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_SMTEncoding_Term.Assume (((form), (Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str))), (Some ((Prims.strcat "lemma_" lid.FStar_Ident.str))))))::[]))
end))))


let encode_free_var : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env fv tt t_norm quals -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if ((let _177_1758 = (FStar_Syntax_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _177_1758)) || (FStar_Syntax_Util.is_lemma t_norm)) then begin
(

let _85_1999 = (new_term_constant_and_tok_from_lid env lid)
in (match (_85_1999) with
| (vname, vtok, env) -> begin
(

let arg_sorts = (match ((let _177_1759 = (FStar_Syntax_Subst.compress t_norm)
in _177_1759.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _85_2002) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun _85_2005 -> FStar_SMTEncoding_Term.Term_sort)))
end
| _85_2008 -> begin
[]
end)
in (

let d = FStar_SMTEncoding_Term.DeclFun (((vname), (arg_sorts), (FStar_SMTEncoding_Term.Term_sort), (Some ("Uninterpreted function symbol for impure function"))))
in (

let dd = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Uninterpreted name for impure function"))))
in (((d)::(dd)::[]), (env)))))
end))
end else begin
if (prims.is lid) then begin
(

let vname = (varops.new_fvar lid)
in (

let definition = (prims.mk lid vname)
in (

let env = (push_free_var env lid vname None)
in ((definition), (env)))))
end else begin
(

let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (

let _85_2023 = (

let _85_2018 = (curried_arrow_formals_comp t_norm)
in (match (_85_2018) with
| (args, comp) -> begin
if encode_non_total_function_typ then begin
(let _177_1761 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in ((args), (_177_1761)))
end else begin
((args), (((None), ((FStar_Syntax_Util.comp_result comp)))))
end
end))
in (match (_85_2023) with
| (formals, (pre_opt, res_t)) -> begin
(

let _85_2027 = (new_term_constant_and_tok_from_lid env lid)
in (match (_85_2027) with
| (vname, vtok, env) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
end
| _85_2030 -> begin
(FStar_SMTEncoding_Term.mkApp ((vtok), ([])))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun _85_14 -> (match (_85_14) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(

let _85_2046 = (FStar_Util.prefix vars)
in (match (_85_2046) with
| (_85_2041, (xxsym, _85_2044)) -> begin
(

let xx = (FStar_SMTEncoding_Term.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (let _177_1778 = (let _177_1777 = (let _177_1776 = (let _177_1775 = (let _177_1774 = (let _177_1773 = (let _177_1772 = (let _177_1771 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1771))
in ((vapp), (_177_1772)))
in (FStar_SMTEncoding_Term.mkEq _177_1773))
in ((((vapp)::[])::[]), (vars), (_177_1774)))
in (FStar_SMTEncoding_Term.mkForall _177_1775))
in ((_177_1776), (Some ("Discriminator equation")), (Some ((Prims.strcat "disc_equation_" (escape d.FStar_Ident.str))))))
in FStar_SMTEncoding_Term.Assume (_177_1777))
in (_177_1778)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(

let _85_2058 = (FStar_Util.prefix vars)
in (match (_85_2058) with
| (_85_2053, (xxsym, _85_2056)) -> begin
(

let xx = (FStar_SMTEncoding_Term.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = 0; FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (

let tp_name = (mk_term_projector_name d f)
in (

let prim_app = (FStar_SMTEncoding_Term.mkApp ((tp_name), ((xx)::[])))
in (let _177_1783 = (let _177_1782 = (let _177_1781 = (let _177_1780 = (let _177_1779 = (FStar_SMTEncoding_Term.mkEq ((vapp), (prim_app)))
in ((((vapp)::[])::[]), (vars), (_177_1779)))
in (FStar_SMTEncoding_Term.mkForall _177_1780))
in ((_177_1781), (Some ("Projector equation")), (Some ((Prims.strcat "proj_equation_" tp_name)))))
in FStar_SMTEncoding_Term.Assume (_177_1782))
in (_177_1783)::[])))))
end))
end
| _85_2064 -> begin
[]
end)))))
in (

let _85_2071 = (encode_binders None formals env)
in (match (_85_2071) with
| (vars, guards, env', decls1, _85_2070) -> begin
(

let _85_2080 = (match (pre_opt) with
| None -> begin
(let _177_1784 = (FStar_SMTEncoding_Term.mk_and_l guards)
in ((_177_1784), (decls1)))
end
| Some (p) -> begin
(

let _85_2077 = (encode_formula p env')
in (match (_85_2077) with
| (g, ds) -> begin
(let _177_1785 = (FStar_SMTEncoding_Term.mk_and_l ((g)::guards))
in ((_177_1785), ((FStar_List.append decls1 ds))))
end))
end)
in (match (_85_2080) with
| (guard, decls1) -> begin
(

let vtok_app = (mk_Apply vtok_tm vars)
in (

let vapp = (let _177_1787 = (let _177_1786 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in ((vname), (_177_1786)))
in (FStar_SMTEncoding_Term.mkApp _177_1787))
in (

let _85_2104 = (

let vname_decl = (let _177_1790 = (let _177_1789 = (FStar_All.pipe_right formals (FStar_List.map (fun _85_2083 -> FStar_SMTEncoding_Term.Term_sort)))
in ((vname), (_177_1789), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (_177_1790))
in (

let _85_2091 = (

let env = (

let _85_2086 = env
in {bindings = _85_2086.bindings; depth = _85_2086.depth; tcenv = _85_2086.tcenv; warn = _85_2086.warn; cache = _85_2086.cache; nolabels = _85_2086.nolabels; use_zfuel_name = _85_2086.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in if (not ((head_normal env tt))) then begin
(encode_term_pred None tt env vtok_tm)
end else begin
(encode_term_pred None t_norm env vtok_tm)
end)
in (match (_85_2091) with
| (tok_typing, decls2) -> begin
(

let tok_typing = FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("function token typing")), (Some ((Prims.strcat "function_token_typing_" vname)))))
in (

let _85_2101 = (match (formals) with
| [] -> begin
(let _177_1794 = (let _177_1793 = (let _177_1792 = (FStar_SMTEncoding_Term.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left (fun _177_1791 -> Some (_177_1791)) _177_1792))
in (push_free_var env lid vname _177_1793))
in (((FStar_List.append decls2 ((tok_typing)::[]))), (_177_1794)))
end
| _85_2095 -> begin
(

let vtok_decl = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let vtok_fresh = (let _177_1795 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((vtok), (FStar_SMTEncoding_Term.Term_sort)) _177_1795))
in (

let name_tok_corr = (let _177_1799 = (let _177_1798 = (let _177_1797 = (let _177_1796 = (FStar_SMTEncoding_Term.mkEq ((vtok_app), (vapp)))
in ((((vtok_app)::[])::[]), (vars), (_177_1796)))
in (FStar_SMTEncoding_Term.mkForall _177_1797))
in ((_177_1798), (Some ("Name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" vname)))))
in FStar_SMTEncoding_Term.Assume (_177_1799))
in (((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[]))), (env)))))
end)
in (match (_85_2101) with
| (tok_decl, env) -> begin
(((vname_decl)::tok_decl), (env))
end)))
end)))
in (match (_85_2104) with
| (decls2, env) -> begin
(

let _85_2112 = (

let res_t = (FStar_Syntax_Subst.compress res_t)
in (

let _85_2108 = (encode_term res_t env')
in (match (_85_2108) with
| (encoded_res_t, decls) -> begin
(let _177_1800 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in ((encoded_res_t), (_177_1800), (decls)))
end)))
in (match (_85_2112) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (let _177_1804 = (let _177_1803 = (let _177_1802 = (let _177_1801 = (FStar_SMTEncoding_Term.mkImp ((guard), (ty_pred)))
in ((((vapp)::[])::[]), (vars), (_177_1801)))
in (FStar_SMTEncoding_Term.mkForall _177_1802))
in ((_177_1803), (Some ("free var typing")), (Some ((Prims.strcat "typing_" vname)))))
in FStar_SMTEncoding_Term.Assume (_177_1804))
in (

let freshness = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New)) then begin
(let _177_1810 = (let _177_1807 = (let _177_1806 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (let _177_1805 = (varops.next_id ())
in ((vname), (_177_1806), (FStar_SMTEncoding_Term.Term_sort), (_177_1805))))
in (FStar_SMTEncoding_Term.fresh_constructor _177_1807))
in (let _177_1809 = (let _177_1808 = (pretype_axiom vapp vars)
in (_177_1808)::[])
in (_177_1810)::_177_1809))
end else begin
[]
end
in (

let g = (let _177_1812 = (let _177_1811 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_177_1811)
in (FStar_List.append (FStar_List.append (FStar_List.append (FStar_List.append decls1 decls2) decls3) freshness) _177_1812))
in ((g), (env)))))
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

let _85_2123 = (encode_free_var env x t t_norm [])
in (match (_85_2123) with
| (decls, env) -> begin
(

let _85_2128 = (lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_85_2128) with
| (n, x', _85_2127) -> begin
((((n), (x'))), (decls), (env))
end))
end))
end
| Some (n, x, _85_2132) -> begin
((((n), (x))), ([]), (env))
end))


let encode_top_level_val : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env lid t quals -> (

let tt = (norm env t)
in (

let _85_2142 = (encode_free_var env lid t tt quals)
in (match (_85_2142) with
| (decls, env) -> begin
if (FStar_Syntax_Util.is_smt_lemma t) then begin
(let _177_1830 = (let _177_1829 = (encode_smt_lemma env lid tt)
in (FStar_List.append decls _177_1829))
in ((_177_1830), (env)))
end else begin
((decls), (env))
end
end))))


let encode_top_level_vals : env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _85_2148 lb -> (match (_85_2148) with
| (decls, env) -> begin
(

let _85_2152 = (let _177_1839 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env _177_1839 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (_85_2152) with
| (decls', env) -> begin
(((FStar_List.append decls decls')), (env))
end))
end)) (([]), (env)))))


let encode_top_level_let : env_t  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env _85_2156 quals -> (match (_85_2156) with
| (is_rec, bindings) -> begin
(

let eta_expand = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let _85_2166 = (FStar_Util.first_N nbinders formals)
in (match (_85_2166) with
| (formals, extra_formals) -> begin
(

let subst = (FStar_List.map2 (fun _85_2170 _85_2174 -> (match (((_85_2170), (_85_2174))) with
| ((formal, _85_2169), (binder, _85_2173)) -> begin
(let _177_1857 = (let _177_1856 = (FStar_Syntax_Syntax.bv_to_name binder)
in ((formal), (_177_1856)))
in FStar_Syntax_Syntax.NT (_177_1857))
end)) formals binders)
in (

let extra_formals = (let _177_1861 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun _85_2178 -> (match (_85_2178) with
| (x, i) -> begin
(let _177_1860 = (

let _85_2179 = x
in (let _177_1859 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _85_2179.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _85_2179.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _177_1859}))
in ((_177_1860), (i)))
end))))
in (FStar_All.pipe_right _177_1861 FStar_Syntax_Util.name_binders))
in (

let body = (let _177_1868 = (FStar_Syntax_Subst.compress body)
in (let _177_1867 = (let _177_1862 = (FStar_Syntax_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _177_1862))
in (let _177_1866 = (let _177_1865 = (let _177_1864 = (FStar_Syntax_Subst.subst subst t)
in _177_1864.FStar_Syntax_Syntax.n)
in (FStar_All.pipe_left (fun _177_1863 -> Some (_177_1863)) _177_1865))
in (FStar_Syntax_Syntax.extend_app_n _177_1868 _177_1867 _177_1866 body.FStar_Syntax_Syntax.pos))))
in (((FStar_List.append binders extra_formals)), (body)))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (

let rec aux = (fun norm t_norm -> (match ((let _177_1879 = (FStar_Syntax_Util.unascribe e)
in _177_1879.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, lopt) -> begin
(

let _85_2198 = (FStar_Syntax_Subst.open_term' binders body)
in (match (_85_2198) with
| (binders, body, opening) -> begin
(match ((let _177_1880 = (FStar_Syntax_Subst.compress t_norm)
in _177_1880.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let _85_2205 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_85_2205) with
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

let _85_2212 = (FStar_Util.first_N nformals binders)
in (match (_85_2212) with
| (bs0, rest) -> begin
(

let c = (

let subst = (FStar_List.map2 (fun _85_2216 _85_2220 -> (match (((_85_2216), (_85_2220))) with
| ((b, _85_2215), (x, _85_2219)) -> begin
(let _177_1884 = (let _177_1883 = (FStar_Syntax_Syntax.bv_to_name x)
in ((b), (_177_1883)))
in FStar_Syntax_Syntax.NT (_177_1884))
end)) bs0 formals)
in (FStar_Syntax_Subst.subst_comp subst c))
in (

let body = (FStar_Syntax_Util.abs rest body lopt)
in ((bs0), (body), (bs0), ((FStar_Syntax_Util.comp_result c)))))
end)))
end else begin
if (nformals > nbinders) then begin
(

let _85_2226 = (eta_expand binders formals body tres)
in (match (_85_2226) with
| (binders, body) -> begin
((binders), (body), (formals), (tres))
end))
end else begin
((binders), (body), (formals), (tres))
end
end)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, _85_2229) -> begin
(aux norm x.FStar_Syntax_Syntax.sort)
end
| _85_2233 when (not (norm)) -> begin
(

let t_norm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm)
in (aux true t_norm))
end
| _85_2236 -> begin
(let _177_1887 = (let _177_1886 = (FStar_Syntax_Print.term_to_string e)
in (let _177_1885 = (FStar_Syntax_Print.term_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str _177_1886 _177_1885)))
in (FStar_All.failwith _177_1887))
end)
end))
end
| _85_2238 -> begin
(match ((let _177_1888 = (FStar_Syntax_Subst.compress t_norm)
in _177_1888.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let _85_2245 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_85_2245) with
| (formals, c) -> begin
(

let tres = (FStar_Syntax_Util.comp_result c)
in (

let _85_2249 = (eta_expand [] formals e tres)
in (match (_85_2249) with
| (binders, body) -> begin
((binders), (body), (formals), (tres))
end)))
end))
end
| _85_2251 -> begin
(([]), (e), ([]), (t_norm))
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

let _85_2279 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _85_2266 lb -> (match (_85_2266) with
| (toks, typs, decls, env) -> begin
(

let _85_2268 = if (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) then begin
(Prims.raise Let_rec_unencodeable)
end else begin
()
end
in (

let t_norm = (whnf env lb.FStar_Syntax_Syntax.lbtyp)
in (

let _85_2274 = (let _177_1893 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env _177_1893 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (_85_2274) with
| (tok, decl, env) -> begin
(let _177_1896 = (let _177_1895 = (let _177_1894 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in ((_177_1894), (tok)))
in (_177_1895)::toks)
in ((_177_1896), ((t_norm)::typs), ((decl)::decls), (env)))
end))))
end)) (([]), ([]), ([]), (env))))
in (match (_85_2279) with
| (toks, typs, decls, env) -> begin
(

let toks = (FStar_List.rev toks)
in (

let decls = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (

let typs = (FStar_List.rev typs)
in if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _85_15 -> (match (_85_15) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| _85_2286 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> (let _177_1899 = (FStar_Syntax_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _177_1899)))))) then begin
((decls), (env))
end else begin
if (not (is_rec)) then begin
(match (((bindings), (typs), (toks))) with
| (({FStar_Syntax_Syntax.lbname = _85_2296; FStar_Syntax_Syntax.lbunivs = _85_2294; FStar_Syntax_Syntax.lbtyp = _85_2292; FStar_Syntax_Syntax.lbeff = _85_2290; FStar_Syntax_Syntax.lbdef = e})::[], (t_norm)::[], ((flid_fv, (f, ftok)))::[]) -> begin
(

let e = (FStar_Syntax_Subst.compress e)
in (

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let _85_2316 = (destruct_bound_function flid t_norm e)
in (match (_85_2316) with
| (binders, body, _85_2313, _85_2315) -> begin
(

let _85_2323 = (encode_binders None binders env)
in (match (_85_2323) with
| (vars, guards, env', binder_decls, _85_2322) -> begin
(

let app = (match (vars) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
end
| _85_2326 -> begin
(let _177_1901 = (let _177_1900 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in ((f), (_177_1900)))
in (FStar_SMTEncoding_Term.mkApp _177_1901))
end)
in (

let _85_2332 = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic)) then begin
(let _177_1903 = (FStar_SMTEncoding_Term.mk_Valid app)
in (let _177_1902 = (encode_formula body env')
in ((_177_1903), (_177_1902))))
end else begin
(let _177_1904 = (encode_term body env')
in ((app), (_177_1904)))
end
in (match (_85_2332) with
| (app, (body, decls2)) -> begin
(

let eqn = (let _177_1910 = (let _177_1909 = (let _177_1906 = (let _177_1905 = (FStar_SMTEncoding_Term.mkEq ((app), (body)))
in ((((app)::[])::[]), (vars), (_177_1905)))
in (FStar_SMTEncoding_Term.mkForall _177_1906))
in (let _177_1908 = (let _177_1907 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (_177_1907))
in ((_177_1909), (_177_1908), (Some ((Prims.strcat "equation_" f))))))
in FStar_SMTEncoding_Term.Assume (_177_1910))
in (let _177_1912 = (let _177_1911 = (primitive_type_axioms env.tcenv flid f app)
in (FStar_List.append (FStar_List.append (FStar_List.append (FStar_List.append decls binder_decls) decls2) ((eqn)::[])) _177_1911))
in ((_177_1912), (env))))
end)))
end))
end))))
end
| _85_2335 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(

let fuel = (let _177_1913 = (varops.fresh "fuel")
in ((_177_1913), (FStar_SMTEncoding_Term.Fuel_sort)))
in (

let fuel_tm = (FStar_SMTEncoding_Term.mkFreeV fuel)
in (

let env0 = env
in (

let _85_2353 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _85_2341 _85_2346 -> (match (((_85_2341), (_85_2346))) with
| ((gtoks, env), (flid_fv, (f, ftok))) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let g = (varops.new_fvar flid)
in (

let gtok = (varops.new_fvar flid)
in (

let env = (let _177_1918 = (let _177_1917 = (FStar_SMTEncoding_Term.mkApp ((g), ((fuel_tm)::[])))
in (FStar_All.pipe_left (fun _177_1916 -> Some (_177_1916)) _177_1917))
in (push_free_var env flid gtok _177_1918))
in (((((flid), (f), (ftok), (g), (gtok)))::gtoks), (env))))))
end)) (([]), (env))))
in (match (_85_2353) with
| (gtoks, env) -> begin
(

let gtoks = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env0 _85_2362 t_norm _85_2373 -> (match (((_85_2362), (_85_2373))) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = _85_2372; FStar_Syntax_Syntax.lbunivs = _85_2370; FStar_Syntax_Syntax.lbtyp = _85_2368; FStar_Syntax_Syntax.lbeff = _85_2366; FStar_Syntax_Syntax.lbdef = e}) -> begin
(

let _85_2378 = (destruct_bound_function flid t_norm e)
in (match (_85_2378) with
| (binders, body, formals, tres) -> begin
(

let _85_2385 = (encode_binders None binders env)
in (match (_85_2385) with
| (vars, guards, env', binder_decls, _85_2384) -> begin
(

let decl_g = (let _177_1929 = (let _177_1928 = (let _177_1927 = (FStar_List.map Prims.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::_177_1927)
in ((g), (_177_1928), (FStar_SMTEncoding_Term.Term_sort), (Some ("Fuel-instrumented function name"))))
in FStar_SMTEncoding_Term.DeclFun (_177_1929))
in (

let env0 = (push_zfuel_name env0 flid g)
in (

let decl_g_tok = FStar_SMTEncoding_Term.DeclFun (((gtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Token for fuel-instrumented partial applications"))))
in (

let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (

let app = (FStar_SMTEncoding_Term.mkApp ((f), (vars_tm)))
in (

let gsapp = (let _177_1932 = (let _177_1931 = (let _177_1930 = (FStar_SMTEncoding_Term.mkApp (("SFuel"), ((fuel_tm)::[])))
in (_177_1930)::vars_tm)
in ((g), (_177_1931)))
in (FStar_SMTEncoding_Term.mkApp _177_1932))
in (

let gmax = (let _177_1935 = (let _177_1934 = (let _177_1933 = (FStar_SMTEncoding_Term.mkApp (("MaxFuel"), ([])))
in (_177_1933)::vars_tm)
in ((g), (_177_1934)))
in (FStar_SMTEncoding_Term.mkApp _177_1935))
in (

let _85_2395 = (encode_term body env')
in (match (_85_2395) with
| (body_tm, decls2) -> begin
(

let eqn_g = (let _177_1941 = (let _177_1940 = (let _177_1937 = (let _177_1936 = (FStar_SMTEncoding_Term.mkEq ((gsapp), (body_tm)))
in ((((gsapp)::[])::[]), ((fuel)::vars), (_177_1936)))
in (FStar_SMTEncoding_Term.mkForall _177_1937))
in (let _177_1939 = (let _177_1938 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (_177_1938))
in ((_177_1940), (_177_1939), (Some ((Prims.strcat "equation_with_fuel_" g))))))
in FStar_SMTEncoding_Term.Assume (_177_1941))
in (

let eqn_f = (let _177_1945 = (let _177_1944 = (let _177_1943 = (let _177_1942 = (FStar_SMTEncoding_Term.mkEq ((app), (gmax)))
in ((((app)::[])::[]), (vars), (_177_1942)))
in (FStar_SMTEncoding_Term.mkForall _177_1943))
in ((_177_1944), (Some ("Correspondence of recursive function to instrumented version")), (Some ((Prims.strcat "fuel_correspondence_" g)))))
in FStar_SMTEncoding_Term.Assume (_177_1945))
in (

let eqn_g' = (let _177_1954 = (let _177_1953 = (let _177_1952 = (let _177_1951 = (let _177_1950 = (let _177_1949 = (let _177_1948 = (let _177_1947 = (let _177_1946 = (FStar_SMTEncoding_Term.n_fuel 0)
in (_177_1946)::vars_tm)
in ((g), (_177_1947)))
in (FStar_SMTEncoding_Term.mkApp _177_1948))
in ((gsapp), (_177_1949)))
in (FStar_SMTEncoding_Term.mkEq _177_1950))
in ((((gsapp)::[])::[]), ((fuel)::vars), (_177_1951)))
in (FStar_SMTEncoding_Term.mkForall _177_1952))
in ((_177_1953), (Some ("Fuel irrelevance")), (Some ((Prims.strcat "fuel_irrelevance_" g)))))
in FStar_SMTEncoding_Term.Assume (_177_1954))
in (

let _85_2418 = (

let _85_2405 = (encode_binders None formals env0)
in (match (_85_2405) with
| (vars, v_guards, env, binder_decls, _85_2404) -> begin
(

let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (

let gapp = (FStar_SMTEncoding_Term.mkApp ((g), ((fuel_tm)::vars_tm)))
in (

let tok_corr = (

let tok_app = (let _177_1955 = (FStar_SMTEncoding_Term.mkFreeV ((gtok), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply _177_1955 ((fuel)::vars)))
in (let _177_1959 = (let _177_1958 = (let _177_1957 = (let _177_1956 = (FStar_SMTEncoding_Term.mkEq ((tok_app), (gapp)))
in ((((tok_app)::[])::[]), ((fuel)::vars), (_177_1956)))
in (FStar_SMTEncoding_Term.mkForall _177_1957))
in ((_177_1958), (Some ("Fuel token correspondence")), (Some ((Prims.strcat "fuel_tokem_correspondence_" gtok)))))
in FStar_SMTEncoding_Term.Assume (_177_1959)))
in (

let _85_2415 = (

let _85_2412 = (encode_term_pred None tres env gapp)
in (match (_85_2412) with
| (g_typing, d3) -> begin
(let _177_1967 = (let _177_1966 = (let _177_1965 = (let _177_1964 = (let _177_1963 = (let _177_1962 = (let _177_1961 = (let _177_1960 = (FStar_SMTEncoding_Term.mk_and_l v_guards)
in ((_177_1960), (g_typing)))
in (FStar_SMTEncoding_Term.mkImp _177_1961))
in ((((gapp)::[])::[]), ((fuel)::vars), (_177_1962)))
in (FStar_SMTEncoding_Term.mkForall _177_1963))
in ((_177_1964), (Some ("Typing correspondence of token to term")), (Some ((Prims.strcat "token_correspondence_" g)))))
in FStar_SMTEncoding_Term.Assume (_177_1965))
in (_177_1966)::[])
in ((d3), (_177_1967)))
end))
in (match (_85_2415) with
| (aux_decls, typing_corr) -> begin
(((FStar_List.append binder_decls aux_decls)), ((FStar_List.append typing_corr ((tok_corr)::[]))))
end)))))
end))
in (match (_85_2418) with
| (aux_decls, g_typing) -> begin
(((FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) aux_decls) ((decl_g)::(decl_g_tok)::[]))), ((FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing)), (env0))
end)))))
end)))))))))
end))
end))
end))
in (

let _85_2434 = (let _177_1970 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _85_2422 _85_2426 -> (match (((_85_2422), (_85_2426))) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(

let _85_2430 = (encode_one_binding env0 gtok ty bs)
in (match (_85_2430) with
| (decls', eqns', env0) -> begin
(((decls')::decls), ((FStar_List.append eqns' eqns)), (env0))
end))
end)) (((decls)::[]), ([]), (env0)) _177_1970))
in (match (_85_2434) with
| (decls, eqns, env0) -> begin
(

let _85_2443 = (let _177_1972 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _177_1972 (FStar_List.partition (fun _85_16 -> (match (_85_16) with
| FStar_SMTEncoding_Term.DeclFun (_85_2437) -> begin
true
end
| _85_2440 -> begin
false
end)))))
in (match (_85_2443) with
| (prefix_decls, rest) -> begin
(

let eqns = (FStar_List.rev eqns)
in (((FStar_List.append (FStar_List.append prefix_decls rest) eqns)), (env0)))
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

let msg = (let _177_1975 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _177_1975 (FStar_String.concat " and ")))
in (

let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in (((decl)::[]), (env))))
end))
end))


let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let _85_2447 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _177_1984 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _177_1984))
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

let _85_2455 = (encode_sigelt' env se)
in (match (_85_2455) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _177_1987 = (let _177_1986 = (let _177_1985 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (_177_1985))
in (_177_1986)::[])
in ((_177_1987), (e)))
end
| _85_2458 -> begin
(let _177_1994 = (let _177_1993 = (let _177_1989 = (let _177_1988 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_177_1988))
in (_177_1989)::g)
in (let _177_1992 = (let _177_1991 = (let _177_1990 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_177_1990))
in (_177_1991)::[])
in (FStar_List.append _177_1993 _177_1992)))
in ((_177_1994), (e)))
end)
end)))))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let should_skip = (fun l -> false)
in (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_85_2464) -> begin
(FStar_All.failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _85_2480) -> begin
if (let _177_1999 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right _177_1999 Prims.op_Negation)) then begin
(([]), (env))
end else begin
(

let encode_monad_op = (fun tm name env -> (

let repr_name = (fun ed -> (FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid ed.FStar_Syntax_Syntax.mname) (((FStar_Ident.id_of_text (Prims.strcat name "_repr")))::[]))))
in (

let _85_2493 = (let _177_2008 = (repr_name ed)
in (new_term_constant_and_tok_from_lid env _177_2008))
in (match (_85_2493) with
| (br_name, _85_2491, env) -> begin
(

let _85_2496 = (encode_term (Prims.snd tm) env)
in (match (_85_2496) with
| (tm, decls) -> begin
(

let xs = if (name = "bind") then begin
((("@x0"), (FStar_SMTEncoding_Term.Term_sort)))::((("@x1"), (FStar_SMTEncoding_Term.Term_sort)))::((("@x2"), (FStar_SMTEncoding_Term.Term_sort)))::((("@x3"), (FStar_SMTEncoding_Term.Term_sort)))::((("@x4"), (FStar_SMTEncoding_Term.Term_sort)))::((("@x5"), (FStar_SMTEncoding_Term.Term_sort)))::[]
end else begin
((("@x0"), (FStar_SMTEncoding_Term.Term_sort)))::((("@x1"), (FStar_SMTEncoding_Term.Term_sort)))::((("@x2"), (FStar_SMTEncoding_Term.Term_sort)))::[]
end
in (

let m_decl = (let _177_2010 = (let _177_2009 = (FStar_All.pipe_right xs (FStar_List.map Prims.snd))
in ((br_name), (_177_2009), (FStar_SMTEncoding_Term.Term_sort), (Some (name))))
in FStar_SMTEncoding_Term.DeclFun (_177_2010))
in (

let eqn = (

let app = (let _177_2013 = (let _177_2012 = (let _177_2011 = (FStar_All.pipe_right xs (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in ((FStar_SMTEncoding_Term.Var (br_name)), (_177_2011)))
in FStar_SMTEncoding_Term.App (_177_2012))
in (FStar_SMTEncoding_Term.mk _177_2013))
in (let _177_2019 = (let _177_2018 = (let _177_2017 = (let _177_2016 = (let _177_2015 = (let _177_2014 = (mk_Apply tm xs)
in ((app), (_177_2014)))
in (FStar_SMTEncoding_Term.mkEq _177_2015))
in ((((app)::[])::[]), (xs), (_177_2016)))
in (FStar_SMTEncoding_Term.mkForall _177_2017))
in ((_177_2018), (Some ((Prims.strcat name " equality"))), (Some ((Prims.strcat br_name "_equality")))))
in FStar_SMTEncoding_Term.Assume (_177_2019)))
in ((env), ((m_decl)::(eqn)::[])))))
end))
end))))
in (

let encode_action = (fun env a -> (

let _85_2507 = (new_term_constant_and_tok_from_lid env a.FStar_Syntax_Syntax.action_name)
in (match (_85_2507) with
| (aname, atok, env) -> begin
(

let _85_2511 = (FStar_Syntax_Util.arrow_formals_comp a.FStar_Syntax_Syntax.action_typ)
in (match (_85_2511) with
| (formals, _85_2510) -> begin
(

let _85_2514 = (encode_term a.FStar_Syntax_Syntax.action_defn env)
in (match (_85_2514) with
| (tm, decls) -> begin
(

let a_decls = (let _177_2027 = (let _177_2026 = (let _177_2025 = (FStar_All.pipe_right formals (FStar_List.map (fun _85_2515 -> FStar_SMTEncoding_Term.Term_sort)))
in ((aname), (_177_2025), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action"))))
in FStar_SMTEncoding_Term.DeclFun (_177_2026))
in (_177_2027)::(FStar_SMTEncoding_Term.DeclFun (((atok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action token")))))::[])
in (

let _85_2529 = (let _177_2029 = (FStar_All.pipe_right formals (FStar_List.map (fun _85_2521 -> (match (_85_2521) with
| (bv, _85_2520) -> begin
(

let _85_2526 = (gen_term_var env bv)
in (match (_85_2526) with
| (xxsym, xx, _85_2525) -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (xx))
end))
end))))
in (FStar_All.pipe_right _177_2029 FStar_List.split))
in (match (_85_2529) with
| (xs_sorts, xs) -> begin
(

let app = (let _177_2033 = (let _177_2032 = (let _177_2031 = (let _177_2030 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Var (aname)), (xs)))))
in (_177_2030)::[])
in ((FStar_SMTEncoding_Term.Var ("Reify")), (_177_2031)))
in FStar_SMTEncoding_Term.App (_177_2032))
in (FStar_All.pipe_right _177_2033 FStar_SMTEncoding_Term.mk))
in (

let a_eq = (let _177_2039 = (let _177_2038 = (let _177_2037 = (let _177_2036 = (let _177_2035 = (let _177_2034 = (mk_Apply tm xs_sorts)
in ((app), (_177_2034)))
in (FStar_SMTEncoding_Term.mkEq _177_2035))
in ((((app)::[])::[]), (xs_sorts), (_177_2036)))
in (FStar_SMTEncoding_Term.mkForall _177_2037))
in ((_177_2038), (Some ("Action equality")), (Some ((Prims.strcat aname "_equality")))))
in FStar_SMTEncoding_Term.Assume (_177_2039))
in (

let tok_correspondence = (

let tok_term = (FStar_SMTEncoding_Term.mkFreeV ((atok), (FStar_SMTEncoding_Term.Term_sort)))
in (

let tok_app = (mk_Apply tok_term xs_sorts)
in (let _177_2043 = (let _177_2042 = (let _177_2041 = (let _177_2040 = (FStar_SMTEncoding_Term.mkEq ((tok_app), (app)))
in ((((tok_app)::[])::[]), (xs_sorts), (_177_2040)))
in (FStar_SMTEncoding_Term.mkForall _177_2041))
in ((_177_2042), (Some ("Action token correspondence")), (Some ((Prims.strcat aname "_token_correspondence")))))
in FStar_SMTEncoding_Term.Assume (_177_2043))))
in ((env), ((FStar_List.append (FStar_List.append decls a_decls) ((a_eq)::(tok_correspondence)::[])))))))
end)))
end))
end))
end)))
in (

let _85_2537 = (encode_monad_op ed.FStar_Syntax_Syntax.bind_repr "bind" env)
in (match (_85_2537) with
| (env, decls0) -> begin
(

let _85_2540 = (encode_monad_op ed.FStar_Syntax_Syntax.return_repr "return" env)
in (match (_85_2540) with
| (env, decls1) -> begin
(

let _85_2543 = (FStar_Util.fold_map encode_action env ed.FStar_Syntax_Syntax.actions)
in (match (_85_2543) with
| (env, decls2) -> begin
(((FStar_List.append (FStar_List.append decls0 decls1) (FStar_List.flatten decls2))), (env))
end))
end))
end))))
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _85_2546, _85_2548, _85_2550, _85_2552) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid) -> begin
(

let _85_2558 = (new_term_constant_and_tok_from_lid env lid)
in (match (_85_2558) with
| (tname, ttok, env) -> begin
(([]), (env))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _85_2561, t, quals, _85_2565) -> begin
(

let will_encode_definition = (not ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _85_17 -> (match (_85_17) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Irreducible) -> begin
true
end
| _85_2578 -> begin
false
end))))))
in if will_encode_definition then begin
(([]), (env))
end else begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (

let _85_2583 = (encode_top_level_val env fv t quals)
in (match (_85_2583) with
| (decls, env) -> begin
(

let tname = lid.FStar_Ident.str
in (

let tsym = (FStar_SMTEncoding_Term.mkFreeV ((tname), (FStar_SMTEncoding_Term.Term_sort)))
in (let _177_2046 = (let _177_2045 = (primitive_type_axioms env.tcenv lid tname tsym)
in (FStar_List.append decls _177_2045))
in ((_177_2046), (env)))))
end)))
end)
end
| FStar_Syntax_Syntax.Sig_assume (l, f, _85_2589, _85_2591) -> begin
(

let _85_2596 = (encode_formula f env)
in (match (_85_2596) with
| (f, decls) -> begin
(

let g = (let _177_2053 = (let _177_2052 = (let _177_2051 = (let _177_2048 = (let _177_2047 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" _177_2047))
in Some (_177_2048))
in (let _177_2050 = (let _177_2049 = (varops.fresh (Prims.strcat "assumption_" l.FStar_Ident.str))
in Some (_177_2049))
in ((f), (_177_2051), (_177_2050))))
in FStar_SMTEncoding_Term.Assume (_177_2052))
in (_177_2053)::[])
in (((FStar_List.append decls g)), (env)))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _85_2601, quals) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) -> begin
(

let _85_2614 = (FStar_Util.fold_map (fun env lb -> (

let lid = (let _177_2057 = (let _177_2056 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _177_2056.FStar_Syntax_Syntax.fv_name)
in _177_2057.FStar_Syntax_Syntax.v)
in if (let _177_2058 = (FStar_TypeChecker_Env.try_lookup_val_decl env.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone _177_2058)) then begin
(

let val_decl = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), (r)))
in (

let _85_2611 = (encode_sigelt' env val_decl)
in (match (_85_2611) with
| (decls, env) -> begin
((env), (decls))
end)))
end else begin
((env), ([]))
end)) env (Prims.snd lbs))
in (match (_85_2614) with
| (env, decls) -> begin
(((FStar_List.flatten decls)), (env))
end))
end
| FStar_Syntax_Syntax.Sig_let ((_85_2616, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t); FStar_Syntax_Syntax.lbunivs = _85_2624; FStar_Syntax_Syntax.lbtyp = _85_2622; FStar_Syntax_Syntax.lbeff = _85_2620; FStar_Syntax_Syntax.lbdef = _85_2618})::[]), _85_2631, _85_2633, _85_2635) when (FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Syntax_Const.b2t_lid) -> begin
(

let _85_2641 = (new_term_constant_and_tok_from_lid env b2t.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_85_2641) with
| (tname, ttok, env) -> begin
(

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (

let valid_b2t_x = (let _177_2061 = (let _177_2060 = (let _177_2059 = (FStar_SMTEncoding_Term.mkApp (("Prims.b2t"), ((x)::[])))
in (_177_2059)::[])
in (("Valid"), (_177_2060)))
in (FStar_SMTEncoding_Term.mkApp _177_2061))
in (

let decls = (let _177_2069 = (let _177_2068 = (let _177_2067 = (let _177_2066 = (let _177_2065 = (let _177_2064 = (let _177_2063 = (let _177_2062 = (FStar_SMTEncoding_Term.mkApp (("BoxBool_proj_0"), ((x)::[])))
in ((valid_b2t_x), (_177_2062)))
in (FStar_SMTEncoding_Term.mkEq _177_2063))
in ((((valid_b2t_x)::[])::[]), ((xx)::[]), (_177_2064)))
in (FStar_SMTEncoding_Term.mkForall _177_2065))
in ((_177_2066), (Some ("b2t def")), (Some ("b2t_def"))))
in FStar_SMTEncoding_Term.Assume (_177_2067))
in (_177_2068)::[])
in (FStar_SMTEncoding_Term.DeclFun (((tname), ((FStar_SMTEncoding_Term.Term_sort)::[]), (FStar_SMTEncoding_Term.Term_sort), (None))))::_177_2069)
in ((decls), (env))))))
end))
end
| FStar_Syntax_Syntax.Sig_let (_85_2647, _85_2649, _85_2651, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _85_18 -> (match (_85_18) with
| FStar_Syntax_Syntax.Discriminator (_85_2657) -> begin
true
end
| _85_2660 -> begin
false
end)))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let (_85_2662, _85_2664, lids, quals) when ((FStar_All.pipe_right lids (FStar_Util.for_some (fun l -> ((let _177_2072 = (FStar_List.hd l.FStar_Ident.ns)
in _177_2072.FStar_Ident.idText) = "Prims")))) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun _85_19 -> (match (_85_19) with
| FStar_Syntax_Syntax.Inline -> begin
true
end
| _85_2673 -> begin
false
end))))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _85_2679, _85_2681, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _85_20 -> (match (_85_20) with
| FStar_Syntax_Syntax.Projector (_85_2687) -> begin
true
end
| _85_2690 -> begin
false
end)))) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((try_lookup_free_var env l)) with
| Some (_85_2694) -> begin
(([]), (env))
end
| None -> begin
(

let se = FStar_Syntax_Syntax.Sig_declare_typ (((l), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), ((FStar_Ident.range_of_lid l))))
in (encode_sigelt env se))
end)))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _85_2703, _85_2705, quals) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) -> begin
(match ((let _177_2075 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef)
in _177_2075.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, _85_2712) -> begin
(

let body = (FStar_Syntax_Util.mk_reify body)
in (

let tm = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None)))) None lb.FStar_Syntax_Syntax.lbdef.FStar_Syntax_Syntax.pos)
in (

let tm' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env.tcenv tm)
in (

let lb_typ = (

let _85_2720 = (FStar_Syntax_Util.arrow_formals_comp lb.FStar_Syntax_Syntax.lbtyp)
in (match (_85_2720) with
| (formals, comp) -> begin
(

let reified_typ = (FStar_TypeChecker_Util.reify_comp env.tcenv (FStar_Syntax_Util.lcomp_of_comp comp) FStar_Syntax_Syntax.U_unknown)
in (let _177_2076 = (FStar_Syntax_Syntax.mk_Total reified_typ)
in (FStar_Syntax_Util.arrow formals _177_2076)))
end))
in (

let lb = (

let _85_2723 = lb
in {FStar_Syntax_Syntax.lbname = _85_2723.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _85_2723.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lb_typ; FStar_Syntax_Syntax.lbeff = _85_2723.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = tm'})
in (encode_top_level_let env ((false), ((lb)::[])) quals))))))
end
| _85_2727 -> begin
(([]), (env))
end)
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), _85_2732, _85_2734, quals) -> begin
(encode_top_level_let env ((is_rec), (bindings)) quals)
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _85_2740, _85_2742, _85_2744) -> begin
(

let _85_2749 = (encode_signature env ses)
in (match (_85_2749) with
| (g, env) -> begin
(

let _85_2763 = (FStar_All.pipe_right g (FStar_List.partition (fun _85_21 -> (match (_85_21) with
| FStar_SMTEncoding_Term.Assume (_85_2752, Some ("inversion axiom"), _85_2756) -> begin
false
end
| _85_2760 -> begin
true
end))))
in (match (_85_2763) with
| (g', inversions) -> begin
(

let _85_2772 = (FStar_All.pipe_right g' (FStar_List.partition (fun _85_22 -> (match (_85_22) with
| FStar_SMTEncoding_Term.DeclFun (_85_2766) -> begin
true
end
| _85_2769 -> begin
false
end))))
in (match (_85_2772) with
| (decls, rest) -> begin
(((FStar_List.append (FStar_List.append decls rest) inversions)), (env))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, _85_2775, tps, k, _85_2779, datas, quals, _85_2783) -> begin
(

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _85_23 -> (match (_85_23) with
| (FStar_Syntax_Syntax.Logic) | (FStar_Syntax_Syntax.Assumption) -> begin
true
end
| _85_2790 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(

let _85_2802 = c
in (match (_85_2802) with
| (name, args, _85_2797, _85_2799, _85_2801) -> begin
(let _177_2084 = (let _177_2083 = (let _177_2082 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in ((name), (_177_2082), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (_177_2083))
in (_177_2084)::[])
end))
end else begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end)
in (

let inversion_axioms = (fun tapp vars -> if (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _177_2090 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right _177_2090 FStar_Option.isNone))))) then begin
[]
end else begin
(

let _85_2809 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_85_2809) with
| (xxsym, xx) -> begin
(

let _85_2845 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _85_2812 l -> (match (_85_2812) with
| (out, decls) -> begin
(

let _85_2817 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (_85_2817) with
| (_85_2815, data_t) -> begin
(

let _85_2820 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (_85_2820) with
| (args, res) -> begin
(

let indices = (match ((let _177_2093 = (FStar_Syntax_Subst.compress res)
in _177_2093.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_85_2822, indices) -> begin
indices
end
| _85_2827 -> begin
[]
end)
in (

let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env _85_2833 -> (match (_85_2833) with
| (x, _85_2832) -> begin
(let _177_2098 = (let _177_2097 = (let _177_2096 = (mk_term_projector_name l x)
in ((_177_2096), ((xx)::[])))
in (FStar_SMTEncoding_Term.mkApp _177_2097))
in (push_term_var env x _177_2098))
end)) env))
in (

let _85_2837 = (encode_args indices env)
in (match (_85_2837) with
| (indices, decls') -> begin
(

let _85_2838 = if ((FStar_List.length indices) <> (FStar_List.length vars)) then begin
(FStar_All.failwith "Impossible")
end else begin
()
end
in (

let eqs = (let _177_2103 = (FStar_List.map2 (fun v a -> (let _177_2102 = (let _177_2101 = (FStar_SMTEncoding_Term.mkFreeV v)
in ((_177_2101), (a)))
in (FStar_SMTEncoding_Term.mkEq _177_2102))) vars indices)
in (FStar_All.pipe_right _177_2103 FStar_SMTEncoding_Term.mk_and_l))
in (let _177_2108 = (let _177_2107 = (let _177_2106 = (let _177_2105 = (let _177_2104 = (mk_data_tester env l xx)
in ((_177_2104), (eqs)))
in (FStar_SMTEncoding_Term.mkAnd _177_2105))
in ((out), (_177_2106)))
in (FStar_SMTEncoding_Term.mkOr _177_2107))
in ((_177_2108), ((FStar_List.append decls decls'))))))
end))))
end))
end))
end)) ((FStar_SMTEncoding_Term.mkFalse), ([]))))
in (match (_85_2845) with
| (data_ax, decls) -> begin
(

let _85_2848 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_85_2848) with
| (ffsym, ff) -> begin
(

let fuel_guarded_inversion = (

let xx_has_type_sfuel = if ((FStar_List.length datas) > 1) then begin
(let _177_2109 = (FStar_SMTEncoding_Term.mkApp (("SFuel"), ((ff)::[])))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel _177_2109 xx tapp))
end else begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end
in (let _177_2116 = (let _177_2115 = (let _177_2112 = (let _177_2111 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (let _177_2110 = (FStar_SMTEncoding_Term.mkImp ((xx_has_type_sfuel), (data_ax)))
in ((((xx_has_type_sfuel)::[])::[]), (_177_2111), (_177_2110))))
in (FStar_SMTEncoding_Term.mkForall _177_2112))
in (let _177_2114 = (let _177_2113 = (varops.fresh (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str))
in Some (_177_2113))
in ((_177_2115), (Some ("inversion axiom")), (_177_2114))))
in FStar_SMTEncoding_Term.Assume (_177_2116)))
in (

let pattern_guarded_inversion = if ((contains_name env "Prims.inversion") && ((FStar_List.length datas) > 1)) then begin
(

let xx_has_type_fuel = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let pattern_guard = (FStar_SMTEncoding_Term.mkApp (("Prims.inversion"), ((tapp)::[])))
in (let _177_2124 = (let _177_2123 = (let _177_2122 = (let _177_2119 = (let _177_2118 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (let _177_2117 = (FStar_SMTEncoding_Term.mkImp ((xx_has_type_fuel), (data_ax)))
in ((((xx_has_type_fuel)::(pattern_guard)::[])::[]), (_177_2118), (_177_2117))))
in (FStar_SMTEncoding_Term.mkForall _177_2119))
in (let _177_2121 = (let _177_2120 = (varops.fresh (Prims.strcat "pattern_guarded_inversion_" t.FStar_Ident.str))
in Some (_177_2120))
in ((_177_2122), (Some ("inversion axiom")), (_177_2121))))
in FStar_SMTEncoding_Term.Assume (_177_2123))
in (_177_2124)::[])))
end else begin
[]
end
in (FStar_List.append (FStar_List.append decls ((fuel_guarded_inversion)::[])) pattern_guarded_inversion)))
end))
end))
end))
end)
in (

let _85_2862 = (match ((let _177_2125 = (FStar_Syntax_Subst.compress k)
in _177_2125.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
(((FStar_List.append tps formals)), ((FStar_Syntax_Util.comp_result kres)))
end
| _85_2859 -> begin
((tps), (k))
end)
in (match (_85_2862) with
| (formals, res) -> begin
(

let _85_2865 = (FStar_Syntax_Subst.open_term formals res)
in (match (_85_2865) with
| (formals, res) -> begin
(

let _85_2872 = (encode_binders None formals env)
in (match (_85_2872) with
| (vars, guards, env', binder_decls, _85_2871) -> begin
(

let _85_2876 = (new_term_constant_and_tok_from_lid env t)
in (match (_85_2876) with
| (tname, ttok, env) -> begin
(

let ttok_tm = (FStar_SMTEncoding_Term.mkApp ((ttok), ([])))
in (

let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (

let tapp = (let _177_2127 = (let _177_2126 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in ((tname), (_177_2126)))
in (FStar_SMTEncoding_Term.mkApp _177_2127))
in (

let _85_2897 = (

let tname_decl = (let _177_2131 = (let _177_2130 = (FStar_All.pipe_right vars (FStar_List.map (fun _85_2882 -> (match (_85_2882) with
| (n, s) -> begin
(((Prims.strcat tname n)), (s))
end))))
in (let _177_2129 = (varops.next_id ())
in ((tname), (_177_2130), (FStar_SMTEncoding_Term.Term_sort), (_177_2129), (false))))
in (constructor_or_logic_type_decl _177_2131))
in (

let _85_2894 = (match (vars) with
| [] -> begin
(let _177_2135 = (let _177_2134 = (let _177_2133 = (FStar_SMTEncoding_Term.mkApp ((tname), ([])))
in (FStar_All.pipe_left (fun _177_2132 -> Some (_177_2132)) _177_2133))
in (push_free_var env t tname _177_2134))
in (([]), (_177_2135)))
end
| _85_2886 -> begin
(

let ttok_decl = FStar_SMTEncoding_Term.DeclFun (((ttok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("token"))))
in (

let ttok_fresh = (let _177_2136 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ttok), (FStar_SMTEncoding_Term.Term_sort)) _177_2136))
in (

let ttok_app = (mk_Apply ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (let _177_2140 = (let _177_2139 = (let _177_2138 = (let _177_2137 = (FStar_SMTEncoding_Term.mkEq ((ttok_app), (tapp)))
in ((pats), (None), (vars), (_177_2137)))
in (FStar_SMTEncoding_Term.mkForall' _177_2138))
in ((_177_2139), (Some ("name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" ttok)))))
in FStar_SMTEncoding_Term.Assume (_177_2140))
in (((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[]), (env)))))))
end)
in (match (_85_2894) with
| (tok_decls, env) -> begin
(((FStar_List.append tname_decl tok_decls)), (env))
end)))
in (match (_85_2897) with
| (decls, env) -> begin
(

let kindingAx = (

let _85_2900 = (encode_term_pred None res env' tapp)
in (match (_85_2900) with
| (k, decls) -> begin
(

let karr = if ((FStar_List.length formals) > 0) then begin
(let _177_2144 = (let _177_2143 = (let _177_2142 = (let _177_2141 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _177_2141))
in ((_177_2142), (Some ("kinding")), (Some ((Prims.strcat "pre_kinding_" ttok)))))
in FStar_SMTEncoding_Term.Assume (_177_2143))
in (_177_2144)::[])
end else begin
[]
end
in (let _177_2150 = (let _177_2149 = (let _177_2148 = (let _177_2147 = (let _177_2146 = (let _177_2145 = (FStar_SMTEncoding_Term.mkImp ((guard), (k)))
in ((((tapp)::[])::[]), (vars), (_177_2145)))
in (FStar_SMTEncoding_Term.mkForall _177_2146))
in ((_177_2147), (None), (Some ((Prims.strcat "kinding_" ttok)))))
in FStar_SMTEncoding_Term.Assume (_177_2148))
in (_177_2149)::[])
in (FStar_List.append (FStar_List.append decls karr) _177_2150)))
end))
in (

let aux = (let _177_2154 = (let _177_2151 = (inversion_axioms tapp vars)
in (FStar_List.append kindingAx _177_2151))
in (let _177_2153 = (let _177_2152 = (pretype_axiom tapp vars)
in (_177_2152)::[])
in (FStar_List.append _177_2154 _177_2153)))
in (

let g = (FStar_List.append (FStar_List.append decls binder_decls) aux)
in ((g), (env)))))
end)))))
end))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, _85_2907, _85_2909, _85_2911, _85_2913, _85_2915, _85_2917, _85_2919) when (FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_datacon (d, _85_2924, t, _85_2927, n_tps, quals, _85_2931, drange) -> begin
(

let _85_2938 = (new_term_constant_and_tok_from_lid env d)
in (match (_85_2938) with
| (ddconstrsym, ddtok, env) -> begin
(

let ddtok_tm = (FStar_SMTEncoding_Term.mkApp ((ddtok), ([])))
in (

let _85_2942 = (FStar_Syntax_Util.arrow_formals t)
in (match (_85_2942) with
| (formals, t_res) -> begin
(

let _85_2945 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_85_2945) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_SMTEncoding_Term.mkApp (("SFuel"), ((fuel_tm)::[])))
in (

let _85_2952 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_85_2952) with
| (vars, guards, env', binder_decls, names) -> begin
(

let projectors = (FStar_All.pipe_right names (FStar_List.map (fun x -> (let _177_2156 = (mk_term_projector_name d x)
in ((_177_2156), (FStar_SMTEncoding_Term.Term_sort))))))
in (

let datacons = (let _177_2158 = (let _177_2157 = (varops.next_id ())
in ((ddconstrsym), (projectors), (FStar_SMTEncoding_Term.Term_sort), (_177_2157), (true)))
in (FStar_All.pipe_right _177_2158 FStar_SMTEncoding_Term.constructor_to_decl))
in (

let app = (mk_Apply ddtok_tm vars)
in (

let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Term.mkApp ((ddconstrsym), (xvars)))
in (

let _85_2962 = (encode_term_pred None t env ddtok_tm)
in (match (_85_2962) with
| (tok_typing, decls3) -> begin
(

let _85_2969 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_85_2969) with
| (vars', guards', env'', decls_formals, _85_2968) -> begin
(

let _85_2974 = (

let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars')
in (

let dapp = (FStar_SMTEncoding_Term.mkApp ((ddconstrsym), (xvars)))
in (encode_term_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_85_2974) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_SMTEncoding_Term.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _85_2978 -> begin
(let _177_2160 = (let _177_2159 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ddtok), (FStar_SMTEncoding_Term.Term_sort)) _177_2159))
in (_177_2160)::[])
end)
in (

let encode_elim = (fun _85_2981 -> (match (()) with
| () -> begin
(

let _85_2984 = (FStar_Syntax_Util.head_and_args t_res)
in (match (_85_2984) with
| (head, args) -> begin
(match ((let _177_2163 = (FStar_Syntax_Subst.compress head)
in _177_2163.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let _85_3002 = (encode_args args env')
in (match (_85_3002) with
| (encoded_args, arg_decls) -> begin
(

let _85_3017 = (FStar_List.fold_left (fun _85_3006 arg -> (match (_85_3006) with
| (env, arg_vars, eqns) -> begin
(

let _85_3012 = (let _177_2166 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in (gen_term_var env _177_2166))
in (match (_85_3012) with
| (_85_3009, xv, env) -> begin
(let _177_2168 = (let _177_2167 = (FStar_SMTEncoding_Term.mkEq ((arg), (xv)))
in (_177_2167)::eqns)
in ((env), ((xv)::arg_vars), (_177_2168)))
end))
end)) ((env'), ([]), ([])) encoded_args)
in (match (_85_3017) with
| (_85_3014, arg_vars, eqns) -> begin
(

let arg_vars = (FStar_List.rev arg_vars)
in (

let ty = (FStar_SMTEncoding_Term.mkApp ((encoded_head), (arg_vars)))
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Term.mkApp ((ddconstrsym), (xvars)))
in (

let ty_pred = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp ty)
in (

let arg_binders = (FStar_List.map FStar_SMTEncoding_Term.fv_of_term arg_vars)
in (

let typing_inversion = (let _177_2175 = (let _177_2174 = (let _177_2173 = (let _177_2172 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (let _177_2171 = (let _177_2170 = (let _177_2169 = (FStar_SMTEncoding_Term.mk_and_l (FStar_List.append eqns guards))
in ((ty_pred), (_177_2169)))
in (FStar_SMTEncoding_Term.mkImp _177_2170))
in ((((ty_pred)::[])::[]), (_177_2172), (_177_2171))))
in (FStar_SMTEncoding_Term.mkForall _177_2173))
in ((_177_2174), (Some ("data constructor typing elim")), (Some ((Prims.strcat "data_elim_" ddconstrsym)))))
in FStar_SMTEncoding_Term.Assume (_177_2175))
in (

let subterm_ordering = if (FStar_Ident.lid_equals d FStar_Syntax_Const.lextop_lid) then begin
(

let x = (let _177_2176 = (varops.fresh "x")
in ((_177_2176), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Term.mkFreeV x)
in (let _177_2188 = (let _177_2187 = (let _177_2184 = (let _177_2183 = (let _177_2178 = (let _177_2177 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in (_177_2177)::[])
in (_177_2178)::[])
in (let _177_2182 = (let _177_2181 = (let _177_2180 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (let _177_2179 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in ((_177_2180), (_177_2179))))
in (FStar_SMTEncoding_Term.mkImp _177_2181))
in ((_177_2183), ((x)::[]), (_177_2182))))
in (FStar_SMTEncoding_Term.mkForall _177_2184))
in (let _177_2186 = (let _177_2185 = (varops.fresh "lextop")
in Some (_177_2185))
in ((_177_2187), (Some ("lextop is top")), (_177_2186))))
in FStar_SMTEncoding_Term.Assume (_177_2188))))
end else begin
(

let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
[]
end
| FStar_SMTEncoding_Term.Term_sort -> begin
(let _177_2191 = (let _177_2190 = (FStar_SMTEncoding_Term.mkFreeV v)
in (FStar_SMTEncoding_Term.mk_Precedes _177_2190 dapp))
in (_177_2191)::[])
end
| _85_3031 -> begin
(FStar_All.failwith "unexpected sort")
end))))
in (let _177_2198 = (let _177_2197 = (let _177_2196 = (let _177_2195 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (let _177_2194 = (let _177_2193 = (let _177_2192 = (FStar_SMTEncoding_Term.mk_and_l prec)
in ((ty_pred), (_177_2192)))
in (FStar_SMTEncoding_Term.mkImp _177_2193))
in ((((ty_pred)::[])::[]), (_177_2195), (_177_2194))))
in (FStar_SMTEncoding_Term.mkForall _177_2196))
in ((_177_2197), (Some ("subterm ordering")), (Some ((Prims.strcat "subterm_ordering_" ddconstrsym)))))
in FStar_SMTEncoding_Term.Assume (_177_2198)))
end
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end))
end)))
end
| _85_3035 -> begin
(

let _85_3036 = (let _177_2201 = (let _177_2200 = (FStar_Syntax_Print.lid_to_string d)
in (let _177_2199 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _177_2200 _177_2199)))
in (FStar_TypeChecker_Errors.warn drange _177_2201))
in (([]), ([])))
end)
end))
end))
in (

let _85_3040 = (encode_elim ())
in (match (_85_3040) with
| (decls2, elim) -> begin
(

let g = (let _177_2226 = (let _177_2225 = (let _177_2210 = (let _177_2209 = (let _177_2208 = (let _177_2207 = (let _177_2206 = (let _177_2205 = (let _177_2204 = (let _177_2203 = (let _177_2202 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" _177_2202))
in Some (_177_2203))
in ((ddtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (_177_2204)))
in FStar_SMTEncoding_Term.DeclFun (_177_2205))
in (_177_2206)::[])
in (FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) decls3) _177_2207))
in (FStar_List.append _177_2208 proxy_fresh))
in (FStar_List.append _177_2209 decls_formals))
in (FStar_List.append _177_2210 decls_pred))
in (let _177_2224 = (let _177_2223 = (let _177_2222 = (let _177_2214 = (let _177_2213 = (let _177_2212 = (let _177_2211 = (FStar_SMTEncoding_Term.mkEq ((app), (dapp)))
in ((((app)::[])::[]), (vars), (_177_2211)))
in (FStar_SMTEncoding_Term.mkForall _177_2212))
in ((_177_2213), (Some ("equality for proxy")), (Some ((Prims.strcat "equality_tok_" ddtok)))))
in FStar_SMTEncoding_Term.Assume (_177_2214))
in (let _177_2221 = (let _177_2220 = (let _177_2219 = (let _177_2218 = (let _177_2217 = (let _177_2216 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) vars')
in (let _177_2215 = (FStar_SMTEncoding_Term.mkImp ((guard'), (ty_pred')))
in ((((ty_pred')::[])::[]), (_177_2216), (_177_2215))))
in (FStar_SMTEncoding_Term.mkForall _177_2217))
in ((_177_2218), (Some ("data constructor typing intro")), (Some ((Prims.strcat "data_typing_intro_" ddtok)))))
in FStar_SMTEncoding_Term.Assume (_177_2219))
in (_177_2220)::[])
in (_177_2222)::_177_2221))
in (FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("typing for data constructor proxy")), (Some ((Prims.strcat "typing_tok_" ddtok))))))::_177_2223)
in (FStar_List.append _177_2225 _177_2224)))
in (FStar_List.append _177_2226 elim))
in (((FStar_List.append datacons g)), (env)))
end)))))
end))
end))
end))))))))
end)))
end))
end)))
end))
end)))
and encode_signature : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _85_3046 se -> (match (_85_3046) with
| (g, env) -> begin
(

let _85_3050 = (encode_sigelt env se)
in (match (_85_3050) with
| (g', env) -> begin
(((FStar_List.append g g')), (env))
end))
end)) (([]), (env)))))


let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings -> (

let encode_binding = (fun b _85_3057 -> (match (_85_3057) with
| (decls, env) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (_85_3059) -> begin
(([]), (env))
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(

let _85_3066 = (new_term_constant env x)
in (match (_85_3066) with
| (xxsym, xx, env') -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (

let _85_3068 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _177_2241 = (FStar_Syntax_Print.bv_to_string x)
in (let _177_2240 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _177_2239 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" _177_2241 _177_2240 _177_2239))))
end else begin
()
end
in (

let _85_3072 = (encode_term_pred None t1 env xx)
in (match (_85_3072) with
| (t, decls') -> begin
(

let caption = if (FStar_Options.log_queries ()) then begin
(let _177_2245 = (let _177_2244 = (FStar_Syntax_Print.bv_to_string x)
in (let _177_2243 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _177_2242 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _177_2244 _177_2243 _177_2242))))
in Some (_177_2245))
end else begin
None
end
in (

let ax = (

let a_name = Some ((Prims.strcat "binder_" xxsym))
in FStar_SMTEncoding_Term.Assume (((t), (a_name), (a_name))))
in (

let g = (FStar_List.append (FStar_List.append ((FStar_SMTEncoding_Term.DeclFun (((xxsym), ([]), (FStar_SMTEncoding_Term.Term_sort), (caption))))::[]) decls') ((ax)::[]))
in (((FStar_List.append decls g)), (env')))))
end))))
end))
end
| FStar_TypeChecker_Env.Binding_lid (x, (_85_3079, t)) -> begin
(

let t_norm = (whnf env t)
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant None)
in (

let _85_3088 = (encode_free_var env fv t t_norm [])
in (match (_85_3088) with
| (g, env') -> begin
(((FStar_List.append decls g)), (env'))
end))))
end
| (FStar_TypeChecker_Env.Binding_sig_inst (_, se, _)) | (FStar_TypeChecker_Env.Binding_sig (_, se)) -> begin
(

let _85_3102 = (encode_sigelt env se)
in (match (_85_3102) with
| (g, env') -> begin
(((FStar_List.append decls g)), (env'))
end))
end)
end))
in (FStar_List.fold_right encode_binding bindings (([]), (env)))))


let encode_labels = (fun labs -> (

let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _85_3109 -> (match (_85_3109) with
| (l, _85_3106, _85_3108) -> begin
FStar_SMTEncoding_Term.DeclFun ((((Prims.fst l)), ([]), (FStar_SMTEncoding_Term.Bool_sort), (None)))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _85_3116 -> (match (_85_3116) with
| (l, _85_3113, _85_3115) -> begin
(let _177_2253 = (FStar_All.pipe_left (fun _177_2249 -> FStar_SMTEncoding_Term.Echo (_177_2249)) (Prims.fst l))
in (let _177_2252 = (let _177_2251 = (let _177_2250 = (FStar_SMTEncoding_Term.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (_177_2250))
in (_177_2251)::[])
in (_177_2253)::_177_2252))
end))))
in ((prefix), (suffix)))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (let _177_2258 = (let _177_2257 = (let _177_2256 = (FStar_Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _177_2256; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_177_2257)::[])
in (FStar_ST.op_Colon_Equals last_env _177_2258)))


let get_env : FStar_TypeChecker_Env.env  ->  env_t = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "No env; call init first!")
end
| (e)::_85_3122 -> begin
(

let _85_3125 = e
in {bindings = _85_3125.bindings; depth = _85_3125.depth; tcenv = tcenv; warn = _85_3125.warn; cache = _85_3125.cache; nolabels = _85_3125.nolabels; use_zfuel_name = _85_3125.use_zfuel_name; encode_non_total_function_typ = _85_3125.encode_non_total_function_typ})
end))


let set_env : env_t  ->  Prims.unit = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| (_85_3131)::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))


let push_env : Prims.unit  ->  Prims.unit = (fun _85_3133 -> (match (()) with
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

let _85_3139 = hd
in {bindings = _85_3139.bindings; depth = _85_3139.depth; tcenv = _85_3139.tcenv; warn = _85_3139.warn; cache = refs; nolabels = _85_3139.nolabels; use_zfuel_name = _85_3139.use_zfuel_name; encode_non_total_function_typ = _85_3139.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))


let pop_env : Prims.unit  ->  Prims.unit = (fun _85_3142 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Popping an empty stack")
end
| (_85_3146)::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))


let mark_env : Prims.unit  ->  Prims.unit = (fun _85_3148 -> (match (()) with
| () -> begin
(push_env ())
end))


let reset_mark_env : Prims.unit  ->  Prims.unit = (fun _85_3149 -> (match (()) with
| () -> begin
(pop_env ())
end))


let commit_mark_env : Prims.unit  ->  Prims.unit = (fun _85_3150 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| (hd)::(_85_3153)::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _85_3158 -> begin
(FStar_All.failwith "Impossible")
end)
end))


let init : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (

let _85_3160 = (init_env tcenv)
in (

let _85_3162 = (FStar_SMTEncoding_Z3.init ())
in (FStar_SMTEncoding_Z3.giveZ3 ((FStar_SMTEncoding_Term.DefPrelude)::[])))))


let push : Prims.string  ->  Prims.unit = (fun msg -> (

let _85_3165 = (push_env ())
in (

let _85_3167 = (varops.push ())
in (FStar_SMTEncoding_Z3.push msg))))


let pop : Prims.string  ->  Prims.unit = (fun msg -> (

let _85_3170 = (let _177_2279 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _177_2279))
in (

let _85_3172 = (varops.pop ())
in (FStar_SMTEncoding_Z3.pop msg))))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _85_3175 = (mark_env ())
in (

let _85_3177 = (varops.mark ())
in (FStar_SMTEncoding_Z3.mark msg))))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _85_3180 = (reset_mark_env ())
in (

let _85_3182 = (varops.reset_mark ())
in (FStar_SMTEncoding_Z3.reset_mark msg))))


let commit_mark = (fun msg -> (

let _85_3185 = (commit_mark_env ())
in (

let _85_3187 = (varops.commit_mark ())
in (FStar_SMTEncoding_Z3.commit_mark msg))))


let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (

let caption = (fun decls -> if (FStar_Options.log_queries ()) then begin
(let _177_2295 = (let _177_2294 = (let _177_2293 = (let _177_2292 = (let _177_2291 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _177_2291 (FStar_List.map FStar_Syntax_Print.lid_to_string)))
in (FStar_All.pipe_right _177_2292 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " _177_2293))
in FStar_SMTEncoding_Term.Caption (_177_2294))
in (_177_2295)::decls)
end else begin
decls
end)
in (

let env = (get_env tcenv)
in (

let _85_3196 = (encode_sigelt env se)
in (match (_85_3196) with
| (decls, env) -> begin
(

let _85_3197 = (set_env env)
in (let _177_2296 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 _177_2296)))
end)))))


let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let _85_3202 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(let _177_2301 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name _177_2301))
end else begin
()
end
in (

let env = (get_env tcenv)
in (

let _85_3209 = (encode_signature (

let _85_3205 = env
in {bindings = _85_3205.bindings; depth = _85_3205.depth; tcenv = _85_3205.tcenv; warn = false; cache = _85_3205.cache; nolabels = _85_3205.nolabels; use_zfuel_name = _85_3205.use_zfuel_name; encode_non_total_function_typ = _85_3205.encode_non_total_function_typ}) modul.FStar_Syntax_Syntax.exports)
in (match (_85_3209) with
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

let _85_3215 = (set_env (

let _85_3213 = env
in {bindings = _85_3213.bindings; depth = _85_3213.depth; tcenv = _85_3213.tcenv; warn = true; cache = _85_3213.cache; nolabels = _85_3213.nolabels; use_zfuel_name = _85_3213.use_zfuel_name; encode_non_total_function_typ = _85_3213.encode_non_total_function_typ}))
in (

let _85_3217 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
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

let _85_3246 = (

let rec aux = (fun bindings -> (match (bindings) with
| (FStar_TypeChecker_Env.Binding_var (x))::rest -> begin
(

let _85_3235 = (aux rest)
in (match (_85_3235) with
| (out, rest) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (let _177_2323 = (let _177_2322 = (FStar_Syntax_Syntax.mk_binder (

let _85_3237 = x
in {FStar_Syntax_Syntax.ppname = _85_3237.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _85_3237.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_177_2322)::out)
in ((_177_2323), (rest))))
end))
end
| _85_3240 -> begin
(([]), (bindings))
end))
in (

let _85_3243 = (aux bindings)
in (match (_85_3243) with
| (closing, bindings) -> begin
(let _177_2324 = (FStar_Syntax_Util.close_forall (FStar_List.rev closing) q)
in ((_177_2324), (bindings)))
end)))
in (match (_85_3246) with
| (q, bindings) -> begin
(

let _85_3255 = (let _177_2326 = (FStar_List.filter (fun _85_24 -> (match (_85_24) with
| FStar_TypeChecker_Env.Binding_sig (_85_3249) -> begin
false
end
| _85_3252 -> begin
true
end)) bindings)
in (encode_env_bindings env _177_2326))
in (match (_85_3255) with
| (env_decls, env) -> begin
(

let _85_3256 = if (((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTQuery")))) then begin
(let _177_2327 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" _177_2327))
end else begin
()
end
in (

let _85_3260 = (encode_formula q env)
in (match (_85_3260) with
| (phi, qdecls) -> begin
(

let _85_3265 = (let _177_2328 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg _177_2328 phi))
in (match (_85_3265) with
| (phi, labels, _85_3264) -> begin
(

let _85_3268 = (encode_labels labels)
in (match (_85_3268) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append (FStar_List.append env_decls label_prefix) qdecls)
in (

let qry = (let _177_2332 = (let _177_2331 = (FStar_SMTEncoding_Term.mkNot phi)
in (let _177_2330 = (let _177_2329 = (varops.fresh "@query")
in Some (_177_2329))
in ((_177_2331), (Some ("query")), (_177_2330))))
in FStar_SMTEncoding_Term.Assume (_177_2332))
in (

let suffix = (FStar_List.append label_suffix ((FStar_SMTEncoding_Term.Echo ("Done!"))::[]))
in ((query_prelude), (labels), (qry), (suffix)))))
end))
end))
end)))
end))
end)))))


let is_trivial : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun tcenv q -> (

let env = (get_env tcenv)
in (

let _85_3275 = (push "query")
in (

let _85_3280 = (encode_formula q env)
in (match (_85_3280) with
| (f, _85_3279) -> begin
(

let _85_3281 = (pop "query")
in (match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _85_3285) -> begin
true
end
| _85_3289 -> begin
false
end))
end)))))




