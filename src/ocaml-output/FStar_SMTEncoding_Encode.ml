
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
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; mark : Prims.unit  ->  Prims.unit; reset_mark : Prims.unit  ->  Prims.unit; commit_mark : Prims.unit  ->  Prims.unit; new_var : FStar_Ident.ident  ->  Prims.int  ->  Prims.string; new_fvar : FStar_Ident.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_SMTEncoding_Term.term; next_id : Prims.unit  ->  Prims.int; mk_unique : Prims.string  ->  Prims.string}


let is_Mkvarops_t : varops_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkvarops_t"))))


let varops : varops_t = (

let initial_ctr = 100
in (

let ctr = (FStar_Util.mk_ref initial_ctr)
in (

let new_scope = (fun _85_98 -> (match (()) with
| () -> begin
(let _177_162 = (FStar_Util.smap_create 100)
in (let _177_161 = (FStar_Util.smap_create 100)
in ((_177_162), (_177_161))))
end))
in (

let scopes = (let _177_164 = (let _177_163 = (new_scope ())
in (_177_163)::[])
in (FStar_Util.mk_ref _177_164))
in (

let mk_unique = (fun y -> (

let y = (escape y)
in (

let y = (match ((let _177_168 = (FStar_ST.read scopes)
in (FStar_Util.find_map _177_168 (fun _85_106 -> (match (_85_106) with
| (names, _85_105) -> begin
(FStar_Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_85_109) -> begin
(

let _85_111 = (FStar_Util.incr ctr)
in (let _177_171 = (let _177_170 = (let _177_169 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _177_169))
in (Prims.strcat "__" _177_170))
in (Prims.strcat y _177_171)))
end)
in (

let top_scope = (let _177_173 = (let _177_172 = (FStar_ST.read scopes)
in (FStar_List.hd _177_172))
in (FStar_All.pipe_left Prims.fst _177_173))
in (

let _85_115 = (FStar_Util.smap_add top_scope y true)
in y)))))
in (

let new_var = (fun pp rn -> (let _177_180 = (let _177_179 = (let _177_178 = (FStar_Util.string_of_int rn)
in (Prims.strcat "__" _177_178))
in (Prims.strcat pp.FStar_Ident.idText _177_179))
in (FStar_All.pipe_left mk_unique _177_180)))
in (

let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (

let next_id = (fun _85_123 -> (match (()) with
| () -> begin
(

let _85_124 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end))
in (

let fresh = (fun pfx -> (let _177_188 = (let _177_187 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _177_187))
in (FStar_Util.format2 "%s_%s" pfx _177_188)))
in (

let string_const = (fun s -> (match ((let _177_192 = (FStar_ST.read scopes)
in (FStar_Util.find_map _177_192 (fun _85_133 -> (match (_85_133) with
| (_85_131, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))) with
| Some (f) -> begin
f
end
| None -> begin
(

let id = (next_id ())
in (

let f = (let _177_193 = (FStar_SMTEncoding_Term.mk_String_const id)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString _177_193))
in (

let top_scope = (let _177_195 = (let _177_194 = (FStar_ST.read scopes)
in (FStar_List.hd _177_194))
in (FStar_All.pipe_left Prims.snd _177_195))
in (

let _85_140 = (FStar_Util.smap_add top_scope s f)
in f))))
end))
in (

let push = (fun _85_143 -> (match (()) with
| () -> begin
(let _177_200 = (let _177_199 = (new_scope ())
in (let _177_198 = (FStar_ST.read scopes)
in (_177_199)::_177_198))
in (FStar_ST.op_Colon_Equals scopes _177_200))
end))
in (

let pop = (fun _85_145 -> (match (()) with
| () -> begin
(let _177_204 = (let _177_203 = (FStar_ST.read scopes)
in (FStar_List.tl _177_203))
in (FStar_ST.op_Colon_Equals scopes _177_204))
end))
in (

let mark = (fun _85_147 -> (match (()) with
| () -> begin
(push ())
end))
in (

let reset_mark = (fun _85_149 -> (match (()) with
| () -> begin
(pop ())
end))
in (

let commit_mark = (fun _85_151 -> (match (()) with
| () -> begin
(match ((FStar_ST.read scopes)) with
| ((hd1, hd2))::((next1, next2))::tl -> begin
(

let _85_164 = (FStar_Util.smap_fold hd1 (fun key value v -> (FStar_Util.smap_add next1 key value)) ())
in (

let _85_169 = (FStar_Util.smap_fold hd2 (fun key value v -> (FStar_Util.smap_add next2 key value)) ())
in (FStar_ST.op_Colon_Equals scopes ((((next1), (next2)))::tl))))
end
| _85_172 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id; mk_unique = mk_unique})))))))))))))))


let unmangle : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv = (fun x -> (

let _85_174 = x
in (let _177_219 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _177_219; FStar_Syntax_Syntax.index = _85_174.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _85_174.FStar_Syntax_Syntax.sort})))


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
| Binding_var (_85_178) -> begin
_85_178
end))


let ___Binding_fvar____0 = (fun projectee -> (match (projectee) with
| Binding_fvar (_85_181) -> begin
_85_181
end))


let binder_of_eithervar = (fun v -> ((v), (None)))


type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_TypeChecker_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_SMTEncoding_Term.sort Prims.list * FStar_SMTEncoding_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}


let is_Mkenv_t : env_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_t"))))


let print_env : env_t  ->  Prims.string = (fun e -> (let _177_277 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun _85_2 -> (match (_85_2) with
| Binding_var (x, _85_196) -> begin
(FStar_Syntax_Print.bv_to_string x)
end
| Binding_fvar (l, _85_201, _85_203, _85_205) -> begin
(FStar_Syntax_Print.lid_to_string l)
end))))
in (FStar_All.pipe_right _177_277 (FStar_String.concat ", "))))


let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))


let caption_t : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.string Prims.option = (fun env t -> if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _177_287 = (FStar_Syntax_Print.term_to_string t)
in Some (_177_287))
end else begin
None
end)


let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (

let xsym = (varops.fresh x)
in (let _177_292 = (FStar_SMTEncoding_Term.mkFreeV ((xsym), (s)))
in ((xsym), (_177_292)))))


let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (let _177_297 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _177_297))
in (

let y = (FStar_SMTEncoding_Term.mkFreeV ((ysym), (FStar_SMTEncoding_Term.Term_sort)))
in ((ysym), (y), ((

let _85_219 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = (env.depth + 1); tcenv = _85_219.tcenv; warn = _85_219.warn; cache = _85_219.cache; nolabels = _85_219.nolabels; use_zfuel_name = _85_219.use_zfuel_name; encode_non_total_function_typ = _85_219.encode_non_total_function_typ}))))))


let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (

let y = (FStar_SMTEncoding_Term.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let _85_225 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = _85_225.depth; tcenv = _85_225.tcenv; warn = _85_225.warn; cache = _85_225.cache; nolabels = _85_225.nolabels; use_zfuel_name = _85_225.use_zfuel_name; encode_non_total_function_typ = _85_225.encode_non_total_function_typ}))))))


let new_term_constant_from_string : env_t  ->  FStar_Syntax_Syntax.bv  ->  Prims.string  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x str -> (

let ysym = (varops.mk_unique str)
in (

let y = (FStar_SMTEncoding_Term.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let _85_232 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = _85_232.depth; tcenv = _85_232.tcenv; warn = _85_232.warn; cache = _85_232.cache; nolabels = _85_232.nolabels; use_zfuel_name = _85_232.use_zfuel_name; encode_non_total_function_typ = _85_232.encode_non_total_function_typ}))))))


let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (

let _85_237 = env
in {bindings = (Binding_var (((x), (t))))::env.bindings; depth = _85_237.depth; tcenv = _85_237.tcenv; warn = _85_237.warn; cache = _85_237.cache; nolabels = _85_237.nolabels; use_zfuel_name = _85_237.use_zfuel_name; encode_non_total_function_typ = _85_237.encode_non_total_function_typ}))


let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let aux = (fun a' -> (lookup_binding env (fun _85_3 -> (match (_85_3) with
| Binding_var (b, t) when (FStar_Syntax_Syntax.bv_eq b a') -> begin
Some (((b), (t)))
end
| _85_249 -> begin
None
end))))
in (match ((aux a)) with
| None -> begin
(

let a = (unmangle a)
in (match ((aux a)) with
| None -> begin
(let _177_322 = (let _177_321 = (FStar_Syntax_Print.bv_to_string a)
in (FStar_Util.format1 "Bound term variable not found (after unmangling): %s" _177_321))
in (FStar_All.failwith _177_322))
end
| Some (b, t) -> begin
t
end))
end
| Some (b, t) -> begin
t
end)))


let new_term_constant_and_tok_from_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * Prims.string * env_t) = (fun env x -> (

let fname = (varops.new_fvar x)
in (

let ftok = (Prims.strcat fname "@tok")
in (let _177_333 = (

let _85_265 = env
in (let _177_332 = (let _177_331 = (let _177_330 = (let _177_329 = (let _177_328 = (FStar_SMTEncoding_Term.mkApp ((ftok), ([])))
in (FStar_All.pipe_left (fun _177_327 -> Some (_177_327)) _177_328))
in ((x), (fname), (_177_329), (None)))
in Binding_fvar (_177_330))
in (_177_331)::env.bindings)
in {bindings = _177_332; depth = _85_265.depth; tcenv = _85_265.tcenv; warn = _85_265.warn; cache = _85_265.cache; nolabels = _85_265.nolabels; use_zfuel_name = _85_265.use_zfuel_name; encode_non_total_function_typ = _85_265.encode_non_total_function_typ}))
in ((fname), (ftok), (_177_333))))))


let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun _85_4 -> (match (_85_4) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some (((t1), (t2), (t3)))
end
| _85_277 -> begin
None
end))))


let contains_name : env_t  ->  Prims.string  ->  Prims.bool = (fun env s -> (let _177_344 = (lookup_binding env (fun _85_5 -> (match (_85_5) with
| Binding_fvar (b, t1, t2, t3) when (b.FStar_Ident.str = s) -> begin
Some (())
end
| _85_288 -> begin
None
end)))
in (FStar_All.pipe_right _177_344 FStar_Option.isSome)))


let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _177_350 = (let _177_349 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" _177_349))
in (FStar_All.failwith _177_350))
end
| Some (s) -> begin
s
end))


let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (

let _85_298 = env
in {bindings = (Binding_fvar (((x), (fname), (ftok), (None))))::env.bindings; depth = _85_298.depth; tcenv = _85_298.tcenv; warn = _85_298.warn; cache = _85_298.cache; nolabels = _85_298.nolabels; use_zfuel_name = _85_298.use_zfuel_name; encode_non_total_function_typ = _85_298.encode_non_total_function_typ}))


let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (

let _85_307 = (lookup_lid env x)
in (match (_85_307) with
| (t1, t2, _85_306) -> begin
(

let t3 = (let _177_367 = (let _177_366 = (let _177_365 = (FStar_SMTEncoding_Term.mkApp (("ZFuel"), ([])))
in (_177_365)::[])
in ((f), (_177_366)))
in (FStar_SMTEncoding_Term.mkApp _177_367))
in (

let _85_309 = env
in {bindings = (Binding_fvar (((x), (t1), (t2), (Some (t3)))))::env.bindings; depth = _85_309.depth; tcenv = _85_309.tcenv; warn = _85_309.warn; cache = _85_309.cache; nolabels = _85_309.nolabels; use_zfuel_name = _85_309.use_zfuel_name; encode_non_total_function_typ = _85_309.encode_non_total_function_typ}))
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
| _85_322 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (_85_326, (fuel)::[]) -> begin
if (let _177_373 = (let _177_372 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right _177_372 Prims.fst))
in (FStar_Util.starts_with _177_373 "fuel")) then begin
(let _177_376 = (let _177_375 = (FStar_SMTEncoding_Term.mkFreeV ((name), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_ApplyTF _177_375 fuel))
in (FStar_All.pipe_left (fun _177_374 -> Some (_177_374)) _177_376))
end else begin
Some (t)
end
end
| _85_332 -> begin
Some (t)
end)
end
| _85_334 -> begin
None
end)
end)
end))


let lookup_free_var = (fun env a -> (match ((try_lookup_free_var env a.FStar_Syntax_Syntax.v)) with
| Some (t) -> begin
t
end
| None -> begin
(let _177_380 = (let _177_379 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _177_379))
in (FStar_All.failwith _177_380))
end))


let lookup_free_var_name = (fun env a -> (

let _85_347 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_85_347) with
| (x, _85_344, _85_346) -> begin
x
end)))


let lookup_free_var_sym = (fun env a -> (

let _85_353 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_85_353) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.hash = _85_357; FStar_SMTEncoding_Term.freevars = _85_355}) when env.use_zfuel_name -> begin
((g), (zf))
end
| _85_365 -> begin
(match (sym) with
| None -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end
| Some (sym) -> begin
(match (sym.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, (fuel)::[]) -> begin
((g), ((fuel)::[]))
end
| _85_375 -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end)
end)
end)
end)))


let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun _85_6 -> (match (_85_6) with
| Binding_fvar (_85_380, nm', tok, _85_384) when (nm = nm') -> begin
tok
end
| _85_388 -> begin
None
end))))


let mkForall_fuel' = (fun n _85_393 -> (match (_85_393) with
| (pats, vars, body) -> begin
(

let fallback = (fun _85_395 -> (match (()) with
| () -> begin
(FStar_SMTEncoding_Term.mkForall ((pats), (vars), (body)))
end))
in if (FStar_Options.unthrottle_inductives ()) then begin
(fallback ())
end else begin
(

let _85_398 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_85_398) with
| (fsym, fterm) -> begin
(

let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Term.mkApp (("HasTypeFuel"), ((fterm)::args)))
end
| _85_408 -> begin
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
(let _177_397 = (add_fuel guards)
in (FStar_SMTEncoding_Term.mk_and_l _177_397))
end
| _85_421 -> begin
(let _177_398 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _177_398 FStar_List.hd))
end)
in (FStar_SMTEncoding_Term.mkImp ((guard), (body'))))
end
| _85_424 -> begin
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
(let _177_404 = (FStar_TypeChecker_Env.lookup_definition FStar_TypeChecker_Env.OnlyInline env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _177_404 FStar_Option.isNone))
end
| _85_463 -> begin
false
end)))


let head_redex : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (match ((let _177_409 = (FStar_Syntax_Util.un_uinst t)
in _177_409.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_85_467) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(let _177_410 = (FStar_TypeChecker_Env.lookup_definition FStar_TypeChecker_Env.OnlyInline env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _177_410 FStar_Option.isSome))
end
| _85_472 -> begin
false
end))


let whnf : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> if (head_normal env t) then begin
t
end else begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
end)


let norm : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t))


let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (let _177_423 = (let _177_421 = (FStar_Syntax_Syntax.null_binder t)
in (_177_421)::[])
in (let _177_422 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Util.abs _177_423 _177_422 None))))


let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(let _177_430 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out _177_430))
end
| s -> begin
(

let _85_484 = ()
in (let _177_431 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTT out _177_431)))
end)) e)))


let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Term.mk_ApplyTT e)))


let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun _85_7 -> (match (_85_7) with
| (FStar_SMTEncoding_Term.Var ("ApplyTT")) | (FStar_SMTEncoding_Term.Var ("ApplyTF")) -> begin
true
end
| _85_494 -> begin
false
end))


let is_eta : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env vars t -> (

let rec aux = (fun t xs -> (match (((t.FStar_SMTEncoding_Term.tm), (xs))) with
| (FStar_SMTEncoding_Term.App (app, (f)::({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.hash = _85_505; FStar_SMTEncoding_Term.freevars = _85_503})::[]), (x)::xs) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), _85_523) -> begin
if (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v)
end
| _85_530 -> begin
false
end)) args vars)) then begin
(tok_of_name env f)
end else begin
None
end
end
| (_85_532, []) -> begin
(

let fvs = (FStar_SMTEncoding_Term.free_variables t)
in if (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (not ((FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)))))) then begin
Some (t)
end else begin
None
end)
end
| _85_538 -> begin
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
(let _177_488 = (let _177_487 = (let _177_486 = (let _177_485 = (FStar_SMTEncoding_Term.mkInteger' (FStar_Util.int_of_char c))
in (FStar_SMTEncoding_Term.boxInt _177_485))
in (_177_486)::[])
in (("FStar.Char.Char"), (_177_487)))
in (FStar_SMTEncoding_Term.mkApp _177_488))
end
| FStar_Const.Const_int (i, None) -> begin
(let _177_489 = (FStar_SMTEncoding_Term.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt _177_489))
end
| FStar_Const.Const_int (i, Some (_85_558)) -> begin
(FStar_All.failwith "Machine integers should be desugared")
end
| FStar_Const.Const_string (bytes, _85_564) -> begin
(let _177_490 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _177_490))
end
| FStar_Const.Const_range (r) -> begin
FStar_SMTEncoding_Term.mk_Range_const
end
| FStar_Const.Const_effect -> begin
FStar_SMTEncoding_Term.mk_Term_type
end
| c -> begin
(let _177_492 = (let _177_491 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" _177_491))
in (FStar_All.failwith _177_492))
end))


let as_function_typ : env_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (

let rec aux = (fun norm t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_85_578) -> begin
t
end
| FStar_Syntax_Syntax.Tm_refine (_85_581) -> begin
(let _177_501 = (FStar_Syntax_Util.unrefine t)
in (aux true _177_501))
end
| _85_584 -> begin
if norm then begin
(let _177_502 = (whnf env t)
in (aux false _177_502))
end else begin
(let _177_505 = (let _177_504 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (let _177_503 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _177_504 _177_503)))
in (FStar_All.failwith _177_505))
end
end)))
in (aux true t0)))


let curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun k -> (

let k = (FStar_Syntax_Subst.compress k)
in (match (k.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| _85_592 -> begin
(let _177_508 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (_177_508)))
end)))


let rec encode_binders : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> (

let _85_596 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _177_556 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" _177_556))
end else begin
()
end
in (

let _85_624 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _85_603 b -> (match (_85_603) with
| (vars, guards, env, decls, names) -> begin
(

let _85_618 = (

let x = (unmangle (Prims.fst b))
in (

let _85_609 = (gen_term_var env x)
in (match (_85_609) with
| (xxsym, xx, env') -> begin
(

let _85_612 = (let _177_559 = (norm env x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt _177_559 env xx))
in (match (_85_612) with
| (guard_x_t, decls') -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (guard_x_t), (env'), (decls'), (x))
end))
end)))
in (match (_85_618) with
| (v, g, env, decls', n) -> begin
(((v)::vars), ((g)::guards), (env), ((FStar_List.append decls decls')), ((n)::names))
end))
end)) (([]), ([]), (env), ([]), ([]))))
in (match (_85_624) with
| (vars, guards, env, decls, names) -> begin
(((FStar_List.rev vars)), ((FStar_List.rev guards)), (env), (decls), ((FStar_List.rev names)))
end))))
and encode_term_pred : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let _85_631 = (encode_term t env)
in (match (_85_631) with
| (t, decls) -> begin
(let _177_564 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t)
in ((_177_564), (decls)))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let _85_638 = (encode_term t env)
in (match (_85_638) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _177_569 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t)
in ((_177_569), (decls)))
end
| Some (f) -> begin
(let _177_570 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t)
in ((_177_570), (decls)))
end)
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let t0 = (FStar_Syntax_Subst.compress t)
in (

let _85_645 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _177_575 = (FStar_Syntax_Print.tag_of_term t)
in (let _177_574 = (FStar_Syntax_Print.tag_of_term t0)
in (let _177_573 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" _177_575 _177_574 _177_573))))
end else begin
()
end
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _177_580 = (let _177_579 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (let _177_578 = (FStar_Syntax_Print.tag_of_term t0)
in (let _177_577 = (FStar_Syntax_Print.term_to_string t0)
in (let _177_576 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _177_579 _177_578 _177_577 _177_576)))))
in (FStar_All.failwith _177_580))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _177_582 = (let _177_581 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" _177_581))
in (FStar_All.failwith _177_582))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, k, _85_656) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_meta (t, _85_661) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t = (lookup_term_var env x)
in ((t), ([])))
end
| FStar_Syntax_Syntax.Tm_fvar (v) -> begin
(let _177_583 = (lookup_free_var env v.FStar_Syntax_Syntax.fv_name)
in ((_177_583), ([])))
end
| FStar_Syntax_Syntax.Tm_type (_85_670) -> begin
((FStar_SMTEncoding_Term.mk_Term_type), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t, _85_674) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(let _177_584 = (encode_const c)
in ((_177_584), ([])))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _85_685 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_85_685) with
| (binders, res) -> begin
if ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res)) then begin
(

let _85_692 = (encode_binders None binders env)
in (match (_85_692) with
| (vars, guards, env', decls, _85_691) -> begin
(

let fsym = (let _177_585 = (varops.fresh "f")
in ((_177_585), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (

let app = (mk_Apply f vars)
in (

let _85_700 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post (

let _85_696 = env.tcenv
in {FStar_TypeChecker_Env.solver = _85_696.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _85_696.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _85_696.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _85_696.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _85_696.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _85_696.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _85_696.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _85_696.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _85_696.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _85_696.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _85_696.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _85_696.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _85_696.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _85_696.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _85_696.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _85_696.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _85_696.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _85_696.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.type_of = _85_696.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _85_696.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _85_696.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _85_696.FStar_TypeChecker_Env.qname_and_index}) res)
in (match (_85_700) with
| (pre_opt, res_t) -> begin
(

let _85_703 = (encode_term_pred None res_t env' app)
in (match (_85_703) with
| (res_pred, decls') -> begin
(

let _85_712 = (match (pre_opt) with
| None -> begin
(let _177_586 = (FStar_SMTEncoding_Term.mk_and_l guards)
in ((_177_586), ([])))
end
| Some (pre) -> begin
(

let _85_709 = (encode_formula pre env')
in (match (_85_709) with
| (guard, decls0) -> begin
(let _177_587 = (FStar_SMTEncoding_Term.mk_and_l ((guard)::guards))
in ((_177_587), (decls0)))
end))
end)
in (match (_85_712) with
| (guards, guard_decls) -> begin
(

let t_interp = (let _177_589 = (let _177_588 = (FStar_SMTEncoding_Term.mkImp ((guards), (res_pred)))
in ((((app)::[])::[]), (vars), (_177_588)))
in (FStar_SMTEncoding_Term.mkForall _177_589))
in (

let cvars = (let _177_591 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right _177_591 (FStar_List.filter (fun _85_717 -> (match (_85_717) with
| (x, _85_716) -> begin
(x <> (Prims.fst fsym))
end)))))
in (

let tkey = (FStar_SMTEncoding_Term.mkForall (([]), ((fsym)::cvars), (t_interp)))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t', sorts, _85_723) -> begin
(let _177_594 = (let _177_593 = (let _177_592 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in ((t'), (_177_592)))
in (FStar_SMTEncoding_Term.mkApp _177_593))
in ((_177_594), ([])))
end
| None -> begin
(

let tsym = (let _177_596 = (let _177_595 = (FStar_Util.digest_of_string tkey.FStar_SMTEncoding_Term.hash)
in (Prims.strcat "Tm_arrow_" _177_595))
in (varops.mk_unique _177_596))
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let caption = if (FStar_Options.log_queries ()) then begin
(let _177_597 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in Some (_177_597))
end else begin
None
end
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (caption)))
in (

let t = (let _177_599 = (let _177_598 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in ((tsym), (_177_598)))
in (FStar_SMTEncoding_Term.mkApp _177_599))
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let k_assumption = (

let a_name = Some ((Prims.strcat "kinding_" tsym))
in (let _177_601 = (let _177_600 = (FStar_SMTEncoding_Term.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((_177_600), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_177_601)))
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t)
in (

let pre_typing = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in (let _177_608 = (let _177_607 = (let _177_606 = (let _177_605 = (let _177_604 = (let _177_603 = (let _177_602 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _177_602))
in ((f_has_t), (_177_603)))
in (FStar_SMTEncoding_Term.mkImp _177_604))
in ((((f_has_t)::[])::[]), ((fsym)::cvars), (_177_605)))
in (mkForall_fuel _177_606))
in ((_177_607), (Some ("pre-typing for functions")), (a_name)))
in FStar_SMTEncoding_Term.Assume (_177_608)))
in (

let t_interp = (

let a_name = Some ((Prims.strcat "interpretation_" tsym))
in (let _177_612 = (let _177_611 = (let _177_610 = (let _177_609 = (FStar_SMTEncoding_Term.mkIff ((f_has_t_z), (t_interp)))
in ((((f_has_t_z)::[])::[]), ((fsym)::cvars), (_177_609)))
in (FStar_SMTEncoding_Term.mkForall _177_610))
in ((_177_611), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_177_612)))
in (

let t_decls = (FStar_List.append ((tdecl)::decls) (FStar_List.append decls' (FStar_List.append guard_decls ((k_assumption)::(pre_typing)::(t_interp)::[]))))
in (

let _85_742 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash ((tsym), (cvar_sorts), (t_decls)))
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
in (let _177_614 = (let _177_613 = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in ((_177_613), (Some ("Typing for non-total arrows")), (a_name)))
in FStar_SMTEncoding_Term.Assume (_177_614)))
in (

let fsym = (("f"), (FStar_SMTEncoding_Term.Term_sort))
in (

let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let t_interp = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in (let _177_621 = (let _177_620 = (let _177_619 = (let _177_618 = (let _177_617 = (let _177_616 = (let _177_615 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _177_615))
in ((f_has_t), (_177_616)))
in (FStar_SMTEncoding_Term.mkImp _177_617))
in ((((f_has_t)::[])::[]), ((fsym)::[]), (_177_618)))
in (mkForall_fuel _177_619))
in ((_177_620), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_177_621)))
in ((t), ((tdecl)::(t_kinding)::(t_interp)::[]))))))))))
end
end))
end
| FStar_Syntax_Syntax.Tm_refine (_85_755) -> begin
(

let _85_775 = (match ((FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.tk = _85_762; FStar_Syntax_Syntax.pos = _85_760; FStar_Syntax_Syntax.vars = _85_758} -> begin
(

let _85_770 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) f)
in (match (_85_770) with
| (b, f) -> begin
(let _177_623 = (let _177_622 = (FStar_List.hd b)
in (Prims.fst _177_622))
in ((_177_623), (f)))
end))
end
| _85_772 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_85_775) with
| (x, f) -> begin
(

let _85_778 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (_85_778) with
| (base_t, decls) -> begin
(

let _85_782 = (gen_term_var env x)
in (match (_85_782) with
| (x, xtm, env') -> begin
(

let _85_785 = (encode_formula f env')
in (match (_85_785) with
| (refinement, decls') -> begin
(

let _85_788 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_85_788) with
| (fsym, fterm) -> begin
(

let encoding = (let _177_625 = (let _177_624 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in ((_177_624), (refinement)))
in (FStar_SMTEncoding_Term.mkAnd _177_625))
in (

let cvars = (let _177_627 = (FStar_SMTEncoding_Term.free_variables encoding)
in (FStar_All.pipe_right _177_627 (FStar_List.filter (fun _85_793 -> (match (_85_793) with
| (y, _85_792) -> begin
((y <> x) && (y <> fsym))
end)))))
in (

let xfv = ((x), (FStar_SMTEncoding_Term.Term_sort))
in (

let ffv = ((fsym), (FStar_SMTEncoding_Term.Fuel_sort))
in (

let tkey = (FStar_SMTEncoding_Term.mkForall (([]), ((ffv)::(xfv)::cvars), (encoding)))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _85_800, _85_802) -> begin
(let _177_630 = (let _177_629 = (let _177_628 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in ((t), (_177_628)))
in (FStar_SMTEncoding_Term.mkApp _177_629))
in ((_177_630), ([])))
end
| None -> begin
(

let tsym = (let _177_632 = (let _177_631 = (FStar_Util.digest_of_string tkey.FStar_SMTEncoding_Term.hash)
in (Prims.strcat "Tm_refine_" _177_631))
in (varops.mk_unique _177_632))
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let t = (let _177_634 = (let _177_633 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in ((tsym), (_177_633)))
in (FStar_SMTEncoding_Term.mkApp _177_634))
in (

let x_has_t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let t_haseq_base = (FStar_SMTEncoding_Term.mk_haseq base_t)
in (

let t_haseq_ref = (FStar_SMTEncoding_Term.mk_haseq t)
in (

let t_haseq = (let _177_638 = (let _177_637 = (let _177_636 = (let _177_635 = (FStar_SMTEncoding_Term.mkIff ((t_haseq_ref), (t_haseq_base)))
in ((((t_haseq_ref)::[])::[]), (cvars), (_177_635)))
in (FStar_SMTEncoding_Term.mkForall _177_636))
in ((_177_637), (Some ((Prims.strcat "haseq for " tsym))), (Some ((Prims.strcat "haseq" tsym)))))
in FStar_SMTEncoding_Term.Assume (_177_638))
in (

let t_kinding = (let _177_640 = (let _177_639 = (FStar_SMTEncoding_Term.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((_177_639), (Some ("refinement kinding")), (Some ((Prims.strcat "refinement_kinding_" tsym)))))
in FStar_SMTEncoding_Term.Assume (_177_640))
in (

let t_interp = (let _177_646 = (let _177_645 = (let _177_642 = (let _177_641 = (FStar_SMTEncoding_Term.mkIff ((x_has_t), (encoding)))
in ((((x_has_t)::[])::[]), ((ffv)::(xfv)::cvars), (_177_641)))
in (FStar_SMTEncoding_Term.mkForall _177_642))
in (let _177_644 = (let _177_643 = (FStar_Syntax_Print.term_to_string t0)
in Some (_177_643))
in ((_177_645), (_177_644), (Some ((Prims.strcat "refinement_interpretation_" tsym))))))
in FStar_SMTEncoding_Term.Assume (_177_646))
in (

let t_decls = (FStar_List.append decls (FStar_List.append decls' ((tdecl)::(t_kinding)::(t_interp)::(t_haseq)::[])))
in (

let _85_818 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash ((tsym), (cvar_sorts), (t_decls)))
in ((t), (t_decls)))))))))))))))
end))))))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
(

let ttm = (let _177_647 = (FStar_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Term.mk_Term_uvar _177_647))
in (

let _85_827 = (encode_term_pred None k env ttm)
in (match (_85_827) with
| (t_has_k, decls) -> begin
(

let d = (let _177_653 = (let _177_652 = (let _177_651 = (let _177_650 = (let _177_649 = (let _177_648 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _177_648))
in (FStar_Util.format1 "uvar_typing_%s" _177_649))
in (varops.mk_unique _177_650))
in Some (_177_651))
in ((t_has_k), (Some ("Uvar typing")), (_177_652)))
in FStar_SMTEncoding_Term.Assume (_177_653))
in ((ttm), ((FStar_List.append decls ((d)::[])))))
end)))
end
| FStar_Syntax_Syntax.Tm_app (_85_830) -> begin
(

let _85_834 = (FStar_Syntax_Util.head_and_args t0)
in (match (_85_834) with
| (head, args_e) -> begin
(match ((let _177_655 = (let _177_654 = (FStar_Syntax_Subst.compress head)
in _177_654.FStar_Syntax_Syntax.n)
in ((_177_655), (args_e)))) with
| (_85_836, _85_838) when (head_redex env head) -> begin
(let _177_656 = (whnf env t)
in (encode_term _177_656 env))
end
| ((FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), (_)::((v1, _))::((v2, _))::[])) | ((FStar_Syntax_Syntax.Tm_fvar (fv), (_)::((v1, _))::((v2, _))::[])) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
(

let _85_878 = (encode_term v1 env)
in (match (_85_878) with
| (v1, decls1) -> begin
(

let _85_881 = (encode_term v2 env)
in (match (_85_881) with
| (v2, decls2) -> begin
(let _177_657 = (FStar_SMTEncoding_Term.mk_LexCons v1 v2)
in ((_177_657), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), (_85_890)::(_85_887)::_85_885) -> begin
(

let e0 = (let _177_661 = (let _177_660 = (let _177_659 = (let _177_658 = (FStar_List.hd args_e)
in (_177_658)::[])
in ((head), (_177_659)))
in FStar_Syntax_Syntax.Tm_app (_177_660))
in (FStar_Syntax_Syntax.mk _177_661 None head.FStar_Syntax_Syntax.pos))
in (

let e = (let _177_664 = (let _177_663 = (let _177_662 = (FStar_List.tl args_e)
in ((e0), (_177_662)))
in FStar_Syntax_Syntax.Tm_app (_177_663))
in (FStar_Syntax_Syntax.mk _177_664 None t0.FStar_Syntax_Syntax.pos))
in (encode_term e env)))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), ((arg, _85_899))::[]) -> begin
(

let _85_905 = (encode_term arg env)
in (match (_85_905) with
| (tm, decls) -> begin
(let _177_665 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Var ("Reify")), ((tm)::[])))))
in ((_177_665), (decls)))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (_85_907)), ((arg, _85_912))::[]) -> begin
(encode_term arg env)
end
| _85_917 -> begin
(

let _85_920 = (encode_args args_e env)
in (match (_85_920) with
| (args, decls) -> begin
(

let encode_partial_app = (fun ht_opt -> (

let _85_925 = (encode_term head env)
in (match (_85_925) with
| (head, decls') -> begin
(

let app_tm = (mk_Apply_args head args)
in (match (ht_opt) with
| None -> begin
((app_tm), ((FStar_List.append decls decls')))
end
| Some (formals, c) -> begin
(

let _85_934 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (_85_934) with
| (formals, rest) -> begin
(

let subst = (FStar_List.map2 (fun _85_938 _85_942 -> (match (((_85_938), (_85_942))) with
| ((bv, _85_937), (a, _85_941)) -> begin
FStar_Syntax_Syntax.NT (((bv), (a)))
end)) formals args_e)
in (

let ty = (let _177_670 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right _177_670 (FStar_Syntax_Subst.subst subst)))
in (

let _85_947 = (encode_term_pred None ty env app_tm)
in (match (_85_947) with
| (has_type, decls'') -> begin
(

let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (

let e_typing = (let _177_676 = (let _177_675 = (FStar_SMTEncoding_Term.mkForall ((((has_type)::[])::[]), (cvars), (has_type)))
in (let _177_674 = (let _177_673 = (let _177_672 = (let _177_671 = (FStar_Util.digest_of_string app_tm.FStar_SMTEncoding_Term.hash)
in (Prims.strcat "partial_app_typing_" _177_671))
in (varops.mk_unique _177_672))
in Some (_177_673))
in ((_177_675), (Some ("Partial app typing")), (_177_674))))
in FStar_SMTEncoding_Term.Assume (_177_676))
in ((app_tm), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' ((e_typing)::[]))))))))
end))))
end))
end))
end)))
in (

let encode_full_app = (fun fv -> (

let _85_954 = (lookup_free_var_sym env fv)
in (match (_85_954) with
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
(let _177_680 = (let _177_679 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _177_679 Prims.snd))
in Some (_177_680))
end
| FStar_Syntax_Syntax.Tm_ascribed (_85_986, FStar_Util.Inl (t), _85_990) -> begin
Some (t)
end
| FStar_Syntax_Syntax.Tm_ascribed (_85_994, FStar_Util.Inr (c), _85_998) -> begin
Some ((FStar_Syntax_Util.comp_result c))
end
| _85_1002 -> begin
None
end)
in (match (head_type) with
| None -> begin
(encode_partial_app None)
end
| Some (head_type) -> begin
(

let head_type = (let _177_681 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine _177_681))
in (

let _85_1010 = (curried_arrow_formals_comp head_type)
in (match (_85_1010) with
| (formals, c) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| _85_1026 -> begin
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

let _85_1035 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_85_1035) with
| (bs, body, opening) -> begin
(

let fallback = (fun _85_1037 -> (match (()) with
| () -> begin
(

let f = (varops.fresh "Tm_abs")
in (

let decl = FStar_SMTEncoding_Term.DeclFun (((f), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Imprecise function encoding"))))
in (let _177_684 = (FStar_SMTEncoding_Term.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in ((_177_684), ((decl)::[])))))
end))
in (

let is_impure = (fun _85_9 -> (match (_85_9) with
| FStar_Util.Inl (lc) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)))
end
| FStar_Util.Inr (eff) -> begin
(let _177_687 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv eff)
in (FStar_All.pipe_right _177_687 Prims.op_Negation))
end))
in (

let codomain_eff = (fun lc -> (match (lc) with
| FStar_Util.Inl (lc) -> begin
(let _177_692 = (let _177_690 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening _177_690))
in (FStar_All.pipe_right _177_692 (fun _177_691 -> Some (_177_691))))
end
| FStar_Util.Inr (eff) -> begin
(

let new_uvar = (fun _85_1053 -> (match (()) with
| () -> begin
(let _177_695 = (FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange [] FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _177_695 Prims.fst))
end))
in if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid) then begin
(let _177_698 = (let _177_696 = (new_uvar ())
in (FStar_Syntax_Syntax.mk_Total _177_696))
in (FStar_All.pipe_right _177_698 (fun _177_697 -> Some (_177_697))))
end else begin
if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid) then begin
(let _177_701 = (let _177_699 = (new_uvar ())
in (FStar_Syntax_Syntax.mk_GTotal _177_699))
in (FStar_All.pipe_right _177_701 (fun _177_700 -> Some (_177_700))))
end else begin
None
end
end)
end))
in (match (lopt) with
| None -> begin
(

let _85_1055 = (let _177_703 = (let _177_702 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s" _177_702))
in (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos _177_703))
in (fallback ()))
end
| Some (lc) -> begin
if (is_impure lc) then begin
(fallback ())
end else begin
(

let _85_1065 = (encode_binders None bs env)
in (match (_85_1065) with
| (vars, guards, envbody, decls, _85_1064) -> begin
(

let _85_1068 = (encode_term body envbody)
in (match (_85_1068) with
| (body, decls') -> begin
(

let key_body = (let _177_707 = (let _177_706 = (let _177_705 = (let _177_704 = (FStar_SMTEncoding_Term.mk_and_l guards)
in ((_177_704), (body)))
in (FStar_SMTEncoding_Term.mkImp _177_705))
in (([]), (vars), (_177_706)))
in (FStar_SMTEncoding_Term.mkForall _177_707))
in (

let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (

let tkey = (FStar_SMTEncoding_Term.mkForall (([]), (cvars), (key_body)))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _85_1074, _85_1076) -> begin
(let _177_710 = (let _177_709 = (let _177_708 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in ((t), (_177_708)))
in (FStar_SMTEncoding_Term.mkApp _177_709))
in ((_177_710), ([])))
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

let fsym = (let _177_712 = (let _177_711 = (FStar_Util.digest_of_string tkey.FStar_SMTEncoding_Term.hash)
in (Prims.strcat "Tm_abs_" _177_711))
in (varops.mk_unique _177_712))
in (

let fdecl = FStar_SMTEncoding_Term.DeclFun (((fsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let f = (let _177_714 = (let _177_713 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in ((fsym), (_177_713)))
in (FStar_SMTEncoding_Term.mkApp _177_714))
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

let _85_1094 = (encode_term_pred None tfun env f)
in (match (_85_1094) with
| (f_has_t, decls'') -> begin
(

let a_name = Some ((Prims.strcat "typing_" fsym))
in (let _177_718 = (let _177_717 = (let _177_716 = (let _177_715 = (FStar_SMTEncoding_Term.mkForall ((((f)::[])::[]), (cvars), (f_has_t)))
in ((_177_715), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_177_716))
in (_177_717)::[])
in (FStar_List.append decls'' _177_718)))
end)))
end)
in (

let interp_f = (

let a_name = Some ((Prims.strcat "interpretation_" fsym))
in (let _177_722 = (let _177_721 = (let _177_720 = (let _177_719 = (FStar_SMTEncoding_Term.mkEq ((app), (body)))
in ((((app)::[])::[]), ((FStar_List.append vars cvars)), (_177_719)))
in (FStar_SMTEncoding_Term.mkForall _177_720))
in ((_177_721), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_177_722)))
in (

let f_decls = (FStar_List.append decls (FStar_List.append decls' (FStar_List.append ((fdecl)::typing_f) ((interp_f)::[]))))
in (

let _85_1100 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash ((fsym), (cvar_sorts), (f_decls)))
in ((f), (f_decls)))))))))))
end)
end))))
end))
end))
end
end))))
end))
end
| FStar_Syntax_Syntax.Tm_let ((_85_1103, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_85_1115); FStar_Syntax_Syntax.lbunivs = _85_1113; FStar_Syntax_Syntax.lbtyp = _85_1111; FStar_Syntax_Syntax.lbeff = _85_1109; FStar_Syntax_Syntax.lbdef = _85_1107})::_85_1105), _85_1121) -> begin
(FStar_All.failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _85_1130; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _85_1127; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (_85_1140) -> begin
(

let _85_1142 = (FStar_TypeChecker_Errors.diag t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (

let e = (varops.fresh "let-rec")
in (

let decl_e = FStar_SMTEncoding_Term.DeclFun (((e), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (let _177_723 = (FStar_SMTEncoding_Term.mkFreeV ((e), (FStar_SMTEncoding_Term.Term_sort)))
in ((_177_723), ((decl_e)::[]))))))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end))))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (

let _85_1158 = (encode_term e1 env)
in (match (_85_1158) with
| (ee1, decls1) -> begin
(

let _85_1161 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) e2)
in (match (_85_1161) with
| (xs, e2) -> begin
(

let _85_1165 = (FStar_List.hd xs)
in (match (_85_1165) with
| (x, _85_1164) -> begin
(

let env' = (push_term_var env x ee1)
in (

let _85_1169 = (encode_body e2 env')
in (match (_85_1169) with
| (ee2, decls2) -> begin
((ee2), ((FStar_List.append decls1 decls2)))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (

let _85_1177 = (encode_term e env)
in (match (_85_1177) with
| (scr, decls) -> begin
(

let _85_1214 = (FStar_List.fold_right (fun b _85_1181 -> (match (_85_1181) with
| (else_case, decls) -> begin
(

let _85_1185 = (FStar_Syntax_Subst.open_branch b)
in (match (_85_1185) with
| (p, w, br) -> begin
(

let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun _85_1189 _85_1192 -> (match (((_85_1189), (_85_1192))) with
| ((env0, pattern), (else_case, decls)) -> begin
(

let guard = (pattern.guard scr)
in (

let projections = (pattern.projections scr)
in (

let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env _85_1198 -> (match (_85_1198) with
| (x, t) -> begin
(push_term_var env x t)
end)) env))
in (

let _85_1208 = (match (w) with
| None -> begin
((guard), ([]))
end
| Some (w) -> begin
(

let _85_1205 = (encode_term w env)
in (match (_85_1205) with
| (w, decls2) -> begin
(let _177_757 = (let _177_756 = (let _177_755 = (let _177_754 = (let _177_753 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Term.mkTrue)
in ((w), (_177_753)))
in (FStar_SMTEncoding_Term.mkEq _177_754))
in ((guard), (_177_755)))
in (FStar_SMTEncoding_Term.mkAnd _177_756))
in ((_177_757), (decls2)))
end))
end)
in (match (_85_1208) with
| (guard, decls2) -> begin
(

let _85_1211 = (encode_br br env)
in (match (_85_1211) with
| (br, decls3) -> begin
(let _177_758 = (FStar_SMTEncoding_Term.mkITE ((guard), (br), (else_case)))
in ((_177_758), ((FStar_List.append decls (FStar_List.append decls2 decls3)))))
end))
end)))))
end)) patterns ((else_case), (decls))))
end))
end)) pats ((default_case), (decls)))
in (match (_85_1214) with
| (match_tm, decls) -> begin
((match_tm), (decls))
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _85_1220 -> begin
(let _177_761 = (encode_one_pat env pat)
in (_177_761)::[])
end))
and encode_one_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> (

let _85_1223 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _177_764 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" _177_764))
end else begin
()
end
in (

let _85_1227 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (_85_1227) with
| (vars, pat_term) -> begin
(

let _85_1239 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun _85_1230 v -> (match (_85_1230) with
| (env, vars) -> begin
(

let _85_1236 = (gen_term_var env v)
in (match (_85_1236) with
| (xx, _85_1234, env) -> begin
((env), ((((v), (((xx), (FStar_SMTEncoding_Term.Term_sort)))))::vars))
end))
end)) ((env), ([]))))
in (match (_85_1239) with
| (env, vars) -> begin
(

let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_85_1244) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_dot_term (_)) -> begin
FStar_SMTEncoding_Term.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _177_772 = (let _177_771 = (encode_const c)
in ((scrutinee), (_177_771)))
in (FStar_SMTEncoding_Term.mkEq _177_772))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let is_f = (mk_data_tester env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _85_1266 -> (match (_85_1266) with
| (arg, _85_1265) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _177_775 = (FStar_SMTEncoding_Term.mkApp ((proj), ((scrutinee)::[])))
in (mk_guard arg _177_775)))
end))))
in (FStar_SMTEncoding_Term.mk_and_l ((is_f)::sub_term_guards))))
end))
in (

let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_85_1273) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _)) | (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_constant (_85_1283) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(let _177_783 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _85_1293 -> (match (_85_1293) with
| (arg, _85_1292) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _177_782 = (FStar_SMTEncoding_Term.mkApp ((proj), ((scrutinee)::[])))
in (mk_projections arg _177_782)))
end))))
in (FStar_All.pipe_right _177_783 FStar_List.flatten))
end))
in (

let pat_term = (fun _85_1296 -> (match (()) with
| () -> begin
(encode_term pat_term env)
end))
in (

let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in ((env), (pattern))))))
end))
end))))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (

let _85_1312 = (FStar_All.pipe_right l (FStar_List.fold_left (fun _85_1302 _85_1306 -> (match (((_85_1302), (_85_1306))) with
| ((tms, decls), (t, _85_1305)) -> begin
(

let _85_1309 = (encode_term t env)
in (match (_85_1309) with
| (t, decls') -> begin
(((t)::tms), ((FStar_List.append decls decls')))
end))
end)) (([]), ([]))))
in (match (_85_1312) with
| (l, decls) -> begin
(((FStar_List.rev l)), (decls))
end)))
and encode_function_type_as_formula : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun induction_on new_pats t env -> (

let rec list_elements = (fun e -> (

let _85_1321 = (let _177_796 = (FStar_Syntax_Util.unmeta e)
in (FStar_Syntax_Util.head_and_args _177_796))
in (match (_85_1321) with
| (head, args) -> begin
(match ((let _177_798 = (let _177_797 = (FStar_Syntax_Util.un_uinst head)
in _177_797.FStar_Syntax_Syntax.n)
in ((_177_798), (args)))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), _85_1325) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid) -> begin
[]
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_85_1338)::((hd, _85_1335))::((tl, _85_1331))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid) -> begin
(let _177_799 = (list_elements tl)
in (hd)::_177_799)
end
| _85_1342 -> begin
(

let _85_1343 = (FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern")
in [])
end)
end)))
in (

let one_pat = (fun p -> (

let _85_1349 = (let _177_802 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right _177_802 FStar_Syntax_Util.head_and_args))
in (match (_85_1349) with
| (head, args) -> begin
(match ((let _177_804 = (let _177_803 = (FStar_Syntax_Util.un_uinst head)
in _177_803.FStar_Syntax_Syntax.n)
in ((_177_804), (args)))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((_85_1357, _85_1359))::((e, _85_1354))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpat_lid) -> begin
((e), (None))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, _85_1367))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatT_lid) -> begin
((e), (None))
end
| _85_1372 -> begin
(FStar_All.failwith "Unexpected pattern term")
end)
end)))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements p)
in (

let smt_pat_or = (fun t -> (

let _85_1380 = (let _177_809 = (FStar_Syntax_Util.unmeta t)
in (FStar_All.pipe_right _177_809 FStar_Syntax_Util.head_and_args))
in (match (_85_1380) with
| (head, args) -> begin
(match ((let _177_811 = (let _177_810 = (FStar_Syntax_Util.un_uinst head)
in _177_810.FStar_Syntax_Syntax.n)
in ((_177_811), (args)))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, _85_1385))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatOr_lid) -> begin
Some (e)
end
| _85_1390 -> begin
None
end)
end)))
in (match (elts) with
| (t)::[] -> begin
(match ((smt_pat_or t)) with
| Some (e) -> begin
(let _177_814 = (list_elements e)
in (FStar_All.pipe_right _177_814 (FStar_List.map (fun branch -> (let _177_813 = (list_elements branch)
in (FStar_All.pipe_right _177_813 (FStar_List.map one_pat)))))))
end
| _85_1397 -> begin
(let _177_815 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_177_815)::[])
end)
end
| _85_1399 -> begin
(let _177_816 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_177_816)::[])
end))))
in (

let _85_1433 = (match ((let _177_817 = (FStar_Syntax_Subst.compress t)
in _177_817.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _85_1406 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_85_1406) with
| (binders, c) -> begin
(

let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| ((pre, _85_1418))::((post, _85_1414))::((pats, _85_1410))::[] -> begin
(

let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _177_818 = (lemma_pats pats')
in ((binders), (pre), (post), (_177_818))))
end
| _85_1426 -> begin
(FStar_All.failwith "impos")
end))
end))
end
| _85_1428 -> begin
(FStar_All.failwith "Impos")
end)
in (match (_85_1433) with
| (binders, pre, post, patterns) -> begin
(

let _85_1440 = (encode_binders None binders env)
in (match (_85_1440) with
| (vars, guards, env, decls, _85_1439) -> begin
(

let _85_1453 = (let _177_822 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (

let _85_1450 = (let _177_821 = (FStar_All.pipe_right branch (FStar_List.map (fun _85_1445 -> (match (_85_1445) with
| (t, _85_1444) -> begin
(encode_term t (

let _85_1446 = env
in {bindings = _85_1446.bindings; depth = _85_1446.depth; tcenv = _85_1446.tcenv; warn = _85_1446.warn; cache = _85_1446.cache; nolabels = _85_1446.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _85_1446.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _177_821 FStar_List.unzip))
in (match (_85_1450) with
| (pats, decls) -> begin
((pats), (decls))
end)))))
in (FStar_All.pipe_right _177_822 FStar_List.unzip))
in (match (_85_1453) with
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
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _177_825 = (let _177_824 = (FStar_SMTEncoding_Term.mkFreeV l)
in (FStar_SMTEncoding_Term.mk_Precedes _177_824 e))
in (_177_825)::p))))
end
| _85_1463 -> begin
(

let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _177_831 = (FStar_SMTEncoding_Term.mk_Precedes tl e)
in (_177_831)::p))))
end
| ((x, FStar_SMTEncoding_Term.Term_sort))::vars -> begin
(let _177_833 = (let _177_832 = (FStar_SMTEncoding_Term.mkFreeV ((x), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_LexCons _177_832 tl))
in (aux _177_833 vars))
end
| _85_1475 -> begin
pats
end))
in (let _177_834 = (FStar_SMTEncoding_Term.mkFreeV (("Prims.LexTop"), (FStar_SMTEncoding_Term.Term_sort)))
in (aux _177_834 vars)))
end)
end)
in (

let env = (

let _85_1477 = env
in {bindings = _85_1477.bindings; depth = _85_1477.depth; tcenv = _85_1477.tcenv; warn = _85_1477.warn; cache = _85_1477.cache; nolabels = true; use_zfuel_name = _85_1477.use_zfuel_name; encode_non_total_function_typ = _85_1477.encode_non_total_function_typ})
in (

let _85_1482 = (let _177_835 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula _177_835 env))
in (match (_85_1482) with
| (pre, decls'') -> begin
(

let _85_1485 = (let _177_836 = (FStar_Syntax_Util.unmeta post)
in (encode_formula _177_836 env))
in (match (_85_1485) with
| (post, decls''') -> begin
(

let decls = (FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') (FStar_List.append decls'' decls''')))
in (let _177_841 = (let _177_840 = (let _177_839 = (let _177_838 = (let _177_837 = (FStar_SMTEncoding_Term.mk_and_l ((pre)::guards))
in ((_177_837), (post)))
in (FStar_SMTEncoding_Term.mkImp _177_838))
in ((pats), (vars), (_177_839)))
in (FStar_SMTEncoding_Term.mkForall _177_840))
in ((_177_841), (decls))))
end))
end)))))
end))
end))
end))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (

let debug = (fun phi -> if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _177_847 = (FStar_Syntax_Print.tag_of_term phi)
in (let _177_846 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print2 "Formula (%s)  %s\n" _177_847 _177_846)))
end else begin
()
end)
in (

let enc = (fun f l -> (

let _85_1501 = (FStar_Util.fold_map (fun decls x -> (

let _85_1498 = (encode_term (Prims.fst x) env)
in (match (_85_1498) with
| (t, decls') -> begin
(((FStar_List.append decls decls')), (t))
end))) [] l)
in (match (_85_1501) with
| (decls, args) -> begin
(let _177_863 = (f args)
in ((_177_863), (decls)))
end)))
in (

let const_op = (fun f _85_1504 -> ((f), ([])))
in (

let un_op = (fun f l -> (let _177_877 = (FStar_List.hd l)
in (FStar_All.pipe_left f _177_877)))
in (

let bin_op = (fun f _85_10 -> (match (_85_10) with
| (t1)::(t2)::[] -> begin
(f ((t1), (t2)))
end
| _85_1515 -> begin
(FStar_All.failwith "Impossible")
end))
in (

let enc_prop_c = (fun f l -> (

let _85_1530 = (FStar_Util.fold_map (fun decls _85_1524 -> (match (_85_1524) with
| (t, _85_1523) -> begin
(

let _85_1527 = (encode_formula t env)
in (match (_85_1527) with
| (phi, decls') -> begin
(((FStar_List.append decls decls')), (phi))
end))
end)) [] l)
in (match (_85_1530) with
| (decls, phis) -> begin
(let _177_902 = (f phis)
in ((_177_902), (decls)))
end)))
in (

let eq_op = (fun _85_11 -> (match (_85_11) with
| ((_)::(e1)::(e2)::[]) | ((_)::(_)::(e1)::(e2)::[]) -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) l)
end))
in (

let mk_imp = (fun _85_12 -> (match (_85_12) with
| ((lhs, _85_1551))::((rhs, _85_1547))::[] -> begin
(

let _85_1556 = (encode_formula rhs env)
in (match (_85_1556) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _85_1559) -> begin
((l1), (decls1))
end
| _85_1563 -> begin
(

let _85_1566 = (encode_formula lhs env)
in (match (_85_1566) with
| (l2, decls2) -> begin
(let _177_907 = (FStar_SMTEncoding_Term.mkImp ((l2), (l1)))
in ((_177_907), ((FStar_List.append decls1 decls2))))
end))
end)
end))
end
| _85_1568 -> begin
(FStar_All.failwith "impossible")
end))
in (

let mk_ite = (fun _85_13 -> (match (_85_13) with
| ((guard, _85_1581))::((_then, _85_1577))::((_else, _85_1573))::[] -> begin
(

let _85_1586 = (encode_formula guard env)
in (match (_85_1586) with
| (g, decls1) -> begin
(

let _85_1589 = (encode_formula _then env)
in (match (_85_1589) with
| (t, decls2) -> begin
(

let _85_1592 = (encode_formula _else env)
in (match (_85_1592) with
| (e, decls3) -> begin
(

let res = (FStar_SMTEncoding_Term.mkITE ((g), (t), (e)))
in ((res), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end))
end))
end
| _85_1595 -> begin
(FStar_All.failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (let _177_919 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f _177_919)))
in (

let connectives = (let _177_975 = (let _177_928 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkAnd))
in ((FStar_Syntax_Const.and_lid), (_177_928)))
in (let _177_974 = (let _177_973 = (let _177_934 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkOr))
in ((FStar_Syntax_Const.or_lid), (_177_934)))
in (let _177_972 = (let _177_971 = (let _177_970 = (let _177_943 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkIff))
in ((FStar_Syntax_Const.iff_lid), (_177_943)))
in (let _177_969 = (let _177_968 = (let _177_967 = (let _177_952 = (FStar_All.pipe_left enc_prop_c (un_op FStar_SMTEncoding_Term.mkNot))
in ((FStar_Syntax_Const.not_lid), (_177_952)))
in (_177_967)::(((FStar_Syntax_Const.eq2_lid), (eq_op)))::(((FStar_Syntax_Const.eq3_lid), (eq_op)))::(((FStar_Syntax_Const.true_lid), ((const_op FStar_SMTEncoding_Term.mkTrue))))::(((FStar_Syntax_Const.false_lid), ((const_op FStar_SMTEncoding_Term.mkFalse))))::[])
in (((FStar_Syntax_Const.ite_lid), (mk_ite)))::_177_968)
in (_177_970)::_177_969))
in (((FStar_Syntax_Const.imp_lid), (mk_imp)))::_177_971)
in (_177_973)::_177_972))
in (_177_975)::_177_974))
in (

let rec fallback = (fun phi -> (match (phi.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(

let _85_1613 = (encode_formula phi' env)
in (match (_85_1613) with
| (phi, decls) -> begin
(let _177_978 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled (((phi), (msg), (r)))))
in ((_177_978), (decls)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (_85_1615) -> begin
(let _177_979 = (FStar_Syntax_Util.unmeta phi)
in (encode_formula _177_979 env))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(

let _85_1623 = (encode_match e pats FStar_SMTEncoding_Term.mkFalse env encode_formula)
in (match (_85_1623) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _85_1630; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _85_1627; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _85_1641 = (encode_let x t1 e1 e2 env encode_formula)
in (match (_85_1641) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let head = (FStar_Syntax_Util.un_uinst head)
in (match (((head.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_85_1658)::((x, _85_1655))::((t, _85_1651))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.has_type_lid) -> begin
(

let _85_1663 = (encode_term x env)
in (match (_85_1663) with
| (x, decls) -> begin
(

let _85_1666 = (encode_term t env)
in (match (_85_1666) with
| (t, decls') -> begin
(let _177_980 = (FStar_SMTEncoding_Term.mk_HasType x t)
in ((_177_980), ((FStar_List.append decls decls'))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((r, _85_1679))::((msg, _85_1675))::((phi, _85_1671))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.labeled_lid) -> begin
(match ((let _177_984 = (let _177_981 = (FStar_Syntax_Subst.compress r)
in _177_981.FStar_Syntax_Syntax.n)
in (let _177_983 = (let _177_982 = (FStar_Syntax_Subst.compress msg)
in _177_982.FStar_Syntax_Syntax.n)
in ((_177_984), (_177_983))))) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, _85_1688))) -> begin
(

let phi = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((phi), (FStar_Syntax_Syntax.Meta_labeled ((((FStar_Util.string_of_unicode s)), (r), (false))))))) None r)
in (fallback phi))
end
| _85_1695 -> begin
(fallback phi)
end)
end
| _85_1697 when (head_redex env head) -> begin
(let _177_985 = (whnf env phi)
in (encode_formula _177_985 env))
end
| _85_1699 -> begin
(

let _85_1702 = (encode_term phi env)
in (match (_85_1702) with
| (tt, decls) -> begin
(let _177_986 = (FStar_SMTEncoding_Term.mk_Valid tt)
in ((_177_986), (decls)))
end))
end))
end
| _85_1704 -> begin
(

let _85_1707 = (encode_term phi env)
in (match (_85_1707) with
| (tt, decls) -> begin
(let _177_987 = (FStar_SMTEncoding_Term.mk_Valid tt)
in ((_177_987), (decls)))
end))
end))
in (

let encode_q_body = (fun env bs ps body -> (

let _85_1719 = (encode_binders None bs env)
in (match (_85_1719) with
| (vars, guards, env, decls, _85_1718) -> begin
(

let _85_1732 = (let _177_999 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let _85_1729 = (let _177_998 = (FStar_All.pipe_right p (FStar_List.map (fun _85_1724 -> (match (_85_1724) with
| (t, _85_1723) -> begin
(encode_term t (

let _85_1725 = env
in {bindings = _85_1725.bindings; depth = _85_1725.depth; tcenv = _85_1725.tcenv; warn = _85_1725.warn; cache = _85_1725.cache; nolabels = _85_1725.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _85_1725.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _177_998 FStar_List.unzip))
in (match (_85_1729) with
| (p, decls) -> begin
((p), ((FStar_List.flatten decls)))
end)))))
in (FStar_All.pipe_right _177_999 FStar_List.unzip))
in (match (_85_1732) with
| (pats, decls') -> begin
(

let _85_1735 = (encode_formula body env)
in (match (_85_1735) with
| (body, decls'') -> begin
(

let guards = (match (pats) with
| (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (gf), (p)::[]); FStar_SMTEncoding_Term.hash = _85_1739; FStar_SMTEncoding_Term.freevars = _85_1737})::[])::[] when ((FStar_Ident.text_of_lid FStar_Syntax_Const.guard_free) = gf) -> begin
[]
end
| _85_1750 -> begin
guards
end)
in (let _177_1000 = (FStar_SMTEncoding_Term.mk_and_l guards)
in ((vars), (pats), (_177_1000), (body), ((FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') decls''))))))
end))
end))
end)))
in (

let _85_1752 = (debug phi)
in (

let phi = (FStar_Syntax_Util.unascribe phi)
in (match ((FStar_Syntax_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _85_1764 -> (match (_85_1764) with
| (l, _85_1763) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_85_1767, f) -> begin
(f arms)
end)
end
| Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
(

let _85_1777 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _177_1017 = (FStar_All.pipe_right vars (FStar_Syntax_Print.binders_to_string "; "))
in (FStar_Util.print1 ">>>> Got QALL [%s]\n" _177_1017))
end else begin
()
end
in (

let _85_1784 = (encode_q_body env vars pats body)
in (match (_85_1784) with
| (vars, pats, guard, body, decls) -> begin
(

let tm = (let _177_1019 = (let _177_1018 = (FStar_SMTEncoding_Term.mkImp ((guard), (body)))
in ((pats), (vars), (_177_1018)))
in (FStar_SMTEncoding_Term.mkForall _177_1019))
in (

let _85_1786 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _177_1020 = (FStar_SMTEncoding_Term.termToSmt tm)
in (FStar_Util.print1 ">>>> Encoded QALL to %s\n" _177_1020))
end else begin
()
end
in ((tm), (decls))))
end)))
end
| Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
(

let _85_1799 = (encode_q_body env vars pats body)
in (match (_85_1799) with
| (vars, pats, guard, body, decls) -> begin
(let _177_1023 = (let _177_1022 = (let _177_1021 = (FStar_SMTEncoding_Term.mkAnd ((guard), (body)))
in ((pats), (vars), (_177_1021)))
in (FStar_SMTEncoding_Term.mkExists _177_1022))
in ((_177_1023), (decls)))
end))
end)))))))))))))))))


type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list); is : FStar_Ident.lident  ->  Prims.bool}


let is_Mkprims_t : prims_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkprims_t"))))


let prims : prims_t = (

let _85_1805 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (_85_1805) with
| (asym, a) -> begin
(

let _85_1808 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_85_1808) with
| (xsym, x) -> begin
(

let _85_1811 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (_85_1811) with
| (ysym, y) -> begin
(

let deffun = (fun vars body x -> (FStar_SMTEncoding_Term.DefineFun (((x), (vars), (FStar_SMTEncoding_Term.Term_sort), (body), (None))))::[])
in (

let quant = (fun vars body x -> (

let xname_decl = (let _177_1066 = (let _177_1065 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in ((x), (_177_1065), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (_177_1066))
in (

let xtok = (Prims.strcat x "@tok")
in (

let xtok_decl = FStar_SMTEncoding_Term.DeclFun (((xtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let xapp = (let _177_1068 = (let _177_1067 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in ((x), (_177_1067)))
in (FStar_SMTEncoding_Term.mkApp _177_1068))
in (

let xtok = (FStar_SMTEncoding_Term.mkApp ((xtok), ([])))
in (

let xtok_app = (mk_Apply xtok vars)
in (let _177_1082 = (let _177_1081 = (let _177_1080 = (let _177_1079 = (let _177_1072 = (let _177_1071 = (let _177_1070 = (let _177_1069 = (FStar_SMTEncoding_Term.mkEq ((xapp), (body)))
in ((((xapp)::[])::[]), (vars), (_177_1069)))
in (FStar_SMTEncoding_Term.mkForall _177_1070))
in ((_177_1071), (None), (Some ((Prims.strcat "primitive_" x)))))
in FStar_SMTEncoding_Term.Assume (_177_1072))
in (let _177_1078 = (let _177_1077 = (let _177_1076 = (let _177_1075 = (let _177_1074 = (let _177_1073 = (FStar_SMTEncoding_Term.mkEq ((xtok_app), (xapp)))
in ((((xtok_app)::[])::[]), (vars), (_177_1073)))
in (FStar_SMTEncoding_Term.mkForall _177_1074))
in ((_177_1075), (Some ("Name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" x)))))
in FStar_SMTEncoding_Term.Assume (_177_1076))
in (_177_1077)::[])
in (_177_1079)::_177_1078))
in (xtok_decl)::_177_1080)
in (xname_decl)::_177_1081)
in ((xtok), (_177_1082))))))))))
in (

let axy = (((asym), (FStar_SMTEncoding_Term.Term_sort)))::(((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let xy = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let qx = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let prims = (let _177_1242 = (let _177_1091 = (let _177_1090 = (let _177_1089 = (FStar_SMTEncoding_Term.mkEq ((x), (y)))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1089))
in (quant axy _177_1090))
in ((FStar_Syntax_Const.op_Eq), (_177_1091)))
in (let _177_1241 = (let _177_1240 = (let _177_1098 = (let _177_1097 = (let _177_1096 = (let _177_1095 = (FStar_SMTEncoding_Term.mkEq ((x), (y)))
in (FStar_SMTEncoding_Term.mkNot _177_1095))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1096))
in (quant axy _177_1097))
in ((FStar_Syntax_Const.op_notEq), (_177_1098)))
in (let _177_1239 = (let _177_1238 = (let _177_1107 = (let _177_1106 = (let _177_1105 = (let _177_1104 = (let _177_1103 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1102 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_177_1103), (_177_1102))))
in (FStar_SMTEncoding_Term.mkLT _177_1104))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1105))
in (quant xy _177_1106))
in ((FStar_Syntax_Const.op_LT), (_177_1107)))
in (let _177_1237 = (let _177_1236 = (let _177_1116 = (let _177_1115 = (let _177_1114 = (let _177_1113 = (let _177_1112 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1111 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_177_1112), (_177_1111))))
in (FStar_SMTEncoding_Term.mkLTE _177_1113))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1114))
in (quant xy _177_1115))
in ((FStar_Syntax_Const.op_LTE), (_177_1116)))
in (let _177_1235 = (let _177_1234 = (let _177_1125 = (let _177_1124 = (let _177_1123 = (let _177_1122 = (let _177_1121 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1120 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_177_1121), (_177_1120))))
in (FStar_SMTEncoding_Term.mkGT _177_1122))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1123))
in (quant xy _177_1124))
in ((FStar_Syntax_Const.op_GT), (_177_1125)))
in (let _177_1233 = (let _177_1232 = (let _177_1134 = (let _177_1133 = (let _177_1132 = (let _177_1131 = (let _177_1130 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1129 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_177_1130), (_177_1129))))
in (FStar_SMTEncoding_Term.mkGTE _177_1131))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1132))
in (quant xy _177_1133))
in ((FStar_Syntax_Const.op_GTE), (_177_1134)))
in (let _177_1231 = (let _177_1230 = (let _177_1143 = (let _177_1142 = (let _177_1141 = (let _177_1140 = (let _177_1139 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1138 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_177_1139), (_177_1138))))
in (FStar_SMTEncoding_Term.mkSub _177_1140))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _177_1141))
in (quant xy _177_1142))
in ((FStar_Syntax_Const.op_Subtraction), (_177_1143)))
in (let _177_1229 = (let _177_1228 = (let _177_1150 = (let _177_1149 = (let _177_1148 = (let _177_1147 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Term.mkMinus _177_1147))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _177_1148))
in (quant qx _177_1149))
in ((FStar_Syntax_Const.op_Minus), (_177_1150)))
in (let _177_1227 = (let _177_1226 = (let _177_1159 = (let _177_1158 = (let _177_1157 = (let _177_1156 = (let _177_1155 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1154 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_177_1155), (_177_1154))))
in (FStar_SMTEncoding_Term.mkAdd _177_1156))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _177_1157))
in (quant xy _177_1158))
in ((FStar_Syntax_Const.op_Addition), (_177_1159)))
in (let _177_1225 = (let _177_1224 = (let _177_1168 = (let _177_1167 = (let _177_1166 = (let _177_1165 = (let _177_1164 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1163 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_177_1164), (_177_1163))))
in (FStar_SMTEncoding_Term.mkMul _177_1165))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _177_1166))
in (quant xy _177_1167))
in ((FStar_Syntax_Const.op_Multiply), (_177_1168)))
in (let _177_1223 = (let _177_1222 = (let _177_1177 = (let _177_1176 = (let _177_1175 = (let _177_1174 = (let _177_1173 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1172 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_177_1173), (_177_1172))))
in (FStar_SMTEncoding_Term.mkDiv _177_1174))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _177_1175))
in (quant xy _177_1176))
in ((FStar_Syntax_Const.op_Division), (_177_1177)))
in (let _177_1221 = (let _177_1220 = (let _177_1186 = (let _177_1185 = (let _177_1184 = (let _177_1183 = (let _177_1182 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1181 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_177_1182), (_177_1181))))
in (FStar_SMTEncoding_Term.mkMod _177_1183))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _177_1184))
in (quant xy _177_1185))
in ((FStar_Syntax_Const.op_Modulus), (_177_1186)))
in (let _177_1219 = (let _177_1218 = (let _177_1195 = (let _177_1194 = (let _177_1193 = (let _177_1192 = (let _177_1191 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _177_1190 = (FStar_SMTEncoding_Term.unboxBool y)
in ((_177_1191), (_177_1190))))
in (FStar_SMTEncoding_Term.mkAnd _177_1192))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1193))
in (quant xy _177_1194))
in ((FStar_Syntax_Const.op_And), (_177_1195)))
in (let _177_1217 = (let _177_1216 = (let _177_1204 = (let _177_1203 = (let _177_1202 = (let _177_1201 = (let _177_1200 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _177_1199 = (FStar_SMTEncoding_Term.unboxBool y)
in ((_177_1200), (_177_1199))))
in (FStar_SMTEncoding_Term.mkOr _177_1201))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1202))
in (quant xy _177_1203))
in ((FStar_Syntax_Const.op_Or), (_177_1204)))
in (let _177_1215 = (let _177_1214 = (let _177_1211 = (let _177_1210 = (let _177_1209 = (let _177_1208 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Term.mkNot _177_1208))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1209))
in (quant qx _177_1210))
in ((FStar_Syntax_Const.op_Negation), (_177_1211)))
in (_177_1214)::[])
in (_177_1216)::_177_1215))
in (_177_1218)::_177_1217))
in (_177_1220)::_177_1219))
in (_177_1222)::_177_1221))
in (_177_1224)::_177_1223))
in (_177_1226)::_177_1225))
in (_177_1228)::_177_1227))
in (_177_1230)::_177_1229))
in (_177_1232)::_177_1231))
in (_177_1234)::_177_1233))
in (_177_1236)::_177_1235))
in (_177_1238)::_177_1237))
in (_177_1240)::_177_1239))
in (_177_1242)::_177_1241))
in (

let mk = (fun l v -> (let _177_1289 = (let _177_1288 = (FStar_All.pipe_right prims (FStar_List.find (fun _85_1835 -> (match (_85_1835) with
| (l', _85_1834) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right _177_1288 (FStar_Option.map (fun _85_1839 -> (match (_85_1839) with
| (_85_1837, b) -> begin
(b v)
end)))))
in (FStar_All.pipe_right _177_1289 FStar_Option.get)))
in (

let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _85_1845 -> (match (_85_1845) with
| (l', _85_1844) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is}))))))))
end))
end))
end))


let pretype_axiom : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun tapp vars -> (

let _85_1851 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_85_1851) with
| (xxsym, xx) -> begin
(

let _85_1854 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_85_1854) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (let _177_1319 = (let _177_1318 = (let _177_1313 = (let _177_1312 = (let _177_1311 = (let _177_1310 = (let _177_1309 = (let _177_1308 = (FStar_SMTEncoding_Term.mkApp (("PreType"), ((xx)::[])))
in ((tapp), (_177_1308)))
in (FStar_SMTEncoding_Term.mkEq _177_1309))
in ((xx_has_type), (_177_1310)))
in (FStar_SMTEncoding_Term.mkImp _177_1311))
in ((((xx_has_type)::[])::[]), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars), (_177_1312)))
in (FStar_SMTEncoding_Term.mkForall _177_1313))
in (let _177_1317 = (let _177_1316 = (let _177_1315 = (let _177_1314 = (FStar_Util.digest_of_string tapp.FStar_SMTEncoding_Term.hash)
in (Prims.strcat "pretyping_" _177_1314))
in (varops.mk_unique _177_1315))
in Some (_177_1316))
in ((_177_1318), (Some ("pretyping")), (_177_1317))))
in FStar_SMTEncoding_Term.Assume (_177_1319)))
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
in (let _177_1340 = (let _177_1331 = (let _177_1330 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in ((_177_1330), (Some ("unit typing")), (Some ("unit_typing"))))
in FStar_SMTEncoding_Term.Assume (_177_1331))
in (let _177_1339 = (let _177_1338 = (let _177_1337 = (let _177_1336 = (let _177_1335 = (let _177_1334 = (let _177_1333 = (let _177_1332 = (FStar_SMTEncoding_Term.mkEq ((x), (FStar_SMTEncoding_Term.mk_Term_unit)))
in ((typing_pred), (_177_1332)))
in (FStar_SMTEncoding_Term.mkImp _177_1333))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_177_1334)))
in (mkForall_fuel _177_1335))
in ((_177_1336), (Some ("unit inversion")), (Some ("unit_inversion"))))
in FStar_SMTEncoding_Term.Assume (_177_1337))
in (_177_1338)::[])
in (_177_1340)::_177_1339))))
in (

let mk_bool = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Bool_sort))
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _177_1363 = (let _177_1354 = (let _177_1353 = (let _177_1352 = (let _177_1351 = (let _177_1348 = (let _177_1347 = (FStar_SMTEncoding_Term.boxBool b)
in (_177_1347)::[])
in (_177_1348)::[])
in (let _177_1350 = (let _177_1349 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType _177_1349 tt))
in ((_177_1351), ((bb)::[]), (_177_1350))))
in (FStar_SMTEncoding_Term.mkForall _177_1352))
in ((_177_1353), (Some ("bool typing")), (Some ("bool_typing"))))
in FStar_SMTEncoding_Term.Assume (_177_1354))
in (let _177_1362 = (let _177_1361 = (let _177_1360 = (let _177_1359 = (let _177_1358 = (let _177_1357 = (let _177_1356 = (let _177_1355 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in ((typing_pred), (_177_1355)))
in (FStar_SMTEncoding_Term.mkImp _177_1356))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_177_1357)))
in (mkForall_fuel _177_1358))
in ((_177_1359), (Some ("bool inversion")), (Some ("bool_inversion"))))
in FStar_SMTEncoding_Term.Assume (_177_1360))
in (_177_1361)::[])
in (_177_1363)::_177_1362))))))
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

let precedes = (let _177_1377 = (let _177_1376 = (let _177_1375 = (let _177_1374 = (let _177_1373 = (let _177_1372 = (FStar_SMTEncoding_Term.boxInt a)
in (let _177_1371 = (let _177_1370 = (FStar_SMTEncoding_Term.boxInt b)
in (_177_1370)::[])
in (_177_1372)::_177_1371))
in (tt)::_177_1373)
in (tt)::_177_1374)
in (("Prims.Precedes"), (_177_1375)))
in (FStar_SMTEncoding_Term.mkApp _177_1376))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _177_1377))
in (

let precedes_y_x = (let _177_1378 = (FStar_SMTEncoding_Term.mkApp (("Precedes"), ((y)::(x)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _177_1378))
in (let _177_1420 = (let _177_1386 = (let _177_1385 = (let _177_1384 = (let _177_1383 = (let _177_1380 = (let _177_1379 = (FStar_SMTEncoding_Term.boxInt b)
in (_177_1379)::[])
in (_177_1380)::[])
in (let _177_1382 = (let _177_1381 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType _177_1381 tt))
in ((_177_1383), ((bb)::[]), (_177_1382))))
in (FStar_SMTEncoding_Term.mkForall _177_1384))
in ((_177_1385), (Some ("int typing")), (Some ("int_typing"))))
in FStar_SMTEncoding_Term.Assume (_177_1386))
in (let _177_1419 = (let _177_1418 = (let _177_1392 = (let _177_1391 = (let _177_1390 = (let _177_1389 = (let _177_1388 = (let _177_1387 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in ((typing_pred), (_177_1387)))
in (FStar_SMTEncoding_Term.mkImp _177_1388))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_177_1389)))
in (mkForall_fuel _177_1390))
in ((_177_1391), (Some ("int inversion")), (Some ("int_inversion"))))
in FStar_SMTEncoding_Term.Assume (_177_1392))
in (let _177_1417 = (let _177_1416 = (let _177_1415 = (let _177_1414 = (let _177_1413 = (let _177_1412 = (let _177_1411 = (let _177_1410 = (let _177_1409 = (let _177_1408 = (let _177_1407 = (let _177_1406 = (let _177_1395 = (let _177_1394 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1393 = (FStar_SMTEncoding_Term.mkInteger' 0)
in ((_177_1394), (_177_1393))))
in (FStar_SMTEncoding_Term.mkGT _177_1395))
in (let _177_1405 = (let _177_1404 = (let _177_1398 = (let _177_1397 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _177_1396 = (FStar_SMTEncoding_Term.mkInteger' 0)
in ((_177_1397), (_177_1396))))
in (FStar_SMTEncoding_Term.mkGTE _177_1398))
in (let _177_1403 = (let _177_1402 = (let _177_1401 = (let _177_1400 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _177_1399 = (FStar_SMTEncoding_Term.unboxInt x)
in ((_177_1400), (_177_1399))))
in (FStar_SMTEncoding_Term.mkLT _177_1401))
in (_177_1402)::[])
in (_177_1404)::_177_1403))
in (_177_1406)::_177_1405))
in (typing_pred_y)::_177_1407)
in (typing_pred)::_177_1408)
in (FStar_SMTEncoding_Term.mk_and_l _177_1409))
in ((_177_1410), (precedes_y_x)))
in (FStar_SMTEncoding_Term.mkImp _177_1411))
in ((((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[]), ((xx)::(yy)::[]), (_177_1412)))
in (mkForall_fuel _177_1413))
in ((_177_1414), (Some ("well-founded ordering on nat (alt)")), (Some ("well-founded-ordering-on-nat"))))
in FStar_SMTEncoding_Term.Assume (_177_1415))
in (_177_1416)::[])
in (_177_1418)::_177_1417))
in (_177_1420)::_177_1419)))))))))))
in (

let mk_str = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.String_sort))
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _177_1443 = (let _177_1434 = (let _177_1433 = (let _177_1432 = (let _177_1431 = (let _177_1428 = (let _177_1427 = (FStar_SMTEncoding_Term.boxString b)
in (_177_1427)::[])
in (_177_1428)::[])
in (let _177_1430 = (let _177_1429 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType _177_1429 tt))
in ((_177_1431), ((bb)::[]), (_177_1430))))
in (FStar_SMTEncoding_Term.mkForall _177_1432))
in ((_177_1433), (Some ("string typing")), (Some ("string_typing"))))
in FStar_SMTEncoding_Term.Assume (_177_1434))
in (let _177_1442 = (let _177_1441 = (let _177_1440 = (let _177_1439 = (let _177_1438 = (let _177_1437 = (let _177_1436 = (let _177_1435 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in ((typing_pred), (_177_1435)))
in (FStar_SMTEncoding_Term.mkImp _177_1436))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_177_1437)))
in (mkForall_fuel _177_1438))
in ((_177_1439), (Some ("string inversion")), (Some ("string_inversion"))))
in FStar_SMTEncoding_Term.Assume (_177_1440))
in (_177_1441)::[])
in (_177_1443)::_177_1442))))))
in (

let mk_ref = (fun env reft_name _85_1893 -> (

let r = (("r"), (FStar_SMTEncoding_Term.Ref_sort))
in (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let refa = (let _177_1452 = (let _177_1451 = (let _177_1450 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (_177_1450)::[])
in ((reft_name), (_177_1451)))
in (FStar_SMTEncoding_Term.mkApp _177_1452))
in (

let refb = (let _177_1455 = (let _177_1454 = (let _177_1453 = (FStar_SMTEncoding_Term.mkFreeV bb)
in (_177_1453)::[])
in ((reft_name), (_177_1454)))
in (FStar_SMTEncoding_Term.mkApp _177_1455))
in (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (

let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (let _177_1474 = (let _177_1461 = (let _177_1460 = (let _177_1459 = (let _177_1458 = (let _177_1457 = (let _177_1456 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in ((typing_pred), (_177_1456)))
in (FStar_SMTEncoding_Term.mkImp _177_1457))
in ((((typing_pred)::[])::[]), ((xx)::(aa)::[]), (_177_1458)))
in (mkForall_fuel _177_1459))
in ((_177_1460), (Some ("ref inversion")), (Some ("ref_inversion"))))
in FStar_SMTEncoding_Term.Assume (_177_1461))
in (let _177_1473 = (let _177_1472 = (let _177_1471 = (let _177_1470 = (let _177_1469 = (let _177_1468 = (let _177_1467 = (let _177_1466 = (FStar_SMTEncoding_Term.mkAnd ((typing_pred), (typing_pred_b)))
in (let _177_1465 = (let _177_1464 = (let _177_1463 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (let _177_1462 = (FStar_SMTEncoding_Term.mkFreeV bb)
in ((_177_1463), (_177_1462))))
in (FStar_SMTEncoding_Term.mkEq _177_1464))
in ((_177_1466), (_177_1465))))
in (FStar_SMTEncoding_Term.mkImp _177_1467))
in ((((typing_pred)::(typing_pred_b)::[])::[]), ((xx)::(aa)::(bb)::[]), (_177_1468)))
in (mkForall_fuel' 2 _177_1469))
in ((_177_1470), (Some ("ref typing is injective")), (Some ("ref_injectivity"))))
in FStar_SMTEncoding_Term.Assume (_177_1471))
in (_177_1472)::[])
in (_177_1474)::_177_1473))))))))))
in (

let mk_false_interp = (fun env nm false_tm -> (

let valid = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((false_tm)::[])))
in (let _177_1483 = (let _177_1482 = (let _177_1481 = (FStar_SMTEncoding_Term.mkIff ((FStar_SMTEncoding_Term.mkFalse), (valid)))
in ((_177_1481), (Some ("False interpretation")), (Some ("false_interp"))))
in FStar_SMTEncoding_Term.Assume (_177_1482))
in (_177_1483)::[])))
in (

let mk_and_interp = (fun env conj _85_1910 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (

let valid = (let _177_1492 = (let _177_1491 = (let _177_1490 = (FStar_SMTEncoding_Term.mkApp ((conj), ((a)::(b)::[])))
in (_177_1490)::[])
in (("Valid"), (_177_1491)))
in (FStar_SMTEncoding_Term.mkApp _177_1492))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((b)::[])))
in (let _177_1499 = (let _177_1498 = (let _177_1497 = (let _177_1496 = (let _177_1495 = (let _177_1494 = (let _177_1493 = (FStar_SMTEncoding_Term.mkAnd ((valid_a), (valid_b)))
in ((_177_1493), (valid)))
in (FStar_SMTEncoding_Term.mkIff _177_1494))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_177_1495)))
in (FStar_SMTEncoding_Term.mkForall _177_1496))
in ((_177_1497), (Some ("/\\ interpretation")), (Some ("l_and-interp"))))
in FStar_SMTEncoding_Term.Assume (_177_1498))
in (_177_1499)::[])))))))))
in (

let mk_or_interp = (fun env disj _85_1922 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (

let valid = (let _177_1508 = (let _177_1507 = (let _177_1506 = (FStar_SMTEncoding_Term.mkApp ((disj), ((a)::(b)::[])))
in (_177_1506)::[])
in (("Valid"), (_177_1507)))
in (FStar_SMTEncoding_Term.mkApp _177_1508))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((b)::[])))
in (let _177_1515 = (let _177_1514 = (let _177_1513 = (let _177_1512 = (let _177_1511 = (let _177_1510 = (let _177_1509 = (FStar_SMTEncoding_Term.mkOr ((valid_a), (valid_b)))
in ((_177_1509), (valid)))
in (FStar_SMTEncoding_Term.mkIff _177_1510))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_177_1511)))
in (FStar_SMTEncoding_Term.mkForall _177_1512))
in ((_177_1513), (Some ("\\/ interpretation")), (Some ("l_or-interp"))))
in FStar_SMTEncoding_Term.Assume (_177_1514))
in (_177_1515)::[])))))))))
in (

let mk_eq2_interp = (fun env eq2 tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let yy = (("y"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (

let y = (FStar_SMTEncoding_Term.mkFreeV yy)
in (

let valid = (let _177_1524 = (let _177_1523 = (let _177_1522 = (FStar_SMTEncoding_Term.mkApp ((eq2), ((a)::(x)::(y)::[])))
in (_177_1522)::[])
in (("Valid"), (_177_1523)))
in (FStar_SMTEncoding_Term.mkApp _177_1524))
in (let _177_1531 = (let _177_1530 = (let _177_1529 = (let _177_1528 = (let _177_1527 = (let _177_1526 = (let _177_1525 = (FStar_SMTEncoding_Term.mkEq ((x), (y)))
in ((_177_1525), (valid)))
in (FStar_SMTEncoding_Term.mkIff _177_1526))
in ((((valid)::[])::[]), ((aa)::(xx)::(yy)::[]), (_177_1527)))
in (FStar_SMTEncoding_Term.mkForall _177_1528))
in ((_177_1529), (Some ("Eq2 interpretation")), (Some ("eq2-interp"))))
in FStar_SMTEncoding_Term.Assume (_177_1530))
in (_177_1531)::[])))))))))
in (

let mk_eq3_interp = (fun env eq3 tt -> (

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

let valid = (let _177_1540 = (let _177_1539 = (let _177_1538 = (FStar_SMTEncoding_Term.mkApp ((eq3), ((a)::(b)::(x)::(y)::[])))
in (_177_1538)::[])
in (("Valid"), (_177_1539)))
in (FStar_SMTEncoding_Term.mkApp _177_1540))
in (let _177_1547 = (let _177_1546 = (let _177_1545 = (let _177_1544 = (let _177_1543 = (let _177_1542 = (let _177_1541 = (FStar_SMTEncoding_Term.mkEq ((x), (y)))
in ((_177_1541), (valid)))
in (FStar_SMTEncoding_Term.mkIff _177_1542))
in ((((valid)::[])::[]), ((aa)::(bb)::(xx)::(yy)::[]), (_177_1543)))
in (FStar_SMTEncoding_Term.mkForall _177_1544))
in ((_177_1545), (Some ("Eq3 interpretation")), (Some ("eq3-interp"))))
in FStar_SMTEncoding_Term.Assume (_177_1546))
in (_177_1547)::[])))))))))))
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

let valid = (let _177_1556 = (let _177_1555 = (let _177_1554 = (FStar_SMTEncoding_Term.mkApp ((imp), ((a)::(b)::[])))
in (_177_1554)::[])
in (("Valid"), (_177_1555)))
in (FStar_SMTEncoding_Term.mkApp _177_1556))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((b)::[])))
in (let _177_1563 = (let _177_1562 = (let _177_1561 = (let _177_1560 = (let _177_1559 = (let _177_1558 = (let _177_1557 = (FStar_SMTEncoding_Term.mkImp ((valid_a), (valid_b)))
in ((_177_1557), (valid)))
in (FStar_SMTEncoding_Term.mkIff _177_1558))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_177_1559)))
in (FStar_SMTEncoding_Term.mkForall _177_1560))
in ((_177_1561), (Some ("==> interpretation")), (Some ("l_imp-interp"))))
in FStar_SMTEncoding_Term.Assume (_177_1562))
in (_177_1563)::[])))))))))
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

let valid = (let _177_1572 = (let _177_1571 = (let _177_1570 = (FStar_SMTEncoding_Term.mkApp ((iff), ((a)::(b)::[])))
in (_177_1570)::[])
in (("Valid"), (_177_1571)))
in (FStar_SMTEncoding_Term.mkApp _177_1572))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((b)::[])))
in (let _177_1579 = (let _177_1578 = (let _177_1577 = (let _177_1576 = (let _177_1575 = (let _177_1574 = (let _177_1573 = (FStar_SMTEncoding_Term.mkIff ((valid_a), (valid_b)))
in ((_177_1573), (valid)))
in (FStar_SMTEncoding_Term.mkIff _177_1574))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_177_1575)))
in (FStar_SMTEncoding_Term.mkForall _177_1576))
in ((_177_1577), (Some ("<==> interpretation")), (Some ("l_iff-interp"))))
in FStar_SMTEncoding_Term.Assume (_177_1578))
in (_177_1579)::[])))))))))
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

let valid = (let _177_1588 = (let _177_1587 = (let _177_1586 = (FStar_SMTEncoding_Term.mkApp ((for_all), ((a)::(b)::[])))
in (_177_1586)::[])
in (("Valid"), (_177_1587)))
in (FStar_SMTEncoding_Term.mkApp _177_1588))
in (

let valid_b_x = (let _177_1591 = (let _177_1590 = (let _177_1589 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_177_1589)::[])
in (("Valid"), (_177_1590)))
in (FStar_SMTEncoding_Term.mkApp _177_1591))
in (let _177_1605 = (let _177_1604 = (let _177_1603 = (let _177_1602 = (let _177_1601 = (let _177_1600 = (let _177_1599 = (let _177_1598 = (let _177_1597 = (let _177_1593 = (let _177_1592 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_177_1592)::[])
in (_177_1593)::[])
in (let _177_1596 = (let _177_1595 = (let _177_1594 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((_177_1594), (valid_b_x)))
in (FStar_SMTEncoding_Term.mkImp _177_1595))
in ((_177_1597), ((xx)::[]), (_177_1596))))
in (FStar_SMTEncoding_Term.mkForall _177_1598))
in ((_177_1599), (valid)))
in (FStar_SMTEncoding_Term.mkIff _177_1600))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_177_1601)))
in (FStar_SMTEncoding_Term.mkForall _177_1602))
in ((_177_1603), (Some ("forall interpretation")), (Some ("forall-interp"))))
in FStar_SMTEncoding_Term.Assume (_177_1604))
in (_177_1605)::[]))))))))))
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

let valid = (let _177_1614 = (let _177_1613 = (let _177_1612 = (FStar_SMTEncoding_Term.mkApp ((for_some), ((a)::(b)::[])))
in (_177_1612)::[])
in (("Valid"), (_177_1613)))
in (FStar_SMTEncoding_Term.mkApp _177_1614))
in (

let valid_b_x = (let _177_1617 = (let _177_1616 = (let _177_1615 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_177_1615)::[])
in (("Valid"), (_177_1616)))
in (FStar_SMTEncoding_Term.mkApp _177_1617))
in (let _177_1631 = (let _177_1630 = (let _177_1629 = (let _177_1628 = (let _177_1627 = (let _177_1626 = (let _177_1625 = (let _177_1624 = (let _177_1623 = (let _177_1619 = (let _177_1618 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_177_1618)::[])
in (_177_1619)::[])
in (let _177_1622 = (let _177_1621 = (let _177_1620 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((_177_1620), (valid_b_x)))
in (FStar_SMTEncoding_Term.mkImp _177_1621))
in ((_177_1623), ((xx)::[]), (_177_1622))))
in (FStar_SMTEncoding_Term.mkExists _177_1624))
in ((_177_1625), (valid)))
in (FStar_SMTEncoding_Term.mkIff _177_1626))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_177_1627)))
in (FStar_SMTEncoding_Term.mkForall _177_1628))
in ((_177_1629), (Some ("exists interpretation")), (Some ("exists-interp"))))
in FStar_SMTEncoding_Term.Assume (_177_1630))
in (_177_1631)::[]))))))))))
in (

let mk_range_interp = (fun env range tt -> (

let range_ty = (FStar_SMTEncoding_Term.mkApp ((range), ([])))
in (let _177_1642 = (let _177_1641 = (let _177_1640 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_ty)
in (let _177_1639 = (let _177_1638 = (varops.mk_unique "typing_range_const")
in Some (_177_1638))
in ((_177_1640), (Some ("Range_const typing")), (_177_1639))))
in FStar_SMTEncoding_Term.Assume (_177_1641))
in (_177_1642)::[])))
in (

let prims = (((FStar_Syntax_Const.unit_lid), (mk_unit)))::(((FStar_Syntax_Const.bool_lid), (mk_bool)))::(((FStar_Syntax_Const.int_lid), (mk_int)))::(((FStar_Syntax_Const.string_lid), (mk_str)))::(((FStar_Syntax_Const.ref_lid), (mk_ref)))::(((FStar_Syntax_Const.false_lid), (mk_false_interp)))::(((FStar_Syntax_Const.and_lid), (mk_and_interp)))::(((FStar_Syntax_Const.or_lid), (mk_or_interp)))::(((FStar_Syntax_Const.eq2_lid), (mk_eq2_interp)))::(((FStar_Syntax_Const.eq3_lid), (mk_eq3_interp)))::(((FStar_Syntax_Const.imp_lid), (mk_imp_interp)))::(((FStar_Syntax_Const.iff_lid), (mk_iff_interp)))::(((FStar_Syntax_Const.forall_lid), (mk_forall_interp)))::(((FStar_Syntax_Const.exists_lid), (mk_exists_interp)))::(((FStar_Syntax_Const.range_lid), (mk_range_interp)))::[]
in (fun env t s tt -> (match ((FStar_Util.find_opt (fun _85_2015 -> (match (_85_2015) with
| (l, _85_2014) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_85_2018, f) -> begin
(f env s tt)
end))))))))))))))))))))))


let encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let _85_2028 = (encode_function_type_as_formula None None t env)
in (match (_85_2028) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_SMTEncoding_Term.Assume (((form), (Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str))), (Some ((Prims.strcat "lemma_" lid.FStar_Ident.str))))))::[]))
end))))


let encode_free_var : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env fv tt t_norm quals -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if ((let _177_1841 = (FStar_Syntax_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _177_1841)) || (FStar_Syntax_Util.is_lemma t_norm)) then begin
(

let _85_2038 = (new_term_constant_and_tok_from_lid env lid)
in (match (_85_2038) with
| (vname, vtok, env) -> begin
(

let arg_sorts = (match ((let _177_1842 = (FStar_Syntax_Subst.compress t_norm)
in _177_1842.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _85_2041) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun _85_2044 -> FStar_SMTEncoding_Term.Term_sort)))
end
| _85_2047 -> begin
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

let _85_2054 = (prims.mk lid vname)
in (match (_85_2054) with
| (tok, definition) -> begin
(

let env = (push_free_var env lid vname (Some (tok)))
in ((definition), (env)))
end)))
end else begin
(

let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (

let _85_2064 = (

let _85_2059 = (curried_arrow_formals_comp t_norm)
in (match (_85_2059) with
| (args, comp) -> begin
if encode_non_total_function_typ then begin
(let _177_1844 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in ((args), (_177_1844)))
end else begin
((args), (((None), ((FStar_Syntax_Util.comp_result comp)))))
end
end))
in (match (_85_2064) with
| (formals, (pre_opt, res_t)) -> begin
(

let _85_2068 = (new_term_constant_and_tok_from_lid env lid)
in (match (_85_2068) with
| (vname, vtok, env) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
end
| _85_2071 -> begin
(FStar_SMTEncoding_Term.mkApp ((vtok), ([])))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun _85_14 -> (match (_85_14) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(

let _85_2087 = (FStar_Util.prefix vars)
in (match (_85_2087) with
| (_85_2082, (xxsym, _85_2085)) -> begin
(

let xx = (FStar_SMTEncoding_Term.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (let _177_1861 = (let _177_1860 = (let _177_1859 = (let _177_1858 = (let _177_1857 = (let _177_1856 = (let _177_1855 = (let _177_1854 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1854))
in ((vapp), (_177_1855)))
in (FStar_SMTEncoding_Term.mkEq _177_1856))
in ((((vapp)::[])::[]), (vars), (_177_1857)))
in (FStar_SMTEncoding_Term.mkForall _177_1858))
in ((_177_1859), (Some ("Discriminator equation")), (Some ((Prims.strcat "disc_equation_" (escape d.FStar_Ident.str))))))
in FStar_SMTEncoding_Term.Assume (_177_1860))
in (_177_1861)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(

let _85_2099 = (FStar_Util.prefix vars)
in (match (_85_2099) with
| (_85_2094, (xxsym, _85_2097)) -> begin
(

let xx = (FStar_SMTEncoding_Term.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = 0; FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (

let tp_name = (mk_term_projector_name d f)
in (

let prim_app = (FStar_SMTEncoding_Term.mkApp ((tp_name), ((xx)::[])))
in (let _177_1866 = (let _177_1865 = (let _177_1864 = (let _177_1863 = (let _177_1862 = (FStar_SMTEncoding_Term.mkEq ((vapp), (prim_app)))
in ((((vapp)::[])::[]), (vars), (_177_1862)))
in (FStar_SMTEncoding_Term.mkForall _177_1863))
in ((_177_1864), (Some ("Projector equation")), (Some ((Prims.strcat "proj_equation_" tp_name)))))
in FStar_SMTEncoding_Term.Assume (_177_1865))
in (_177_1866)::[])))))
end))
end
| _85_2105 -> begin
[]
end)))))
in (

let _85_2112 = (encode_binders None formals env)
in (match (_85_2112) with
| (vars, guards, env', decls1, _85_2111) -> begin
(

let _85_2121 = (match (pre_opt) with
| None -> begin
(let _177_1867 = (FStar_SMTEncoding_Term.mk_and_l guards)
in ((_177_1867), (decls1)))
end
| Some (p) -> begin
(

let _85_2118 = (encode_formula p env')
in (match (_85_2118) with
| (g, ds) -> begin
(let _177_1868 = (FStar_SMTEncoding_Term.mk_and_l ((g)::guards))
in ((_177_1868), ((FStar_List.append decls1 ds))))
end))
end)
in (match (_85_2121) with
| (guard, decls1) -> begin
(

let vtok_app = (mk_Apply vtok_tm vars)
in (

let vapp = (let _177_1870 = (let _177_1869 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in ((vname), (_177_1869)))
in (FStar_SMTEncoding_Term.mkApp _177_1870))
in (

let _85_2145 = (

let vname_decl = (let _177_1873 = (let _177_1872 = (FStar_All.pipe_right formals (FStar_List.map (fun _85_2124 -> FStar_SMTEncoding_Term.Term_sort)))
in ((vname), (_177_1872), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (_177_1873))
in (

let _85_2132 = (

let env = (

let _85_2127 = env
in {bindings = _85_2127.bindings; depth = _85_2127.depth; tcenv = _85_2127.tcenv; warn = _85_2127.warn; cache = _85_2127.cache; nolabels = _85_2127.nolabels; use_zfuel_name = _85_2127.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in if (not ((head_normal env tt))) then begin
(encode_term_pred None tt env vtok_tm)
end else begin
(encode_term_pred None t_norm env vtok_tm)
end)
in (match (_85_2132) with
| (tok_typing, decls2) -> begin
(

let tok_typing = FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("function token typing")), (Some ((Prims.strcat "function_token_typing_" vname)))))
in (

let _85_2142 = (match (formals) with
| [] -> begin
(let _177_1877 = (let _177_1876 = (let _177_1875 = (FStar_SMTEncoding_Term.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left (fun _177_1874 -> Some (_177_1874)) _177_1875))
in (push_free_var env lid vname _177_1876))
in (((FStar_List.append decls2 ((tok_typing)::[]))), (_177_1877)))
end
| _85_2136 -> begin
(

let vtok_decl = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let vtok_fresh = (let _177_1878 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((vtok), (FStar_SMTEncoding_Term.Term_sort)) _177_1878))
in (

let name_tok_corr = (let _177_1882 = (let _177_1881 = (let _177_1880 = (let _177_1879 = (FStar_SMTEncoding_Term.mkEq ((vtok_app), (vapp)))
in ((((vtok_app)::[])::[]), (vars), (_177_1879)))
in (FStar_SMTEncoding_Term.mkForall _177_1880))
in ((_177_1881), (Some ("Name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" vname)))))
in FStar_SMTEncoding_Term.Assume (_177_1882))
in (((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[]))), (env)))))
end)
in (match (_85_2142) with
| (tok_decl, env) -> begin
(((vname_decl)::tok_decl), (env))
end)))
end)))
in (match (_85_2145) with
| (decls2, env) -> begin
(

let _85_2153 = (

let res_t = (FStar_Syntax_Subst.compress res_t)
in (

let _85_2149 = (encode_term res_t env')
in (match (_85_2149) with
| (encoded_res_t, decls) -> begin
(let _177_1883 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in ((encoded_res_t), (_177_1883), (decls)))
end)))
in (match (_85_2153) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (let _177_1887 = (let _177_1886 = (let _177_1885 = (let _177_1884 = (FStar_SMTEncoding_Term.mkImp ((guard), (ty_pred)))
in ((((vapp)::[])::[]), (vars), (_177_1884)))
in (FStar_SMTEncoding_Term.mkForall _177_1885))
in ((_177_1886), (Some ("free var typing")), (Some ((Prims.strcat "typing_" vname)))))
in FStar_SMTEncoding_Term.Assume (_177_1887))
in (

let freshness = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New)) then begin
(let _177_1893 = (let _177_1890 = (let _177_1889 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (let _177_1888 = (varops.next_id ())
in ((vname), (_177_1889), (FStar_SMTEncoding_Term.Term_sort), (_177_1888))))
in (FStar_SMTEncoding_Term.fresh_constructor _177_1890))
in (let _177_1892 = (let _177_1891 = (pretype_axiom vapp vars)
in (_177_1891)::[])
in (_177_1893)::_177_1892))
end else begin
[]
end
in (

let g = (let _177_1898 = (let _177_1897 = (let _177_1896 = (let _177_1895 = (let _177_1894 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_177_1894)
in (FStar_List.append freshness _177_1895))
in (FStar_List.append decls3 _177_1896))
in (FStar_List.append decls2 _177_1897))
in (FStar_List.append decls1 _177_1898))
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

let _85_2164 = (encode_free_var env x t t_norm [])
in (match (_85_2164) with
| (decls, env) -> begin
(

let _85_2169 = (lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_85_2169) with
| (n, x', _85_2168) -> begin
((((n), (x'))), (decls), (env))
end))
end))
end
| Some (n, x, _85_2173) -> begin
((((n), (x))), ([]), (env))
end))


let encode_top_level_val : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env lid t quals -> (

let tt = (norm env t)
in (

let _85_2183 = (encode_free_var env lid t tt quals)
in (match (_85_2183) with
| (decls, env) -> begin
if (FStar_Syntax_Util.is_smt_lemma t) then begin
(let _177_1916 = (let _177_1915 = (encode_smt_lemma env lid tt)
in (FStar_List.append decls _177_1915))
in ((_177_1916), (env)))
end else begin
((decls), (env))
end
end))))


let encode_top_level_vals : env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _85_2189 lb -> (match (_85_2189) with
| (decls, env) -> begin
(

let _85_2193 = (let _177_1925 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env _177_1925 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (_85_2193) with
| (decls', env) -> begin
(((FStar_List.append decls decls')), (env))
end))
end)) (([]), (env)))))


let encode_top_level_let : env_t  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env _85_2197 quals -> (match (_85_2197) with
| (is_rec, bindings) -> begin
(

let eta_expand = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let _85_2207 = (FStar_Util.first_N nbinders formals)
in (match (_85_2207) with
| (formals, extra_formals) -> begin
(

let subst = (FStar_List.map2 (fun _85_2211 _85_2215 -> (match (((_85_2211), (_85_2215))) with
| ((formal, _85_2210), (binder, _85_2214)) -> begin
(let _177_1943 = (let _177_1942 = (FStar_Syntax_Syntax.bv_to_name binder)
in ((formal), (_177_1942)))
in FStar_Syntax_Syntax.NT (_177_1943))
end)) formals binders)
in (

let extra_formals = (let _177_1947 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun _85_2219 -> (match (_85_2219) with
| (x, i) -> begin
(let _177_1946 = (

let _85_2220 = x
in (let _177_1945 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _85_2220.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _85_2220.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _177_1945}))
in ((_177_1946), (i)))
end))))
in (FStar_All.pipe_right _177_1947 FStar_Syntax_Util.name_binders))
in (

let body = (let _177_1954 = (FStar_Syntax_Subst.compress body)
in (let _177_1953 = (let _177_1948 = (FStar_Syntax_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _177_1948))
in (let _177_1952 = (let _177_1951 = (let _177_1950 = (FStar_Syntax_Subst.subst subst t)
in _177_1950.FStar_Syntax_Syntax.n)
in (FStar_All.pipe_left (fun _177_1949 -> Some (_177_1949)) _177_1951))
in (FStar_Syntax_Syntax.extend_app_n _177_1954 _177_1953 _177_1952 body.FStar_Syntax_Syntax.pos))))
in (((FStar_List.append binders extra_formals)), (body)))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (

let rec aux = (fun norm t_norm -> (match ((let _177_1965 = (FStar_Syntax_Util.unascribe e)
in _177_1965.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, lopt) -> begin
(

let _85_2239 = (FStar_Syntax_Subst.open_term' binders body)
in (match (_85_2239) with
| (binders, body, opening) -> begin
(match ((let _177_1966 = (FStar_Syntax_Subst.compress t_norm)
in _177_1966.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let _85_2246 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_85_2246) with
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

let _85_2253 = (FStar_Util.first_N nformals binders)
in (match (_85_2253) with
| (bs0, rest) -> begin
(

let c = (

let subst = (FStar_List.map2 (fun _85_2257 _85_2261 -> (match (((_85_2257), (_85_2261))) with
| ((b, _85_2256), (x, _85_2260)) -> begin
(let _177_1970 = (let _177_1969 = (FStar_Syntax_Syntax.bv_to_name x)
in ((b), (_177_1969)))
in FStar_Syntax_Syntax.NT (_177_1970))
end)) bs0 formals)
in (FStar_Syntax_Subst.subst_comp subst c))
in (

let body = (FStar_Syntax_Util.abs rest body lopt)
in ((bs0), (body), (bs0), ((FStar_Syntax_Util.comp_result c)))))
end)))
end else begin
if (nformals > nbinders) then begin
(

let _85_2267 = (eta_expand binders formals body tres)
in (match (_85_2267) with
| (binders, body) -> begin
((binders), (body), (formals), (tres))
end))
end else begin
((binders), (body), (formals), (tres))
end
end)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, _85_2270) -> begin
(aux norm x.FStar_Syntax_Syntax.sort)
end
| _85_2274 when (not (norm)) -> begin
(

let t_norm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm)
in (aux true t_norm))
end
| _85_2277 -> begin
(let _177_1973 = (let _177_1972 = (FStar_Syntax_Print.term_to_string e)
in (let _177_1971 = (FStar_Syntax_Print.term_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str _177_1972 _177_1971)))
in (FStar_All.failwith _177_1973))
end)
end))
end
| _85_2279 -> begin
(match ((let _177_1974 = (FStar_Syntax_Subst.compress t_norm)
in _177_1974.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let _85_2286 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_85_2286) with
| (formals, c) -> begin
(

let tres = (FStar_Syntax_Util.comp_result c)
in (

let _85_2290 = (eta_expand [] formals e tres)
in (match (_85_2290) with
| (binders, body) -> begin
((binders), (body), (formals), (tres))
end)))
end))
end
| _85_2292 -> begin
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

let _85_2320 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _85_2307 lb -> (match (_85_2307) with
| (toks, typs, decls, env) -> begin
(

let _85_2309 = if (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) then begin
(Prims.raise Let_rec_unencodeable)
end else begin
()
end
in (

let t_norm = (whnf env lb.FStar_Syntax_Syntax.lbtyp)
in (

let _85_2315 = (let _177_1979 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env _177_1979 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (_85_2315) with
| (tok, decl, env) -> begin
(let _177_1982 = (let _177_1981 = (let _177_1980 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in ((_177_1980), (tok)))
in (_177_1981)::toks)
in ((_177_1982), ((t_norm)::typs), ((decl)::decls), (env)))
end))))
end)) (([]), ([]), ([]), (env))))
in (match (_85_2320) with
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
| _85_2327 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> (let _177_1985 = (FStar_Syntax_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _177_1985)))))) then begin
((decls), (env))
end else begin
if (not (is_rec)) then begin
(match (((bindings), (typs), (toks))) with
| (({FStar_Syntax_Syntax.lbname = _85_2337; FStar_Syntax_Syntax.lbunivs = _85_2335; FStar_Syntax_Syntax.lbtyp = _85_2333; FStar_Syntax_Syntax.lbeff = _85_2331; FStar_Syntax_Syntax.lbdef = e})::[], (t_norm)::[], ((flid_fv, (f, ftok)))::[]) -> begin
(

let e = (FStar_Syntax_Subst.compress e)
in (

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let _85_2357 = (destruct_bound_function flid t_norm e)
in (match (_85_2357) with
| (binders, body, _85_2354, _85_2356) -> begin
(

let _85_2364 = (encode_binders None binders env)
in (match (_85_2364) with
| (vars, guards, env', binder_decls, _85_2363) -> begin
(

let app = (match (vars) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
end
| _85_2367 -> begin
(let _177_1987 = (let _177_1986 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in ((f), (_177_1986)))
in (FStar_SMTEncoding_Term.mkApp _177_1987))
end)
in (

let _85_2373 = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic)) then begin
(let _177_1989 = (FStar_SMTEncoding_Term.mk_Valid app)
in (let _177_1988 = (encode_formula body env')
in ((_177_1989), (_177_1988))))
end else begin
(let _177_1990 = (encode_term body env')
in ((app), (_177_1990)))
end
in (match (_85_2373) with
| (app, (body, decls2)) -> begin
(

let eqn = (let _177_1996 = (let _177_1995 = (let _177_1992 = (let _177_1991 = (FStar_SMTEncoding_Term.mkEq ((app), (body)))
in ((((app)::[])::[]), (vars), (_177_1991)))
in (FStar_SMTEncoding_Term.mkForall _177_1992))
in (let _177_1994 = (let _177_1993 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (_177_1993))
in ((_177_1995), (_177_1994), (Some ((Prims.strcat "equation_" f))))))
in FStar_SMTEncoding_Term.Assume (_177_1996))
in (let _177_2001 = (let _177_2000 = (let _177_1999 = (let _177_1998 = (let _177_1997 = (primitive_type_axioms env.tcenv flid f app)
in (FStar_List.append ((eqn)::[]) _177_1997))
in (FStar_List.append decls2 _177_1998))
in (FStar_List.append binder_decls _177_1999))
in (FStar_List.append decls _177_2000))
in ((_177_2001), (env))))
end)))
end))
end))))
end
| _85_2376 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(

let fuel = (let _177_2002 = (varops.fresh "fuel")
in ((_177_2002), (FStar_SMTEncoding_Term.Fuel_sort)))
in (

let fuel_tm = (FStar_SMTEncoding_Term.mkFreeV fuel)
in (

let env0 = env
in (

let _85_2394 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _85_2382 _85_2387 -> (match (((_85_2382), (_85_2387))) with
| ((gtoks, env), (flid_fv, (f, ftok))) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let g = (let _177_2005 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented")
in (varops.new_fvar _177_2005))
in (

let gtok = (let _177_2006 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented_token")
in (varops.new_fvar _177_2006))
in (

let env = (let _177_2009 = (let _177_2008 = (FStar_SMTEncoding_Term.mkApp ((g), ((fuel_tm)::[])))
in (FStar_All.pipe_left (fun _177_2007 -> Some (_177_2007)) _177_2008))
in (push_free_var env flid gtok _177_2009))
in (((((flid), (f), (ftok), (g), (gtok)))::gtoks), (env))))))
end)) (([]), (env))))
in (match (_85_2394) with
| (gtoks, env) -> begin
(

let gtoks = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env0 _85_2403 t_norm _85_2414 -> (match (((_85_2403), (_85_2414))) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = _85_2413; FStar_Syntax_Syntax.lbunivs = _85_2411; FStar_Syntax_Syntax.lbtyp = _85_2409; FStar_Syntax_Syntax.lbeff = _85_2407; FStar_Syntax_Syntax.lbdef = e}) -> begin
(

let _85_2419 = (destruct_bound_function flid t_norm e)
in (match (_85_2419) with
| (binders, body, formals, tres) -> begin
(

let _85_2426 = (encode_binders None binders env)
in (match (_85_2426) with
| (vars, guards, env', binder_decls, _85_2425) -> begin
(

let decl_g = (let _177_2020 = (let _177_2019 = (let _177_2018 = (FStar_List.map Prims.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::_177_2018)
in ((g), (_177_2019), (FStar_SMTEncoding_Term.Term_sort), (Some ("Fuel-instrumented function name"))))
in FStar_SMTEncoding_Term.DeclFun (_177_2020))
in (

let env0 = (push_zfuel_name env0 flid g)
in (

let decl_g_tok = FStar_SMTEncoding_Term.DeclFun (((gtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Token for fuel-instrumented partial applications"))))
in (

let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (

let app = (FStar_SMTEncoding_Term.mkApp ((f), (vars_tm)))
in (

let gsapp = (let _177_2023 = (let _177_2022 = (let _177_2021 = (FStar_SMTEncoding_Term.mkApp (("SFuel"), ((fuel_tm)::[])))
in (_177_2021)::vars_tm)
in ((g), (_177_2022)))
in (FStar_SMTEncoding_Term.mkApp _177_2023))
in (

let gmax = (let _177_2026 = (let _177_2025 = (let _177_2024 = (FStar_SMTEncoding_Term.mkApp (("MaxFuel"), ([])))
in (_177_2024)::vars_tm)
in ((g), (_177_2025)))
in (FStar_SMTEncoding_Term.mkApp _177_2026))
in (

let _85_2436 = (encode_term body env')
in (match (_85_2436) with
| (body_tm, decls2) -> begin
(

let eqn_g = (let _177_2032 = (let _177_2031 = (let _177_2028 = (let _177_2027 = (FStar_SMTEncoding_Term.mkEq ((gsapp), (body_tm)))
in ((((gsapp)::[])::[]), (Some (0)), ((fuel)::vars), (_177_2027)))
in (FStar_SMTEncoding_Term.mkForall' _177_2028))
in (let _177_2030 = (let _177_2029 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (_177_2029))
in ((_177_2031), (_177_2030), (Some ((Prims.strcat "equation_with_fuel_" g))))))
in FStar_SMTEncoding_Term.Assume (_177_2032))
in (

let eqn_f = (let _177_2036 = (let _177_2035 = (let _177_2034 = (let _177_2033 = (FStar_SMTEncoding_Term.mkEq ((app), (gmax)))
in ((((app)::[])::[]), (vars), (_177_2033)))
in (FStar_SMTEncoding_Term.mkForall _177_2034))
in ((_177_2035), (Some ("Correspondence of recursive function to instrumented version")), (Some ((Prims.strcat "fuel_correspondence_" g)))))
in FStar_SMTEncoding_Term.Assume (_177_2036))
in (

let eqn_g' = (let _177_2045 = (let _177_2044 = (let _177_2043 = (let _177_2042 = (let _177_2041 = (let _177_2040 = (let _177_2039 = (let _177_2038 = (let _177_2037 = (FStar_SMTEncoding_Term.n_fuel 0)
in (_177_2037)::vars_tm)
in ((g), (_177_2038)))
in (FStar_SMTEncoding_Term.mkApp _177_2039))
in ((gsapp), (_177_2040)))
in (FStar_SMTEncoding_Term.mkEq _177_2041))
in ((((gsapp)::[])::[]), ((fuel)::vars), (_177_2042)))
in (FStar_SMTEncoding_Term.mkForall _177_2043))
in ((_177_2044), (Some ("Fuel irrelevance")), (Some ((Prims.strcat "fuel_irrelevance_" g)))))
in FStar_SMTEncoding_Term.Assume (_177_2045))
in (

let _85_2459 = (

let _85_2446 = (encode_binders None formals env0)
in (match (_85_2446) with
| (vars, v_guards, env, binder_decls, _85_2445) -> begin
(

let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (

let gapp = (FStar_SMTEncoding_Term.mkApp ((g), ((fuel_tm)::vars_tm)))
in (

let tok_corr = (

let tok_app = (let _177_2046 = (FStar_SMTEncoding_Term.mkFreeV ((gtok), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply _177_2046 ((fuel)::vars)))
in (let _177_2050 = (let _177_2049 = (let _177_2048 = (let _177_2047 = (FStar_SMTEncoding_Term.mkEq ((tok_app), (gapp)))
in ((((tok_app)::[])::[]), ((fuel)::vars), (_177_2047)))
in (FStar_SMTEncoding_Term.mkForall _177_2048))
in ((_177_2049), (Some ("Fuel token correspondence")), (Some ((Prims.strcat "fuel_token_correspondence_" gtok)))))
in FStar_SMTEncoding_Term.Assume (_177_2050)))
in (

let _85_2456 = (

let _85_2453 = (encode_term_pred None tres env gapp)
in (match (_85_2453) with
| (g_typing, d3) -> begin
(let _177_2058 = (let _177_2057 = (let _177_2056 = (let _177_2055 = (let _177_2054 = (let _177_2053 = (let _177_2052 = (let _177_2051 = (FStar_SMTEncoding_Term.mk_and_l v_guards)
in ((_177_2051), (g_typing)))
in (FStar_SMTEncoding_Term.mkImp _177_2052))
in ((((gapp)::[])::[]), ((fuel)::vars), (_177_2053)))
in (FStar_SMTEncoding_Term.mkForall _177_2054))
in ((_177_2055), (Some ("Typing correspondence of token to term")), (Some ((Prims.strcat "token_correspondence_" g)))))
in FStar_SMTEncoding_Term.Assume (_177_2056))
in (_177_2057)::[])
in ((d3), (_177_2058)))
end))
in (match (_85_2456) with
| (aux_decls, typing_corr) -> begin
(((FStar_List.append binder_decls aux_decls)), ((FStar_List.append typing_corr ((tok_corr)::[]))))
end)))))
end))
in (match (_85_2459) with
| (aux_decls, g_typing) -> begin
(((FStar_List.append binder_decls (FStar_List.append decls2 (FStar_List.append aux_decls ((decl_g)::(decl_g_tok)::[]))))), ((FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing)), (env0))
end)))))
end)))))))))
end))
end))
end))
in (

let _85_2475 = (let _177_2061 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _85_2463 _85_2467 -> (match (((_85_2463), (_85_2467))) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(

let _85_2471 = (encode_one_binding env0 gtok ty bs)
in (match (_85_2471) with
| (decls', eqns', env0) -> begin
(((decls')::decls), ((FStar_List.append eqns' eqns)), (env0))
end))
end)) (((decls)::[]), ([]), (env0)) _177_2061))
in (match (_85_2475) with
| (decls, eqns, env0) -> begin
(

let _85_2484 = (let _177_2063 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _177_2063 (FStar_List.partition (fun _85_16 -> (match (_85_16) with
| FStar_SMTEncoding_Term.DeclFun (_85_2478) -> begin
true
end
| _85_2481 -> begin
false
end)))))
in (match (_85_2484) with
| (prefix_decls, rest) -> begin
(

let eqns = (FStar_List.rev eqns)
in (((FStar_List.append prefix_decls (FStar_List.append rest eqns))), (env0)))
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

let msg = (let _177_2066 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _177_2066 (FStar_String.concat " and ")))
in (

let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in (((decl)::[]), (env))))
end))
end))


let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let _85_2488 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _177_2075 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _177_2075))
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

let _85_2496 = (encode_sigelt' env se)
in (match (_85_2496) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _177_2078 = (let _177_2077 = (let _177_2076 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (_177_2076))
in (_177_2077)::[])
in ((_177_2078), (e)))
end
| _85_2499 -> begin
(let _177_2085 = (let _177_2084 = (let _177_2080 = (let _177_2079 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_177_2079))
in (_177_2080)::g)
in (let _177_2083 = (let _177_2082 = (let _177_2081 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_177_2081))
in (_177_2082)::[])
in (FStar_List.append _177_2084 _177_2083)))
in ((_177_2085), (e)))
end)
end)))))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let should_skip = (fun l -> false)
in (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_85_2505) -> begin
(FStar_All.failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _85_2521) -> begin
if (let _177_2090 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right _177_2090 Prims.op_Negation)) then begin
(([]), (env))
end else begin
(

let close_effect_params = (fun tm -> (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
tm
end
| _85_2528 -> begin
(let _177_2096 = (let _177_2095 = (let _177_2094 = (FStar_All.pipe_left (fun _177_2093 -> Some (_177_2093)) (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid)))
in ((ed.FStar_Syntax_Syntax.binders), (tm), (_177_2094)))
in FStar_Syntax_Syntax.Tm_abs (_177_2095))
in (FStar_Syntax_Syntax.mk _177_2096 None tm.FStar_Syntax_Syntax.pos))
end))
in (

let encode_action = (fun env a -> (

let _85_2535 = (new_term_constant_and_tok_from_lid env a.FStar_Syntax_Syntax.action_name)
in (match (_85_2535) with
| (aname, atok, env) -> begin
(

let _85_2539 = (FStar_Syntax_Util.arrow_formals_comp a.FStar_Syntax_Syntax.action_typ)
in (match (_85_2539) with
| (formals, _85_2538) -> begin
(

let _85_2542 = (let _177_2101 = (close_effect_params a.FStar_Syntax_Syntax.action_defn)
in (encode_term _177_2101 env))
in (match (_85_2542) with
| (tm, decls) -> begin
(

let a_decls = (let _177_2105 = (let _177_2104 = (let _177_2103 = (FStar_All.pipe_right formals (FStar_List.map (fun _85_2543 -> FStar_SMTEncoding_Term.Term_sort)))
in ((aname), (_177_2103), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action"))))
in FStar_SMTEncoding_Term.DeclFun (_177_2104))
in (_177_2105)::(FStar_SMTEncoding_Term.DeclFun (((atok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action token")))))::[])
in (

let _85_2557 = (let _177_2107 = (FStar_All.pipe_right formals (FStar_List.map (fun _85_2549 -> (match (_85_2549) with
| (bv, _85_2548) -> begin
(

let _85_2554 = (gen_term_var env bv)
in (match (_85_2554) with
| (xxsym, xx, _85_2553) -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (xx))
end))
end))))
in (FStar_All.pipe_right _177_2107 FStar_List.split))
in (match (_85_2557) with
| (xs_sorts, xs) -> begin
(

let app = (let _177_2111 = (let _177_2110 = (let _177_2109 = (let _177_2108 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Var (aname)), (xs)))))
in (_177_2108)::[])
in ((FStar_SMTEncoding_Term.Var ("Reify")), (_177_2109)))
in FStar_SMTEncoding_Term.App (_177_2110))
in (FStar_All.pipe_right _177_2111 FStar_SMTEncoding_Term.mk))
in (

let a_eq = (let _177_2117 = (let _177_2116 = (let _177_2115 = (let _177_2114 = (let _177_2113 = (let _177_2112 = (mk_Apply tm xs_sorts)
in ((app), (_177_2112)))
in (FStar_SMTEncoding_Term.mkEq _177_2113))
in ((((app)::[])::[]), (xs_sorts), (_177_2114)))
in (FStar_SMTEncoding_Term.mkForall _177_2115))
in ((_177_2116), (Some ("Action equality")), (Some ((Prims.strcat aname "_equality")))))
in FStar_SMTEncoding_Term.Assume (_177_2117))
in (

let tok_correspondence = (

let tok_term = (FStar_SMTEncoding_Term.mkFreeV ((atok), (FStar_SMTEncoding_Term.Term_sort)))
in (

let tok_app = (mk_Apply tok_term xs_sorts)
in (let _177_2121 = (let _177_2120 = (let _177_2119 = (let _177_2118 = (FStar_SMTEncoding_Term.mkEq ((tok_app), (app)))
in ((((tok_app)::[])::[]), (xs_sorts), (_177_2118)))
in (FStar_SMTEncoding_Term.mkForall _177_2119))
in ((_177_2120), (Some ("Action token correspondence")), (Some ((Prims.strcat aname "_token_correspondence")))))
in FStar_SMTEncoding_Term.Assume (_177_2121))))
in ((env), ((FStar_List.append decls (FStar_List.append a_decls ((a_eq)::(tok_correspondence)::[]))))))))
end)))
end))
end))
end)))
in (

let _85_2565 = (FStar_Util.fold_map encode_action env ed.FStar_Syntax_Syntax.actions)
in (match (_85_2565) with
| (env, decls2) -> begin
(((FStar_List.flatten decls2)), (env))
end))))
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _85_2568, _85_2570, _85_2572, _85_2574) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid) -> begin
(

let _85_2580 = (new_term_constant_and_tok_from_lid env lid)
in (match (_85_2580) with
| (tname, ttok, env) -> begin
(([]), (env))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _85_2583, t, quals, _85_2587) -> begin
(

let will_encode_definition = (not ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _85_17 -> (match (_85_17) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Irreducible) -> begin
true
end
| _85_2600 -> begin
false
end))))))
in if will_encode_definition then begin
(([]), (env))
end else begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (

let _85_2605 = (encode_top_level_val env fv t quals)
in (match (_85_2605) with
| (decls, env) -> begin
(

let tname = lid.FStar_Ident.str
in (

let tsym = (FStar_SMTEncoding_Term.mkFreeV ((tname), (FStar_SMTEncoding_Term.Term_sort)))
in (let _177_2124 = (let _177_2123 = (primitive_type_axioms env.tcenv lid tname tsym)
in (FStar_List.append decls _177_2123))
in ((_177_2124), (env)))))
end)))
end)
end
| FStar_Syntax_Syntax.Sig_assume (l, f, _85_2611, _85_2613) -> begin
(

let _85_2618 = (encode_formula f env)
in (match (_85_2618) with
| (f, decls) -> begin
(

let g = (let _177_2131 = (let _177_2130 = (let _177_2129 = (let _177_2126 = (let _177_2125 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" _177_2125))
in Some (_177_2126))
in (let _177_2128 = (let _177_2127 = (varops.mk_unique (Prims.strcat "assumption_" l.FStar_Ident.str))
in Some (_177_2127))
in ((f), (_177_2129), (_177_2128))))
in FStar_SMTEncoding_Term.Assume (_177_2130))
in (_177_2131)::[])
in (((FStar_List.append decls g)), (env)))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _85_2623, quals) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) -> begin
(

let _85_2636 = (FStar_Util.fold_map (fun env lb -> (

let lid = (let _177_2135 = (let _177_2134 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _177_2134.FStar_Syntax_Syntax.fv_name)
in _177_2135.FStar_Syntax_Syntax.v)
in if (let _177_2136 = (FStar_TypeChecker_Env.try_lookup_val_decl env.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone _177_2136)) then begin
(

let val_decl = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), (r)))
in (

let _85_2633 = (encode_sigelt' env val_decl)
in (match (_85_2633) with
| (decls, env) -> begin
((env), (decls))
end)))
end else begin
((env), ([]))
end)) env (Prims.snd lbs))
in (match (_85_2636) with
| (env, decls) -> begin
(((FStar_List.flatten decls)), (env))
end))
end
| FStar_Syntax_Syntax.Sig_let ((_85_2638, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t); FStar_Syntax_Syntax.lbunivs = _85_2646; FStar_Syntax_Syntax.lbtyp = _85_2644; FStar_Syntax_Syntax.lbeff = _85_2642; FStar_Syntax_Syntax.lbdef = _85_2640})::[]), _85_2653, _85_2655, _85_2657) when (FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Syntax_Const.b2t_lid) -> begin
(

let _85_2663 = (new_term_constant_and_tok_from_lid env b2t.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_85_2663) with
| (tname, ttok, env) -> begin
(

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (

let valid_b2t_x = (let _177_2139 = (let _177_2138 = (let _177_2137 = (FStar_SMTEncoding_Term.mkApp (("Prims.b2t"), ((x)::[])))
in (_177_2137)::[])
in (("Valid"), (_177_2138)))
in (FStar_SMTEncoding_Term.mkApp _177_2139))
in (

let decls = (let _177_2147 = (let _177_2146 = (let _177_2145 = (let _177_2144 = (let _177_2143 = (let _177_2142 = (let _177_2141 = (let _177_2140 = (FStar_SMTEncoding_Term.mkApp (("BoxBool_proj_0"), ((x)::[])))
in ((valid_b2t_x), (_177_2140)))
in (FStar_SMTEncoding_Term.mkEq _177_2141))
in ((((valid_b2t_x)::[])::[]), ((xx)::[]), (_177_2142)))
in (FStar_SMTEncoding_Term.mkForall _177_2143))
in ((_177_2144), (Some ("b2t def")), (Some ("b2t_def"))))
in FStar_SMTEncoding_Term.Assume (_177_2145))
in (_177_2146)::[])
in (FStar_SMTEncoding_Term.DeclFun (((tname), ((FStar_SMTEncoding_Term.Term_sort)::[]), (FStar_SMTEncoding_Term.Term_sort), (None))))::_177_2147)
in ((decls), (env))))))
end))
end
| FStar_Syntax_Syntax.Sig_let (_85_2669, _85_2671, _85_2673, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _85_18 -> (match (_85_18) with
| FStar_Syntax_Syntax.Discriminator (_85_2679) -> begin
true
end
| _85_2682 -> begin
false
end)))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let (_85_2684, _85_2686, lids, quals) when ((FStar_All.pipe_right lids (FStar_Util.for_some (fun l -> ((let _177_2150 = (FStar_List.hd l.FStar_Ident.ns)
in _177_2150.FStar_Ident.idText) = "Prims")))) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun _85_19 -> (match (_85_19) with
| FStar_Syntax_Syntax.Inline -> begin
true
end
| _85_2695 -> begin
false
end))))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _85_2701, _85_2703, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _85_20 -> (match (_85_20) with
| FStar_Syntax_Syntax.Projector (_85_2709) -> begin
true
end
| _85_2712 -> begin
false
end)))) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((try_lookup_free_var env l)) with
| Some (_85_2716) -> begin
(([]), (env))
end
| None -> begin
(

let se = FStar_Syntax_Syntax.Sig_declare_typ (((l), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), ((FStar_Ident.range_of_lid l))))
in (encode_sigelt env se))
end)))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _85_2725, _85_2727, quals) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) -> begin
(match ((let _177_2153 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef)
in _177_2153.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, _85_2734) -> begin
(

let body = (FStar_Syntax_Util.mk_reify body)
in (

let tm = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None)))) None lb.FStar_Syntax_Syntax.lbdef.FStar_Syntax_Syntax.pos)
in (

let tm' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env.tcenv tm)
in (

let lb_typ = (

let _85_2742 = (FStar_Syntax_Util.arrow_formals_comp lb.FStar_Syntax_Syntax.lbtyp)
in (match (_85_2742) with
| (formals, comp) -> begin
(

let reified_typ = (FStar_TypeChecker_Util.reify_comp (

let _85_2743 = env.tcenv
in {FStar_TypeChecker_Env.solver = _85_2743.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _85_2743.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _85_2743.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _85_2743.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _85_2743.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _85_2743.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _85_2743.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _85_2743.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _85_2743.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _85_2743.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _85_2743.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _85_2743.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _85_2743.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _85_2743.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _85_2743.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _85_2743.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _85_2743.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _85_2743.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.type_of = _85_2743.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _85_2743.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _85_2743.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _85_2743.FStar_TypeChecker_Env.qname_and_index}) (FStar_Syntax_Util.lcomp_of_comp comp) FStar_Syntax_Syntax.U_unknown)
in (let _177_2154 = (FStar_Syntax_Syntax.mk_Total reified_typ)
in (FStar_Syntax_Util.arrow formals _177_2154)))
end))
in (

let lb = (

let _85_2747 = lb
in {FStar_Syntax_Syntax.lbname = _85_2747.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _85_2747.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lb_typ; FStar_Syntax_Syntax.lbeff = _85_2747.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = tm'})
in (encode_top_level_let env ((false), ((lb)::[])) quals))))))
end
| _85_2751 -> begin
(([]), (env))
end)
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), _85_2756, _85_2758, quals) -> begin
(encode_top_level_let env ((is_rec), (bindings)) quals)
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _85_2764, _85_2766, _85_2768) -> begin
(

let _85_2773 = (encode_signature env ses)
in (match (_85_2773) with
| (g, env) -> begin
(

let _85_2787 = (FStar_All.pipe_right g (FStar_List.partition (fun _85_21 -> (match (_85_21) with
| FStar_SMTEncoding_Term.Assume (_85_2776, Some ("inversion axiom"), _85_2780) -> begin
false
end
| _85_2784 -> begin
true
end))))
in (match (_85_2787) with
| (g', inversions) -> begin
(

let _85_2796 = (FStar_All.pipe_right g' (FStar_List.partition (fun _85_22 -> (match (_85_22) with
| FStar_SMTEncoding_Term.DeclFun (_85_2790) -> begin
true
end
| _85_2793 -> begin
false
end))))
in (match (_85_2796) with
| (decls, rest) -> begin
(((FStar_List.append decls (FStar_List.append rest inversions))), (env))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, _85_2799, tps, k, _85_2803, datas, quals, _85_2807) -> begin
(

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _85_23 -> (match (_85_23) with
| (FStar_Syntax_Syntax.Logic) | (FStar_Syntax_Syntax.Assumption) -> begin
true
end
| _85_2814 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(

let _85_2826 = c
in (match (_85_2826) with
| (name, args, _85_2821, _85_2823, _85_2825) -> begin
(let _177_2162 = (let _177_2161 = (let _177_2160 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in ((name), (_177_2160), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (_177_2161))
in (_177_2162)::[])
end))
end else begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end)
in (

let inversion_axioms = (fun tapp vars -> if (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _177_2168 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right _177_2168 FStar_Option.isNone))))) then begin
[]
end else begin
(

let _85_2833 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_85_2833) with
| (xxsym, xx) -> begin
(

let _85_2869 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _85_2836 l -> (match (_85_2836) with
| (out, decls) -> begin
(

let _85_2841 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (_85_2841) with
| (_85_2839, data_t) -> begin
(

let _85_2844 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (_85_2844) with
| (args, res) -> begin
(

let indices = (match ((let _177_2171 = (FStar_Syntax_Subst.compress res)
in _177_2171.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_85_2846, indices) -> begin
indices
end
| _85_2851 -> begin
[]
end)
in (

let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env _85_2857 -> (match (_85_2857) with
| (x, _85_2856) -> begin
(let _177_2176 = (let _177_2175 = (let _177_2174 = (mk_term_projector_name l x)
in ((_177_2174), ((xx)::[])))
in (FStar_SMTEncoding_Term.mkApp _177_2175))
in (push_term_var env x _177_2176))
end)) env))
in (

let _85_2861 = (encode_args indices env)
in (match (_85_2861) with
| (indices, decls') -> begin
(

let _85_2862 = if ((FStar_List.length indices) <> (FStar_List.length vars)) then begin
(FStar_All.failwith "Impossible")
end else begin
()
end
in (

let eqs = (let _177_2181 = (FStar_List.map2 (fun v a -> (let _177_2180 = (let _177_2179 = (FStar_SMTEncoding_Term.mkFreeV v)
in ((_177_2179), (a)))
in (FStar_SMTEncoding_Term.mkEq _177_2180))) vars indices)
in (FStar_All.pipe_right _177_2181 FStar_SMTEncoding_Term.mk_and_l))
in (let _177_2186 = (let _177_2185 = (let _177_2184 = (let _177_2183 = (let _177_2182 = (mk_data_tester env l xx)
in ((_177_2182), (eqs)))
in (FStar_SMTEncoding_Term.mkAnd _177_2183))
in ((out), (_177_2184)))
in (FStar_SMTEncoding_Term.mkOr _177_2185))
in ((_177_2186), ((FStar_List.append decls decls'))))))
end))))
end))
end))
end)) ((FStar_SMTEncoding_Term.mkFalse), ([]))))
in (match (_85_2869) with
| (data_ax, decls) -> begin
(

let _85_2872 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_85_2872) with
| (ffsym, ff) -> begin
(

let fuel_guarded_inversion = (

let xx_has_type_sfuel = if ((FStar_List.length datas) > 1) then begin
(let _177_2187 = (FStar_SMTEncoding_Term.mkApp (("SFuel"), ((ff)::[])))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel _177_2187 xx tapp))
end else begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end
in (let _177_2194 = (let _177_2193 = (let _177_2190 = (let _177_2189 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (let _177_2188 = (FStar_SMTEncoding_Term.mkImp ((xx_has_type_sfuel), (data_ax)))
in ((((xx_has_type_sfuel)::[])::[]), (_177_2189), (_177_2188))))
in (FStar_SMTEncoding_Term.mkForall _177_2190))
in (let _177_2192 = (let _177_2191 = (varops.mk_unique (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str))
in Some (_177_2191))
in ((_177_2193), (Some ("inversion axiom")), (_177_2192))))
in FStar_SMTEncoding_Term.Assume (_177_2194)))
in (

let pattern_guarded_inversion = if ((contains_name env "Prims.inversion") && ((FStar_List.length datas) > 1)) then begin
(

let xx_has_type_fuel = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let pattern_guard = (FStar_SMTEncoding_Term.mkApp (("Prims.inversion"), ((tapp)::[])))
in (let _177_2202 = (let _177_2201 = (let _177_2200 = (let _177_2197 = (let _177_2196 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (let _177_2195 = (FStar_SMTEncoding_Term.mkImp ((xx_has_type_fuel), (data_ax)))
in ((((xx_has_type_fuel)::(pattern_guard)::[])::[]), (_177_2196), (_177_2195))))
in (FStar_SMTEncoding_Term.mkForall _177_2197))
in (let _177_2199 = (let _177_2198 = (varops.mk_unique (Prims.strcat "pattern_guarded_inversion_" t.FStar_Ident.str))
in Some (_177_2198))
in ((_177_2200), (Some ("inversion axiom")), (_177_2199))))
in FStar_SMTEncoding_Term.Assume (_177_2201))
in (_177_2202)::[])))
end else begin
[]
end
in (FStar_List.append decls (FStar_List.append ((fuel_guarded_inversion)::[]) pattern_guarded_inversion))))
end))
end))
end))
end)
in (

let _85_2886 = (match ((let _177_2203 = (FStar_Syntax_Subst.compress k)
in _177_2203.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
(((FStar_List.append tps formals)), ((FStar_Syntax_Util.comp_result kres)))
end
| _85_2883 -> begin
((tps), (k))
end)
in (match (_85_2886) with
| (formals, res) -> begin
(

let _85_2889 = (FStar_Syntax_Subst.open_term formals res)
in (match (_85_2889) with
| (formals, res) -> begin
(

let _85_2896 = (encode_binders None formals env)
in (match (_85_2896) with
| (vars, guards, env', binder_decls, _85_2895) -> begin
(

let _85_2900 = (new_term_constant_and_tok_from_lid env t)
in (match (_85_2900) with
| (tname, ttok, env) -> begin
(

let ttok_tm = (FStar_SMTEncoding_Term.mkApp ((ttok), ([])))
in (

let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (

let tapp = (let _177_2205 = (let _177_2204 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in ((tname), (_177_2204)))
in (FStar_SMTEncoding_Term.mkApp _177_2205))
in (

let _85_2921 = (

let tname_decl = (let _177_2209 = (let _177_2208 = (FStar_All.pipe_right vars (FStar_List.map (fun _85_2906 -> (match (_85_2906) with
| (n, s) -> begin
(((Prims.strcat tname n)), (s))
end))))
in (let _177_2207 = (varops.next_id ())
in ((tname), (_177_2208), (FStar_SMTEncoding_Term.Term_sort), (_177_2207), (false))))
in (constructor_or_logic_type_decl _177_2209))
in (

let _85_2918 = (match (vars) with
| [] -> begin
(let _177_2213 = (let _177_2212 = (let _177_2211 = (FStar_SMTEncoding_Term.mkApp ((tname), ([])))
in (FStar_All.pipe_left (fun _177_2210 -> Some (_177_2210)) _177_2211))
in (push_free_var env t tname _177_2212))
in (([]), (_177_2213)))
end
| _85_2910 -> begin
(

let ttok_decl = FStar_SMTEncoding_Term.DeclFun (((ttok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("token"))))
in (

let ttok_fresh = (let _177_2214 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ttok), (FStar_SMTEncoding_Term.Term_sort)) _177_2214))
in (

let ttok_app = (mk_Apply ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (let _177_2218 = (let _177_2217 = (let _177_2216 = (let _177_2215 = (FStar_SMTEncoding_Term.mkEq ((ttok_app), (tapp)))
in ((pats), (None), (vars), (_177_2215)))
in (FStar_SMTEncoding_Term.mkForall' _177_2216))
in ((_177_2217), (Some ("name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" ttok)))))
in FStar_SMTEncoding_Term.Assume (_177_2218))
in (((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[]), (env)))))))
end)
in (match (_85_2918) with
| (tok_decls, env) -> begin
(((FStar_List.append tname_decl tok_decls)), (env))
end)))
in (match (_85_2921) with
| (decls, env) -> begin
(

let kindingAx = (

let _85_2924 = (encode_term_pred None res env' tapp)
in (match (_85_2924) with
| (k, decls) -> begin
(

let karr = if ((FStar_List.length formals) > 0) then begin
(let _177_2222 = (let _177_2221 = (let _177_2220 = (let _177_2219 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _177_2219))
in ((_177_2220), (Some ("kinding")), (Some ((Prims.strcat "pre_kinding_" ttok)))))
in FStar_SMTEncoding_Term.Assume (_177_2221))
in (_177_2222)::[])
end else begin
[]
end
in (let _177_2229 = (let _177_2228 = (let _177_2227 = (let _177_2226 = (let _177_2225 = (let _177_2224 = (let _177_2223 = (FStar_SMTEncoding_Term.mkImp ((guard), (k)))
in ((((tapp)::[])::[]), (vars), (_177_2223)))
in (FStar_SMTEncoding_Term.mkForall _177_2224))
in ((_177_2225), (None), (Some ((Prims.strcat "kinding_" ttok)))))
in FStar_SMTEncoding_Term.Assume (_177_2226))
in (_177_2227)::[])
in (FStar_List.append karr _177_2228))
in (FStar_List.append decls _177_2229)))
end))
in (

let aux = (let _177_2233 = (let _177_2232 = (inversion_axioms tapp vars)
in (let _177_2231 = (let _177_2230 = (pretype_axiom tapp vars)
in (_177_2230)::[])
in (FStar_List.append _177_2232 _177_2231)))
in (FStar_List.append kindingAx _177_2233))
in (

let g = (FStar_List.append decls (FStar_List.append binder_decls aux))
in ((g), (env)))))
end)))))
end))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, _85_2931, _85_2933, _85_2935, _85_2937, _85_2939, _85_2941, _85_2943) when (FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_datacon (d, _85_2948, t, _85_2951, n_tps, quals, _85_2955, drange) -> begin
(

let _85_2962 = (new_term_constant_and_tok_from_lid env d)
in (match (_85_2962) with
| (ddconstrsym, ddtok, env) -> begin
(

let ddtok_tm = (FStar_SMTEncoding_Term.mkApp ((ddtok), ([])))
in (

let _85_2966 = (FStar_Syntax_Util.arrow_formals t)
in (match (_85_2966) with
| (formals, t_res) -> begin
(

let _85_2969 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_85_2969) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_SMTEncoding_Term.mkApp (("SFuel"), ((fuel_tm)::[])))
in (

let _85_2976 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_85_2976) with
| (vars, guards, env', binder_decls, names) -> begin
(

let projectors = (FStar_All.pipe_right names (FStar_List.map (fun x -> (let _177_2235 = (mk_term_projector_name d x)
in ((_177_2235), (FStar_SMTEncoding_Term.Term_sort))))))
in (

let datacons = (let _177_2237 = (let _177_2236 = (varops.next_id ())
in ((ddconstrsym), (projectors), (FStar_SMTEncoding_Term.Term_sort), (_177_2236), (true)))
in (FStar_All.pipe_right _177_2237 FStar_SMTEncoding_Term.constructor_to_decl))
in (

let app = (mk_Apply ddtok_tm vars)
in (

let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Term.mkApp ((ddconstrsym), (xvars)))
in (

let _85_2986 = (encode_term_pred None t env ddtok_tm)
in (match (_85_2986) with
| (tok_typing, decls3) -> begin
(

let _85_2993 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_85_2993) with
| (vars', guards', env'', decls_formals, _85_2992) -> begin
(

let _85_2998 = (

let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars')
in (

let dapp = (FStar_SMTEncoding_Term.mkApp ((ddconstrsym), (xvars)))
in (encode_term_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_85_2998) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_SMTEncoding_Term.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _85_3002 -> begin
(let _177_2239 = (let _177_2238 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ddtok), (FStar_SMTEncoding_Term.Term_sort)) _177_2238))
in (_177_2239)::[])
end)
in (

let encode_elim = (fun _85_3005 -> (match (()) with
| () -> begin
(

let _85_3008 = (FStar_Syntax_Util.head_and_args t_res)
in (match (_85_3008) with
| (head, args) -> begin
(match ((let _177_2242 = (FStar_Syntax_Subst.compress head)
in _177_2242.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let _85_3026 = (encode_args args env')
in (match (_85_3026) with
| (encoded_args, arg_decls) -> begin
(

let _85_3041 = (FStar_List.fold_left (fun _85_3030 arg -> (match (_85_3030) with
| (env, arg_vars, eqns) -> begin
(

let _85_3036 = (let _177_2245 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in (gen_term_var env _177_2245))
in (match (_85_3036) with
| (_85_3033, xv, env) -> begin
(let _177_2247 = (let _177_2246 = (FStar_SMTEncoding_Term.mkEq ((arg), (xv)))
in (_177_2246)::eqns)
in ((env), ((xv)::arg_vars), (_177_2247)))
end))
end)) ((env'), ([]), ([])) encoded_args)
in (match (_85_3041) with
| (_85_3038, arg_vars, eqns) -> begin
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

let typing_inversion = (let _177_2254 = (let _177_2253 = (let _177_2252 = (let _177_2251 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (let _177_2250 = (let _177_2249 = (let _177_2248 = (FStar_SMTEncoding_Term.mk_and_l (FStar_List.append eqns guards))
in ((ty_pred), (_177_2248)))
in (FStar_SMTEncoding_Term.mkImp _177_2249))
in ((((ty_pred)::[])::[]), (_177_2251), (_177_2250))))
in (FStar_SMTEncoding_Term.mkForall _177_2252))
in ((_177_2253), (Some ("data constructor typing elim")), (Some ((Prims.strcat "data_elim_" ddconstrsym)))))
in FStar_SMTEncoding_Term.Assume (_177_2254))
in (

let subterm_ordering = if (FStar_Ident.lid_equals d FStar_Syntax_Const.lextop_lid) then begin
(

let x = (let _177_2255 = (varops.fresh "x")
in ((_177_2255), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Term.mkFreeV x)
in (let _177_2267 = (let _177_2266 = (let _177_2263 = (let _177_2262 = (let _177_2257 = (let _177_2256 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in (_177_2256)::[])
in (_177_2257)::[])
in (let _177_2261 = (let _177_2260 = (let _177_2259 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (let _177_2258 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in ((_177_2259), (_177_2258))))
in (FStar_SMTEncoding_Term.mkImp _177_2260))
in ((_177_2262), ((x)::[]), (_177_2261))))
in (FStar_SMTEncoding_Term.mkForall _177_2263))
in (let _177_2265 = (let _177_2264 = (varops.mk_unique "lextop")
in Some (_177_2264))
in ((_177_2266), (Some ("lextop is top")), (_177_2265))))
in FStar_SMTEncoding_Term.Assume (_177_2267))))
end else begin
(

let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
[]
end
| FStar_SMTEncoding_Term.Term_sort -> begin
(let _177_2270 = (let _177_2269 = (FStar_SMTEncoding_Term.mkFreeV v)
in (FStar_SMTEncoding_Term.mk_Precedes _177_2269 dapp))
in (_177_2270)::[])
end
| _85_3055 -> begin
(FStar_All.failwith "unexpected sort")
end))))
in (let _177_2277 = (let _177_2276 = (let _177_2275 = (let _177_2274 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (let _177_2273 = (let _177_2272 = (let _177_2271 = (FStar_SMTEncoding_Term.mk_and_l prec)
in ((ty_pred), (_177_2271)))
in (FStar_SMTEncoding_Term.mkImp _177_2272))
in ((((ty_pred)::[])::[]), (_177_2274), (_177_2273))))
in (FStar_SMTEncoding_Term.mkForall _177_2275))
in ((_177_2276), (Some ("subterm ordering")), (Some ((Prims.strcat "subterm_ordering_" ddconstrsym)))))
in FStar_SMTEncoding_Term.Assume (_177_2277)))
end
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end))
end)))
end
| _85_3059 -> begin
(

let _85_3060 = (let _177_2280 = (let _177_2279 = (FStar_Syntax_Print.lid_to_string d)
in (let _177_2278 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _177_2279 _177_2278)))
in (FStar_TypeChecker_Errors.warn drange _177_2280))
in (([]), ([])))
end)
end))
end))
in (

let _85_3064 = (encode_elim ())
in (match (_85_3064) with
| (decls2, elim) -> begin
(

let g = (let _177_2307 = (let _177_2306 = (let _177_2305 = (let _177_2304 = (let _177_2285 = (let _177_2284 = (let _177_2283 = (let _177_2282 = (let _177_2281 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" _177_2281))
in Some (_177_2282))
in ((ddtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (_177_2283)))
in FStar_SMTEncoding_Term.DeclFun (_177_2284))
in (_177_2285)::[])
in (let _177_2303 = (let _177_2302 = (let _177_2301 = (let _177_2300 = (let _177_2299 = (let _177_2298 = (let _177_2297 = (let _177_2289 = (let _177_2288 = (let _177_2287 = (let _177_2286 = (FStar_SMTEncoding_Term.mkEq ((app), (dapp)))
in ((((app)::[])::[]), (vars), (_177_2286)))
in (FStar_SMTEncoding_Term.mkForall _177_2287))
in ((_177_2288), (Some ("equality for proxy")), (Some ((Prims.strcat "equality_tok_" ddtok)))))
in FStar_SMTEncoding_Term.Assume (_177_2289))
in (let _177_2296 = (let _177_2295 = (let _177_2294 = (let _177_2293 = (let _177_2292 = (let _177_2291 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) vars')
in (let _177_2290 = (FStar_SMTEncoding_Term.mkImp ((guard'), (ty_pred')))
in ((((ty_pred')::[])::[]), (_177_2291), (_177_2290))))
in (FStar_SMTEncoding_Term.mkForall _177_2292))
in ((_177_2293), (Some ("data constructor typing intro")), (Some ((Prims.strcat "data_typing_intro_" ddtok)))))
in FStar_SMTEncoding_Term.Assume (_177_2294))
in (_177_2295)::[])
in (_177_2297)::_177_2296))
in (FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("typing for data constructor proxy")), (Some ((Prims.strcat "typing_tok_" ddtok))))))::_177_2298)
in (FStar_List.append _177_2299 elim))
in (FStar_List.append decls_pred _177_2300))
in (FStar_List.append decls_formals _177_2301))
in (FStar_List.append proxy_fresh _177_2302))
in (FStar_List.append _177_2304 _177_2303)))
in (FStar_List.append decls3 _177_2305))
in (FStar_List.append decls2 _177_2306))
in (FStar_List.append binder_decls _177_2307))
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
and encode_signature : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _85_3070 se -> (match (_85_3070) with
| (g, env) -> begin
(

let _85_3074 = (encode_sigelt env se)
in (match (_85_3074) with
| (g', env) -> begin
(((FStar_List.append g g')), (env))
end))
end)) (([]), (env)))))


let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env bindings -> (

let encode_binding = (fun b _85_3082 -> (match (_85_3082) with
| (i, decls, env) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (_85_3084) -> begin
(((i + 1)), ([]), (env))
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (

let _85_3089 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _177_2322 = (FStar_Syntax_Print.bv_to_string x)
in (let _177_2321 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _177_2320 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" _177_2322 _177_2321 _177_2320))))
end else begin
()
end
in (

let _85_3093 = (encode_term t1 env)
in (match (_85_3093) with
| (t, decls') -> begin
(

let _85_3097 = (let _177_2327 = (let _177_2326 = (let _177_2325 = (FStar_Util.digest_of_string t.FStar_SMTEncoding_Term.hash)
in (let _177_2324 = (let _177_2323 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _177_2323))
in (Prims.strcat _177_2325 _177_2324)))
in (Prims.strcat "x_" _177_2326))
in (new_term_constant_from_string env x _177_2327))
in (match (_85_3097) with
| (xxsym, xx, env') -> begin
(

let t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel None xx t)
in (

let caption = if (FStar_Options.log_queries ()) then begin
(let _177_2331 = (let _177_2330 = (FStar_Syntax_Print.bv_to_string x)
in (let _177_2329 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _177_2328 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _177_2330 _177_2329 _177_2328))))
in Some (_177_2331))
end else begin
None
end
in (

let ax = (

let a_name = Some ((Prims.strcat "binder_" xxsym))
in FStar_SMTEncoding_Term.Assume (((t), (a_name), (a_name))))
in (

let g = (FStar_List.append ((FStar_SMTEncoding_Term.DeclFun (((xxsym), ([]), (FStar_SMTEncoding_Term.Term_sort), (caption))))::[]) (FStar_List.append decls' ((ax)::[])))
in (((i + 1)), ((FStar_List.append decls g)), (env'))))))
end))
end))))
end
| FStar_TypeChecker_Env.Binding_lid (x, (_85_3105, t)) -> begin
(

let t_norm = (whnf env t)
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant None)
in (

let _85_3114 = (encode_free_var env fv t t_norm [])
in (match (_85_3114) with
| (g, env') -> begin
(((i + 1)), ((FStar_List.append decls g)), (env'))
end))))
end
| (FStar_TypeChecker_Env.Binding_sig_inst (_, se, _)) | (FStar_TypeChecker_Env.Binding_sig (_, se)) -> begin
(

let _85_3128 = (encode_sigelt env se)
in (match (_85_3128) with
| (g, env') -> begin
(((i + 1)), ((FStar_List.append decls g)), (env'))
end))
end)
end))
in (

let _85_3133 = (FStar_List.fold_right encode_binding bindings ((0), ([]), (env)))
in (match (_85_3133) with
| (_85_3130, decls, env) -> begin
((decls), (env))
end))))


let encode_labels = (fun labs -> (

let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _85_3140 -> (match (_85_3140) with
| (l, _85_3137, _85_3139) -> begin
FStar_SMTEncoding_Term.DeclFun ((((Prims.fst l)), ([]), (FStar_SMTEncoding_Term.Bool_sort), (None)))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _85_3147 -> (match (_85_3147) with
| (l, _85_3144, _85_3146) -> begin
(let _177_2339 = (FStar_All.pipe_left (fun _177_2335 -> FStar_SMTEncoding_Term.Echo (_177_2335)) (Prims.fst l))
in (let _177_2338 = (let _177_2337 = (let _177_2336 = (FStar_SMTEncoding_Term.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (_177_2336))
in (_177_2337)::[])
in (_177_2339)::_177_2338))
end))))
in ((prefix), (suffix)))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (let _177_2344 = (let _177_2343 = (let _177_2342 = (FStar_Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _177_2342; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_177_2343)::[])
in (FStar_ST.op_Colon_Equals last_env _177_2344)))


let get_env : FStar_TypeChecker_Env.env  ->  env_t = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "No env; call init first!")
end
| (e)::_85_3153 -> begin
(

let _85_3156 = e
in {bindings = _85_3156.bindings; depth = _85_3156.depth; tcenv = tcenv; warn = _85_3156.warn; cache = _85_3156.cache; nolabels = _85_3156.nolabels; use_zfuel_name = _85_3156.use_zfuel_name; encode_non_total_function_typ = _85_3156.encode_non_total_function_typ})
end))


let set_env : env_t  ->  Prims.unit = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| (_85_3162)::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))


let push_env : Prims.unit  ->  Prims.unit = (fun _85_3164 -> (match (()) with
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

let _85_3170 = hd
in {bindings = _85_3170.bindings; depth = _85_3170.depth; tcenv = _85_3170.tcenv; warn = _85_3170.warn; cache = refs; nolabels = _85_3170.nolabels; use_zfuel_name = _85_3170.use_zfuel_name; encode_non_total_function_typ = _85_3170.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))


let pop_env : Prims.unit  ->  Prims.unit = (fun _85_3173 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Popping an empty stack")
end
| (_85_3177)::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))


let mark_env : Prims.unit  ->  Prims.unit = (fun _85_3179 -> (match (()) with
| () -> begin
(push_env ())
end))


let reset_mark_env : Prims.unit  ->  Prims.unit = (fun _85_3180 -> (match (()) with
| () -> begin
(pop_env ())
end))


let commit_mark_env : Prims.unit  ->  Prims.unit = (fun _85_3181 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| (hd)::(_85_3184)::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _85_3189 -> begin
(FStar_All.failwith "Impossible")
end)
end))


let init : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (

let _85_3191 = (init_env tcenv)
in (

let _85_3193 = (FStar_SMTEncoding_Z3.init ())
in (FStar_SMTEncoding_Z3.giveZ3 ((FStar_SMTEncoding_Term.DefPrelude)::[])))))


let push : Prims.string  ->  Prims.unit = (fun msg -> (

let _85_3196 = (push_env ())
in (

let _85_3198 = (varops.push ())
in (FStar_SMTEncoding_Z3.push msg))))


let pop : Prims.string  ->  Prims.unit = (fun msg -> (

let _85_3201 = (let _177_2365 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _177_2365))
in (

let _85_3203 = (varops.pop ())
in (FStar_SMTEncoding_Z3.pop msg))))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _85_3206 = (mark_env ())
in (

let _85_3208 = (varops.mark ())
in (FStar_SMTEncoding_Z3.mark msg))))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _85_3211 = (reset_mark_env ())
in (

let _85_3213 = (varops.reset_mark ())
in (FStar_SMTEncoding_Z3.reset_mark msg))))


let commit_mark = (fun msg -> (

let _85_3216 = (commit_mark_env ())
in (

let _85_3218 = (varops.commit_mark ())
in (FStar_SMTEncoding_Z3.commit_mark msg))))


let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (

let caption = (fun decls -> if (FStar_Options.log_queries ()) then begin
(let _177_2381 = (let _177_2380 = (let _177_2379 = (let _177_2378 = (let _177_2377 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _177_2377 (FStar_List.map FStar_Syntax_Print.lid_to_string)))
in (FStar_All.pipe_right _177_2378 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " _177_2379))
in FStar_SMTEncoding_Term.Caption (_177_2380))
in (_177_2381)::decls)
end else begin
decls
end)
in (

let env = (get_env tcenv)
in (

let _85_3227 = (encode_sigelt env se)
in (match (_85_3227) with
| (decls, env) -> begin
(

let _85_3228 = (set_env env)
in (let _177_2382 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 _177_2382)))
end)))))


let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let _85_3233 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(let _177_2387 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name _177_2387))
end else begin
()
end
in (

let env = (get_env tcenv)
in (

let _85_3240 = (encode_signature (

let _85_3236 = env
in {bindings = _85_3236.bindings; depth = _85_3236.depth; tcenv = _85_3236.tcenv; warn = false; cache = _85_3236.cache; nolabels = _85_3236.nolabels; use_zfuel_name = _85_3236.use_zfuel_name; encode_non_total_function_typ = _85_3236.encode_non_total_function_typ}) modul.FStar_Syntax_Syntax.exports)
in (match (_85_3240) with
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

let _85_3246 = (set_env (

let _85_3244 = env
in {bindings = _85_3244.bindings; depth = _85_3244.depth; tcenv = _85_3244.tcenv; warn = true; cache = _85_3244.cache; nolabels = _85_3244.nolabels; use_zfuel_name = _85_3244.use_zfuel_name; encode_non_total_function_typ = _85_3244.encode_non_total_function_typ}))
in (

let _85_3248 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end else begin
()
end
in (

let decls = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls)))))
end))))))


let encode_query : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_ErrorReporting.label Prims.list * FStar_SMTEncoding_Term.decl * FStar_SMTEncoding_Term.decl Prims.list) = (fun use_env_msg tcenv q -> (

let _85_3254 = (let _177_2405 = (let _177_2404 = (FStar_TypeChecker_Env.current_module tcenv)
in _177_2404.FStar_Ident.str)
in (FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name _177_2405))
in (

let env = (get_env tcenv)
in (

let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (

let _85_3279 = (

let rec aux = (fun bindings -> (match (bindings) with
| (FStar_TypeChecker_Env.Binding_var (x))::rest -> begin
(

let _85_3268 = (aux rest)
in (match (_85_3268) with
| (out, rest) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (let _177_2411 = (let _177_2410 = (FStar_Syntax_Syntax.mk_binder (

let _85_3270 = x
in {FStar_Syntax_Syntax.ppname = _85_3270.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _85_3270.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_177_2410)::out)
in ((_177_2411), (rest))))
end))
end
| _85_3273 -> begin
(([]), (bindings))
end))
in (

let _85_3276 = (aux bindings)
in (match (_85_3276) with
| (closing, bindings) -> begin
(let _177_2412 = (FStar_Syntax_Util.close_forall (FStar_List.rev closing) q)
in ((_177_2412), (bindings)))
end)))
in (match (_85_3279) with
| (q, bindings) -> begin
(

let _85_3288 = (let _177_2414 = (FStar_List.filter (fun _85_24 -> (match (_85_24) with
| FStar_TypeChecker_Env.Binding_sig (_85_3282) -> begin
false
end
| _85_3285 -> begin
true
end)) bindings)
in (encode_env_bindings env _177_2414))
in (match (_85_3288) with
| (env_decls, env) -> begin
(

let _85_3289 = if (((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTQuery")))) then begin
(let _177_2415 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" _177_2415))
end else begin
()
end
in (

let _85_3293 = (encode_formula q env)
in (match (_85_3293) with
| (phi, qdecls) -> begin
(

let _85_3298 = (let _177_2416 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg _177_2416 phi))
in (match (_85_3298) with
| (phi, labels, _85_3297) -> begin
(

let _85_3301 = (encode_labels labels)
in (match (_85_3301) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append env_decls (FStar_List.append label_prefix qdecls))
in (

let qry = (let _177_2420 = (let _177_2419 = (FStar_SMTEncoding_Term.mkNot phi)
in (let _177_2418 = (let _177_2417 = (varops.mk_unique "@query")
in Some (_177_2417))
in ((_177_2419), (Some ("query")), (_177_2418))))
in FStar_SMTEncoding_Term.Assume (_177_2420))
in (

let suffix = (FStar_List.append label_suffix ((FStar_SMTEncoding_Term.Echo ("Done!"))::[]))
in ((query_prelude), (labels), (qry), (suffix)))))
end))
end))
end)))
end))
end))))))


let is_trivial : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun tcenv q -> (

let env = (get_env tcenv)
in (

let _85_3308 = (push "query")
in (

let _85_3313 = (encode_formula q env)
in (match (_85_3313) with
| (f, _85_3312) -> begin
(

let _85_3314 = (pop "query")
in (match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _85_3318) -> begin
true
end
| _85_3322 -> begin
false
end))
end)))))




