
open Prims

let add_fuel = (fun x tl -> if (FStar_Options.unthrottle_inductives ()) then begin
tl
end else begin
(x)::tl
end)


let withenv = (fun c _87_30 -> (match (_87_30) with
| (a, b) -> begin
((a), (b), (c))
end))


let vargs = (fun args -> (FStar_List.filter (fun _87_1 -> (match (_87_1) with
| (FStar_Util.Inl (_87_34), _87_37) -> begin
false
end
| _87_40 -> begin
true
end)) args))


let subst_lcomp_opt = (fun s l -> (match (l) with
| Some (FStar_Util.Inl (l)) -> begin
(let _181_12 = (let _181_11 = (let _181_10 = (let _181_9 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp s _181_9))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _181_10))
in FStar_Util.Inl (_181_11))
in Some (_181_12))
end
| _87_47 -> begin
l
end))


let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s '\'' '_'))


let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun lid a -> (

let a = (

let _87_51 = a
in (let _181_19 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _181_19; FStar_Syntax_Syntax.index = _87_51.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _87_51.FStar_Syntax_Syntax.sort}))
in (let _181_20 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str a.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (FStar_All.pipe_left escape _181_20))))


let primitive_projector_by_pos : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (

let fail = (fun _87_58 -> (match (()) with
| () -> begin
(let _181_30 = (let _181_29 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" _181_29 lid.FStar_Ident.str))
in (FStar_All.failwith _181_30))
end))
in (

let _87_62 = (FStar_TypeChecker_Env.lookup_datacon env lid)
in (match (_87_62) with
| (_87_60, t) -> begin
(match ((let _181_31 = (FStar_Syntax_Subst.compress t)
in _181_31.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _87_70 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_87_70) with
| (binders, _87_69) -> begin
if ((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(

let b = (FStar_List.nth binders i)
in (mk_term_projector_name lid (Prims.fst b)))
end
end))
end
| _87_73 -> begin
(fail ())
end)
end))))


let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (let _181_37 = (let _181_36 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str _181_36))
in (FStar_All.pipe_left escape _181_37)))


let mk_term_projector : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun lid a -> (let _181_43 = (let _181_42 = (mk_term_projector_name lid a)
in ((_181_42), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Term.mkFreeV _181_43)))


let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_SMTEncoding_Term.term = (fun lid i -> (let _181_49 = (let _181_48 = (mk_term_projector_name_by_pos lid i)
in ((_181_48), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Term.mkFreeV _181_49)))


let mk_data_tester = (fun env l x -> (FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x))


type varops_t =
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; mark : Prims.unit  ->  Prims.unit; reset_mark : Prims.unit  ->  Prims.unit; commit_mark : Prims.unit  ->  Prims.unit; new_var : FStar_Ident.ident  ->  Prims.int  ->  Prims.string; new_fvar : FStar_Ident.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_SMTEncoding_Term.term; next_id : Prims.unit  ->  Prims.int; mk_unique : Prims.string  ->  Prims.string}


let is_Mkvarops_t : varops_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkvarops_t"))))


let varops : varops_t = (

let initial_ctr = (Prims.parse_int "100")
in (

let ctr = (FStar_Util.mk_ref initial_ctr)
in (

let new_scope = (fun _87_98 -> (match (()) with
| () -> begin
(let _181_162 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (let _181_161 = (FStar_Util.smap_create (Prims.parse_int "100"))
in ((_181_162), (_181_161))))
end))
in (

let scopes = (let _181_164 = (let _181_163 = (new_scope ())
in (_181_163)::[])
in (FStar_Util.mk_ref _181_164))
in (

let mk_unique = (fun y -> (

let y = (escape y)
in (

let y = (match ((let _181_168 = (FStar_ST.read scopes)
in (FStar_Util.find_map _181_168 (fun _87_106 -> (match (_87_106) with
| (names, _87_105) -> begin
(FStar_Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_87_109) -> begin
(

let _87_111 = (FStar_Util.incr ctr)
in (let _181_171 = (let _181_170 = (let _181_169 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _181_169))
in (Prims.strcat "__" _181_170))
in (Prims.strcat y _181_171)))
end)
in (

let top_scope = (let _181_173 = (let _181_172 = (FStar_ST.read scopes)
in (FStar_List.hd _181_172))
in (FStar_All.pipe_left Prims.fst _181_173))
in (

let _87_115 = (FStar_Util.smap_add top_scope y true)
in y)))))
in (

let new_var = (fun pp rn -> (let _181_180 = (let _181_179 = (let _181_178 = (FStar_Util.string_of_int rn)
in (Prims.strcat "__" _181_178))
in (Prims.strcat pp.FStar_Ident.idText _181_179))
in (FStar_All.pipe_left mk_unique _181_180)))
in (

let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (

let next_id = (fun _87_123 -> (match (()) with
| () -> begin
(

let _87_124 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end))
in (

let fresh = (fun pfx -> (let _181_188 = (let _181_187 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _181_187))
in (FStar_Util.format2 "%s_%s" pfx _181_188)))
in (

let string_const = (fun s -> (match ((let _181_192 = (FStar_ST.read scopes)
in (FStar_Util.find_map _181_192 (fun _87_133 -> (match (_87_133) with
| (_87_131, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))) with
| Some (f) -> begin
f
end
| None -> begin
(

let id = (next_id ())
in (

let f = (let _181_193 = (FStar_SMTEncoding_Term.mk_String_const id)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString _181_193))
in (

let top_scope = (let _181_195 = (let _181_194 = (FStar_ST.read scopes)
in (FStar_List.hd _181_194))
in (FStar_All.pipe_left Prims.snd _181_195))
in (

let _87_140 = (FStar_Util.smap_add top_scope s f)
in f))))
end))
in (

let push = (fun _87_143 -> (match (()) with
| () -> begin
(let _181_200 = (let _181_199 = (new_scope ())
in (let _181_198 = (FStar_ST.read scopes)
in (_181_199)::_181_198))
in (FStar_ST.op_Colon_Equals scopes _181_200))
end))
in (

let pop = (fun _87_145 -> (match (()) with
| () -> begin
(let _181_204 = (let _181_203 = (FStar_ST.read scopes)
in (FStar_List.tl _181_203))
in (FStar_ST.op_Colon_Equals scopes _181_204))
end))
in (

let mark = (fun _87_147 -> (match (()) with
| () -> begin
(push ())
end))
in (

let reset_mark = (fun _87_149 -> (match (()) with
| () -> begin
(pop ())
end))
in (

let commit_mark = (fun _87_151 -> (match (()) with
| () -> begin
(match ((FStar_ST.read scopes)) with
| ((hd1, hd2))::((next1, next2))::tl -> begin
(

let _87_164 = (FStar_Util.smap_fold hd1 (fun key value v -> (FStar_Util.smap_add next1 key value)) ())
in (

let _87_169 = (FStar_Util.smap_fold hd2 (fun key value v -> (FStar_Util.smap_add next2 key value)) ())
in (FStar_ST.op_Colon_Equals scopes ((((next1), (next2)))::tl))))
end
| _87_172 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id; mk_unique = mk_unique})))))))))))))))


let unmangle : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv = (fun x -> (

let _87_174 = x
in (let _181_219 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _181_219; FStar_Syntax_Syntax.index = _87_174.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _87_174.FStar_Syntax_Syntax.sort})))


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
| Binding_var (_87_178) -> begin
_87_178
end))


let ___Binding_fvar____0 = (fun projectee -> (match (projectee) with
| Binding_fvar (_87_181) -> begin
_87_181
end))


let binder_of_eithervar = (fun v -> ((v), (None)))


type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_TypeChecker_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_SMTEncoding_Term.sort Prims.list * FStar_SMTEncoding_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}


let is_Mkenv_t : env_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_t"))))


let print_env : env_t  ->  Prims.string = (fun e -> (let _181_277 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun _87_2 -> (match (_87_2) with
| Binding_var (x, _87_196) -> begin
(FStar_Syntax_Print.bv_to_string x)
end
| Binding_fvar (l, _87_201, _87_203, _87_205) -> begin
(FStar_Syntax_Print.lid_to_string l)
end))))
in (FStar_All.pipe_right _181_277 (FStar_String.concat ", "))))


let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))


let caption_t : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.string Prims.option = (fun env t -> if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _181_287 = (FStar_Syntax_Print.term_to_string t)
in Some (_181_287))
end else begin
None
end)


let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (

let xsym = (varops.fresh x)
in (let _181_292 = (FStar_SMTEncoding_Term.mkFreeV ((xsym), (s)))
in ((xsym), (_181_292)))))


let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (let _181_297 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _181_297))
in (

let y = (FStar_SMTEncoding_Term.mkFreeV ((ysym), (FStar_SMTEncoding_Term.Term_sort)))
in ((ysym), (y), ((

let _87_219 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = (env.depth + (Prims.parse_int "1")); tcenv = _87_219.tcenv; warn = _87_219.warn; cache = _87_219.cache; nolabels = _87_219.nolabels; use_zfuel_name = _87_219.use_zfuel_name; encode_non_total_function_typ = _87_219.encode_non_total_function_typ}))))))


let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (

let y = (FStar_SMTEncoding_Term.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let _87_225 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = _87_225.depth; tcenv = _87_225.tcenv; warn = _87_225.warn; cache = _87_225.cache; nolabels = _87_225.nolabels; use_zfuel_name = _87_225.use_zfuel_name; encode_non_total_function_typ = _87_225.encode_non_total_function_typ}))))))


let new_term_constant_from_string : env_t  ->  FStar_Syntax_Syntax.bv  ->  Prims.string  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x str -> (

let ysym = (varops.mk_unique str)
in (

let y = (FStar_SMTEncoding_Term.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let _87_232 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = _87_232.depth; tcenv = _87_232.tcenv; warn = _87_232.warn; cache = _87_232.cache; nolabels = _87_232.nolabels; use_zfuel_name = _87_232.use_zfuel_name; encode_non_total_function_typ = _87_232.encode_non_total_function_typ}))))))


let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (

let _87_237 = env
in {bindings = (Binding_var (((x), (t))))::env.bindings; depth = _87_237.depth; tcenv = _87_237.tcenv; warn = _87_237.warn; cache = _87_237.cache; nolabels = _87_237.nolabels; use_zfuel_name = _87_237.use_zfuel_name; encode_non_total_function_typ = _87_237.encode_non_total_function_typ}))


let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let aux = (fun a' -> (lookup_binding env (fun _87_3 -> (match (_87_3) with
| Binding_var (b, t) when (FStar_Syntax_Syntax.bv_eq b a') -> begin
Some (((b), (t)))
end
| _87_249 -> begin
None
end))))
in (match ((aux a)) with
| None -> begin
(

let a = (unmangle a)
in (match ((aux a)) with
| None -> begin
(let _181_322 = (let _181_321 = (FStar_Syntax_Print.bv_to_string a)
in (FStar_Util.format1 "Bound term variable not found (after unmangling): %s" _181_321))
in (FStar_All.failwith _181_322))
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
in (let _181_333 = (

let _87_265 = env
in (let _181_332 = (let _181_331 = (let _181_330 = (let _181_329 = (let _181_328 = (FStar_SMTEncoding_Term.mkApp ((ftok), ([])))
in (FStar_All.pipe_left (fun _181_327 -> Some (_181_327)) _181_328))
in ((x), (fname), (_181_329), (None)))
in Binding_fvar (_181_330))
in (_181_331)::env.bindings)
in {bindings = _181_332; depth = _87_265.depth; tcenv = _87_265.tcenv; warn = _87_265.warn; cache = _87_265.cache; nolabels = _87_265.nolabels; use_zfuel_name = _87_265.use_zfuel_name; encode_non_total_function_typ = _87_265.encode_non_total_function_typ}))
in ((fname), (ftok), (_181_333))))))


let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun _87_4 -> (match (_87_4) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some (((t1), (t2), (t3)))
end
| _87_277 -> begin
None
end))))


let contains_name : env_t  ->  Prims.string  ->  Prims.bool = (fun env s -> (let _181_344 = (lookup_binding env (fun _87_5 -> (match (_87_5) with
| Binding_fvar (b, t1, t2, t3) when (b.FStar_Ident.str = s) -> begin
Some (())
end
| _87_288 -> begin
None
end)))
in (FStar_All.pipe_right _181_344 FStar_Option.isSome)))


let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _181_350 = (let _181_349 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" _181_349))
in (FStar_All.failwith _181_350))
end
| Some (s) -> begin
s
end))


let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (

let _87_298 = env
in {bindings = (Binding_fvar (((x), (fname), (ftok), (None))))::env.bindings; depth = _87_298.depth; tcenv = _87_298.tcenv; warn = _87_298.warn; cache = _87_298.cache; nolabels = _87_298.nolabels; use_zfuel_name = _87_298.use_zfuel_name; encode_non_total_function_typ = _87_298.encode_non_total_function_typ}))


let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (

let _87_307 = (lookup_lid env x)
in (match (_87_307) with
| (t1, t2, _87_306) -> begin
(

let t3 = (let _181_367 = (let _181_366 = (let _181_365 = (FStar_SMTEncoding_Term.mkApp (("ZFuel"), ([])))
in (_181_365)::[])
in ((f), (_181_366)))
in (FStar_SMTEncoding_Term.mkApp _181_367))
in (

let _87_309 = env
in {bindings = (Binding_fvar (((x), (t1), (t2), (Some (t3)))))::env.bindings; depth = _87_309.depth; tcenv = _87_309.tcenv; warn = _87_309.warn; cache = _87_309.cache; nolabels = _87_309.nolabels; use_zfuel_name = _87_309.use_zfuel_name; encode_non_total_function_typ = _87_309.encode_non_total_function_typ}))
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
| _87_322 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (_87_326, (fuel)::[]) -> begin
if (let _181_373 = (let _181_372 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right _181_372 Prims.fst))
in (FStar_Util.starts_with _181_373 "fuel")) then begin
(let _181_376 = (let _181_375 = (FStar_SMTEncoding_Term.mkFreeV ((name), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_ApplyTF _181_375 fuel))
in (FStar_All.pipe_left (fun _181_374 -> Some (_181_374)) _181_376))
end else begin
Some (t)
end
end
| _87_332 -> begin
Some (t)
end)
end
| _87_334 -> begin
None
end)
end)
end))


let lookup_free_var = (fun env a -> (match ((try_lookup_free_var env a.FStar_Syntax_Syntax.v)) with
| Some (t) -> begin
t
end
| None -> begin
(let _181_380 = (let _181_379 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _181_379))
in (FStar_All.failwith _181_380))
end))


let lookup_free_var_name = (fun env a -> (

let _87_347 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_87_347) with
| (x, _87_344, _87_346) -> begin
x
end)))


let lookup_free_var_sym = (fun env a -> (

let _87_353 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_87_353) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.hash = _87_357; FStar_SMTEncoding_Term.freevars = _87_355}) when env.use_zfuel_name -> begin
((g), (zf))
end
| _87_365 -> begin
(match (sym) with
| None -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end
| Some (sym) -> begin
(match (sym.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, (fuel)::[]) -> begin
((g), ((fuel)::[]))
end
| _87_375 -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end)
end)
end)
end)))


let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun _87_6 -> (match (_87_6) with
| Binding_fvar (_87_380, nm', tok, _87_384) when (nm = nm') -> begin
tok
end
| _87_388 -> begin
None
end))))


let mkForall_fuel' = (fun n _87_393 -> (match (_87_393) with
| (pats, vars, body) -> begin
(

let fallback = (fun _87_395 -> (match (()) with
| () -> begin
(FStar_SMTEncoding_Term.mkForall ((pats), (vars), (body)))
end))
in if (FStar_Options.unthrottle_inductives ()) then begin
(fallback ())
end else begin
(

let _87_398 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_87_398) with
| (fsym, fterm) -> begin
(

let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Term.mkApp (("HasTypeFuel"), ((fterm)::args)))
end
| _87_408 -> begin
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
(let _181_397 = (add_fuel guards)
in (FStar_SMTEncoding_Term.mk_and_l _181_397))
end
| _87_421 -> begin
(let _181_398 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _181_398 FStar_List.hd))
end)
in (FStar_SMTEncoding_Term.mkImp ((guard), (body'))))
end
| _87_424 -> begin
body
end)
in (

let vars = (((fsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars
in (FStar_SMTEncoding_Term.mkForall ((pats), (vars), (body)))))))
end))
end)
end))


let mkForall_fuel : (FStar_SMTEncoding_Term.pat Prims.list Prims.list * FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (mkForall_fuel' (Prims.parse_int "1"))


let head_normal : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let t = (FStar_Syntax_Util.unmeta t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) -> begin
true
end
| (FStar_Syntax_Syntax.Tm_fvar (fv)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(let _181_404 = (FStar_TypeChecker_Env.lookup_definition FStar_TypeChecker_Env.OnlyInline env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _181_404 FStar_Option.isNone))
end
| _87_463 -> begin
false
end)))


let head_redex : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (match ((let _181_409 = (FStar_Syntax_Util.un_uinst t)
in _181_409.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_87_467) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(let _181_410 = (FStar_TypeChecker_Env.lookup_definition FStar_TypeChecker_Env.OnlyInline env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _181_410 FStar_Option.isSome))
end
| _87_472 -> begin
false
end))


let whnf : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> if (head_normal env t) then begin
t
end else begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
end)


let norm : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t))


let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (let _181_423 = (let _181_421 = (FStar_Syntax_Syntax.null_binder t)
in (_181_421)::[])
in (let _181_422 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Util.abs _181_423 _181_422 None))))


let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(let _181_430 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out _181_430))
end
| s -> begin
(

let _87_484 = ()
in (let _181_431 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTT out _181_431)))
end)) e)))


let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Term.mk_ApplyTT e)))


let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun _87_7 -> (match (_87_7) with
| (FStar_SMTEncoding_Term.Var ("ApplyTT")) | (FStar_SMTEncoding_Term.Var ("ApplyTF")) -> begin
true
end
| _87_494 -> begin
false
end))


let is_eta : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env vars t -> (

let rec aux = (fun t xs -> (match (((t.FStar_SMTEncoding_Term.tm), (xs))) with
| (FStar_SMTEncoding_Term.App (app, (f)::({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.hash = _87_505; FStar_SMTEncoding_Term.freevars = _87_503})::[]), (x)::xs) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), _87_523) -> begin
if (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v)
end
| _87_530 -> begin
false
end)) args vars)) then begin
(tok_of_name env f)
end else begin
None
end
end
| (_87_532, []) -> begin
(

let fvs = (FStar_SMTEncoding_Term.free_variables t)
in if (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (not ((FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)))))) then begin
Some (t)
end else begin
None
end)
end
| _87_538 -> begin
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


let encode_const : FStar_Const.sconst  ->  FStar_SMTEncoding_Term.term = (fun _87_8 -> (match (_87_8) with
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
(let _181_488 = (let _181_487 = (let _181_486 = (let _181_485 = (FStar_SMTEncoding_Term.mkInteger' (FStar_Util.int_of_char c))
in (FStar_SMTEncoding_Term.boxInt _181_485))
in (_181_486)::[])
in (("FStar.Char.Char"), (_181_487)))
in (FStar_SMTEncoding_Term.mkApp _181_488))
end
| FStar_Const.Const_int (i, None) -> begin
(let _181_489 = (FStar_SMTEncoding_Term.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt _181_489))
end
| FStar_Const.Const_int (i, Some (_87_558)) -> begin
(FStar_All.failwith "Machine integers should be desugared")
end
| FStar_Const.Const_string (bytes, _87_564) -> begin
(let _181_490 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _181_490))
end
| FStar_Const.Const_range (r) -> begin
FStar_SMTEncoding_Term.mk_Range_const
end
| FStar_Const.Const_effect -> begin
FStar_SMTEncoding_Term.mk_Term_type
end
| c -> begin
(let _181_492 = (let _181_491 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" _181_491))
in (FStar_All.failwith _181_492))
end))


let as_function_typ : env_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (

let rec aux = (fun norm t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_87_578) -> begin
t
end
| FStar_Syntax_Syntax.Tm_refine (_87_581) -> begin
(let _181_501 = (FStar_Syntax_Util.unrefine t)
in (aux true _181_501))
end
| _87_584 -> begin
if norm then begin
(let _181_502 = (whnf env t)
in (aux false _181_502))
end else begin
(let _181_505 = (let _181_504 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (let _181_503 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _181_504 _181_503)))
in (FStar_All.failwith _181_505))
end
end)))
in (aux true t0)))


let curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun k -> (

let k = (FStar_Syntax_Subst.compress k)
in (match (k.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| _87_592 -> begin
(let _181_508 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (_181_508)))
end)))


let rec encode_binders : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> (

let _87_596 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _181_556 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" _181_556))
end else begin
()
end
in (

let _87_624 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _87_603 b -> (match (_87_603) with
| (vars, guards, env, decls, names) -> begin
(

let _87_618 = (

let x = (unmangle (Prims.fst b))
in (

let _87_609 = (gen_term_var env x)
in (match (_87_609) with
| (xxsym, xx, env') -> begin
(

let _87_612 = (let _181_559 = (norm env x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt _181_559 env xx))
in (match (_87_612) with
| (guard_x_t, decls') -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (guard_x_t), (env'), (decls'), (x))
end))
end)))
in (match (_87_618) with
| (v, g, env, decls', n) -> begin
(((v)::vars), ((g)::guards), (env), ((FStar_List.append decls decls')), ((n)::names))
end))
end)) (([]), ([]), (env), ([]), ([]))))
in (match (_87_624) with
| (vars, guards, env, decls, names) -> begin
(((FStar_List.rev vars)), ((FStar_List.rev guards)), (env), (decls), ((FStar_List.rev names)))
end))))
and encode_term_pred : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let _87_631 = (encode_term t env)
in (match (_87_631) with
| (t, decls) -> begin
(let _181_564 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t)
in ((_181_564), (decls)))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let _87_638 = (encode_term t env)
in (match (_87_638) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _181_569 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t)
in ((_181_569), (decls)))
end
| Some (f) -> begin
(let _181_570 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t)
in ((_181_570), (decls)))
end)
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let t0 = (FStar_Syntax_Subst.compress t)
in (

let _87_645 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _181_575 = (FStar_Syntax_Print.tag_of_term t)
in (let _181_574 = (FStar_Syntax_Print.tag_of_term t0)
in (let _181_573 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" _181_575 _181_574 _181_573))))
end else begin
()
end
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _181_580 = (let _181_579 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (let _181_578 = (FStar_Syntax_Print.tag_of_term t0)
in (let _181_577 = (FStar_Syntax_Print.term_to_string t0)
in (let _181_576 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _181_579 _181_578 _181_577 _181_576)))))
in (FStar_All.failwith _181_580))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _181_582 = (let _181_581 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" _181_581))
in (FStar_All.failwith _181_582))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, k, _87_656) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_meta (t, _87_661) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t = (lookup_term_var env x)
in ((t), ([])))
end
| FStar_Syntax_Syntax.Tm_fvar (v) -> begin
(let _181_583 = (lookup_free_var env v.FStar_Syntax_Syntax.fv_name)
in ((_181_583), ([])))
end
| FStar_Syntax_Syntax.Tm_type (_87_670) -> begin
((FStar_SMTEncoding_Term.mk_Term_type), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t, _87_674) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(let _181_584 = (encode_const c)
in ((_181_584), ([])))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _87_685 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_87_685) with
| (binders, res) -> begin
if ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res)) then begin
(

let _87_692 = (encode_binders None binders env)
in (match (_87_692) with
| (vars, guards, env', decls, _87_691) -> begin
(

let fsym = (let _181_585 = (varops.fresh "f")
in ((_181_585), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (

let app = (mk_Apply f vars)
in (

let _87_700 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post (

let _87_696 = env.tcenv
in {FStar_TypeChecker_Env.solver = _87_696.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _87_696.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _87_696.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _87_696.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _87_696.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _87_696.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _87_696.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _87_696.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _87_696.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _87_696.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _87_696.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _87_696.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _87_696.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _87_696.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _87_696.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _87_696.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _87_696.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _87_696.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _87_696.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _87_696.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _87_696.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _87_696.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _87_696.FStar_TypeChecker_Env.qname_and_index}) res)
in (match (_87_700) with
| (pre_opt, res_t) -> begin
(

let _87_703 = (encode_term_pred None res_t env' app)
in (match (_87_703) with
| (res_pred, decls') -> begin
(

let _87_712 = (match (pre_opt) with
| None -> begin
(let _181_586 = (FStar_SMTEncoding_Term.mk_and_l guards)
in ((_181_586), ([])))
end
| Some (pre) -> begin
(

let _87_709 = (encode_formula pre env')
in (match (_87_709) with
| (guard, decls0) -> begin
(let _181_587 = (FStar_SMTEncoding_Term.mk_and_l ((guard)::guards))
in ((_181_587), (decls0)))
end))
end)
in (match (_87_712) with
| (guards, guard_decls) -> begin
(

let t_interp = (let _181_589 = (let _181_588 = (FStar_SMTEncoding_Term.mkImp ((guards), (res_pred)))
in ((((app)::[])::[]), (vars), (_181_588)))
in (FStar_SMTEncoding_Term.mkForall _181_589))
in (

let cvars = (let _181_591 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right _181_591 (FStar_List.filter (fun _87_717 -> (match (_87_717) with
| (x, _87_716) -> begin
(x <> (Prims.fst fsym))
end)))))
in (

let tkey = (FStar_SMTEncoding_Term.mkForall (([]), ((fsym)::cvars), (t_interp)))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t', sorts, _87_723) -> begin
(let _181_594 = (let _181_593 = (let _181_592 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in ((t'), (_181_592)))
in (FStar_SMTEncoding_Term.mkApp _181_593))
in ((_181_594), ([])))
end
| None -> begin
(

let tsym = (let _181_596 = (let _181_595 = (FStar_Util.digest_of_string tkey.FStar_SMTEncoding_Term.hash)
in (Prims.strcat "Tm_arrow_" _181_595))
in (varops.mk_unique _181_596))
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let caption = if (FStar_Options.log_queries ()) then begin
(let _181_597 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in Some (_181_597))
end else begin
None
end
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (caption)))
in (

let t = (let _181_599 = (let _181_598 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in ((tsym), (_181_598)))
in (FStar_SMTEncoding_Term.mkApp _181_599))
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let k_assumption = (

let a_name = Some ((Prims.strcat "kinding_" tsym))
in (let _181_601 = (let _181_600 = (FStar_SMTEncoding_Term.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((_181_600), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_181_601)))
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t)
in (

let pre_typing = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in (let _181_608 = (let _181_607 = (let _181_606 = (let _181_605 = (let _181_604 = (let _181_603 = (let _181_602 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _181_602))
in ((f_has_t), (_181_603)))
in (FStar_SMTEncoding_Term.mkImp _181_604))
in ((((f_has_t)::[])::[]), ((fsym)::cvars), (_181_605)))
in (mkForall_fuel _181_606))
in ((_181_607), (Some ("pre-typing for functions")), (a_name)))
in FStar_SMTEncoding_Term.Assume (_181_608)))
in (

let t_interp = (

let a_name = Some ((Prims.strcat "interpretation_" tsym))
in (let _181_612 = (let _181_611 = (let _181_610 = (let _181_609 = (FStar_SMTEncoding_Term.mkIff ((f_has_t_z), (t_interp)))
in ((((f_has_t_z)::[])::[]), ((fsym)::cvars), (_181_609)))
in (FStar_SMTEncoding_Term.mkForall _181_610))
in ((_181_611), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_181_612)))
in (

let t_decls = (FStar_List.append ((tdecl)::decls) (FStar_List.append decls' (FStar_List.append guard_decls ((k_assumption)::(pre_typing)::(t_interp)::[]))))
in (

let _87_742 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash ((tsym), (cvar_sorts), (t_decls)))
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
in (let _181_614 = (let _181_613 = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in ((_181_613), (Some ("Typing for non-total arrows")), (a_name)))
in FStar_SMTEncoding_Term.Assume (_181_614)))
in (

let fsym = (("f"), (FStar_SMTEncoding_Term.Term_sort))
in (

let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let t_interp = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in (let _181_621 = (let _181_620 = (let _181_619 = (let _181_618 = (let _181_617 = (let _181_616 = (let _181_615 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _181_615))
in ((f_has_t), (_181_616)))
in (FStar_SMTEncoding_Term.mkImp _181_617))
in ((((f_has_t)::[])::[]), ((fsym)::[]), (_181_618)))
in (mkForall_fuel _181_619))
in ((_181_620), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_181_621)))
in ((t), ((tdecl)::(t_kinding)::(t_interp)::[]))))))))))
end
end))
end
| FStar_Syntax_Syntax.Tm_refine (_87_755) -> begin
(

let _87_775 = (match ((FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.tk = _87_762; FStar_Syntax_Syntax.pos = _87_760; FStar_Syntax_Syntax.vars = _87_758} -> begin
(

let _87_770 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) f)
in (match (_87_770) with
| (b, f) -> begin
(let _181_623 = (let _181_622 = (FStar_List.hd b)
in (Prims.fst _181_622))
in ((_181_623), (f)))
end))
end
| _87_772 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_87_775) with
| (x, f) -> begin
(

let _87_778 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (_87_778) with
| (base_t, decls) -> begin
(

let _87_782 = (gen_term_var env x)
in (match (_87_782) with
| (x, xtm, env') -> begin
(

let _87_785 = (encode_formula f env')
in (match (_87_785) with
| (refinement, decls') -> begin
(

let _87_788 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_87_788) with
| (fsym, fterm) -> begin
(

let encoding = (let _181_625 = (let _181_624 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in ((_181_624), (refinement)))
in (FStar_SMTEncoding_Term.mkAnd _181_625))
in (

let cvars = (let _181_627 = (FStar_SMTEncoding_Term.free_variables encoding)
in (FStar_All.pipe_right _181_627 (FStar_List.filter (fun _87_793 -> (match (_87_793) with
| (y, _87_792) -> begin
((y <> x) && (y <> fsym))
end)))))
in (

let xfv = ((x), (FStar_SMTEncoding_Term.Term_sort))
in (

let ffv = ((fsym), (FStar_SMTEncoding_Term.Fuel_sort))
in (

let tkey = (FStar_SMTEncoding_Term.mkForall (([]), ((ffv)::(xfv)::cvars), (encoding)))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _87_800, _87_802) -> begin
(let _181_630 = (let _181_629 = (let _181_628 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in ((t), (_181_628)))
in (FStar_SMTEncoding_Term.mkApp _181_629))
in ((_181_630), ([])))
end
| None -> begin
(

let tsym = (let _181_632 = (let _181_631 = (FStar_Util.digest_of_string tkey.FStar_SMTEncoding_Term.hash)
in (Prims.strcat "Tm_refine_" _181_631))
in (varops.mk_unique _181_632))
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let t = (let _181_634 = (let _181_633 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in ((tsym), (_181_633)))
in (FStar_SMTEncoding_Term.mkApp _181_634))
in (

let x_has_t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let t_haseq_base = (FStar_SMTEncoding_Term.mk_haseq base_t)
in (

let t_haseq_ref = (FStar_SMTEncoding_Term.mk_haseq t)
in (

let t_haseq = (let _181_638 = (let _181_637 = (let _181_636 = (let _181_635 = (FStar_SMTEncoding_Term.mkIff ((t_haseq_ref), (t_haseq_base)))
in ((((t_haseq_ref)::[])::[]), (cvars), (_181_635)))
in (FStar_SMTEncoding_Term.mkForall _181_636))
in ((_181_637), (Some ((Prims.strcat "haseq for " tsym))), (Some ((Prims.strcat "haseq" tsym)))))
in FStar_SMTEncoding_Term.Assume (_181_638))
in (

let t_kinding = (let _181_640 = (let _181_639 = (FStar_SMTEncoding_Term.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((_181_639), (Some ("refinement kinding")), (Some ((Prims.strcat "refinement_kinding_" tsym)))))
in FStar_SMTEncoding_Term.Assume (_181_640))
in (

let t_interp = (let _181_646 = (let _181_645 = (let _181_642 = (let _181_641 = (FStar_SMTEncoding_Term.mkIff ((x_has_t), (encoding)))
in ((((x_has_t)::[])::[]), ((ffv)::(xfv)::cvars), (_181_641)))
in (FStar_SMTEncoding_Term.mkForall _181_642))
in (let _181_644 = (let _181_643 = (FStar_Syntax_Print.term_to_string t0)
in Some (_181_643))
in ((_181_645), (_181_644), (Some ((Prims.strcat "refinement_interpretation_" tsym))))))
in FStar_SMTEncoding_Term.Assume (_181_646))
in (

let t_decls = (FStar_List.append decls (FStar_List.append decls' ((tdecl)::(t_kinding)::(t_interp)::(t_haseq)::[])))
in (

let _87_818 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash ((tsym), (cvar_sorts), (t_decls)))
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

let ttm = (let _181_647 = (FStar_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Term.mk_Term_uvar _181_647))
in (

let _87_827 = (encode_term_pred None k env ttm)
in (match (_87_827) with
| (t_has_k, decls) -> begin
(

let d = (let _181_653 = (let _181_652 = (let _181_651 = (let _181_650 = (let _181_649 = (let _181_648 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _181_648))
in (FStar_Util.format1 "uvar_typing_%s" _181_649))
in (varops.mk_unique _181_650))
in Some (_181_651))
in ((t_has_k), (Some ("Uvar typing")), (_181_652)))
in FStar_SMTEncoding_Term.Assume (_181_653))
in ((ttm), ((FStar_List.append decls ((d)::[])))))
end)))
end
| FStar_Syntax_Syntax.Tm_app (_87_830) -> begin
(

let _87_834 = (FStar_Syntax_Util.head_and_args t0)
in (match (_87_834) with
| (head, args_e) -> begin
(match ((let _181_655 = (let _181_654 = (FStar_Syntax_Subst.compress head)
in _181_654.FStar_Syntax_Syntax.n)
in ((_181_655), (args_e)))) with
| (_87_836, _87_838) when (head_redex env head) -> begin
(let _181_656 = (whnf env t)
in (encode_term _181_656 env))
end
| ((FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), (_)::((v1, _))::((v2, _))::[])) | ((FStar_Syntax_Syntax.Tm_fvar (fv), (_)::((v1, _))::((v2, _))::[])) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
(

let _87_878 = (encode_term v1 env)
in (match (_87_878) with
| (v1, decls1) -> begin
(

let _87_881 = (encode_term v2 env)
in (match (_87_881) with
| (v2, decls2) -> begin
(let _181_657 = (FStar_SMTEncoding_Term.mk_LexCons v1 v2)
in ((_181_657), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), (_87_890)::(_87_887)::_87_885) -> begin
(

let e0 = (let _181_661 = (let _181_660 = (let _181_659 = (let _181_658 = (FStar_List.hd args_e)
in (_181_658)::[])
in ((head), (_181_659)))
in FStar_Syntax_Syntax.Tm_app (_181_660))
in (FStar_Syntax_Syntax.mk _181_661 None head.FStar_Syntax_Syntax.pos))
in (

let e = (let _181_664 = (let _181_663 = (let _181_662 = (FStar_List.tl args_e)
in ((e0), (_181_662)))
in FStar_Syntax_Syntax.Tm_app (_181_663))
in (FStar_Syntax_Syntax.mk _181_664 None t0.FStar_Syntax_Syntax.pos))
in (encode_term e env)))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), ((arg, _87_899))::[]) -> begin
(

let _87_905 = (encode_term arg env)
in (match (_87_905) with
| (tm, decls) -> begin
(let _181_665 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Var ("Reify")), ((tm)::[])))))
in ((_181_665), (decls)))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (_87_907)), ((arg, _87_912))::[]) -> begin
(encode_term arg env)
end
| _87_917 -> begin
(

let _87_920 = (encode_args args_e env)
in (match (_87_920) with
| (args, decls) -> begin
(

let encode_partial_app = (fun ht_opt -> (

let _87_925 = (encode_term head env)
in (match (_87_925) with
| (head, decls') -> begin
(

let app_tm = (mk_Apply_args head args)
in (match (ht_opt) with
| None -> begin
((app_tm), ((FStar_List.append decls decls')))
end
| Some (formals, c) -> begin
(

let _87_934 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (_87_934) with
| (formals, rest) -> begin
(

let subst = (FStar_List.map2 (fun _87_938 _87_942 -> (match (((_87_938), (_87_942))) with
| ((bv, _87_937), (a, _87_941)) -> begin
FStar_Syntax_Syntax.NT (((bv), (a)))
end)) formals args_e)
in (

let ty = (let _181_670 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right _181_670 (FStar_Syntax_Subst.subst subst)))
in (

let _87_947 = (encode_term_pred None ty env app_tm)
in (match (_87_947) with
| (has_type, decls'') -> begin
(

let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (

let e_typing = (let _181_676 = (let _181_675 = (FStar_SMTEncoding_Term.mkForall ((((has_type)::[])::[]), (cvars), (has_type)))
in (let _181_674 = (let _181_673 = (let _181_672 = (let _181_671 = (FStar_Util.digest_of_string app_tm.FStar_SMTEncoding_Term.hash)
in (Prims.strcat "partial_app_typing_" _181_671))
in (varops.mk_unique _181_672))
in Some (_181_673))
in ((_181_675), (Some ("Partial app typing")), (_181_674))))
in FStar_SMTEncoding_Term.Assume (_181_676))
in ((app_tm), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' ((e_typing)::[]))))))))
end))))
end))
end))
end)))
in (

let encode_full_app = (fun fv -> (

let _87_954 = (lookup_free_var_sym env fv)
in (match (_87_954) with
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
(let _181_680 = (let _181_679 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _181_679 Prims.snd))
in Some (_181_680))
end
| FStar_Syntax_Syntax.Tm_ascribed (_87_986, FStar_Util.Inl (t), _87_990) -> begin
Some (t)
end
| FStar_Syntax_Syntax.Tm_ascribed (_87_994, FStar_Util.Inr (c), _87_998) -> begin
Some ((FStar_Syntax_Util.comp_result c))
end
| _87_1002 -> begin
None
end)
in (match (head_type) with
| None -> begin
(encode_partial_app None)
end
| Some (head_type) -> begin
(

let head_type = (let _181_681 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine _181_681))
in (

let _87_1010 = (curried_arrow_formals_comp head_type)
in (match (_87_1010) with
| (formals, c) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| _87_1026 -> begin
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

let _87_1035 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_87_1035) with
| (bs, body, opening) -> begin
(

let fallback = (fun _87_1037 -> (match (()) with
| () -> begin
(

let f = (varops.fresh "Tm_abs")
in (

let decl = FStar_SMTEncoding_Term.DeclFun (((f), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Imprecise function encoding"))))
in (let _181_684 = (FStar_SMTEncoding_Term.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in ((_181_684), ((decl)::[])))))
end))
in (

let is_impure = (fun _87_9 -> (match (_87_9) with
| FStar_Util.Inl (lc) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)))
end
| FStar_Util.Inr (eff) -> begin
(let _181_687 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv eff)
in (FStar_All.pipe_right _181_687 Prims.op_Negation))
end))
in (

let codomain_eff = (fun lc -> (match (lc) with
| FStar_Util.Inl (lc) -> begin
(let _181_692 = (let _181_690 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening _181_690))
in (FStar_All.pipe_right _181_692 (fun _181_691 -> Some (_181_691))))
end
| FStar_Util.Inr (eff) -> begin
(

let new_uvar = (fun _87_1053 -> (match (()) with
| () -> begin
(let _181_695 = (FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange [] FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _181_695 Prims.fst))
end))
in if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid) then begin
(let _181_698 = (let _181_696 = (new_uvar ())
in (FStar_Syntax_Syntax.mk_Total _181_696))
in (FStar_All.pipe_right _181_698 (fun _181_697 -> Some (_181_697))))
end else begin
if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid) then begin
(let _181_701 = (let _181_699 = (new_uvar ())
in (FStar_Syntax_Syntax.mk_GTotal _181_699))
in (FStar_All.pipe_right _181_701 (fun _181_700 -> Some (_181_700))))
end else begin
None
end
end)
end))
in (match (lopt) with
| None -> begin
(

let _87_1055 = (let _181_703 = (let _181_702 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s" _181_702))
in (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos _181_703))
in (fallback ()))
end
| Some (lc) -> begin
if (is_impure lc) then begin
(fallback ())
end else begin
(

let _87_1065 = (encode_binders None bs env)
in (match (_87_1065) with
| (vars, guards, envbody, decls, _87_1064) -> begin
(

let _87_1068 = (encode_term body envbody)
in (match (_87_1068) with
| (body, decls') -> begin
(

let key_body = (let _181_707 = (let _181_706 = (let _181_705 = (let _181_704 = (FStar_SMTEncoding_Term.mk_and_l guards)
in ((_181_704), (body)))
in (FStar_SMTEncoding_Term.mkImp _181_705))
in (([]), (vars), (_181_706)))
in (FStar_SMTEncoding_Term.mkForall _181_707))
in (

let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (

let tkey = (FStar_SMTEncoding_Term.mkForall (([]), (cvars), (key_body)))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _87_1074, _87_1076) -> begin
(let _181_710 = (let _181_709 = (let _181_708 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in ((t), (_181_708)))
in (FStar_SMTEncoding_Term.mkApp _181_709))
in ((_181_710), ([])))
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

let fsym = (let _181_712 = (let _181_711 = (FStar_Util.digest_of_string tkey.FStar_SMTEncoding_Term.hash)
in (Prims.strcat "Tm_abs_" _181_711))
in (varops.mk_unique _181_712))
in (

let fdecl = FStar_SMTEncoding_Term.DeclFun (((fsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let f = (let _181_714 = (let _181_713 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in ((fsym), (_181_713)))
in (FStar_SMTEncoding_Term.mkApp _181_714))
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

let _87_1094 = (encode_term_pred None tfun env f)
in (match (_87_1094) with
| (f_has_t, decls'') -> begin
(

let a_name = Some ((Prims.strcat "typing_" fsym))
in (let _181_718 = (let _181_717 = (let _181_716 = (let _181_715 = (FStar_SMTEncoding_Term.mkForall ((((f)::[])::[]), (cvars), (f_has_t)))
in ((_181_715), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_181_716))
in (_181_717)::[])
in (FStar_List.append decls'' _181_718)))
end)))
end)
in (

let interp_f = (

let a_name = Some ((Prims.strcat "interpretation_" fsym))
in (let _181_722 = (let _181_721 = (let _181_720 = (let _181_719 = (FStar_SMTEncoding_Term.mkEq ((app), (body)))
in ((((app)::[])::[]), ((FStar_List.append vars cvars)), (_181_719)))
in (FStar_SMTEncoding_Term.mkForall _181_720))
in ((_181_721), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_181_722)))
in (

let f_decls = (FStar_List.append decls (FStar_List.append decls' (FStar_List.append ((fdecl)::typing_f) ((interp_f)::[]))))
in (

let _87_1100 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash ((fsym), (cvar_sorts), (f_decls)))
in ((f), (f_decls)))))))))))
end)
end))))
end))
end))
end
end))))
end))
end
| FStar_Syntax_Syntax.Tm_let ((_87_1103, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_87_1115); FStar_Syntax_Syntax.lbunivs = _87_1113; FStar_Syntax_Syntax.lbtyp = _87_1111; FStar_Syntax_Syntax.lbeff = _87_1109; FStar_Syntax_Syntax.lbdef = _87_1107})::_87_1105), _87_1121) -> begin
(FStar_All.failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _87_1130; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _87_1127; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (_87_1140) -> begin
(

let _87_1142 = (FStar_TypeChecker_Errors.diag t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (

let e = (varops.fresh "let-rec")
in (

let decl_e = FStar_SMTEncoding_Term.DeclFun (((e), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (let _181_723 = (FStar_SMTEncoding_Term.mkFreeV ((e), (FStar_SMTEncoding_Term.Term_sort)))
in ((_181_723), ((decl_e)::[]))))))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end))))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (

let _87_1158 = (encode_term e1 env)
in (match (_87_1158) with
| (ee1, decls1) -> begin
(

let _87_1161 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) e2)
in (match (_87_1161) with
| (xs, e2) -> begin
(

let _87_1165 = (FStar_List.hd xs)
in (match (_87_1165) with
| (x, _87_1164) -> begin
(

let env' = (push_term_var env x ee1)
in (

let _87_1169 = (encode_body e2 env')
in (match (_87_1169) with
| (ee2, decls2) -> begin
((ee2), ((FStar_List.append decls1 decls2)))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (

let _87_1177 = (encode_term e env)
in (match (_87_1177) with
| (scr, decls) -> begin
(

let _87_1214 = (FStar_List.fold_right (fun b _87_1181 -> (match (_87_1181) with
| (else_case, decls) -> begin
(

let _87_1185 = (FStar_Syntax_Subst.open_branch b)
in (match (_87_1185) with
| (p, w, br) -> begin
(

let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun _87_1189 _87_1192 -> (match (((_87_1189), (_87_1192))) with
| ((env0, pattern), (else_case, decls)) -> begin
(

let guard = (pattern.guard scr)
in (

let projections = (pattern.projections scr)
in (

let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env _87_1198 -> (match (_87_1198) with
| (x, t) -> begin
(push_term_var env x t)
end)) env))
in (

let _87_1208 = (match (w) with
| None -> begin
((guard), ([]))
end
| Some (w) -> begin
(

let _87_1205 = (encode_term w env)
in (match (_87_1205) with
| (w, decls2) -> begin
(let _181_757 = (let _181_756 = (let _181_755 = (let _181_754 = (let _181_753 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Term.mkTrue)
in ((w), (_181_753)))
in (FStar_SMTEncoding_Term.mkEq _181_754))
in ((guard), (_181_755)))
in (FStar_SMTEncoding_Term.mkAnd _181_756))
in ((_181_757), (decls2)))
end))
end)
in (match (_87_1208) with
| (guard, decls2) -> begin
(

let _87_1211 = (encode_br br env)
in (match (_87_1211) with
| (br, decls3) -> begin
(let _181_758 = (FStar_SMTEncoding_Term.mkITE ((guard), (br), (else_case)))
in ((_181_758), ((FStar_List.append decls (FStar_List.append decls2 decls3)))))
end))
end)))))
end)) patterns ((else_case), (decls))))
end))
end)) pats ((default_case), (decls)))
in (match (_87_1214) with
| (match_tm, decls) -> begin
((match_tm), (decls))
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _87_1220 -> begin
(let _181_761 = (encode_one_pat env pat)
in (_181_761)::[])
end))
and encode_one_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> (

let _87_1223 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _181_764 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" _181_764))
end else begin
()
end
in (

let _87_1227 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (_87_1227) with
| (vars, pat_term) -> begin
(

let _87_1239 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun _87_1230 v -> (match (_87_1230) with
| (env, vars) -> begin
(

let _87_1236 = (gen_term_var env v)
in (match (_87_1236) with
| (xx, _87_1234, env) -> begin
((env), ((((v), (((xx), (FStar_SMTEncoding_Term.Term_sort)))))::vars))
end))
end)) ((env), ([]))))
in (match (_87_1239) with
| (env, vars) -> begin
(

let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_87_1244) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_dot_term (_)) -> begin
FStar_SMTEncoding_Term.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _181_772 = (let _181_771 = (encode_const c)
in ((scrutinee), (_181_771)))
in (FStar_SMTEncoding_Term.mkEq _181_772))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let is_f = (mk_data_tester env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _87_1266 -> (match (_87_1266) with
| (arg, _87_1265) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _181_775 = (FStar_SMTEncoding_Term.mkApp ((proj), ((scrutinee)::[])))
in (mk_guard arg _181_775)))
end))))
in (FStar_SMTEncoding_Term.mk_and_l ((is_f)::sub_term_guards))))
end))
in (

let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_87_1273) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _)) | (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_constant (_87_1283) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(let _181_783 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _87_1293 -> (match (_87_1293) with
| (arg, _87_1292) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _181_782 = (FStar_SMTEncoding_Term.mkApp ((proj), ((scrutinee)::[])))
in (mk_projections arg _181_782)))
end))))
in (FStar_All.pipe_right _181_783 FStar_List.flatten))
end))
in (

let pat_term = (fun _87_1296 -> (match (()) with
| () -> begin
(encode_term pat_term env)
end))
in (

let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in ((env), (pattern))))))
end))
end))))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (

let _87_1312 = (FStar_All.pipe_right l (FStar_List.fold_left (fun _87_1302 _87_1306 -> (match (((_87_1302), (_87_1306))) with
| ((tms, decls), (t, _87_1305)) -> begin
(

let _87_1309 = (encode_term t env)
in (match (_87_1309) with
| (t, decls') -> begin
(((t)::tms), ((FStar_List.append decls decls')))
end))
end)) (([]), ([]))))
in (match (_87_1312) with
| (l, decls) -> begin
(((FStar_List.rev l)), (decls))
end)))
and encode_function_type_as_formula : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun induction_on new_pats t env -> (

let list_elements = (fun e -> (match ((FStar_Syntax_Util.list_elements e)) with
| Some (l) -> begin
l
end
| None -> begin
(

let _87_1322 = (FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern")
in [])
end))
in (

let one_pat = (fun p -> (

let _87_1328 = (let _181_798 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right _181_798 FStar_Syntax_Util.head_and_args))
in (match (_87_1328) with
| (head, args) -> begin
(match ((let _181_800 = (let _181_799 = (FStar_Syntax_Util.un_uinst head)
in _181_799.FStar_Syntax_Syntax.n)
in ((_181_800), (args)))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((_87_1336, _87_1338))::((e, _87_1333))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpat_lid) -> begin
((e), (None))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, _87_1346))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatT_lid) -> begin
((e), (None))
end
| _87_1351 -> begin
(FStar_All.failwith "Unexpected pattern term")
end)
end)))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements p)
in (

let smt_pat_or = (fun t -> (

let _87_1359 = (let _181_805 = (FStar_Syntax_Util.unmeta t)
in (FStar_All.pipe_right _181_805 FStar_Syntax_Util.head_and_args))
in (match (_87_1359) with
| (head, args) -> begin
(match ((let _181_807 = (let _181_806 = (FStar_Syntax_Util.un_uinst head)
in _181_806.FStar_Syntax_Syntax.n)
in ((_181_807), (args)))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, _87_1364))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatOr_lid) -> begin
Some (e)
end
| _87_1369 -> begin
None
end)
end)))
in (match (elts) with
| (t)::[] -> begin
(match ((smt_pat_or t)) with
| Some (e) -> begin
(let _181_810 = (list_elements e)
in (FStar_All.pipe_right _181_810 (FStar_List.map (fun branch -> (let _181_809 = (list_elements branch)
in (FStar_All.pipe_right _181_809 (FStar_List.map one_pat)))))))
end
| _87_1376 -> begin
(let _181_811 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_181_811)::[])
end)
end
| _87_1378 -> begin
(let _181_812 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_181_812)::[])
end))))
in (

let _87_1421 = (match ((let _181_813 = (FStar_Syntax_Subst.compress t)
in _181_813.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _87_1385 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_87_1385) with
| (binders, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = _87_1406; FStar_Syntax_Syntax.effect_name = _87_1404; FStar_Syntax_Syntax.result_typ = _87_1402; FStar_Syntax_Syntax.effect_args = ((pre, _87_1398))::((post, _87_1394))::((pats, _87_1390))::[]; FStar_Syntax_Syntax.flags = _87_1387}) -> begin
(

let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _181_814 = (lemma_pats pats')
in ((binders), (pre), (post), (_181_814))))
end
| _87_1414 -> begin
(FStar_All.failwith "impos")
end)
end))
end
| _87_1416 -> begin
(FStar_All.failwith "Impos")
end)
in (match (_87_1421) with
| (binders, pre, post, patterns) -> begin
(

let _87_1428 = (encode_binders None binders env)
in (match (_87_1428) with
| (vars, guards, env, decls, _87_1427) -> begin
(

let _87_1441 = (let _181_818 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (

let _87_1438 = (let _181_817 = (FStar_All.pipe_right branch (FStar_List.map (fun _87_1433 -> (match (_87_1433) with
| (t, _87_1432) -> begin
(encode_term t (

let _87_1434 = env
in {bindings = _87_1434.bindings; depth = _87_1434.depth; tcenv = _87_1434.tcenv; warn = _87_1434.warn; cache = _87_1434.cache; nolabels = _87_1434.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _87_1434.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _181_817 FStar_List.unzip))
in (match (_87_1438) with
| (pats, decls) -> begin
((pats), (decls))
end)))))
in (FStar_All.pipe_right _181_818 FStar_List.unzip))
in (match (_87_1441) with
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
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _181_821 = (let _181_820 = (FStar_SMTEncoding_Term.mkFreeV l)
in (FStar_SMTEncoding_Term.mk_Precedes _181_820 e))
in (_181_821)::p))))
end
| _87_1451 -> begin
(

let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _181_827 = (FStar_SMTEncoding_Term.mk_Precedes tl e)
in (_181_827)::p))))
end
| ((x, FStar_SMTEncoding_Term.Term_sort))::vars -> begin
(let _181_829 = (let _181_828 = (FStar_SMTEncoding_Term.mkFreeV ((x), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_LexCons _181_828 tl))
in (aux _181_829 vars))
end
| _87_1463 -> begin
pats
end))
in (let _181_830 = (FStar_SMTEncoding_Term.mkFreeV (("Prims.LexTop"), (FStar_SMTEncoding_Term.Term_sort)))
in (aux _181_830 vars)))
end)
end)
in (

let env = (

let _87_1465 = env
in {bindings = _87_1465.bindings; depth = _87_1465.depth; tcenv = _87_1465.tcenv; warn = _87_1465.warn; cache = _87_1465.cache; nolabels = true; use_zfuel_name = _87_1465.use_zfuel_name; encode_non_total_function_typ = _87_1465.encode_non_total_function_typ})
in (

let _87_1470 = (let _181_831 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula _181_831 env))
in (match (_87_1470) with
| (pre, decls'') -> begin
(

let _87_1473 = (let _181_832 = (FStar_Syntax_Util.unmeta post)
in (encode_formula _181_832 env))
in (match (_87_1473) with
| (post, decls''') -> begin
(

let decls = (FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') (FStar_List.append decls'' decls''')))
in (let _181_837 = (let _181_836 = (let _181_835 = (let _181_834 = (let _181_833 = (FStar_SMTEncoding_Term.mk_and_l ((pre)::guards))
in ((_181_833), (post)))
in (FStar_SMTEncoding_Term.mkImp _181_834))
in ((pats), (vars), (_181_835)))
in (FStar_SMTEncoding_Term.mkForall _181_836))
in ((_181_837), (decls))))
end))
end)))))
end))
end))
end))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (

let debug = (fun phi -> if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _181_843 = (FStar_Syntax_Print.tag_of_term phi)
in (let _181_842 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print2 "Formula (%s)  %s\n" _181_843 _181_842)))
end else begin
()
end)
in (

let enc = (fun f l -> (

let _87_1489 = (FStar_Util.fold_map (fun decls x -> (

let _87_1486 = (encode_term (Prims.fst x) env)
in (match (_87_1486) with
| (t, decls') -> begin
(((FStar_List.append decls decls')), (t))
end))) [] l)
in (match (_87_1489) with
| (decls, args) -> begin
(let _181_859 = (f args)
in ((_181_859), (decls)))
end)))
in (

let const_op = (fun f _87_1492 -> ((f), ([])))
in (

let un_op = (fun f l -> (let _181_873 = (FStar_List.hd l)
in (FStar_All.pipe_left f _181_873)))
in (

let bin_op = (fun f _87_10 -> (match (_87_10) with
| (t1)::(t2)::[] -> begin
(f ((t1), (t2)))
end
| _87_1503 -> begin
(FStar_All.failwith "Impossible")
end))
in (

let enc_prop_c = (fun f l -> (

let _87_1518 = (FStar_Util.fold_map (fun decls _87_1512 -> (match (_87_1512) with
| (t, _87_1511) -> begin
(

let _87_1515 = (encode_formula t env)
in (match (_87_1515) with
| (phi, decls') -> begin
(((FStar_List.append decls decls')), (phi))
end))
end)) [] l)
in (match (_87_1518) with
| (decls, phis) -> begin
(let _181_898 = (f phis)
in ((_181_898), (decls)))
end)))
in (

let eq_op = (fun _87_11 -> (match (_87_11) with
| ((_)::(e1)::(e2)::[]) | ((_)::(_)::(e1)::(e2)::[]) -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) l)
end))
in (

let mk_imp = (fun _87_12 -> (match (_87_12) with
| ((lhs, _87_1539))::((rhs, _87_1535))::[] -> begin
(

let _87_1544 = (encode_formula rhs env)
in (match (_87_1544) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _87_1547) -> begin
((l1), (decls1))
end
| _87_1551 -> begin
(

let _87_1554 = (encode_formula lhs env)
in (match (_87_1554) with
| (l2, decls2) -> begin
(let _181_903 = (FStar_SMTEncoding_Term.mkImp ((l2), (l1)))
in ((_181_903), ((FStar_List.append decls1 decls2))))
end))
end)
end))
end
| _87_1556 -> begin
(FStar_All.failwith "impossible")
end))
in (

let mk_ite = (fun _87_13 -> (match (_87_13) with
| ((guard, _87_1569))::((_then, _87_1565))::((_else, _87_1561))::[] -> begin
(

let _87_1574 = (encode_formula guard env)
in (match (_87_1574) with
| (g, decls1) -> begin
(

let _87_1577 = (encode_formula _then env)
in (match (_87_1577) with
| (t, decls2) -> begin
(

let _87_1580 = (encode_formula _else env)
in (match (_87_1580) with
| (e, decls3) -> begin
(

let res = (FStar_SMTEncoding_Term.mkITE ((g), (t), (e)))
in ((res), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end))
end))
end
| _87_1583 -> begin
(FStar_All.failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (let _181_915 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f _181_915)))
in (

let connectives = (let _181_971 = (let _181_924 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkAnd))
in ((FStar_Syntax_Const.and_lid), (_181_924)))
in (let _181_970 = (let _181_969 = (let _181_930 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkOr))
in ((FStar_Syntax_Const.or_lid), (_181_930)))
in (let _181_968 = (let _181_967 = (let _181_966 = (let _181_939 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkIff))
in ((FStar_Syntax_Const.iff_lid), (_181_939)))
in (let _181_965 = (let _181_964 = (let _181_963 = (let _181_948 = (FStar_All.pipe_left enc_prop_c (un_op FStar_SMTEncoding_Term.mkNot))
in ((FStar_Syntax_Const.not_lid), (_181_948)))
in (_181_963)::(((FStar_Syntax_Const.eq2_lid), (eq_op)))::(((FStar_Syntax_Const.eq3_lid), (eq_op)))::(((FStar_Syntax_Const.true_lid), ((const_op FStar_SMTEncoding_Term.mkTrue))))::(((FStar_Syntax_Const.false_lid), ((const_op FStar_SMTEncoding_Term.mkFalse))))::[])
in (((FStar_Syntax_Const.ite_lid), (mk_ite)))::_181_964)
in (_181_966)::_181_965))
in (((FStar_Syntax_Const.imp_lid), (mk_imp)))::_181_967)
in (_181_969)::_181_968))
in (_181_971)::_181_970))
in (

let rec fallback = (fun phi -> (match (phi.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(

let _87_1601 = (encode_formula phi' env)
in (match (_87_1601) with
| (phi, decls) -> begin
(let _181_974 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled (((phi), (msg), (r)))))
in ((_181_974), (decls)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (_87_1603) -> begin
(let _181_975 = (FStar_Syntax_Util.unmeta phi)
in (encode_formula _181_975 env))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(

let _87_1611 = (encode_match e pats FStar_SMTEncoding_Term.mkFalse env encode_formula)
in (match (_87_1611) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _87_1618; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _87_1615; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _87_1629 = (encode_let x t1 e1 e2 env encode_formula)
in (match (_87_1629) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let head = (FStar_Syntax_Util.un_uinst head)
in (match (((head.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_87_1646)::((x, _87_1643))::((t, _87_1639))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.has_type_lid) -> begin
(

let _87_1651 = (encode_term x env)
in (match (_87_1651) with
| (x, decls) -> begin
(

let _87_1654 = (encode_term t env)
in (match (_87_1654) with
| (t, decls') -> begin
(let _181_976 = (FStar_SMTEncoding_Term.mk_HasType x t)
in ((_181_976), ((FStar_List.append decls decls'))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((r, _87_1667))::((msg, _87_1663))::((phi, _87_1659))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.labeled_lid) -> begin
(match ((let _181_980 = (let _181_977 = (FStar_Syntax_Subst.compress r)
in _181_977.FStar_Syntax_Syntax.n)
in (let _181_979 = (let _181_978 = (FStar_Syntax_Subst.compress msg)
in _181_978.FStar_Syntax_Syntax.n)
in ((_181_980), (_181_979))))) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, _87_1676))) -> begin
(

let phi = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((phi), (FStar_Syntax_Syntax.Meta_labeled ((((FStar_Util.string_of_unicode s)), (r), (false))))))) None r)
in (fallback phi))
end
| _87_1683 -> begin
(fallback phi)
end)
end
| _87_1685 when (head_redex env head) -> begin
(let _181_981 = (whnf env phi)
in (encode_formula _181_981 env))
end
| _87_1687 -> begin
(

let _87_1690 = (encode_term phi env)
in (match (_87_1690) with
| (tt, decls) -> begin
(let _181_982 = (FStar_SMTEncoding_Term.mk_Valid tt)
in ((_181_982), (decls)))
end))
end))
end
| _87_1692 -> begin
(

let _87_1695 = (encode_term phi env)
in (match (_87_1695) with
| (tt, decls) -> begin
(let _181_983 = (FStar_SMTEncoding_Term.mk_Valid tt)
in ((_181_983), (decls)))
end))
end))
in (

let encode_q_body = (fun env bs ps body -> (

let _87_1707 = (encode_binders None bs env)
in (match (_87_1707) with
| (vars, guards, env, decls, _87_1706) -> begin
(

let _87_1720 = (let _181_995 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let _87_1717 = (let _181_994 = (FStar_All.pipe_right p (FStar_List.map (fun _87_1712 -> (match (_87_1712) with
| (t, _87_1711) -> begin
(encode_term t (

let _87_1713 = env
in {bindings = _87_1713.bindings; depth = _87_1713.depth; tcenv = _87_1713.tcenv; warn = _87_1713.warn; cache = _87_1713.cache; nolabels = _87_1713.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _87_1713.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _181_994 FStar_List.unzip))
in (match (_87_1717) with
| (p, decls) -> begin
((p), ((FStar_List.flatten decls)))
end)))))
in (FStar_All.pipe_right _181_995 FStar_List.unzip))
in (match (_87_1720) with
| (pats, decls') -> begin
(

let _87_1723 = (encode_formula body env)
in (match (_87_1723) with
| (body, decls'') -> begin
(

let guards = (match (pats) with
| (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (gf), (p)::[]); FStar_SMTEncoding_Term.hash = _87_1727; FStar_SMTEncoding_Term.freevars = _87_1725})::[])::[] when ((FStar_Ident.text_of_lid FStar_Syntax_Const.guard_free) = gf) -> begin
[]
end
| _87_1738 -> begin
guards
end)
in (let _181_996 = (FStar_SMTEncoding_Term.mk_and_l guards)
in ((vars), (pats), (_181_996), (body), ((FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') decls''))))))
end))
end))
end)))
in (

let _87_1740 = (debug phi)
in (

let phi = (FStar_Syntax_Util.unascribe phi)
in (

let check_pattern_vars = (fun vars pats -> (

let pats = (FStar_All.pipe_right pats (FStar_List.map (fun _87_1749 -> (match (_87_1749) with
| (x, _87_1748) -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x)
end))))
in (match (pats) with
| [] -> begin
()
end
| (hd)::tl -> begin
(

let pat_vars = (let _181_1005 = (FStar_Syntax_Free.names hd)
in (FStar_List.fold_left (fun out x -> (let _181_1004 = (FStar_Syntax_Free.names x)
in (FStar_Util.set_union out _181_1004))) _181_1005 tl))
in (match ((FStar_All.pipe_right vars (FStar_Util.find_opt (fun _87_1761 -> (match (_87_1761) with
| (b, _87_1760) -> begin
(not ((FStar_Util.set_mem b pat_vars)))
end))))) with
| None -> begin
()
end
| Some (x, _87_1765) -> begin
(

let pos = (FStar_List.fold_left (fun out t -> (FStar_Range.union_ranges out t.FStar_Syntax_Syntax.pos)) hd.FStar_Syntax_Syntax.pos tl)
in (let _181_1010 = (let _181_1009 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variable: %s" _181_1009))
in (FStar_TypeChecker_Errors.warn pos _181_1010)))
end))
end)))
in (match ((FStar_Syntax_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _87_1780 -> (match (_87_1780) with
| (l, _87_1779) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_87_1783, f) -> begin
(f arms)
end)
end
| Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
(

let _87_1793 = (FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)))
in (

let _87_1800 = (encode_q_body env vars pats body)
in (match (_87_1800) with
| (vars, pats, guard, body, decls) -> begin
(

let tm = (let _181_1028 = (let _181_1027 = (FStar_SMTEncoding_Term.mkImp ((guard), (body)))
in ((pats), (vars), (_181_1027)))
in (FStar_SMTEncoding_Term.mkForall _181_1028))
in ((tm), (decls)))
end)))
end
| Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
(

let _87_1808 = (FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)))
in (

let _87_1815 = (encode_q_body env vars pats body)
in (match (_87_1815) with
| (vars, pats, guard, body, decls) -> begin
(let _181_1031 = (let _181_1030 = (let _181_1029 = (FStar_SMTEncoding_Term.mkAnd ((guard), (body)))
in ((pats), (vars), (_181_1029)))
in (FStar_SMTEncoding_Term.mkExists _181_1030))
in ((_181_1031), (decls)))
end)))
end))))))))))))))))))


type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list); is : FStar_Ident.lident  ->  Prims.bool}


let is_Mkprims_t : prims_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkprims_t"))))


let prims : prims_t = (

let _87_1821 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (_87_1821) with
| (asym, a) -> begin
(

let _87_1824 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_87_1824) with
| (xsym, x) -> begin
(

let _87_1827 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (_87_1827) with
| (ysym, y) -> begin
(

let deffun = (fun vars body x -> (FStar_SMTEncoding_Term.DefineFun (((x), (vars), (FStar_SMTEncoding_Term.Term_sort), (body), (None))))::[])
in (

let quant = (fun vars body x -> (

let xname_decl = (let _181_1074 = (let _181_1073 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in ((x), (_181_1073), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (_181_1074))
in (

let xtok = (Prims.strcat x "@tok")
in (

let xtok_decl = FStar_SMTEncoding_Term.DeclFun (((xtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let xapp = (let _181_1076 = (let _181_1075 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in ((x), (_181_1075)))
in (FStar_SMTEncoding_Term.mkApp _181_1076))
in (

let xtok = (FStar_SMTEncoding_Term.mkApp ((xtok), ([])))
in (

let xtok_app = (mk_Apply xtok vars)
in (let _181_1090 = (let _181_1089 = (let _181_1088 = (let _181_1087 = (let _181_1080 = (let _181_1079 = (let _181_1078 = (let _181_1077 = (FStar_SMTEncoding_Term.mkEq ((xapp), (body)))
in ((((xapp)::[])::[]), (vars), (_181_1077)))
in (FStar_SMTEncoding_Term.mkForall _181_1078))
in ((_181_1079), (None), (Some ((Prims.strcat "primitive_" x)))))
in FStar_SMTEncoding_Term.Assume (_181_1080))
in (let _181_1086 = (let _181_1085 = (let _181_1084 = (let _181_1083 = (let _181_1082 = (let _181_1081 = (FStar_SMTEncoding_Term.mkEq ((xtok_app), (xapp)))
in ((((xtok_app)::[])::[]), (vars), (_181_1081)))
in (FStar_SMTEncoding_Term.mkForall _181_1082))
in ((_181_1083), (Some ("Name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" x)))))
in FStar_SMTEncoding_Term.Assume (_181_1084))
in (_181_1085)::[])
in (_181_1087)::_181_1086))
in (xtok_decl)::_181_1088)
in (xname_decl)::_181_1089)
in ((xtok), (_181_1090))))))))))
in (

let axy = (((asym), (FStar_SMTEncoding_Term.Term_sort)))::(((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let xy = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let qx = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let prims = (let _181_1250 = (let _181_1099 = (let _181_1098 = (let _181_1097 = (FStar_SMTEncoding_Term.mkEq ((x), (y)))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _181_1097))
in (quant axy _181_1098))
in ((FStar_Syntax_Const.op_Eq), (_181_1099)))
in (let _181_1249 = (let _181_1248 = (let _181_1106 = (let _181_1105 = (let _181_1104 = (let _181_1103 = (FStar_SMTEncoding_Term.mkEq ((x), (y)))
in (FStar_SMTEncoding_Term.mkNot _181_1103))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _181_1104))
in (quant axy _181_1105))
in ((FStar_Syntax_Const.op_notEq), (_181_1106)))
in (let _181_1247 = (let _181_1246 = (let _181_1115 = (let _181_1114 = (let _181_1113 = (let _181_1112 = (let _181_1111 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _181_1110 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_181_1111), (_181_1110))))
in (FStar_SMTEncoding_Term.mkLT _181_1112))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _181_1113))
in (quant xy _181_1114))
in ((FStar_Syntax_Const.op_LT), (_181_1115)))
in (let _181_1245 = (let _181_1244 = (let _181_1124 = (let _181_1123 = (let _181_1122 = (let _181_1121 = (let _181_1120 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _181_1119 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_181_1120), (_181_1119))))
in (FStar_SMTEncoding_Term.mkLTE _181_1121))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _181_1122))
in (quant xy _181_1123))
in ((FStar_Syntax_Const.op_LTE), (_181_1124)))
in (let _181_1243 = (let _181_1242 = (let _181_1133 = (let _181_1132 = (let _181_1131 = (let _181_1130 = (let _181_1129 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _181_1128 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_181_1129), (_181_1128))))
in (FStar_SMTEncoding_Term.mkGT _181_1130))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _181_1131))
in (quant xy _181_1132))
in ((FStar_Syntax_Const.op_GT), (_181_1133)))
in (let _181_1241 = (let _181_1240 = (let _181_1142 = (let _181_1141 = (let _181_1140 = (let _181_1139 = (let _181_1138 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _181_1137 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_181_1138), (_181_1137))))
in (FStar_SMTEncoding_Term.mkGTE _181_1139))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _181_1140))
in (quant xy _181_1141))
in ((FStar_Syntax_Const.op_GTE), (_181_1142)))
in (let _181_1239 = (let _181_1238 = (let _181_1151 = (let _181_1150 = (let _181_1149 = (let _181_1148 = (let _181_1147 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _181_1146 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_181_1147), (_181_1146))))
in (FStar_SMTEncoding_Term.mkSub _181_1148))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _181_1149))
in (quant xy _181_1150))
in ((FStar_Syntax_Const.op_Subtraction), (_181_1151)))
in (let _181_1237 = (let _181_1236 = (let _181_1158 = (let _181_1157 = (let _181_1156 = (let _181_1155 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Term.mkMinus _181_1155))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _181_1156))
in (quant qx _181_1157))
in ((FStar_Syntax_Const.op_Minus), (_181_1158)))
in (let _181_1235 = (let _181_1234 = (let _181_1167 = (let _181_1166 = (let _181_1165 = (let _181_1164 = (let _181_1163 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _181_1162 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_181_1163), (_181_1162))))
in (FStar_SMTEncoding_Term.mkAdd _181_1164))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _181_1165))
in (quant xy _181_1166))
in ((FStar_Syntax_Const.op_Addition), (_181_1167)))
in (let _181_1233 = (let _181_1232 = (let _181_1176 = (let _181_1175 = (let _181_1174 = (let _181_1173 = (let _181_1172 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _181_1171 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_181_1172), (_181_1171))))
in (FStar_SMTEncoding_Term.mkMul _181_1173))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _181_1174))
in (quant xy _181_1175))
in ((FStar_Syntax_Const.op_Multiply), (_181_1176)))
in (let _181_1231 = (let _181_1230 = (let _181_1185 = (let _181_1184 = (let _181_1183 = (let _181_1182 = (let _181_1181 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _181_1180 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_181_1181), (_181_1180))))
in (FStar_SMTEncoding_Term.mkDiv _181_1182))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _181_1183))
in (quant xy _181_1184))
in ((FStar_Syntax_Const.op_Division), (_181_1185)))
in (let _181_1229 = (let _181_1228 = (let _181_1194 = (let _181_1193 = (let _181_1192 = (let _181_1191 = (let _181_1190 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _181_1189 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_181_1190), (_181_1189))))
in (FStar_SMTEncoding_Term.mkMod _181_1191))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _181_1192))
in (quant xy _181_1193))
in ((FStar_Syntax_Const.op_Modulus), (_181_1194)))
in (let _181_1227 = (let _181_1226 = (let _181_1203 = (let _181_1202 = (let _181_1201 = (let _181_1200 = (let _181_1199 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _181_1198 = (FStar_SMTEncoding_Term.unboxBool y)
in ((_181_1199), (_181_1198))))
in (FStar_SMTEncoding_Term.mkAnd _181_1200))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _181_1201))
in (quant xy _181_1202))
in ((FStar_Syntax_Const.op_And), (_181_1203)))
in (let _181_1225 = (let _181_1224 = (let _181_1212 = (let _181_1211 = (let _181_1210 = (let _181_1209 = (let _181_1208 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _181_1207 = (FStar_SMTEncoding_Term.unboxBool y)
in ((_181_1208), (_181_1207))))
in (FStar_SMTEncoding_Term.mkOr _181_1209))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _181_1210))
in (quant xy _181_1211))
in ((FStar_Syntax_Const.op_Or), (_181_1212)))
in (let _181_1223 = (let _181_1222 = (let _181_1219 = (let _181_1218 = (let _181_1217 = (let _181_1216 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Term.mkNot _181_1216))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _181_1217))
in (quant qx _181_1218))
in ((FStar_Syntax_Const.op_Negation), (_181_1219)))
in (_181_1222)::[])
in (_181_1224)::_181_1223))
in (_181_1226)::_181_1225))
in (_181_1228)::_181_1227))
in (_181_1230)::_181_1229))
in (_181_1232)::_181_1231))
in (_181_1234)::_181_1233))
in (_181_1236)::_181_1235))
in (_181_1238)::_181_1237))
in (_181_1240)::_181_1239))
in (_181_1242)::_181_1241))
in (_181_1244)::_181_1243))
in (_181_1246)::_181_1245))
in (_181_1248)::_181_1247))
in (_181_1250)::_181_1249))
in (

let mk = (fun l v -> (let _181_1297 = (let _181_1296 = (FStar_All.pipe_right prims (FStar_List.find (fun _87_1851 -> (match (_87_1851) with
| (l', _87_1850) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right _181_1296 (FStar_Option.map (fun _87_1855 -> (match (_87_1855) with
| (_87_1853, b) -> begin
(b v)
end)))))
in (FStar_All.pipe_right _181_1297 FStar_Option.get)))
in (

let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _87_1861 -> (match (_87_1861) with
| (l', _87_1860) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is}))))))))
end))
end))
end))


let pretype_axiom : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun tapp vars -> (

let _87_1867 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_87_1867) with
| (xxsym, xx) -> begin
(

let _87_1870 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_87_1870) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (let _181_1327 = (let _181_1326 = (let _181_1321 = (let _181_1320 = (let _181_1319 = (let _181_1318 = (let _181_1317 = (let _181_1316 = (FStar_SMTEncoding_Term.mkApp (("PreType"), ((xx)::[])))
in ((tapp), (_181_1316)))
in (FStar_SMTEncoding_Term.mkEq _181_1317))
in ((xx_has_type), (_181_1318)))
in (FStar_SMTEncoding_Term.mkImp _181_1319))
in ((((xx_has_type)::[])::[]), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars), (_181_1320)))
in (FStar_SMTEncoding_Term.mkForall _181_1321))
in (let _181_1325 = (let _181_1324 = (let _181_1323 = (let _181_1322 = (FStar_Util.digest_of_string tapp.FStar_SMTEncoding_Term.hash)
in (Prims.strcat "pretyping_" _181_1322))
in (varops.mk_unique _181_1323))
in Some (_181_1324))
in ((_181_1326), (Some ("pretyping")), (_181_1325))))
in FStar_SMTEncoding_Term.Assume (_181_1327)))
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
in (let _181_1348 = (let _181_1339 = (let _181_1338 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in ((_181_1338), (Some ("unit typing")), (Some ("unit_typing"))))
in FStar_SMTEncoding_Term.Assume (_181_1339))
in (let _181_1347 = (let _181_1346 = (let _181_1345 = (let _181_1344 = (let _181_1343 = (let _181_1342 = (let _181_1341 = (let _181_1340 = (FStar_SMTEncoding_Term.mkEq ((x), (FStar_SMTEncoding_Term.mk_Term_unit)))
in ((typing_pred), (_181_1340)))
in (FStar_SMTEncoding_Term.mkImp _181_1341))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_181_1342)))
in (mkForall_fuel _181_1343))
in ((_181_1344), (Some ("unit inversion")), (Some ("unit_inversion"))))
in FStar_SMTEncoding_Term.Assume (_181_1345))
in (_181_1346)::[])
in (_181_1348)::_181_1347))))
in (

let mk_bool = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Bool_sort))
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _181_1371 = (let _181_1362 = (let _181_1361 = (let _181_1360 = (let _181_1359 = (let _181_1356 = (let _181_1355 = (FStar_SMTEncoding_Term.boxBool b)
in (_181_1355)::[])
in (_181_1356)::[])
in (let _181_1358 = (let _181_1357 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType _181_1357 tt))
in ((_181_1359), ((bb)::[]), (_181_1358))))
in (FStar_SMTEncoding_Term.mkForall _181_1360))
in ((_181_1361), (Some ("bool typing")), (Some ("bool_typing"))))
in FStar_SMTEncoding_Term.Assume (_181_1362))
in (let _181_1370 = (let _181_1369 = (let _181_1368 = (let _181_1367 = (let _181_1366 = (let _181_1365 = (let _181_1364 = (let _181_1363 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in ((typing_pred), (_181_1363)))
in (FStar_SMTEncoding_Term.mkImp _181_1364))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_181_1365)))
in (mkForall_fuel _181_1366))
in ((_181_1367), (Some ("bool inversion")), (Some ("bool_inversion"))))
in FStar_SMTEncoding_Term.Assume (_181_1368))
in (_181_1369)::[])
in (_181_1371)::_181_1370))))))
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

let precedes = (let _181_1385 = (let _181_1384 = (let _181_1383 = (let _181_1382 = (let _181_1381 = (let _181_1380 = (FStar_SMTEncoding_Term.boxInt a)
in (let _181_1379 = (let _181_1378 = (FStar_SMTEncoding_Term.boxInt b)
in (_181_1378)::[])
in (_181_1380)::_181_1379))
in (tt)::_181_1381)
in (tt)::_181_1382)
in (("Prims.Precedes"), (_181_1383)))
in (FStar_SMTEncoding_Term.mkApp _181_1384))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _181_1385))
in (

let precedes_y_x = (let _181_1386 = (FStar_SMTEncoding_Term.mkApp (("Precedes"), ((y)::(x)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _181_1386))
in (let _181_1428 = (let _181_1394 = (let _181_1393 = (let _181_1392 = (let _181_1391 = (let _181_1388 = (let _181_1387 = (FStar_SMTEncoding_Term.boxInt b)
in (_181_1387)::[])
in (_181_1388)::[])
in (let _181_1390 = (let _181_1389 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType _181_1389 tt))
in ((_181_1391), ((bb)::[]), (_181_1390))))
in (FStar_SMTEncoding_Term.mkForall _181_1392))
in ((_181_1393), (Some ("int typing")), (Some ("int_typing"))))
in FStar_SMTEncoding_Term.Assume (_181_1394))
in (let _181_1427 = (let _181_1426 = (let _181_1400 = (let _181_1399 = (let _181_1398 = (let _181_1397 = (let _181_1396 = (let _181_1395 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in ((typing_pred), (_181_1395)))
in (FStar_SMTEncoding_Term.mkImp _181_1396))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_181_1397)))
in (mkForall_fuel _181_1398))
in ((_181_1399), (Some ("int inversion")), (Some ("int_inversion"))))
in FStar_SMTEncoding_Term.Assume (_181_1400))
in (let _181_1425 = (let _181_1424 = (let _181_1423 = (let _181_1422 = (let _181_1421 = (let _181_1420 = (let _181_1419 = (let _181_1418 = (let _181_1417 = (let _181_1416 = (let _181_1415 = (let _181_1414 = (let _181_1403 = (let _181_1402 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _181_1401 = (FStar_SMTEncoding_Term.mkInteger' (Prims.parse_int "0"))
in ((_181_1402), (_181_1401))))
in (FStar_SMTEncoding_Term.mkGT _181_1403))
in (let _181_1413 = (let _181_1412 = (let _181_1406 = (let _181_1405 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _181_1404 = (FStar_SMTEncoding_Term.mkInteger' (Prims.parse_int "0"))
in ((_181_1405), (_181_1404))))
in (FStar_SMTEncoding_Term.mkGTE _181_1406))
in (let _181_1411 = (let _181_1410 = (let _181_1409 = (let _181_1408 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _181_1407 = (FStar_SMTEncoding_Term.unboxInt x)
in ((_181_1408), (_181_1407))))
in (FStar_SMTEncoding_Term.mkLT _181_1409))
in (_181_1410)::[])
in (_181_1412)::_181_1411))
in (_181_1414)::_181_1413))
in (typing_pred_y)::_181_1415)
in (typing_pred)::_181_1416)
in (FStar_SMTEncoding_Term.mk_and_l _181_1417))
in ((_181_1418), (precedes_y_x)))
in (FStar_SMTEncoding_Term.mkImp _181_1419))
in ((((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[]), ((xx)::(yy)::[]), (_181_1420)))
in (mkForall_fuel _181_1421))
in ((_181_1422), (Some ("well-founded ordering on nat (alt)")), (Some ("well-founded-ordering-on-nat"))))
in FStar_SMTEncoding_Term.Assume (_181_1423))
in (_181_1424)::[])
in (_181_1426)::_181_1425))
in (_181_1428)::_181_1427)))))))))))
in (

let mk_str = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.String_sort))
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _181_1451 = (let _181_1442 = (let _181_1441 = (let _181_1440 = (let _181_1439 = (let _181_1436 = (let _181_1435 = (FStar_SMTEncoding_Term.boxString b)
in (_181_1435)::[])
in (_181_1436)::[])
in (let _181_1438 = (let _181_1437 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType _181_1437 tt))
in ((_181_1439), ((bb)::[]), (_181_1438))))
in (FStar_SMTEncoding_Term.mkForall _181_1440))
in ((_181_1441), (Some ("string typing")), (Some ("string_typing"))))
in FStar_SMTEncoding_Term.Assume (_181_1442))
in (let _181_1450 = (let _181_1449 = (let _181_1448 = (let _181_1447 = (let _181_1446 = (let _181_1445 = (let _181_1444 = (let _181_1443 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in ((typing_pred), (_181_1443)))
in (FStar_SMTEncoding_Term.mkImp _181_1444))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_181_1445)))
in (mkForall_fuel _181_1446))
in ((_181_1447), (Some ("string inversion")), (Some ("string_inversion"))))
in FStar_SMTEncoding_Term.Assume (_181_1448))
in (_181_1449)::[])
in (_181_1451)::_181_1450))))))
in (

let mk_ref = (fun env reft_name _87_1909 -> (

let r = (("r"), (FStar_SMTEncoding_Term.Ref_sort))
in (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let refa = (let _181_1460 = (let _181_1459 = (let _181_1458 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (_181_1458)::[])
in ((reft_name), (_181_1459)))
in (FStar_SMTEncoding_Term.mkApp _181_1460))
in (

let refb = (let _181_1463 = (let _181_1462 = (let _181_1461 = (FStar_SMTEncoding_Term.mkFreeV bb)
in (_181_1461)::[])
in ((reft_name), (_181_1462)))
in (FStar_SMTEncoding_Term.mkApp _181_1463))
in (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (

let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (let _181_1482 = (let _181_1469 = (let _181_1468 = (let _181_1467 = (let _181_1466 = (let _181_1465 = (let _181_1464 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in ((typing_pred), (_181_1464)))
in (FStar_SMTEncoding_Term.mkImp _181_1465))
in ((((typing_pred)::[])::[]), ((xx)::(aa)::[]), (_181_1466)))
in (mkForall_fuel _181_1467))
in ((_181_1468), (Some ("ref inversion")), (Some ("ref_inversion"))))
in FStar_SMTEncoding_Term.Assume (_181_1469))
in (let _181_1481 = (let _181_1480 = (let _181_1479 = (let _181_1478 = (let _181_1477 = (let _181_1476 = (let _181_1475 = (let _181_1474 = (FStar_SMTEncoding_Term.mkAnd ((typing_pred), (typing_pred_b)))
in (let _181_1473 = (let _181_1472 = (let _181_1471 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (let _181_1470 = (FStar_SMTEncoding_Term.mkFreeV bb)
in ((_181_1471), (_181_1470))))
in (FStar_SMTEncoding_Term.mkEq _181_1472))
in ((_181_1474), (_181_1473))))
in (FStar_SMTEncoding_Term.mkImp _181_1475))
in ((((typing_pred)::(typing_pred_b)::[])::[]), ((xx)::(aa)::(bb)::[]), (_181_1476)))
in (mkForall_fuel' (Prims.parse_int "2") _181_1477))
in ((_181_1478), (Some ("ref typing is injective")), (Some ("ref_injectivity"))))
in FStar_SMTEncoding_Term.Assume (_181_1479))
in (_181_1480)::[])
in (_181_1482)::_181_1481))))))))))
in (

let mk_true_interp = (fun env nm true_tm -> (

let valid = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((true_tm)::[])))
in (FStar_SMTEncoding_Term.Assume (((valid), (Some ("True interpretation")), (Some ("true_interp")))))::[]))
in (

let mk_false_interp = (fun env nm false_tm -> (

let valid = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((false_tm)::[])))
in (let _181_1497 = (let _181_1496 = (let _181_1495 = (FStar_SMTEncoding_Term.mkIff ((FStar_SMTEncoding_Term.mkFalse), (valid)))
in ((_181_1495), (Some ("False interpretation")), (Some ("false_interp"))))
in FStar_SMTEncoding_Term.Assume (_181_1496))
in (_181_1497)::[])))
in (

let mk_and_interp = (fun env conj _87_1931 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (

let valid = (let _181_1506 = (let _181_1505 = (let _181_1504 = (FStar_SMTEncoding_Term.mkApp ((conj), ((a)::(b)::[])))
in (_181_1504)::[])
in (("Valid"), (_181_1505)))
in (FStar_SMTEncoding_Term.mkApp _181_1506))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((b)::[])))
in (let _181_1513 = (let _181_1512 = (let _181_1511 = (let _181_1510 = (let _181_1509 = (let _181_1508 = (let _181_1507 = (FStar_SMTEncoding_Term.mkAnd ((valid_a), (valid_b)))
in ((_181_1507), (valid)))
in (FStar_SMTEncoding_Term.mkIff _181_1508))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_181_1509)))
in (FStar_SMTEncoding_Term.mkForall _181_1510))
in ((_181_1511), (Some ("/\\ interpretation")), (Some ("l_and-interp"))))
in FStar_SMTEncoding_Term.Assume (_181_1512))
in (_181_1513)::[])))))))))
in (

let mk_or_interp = (fun env disj _87_1943 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (

let valid = (let _181_1522 = (let _181_1521 = (let _181_1520 = (FStar_SMTEncoding_Term.mkApp ((disj), ((a)::(b)::[])))
in (_181_1520)::[])
in (("Valid"), (_181_1521)))
in (FStar_SMTEncoding_Term.mkApp _181_1522))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((b)::[])))
in (let _181_1529 = (let _181_1528 = (let _181_1527 = (let _181_1526 = (let _181_1525 = (let _181_1524 = (let _181_1523 = (FStar_SMTEncoding_Term.mkOr ((valid_a), (valid_b)))
in ((_181_1523), (valid)))
in (FStar_SMTEncoding_Term.mkIff _181_1524))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_181_1525)))
in (FStar_SMTEncoding_Term.mkForall _181_1526))
in ((_181_1527), (Some ("\\/ interpretation")), (Some ("l_or-interp"))))
in FStar_SMTEncoding_Term.Assume (_181_1528))
in (_181_1529)::[])))))))))
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

let valid = (let _181_1538 = (let _181_1537 = (let _181_1536 = (FStar_SMTEncoding_Term.mkApp ((eq2), ((a)::(x)::(y)::[])))
in (_181_1536)::[])
in (("Valid"), (_181_1537)))
in (FStar_SMTEncoding_Term.mkApp _181_1538))
in (let _181_1545 = (let _181_1544 = (let _181_1543 = (let _181_1542 = (let _181_1541 = (let _181_1540 = (let _181_1539 = (FStar_SMTEncoding_Term.mkEq ((x), (y)))
in ((_181_1539), (valid)))
in (FStar_SMTEncoding_Term.mkIff _181_1540))
in ((((valid)::[])::[]), ((aa)::(xx)::(yy)::[]), (_181_1541)))
in (FStar_SMTEncoding_Term.mkForall _181_1542))
in ((_181_1543), (Some ("Eq2 interpretation")), (Some ("eq2-interp"))))
in FStar_SMTEncoding_Term.Assume (_181_1544))
in (_181_1545)::[])))))))))
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

let valid = (let _181_1554 = (let _181_1553 = (let _181_1552 = (FStar_SMTEncoding_Term.mkApp ((eq3), ((a)::(b)::(x)::(y)::[])))
in (_181_1552)::[])
in (("Valid"), (_181_1553)))
in (FStar_SMTEncoding_Term.mkApp _181_1554))
in (let _181_1561 = (let _181_1560 = (let _181_1559 = (let _181_1558 = (let _181_1557 = (let _181_1556 = (let _181_1555 = (FStar_SMTEncoding_Term.mkEq ((x), (y)))
in ((_181_1555), (valid)))
in (FStar_SMTEncoding_Term.mkIff _181_1556))
in ((((valid)::[])::[]), ((aa)::(bb)::(xx)::(yy)::[]), (_181_1557)))
in (FStar_SMTEncoding_Term.mkForall _181_1558))
in ((_181_1559), (Some ("Eq3 interpretation")), (Some ("eq3-interp"))))
in FStar_SMTEncoding_Term.Assume (_181_1560))
in (_181_1561)::[])))))))))))
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

let valid = (let _181_1570 = (let _181_1569 = (let _181_1568 = (FStar_SMTEncoding_Term.mkApp ((imp), ((a)::(b)::[])))
in (_181_1568)::[])
in (("Valid"), (_181_1569)))
in (FStar_SMTEncoding_Term.mkApp _181_1570))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((b)::[])))
in (let _181_1577 = (let _181_1576 = (let _181_1575 = (let _181_1574 = (let _181_1573 = (let _181_1572 = (let _181_1571 = (FStar_SMTEncoding_Term.mkImp ((valid_a), (valid_b)))
in ((_181_1571), (valid)))
in (FStar_SMTEncoding_Term.mkIff _181_1572))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_181_1573)))
in (FStar_SMTEncoding_Term.mkForall _181_1574))
in ((_181_1575), (Some ("==> interpretation")), (Some ("l_imp-interp"))))
in FStar_SMTEncoding_Term.Assume (_181_1576))
in (_181_1577)::[])))))))))
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

let valid = (let _181_1586 = (let _181_1585 = (let _181_1584 = (FStar_SMTEncoding_Term.mkApp ((iff), ((a)::(b)::[])))
in (_181_1584)::[])
in (("Valid"), (_181_1585)))
in (FStar_SMTEncoding_Term.mkApp _181_1586))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((b)::[])))
in (let _181_1593 = (let _181_1592 = (let _181_1591 = (let _181_1590 = (let _181_1589 = (let _181_1588 = (let _181_1587 = (FStar_SMTEncoding_Term.mkIff ((valid_a), (valid_b)))
in ((_181_1587), (valid)))
in (FStar_SMTEncoding_Term.mkIff _181_1588))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_181_1589)))
in (FStar_SMTEncoding_Term.mkForall _181_1590))
in ((_181_1591), (Some ("<==> interpretation")), (Some ("l_iff-interp"))))
in FStar_SMTEncoding_Term.Assume (_181_1592))
in (_181_1593)::[])))))))))
in (

let mk_not_interp = (fun env l_not tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let valid = (let _181_1602 = (let _181_1601 = (let _181_1600 = (FStar_SMTEncoding_Term.mkApp ((l_not), ((a)::[])))
in (_181_1600)::[])
in (("Valid"), (_181_1601)))
in (FStar_SMTEncoding_Term.mkApp _181_1602))
in (

let not_valid_a = (let _181_1603 = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((a)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mkNot _181_1603))
in (let _181_1608 = (let _181_1607 = (let _181_1606 = (let _181_1605 = (let _181_1604 = (FStar_SMTEncoding_Term.mkIff ((not_valid_a), (valid)))
in ((((valid)::[])::[]), ((aa)::[]), (_181_1604)))
in (FStar_SMTEncoding_Term.mkForall _181_1605))
in ((_181_1606), (Some ("not interpretation")), (Some ("l_not-interp"))))
in FStar_SMTEncoding_Term.Assume (_181_1607))
in (_181_1608)::[]))))))
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

let valid = (let _181_1617 = (let _181_1616 = (let _181_1615 = (FStar_SMTEncoding_Term.mkApp ((for_all), ((a)::(b)::[])))
in (_181_1615)::[])
in (("Valid"), (_181_1616)))
in (FStar_SMTEncoding_Term.mkApp _181_1617))
in (

let valid_b_x = (let _181_1620 = (let _181_1619 = (let _181_1618 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_181_1618)::[])
in (("Valid"), (_181_1619)))
in (FStar_SMTEncoding_Term.mkApp _181_1620))
in (let _181_1634 = (let _181_1633 = (let _181_1632 = (let _181_1631 = (let _181_1630 = (let _181_1629 = (let _181_1628 = (let _181_1627 = (let _181_1626 = (let _181_1622 = (let _181_1621 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_181_1621)::[])
in (_181_1622)::[])
in (let _181_1625 = (let _181_1624 = (let _181_1623 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((_181_1623), (valid_b_x)))
in (FStar_SMTEncoding_Term.mkImp _181_1624))
in ((_181_1626), ((xx)::[]), (_181_1625))))
in (FStar_SMTEncoding_Term.mkForall _181_1627))
in ((_181_1628), (valid)))
in (FStar_SMTEncoding_Term.mkIff _181_1629))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_181_1630)))
in (FStar_SMTEncoding_Term.mkForall _181_1631))
in ((_181_1632), (Some ("forall interpretation")), (Some ("forall-interp"))))
in FStar_SMTEncoding_Term.Assume (_181_1633))
in (_181_1634)::[]))))))))))
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

let valid = (let _181_1643 = (let _181_1642 = (let _181_1641 = (FStar_SMTEncoding_Term.mkApp ((for_some), ((a)::(b)::[])))
in (_181_1641)::[])
in (("Valid"), (_181_1642)))
in (FStar_SMTEncoding_Term.mkApp _181_1643))
in (

let valid_b_x = (let _181_1646 = (let _181_1645 = (let _181_1644 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_181_1644)::[])
in (("Valid"), (_181_1645)))
in (FStar_SMTEncoding_Term.mkApp _181_1646))
in (let _181_1660 = (let _181_1659 = (let _181_1658 = (let _181_1657 = (let _181_1656 = (let _181_1655 = (let _181_1654 = (let _181_1653 = (let _181_1652 = (let _181_1648 = (let _181_1647 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_181_1647)::[])
in (_181_1648)::[])
in (let _181_1651 = (let _181_1650 = (let _181_1649 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((_181_1649), (valid_b_x)))
in (FStar_SMTEncoding_Term.mkImp _181_1650))
in ((_181_1652), ((xx)::[]), (_181_1651))))
in (FStar_SMTEncoding_Term.mkExists _181_1653))
in ((_181_1654), (valid)))
in (FStar_SMTEncoding_Term.mkIff _181_1655))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_181_1656)))
in (FStar_SMTEncoding_Term.mkForall _181_1657))
in ((_181_1658), (Some ("exists interpretation")), (Some ("exists-interp"))))
in FStar_SMTEncoding_Term.Assume (_181_1659))
in (_181_1660)::[]))))))))))
in (

let mk_range_interp = (fun env range tt -> (

let range_ty = (FStar_SMTEncoding_Term.mkApp ((range), ([])))
in (let _181_1671 = (let _181_1670 = (let _181_1669 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_ty)
in (let _181_1668 = (let _181_1667 = (varops.mk_unique "typing_range_const")
in Some (_181_1667))
in ((_181_1669), (Some ("Range_const typing")), (_181_1668))))
in FStar_SMTEncoding_Term.Assume (_181_1670))
in (_181_1671)::[])))
in (

let prims = (((FStar_Syntax_Const.unit_lid), (mk_unit)))::(((FStar_Syntax_Const.bool_lid), (mk_bool)))::(((FStar_Syntax_Const.int_lid), (mk_int)))::(((FStar_Syntax_Const.string_lid), (mk_str)))::(((FStar_Syntax_Const.ref_lid), (mk_ref)))::(((FStar_Syntax_Const.true_lid), (mk_true_interp)))::(((FStar_Syntax_Const.false_lid), (mk_false_interp)))::(((FStar_Syntax_Const.and_lid), (mk_and_interp)))::(((FStar_Syntax_Const.or_lid), (mk_or_interp)))::(((FStar_Syntax_Const.eq2_lid), (mk_eq2_interp)))::(((FStar_Syntax_Const.eq3_lid), (mk_eq3_interp)))::(((FStar_Syntax_Const.imp_lid), (mk_imp_interp)))::(((FStar_Syntax_Const.iff_lid), (mk_iff_interp)))::(((FStar_Syntax_Const.not_lid), (mk_not_interp)))::(((FStar_Syntax_Const.forall_lid), (mk_forall_interp)))::(((FStar_Syntax_Const.exists_lid), (mk_exists_interp)))::(((FStar_Syntax_Const.range_lid), (mk_range_interp)))::[]
in (fun env t s tt -> (match ((FStar_Util.find_opt (fun _87_2044 -> (match (_87_2044) with
| (l, _87_2043) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_87_2047, f) -> begin
(f env s tt)
end))))))))))))))))))))))))


let encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let _87_2057 = (encode_function_type_as_formula None None t env)
in (match (_87_2057) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_SMTEncoding_Term.Assume (((form), (Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str))), (Some ((Prims.strcat "lemma_" lid.FStar_Ident.str))))))::[]))
end))))


let encode_free_var : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env fv tt t_norm quals -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if ((let _181_1888 = (FStar_Syntax_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _181_1888)) || (FStar_Syntax_Util.is_lemma t_norm)) then begin
(

let _87_2067 = (new_term_constant_and_tok_from_lid env lid)
in (match (_87_2067) with
| (vname, vtok, env) -> begin
(

let arg_sorts = (match ((let _181_1889 = (FStar_Syntax_Subst.compress t_norm)
in _181_1889.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _87_2070) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun _87_2073 -> FStar_SMTEncoding_Term.Term_sort)))
end
| _87_2076 -> begin
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

let _87_2083 = (prims.mk lid vname)
in (match (_87_2083) with
| (tok, definition) -> begin
(

let env = (push_free_var env lid vname (Some (tok)))
in ((definition), (env)))
end)))
end else begin
(

let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (

let _87_2093 = (

let _87_2088 = (curried_arrow_formals_comp t_norm)
in (match (_87_2088) with
| (args, comp) -> begin
if encode_non_total_function_typ then begin
(let _181_1891 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in ((args), (_181_1891)))
end else begin
((args), (((None), ((FStar_Syntax_Util.comp_result comp)))))
end
end))
in (match (_87_2093) with
| (formals, (pre_opt, res_t)) -> begin
(

let _87_2097 = (new_term_constant_and_tok_from_lid env lid)
in (match (_87_2097) with
| (vname, vtok, env) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
end
| _87_2100 -> begin
(FStar_SMTEncoding_Term.mkApp ((vtok), ([])))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun _87_14 -> (match (_87_14) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(

let _87_2116 = (FStar_Util.prefix vars)
in (match (_87_2116) with
| (_87_2111, (xxsym, _87_2114)) -> begin
(

let xx = (FStar_SMTEncoding_Term.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (let _181_1908 = (let _181_1907 = (let _181_1906 = (let _181_1905 = (let _181_1904 = (let _181_1903 = (let _181_1902 = (let _181_1901 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _181_1901))
in ((vapp), (_181_1902)))
in (FStar_SMTEncoding_Term.mkEq _181_1903))
in ((((vapp)::[])::[]), (vars), (_181_1904)))
in (FStar_SMTEncoding_Term.mkForall _181_1905))
in ((_181_1906), (Some ("Discriminator equation")), (Some ((Prims.strcat "disc_equation_" (escape d.FStar_Ident.str))))))
in FStar_SMTEncoding_Term.Assume (_181_1907))
in (_181_1908)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(

let _87_2128 = (FStar_Util.prefix vars)
in (match (_87_2128) with
| (_87_2123, (xxsym, _87_2126)) -> begin
(

let xx = (FStar_SMTEncoding_Term.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (

let tp_name = (mk_term_projector_name d f)
in (

let prim_app = (FStar_SMTEncoding_Term.mkApp ((tp_name), ((xx)::[])))
in (let _181_1913 = (let _181_1912 = (let _181_1911 = (let _181_1910 = (let _181_1909 = (FStar_SMTEncoding_Term.mkEq ((vapp), (prim_app)))
in ((((vapp)::[])::[]), (vars), (_181_1909)))
in (FStar_SMTEncoding_Term.mkForall _181_1910))
in ((_181_1911), (Some ("Projector equation")), (Some ((Prims.strcat "proj_equation_" tp_name)))))
in FStar_SMTEncoding_Term.Assume (_181_1912))
in (_181_1913)::[])))))
end))
end
| _87_2134 -> begin
[]
end)))))
in (

let _87_2141 = (encode_binders None formals env)
in (match (_87_2141) with
| (vars, guards, env', decls1, _87_2140) -> begin
(

let _87_2150 = (match (pre_opt) with
| None -> begin
(let _181_1914 = (FStar_SMTEncoding_Term.mk_and_l guards)
in ((_181_1914), (decls1)))
end
| Some (p) -> begin
(

let _87_2147 = (encode_formula p env')
in (match (_87_2147) with
| (g, ds) -> begin
(let _181_1915 = (FStar_SMTEncoding_Term.mk_and_l ((g)::guards))
in ((_181_1915), ((FStar_List.append decls1 ds))))
end))
end)
in (match (_87_2150) with
| (guard, decls1) -> begin
(

let vtok_app = (mk_Apply vtok_tm vars)
in (

let vapp = (let _181_1917 = (let _181_1916 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in ((vname), (_181_1916)))
in (FStar_SMTEncoding_Term.mkApp _181_1917))
in (

let _87_2174 = (

let vname_decl = (let _181_1920 = (let _181_1919 = (FStar_All.pipe_right formals (FStar_List.map (fun _87_2153 -> FStar_SMTEncoding_Term.Term_sort)))
in ((vname), (_181_1919), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (_181_1920))
in (

let _87_2161 = (

let env = (

let _87_2156 = env
in {bindings = _87_2156.bindings; depth = _87_2156.depth; tcenv = _87_2156.tcenv; warn = _87_2156.warn; cache = _87_2156.cache; nolabels = _87_2156.nolabels; use_zfuel_name = _87_2156.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in if (not ((head_normal env tt))) then begin
(encode_term_pred None tt env vtok_tm)
end else begin
(encode_term_pred None t_norm env vtok_tm)
end)
in (match (_87_2161) with
| (tok_typing, decls2) -> begin
(

let tok_typing = FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("function token typing")), (Some ((Prims.strcat "function_token_typing_" vname)))))
in (

let _87_2171 = (match (formals) with
| [] -> begin
(let _181_1924 = (let _181_1923 = (let _181_1922 = (FStar_SMTEncoding_Term.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left (fun _181_1921 -> Some (_181_1921)) _181_1922))
in (push_free_var env lid vname _181_1923))
in (((FStar_List.append decls2 ((tok_typing)::[]))), (_181_1924)))
end
| _87_2165 -> begin
(

let vtok_decl = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let vtok_fresh = (let _181_1925 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((vtok), (FStar_SMTEncoding_Term.Term_sort)) _181_1925))
in (

let name_tok_corr = (let _181_1929 = (let _181_1928 = (let _181_1927 = (let _181_1926 = (FStar_SMTEncoding_Term.mkEq ((vtok_app), (vapp)))
in ((((vtok_app)::[])::((vapp)::[])::[]), (vars), (_181_1926)))
in (FStar_SMTEncoding_Term.mkForall _181_1927))
in ((_181_1928), (Some ("Name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" vname)))))
in FStar_SMTEncoding_Term.Assume (_181_1929))
in (((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[]))), (env)))))
end)
in (match (_87_2171) with
| (tok_decl, env) -> begin
(((vname_decl)::tok_decl), (env))
end)))
end)))
in (match (_87_2174) with
| (decls2, env) -> begin
(

let _87_2182 = (

let res_t = (FStar_Syntax_Subst.compress res_t)
in (

let _87_2178 = (encode_term res_t env')
in (match (_87_2178) with
| (encoded_res_t, decls) -> begin
(let _181_1930 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in ((encoded_res_t), (_181_1930), (decls)))
end)))
in (match (_87_2182) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (let _181_1934 = (let _181_1933 = (let _181_1932 = (let _181_1931 = (FStar_SMTEncoding_Term.mkImp ((guard), (ty_pred)))
in ((((vapp)::[])::[]), (vars), (_181_1931)))
in (FStar_SMTEncoding_Term.mkForall _181_1932))
in ((_181_1933), (Some ("free var typing")), (Some ((Prims.strcat "typing_" vname)))))
in FStar_SMTEncoding_Term.Assume (_181_1934))
in (

let freshness = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New)) then begin
(let _181_1940 = (let _181_1937 = (let _181_1936 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (let _181_1935 = (varops.next_id ())
in ((vname), (_181_1936), (FStar_SMTEncoding_Term.Term_sort), (_181_1935))))
in (FStar_SMTEncoding_Term.fresh_constructor _181_1937))
in (let _181_1939 = (let _181_1938 = (pretype_axiom vapp vars)
in (_181_1938)::[])
in (_181_1940)::_181_1939))
end else begin
[]
end
in (

let g = (let _181_1945 = (let _181_1944 = (let _181_1943 = (let _181_1942 = (let _181_1941 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_181_1941)
in (FStar_List.append freshness _181_1942))
in (FStar_List.append decls3 _181_1943))
in (FStar_List.append decls2 _181_1944))
in (FStar_List.append decls1 _181_1945))
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

let _87_2193 = (encode_free_var env x t t_norm [])
in (match (_87_2193) with
| (decls, env) -> begin
(

let _87_2198 = (lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_87_2198) with
| (n, x', _87_2197) -> begin
((((n), (x'))), (decls), (env))
end))
end))
end
| Some (n, x, _87_2202) -> begin
((((n), (x))), ([]), (env))
end))


let encode_top_level_val : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env lid t quals -> (

let tt = (norm env t)
in (

let _87_2212 = (encode_free_var env lid t tt quals)
in (match (_87_2212) with
| (decls, env) -> begin
if (FStar_Syntax_Util.is_smt_lemma t) then begin
(let _181_1963 = (let _181_1962 = (encode_smt_lemma env lid tt)
in (FStar_List.append decls _181_1962))
in ((_181_1963), (env)))
end else begin
((decls), (env))
end
end))))


let encode_top_level_vals : env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _87_2218 lb -> (match (_87_2218) with
| (decls, env) -> begin
(

let _87_2222 = (let _181_1972 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env _181_1972 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (_87_2222) with
| (decls', env) -> begin
(((FStar_List.append decls decls')), (env))
end))
end)) (([]), (env)))))


let encode_top_level_let : env_t  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env _87_2226 quals -> (match (_87_2226) with
| (is_rec, bindings) -> begin
(

let eta_expand = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let _87_2236 = (FStar_Util.first_N nbinders formals)
in (match (_87_2236) with
| (formals, extra_formals) -> begin
(

let subst = (FStar_List.map2 (fun _87_2240 _87_2244 -> (match (((_87_2240), (_87_2244))) with
| ((formal, _87_2239), (binder, _87_2243)) -> begin
(let _181_1990 = (let _181_1989 = (FStar_Syntax_Syntax.bv_to_name binder)
in ((formal), (_181_1989)))
in FStar_Syntax_Syntax.NT (_181_1990))
end)) formals binders)
in (

let extra_formals = (let _181_1994 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun _87_2248 -> (match (_87_2248) with
| (x, i) -> begin
(let _181_1993 = (

let _87_2249 = x
in (let _181_1992 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _87_2249.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _87_2249.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _181_1992}))
in ((_181_1993), (i)))
end))))
in (FStar_All.pipe_right _181_1994 FStar_Syntax_Util.name_binders))
in (

let body = (let _181_2001 = (FStar_Syntax_Subst.compress body)
in (let _181_2000 = (let _181_1995 = (FStar_Syntax_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _181_1995))
in (let _181_1999 = (let _181_1998 = (let _181_1997 = (FStar_Syntax_Subst.subst subst t)
in _181_1997.FStar_Syntax_Syntax.n)
in (FStar_All.pipe_left (fun _181_1996 -> Some (_181_1996)) _181_1998))
in (FStar_Syntax_Syntax.extend_app_n _181_2001 _181_2000 _181_1999 body.FStar_Syntax_Syntax.pos))))
in (((FStar_List.append binders extra_formals)), (body)))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (

let rec aux = (fun norm t_norm -> (match ((let _181_2012 = (FStar_Syntax_Util.unascribe e)
in _181_2012.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, lopt) -> begin
(

let _87_2268 = (FStar_Syntax_Subst.open_term' binders body)
in (match (_87_2268) with
| (binders, body, opening) -> begin
(match ((let _181_2013 = (FStar_Syntax_Subst.compress t_norm)
in _181_2013.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let _87_2275 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_87_2275) with
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

let _87_2282 = (FStar_Util.first_N nformals binders)
in (match (_87_2282) with
| (bs0, rest) -> begin
(

let c = (

let subst = (FStar_List.map2 (fun _87_2286 _87_2290 -> (match (((_87_2286), (_87_2290))) with
| ((b, _87_2285), (x, _87_2289)) -> begin
(let _181_2017 = (let _181_2016 = (FStar_Syntax_Syntax.bv_to_name x)
in ((b), (_181_2016)))
in FStar_Syntax_Syntax.NT (_181_2017))
end)) bs0 formals)
in (FStar_Syntax_Subst.subst_comp subst c))
in (

let body = (FStar_Syntax_Util.abs rest body lopt)
in ((bs0), (body), (bs0), ((FStar_Syntax_Util.comp_result c)))))
end)))
end else begin
if (nformals > nbinders) then begin
(

let _87_2296 = (eta_expand binders formals body tres)
in (match (_87_2296) with
| (binders, body) -> begin
((binders), (body), (formals), (tres))
end))
end else begin
((binders), (body), (formals), (tres))
end
end)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, _87_2299) -> begin
(aux norm x.FStar_Syntax_Syntax.sort)
end
| _87_2303 when (not (norm)) -> begin
(

let t_norm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm)
in (aux true t_norm))
end
| _87_2306 -> begin
(let _181_2020 = (let _181_2019 = (FStar_Syntax_Print.term_to_string e)
in (let _181_2018 = (FStar_Syntax_Print.term_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str _181_2019 _181_2018)))
in (FStar_All.failwith _181_2020))
end)
end))
end
| _87_2308 -> begin
(match ((let _181_2021 = (FStar_Syntax_Subst.compress t_norm)
in _181_2021.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let _87_2315 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_87_2315) with
| (formals, c) -> begin
(

let tres = (FStar_Syntax_Util.comp_result c)
in (

let _87_2319 = (eta_expand [] formals e tres)
in (match (_87_2319) with
| (binders, body) -> begin
((binders), (body), (formals), (tres))
end)))
end))
end
| _87_2321 -> begin
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

let _87_2349 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _87_2336 lb -> (match (_87_2336) with
| (toks, typs, decls, env) -> begin
(

let _87_2338 = if (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) then begin
(Prims.raise Let_rec_unencodeable)
end else begin
()
end
in (

let t_norm = (whnf env lb.FStar_Syntax_Syntax.lbtyp)
in (

let _87_2344 = (let _181_2026 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env _181_2026 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (_87_2344) with
| (tok, decl, env) -> begin
(let _181_2029 = (let _181_2028 = (let _181_2027 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in ((_181_2027), (tok)))
in (_181_2028)::toks)
in ((_181_2029), ((t_norm)::typs), ((decl)::decls), (env)))
end))))
end)) (([]), ([]), ([]), (env))))
in (match (_87_2349) with
| (toks, typs, decls, env) -> begin
(

let toks = (FStar_List.rev toks)
in (

let decls = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (

let typs = (FStar_List.rev typs)
in if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _87_15 -> (match (_87_15) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| _87_2356 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> (let _181_2032 = (FStar_Syntax_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _181_2032)))))) then begin
((decls), (env))
end else begin
if (not (is_rec)) then begin
(match (((bindings), (typs), (toks))) with
| (({FStar_Syntax_Syntax.lbname = _87_2366; FStar_Syntax_Syntax.lbunivs = _87_2364; FStar_Syntax_Syntax.lbtyp = _87_2362; FStar_Syntax_Syntax.lbeff = _87_2360; FStar_Syntax_Syntax.lbdef = e})::[], (t_norm)::[], ((flid_fv, (f, ftok)))::[]) -> begin
(

let e = (FStar_Syntax_Subst.compress e)
in (

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let _87_2386 = (destruct_bound_function flid t_norm e)
in (match (_87_2386) with
| (binders, body, _87_2383, _87_2385) -> begin
(

let _87_2393 = (encode_binders None binders env)
in (match (_87_2393) with
| (vars, guards, env', binder_decls, _87_2392) -> begin
(

let app = (match (vars) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
end
| _87_2396 -> begin
(let _181_2034 = (let _181_2033 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in ((f), (_181_2033)))
in (FStar_SMTEncoding_Term.mkApp _181_2034))
end)
in (

let _87_2402 = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic)) then begin
(let _181_2036 = (FStar_SMTEncoding_Term.mk_Valid app)
in (let _181_2035 = (encode_formula body env')
in ((_181_2036), (_181_2035))))
end else begin
(let _181_2037 = (encode_term body env')
in ((app), (_181_2037)))
end
in (match (_87_2402) with
| (app, (body, decls2)) -> begin
(

let eqn = (let _181_2043 = (let _181_2042 = (let _181_2039 = (let _181_2038 = (FStar_SMTEncoding_Term.mkEq ((app), (body)))
in ((((app)::[])::[]), (vars), (_181_2038)))
in (FStar_SMTEncoding_Term.mkForall _181_2039))
in (let _181_2041 = (let _181_2040 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (_181_2040))
in ((_181_2042), (_181_2041), (Some ((Prims.strcat "equation_" f))))))
in FStar_SMTEncoding_Term.Assume (_181_2043))
in (let _181_2048 = (let _181_2047 = (let _181_2046 = (let _181_2045 = (let _181_2044 = (primitive_type_axioms env.tcenv flid f app)
in (FStar_List.append ((eqn)::[]) _181_2044))
in (FStar_List.append decls2 _181_2045))
in (FStar_List.append binder_decls _181_2046))
in (FStar_List.append decls _181_2047))
in ((_181_2048), (env))))
end)))
end))
end))))
end
| _87_2405 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(

let fuel = (let _181_2049 = (varops.fresh "fuel")
in ((_181_2049), (FStar_SMTEncoding_Term.Fuel_sort)))
in (

let fuel_tm = (FStar_SMTEncoding_Term.mkFreeV fuel)
in (

let env0 = env
in (

let _87_2423 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _87_2411 _87_2416 -> (match (((_87_2411), (_87_2416))) with
| ((gtoks, env), (flid_fv, (f, ftok))) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let g = (let _181_2052 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented")
in (varops.new_fvar _181_2052))
in (

let gtok = (let _181_2053 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented_token")
in (varops.new_fvar _181_2053))
in (

let env = (let _181_2056 = (let _181_2055 = (FStar_SMTEncoding_Term.mkApp ((g), ((fuel_tm)::[])))
in (FStar_All.pipe_left (fun _181_2054 -> Some (_181_2054)) _181_2055))
in (push_free_var env flid gtok _181_2056))
in (((((flid), (f), (ftok), (g), (gtok)))::gtoks), (env))))))
end)) (([]), (env))))
in (match (_87_2423) with
| (gtoks, env) -> begin
(

let gtoks = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env0 _87_2432 t_norm _87_2443 -> (match (((_87_2432), (_87_2443))) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = _87_2442; FStar_Syntax_Syntax.lbunivs = _87_2440; FStar_Syntax_Syntax.lbtyp = _87_2438; FStar_Syntax_Syntax.lbeff = _87_2436; FStar_Syntax_Syntax.lbdef = e}) -> begin
(

let _87_2448 = (destruct_bound_function flid t_norm e)
in (match (_87_2448) with
| (binders, body, formals, tres) -> begin
(

let _87_2455 = (encode_binders None binders env)
in (match (_87_2455) with
| (vars, guards, env', binder_decls, _87_2454) -> begin
(

let decl_g = (let _181_2067 = (let _181_2066 = (let _181_2065 = (FStar_List.map Prims.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::_181_2065)
in ((g), (_181_2066), (FStar_SMTEncoding_Term.Term_sort), (Some ("Fuel-instrumented function name"))))
in FStar_SMTEncoding_Term.DeclFun (_181_2067))
in (

let env0 = (push_zfuel_name env0 flid g)
in (

let decl_g_tok = FStar_SMTEncoding_Term.DeclFun (((gtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Token for fuel-instrumented partial applications"))))
in (

let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (

let app = (FStar_SMTEncoding_Term.mkApp ((f), (vars_tm)))
in (

let gsapp = (let _181_2070 = (let _181_2069 = (let _181_2068 = (FStar_SMTEncoding_Term.mkApp (("SFuel"), ((fuel_tm)::[])))
in (_181_2068)::vars_tm)
in ((g), (_181_2069)))
in (FStar_SMTEncoding_Term.mkApp _181_2070))
in (

let gmax = (let _181_2073 = (let _181_2072 = (let _181_2071 = (FStar_SMTEncoding_Term.mkApp (("MaxFuel"), ([])))
in (_181_2071)::vars_tm)
in ((g), (_181_2072)))
in (FStar_SMTEncoding_Term.mkApp _181_2073))
in (

let _87_2465 = (encode_term body env')
in (match (_87_2465) with
| (body_tm, decls2) -> begin
(

let eqn_g = (let _181_2079 = (let _181_2078 = (let _181_2075 = (let _181_2074 = (FStar_SMTEncoding_Term.mkEq ((gsapp), (body_tm)))
in ((((gsapp)::[])::[]), (Some ((Prims.parse_int "0"))), ((fuel)::vars), (_181_2074)))
in (FStar_SMTEncoding_Term.mkForall' _181_2075))
in (let _181_2077 = (let _181_2076 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (_181_2076))
in ((_181_2078), (_181_2077), (Some ((Prims.strcat "equation_with_fuel_" g))))))
in FStar_SMTEncoding_Term.Assume (_181_2079))
in (

let eqn_f = (let _181_2083 = (let _181_2082 = (let _181_2081 = (let _181_2080 = (FStar_SMTEncoding_Term.mkEq ((app), (gmax)))
in ((((app)::[])::[]), (vars), (_181_2080)))
in (FStar_SMTEncoding_Term.mkForall _181_2081))
in ((_181_2082), (Some ("Correspondence of recursive function to instrumented version")), (Some ((Prims.strcat "fuel_correspondence_" g)))))
in FStar_SMTEncoding_Term.Assume (_181_2083))
in (

let eqn_g' = (let _181_2092 = (let _181_2091 = (let _181_2090 = (let _181_2089 = (let _181_2088 = (let _181_2087 = (let _181_2086 = (let _181_2085 = (let _181_2084 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "0"))
in (_181_2084)::vars_tm)
in ((g), (_181_2085)))
in (FStar_SMTEncoding_Term.mkApp _181_2086))
in ((gsapp), (_181_2087)))
in (FStar_SMTEncoding_Term.mkEq _181_2088))
in ((((gsapp)::[])::[]), ((fuel)::vars), (_181_2089)))
in (FStar_SMTEncoding_Term.mkForall _181_2090))
in ((_181_2091), (Some ("Fuel irrelevance")), (Some ((Prims.strcat "fuel_irrelevance_" g)))))
in FStar_SMTEncoding_Term.Assume (_181_2092))
in (

let _87_2488 = (

let _87_2475 = (encode_binders None formals env0)
in (match (_87_2475) with
| (vars, v_guards, env, binder_decls, _87_2474) -> begin
(

let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (

let gapp = (FStar_SMTEncoding_Term.mkApp ((g), ((fuel_tm)::vars_tm)))
in (

let tok_corr = (

let tok_app = (let _181_2093 = (FStar_SMTEncoding_Term.mkFreeV ((gtok), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply _181_2093 ((fuel)::vars)))
in (let _181_2097 = (let _181_2096 = (let _181_2095 = (let _181_2094 = (FStar_SMTEncoding_Term.mkEq ((tok_app), (gapp)))
in ((((tok_app)::[])::[]), ((fuel)::vars), (_181_2094)))
in (FStar_SMTEncoding_Term.mkForall _181_2095))
in ((_181_2096), (Some ("Fuel token correspondence")), (Some ((Prims.strcat "fuel_token_correspondence_" gtok)))))
in FStar_SMTEncoding_Term.Assume (_181_2097)))
in (

let _87_2485 = (

let _87_2482 = (encode_term_pred None tres env gapp)
in (match (_87_2482) with
| (g_typing, d3) -> begin
(let _181_2105 = (let _181_2104 = (let _181_2103 = (let _181_2102 = (let _181_2101 = (let _181_2100 = (let _181_2099 = (let _181_2098 = (FStar_SMTEncoding_Term.mk_and_l v_guards)
in ((_181_2098), (g_typing)))
in (FStar_SMTEncoding_Term.mkImp _181_2099))
in ((((gapp)::[])::[]), ((fuel)::vars), (_181_2100)))
in (FStar_SMTEncoding_Term.mkForall _181_2101))
in ((_181_2102), (Some ("Typing correspondence of token to term")), (Some ((Prims.strcat "token_correspondence_" g)))))
in FStar_SMTEncoding_Term.Assume (_181_2103))
in (_181_2104)::[])
in ((d3), (_181_2105)))
end))
in (match (_87_2485) with
| (aux_decls, typing_corr) -> begin
(((FStar_List.append binder_decls aux_decls)), ((FStar_List.append typing_corr ((tok_corr)::[]))))
end)))))
end))
in (match (_87_2488) with
| (aux_decls, g_typing) -> begin
(((FStar_List.append binder_decls (FStar_List.append decls2 (FStar_List.append aux_decls ((decl_g)::(decl_g_tok)::[]))))), ((FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing)), (env0))
end)))))
end)))))))))
end))
end))
end))
in (

let _87_2504 = (let _181_2108 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _87_2492 _87_2496 -> (match (((_87_2492), (_87_2496))) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(

let _87_2500 = (encode_one_binding env0 gtok ty bs)
in (match (_87_2500) with
| (decls', eqns', env0) -> begin
(((decls')::decls), ((FStar_List.append eqns' eqns)), (env0))
end))
end)) (((decls)::[]), ([]), (env0)) _181_2108))
in (match (_87_2504) with
| (decls, eqns, env0) -> begin
(

let _87_2513 = (let _181_2110 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _181_2110 (FStar_List.partition (fun _87_16 -> (match (_87_16) with
| FStar_SMTEncoding_Term.DeclFun (_87_2507) -> begin
true
end
| _87_2510 -> begin
false
end)))))
in (match (_87_2513) with
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

let msg = (let _181_2113 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _181_2113 (FStar_String.concat " and ")))
in (

let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in (((decl)::[]), (env))))
end))
end))


let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let _87_2517 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _181_2122 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _181_2122))
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

let _87_2525 = (encode_sigelt' env se)
in (match (_87_2525) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _181_2125 = (let _181_2124 = (let _181_2123 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (_181_2123))
in (_181_2124)::[])
in ((_181_2125), (e)))
end
| _87_2528 -> begin
(let _181_2132 = (let _181_2131 = (let _181_2127 = (let _181_2126 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_181_2126))
in (_181_2127)::g)
in (let _181_2130 = (let _181_2129 = (let _181_2128 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_181_2128))
in (_181_2129)::[])
in (FStar_List.append _181_2131 _181_2130)))
in ((_181_2132), (e)))
end)
end)))))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let should_skip = (fun l -> false)
in (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_87_2534) -> begin
(FStar_All.failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _87_2550) -> begin
if (let _181_2137 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right _181_2137 Prims.op_Negation)) then begin
(([]), (env))
end else begin
(

let close_effect_params = (fun tm -> (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
tm
end
| _87_2557 -> begin
(let _181_2143 = (let _181_2142 = (let _181_2141 = (FStar_All.pipe_left (fun _181_2140 -> Some (_181_2140)) (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid)))
in ((ed.FStar_Syntax_Syntax.binders), (tm), (_181_2141)))
in FStar_Syntax_Syntax.Tm_abs (_181_2142))
in (FStar_Syntax_Syntax.mk _181_2143 None tm.FStar_Syntax_Syntax.pos))
end))
in (

let encode_action = (fun env a -> (

let _87_2564 = (new_term_constant_and_tok_from_lid env a.FStar_Syntax_Syntax.action_name)
in (match (_87_2564) with
| (aname, atok, env) -> begin
(

let _87_2568 = (FStar_Syntax_Util.arrow_formals_comp a.FStar_Syntax_Syntax.action_typ)
in (match (_87_2568) with
| (formals, _87_2567) -> begin
(

let _87_2571 = (let _181_2148 = (close_effect_params a.FStar_Syntax_Syntax.action_defn)
in (encode_term _181_2148 env))
in (match (_87_2571) with
| (tm, decls) -> begin
(

let a_decls = (let _181_2152 = (let _181_2151 = (let _181_2150 = (FStar_All.pipe_right formals (FStar_List.map (fun _87_2572 -> FStar_SMTEncoding_Term.Term_sort)))
in ((aname), (_181_2150), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action"))))
in FStar_SMTEncoding_Term.DeclFun (_181_2151))
in (_181_2152)::(FStar_SMTEncoding_Term.DeclFun (((atok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action token")))))::[])
in (

let _87_2586 = (let _181_2154 = (FStar_All.pipe_right formals (FStar_List.map (fun _87_2578 -> (match (_87_2578) with
| (bv, _87_2577) -> begin
(

let _87_2583 = (gen_term_var env bv)
in (match (_87_2583) with
| (xxsym, xx, _87_2582) -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (xx))
end))
end))))
in (FStar_All.pipe_right _181_2154 FStar_List.split))
in (match (_87_2586) with
| (xs_sorts, xs) -> begin
(

let app = (let _181_2158 = (let _181_2157 = (let _181_2156 = (let _181_2155 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Var (aname)), (xs)))))
in (_181_2155)::[])
in ((FStar_SMTEncoding_Term.Var ("Reify")), (_181_2156)))
in FStar_SMTEncoding_Term.App (_181_2157))
in (FStar_All.pipe_right _181_2158 FStar_SMTEncoding_Term.mk))
in (

let a_eq = (let _181_2164 = (let _181_2163 = (let _181_2162 = (let _181_2161 = (let _181_2160 = (let _181_2159 = (mk_Apply tm xs_sorts)
in ((app), (_181_2159)))
in (FStar_SMTEncoding_Term.mkEq _181_2160))
in ((((app)::[])::[]), (xs_sorts), (_181_2161)))
in (FStar_SMTEncoding_Term.mkForall _181_2162))
in ((_181_2163), (Some ("Action equality")), (Some ((Prims.strcat aname "_equality")))))
in FStar_SMTEncoding_Term.Assume (_181_2164))
in (

let tok_correspondence = (

let tok_term = (FStar_SMTEncoding_Term.mkFreeV ((atok), (FStar_SMTEncoding_Term.Term_sort)))
in (

let tok_app = (mk_Apply tok_term xs_sorts)
in (let _181_2168 = (let _181_2167 = (let _181_2166 = (let _181_2165 = (FStar_SMTEncoding_Term.mkEq ((tok_app), (app)))
in ((((tok_app)::[])::[]), (xs_sorts), (_181_2165)))
in (FStar_SMTEncoding_Term.mkForall _181_2166))
in ((_181_2167), (Some ("Action token correspondence")), (Some ((Prims.strcat aname "_token_correspondence")))))
in FStar_SMTEncoding_Term.Assume (_181_2168))))
in ((env), ((FStar_List.append decls (FStar_List.append a_decls ((a_eq)::(tok_correspondence)::[]))))))))
end)))
end))
end))
end)))
in (

let _87_2594 = (FStar_Util.fold_map encode_action env ed.FStar_Syntax_Syntax.actions)
in (match (_87_2594) with
| (env, decls2) -> begin
(((FStar_List.flatten decls2)), (env))
end))))
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _87_2597, _87_2599, _87_2601, _87_2603) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid) -> begin
(

let _87_2609 = (new_term_constant_and_tok_from_lid env lid)
in (match (_87_2609) with
| (tname, ttok, env) -> begin
(([]), (env))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _87_2612, t, quals, _87_2616) -> begin
(

let will_encode_definition = (not ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _87_17 -> (match (_87_17) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Irreducible) -> begin
true
end
| _87_2629 -> begin
false
end))))))
in if will_encode_definition then begin
(([]), (env))
end else begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (

let _87_2634 = (encode_top_level_val env fv t quals)
in (match (_87_2634) with
| (decls, env) -> begin
(

let tname = lid.FStar_Ident.str
in (

let tsym = (FStar_SMTEncoding_Term.mkFreeV ((tname), (FStar_SMTEncoding_Term.Term_sort)))
in (let _181_2171 = (let _181_2170 = (primitive_type_axioms env.tcenv lid tname tsym)
in (FStar_List.append decls _181_2170))
in ((_181_2171), (env)))))
end)))
end)
end
| FStar_Syntax_Syntax.Sig_assume (l, f, _87_2640, _87_2642) -> begin
(

let _87_2647 = (encode_formula f env)
in (match (_87_2647) with
| (f, decls) -> begin
(

let g = (let _181_2178 = (let _181_2177 = (let _181_2176 = (let _181_2173 = (let _181_2172 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" _181_2172))
in Some (_181_2173))
in (let _181_2175 = (let _181_2174 = (varops.mk_unique (Prims.strcat "assumption_" l.FStar_Ident.str))
in Some (_181_2174))
in ((f), (_181_2176), (_181_2175))))
in FStar_SMTEncoding_Term.Assume (_181_2177))
in (_181_2178)::[])
in (((FStar_List.append decls g)), (env)))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _87_2652, quals) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) -> begin
(

let _87_2665 = (FStar_Util.fold_map (fun env lb -> (

let lid = (let _181_2182 = (let _181_2181 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _181_2181.FStar_Syntax_Syntax.fv_name)
in _181_2182.FStar_Syntax_Syntax.v)
in if (let _181_2183 = (FStar_TypeChecker_Env.try_lookup_val_decl env.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone _181_2183)) then begin
(

let val_decl = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), (r)))
in (

let _87_2662 = (encode_sigelt' env val_decl)
in (match (_87_2662) with
| (decls, env) -> begin
((env), (decls))
end)))
end else begin
((env), ([]))
end)) env (Prims.snd lbs))
in (match (_87_2665) with
| (env, decls) -> begin
(((FStar_List.flatten decls)), (env))
end))
end
| FStar_Syntax_Syntax.Sig_let ((_87_2667, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t); FStar_Syntax_Syntax.lbunivs = _87_2675; FStar_Syntax_Syntax.lbtyp = _87_2673; FStar_Syntax_Syntax.lbeff = _87_2671; FStar_Syntax_Syntax.lbdef = _87_2669})::[]), _87_2682, _87_2684, _87_2686) when (FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Syntax_Const.b2t_lid) -> begin
(

let _87_2692 = (new_term_constant_and_tok_from_lid env b2t.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_87_2692) with
| (tname, ttok, env) -> begin
(

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (

let valid_b2t_x = (let _181_2186 = (let _181_2185 = (let _181_2184 = (FStar_SMTEncoding_Term.mkApp (("Prims.b2t"), ((x)::[])))
in (_181_2184)::[])
in (("Valid"), (_181_2185)))
in (FStar_SMTEncoding_Term.mkApp _181_2186))
in (

let decls = (let _181_2194 = (let _181_2193 = (let _181_2192 = (let _181_2191 = (let _181_2190 = (let _181_2189 = (let _181_2188 = (let _181_2187 = (FStar_SMTEncoding_Term.mkApp (("BoxBool_proj_0"), ((x)::[])))
in ((valid_b2t_x), (_181_2187)))
in (FStar_SMTEncoding_Term.mkEq _181_2188))
in ((((valid_b2t_x)::[])::[]), ((xx)::[]), (_181_2189)))
in (FStar_SMTEncoding_Term.mkForall _181_2190))
in ((_181_2191), (Some ("b2t def")), (Some ("b2t_def"))))
in FStar_SMTEncoding_Term.Assume (_181_2192))
in (_181_2193)::[])
in (FStar_SMTEncoding_Term.DeclFun (((tname), ((FStar_SMTEncoding_Term.Term_sort)::[]), (FStar_SMTEncoding_Term.Term_sort), (None))))::_181_2194)
in ((decls), (env))))))
end))
end
| FStar_Syntax_Syntax.Sig_let (_87_2698, _87_2700, _87_2702, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _87_18 -> (match (_87_18) with
| FStar_Syntax_Syntax.Discriminator (_87_2708) -> begin
true
end
| _87_2711 -> begin
false
end)))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let (_87_2713, _87_2715, lids, quals) when ((FStar_All.pipe_right lids (FStar_Util.for_some (fun l -> ((let _181_2197 = (FStar_List.hd l.FStar_Ident.ns)
in _181_2197.FStar_Ident.idText) = "Prims")))) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun _87_19 -> (match (_87_19) with
| FStar_Syntax_Syntax.Inline -> begin
true
end
| _87_2724 -> begin
false
end))))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _87_2730, _87_2732, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _87_20 -> (match (_87_20) with
| FStar_Syntax_Syntax.Projector (_87_2738) -> begin
true
end
| _87_2741 -> begin
false
end)))) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((try_lookup_free_var env l)) with
| Some (_87_2745) -> begin
(([]), (env))
end
| None -> begin
(

let se = FStar_Syntax_Syntax.Sig_declare_typ (((l), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), ((FStar_Ident.range_of_lid l))))
in (encode_sigelt env se))
end)))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _87_2754, _87_2756, quals) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) -> begin
(match ((let _181_2200 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef)
in _181_2200.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, _87_2763) -> begin
(

let body = (FStar_Syntax_Util.mk_reify body)
in (

let tm = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None)))) None lb.FStar_Syntax_Syntax.lbdef.FStar_Syntax_Syntax.pos)
in (

let tm' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env.tcenv tm)
in (

let lb_typ = (

let _87_2771 = (FStar_Syntax_Util.arrow_formals_comp lb.FStar_Syntax_Syntax.lbtyp)
in (match (_87_2771) with
| (formals, comp) -> begin
(

let reified_typ = (FStar_TypeChecker_Util.reify_comp (

let _87_2772 = env.tcenv
in {FStar_TypeChecker_Env.solver = _87_2772.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _87_2772.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _87_2772.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _87_2772.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _87_2772.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _87_2772.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _87_2772.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _87_2772.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _87_2772.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _87_2772.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _87_2772.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _87_2772.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _87_2772.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _87_2772.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _87_2772.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _87_2772.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _87_2772.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _87_2772.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _87_2772.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _87_2772.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _87_2772.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _87_2772.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _87_2772.FStar_TypeChecker_Env.qname_and_index}) (FStar_Syntax_Util.lcomp_of_comp comp) FStar_Syntax_Syntax.U_unknown)
in (let _181_2201 = (FStar_Syntax_Syntax.mk_Total reified_typ)
in (FStar_Syntax_Util.arrow formals _181_2201)))
end))
in (

let lb = (

let _87_2776 = lb
in {FStar_Syntax_Syntax.lbname = _87_2776.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _87_2776.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lb_typ; FStar_Syntax_Syntax.lbeff = _87_2776.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = tm'})
in (encode_top_level_let env ((false), ((lb)::[])) quals))))))
end
| _87_2780 -> begin
(([]), (env))
end)
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), _87_2785, _87_2787, quals) -> begin
(encode_top_level_let env ((is_rec), (bindings)) quals)
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _87_2793, _87_2795, _87_2797) -> begin
(

let _87_2802 = (encode_signature env ses)
in (match (_87_2802) with
| (g, env) -> begin
(

let _87_2816 = (FStar_All.pipe_right g (FStar_List.partition (fun _87_21 -> (match (_87_21) with
| FStar_SMTEncoding_Term.Assume (_87_2805, Some ("inversion axiom"), _87_2809) -> begin
false
end
| _87_2813 -> begin
true
end))))
in (match (_87_2816) with
| (g', inversions) -> begin
(

let _87_2825 = (FStar_All.pipe_right g' (FStar_List.partition (fun _87_22 -> (match (_87_22) with
| FStar_SMTEncoding_Term.DeclFun (_87_2819) -> begin
true
end
| _87_2822 -> begin
false
end))))
in (match (_87_2825) with
| (decls, rest) -> begin
(((FStar_List.append decls (FStar_List.append rest inversions))), (env))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, _87_2828, tps, k, _87_2832, datas, quals, _87_2836) -> begin
(

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _87_23 -> (match (_87_23) with
| (FStar_Syntax_Syntax.Logic) | (FStar_Syntax_Syntax.Assumption) -> begin
true
end
| _87_2843 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(

let _87_2855 = c
in (match (_87_2855) with
| (name, args, _87_2850, _87_2852, _87_2854) -> begin
(let _181_2209 = (let _181_2208 = (let _181_2207 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in ((name), (_181_2207), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (_181_2208))
in (_181_2209)::[])
end))
end else begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end)
in (

let inversion_axioms = (fun tapp vars -> if (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _181_2215 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right _181_2215 FStar_Option.isNone))))) then begin
[]
end else begin
(

let _87_2862 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_87_2862) with
| (xxsym, xx) -> begin
(

let _87_2898 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _87_2865 l -> (match (_87_2865) with
| (out, decls) -> begin
(

let _87_2870 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (_87_2870) with
| (_87_2868, data_t) -> begin
(

let _87_2873 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (_87_2873) with
| (args, res) -> begin
(

let indices = (match ((let _181_2218 = (FStar_Syntax_Subst.compress res)
in _181_2218.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_87_2875, indices) -> begin
indices
end
| _87_2880 -> begin
[]
end)
in (

let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env _87_2886 -> (match (_87_2886) with
| (x, _87_2885) -> begin
(let _181_2223 = (let _181_2222 = (let _181_2221 = (mk_term_projector_name l x)
in ((_181_2221), ((xx)::[])))
in (FStar_SMTEncoding_Term.mkApp _181_2222))
in (push_term_var env x _181_2223))
end)) env))
in (

let _87_2890 = (encode_args indices env)
in (match (_87_2890) with
| (indices, decls') -> begin
(

let _87_2891 = if ((FStar_List.length indices) <> (FStar_List.length vars)) then begin
(FStar_All.failwith "Impossible")
end else begin
()
end
in (

let eqs = (let _181_2228 = (FStar_List.map2 (fun v a -> (let _181_2227 = (let _181_2226 = (FStar_SMTEncoding_Term.mkFreeV v)
in ((_181_2226), (a)))
in (FStar_SMTEncoding_Term.mkEq _181_2227))) vars indices)
in (FStar_All.pipe_right _181_2228 FStar_SMTEncoding_Term.mk_and_l))
in (let _181_2233 = (let _181_2232 = (let _181_2231 = (let _181_2230 = (let _181_2229 = (mk_data_tester env l xx)
in ((_181_2229), (eqs)))
in (FStar_SMTEncoding_Term.mkAnd _181_2230))
in ((out), (_181_2231)))
in (FStar_SMTEncoding_Term.mkOr _181_2232))
in ((_181_2233), ((FStar_List.append decls decls'))))))
end))))
end))
end))
end)) ((FStar_SMTEncoding_Term.mkFalse), ([]))))
in (match (_87_2898) with
| (data_ax, decls) -> begin
(

let _87_2901 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_87_2901) with
| (ffsym, ff) -> begin
(

let fuel_guarded_inversion = (

let xx_has_type_sfuel = if ((FStar_List.length datas) > (Prims.parse_int "1")) then begin
(let _181_2234 = (FStar_SMTEncoding_Term.mkApp (("SFuel"), ((ff)::[])))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel _181_2234 xx tapp))
end else begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end
in (let _181_2241 = (let _181_2240 = (let _181_2237 = (let _181_2236 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (let _181_2235 = (FStar_SMTEncoding_Term.mkImp ((xx_has_type_sfuel), (data_ax)))
in ((((xx_has_type_sfuel)::[])::[]), (_181_2236), (_181_2235))))
in (FStar_SMTEncoding_Term.mkForall _181_2237))
in (let _181_2239 = (let _181_2238 = (varops.mk_unique (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str))
in Some (_181_2238))
in ((_181_2240), (Some ("inversion axiom")), (_181_2239))))
in FStar_SMTEncoding_Term.Assume (_181_2241)))
in (

let pattern_guarded_inversion = if ((contains_name env "Prims.inversion") && ((FStar_List.length datas) > (Prims.parse_int "1"))) then begin
(

let xx_has_type_fuel = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let pattern_guard = (FStar_SMTEncoding_Term.mkApp (("Prims.inversion"), ((tapp)::[])))
in (let _181_2249 = (let _181_2248 = (let _181_2247 = (let _181_2244 = (let _181_2243 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (let _181_2242 = (FStar_SMTEncoding_Term.mkImp ((xx_has_type_fuel), (data_ax)))
in ((((xx_has_type_fuel)::(pattern_guard)::[])::[]), (_181_2243), (_181_2242))))
in (FStar_SMTEncoding_Term.mkForall _181_2244))
in (let _181_2246 = (let _181_2245 = (varops.mk_unique (Prims.strcat "pattern_guarded_inversion_" t.FStar_Ident.str))
in Some (_181_2245))
in ((_181_2247), (Some ("inversion axiom")), (_181_2246))))
in FStar_SMTEncoding_Term.Assume (_181_2248))
in (_181_2249)::[])))
end else begin
[]
end
in (FStar_List.append decls (FStar_List.append ((fuel_guarded_inversion)::[]) pattern_guarded_inversion))))
end))
end))
end))
end)
in (

let _87_2915 = (match ((let _181_2250 = (FStar_Syntax_Subst.compress k)
in _181_2250.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
(((FStar_List.append tps formals)), ((FStar_Syntax_Util.comp_result kres)))
end
| _87_2912 -> begin
((tps), (k))
end)
in (match (_87_2915) with
| (formals, res) -> begin
(

let _87_2918 = (FStar_Syntax_Subst.open_term formals res)
in (match (_87_2918) with
| (formals, res) -> begin
(

let _87_2925 = (encode_binders None formals env)
in (match (_87_2925) with
| (vars, guards, env', binder_decls, _87_2924) -> begin
(

let _87_2929 = (new_term_constant_and_tok_from_lid env t)
in (match (_87_2929) with
| (tname, ttok, env) -> begin
(

let ttok_tm = (FStar_SMTEncoding_Term.mkApp ((ttok), ([])))
in (

let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (

let tapp = (let _181_2252 = (let _181_2251 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in ((tname), (_181_2251)))
in (FStar_SMTEncoding_Term.mkApp _181_2252))
in (

let _87_2950 = (

let tname_decl = (let _181_2256 = (let _181_2255 = (FStar_All.pipe_right vars (FStar_List.map (fun _87_2935 -> (match (_87_2935) with
| (n, s) -> begin
(((Prims.strcat tname n)), (s))
end))))
in (let _181_2254 = (varops.next_id ())
in ((tname), (_181_2255), (FStar_SMTEncoding_Term.Term_sort), (_181_2254), (false))))
in (constructor_or_logic_type_decl _181_2256))
in (

let _87_2947 = (match (vars) with
| [] -> begin
(let _181_2260 = (let _181_2259 = (let _181_2258 = (FStar_SMTEncoding_Term.mkApp ((tname), ([])))
in (FStar_All.pipe_left (fun _181_2257 -> Some (_181_2257)) _181_2258))
in (push_free_var env t tname _181_2259))
in (([]), (_181_2260)))
end
| _87_2939 -> begin
(

let ttok_decl = FStar_SMTEncoding_Term.DeclFun (((ttok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("token"))))
in (

let ttok_fresh = (let _181_2261 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ttok), (FStar_SMTEncoding_Term.Term_sort)) _181_2261))
in (

let ttok_app = (mk_Apply ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (let _181_2265 = (let _181_2264 = (let _181_2263 = (let _181_2262 = (FStar_SMTEncoding_Term.mkEq ((ttok_app), (tapp)))
in ((pats), (None), (vars), (_181_2262)))
in (FStar_SMTEncoding_Term.mkForall' _181_2263))
in ((_181_2264), (Some ("name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" ttok)))))
in FStar_SMTEncoding_Term.Assume (_181_2265))
in (((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[]), (env)))))))
end)
in (match (_87_2947) with
| (tok_decls, env) -> begin
(((FStar_List.append tname_decl tok_decls)), (env))
end)))
in (match (_87_2950) with
| (decls, env) -> begin
(

let kindingAx = (

let _87_2953 = (encode_term_pred None res env' tapp)
in (match (_87_2953) with
| (k, decls) -> begin
(

let karr = if ((FStar_List.length formals) > (Prims.parse_int "0")) then begin
(let _181_2269 = (let _181_2268 = (let _181_2267 = (let _181_2266 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _181_2266))
in ((_181_2267), (Some ("kinding")), (Some ((Prims.strcat "pre_kinding_" ttok)))))
in FStar_SMTEncoding_Term.Assume (_181_2268))
in (_181_2269)::[])
end else begin
[]
end
in (let _181_2276 = (let _181_2275 = (let _181_2274 = (let _181_2273 = (let _181_2272 = (let _181_2271 = (let _181_2270 = (FStar_SMTEncoding_Term.mkImp ((guard), (k)))
in ((((tapp)::[])::[]), (vars), (_181_2270)))
in (FStar_SMTEncoding_Term.mkForall _181_2271))
in ((_181_2272), (None), (Some ((Prims.strcat "kinding_" ttok)))))
in FStar_SMTEncoding_Term.Assume (_181_2273))
in (_181_2274)::[])
in (FStar_List.append karr _181_2275))
in (FStar_List.append decls _181_2276)))
end))
in (

let aux = (let _181_2280 = (let _181_2279 = (inversion_axioms tapp vars)
in (let _181_2278 = (let _181_2277 = (pretype_axiom tapp vars)
in (_181_2277)::[])
in (FStar_List.append _181_2279 _181_2278)))
in (FStar_List.append kindingAx _181_2280))
in (

let g = (FStar_List.append decls (FStar_List.append binder_decls aux))
in ((g), (env)))))
end)))))
end))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, _87_2960, _87_2962, _87_2964, _87_2966, _87_2968, _87_2970, _87_2972) when (FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_datacon (d, _87_2977, t, _87_2980, n_tps, quals, _87_2984, drange) -> begin
(

let _87_2991 = (new_term_constant_and_tok_from_lid env d)
in (match (_87_2991) with
| (ddconstrsym, ddtok, env) -> begin
(

let ddtok_tm = (FStar_SMTEncoding_Term.mkApp ((ddtok), ([])))
in (

let _87_2995 = (FStar_Syntax_Util.arrow_formals t)
in (match (_87_2995) with
| (formals, t_res) -> begin
(

let _87_2998 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_87_2998) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_SMTEncoding_Term.mkApp (("SFuel"), ((fuel_tm)::[])))
in (

let _87_3005 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_87_3005) with
| (vars, guards, env', binder_decls, names) -> begin
(

let projectors = (FStar_All.pipe_right names (FStar_List.map (fun x -> (let _181_2282 = (mk_term_projector_name d x)
in ((_181_2282), (FStar_SMTEncoding_Term.Term_sort))))))
in (

let datacons = (let _181_2284 = (let _181_2283 = (varops.next_id ())
in ((ddconstrsym), (projectors), (FStar_SMTEncoding_Term.Term_sort), (_181_2283), (true)))
in (FStar_All.pipe_right _181_2284 FStar_SMTEncoding_Term.constructor_to_decl))
in (

let app = (mk_Apply ddtok_tm vars)
in (

let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Term.mkApp ((ddconstrsym), (xvars)))
in (

let _87_3015 = (encode_term_pred None t env ddtok_tm)
in (match (_87_3015) with
| (tok_typing, decls3) -> begin
(

let _87_3022 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_87_3022) with
| (vars', guards', env'', decls_formals, _87_3021) -> begin
(

let _87_3027 = (

let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars')
in (

let dapp = (FStar_SMTEncoding_Term.mkApp ((ddconstrsym), (xvars)))
in (encode_term_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_87_3027) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_SMTEncoding_Term.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _87_3031 -> begin
(let _181_2286 = (let _181_2285 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ddtok), (FStar_SMTEncoding_Term.Term_sort)) _181_2285))
in (_181_2286)::[])
end)
in (

let encode_elim = (fun _87_3034 -> (match (()) with
| () -> begin
(

let _87_3037 = (FStar_Syntax_Util.head_and_args t_res)
in (match (_87_3037) with
| (head, args) -> begin
(match ((let _181_2289 = (FStar_Syntax_Subst.compress head)
in _181_2289.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let _87_3055 = (encode_args args env')
in (match (_87_3055) with
| (encoded_args, arg_decls) -> begin
(

let _87_3070 = (FStar_List.fold_left (fun _87_3059 arg -> (match (_87_3059) with
| (env, arg_vars, eqns) -> begin
(

let _87_3065 = (let _181_2292 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in (gen_term_var env _181_2292))
in (match (_87_3065) with
| (_87_3062, xv, env) -> begin
(let _181_2294 = (let _181_2293 = (FStar_SMTEncoding_Term.mkEq ((arg), (xv)))
in (_181_2293)::eqns)
in ((env), ((xv)::arg_vars), (_181_2294)))
end))
end)) ((env'), ([]), ([])) encoded_args)
in (match (_87_3070) with
| (_87_3067, arg_vars, eqns) -> begin
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

let typing_inversion = (let _181_2301 = (let _181_2300 = (let _181_2299 = (let _181_2298 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (let _181_2297 = (let _181_2296 = (let _181_2295 = (FStar_SMTEncoding_Term.mk_and_l (FStar_List.append eqns guards))
in ((ty_pred), (_181_2295)))
in (FStar_SMTEncoding_Term.mkImp _181_2296))
in ((((ty_pred)::[])::[]), (_181_2298), (_181_2297))))
in (FStar_SMTEncoding_Term.mkForall _181_2299))
in ((_181_2300), (Some ("data constructor typing elim")), (Some ((Prims.strcat "data_elim_" ddconstrsym)))))
in FStar_SMTEncoding_Term.Assume (_181_2301))
in (

let subterm_ordering = if (FStar_Ident.lid_equals d FStar_Syntax_Const.lextop_lid) then begin
(

let x = (let _181_2302 = (varops.fresh "x")
in ((_181_2302), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Term.mkFreeV x)
in (let _181_2314 = (let _181_2313 = (let _181_2310 = (let _181_2309 = (let _181_2304 = (let _181_2303 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in (_181_2303)::[])
in (_181_2304)::[])
in (let _181_2308 = (let _181_2307 = (let _181_2306 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (let _181_2305 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in ((_181_2306), (_181_2305))))
in (FStar_SMTEncoding_Term.mkImp _181_2307))
in ((_181_2309), ((x)::[]), (_181_2308))))
in (FStar_SMTEncoding_Term.mkForall _181_2310))
in (let _181_2312 = (let _181_2311 = (varops.mk_unique "lextop")
in Some (_181_2311))
in ((_181_2313), (Some ("lextop is top")), (_181_2312))))
in FStar_SMTEncoding_Term.Assume (_181_2314))))
end else begin
(

let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
[]
end
| FStar_SMTEncoding_Term.Term_sort -> begin
(let _181_2317 = (let _181_2316 = (FStar_SMTEncoding_Term.mkFreeV v)
in (FStar_SMTEncoding_Term.mk_Precedes _181_2316 dapp))
in (_181_2317)::[])
end
| _87_3084 -> begin
(FStar_All.failwith "unexpected sort")
end))))
in (let _181_2324 = (let _181_2323 = (let _181_2322 = (let _181_2321 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (let _181_2320 = (let _181_2319 = (let _181_2318 = (FStar_SMTEncoding_Term.mk_and_l prec)
in ((ty_pred), (_181_2318)))
in (FStar_SMTEncoding_Term.mkImp _181_2319))
in ((((ty_pred)::[])::[]), (_181_2321), (_181_2320))))
in (FStar_SMTEncoding_Term.mkForall _181_2322))
in ((_181_2323), (Some ("subterm ordering")), (Some ((Prims.strcat "subterm_ordering_" ddconstrsym)))))
in FStar_SMTEncoding_Term.Assume (_181_2324)))
end
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end))
end)))
end
| _87_3088 -> begin
(

let _87_3089 = (let _181_2327 = (let _181_2326 = (FStar_Syntax_Print.lid_to_string d)
in (let _181_2325 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _181_2326 _181_2325)))
in (FStar_TypeChecker_Errors.warn drange _181_2327))
in (([]), ([])))
end)
end))
end))
in (

let _87_3093 = (encode_elim ())
in (match (_87_3093) with
| (decls2, elim) -> begin
(

let g = (let _181_2354 = (let _181_2353 = (let _181_2352 = (let _181_2351 = (let _181_2332 = (let _181_2331 = (let _181_2330 = (let _181_2329 = (let _181_2328 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" _181_2328))
in Some (_181_2329))
in ((ddtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (_181_2330)))
in FStar_SMTEncoding_Term.DeclFun (_181_2331))
in (_181_2332)::[])
in (let _181_2350 = (let _181_2349 = (let _181_2348 = (let _181_2347 = (let _181_2346 = (let _181_2345 = (let _181_2344 = (let _181_2336 = (let _181_2335 = (let _181_2334 = (let _181_2333 = (FStar_SMTEncoding_Term.mkEq ((app), (dapp)))
in ((((app)::[])::[]), (vars), (_181_2333)))
in (FStar_SMTEncoding_Term.mkForall _181_2334))
in ((_181_2335), (Some ("equality for proxy")), (Some ((Prims.strcat "equality_tok_" ddtok)))))
in FStar_SMTEncoding_Term.Assume (_181_2336))
in (let _181_2343 = (let _181_2342 = (let _181_2341 = (let _181_2340 = (let _181_2339 = (let _181_2338 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) vars')
in (let _181_2337 = (FStar_SMTEncoding_Term.mkImp ((guard'), (ty_pred')))
in ((((ty_pred')::[])::[]), (_181_2338), (_181_2337))))
in (FStar_SMTEncoding_Term.mkForall _181_2339))
in ((_181_2340), (Some ("data constructor typing intro")), (Some ((Prims.strcat "data_typing_intro_" ddtok)))))
in FStar_SMTEncoding_Term.Assume (_181_2341))
in (_181_2342)::[])
in (_181_2344)::_181_2343))
in (FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("typing for data constructor proxy")), (Some ((Prims.strcat "typing_tok_" ddtok))))))::_181_2345)
in (FStar_List.append _181_2346 elim))
in (FStar_List.append decls_pred _181_2347))
in (FStar_List.append decls_formals _181_2348))
in (FStar_List.append proxy_fresh _181_2349))
in (FStar_List.append _181_2351 _181_2350)))
in (FStar_List.append decls3 _181_2352))
in (FStar_List.append decls2 _181_2353))
in (FStar_List.append binder_decls _181_2354))
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
and encode_signature : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _87_3099 se -> (match (_87_3099) with
| (g, env) -> begin
(

let _87_3103 = (encode_sigelt env se)
in (match (_87_3103) with
| (g', env) -> begin
(((FStar_List.append g g')), (env))
end))
end)) (([]), (env)))))


let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env bindings -> (

let encode_binding = (fun b _87_3111 -> (match (_87_3111) with
| (i, decls, env) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (_87_3113) -> begin
(((i + (Prims.parse_int "1"))), ([]), (env))
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (

let _87_3118 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _181_2369 = (FStar_Syntax_Print.bv_to_string x)
in (let _181_2368 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _181_2367 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" _181_2369 _181_2368 _181_2367))))
end else begin
()
end
in (

let _87_3122 = (encode_term t1 env)
in (match (_87_3122) with
| (t, decls') -> begin
(

let _87_3126 = (let _181_2374 = (let _181_2373 = (let _181_2372 = (FStar_Util.digest_of_string t.FStar_SMTEncoding_Term.hash)
in (let _181_2371 = (let _181_2370 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _181_2370))
in (Prims.strcat _181_2372 _181_2371)))
in (Prims.strcat "x_" _181_2373))
in (new_term_constant_from_string env x _181_2374))
in (match (_87_3126) with
| (xxsym, xx, env') -> begin
(

let t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel None xx t)
in (

let caption = if (FStar_Options.log_queries ()) then begin
(let _181_2378 = (let _181_2377 = (FStar_Syntax_Print.bv_to_string x)
in (let _181_2376 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _181_2375 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _181_2377 _181_2376 _181_2375))))
in Some (_181_2378))
end else begin
None
end
in (

let ax = (

let a_name = Some ((Prims.strcat "binder_" xxsym))
in FStar_SMTEncoding_Term.Assume (((t), (a_name), (a_name))))
in (

let g = (FStar_List.append ((FStar_SMTEncoding_Term.DeclFun (((xxsym), ([]), (FStar_SMTEncoding_Term.Term_sort), (caption))))::[]) (FStar_List.append decls' ((ax)::[])))
in (((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))))))
end))
end))))
end
| FStar_TypeChecker_Env.Binding_lid (x, (_87_3134, t)) -> begin
(

let t_norm = (whnf env t)
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant None)
in (

let _87_3143 = (encode_free_var env fv t t_norm [])
in (match (_87_3143) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))))
end
| (FStar_TypeChecker_Env.Binding_sig_inst (_, se, _)) | (FStar_TypeChecker_Env.Binding_sig (_, se)) -> begin
(

let _87_3157 = (encode_sigelt env se)
in (match (_87_3157) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))
end)
end))
in (

let _87_3162 = (FStar_List.fold_right encode_binding bindings (((Prims.parse_int "0")), ([]), (env)))
in (match (_87_3162) with
| (_87_3159, decls, env) -> begin
((decls), (env))
end))))


let encode_labels = (fun labs -> (

let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _87_3169 -> (match (_87_3169) with
| (l, _87_3166, _87_3168) -> begin
FStar_SMTEncoding_Term.DeclFun ((((Prims.fst l)), ([]), (FStar_SMTEncoding_Term.Bool_sort), (None)))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _87_3176 -> (match (_87_3176) with
| (l, _87_3173, _87_3175) -> begin
(let _181_2386 = (FStar_All.pipe_left (fun _181_2382 -> FStar_SMTEncoding_Term.Echo (_181_2382)) (Prims.fst l))
in (let _181_2385 = (let _181_2384 = (let _181_2383 = (FStar_SMTEncoding_Term.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (_181_2383))
in (_181_2384)::[])
in (_181_2386)::_181_2385))
end))))
in ((prefix), (suffix)))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (let _181_2391 = (let _181_2390 = (let _181_2389 = (FStar_Util.smap_create (Prims.parse_int "100"))
in {bindings = []; depth = (Prims.parse_int "0"); tcenv = tcenv; warn = true; cache = _181_2389; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_181_2390)::[])
in (FStar_ST.op_Colon_Equals last_env _181_2391)))


let get_env : FStar_TypeChecker_Env.env  ->  env_t = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "No env; call init first!")
end
| (e)::_87_3182 -> begin
(

let _87_3185 = e
in {bindings = _87_3185.bindings; depth = _87_3185.depth; tcenv = tcenv; warn = _87_3185.warn; cache = _87_3185.cache; nolabels = _87_3185.nolabels; use_zfuel_name = _87_3185.use_zfuel_name; encode_non_total_function_typ = _87_3185.encode_non_total_function_typ})
end))


let set_env : env_t  ->  Prims.unit = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| (_87_3191)::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))


let push_env : Prims.unit  ->  Prims.unit = (fun _87_3193 -> (match (()) with
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

let _87_3199 = hd
in {bindings = _87_3199.bindings; depth = _87_3199.depth; tcenv = _87_3199.tcenv; warn = _87_3199.warn; cache = refs; nolabels = _87_3199.nolabels; use_zfuel_name = _87_3199.use_zfuel_name; encode_non_total_function_typ = _87_3199.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))


let pop_env : Prims.unit  ->  Prims.unit = (fun _87_3202 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Popping an empty stack")
end
| (_87_3206)::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))


let mark_env : Prims.unit  ->  Prims.unit = (fun _87_3208 -> (match (()) with
| () -> begin
(push_env ())
end))


let reset_mark_env : Prims.unit  ->  Prims.unit = (fun _87_3209 -> (match (()) with
| () -> begin
(pop_env ())
end))


let commit_mark_env : Prims.unit  ->  Prims.unit = (fun _87_3210 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| (hd)::(_87_3213)::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _87_3218 -> begin
(FStar_All.failwith "Impossible")
end)
end))


let init : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (

let _87_3220 = (init_env tcenv)
in (

let _87_3222 = (FStar_SMTEncoding_Z3.init ())
in (FStar_SMTEncoding_Z3.giveZ3 ((FStar_SMTEncoding_Term.DefPrelude)::[])))))


let push : Prims.string  ->  Prims.unit = (fun msg -> (

let _87_3225 = (push_env ())
in (

let _87_3227 = (varops.push ())
in (FStar_SMTEncoding_Z3.push msg))))


let pop : Prims.string  ->  Prims.unit = (fun msg -> (

let _87_3230 = (let _181_2412 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _181_2412))
in (

let _87_3232 = (varops.pop ())
in (FStar_SMTEncoding_Z3.pop msg))))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _87_3235 = (mark_env ())
in (

let _87_3237 = (varops.mark ())
in (FStar_SMTEncoding_Z3.mark msg))))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _87_3240 = (reset_mark_env ())
in (

let _87_3242 = (varops.reset_mark ())
in (FStar_SMTEncoding_Z3.reset_mark msg))))


let commit_mark = (fun msg -> (

let _87_3245 = (commit_mark_env ())
in (

let _87_3247 = (varops.commit_mark ())
in (FStar_SMTEncoding_Z3.commit_mark msg))))


let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (

let caption = (fun decls -> if (FStar_Options.log_queries ()) then begin
(let _181_2428 = (let _181_2427 = (let _181_2426 = (let _181_2425 = (let _181_2424 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _181_2424 (FStar_List.map FStar_Syntax_Print.lid_to_string)))
in (FStar_All.pipe_right _181_2425 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " _181_2426))
in FStar_SMTEncoding_Term.Caption (_181_2427))
in (_181_2428)::decls)
end else begin
decls
end)
in (

let env = (get_env tcenv)
in (

let _87_3256 = (encode_sigelt env se)
in (match (_87_3256) with
| (decls, env) -> begin
(

let _87_3257 = (set_env env)
in (let _181_2429 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 _181_2429)))
end)))))


let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let _87_3262 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(let _181_2434 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name _181_2434))
end else begin
()
end
in (

let env = (get_env tcenv)
in (

let _87_3269 = (encode_signature (

let _87_3265 = env
in {bindings = _87_3265.bindings; depth = _87_3265.depth; tcenv = _87_3265.tcenv; warn = false; cache = _87_3265.cache; nolabels = _87_3265.nolabels; use_zfuel_name = _87_3265.use_zfuel_name; encode_non_total_function_typ = _87_3265.encode_non_total_function_typ}) modul.FStar_Syntax_Syntax.exports)
in (match (_87_3269) with
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

let _87_3275 = (set_env (

let _87_3273 = env
in {bindings = _87_3273.bindings; depth = _87_3273.depth; tcenv = _87_3273.tcenv; warn = true; cache = _87_3273.cache; nolabels = _87_3273.nolabels; use_zfuel_name = _87_3273.use_zfuel_name; encode_non_total_function_typ = _87_3273.encode_non_total_function_typ}))
in (

let _87_3277 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end else begin
()
end
in (

let decls = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls)))))
end))))))


let encode_query : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_ErrorReporting.label Prims.list * FStar_SMTEncoding_Term.decl * FStar_SMTEncoding_Term.decl Prims.list) = (fun use_env_msg tcenv q -> (

let _87_3283 = (let _181_2452 = (let _181_2451 = (FStar_TypeChecker_Env.current_module tcenv)
in _181_2451.FStar_Ident.str)
in (FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name _181_2452))
in (

let env = (get_env tcenv)
in (

let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (

let _87_3308 = (

let rec aux = (fun bindings -> (match (bindings) with
| (FStar_TypeChecker_Env.Binding_var (x))::rest -> begin
(

let _87_3297 = (aux rest)
in (match (_87_3297) with
| (out, rest) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (let _181_2458 = (let _181_2457 = (FStar_Syntax_Syntax.mk_binder (

let _87_3299 = x
in {FStar_Syntax_Syntax.ppname = _87_3299.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _87_3299.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_181_2457)::out)
in ((_181_2458), (rest))))
end))
end
| _87_3302 -> begin
(([]), (bindings))
end))
in (

let _87_3305 = (aux bindings)
in (match (_87_3305) with
| (closing, bindings) -> begin
(let _181_2459 = (FStar_Syntax_Util.close_forall (FStar_List.rev closing) q)
in ((_181_2459), (bindings)))
end)))
in (match (_87_3308) with
| (q, bindings) -> begin
(

let _87_3317 = (let _181_2461 = (FStar_List.filter (fun _87_24 -> (match (_87_24) with
| FStar_TypeChecker_Env.Binding_sig (_87_3311) -> begin
false
end
| _87_3314 -> begin
true
end)) bindings)
in (encode_env_bindings env _181_2461))
in (match (_87_3317) with
| (env_decls, env) -> begin
(

let _87_3318 = if (((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTQuery")))) then begin
(let _181_2462 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" _181_2462))
end else begin
()
end
in (

let _87_3322 = (encode_formula q env)
in (match (_87_3322) with
| (phi, qdecls) -> begin
(

let _87_3327 = (let _181_2463 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg _181_2463 phi))
in (match (_87_3327) with
| (phi, labels, _87_3326) -> begin
(

let _87_3330 = (encode_labels labels)
in (match (_87_3330) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append env_decls (FStar_List.append label_prefix qdecls))
in (

let qry = (let _181_2467 = (let _181_2466 = (FStar_SMTEncoding_Term.mkNot phi)
in (let _181_2465 = (let _181_2464 = (varops.mk_unique "@query")
in Some (_181_2464))
in ((_181_2466), (Some ("query")), (_181_2465))))
in FStar_SMTEncoding_Term.Assume (_181_2467))
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

let _87_3337 = (push "query")
in (

let _87_3342 = (encode_formula q env)
in (match (_87_3342) with
| (f, _87_3341) -> begin
(

let _87_3343 = (pop "query")
in (match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _87_3347) -> begin
true
end
| _87_3351 -> begin
false
end))
end)))))




