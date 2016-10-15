
open Prims

let add_fuel = (fun x tl -> if (FStar_Options.unthrottle_inductives ()) then begin
tl
end else begin
(x)::tl
end)


let withenv = (fun c _88_30 -> (match (_88_30) with
| (a, b) -> begin
((a), (b), (c))
end))


let vargs = (fun args -> (FStar_List.filter (fun _88_1 -> (match (_88_1) with
| (FStar_Util.Inl (_88_34), _88_37) -> begin
false
end
| _88_40 -> begin
true
end)) args))


let subst_lcomp_opt = (fun s l -> (match (l) with
| Some (FStar_Util.Inl (l)) -> begin
(let _183_12 = (let _183_11 = (let _183_10 = (let _183_9 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp s _183_9))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _183_10))
in FStar_Util.Inl (_183_11))
in Some (_183_12))
end
| _88_47 -> begin
l
end))


let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s '\'' '_'))


let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun lid a -> (

let a = (

let _88_51 = a
in (let _183_19 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _183_19; FStar_Syntax_Syntax.index = _88_51.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _88_51.FStar_Syntax_Syntax.sort}))
in (let _183_20 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str a.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (FStar_All.pipe_left escape _183_20))))


let primitive_projector_by_pos : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (

let fail = (fun _88_58 -> (match (()) with
| () -> begin
(let _183_30 = (let _183_29 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" _183_29 lid.FStar_Ident.str))
in (FStar_All.failwith _183_30))
end))
in (

let _88_62 = (FStar_TypeChecker_Env.lookup_datacon env lid)
in (match (_88_62) with
| (_88_60, t) -> begin
(match ((let _183_31 = (FStar_Syntax_Subst.compress t)
in _183_31.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _88_70 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_88_70) with
| (binders, _88_69) -> begin
if ((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(

let b = (FStar_List.nth binders i)
in (mk_term_projector_name lid (Prims.fst b)))
end
end))
end
| _88_73 -> begin
(fail ())
end)
end))))


let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (let _183_37 = (let _183_36 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str _183_36))
in (FStar_All.pipe_left escape _183_37)))


let mk_term_projector : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun lid a -> (let _183_43 = (let _183_42 = (mk_term_projector_name lid a)
in ((_183_42), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Util.mkFreeV _183_43)))


let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_SMTEncoding_Term.term = (fun lid i -> (let _183_49 = (let _183_48 = (mk_term_projector_name_by_pos lid i)
in ((_183_48), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Util.mkFreeV _183_49)))


let mk_data_tester = (fun env l x -> (FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x))


type varops_t =
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; mark : Prims.unit  ->  Prims.unit; reset_mark : Prims.unit  ->  Prims.unit; commit_mark : Prims.unit  ->  Prims.unit; new_var : FStar_Ident.ident  ->  Prims.int  ->  Prims.string; new_fvar : FStar_Ident.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_SMTEncoding_Term.term; next_id : Prims.unit  ->  Prims.int; mk_unique : Prims.string  ->  Prims.string}


let is_Mkvarops_t : varops_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkvarops_t"))))


let varops : varops_t = (

let initial_ctr = (Prims.parse_int "100")
in (

let ctr = (FStar_Util.mk_ref initial_ctr)
in (

let new_scope = (fun _88_98 -> (match (()) with
| () -> begin
(let _183_162 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (let _183_161 = (FStar_Util.smap_create (Prims.parse_int "100"))
in ((_183_162), (_183_161))))
end))
in (

let scopes = (let _183_164 = (let _183_163 = (new_scope ())
in (_183_163)::[])
in (FStar_Util.mk_ref _183_164))
in (

let mk_unique = (fun y -> (

let y = (escape y)
in (

let y = (match ((let _183_168 = (FStar_ST.read scopes)
in (FStar_Util.find_map _183_168 (fun _88_106 -> (match (_88_106) with
| (names, _88_105) -> begin
(FStar_Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_88_109) -> begin
(

let _88_111 = (FStar_Util.incr ctr)
in (let _183_171 = (let _183_170 = (let _183_169 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _183_169))
in (Prims.strcat "__" _183_170))
in (Prims.strcat y _183_171)))
end)
in (

let top_scope = (let _183_173 = (let _183_172 = (FStar_ST.read scopes)
in (FStar_List.hd _183_172))
in (FStar_All.pipe_left Prims.fst _183_173))
in (

let _88_115 = (FStar_Util.smap_add top_scope y true)
in y)))))
in (

let new_var = (fun pp rn -> (let _183_180 = (let _183_179 = (let _183_178 = (FStar_Util.string_of_int rn)
in (Prims.strcat "__" _183_178))
in (Prims.strcat pp.FStar_Ident.idText _183_179))
in (FStar_All.pipe_left mk_unique _183_180)))
in (

let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (

let next_id = (fun _88_123 -> (match (()) with
| () -> begin
(

let _88_124 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end))
in (

let fresh = (fun pfx -> (let _183_188 = (let _183_187 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _183_187))
in (FStar_Util.format2 "%s_%s" pfx _183_188)))
in (

let string_const = (fun s -> (match ((let _183_192 = (FStar_ST.read scopes)
in (FStar_Util.find_map _183_192 (fun _88_133 -> (match (_88_133) with
| (_88_131, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))) with
| Some (f) -> begin
f
end
| None -> begin
(

let id = (next_id ())
in (

let f = (let _183_193 = (FStar_SMTEncoding_Util.mk_String_const id)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString _183_193))
in (

let top_scope = (let _183_195 = (let _183_194 = (FStar_ST.read scopes)
in (FStar_List.hd _183_194))
in (FStar_All.pipe_left Prims.snd _183_195))
in (

let _88_140 = (FStar_Util.smap_add top_scope s f)
in f))))
end))
in (

let push = (fun _88_143 -> (match (()) with
| () -> begin
(let _183_200 = (let _183_199 = (new_scope ())
in (let _183_198 = (FStar_ST.read scopes)
in (_183_199)::_183_198))
in (FStar_ST.op_Colon_Equals scopes _183_200))
end))
in (

let pop = (fun _88_145 -> (match (()) with
| () -> begin
(let _183_204 = (let _183_203 = (FStar_ST.read scopes)
in (FStar_List.tl _183_203))
in (FStar_ST.op_Colon_Equals scopes _183_204))
end))
in (

let mark = (fun _88_147 -> (match (()) with
| () -> begin
(push ())
end))
in (

let reset_mark = (fun _88_149 -> (match (()) with
| () -> begin
(pop ())
end))
in (

let commit_mark = (fun _88_151 -> (match (()) with
| () -> begin
(match ((FStar_ST.read scopes)) with
| ((hd1, hd2))::((next1, next2))::tl -> begin
(

let _88_164 = (FStar_Util.smap_fold hd1 (fun key value v -> (FStar_Util.smap_add next1 key value)) ())
in (

let _88_169 = (FStar_Util.smap_fold hd2 (fun key value v -> (FStar_Util.smap_add next2 key value)) ())
in (FStar_ST.op_Colon_Equals scopes ((((next1), (next2)))::tl))))
end
| _88_172 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id; mk_unique = mk_unique})))))))))))))))


let unmangle : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv = (fun x -> (

let _88_174 = x
in (let _183_219 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _183_219; FStar_Syntax_Syntax.index = _88_174.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _88_174.FStar_Syntax_Syntax.sort})))


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
| Binding_var (_88_178) -> begin
_88_178
end))


let ___Binding_fvar____0 = (fun projectee -> (match (projectee) with
| Binding_fvar (_88_181) -> begin
_88_181
end))


let binder_of_eithervar = (fun v -> ((v), (None)))


type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_TypeChecker_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_SMTEncoding_Term.sort Prims.list * FStar_SMTEncoding_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}


let is_Mkenv_t : env_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_t"))))


let print_env : env_t  ->  Prims.string = (fun e -> (let _183_277 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun _88_2 -> (match (_88_2) with
| Binding_var (x, _88_196) -> begin
(FStar_Syntax_Print.bv_to_string x)
end
| Binding_fvar (l, _88_201, _88_203, _88_205) -> begin
(FStar_Syntax_Print.lid_to_string l)
end))))
in (FStar_All.pipe_right _183_277 (FStar_String.concat ", "))))


let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))


let caption_t : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.string Prims.option = (fun env t -> if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _183_287 = (FStar_Syntax_Print.term_to_string t)
in Some (_183_287))
end else begin
None
end)


let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (

let xsym = (varops.fresh x)
in (let _183_292 = (FStar_SMTEncoding_Util.mkFreeV ((xsym), (s)))
in ((xsym), (_183_292)))))


let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (let _183_297 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _183_297))
in (

let y = (FStar_SMTEncoding_Util.mkFreeV ((ysym), (FStar_SMTEncoding_Term.Term_sort)))
in ((ysym), (y), ((

let _88_219 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = (env.depth + (Prims.parse_int "1")); tcenv = _88_219.tcenv; warn = _88_219.warn; cache = _88_219.cache; nolabels = _88_219.nolabels; use_zfuel_name = _88_219.use_zfuel_name; encode_non_total_function_typ = _88_219.encode_non_total_function_typ}))))))


let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let _88_225 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = _88_225.depth; tcenv = _88_225.tcenv; warn = _88_225.warn; cache = _88_225.cache; nolabels = _88_225.nolabels; use_zfuel_name = _88_225.use_zfuel_name; encode_non_total_function_typ = _88_225.encode_non_total_function_typ}))))))


let new_term_constant_from_string : env_t  ->  FStar_Syntax_Syntax.bv  ->  Prims.string  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x str -> (

let ysym = (varops.mk_unique str)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let _88_232 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = _88_232.depth; tcenv = _88_232.tcenv; warn = _88_232.warn; cache = _88_232.cache; nolabels = _88_232.nolabels; use_zfuel_name = _88_232.use_zfuel_name; encode_non_total_function_typ = _88_232.encode_non_total_function_typ}))))))


let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (

let _88_237 = env
in {bindings = (Binding_var (((x), (t))))::env.bindings; depth = _88_237.depth; tcenv = _88_237.tcenv; warn = _88_237.warn; cache = _88_237.cache; nolabels = _88_237.nolabels; use_zfuel_name = _88_237.use_zfuel_name; encode_non_total_function_typ = _88_237.encode_non_total_function_typ}))


let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let aux = (fun a' -> (lookup_binding env (fun _88_3 -> (match (_88_3) with
| Binding_var (b, t) when (FStar_Syntax_Syntax.bv_eq b a') -> begin
Some (((b), (t)))
end
| _88_249 -> begin
None
end))))
in (match ((aux a)) with
| None -> begin
(

let a = (unmangle a)
in (match ((aux a)) with
| None -> begin
(let _183_322 = (let _183_321 = (FStar_Syntax_Print.bv_to_string a)
in (FStar_Util.format1 "Bound term variable not found (after unmangling): %s" _183_321))
in (FStar_All.failwith _183_322))
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
in (let _183_333 = (

let _88_265 = env
in (let _183_332 = (let _183_331 = (let _183_330 = (let _183_329 = (let _183_328 = (FStar_SMTEncoding_Util.mkApp ((ftok), ([])))
in (FStar_All.pipe_left (fun _183_327 -> Some (_183_327)) _183_328))
in ((x), (fname), (_183_329), (None)))
in Binding_fvar (_183_330))
in (_183_331)::env.bindings)
in {bindings = _183_332; depth = _88_265.depth; tcenv = _88_265.tcenv; warn = _88_265.warn; cache = _88_265.cache; nolabels = _88_265.nolabels; use_zfuel_name = _88_265.use_zfuel_name; encode_non_total_function_typ = _88_265.encode_non_total_function_typ}))
in ((fname), (ftok), (_183_333))))))


let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun _88_4 -> (match (_88_4) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some (((t1), (t2), (t3)))
end
| _88_277 -> begin
None
end))))


let contains_name : env_t  ->  Prims.string  ->  Prims.bool = (fun env s -> (let _183_344 = (lookup_binding env (fun _88_5 -> (match (_88_5) with
| Binding_fvar (b, t1, t2, t3) when (b.FStar_Ident.str = s) -> begin
Some (())
end
| _88_288 -> begin
None
end)))
in (FStar_All.pipe_right _183_344 FStar_Option.isSome)))


let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _183_350 = (let _183_349 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" _183_349))
in (FStar_All.failwith _183_350))
end
| Some (s) -> begin
s
end))


let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (

let _88_298 = env
in {bindings = (Binding_fvar (((x), (fname), (ftok), (None))))::env.bindings; depth = _88_298.depth; tcenv = _88_298.tcenv; warn = _88_298.warn; cache = _88_298.cache; nolabels = _88_298.nolabels; use_zfuel_name = _88_298.use_zfuel_name; encode_non_total_function_typ = _88_298.encode_non_total_function_typ}))


let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (

let _88_307 = (lookup_lid env x)
in (match (_88_307) with
| (t1, t2, _88_306) -> begin
(

let t3 = (let _183_367 = (let _183_366 = (let _183_365 = (FStar_SMTEncoding_Util.mkApp (("ZFuel"), ([])))
in (_183_365)::[])
in ((f), (_183_366)))
in (FStar_SMTEncoding_Util.mkApp _183_367))
in (

let _88_309 = env
in {bindings = (Binding_fvar (((x), (t1), (t2), (Some (t3)))))::env.bindings; depth = _88_309.depth; tcenv = _88_309.tcenv; warn = _88_309.warn; cache = _88_309.cache; nolabels = _88_309.nolabels; use_zfuel_name = _88_309.use_zfuel_name; encode_non_total_function_typ = _88_309.encode_non_total_function_typ}))
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
| _88_322 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (_88_326, (fuel)::[]) -> begin
if (let _183_373 = (let _183_372 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right _183_372 Prims.fst))
in (FStar_Util.starts_with _183_373 "fuel")) then begin
(let _183_376 = (let _183_375 = (FStar_SMTEncoding_Util.mkFreeV ((name), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_ApplyTF _183_375 fuel))
in (FStar_All.pipe_left (fun _183_374 -> Some (_183_374)) _183_376))
end else begin
Some (t)
end
end
| _88_332 -> begin
Some (t)
end)
end
| _88_334 -> begin
None
end)
end)
end))


let lookup_free_var = (fun env a -> (match ((try_lookup_free_var env a.FStar_Syntax_Syntax.v)) with
| Some (t) -> begin
t
end
| None -> begin
(let _183_380 = (let _183_379 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _183_379))
in (FStar_All.failwith _183_380))
end))


let lookup_free_var_name = (fun env a -> (

let _88_347 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_88_347) with
| (x, _88_344, _88_346) -> begin
x
end)))


let lookup_free_var_sym = (fun env a -> (

let _88_353 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_88_353) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.freevars = _88_357; FStar_SMTEncoding_Term.rng = _88_355}) when env.use_zfuel_name -> begin
((g), (zf))
end
| _88_365 -> begin
(match (sym) with
| None -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end
| Some (sym) -> begin
(match (sym.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, (fuel)::[]) -> begin
((g), ((fuel)::[]))
end
| _88_375 -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end)
end)
end)
end)))


let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun _88_6 -> (match (_88_6) with
| Binding_fvar (_88_380, nm', tok, _88_384) when (nm = nm') -> begin
tok
end
| _88_388 -> begin
None
end))))


let mkForall_fuel' = (fun n _88_393 -> (match (_88_393) with
| (pats, vars, body) -> begin
(

let fallback = (fun _88_395 -> (match (()) with
| () -> begin
(FStar_SMTEncoding_Util.mkForall ((pats), (vars), (body)))
end))
in if (FStar_Options.unthrottle_inductives ()) then begin
(fallback ())
end else begin
(

let _88_398 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_88_398) with
| (fsym, fterm) -> begin
(

let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Util.mkApp (("HasTypeFuel"), ((fterm)::args)))
end
| _88_408 -> begin
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
(let _183_397 = (add_fuel guards)
in (FStar_SMTEncoding_Util.mk_and_l _183_397))
end
| _88_421 -> begin
(let _183_398 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _183_398 FStar_List.hd))
end)
in (FStar_SMTEncoding_Util.mkImp ((guard), (body'))))
end
| _88_424 -> begin
body
end)
in (

let vars = (((fsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars
in (FStar_SMTEncoding_Util.mkForall ((pats), (vars), (body)))))))
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
(let _183_404 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _183_404 FStar_Option.isNone))
end
| _88_463 -> begin
false
end)))


let head_redex : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (match ((let _183_409 = (FStar_Syntax_Util.un_uinst t)
in _183_409.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_88_467, _88_469, Some (FStar_Util.Inr (l))) -> begin
((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid))
end
| FStar_Syntax_Syntax.Tm_abs (_88_476, _88_478, Some (FStar_Util.Inl (lc))) -> begin
(FStar_Syntax_Util.is_tot_or_gtot_lcomp lc)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(let _183_410 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _183_410 FStar_Option.isSome))
end
| _88_487 -> begin
false
end))


let whnf : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> if (head_normal env t) then begin
t
end else begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
end)


let norm : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t))


let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (let _183_423 = (let _183_421 = (FStar_Syntax_Syntax.null_binder t)
in (_183_421)::[])
in (let _183_422 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Util.abs _183_423 _183_422 None))))


let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(let _183_430 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out _183_430))
end
| s -> begin
(

let _88_499 = ()
in (let _183_431 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Util.mk_ApplyTT out _183_431)))
end)) e)))


let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)))


let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun _88_7 -> (match (_88_7) with
| (FStar_SMTEncoding_Term.Var ("ApplyTT")) | (FStar_SMTEncoding_Term.Var ("ApplyTF")) -> begin
true
end
| _88_509 -> begin
false
end))


let is_eta : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env vars t -> (

let rec aux = (fun t xs -> (match (((t.FStar_SMTEncoding_Term.tm), (xs))) with
| (FStar_SMTEncoding_Term.App (app, (f)::({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.freevars = _88_520; FStar_SMTEncoding_Term.rng = _88_518})::[]), (x)::xs) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), _88_538) -> begin
if (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v)
end
| _88_545 -> begin
false
end)) args vars)) then begin
(tok_of_name env f)
end else begin
None
end
end
| (_88_547, []) -> begin
(

let fvs = (FStar_SMTEncoding_Term.free_variables t)
in if (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (not ((FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)))))) then begin
Some (t)
end else begin
None
end)
end
| _88_553 -> begin
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


let encode_const : FStar_Const.sconst  ->  FStar_SMTEncoding_Term.term = (fun _88_8 -> (match (_88_8) with
| FStar_Const.Const_unit -> begin
FStar_SMTEncoding_Term.mk_Term_unit
end
| FStar_Const.Const_bool (true) -> begin
(FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue)
end
| FStar_Const.Const_bool (false) -> begin
(FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse)
end
| FStar_Const.Const_char (c) -> begin
(let _183_488 = (let _183_487 = (let _183_486 = (let _183_485 = (FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c))
in (FStar_SMTEncoding_Term.boxInt _183_485))
in (_183_486)::[])
in (("FStar.Char.Char"), (_183_487)))
in (FStar_SMTEncoding_Util.mkApp _183_488))
end
| FStar_Const.Const_int (i, None) -> begin
(let _183_489 = (FStar_SMTEncoding_Util.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt _183_489))
end
| FStar_Const.Const_int (i, Some (_88_573)) -> begin
(FStar_All.failwith "Machine integers should be desugared")
end
| FStar_Const.Const_string (bytes, _88_579) -> begin
(let _183_490 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _183_490))
end
| FStar_Const.Const_range (r) -> begin
FStar_SMTEncoding_Term.mk_Range_const
end
| FStar_Const.Const_effect -> begin
FStar_SMTEncoding_Term.mk_Term_type
end
| c -> begin
(let _183_492 = (let _183_491 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" _183_491))
in (FStar_All.failwith _183_492))
end))


let as_function_typ : env_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (

let rec aux = (fun norm t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_88_593) -> begin
t
end
| FStar_Syntax_Syntax.Tm_refine (_88_596) -> begin
(let _183_501 = (FStar_Syntax_Util.unrefine t)
in (aux true _183_501))
end
| _88_599 -> begin
if norm then begin
(let _183_502 = (whnf env t)
in (aux false _183_502))
end else begin
(let _183_505 = (let _183_504 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (let _183_503 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _183_504 _183_503)))
in (FStar_All.failwith _183_505))
end
end)))
in (aux true t0)))


let curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun k -> (

let k = (FStar_Syntax_Subst.compress k)
in (match (k.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| _88_607 -> begin
(let _183_508 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (_183_508)))
end)))


let rec encode_binders : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> (

let _88_611 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _183_556 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" _183_556))
end else begin
()
end
in (

let _88_639 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _88_618 b -> (match (_88_618) with
| (vars, guards, env, decls, names) -> begin
(

let _88_633 = (

let x = (unmangle (Prims.fst b))
in (

let _88_624 = (gen_term_var env x)
in (match (_88_624) with
| (xxsym, xx, env') -> begin
(

let _88_627 = (let _183_559 = (norm env x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt _183_559 env xx))
in (match (_88_627) with
| (guard_x_t, decls') -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (guard_x_t), (env'), (decls'), (x))
end))
end)))
in (match (_88_633) with
| (v, g, env, decls', n) -> begin
(((v)::vars), ((g)::guards), (env), ((FStar_List.append decls decls')), ((n)::names))
end))
end)) (([]), ([]), (env), ([]), ([]))))
in (match (_88_639) with
| (vars, guards, env, decls, names) -> begin
(((FStar_List.rev vars)), ((FStar_List.rev guards)), (env), (decls), ((FStar_List.rev names)))
end))))
and encode_term_pred : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let _88_646 = (encode_term t env)
in (match (_88_646) with
| (t, decls) -> begin
(let _183_564 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t)
in ((_183_564), (decls)))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let _88_653 = (encode_term t env)
in (match (_88_653) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _183_569 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t)
in ((_183_569), (decls)))
end
| Some (f) -> begin
(let _183_570 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t)
in ((_183_570), (decls)))
end)
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let t0 = (FStar_Syntax_Subst.compress t)
in (

let _88_660 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _183_575 = (FStar_Syntax_Print.tag_of_term t)
in (let _183_574 = (FStar_Syntax_Print.tag_of_term t0)
in (let _183_573 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" _183_575 _183_574 _183_573))))
end else begin
()
end
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _183_580 = (let _183_579 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (let _183_578 = (FStar_Syntax_Print.tag_of_term t0)
in (let _183_577 = (FStar_Syntax_Print.term_to_string t0)
in (let _183_576 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _183_579 _183_578 _183_577 _183_576)))))
in (FStar_All.failwith _183_580))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _183_582 = (let _183_581 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" _183_581))
in (FStar_All.failwith _183_582))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, k, _88_671) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_meta (t, _88_676) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t = (lookup_term_var env x)
in ((t), ([])))
end
| FStar_Syntax_Syntax.Tm_fvar (v) -> begin
(let _183_583 = (lookup_free_var env v.FStar_Syntax_Syntax.fv_name)
in ((_183_583), ([])))
end
| FStar_Syntax_Syntax.Tm_type (_88_685) -> begin
((FStar_SMTEncoding_Term.mk_Term_type), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t, _88_689) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(let _183_584 = (encode_const c)
in ((_183_584), ([])))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _88_700 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_88_700) with
| (binders, res) -> begin
if ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res)) then begin
(

let _88_707 = (encode_binders None binders env)
in (match (_88_707) with
| (vars, guards, env', decls, _88_706) -> begin
(

let fsym = (let _183_585 = (varops.fresh "f")
in ((_183_585), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV fsym)
in (

let app = (mk_Apply f vars)
in (

let _88_715 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post (

let _88_711 = env.tcenv
in {FStar_TypeChecker_Env.solver = _88_711.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _88_711.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _88_711.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _88_711.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _88_711.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _88_711.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _88_711.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _88_711.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _88_711.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _88_711.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _88_711.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _88_711.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _88_711.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _88_711.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _88_711.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _88_711.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _88_711.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _88_711.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _88_711.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _88_711.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _88_711.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _88_711.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _88_711.FStar_TypeChecker_Env.qname_and_index}) res)
in (match (_88_715) with
| (pre_opt, res_t) -> begin
(

let _88_718 = (encode_term_pred None res_t env' app)
in (match (_88_718) with
| (res_pred, decls') -> begin
(

let _88_727 = (match (pre_opt) with
| None -> begin
(let _183_586 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((_183_586), ([])))
end
| Some (pre) -> begin
(

let _88_724 = (encode_formula pre env')
in (match (_88_724) with
| (guard, decls0) -> begin
(let _183_587 = (FStar_SMTEncoding_Util.mk_and_l ((guard)::guards))
in ((_183_587), (decls0)))
end))
end)
in (match (_88_727) with
| (guards, guard_decls) -> begin
(

let t_interp = (let _183_589 = (let _183_588 = (FStar_SMTEncoding_Util.mkImp ((guards), (res_pred)))
in ((((app)::[])::[]), (vars), (_183_588)))
in (FStar_SMTEncoding_Util.mkForall _183_589))
in (

let cvars = (let _183_591 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right _183_591 (FStar_List.filter (fun _88_732 -> (match (_88_732) with
| (x, _88_731) -> begin
(x <> (Prims.fst fsym))
end)))))
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), ((fsym)::cvars), (t_interp)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (match ((FStar_Util.smap_try_find env.cache tkey_hash)) with
| Some (t', sorts, _88_739) -> begin
(let _183_594 = (let _183_593 = (let _183_592 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((t'), (_183_592)))
in (FStar_SMTEncoding_Util.mkApp _183_593))
in ((_183_594), ([])))
end
| None -> begin
(

let tsym = (let _183_596 = (let _183_595 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_arrow_" _183_595))
in (varops.mk_unique _183_596))
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let caption = if (FStar_Options.log_queries ()) then begin
(let _183_597 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in Some (_183_597))
end else begin
None
end
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (caption)))
in (

let t = (let _183_599 = (let _183_598 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((tsym), (_183_598)))
in (FStar_SMTEncoding_Util.mkApp _183_599))
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let k_assumption = (

let a_name = Some ((Prims.strcat "kinding_" tsym))
in (let _183_601 = (let _183_600 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((_183_600), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_183_601)))
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t)
in (

let pre_typing = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in (let _183_608 = (let _183_607 = (let _183_606 = (let _183_605 = (let _183_604 = (let _183_603 = (let _183_602 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _183_602))
in ((f_has_t), (_183_603)))
in (FStar_SMTEncoding_Util.mkImp _183_604))
in ((((f_has_t)::[])::[]), ((fsym)::cvars), (_183_605)))
in (mkForall_fuel _183_606))
in ((_183_607), (Some ("pre-typing for functions")), (a_name)))
in FStar_SMTEncoding_Term.Assume (_183_608)))
in (

let t_interp = (

let a_name = Some ((Prims.strcat "interpretation_" tsym))
in (let _183_612 = (let _183_611 = (let _183_610 = (let _183_609 = (FStar_SMTEncoding_Util.mkIff ((f_has_t_z), (t_interp)))
in ((((f_has_t_z)::[])::[]), ((fsym)::cvars), (_183_609)))
in (FStar_SMTEncoding_Util.mkForall _183_610))
in ((_183_611), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_183_612)))
in (

let t_decls = (FStar_List.append ((tdecl)::decls) (FStar_List.append decls' (FStar_List.append guard_decls ((k_assumption)::(pre_typing)::(t_interp)::[]))))
in (

let _88_758 = (FStar_Util.smap_add env.cache tkey_hash ((tsym), (cvar_sorts), (t_decls)))
in ((t), (t_decls)))))))))))))))
end)))))
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

let t = (FStar_SMTEncoding_Util.mkApp ((tsym), ([])))
in (

let t_kinding = (

let a_name = Some ((Prims.strcat "non_total_function_typing_" tsym))
in (let _183_614 = (let _183_613 = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in ((_183_613), (Some ("Typing for non-total arrows")), (a_name)))
in FStar_SMTEncoding_Term.Assume (_183_614)))
in (

let fsym = (("f"), (FStar_SMTEncoding_Term.Term_sort))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV fsym)
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let t_interp = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in (let _183_621 = (let _183_620 = (let _183_619 = (let _183_618 = (let _183_617 = (let _183_616 = (let _183_615 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _183_615))
in ((f_has_t), (_183_616)))
in (FStar_SMTEncoding_Util.mkImp _183_617))
in ((((f_has_t)::[])::[]), ((fsym)::[]), (_183_618)))
in (mkForall_fuel _183_619))
in ((_183_620), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_183_621)))
in ((t), ((tdecl)::(t_kinding)::(t_interp)::[]))))))))))
end
end))
end
| FStar_Syntax_Syntax.Tm_refine (_88_771) -> begin
(

let _88_791 = (match ((FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.tk = _88_778; FStar_Syntax_Syntax.pos = _88_776; FStar_Syntax_Syntax.vars = _88_774} -> begin
(

let _88_786 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) f)
in (match (_88_786) with
| (b, f) -> begin
(let _183_623 = (let _183_622 = (FStar_List.hd b)
in (Prims.fst _183_622))
in ((_183_623), (f)))
end))
end
| _88_788 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_88_791) with
| (x, f) -> begin
(

let _88_794 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (_88_794) with
| (base_t, decls) -> begin
(

let _88_798 = (gen_term_var env x)
in (match (_88_798) with
| (x, xtm, env') -> begin
(

let _88_801 = (encode_formula f env')
in (match (_88_801) with
| (refinement, decls') -> begin
(

let _88_804 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_88_804) with
| (fsym, fterm) -> begin
(

let encoding = (let _183_625 = (let _183_624 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in ((_183_624), (refinement)))
in (FStar_SMTEncoding_Util.mkAnd _183_625))
in (

let cvars = (let _183_627 = (FStar_SMTEncoding_Term.free_variables encoding)
in (FStar_All.pipe_right _183_627 (FStar_List.filter (fun _88_809 -> (match (_88_809) with
| (y, _88_808) -> begin
((y <> x) && (y <> fsym))
end)))))
in (

let xfv = ((x), (FStar_SMTEncoding_Term.Term_sort))
in (

let ffv = ((fsym), (FStar_SMTEncoding_Term.Fuel_sort))
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), ((ffv)::(xfv)::cvars), (encoding)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (match ((FStar_Util.smap_try_find env.cache tkey_hash)) with
| Some (t, _88_817, _88_819) -> begin
(let _183_630 = (let _183_629 = (let _183_628 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((t), (_183_628)))
in (FStar_SMTEncoding_Util.mkApp _183_629))
in ((_183_630), ([])))
end
| None -> begin
(

let tsym = (let _183_632 = (let _183_631 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_refine_" _183_631))
in (varops.mk_unique _183_632))
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let t = (let _183_634 = (let _183_633 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((tsym), (_183_633)))
in (FStar_SMTEncoding_Util.mkApp _183_634))
in (

let x_has_t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let t_haseq_base = (FStar_SMTEncoding_Term.mk_haseq base_t)
in (

let t_haseq_ref = (FStar_SMTEncoding_Term.mk_haseq t)
in (

let t_haseq = (let _183_638 = (let _183_637 = (let _183_636 = (let _183_635 = (FStar_SMTEncoding_Util.mkIff ((t_haseq_ref), (t_haseq_base)))
in ((((t_haseq_ref)::[])::[]), (cvars), (_183_635)))
in (FStar_SMTEncoding_Util.mkForall _183_636))
in ((_183_637), (Some ((Prims.strcat "haseq for " tsym))), (Some ((Prims.strcat "haseq" tsym)))))
in FStar_SMTEncoding_Term.Assume (_183_638))
in (

let t_kinding = (let _183_640 = (let _183_639 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((_183_639), (Some ("refinement kinding")), (Some ((Prims.strcat "refinement_kinding_" tsym)))))
in FStar_SMTEncoding_Term.Assume (_183_640))
in (

let t_interp = (let _183_646 = (let _183_645 = (let _183_642 = (let _183_641 = (FStar_SMTEncoding_Util.mkIff ((x_has_t), (encoding)))
in ((((x_has_t)::[])::[]), ((ffv)::(xfv)::cvars), (_183_641)))
in (FStar_SMTEncoding_Util.mkForall _183_642))
in (let _183_644 = (let _183_643 = (FStar_Syntax_Print.term_to_string t0)
in Some (_183_643))
in ((_183_645), (_183_644), (Some ((Prims.strcat "refinement_interpretation_" tsym))))))
in FStar_SMTEncoding_Term.Assume (_183_646))
in (

let t_decls = (FStar_List.append decls (FStar_List.append decls' ((tdecl)::(t_kinding)::(t_interp)::(t_haseq)::[])))
in (

let _88_835 = (FStar_Util.smap_add env.cache tkey_hash ((tsym), (cvar_sorts), (t_decls)))
in ((t), (t_decls)))))))))))))))
end)))))))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
(

let ttm = (let _183_647 = (FStar_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Util.mk_Term_uvar _183_647))
in (

let _88_844 = (encode_term_pred None k env ttm)
in (match (_88_844) with
| (t_has_k, decls) -> begin
(

let d = (let _183_653 = (let _183_652 = (let _183_651 = (let _183_650 = (let _183_649 = (let _183_648 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _183_648))
in (FStar_Util.format1 "uvar_typing_%s" _183_649))
in (varops.mk_unique _183_650))
in Some (_183_651))
in ((t_has_k), (Some ("Uvar typing")), (_183_652)))
in FStar_SMTEncoding_Term.Assume (_183_653))
in ((ttm), ((FStar_List.append decls ((d)::[])))))
end)))
end
| FStar_Syntax_Syntax.Tm_app (_88_847) -> begin
(

let _88_851 = (FStar_Syntax_Util.head_and_args t0)
in (match (_88_851) with
| (head, args_e) -> begin
(match ((let _183_655 = (let _183_654 = (FStar_Syntax_Subst.compress head)
in _183_654.FStar_Syntax_Syntax.n)
in ((_183_655), (args_e)))) with
| (_88_853, _88_855) when (head_redex env head) -> begin
(let _183_656 = (whnf env t)
in (encode_term _183_656 env))
end
| ((FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), (_)::((v1, _))::((v2, _))::[])) | ((FStar_Syntax_Syntax.Tm_fvar (fv), (_)::((v1, _))::((v2, _))::[])) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
(

let _88_895 = (encode_term v1 env)
in (match (_88_895) with
| (v1, decls1) -> begin
(

let _88_898 = (encode_term v2 env)
in (match (_88_898) with
| (v2, decls2) -> begin
(let _183_657 = (FStar_SMTEncoding_Util.mk_LexCons v1 v2)
in ((_183_657), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), (_88_907)::(_88_904)::_88_902) -> begin
(

let e0 = (let _183_661 = (let _183_660 = (let _183_659 = (let _183_658 = (FStar_List.hd args_e)
in (_183_658)::[])
in ((head), (_183_659)))
in FStar_Syntax_Syntax.Tm_app (_183_660))
in (FStar_Syntax_Syntax.mk _183_661 None head.FStar_Syntax_Syntax.pos))
in (

let e = (let _183_664 = (let _183_663 = (let _183_662 = (FStar_List.tl args_e)
in ((e0), (_183_662)))
in FStar_Syntax_Syntax.Tm_app (_183_663))
in (FStar_Syntax_Syntax.mk _183_664 None t0.FStar_Syntax_Syntax.pos))
in (encode_term e env)))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), ((arg, _88_916))::[]) -> begin
(

let _88_922 = (encode_term arg env)
in (match (_88_922) with
| (tm, decls) -> begin
(let _183_665 = (FStar_SMTEncoding_Util.mkApp (("Reify"), ((tm)::[])))
in ((_183_665), (decls)))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (_88_924)), ((arg, _88_929))::[]) -> begin
(encode_term arg env)
end
| _88_934 -> begin
(

let _88_937 = (encode_args args_e env)
in (match (_88_937) with
| (args, decls) -> begin
(

let encode_partial_app = (fun ht_opt -> (

let _88_942 = (encode_term head env)
in (match (_88_942) with
| (head, decls') -> begin
(

let app_tm = (mk_Apply_args head args)
in (match (ht_opt) with
| None -> begin
((app_tm), ((FStar_List.append decls decls')))
end
| Some (formals, c) -> begin
(

let _88_951 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (_88_951) with
| (formals, rest) -> begin
(

let subst = (FStar_List.map2 (fun _88_955 _88_959 -> (match (((_88_955), (_88_959))) with
| ((bv, _88_954), (a, _88_958)) -> begin
FStar_Syntax_Syntax.NT (((bv), (a)))
end)) formals args_e)
in (

let ty = (let _183_670 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right _183_670 (FStar_Syntax_Subst.subst subst)))
in (

let _88_964 = (encode_term_pred None ty env app_tm)
in (match (_88_964) with
| (has_type, decls'') -> begin
(

let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (

let e_typing = (let _183_677 = (let _183_676 = (FStar_SMTEncoding_Util.mkForall ((((has_type)::[])::[]), (cvars), (has_type)))
in (let _183_675 = (let _183_674 = (let _183_673 = (let _183_672 = (let _183_671 = (FStar_SMTEncoding_Term.hash_of_term app_tm)
in (FStar_Util.digest_of_string _183_671))
in (Prims.strcat "partial_app_typing_" _183_672))
in (varops.mk_unique _183_673))
in Some (_183_674))
in ((_183_676), (Some ("Partial app typing")), (_183_675))))
in FStar_SMTEncoding_Term.Assume (_183_677))
in ((app_tm), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' ((e_typing)::[]))))))))
end))))
end))
end))
end)))
in (

let encode_full_app = (fun fv -> (

let _88_971 = (lookup_free_var_sym env fv)
in (match (_88_971) with
| (fname, fuel_args) -> begin
(

let tm = (FStar_SMTEncoding_Util.mkApp' ((fname), ((FStar_List.append fuel_args args))))
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
(let _183_681 = (let _183_680 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _183_680 Prims.snd))
in Some (_183_681))
end
| FStar_Syntax_Syntax.Tm_ascribed (_88_1003, FStar_Util.Inl (t), _88_1007) -> begin
Some (t)
end
| FStar_Syntax_Syntax.Tm_ascribed (_88_1011, FStar_Util.Inr (c), _88_1015) -> begin
Some ((FStar_Syntax_Util.comp_result c))
end
| _88_1019 -> begin
None
end)
in (match (head_type) with
| None -> begin
(encode_partial_app None)
end
| Some (head_type) -> begin
(

let head_type = (let _183_682 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine _183_682))
in (

let _88_1027 = (curried_arrow_formals_comp head_type)
in (match (_88_1027) with
| (formals, c) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| _88_1043 -> begin
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

let _88_1052 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_88_1052) with
| (bs, body, opening) -> begin
(

let fallback = (fun _88_1054 -> (match (()) with
| () -> begin
(

let f = (varops.fresh "Tm_abs")
in (

let decl = FStar_SMTEncoding_Term.DeclFun (((f), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Imprecise function encoding"))))
in (let _183_685 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in ((_183_685), ((decl)::[])))))
end))
in (

let is_impure = (fun _88_9 -> (match (_88_9) with
| FStar_Util.Inl (lc) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)))
end
| FStar_Util.Inr (eff) -> begin
(let _183_688 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv eff)
in (FStar_All.pipe_right _183_688 Prims.op_Negation))
end))
in (

let codomain_eff = (fun lc -> (match (lc) with
| FStar_Util.Inl (lc) -> begin
(let _183_693 = (let _183_691 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening _183_691))
in (FStar_All.pipe_right _183_693 (fun _183_692 -> Some (_183_692))))
end
| FStar_Util.Inr (eff) -> begin
(

let new_uvar = (fun _88_1070 -> (match (()) with
| () -> begin
(let _183_696 = (FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange [] FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _183_696 Prims.fst))
end))
in if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid) then begin
(let _183_699 = (let _183_697 = (new_uvar ())
in (FStar_Syntax_Syntax.mk_Total _183_697))
in (FStar_All.pipe_right _183_699 (fun _183_698 -> Some (_183_698))))
end else begin
if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid) then begin
(let _183_702 = (let _183_700 = (new_uvar ())
in (FStar_Syntax_Syntax.mk_GTotal _183_700))
in (FStar_All.pipe_right _183_702 (fun _183_701 -> Some (_183_701))))
end else begin
None
end
end)
end))
in (match (lopt) with
| None -> begin
(

let _88_1072 = (let _183_704 = (let _183_703 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s" _183_703))
in (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos _183_704))
in (fallback ()))
end
| Some (lc) -> begin
if (is_impure lc) then begin
(fallback ())
end else begin
(

let _88_1082 = (encode_binders None bs env)
in (match (_88_1082) with
| (vars, guards, envbody, decls, _88_1081) -> begin
(

let _88_1085 = (encode_term body envbody)
in (match (_88_1085) with
| (body, decls') -> begin
(

let key_body = (let _183_708 = (let _183_707 = (let _183_706 = (let _183_705 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((_183_705), (body)))
in (FStar_SMTEncoding_Util.mkImp _183_706))
in (([]), (vars), (_183_707)))
in (FStar_SMTEncoding_Util.mkForall _183_708))
in (

let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), (cvars), (key_body)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (match ((FStar_Util.smap_try_find env.cache tkey_hash)) with
| Some (t, _88_1092, _88_1094) -> begin
(let _183_711 = (let _183_710 = (let _183_709 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((t), (_183_709)))
in (FStar_SMTEncoding_Util.mkApp _183_710))
in ((_183_711), ([])))
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

let fsym = (let _183_713 = (let _183_712 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_abs_" _183_712))
in (varops.mk_unique _183_713))
in (

let fdecl = FStar_SMTEncoding_Term.DeclFun (((fsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let f = (let _183_715 = (let _183_714 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((fsym), (_183_714)))
in (FStar_SMTEncoding_Util.mkApp _183_715))
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

let _88_1112 = (encode_term_pred None tfun env f)
in (match (_88_1112) with
| (f_has_t, decls'') -> begin
(

let a_name = Some ((Prims.strcat "typing_" fsym))
in (let _183_719 = (let _183_718 = (let _183_717 = (let _183_716 = (FStar_SMTEncoding_Util.mkForall ((((f)::[])::[]), (cvars), (f_has_t)))
in ((_183_716), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_183_717))
in (_183_718)::[])
in (FStar_List.append decls'' _183_719)))
end)))
end)
in (

let interp_f = (

let a_name = Some ((Prims.strcat "interpretation_" fsym))
in (let _183_723 = (let _183_722 = (let _183_721 = (let _183_720 = (FStar_SMTEncoding_Util.mkEq ((app), (body)))
in ((((app)::[])::[]), ((FStar_List.append vars cvars)), (_183_720)))
in (FStar_SMTEncoding_Util.mkForall _183_721))
in ((_183_722), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_183_723)))
in (

let f_decls = (FStar_List.append decls (FStar_List.append decls' (FStar_List.append ((fdecl)::typing_f) ((interp_f)::[]))))
in (

let _88_1118 = (FStar_Util.smap_add env.cache tkey_hash ((fsym), (cvar_sorts), (f_decls)))
in ((f), (f_decls)))))))))))
end)
end)))))
end))
end))
end
end))))
end))
end
| FStar_Syntax_Syntax.Tm_let ((_88_1121, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_88_1133); FStar_Syntax_Syntax.lbunivs = _88_1131; FStar_Syntax_Syntax.lbtyp = _88_1129; FStar_Syntax_Syntax.lbeff = _88_1127; FStar_Syntax_Syntax.lbdef = _88_1125})::_88_1123), _88_1139) -> begin
(FStar_All.failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _88_1148; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _88_1145; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (_88_1158) -> begin
(

let _88_1160 = (FStar_TypeChecker_Errors.diag t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (

let e = (varops.fresh "let-rec")
in (

let decl_e = FStar_SMTEncoding_Term.DeclFun (((e), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (let _183_724 = (FStar_SMTEncoding_Util.mkFreeV ((e), (FStar_SMTEncoding_Term.Term_sort)))
in ((_183_724), ((decl_e)::[]))))))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end))))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (

let _88_1176 = (encode_term e1 env)
in (match (_88_1176) with
| (ee1, decls1) -> begin
(

let _88_1179 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) e2)
in (match (_88_1179) with
| (xs, e2) -> begin
(

let _88_1183 = (FStar_List.hd xs)
in (match (_88_1183) with
| (x, _88_1182) -> begin
(

let env' = (push_term_var env x ee1)
in (

let _88_1187 = (encode_body e2 env')
in (match (_88_1187) with
| (ee2, decls2) -> begin
((ee2), ((FStar_List.append decls1 decls2)))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (

let _88_1195 = (encode_term e env)
in (match (_88_1195) with
| (scr, decls) -> begin
(

let _88_1232 = (FStar_List.fold_right (fun b _88_1199 -> (match (_88_1199) with
| (else_case, decls) -> begin
(

let _88_1203 = (FStar_Syntax_Subst.open_branch b)
in (match (_88_1203) with
| (p, w, br) -> begin
(

let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun _88_1207 _88_1210 -> (match (((_88_1207), (_88_1210))) with
| ((env0, pattern), (else_case, decls)) -> begin
(

let guard = (pattern.guard scr)
in (

let projections = (pattern.projections scr)
in (

let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env _88_1216 -> (match (_88_1216) with
| (x, t) -> begin
(push_term_var env x t)
end)) env))
in (

let _88_1226 = (match (w) with
| None -> begin
((guard), ([]))
end
| Some (w) -> begin
(

let _88_1223 = (encode_term w env)
in (match (_88_1223) with
| (w, decls2) -> begin
(let _183_758 = (let _183_757 = (let _183_756 = (let _183_755 = (let _183_754 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue)
in ((w), (_183_754)))
in (FStar_SMTEncoding_Util.mkEq _183_755))
in ((guard), (_183_756)))
in (FStar_SMTEncoding_Util.mkAnd _183_757))
in ((_183_758), (decls2)))
end))
end)
in (match (_88_1226) with
| (guard, decls2) -> begin
(

let _88_1229 = (encode_br br env)
in (match (_88_1229) with
| (br, decls3) -> begin
(let _183_759 = (FStar_SMTEncoding_Util.mkITE ((guard), (br), (else_case)))
in ((_183_759), ((FStar_List.append decls (FStar_List.append decls2 decls3)))))
end))
end)))))
end)) patterns ((else_case), (decls))))
end))
end)) pats ((default_case), (decls)))
in (match (_88_1232) with
| (match_tm, decls) -> begin
((match_tm), (decls))
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _88_1238 -> begin
(let _183_762 = (encode_one_pat env pat)
in (_183_762)::[])
end))
and encode_one_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> (

let _88_1241 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _183_765 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" _183_765))
end else begin
()
end
in (

let _88_1245 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (_88_1245) with
| (vars, pat_term) -> begin
(

let _88_1257 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun _88_1248 v -> (match (_88_1248) with
| (env, vars) -> begin
(

let _88_1254 = (gen_term_var env v)
in (match (_88_1254) with
| (xx, _88_1252, env) -> begin
((env), ((((v), (((xx), (FStar_SMTEncoding_Term.Term_sort)))))::vars))
end))
end)) ((env), ([]))))
in (match (_88_1257) with
| (env, vars) -> begin
(

let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_88_1262) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_dot_term (_)) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _183_773 = (let _183_772 = (encode_const c)
in ((scrutinee), (_183_772)))
in (FStar_SMTEncoding_Util.mkEq _183_773))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let is_f = (mk_data_tester env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _88_1284 -> (match (_88_1284) with
| (arg, _88_1283) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _183_776 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_guard arg _183_776)))
end))))
in (FStar_SMTEncoding_Util.mk_and_l ((is_f)::sub_term_guards))))
end))
in (

let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_88_1291) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _)) | (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_constant (_88_1301) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(let _183_784 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _88_1311 -> (match (_88_1311) with
| (arg, _88_1310) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _183_783 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_projections arg _183_783)))
end))))
in (FStar_All.pipe_right _183_784 FStar_List.flatten))
end))
in (

let pat_term = (fun _88_1314 -> (match (()) with
| () -> begin
(encode_term pat_term env)
end))
in (

let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in ((env), (pattern))))))
end))
end))))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (

let _88_1330 = (FStar_All.pipe_right l (FStar_List.fold_left (fun _88_1320 _88_1324 -> (match (((_88_1320), (_88_1324))) with
| ((tms, decls), (t, _88_1323)) -> begin
(

let _88_1327 = (encode_term t env)
in (match (_88_1327) with
| (t, decls') -> begin
(((t)::tms), ((FStar_List.append decls decls')))
end))
end)) (([]), ([]))))
in (match (_88_1330) with
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

let _88_1340 = (FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern")
in [])
end))
in (

let one_pat = (fun p -> (

let _88_1346 = (let _183_799 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right _183_799 FStar_Syntax_Util.head_and_args))
in (match (_88_1346) with
| (head, args) -> begin
(match ((let _183_801 = (let _183_800 = (FStar_Syntax_Util.un_uinst head)
in _183_800.FStar_Syntax_Syntax.n)
in ((_183_801), (args)))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((_88_1354, _88_1356))::((e, _88_1351))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpat_lid) -> begin
((e), (None))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, _88_1364))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatT_lid) -> begin
((e), (None))
end
| _88_1369 -> begin
(FStar_All.failwith "Unexpected pattern term")
end)
end)))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements p)
in (

let smt_pat_or = (fun t -> (

let _88_1377 = (let _183_806 = (FStar_Syntax_Util.unmeta t)
in (FStar_All.pipe_right _183_806 FStar_Syntax_Util.head_and_args))
in (match (_88_1377) with
| (head, args) -> begin
(match ((let _183_808 = (let _183_807 = (FStar_Syntax_Util.un_uinst head)
in _183_807.FStar_Syntax_Syntax.n)
in ((_183_808), (args)))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, _88_1382))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatOr_lid) -> begin
Some (e)
end
| _88_1387 -> begin
None
end)
end)))
in (match (elts) with
| (t)::[] -> begin
(match ((smt_pat_or t)) with
| Some (e) -> begin
(let _183_811 = (list_elements e)
in (FStar_All.pipe_right _183_811 (FStar_List.map (fun branch -> (let _183_810 = (list_elements branch)
in (FStar_All.pipe_right _183_810 (FStar_List.map one_pat)))))))
end
| _88_1394 -> begin
(let _183_812 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_183_812)::[])
end)
end
| _88_1396 -> begin
(let _183_813 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_183_813)::[])
end))))
in (

let _88_1439 = (match ((let _183_814 = (FStar_Syntax_Subst.compress t)
in _183_814.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _88_1403 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_88_1403) with
| (binders, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = _88_1424; FStar_Syntax_Syntax.effect_name = _88_1422; FStar_Syntax_Syntax.result_typ = _88_1420; FStar_Syntax_Syntax.effect_args = ((pre, _88_1416))::((post, _88_1412))::((pats, _88_1408))::[]; FStar_Syntax_Syntax.flags = _88_1405}) -> begin
(

let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _183_815 = (lemma_pats pats')
in ((binders), (pre), (post), (_183_815))))
end
| _88_1432 -> begin
(FStar_All.failwith "impos")
end)
end))
end
| _88_1434 -> begin
(FStar_All.failwith "Impos")
end)
in (match (_88_1439) with
| (binders, pre, post, patterns) -> begin
(

let _88_1446 = (encode_binders None binders env)
in (match (_88_1446) with
| (vars, guards, env, decls, _88_1445) -> begin
(

let _88_1459 = (let _183_819 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (

let _88_1456 = (let _183_818 = (FStar_All.pipe_right branch (FStar_List.map (fun _88_1451 -> (match (_88_1451) with
| (t, _88_1450) -> begin
(encode_term t (

let _88_1452 = env
in {bindings = _88_1452.bindings; depth = _88_1452.depth; tcenv = _88_1452.tcenv; warn = _88_1452.warn; cache = _88_1452.cache; nolabels = _88_1452.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _88_1452.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _183_818 FStar_List.unzip))
in (match (_88_1456) with
| (pats, decls) -> begin
((pats), (decls))
end)))))
in (FStar_All.pipe_right _183_819 FStar_List.unzip))
in (match (_88_1459) with
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
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _183_822 = (let _183_821 = (FStar_SMTEncoding_Util.mkFreeV l)
in (FStar_SMTEncoding_Util.mk_Precedes _183_821 e))
in (_183_822)::p))))
end
| _88_1469 -> begin
(

let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _183_828 = (FStar_SMTEncoding_Util.mk_Precedes tl e)
in (_183_828)::p))))
end
| ((x, FStar_SMTEncoding_Term.Term_sort))::vars -> begin
(let _183_830 = (let _183_829 = (FStar_SMTEncoding_Util.mkFreeV ((x), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Util.mk_LexCons _183_829 tl))
in (aux _183_830 vars))
end
| _88_1481 -> begin
pats
end))
in (let _183_831 = (FStar_SMTEncoding_Util.mkFreeV (("Prims.LexTop"), (FStar_SMTEncoding_Term.Term_sort)))
in (aux _183_831 vars)))
end)
end)
in (

let env = (

let _88_1483 = env
in {bindings = _88_1483.bindings; depth = _88_1483.depth; tcenv = _88_1483.tcenv; warn = _88_1483.warn; cache = _88_1483.cache; nolabels = true; use_zfuel_name = _88_1483.use_zfuel_name; encode_non_total_function_typ = _88_1483.encode_non_total_function_typ})
in (

let _88_1488 = (let _183_832 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula _183_832 env))
in (match (_88_1488) with
| (pre, decls'') -> begin
(

let _88_1491 = (let _183_833 = (FStar_Syntax_Util.unmeta post)
in (encode_formula _183_833 env))
in (match (_88_1491) with
| (post, decls''') -> begin
(

let decls = (FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') (FStar_List.append decls'' decls''')))
in (let _183_838 = (let _183_837 = (let _183_836 = (let _183_835 = (let _183_834 = (FStar_SMTEncoding_Util.mk_and_l ((pre)::guards))
in ((_183_834), (post)))
in (FStar_SMTEncoding_Util.mkImp _183_835))
in ((pats), (vars), (_183_836)))
in (FStar_SMTEncoding_Util.mkForall _183_837))
in ((_183_838), (decls))))
end))
end)))))
end))
end))
end))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (

let debug = (fun phi -> if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _183_844 = (FStar_Syntax_Print.tag_of_term phi)
in (let _183_843 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print2 "Formula (%s)  %s\n" _183_844 _183_843)))
end else begin
()
end)
in (

let enc = (fun f l -> (

let _88_1507 = (FStar_Util.fold_map (fun decls x -> (

let _88_1504 = (encode_term (Prims.fst x) env)
in (match (_88_1504) with
| (t, decls') -> begin
(((FStar_List.append decls decls')), (t))
end))) [] l)
in (match (_88_1507) with
| (decls, args) -> begin
(let _183_860 = (f args)
in ((_183_860), (decls)))
end)))
in (

let const_op = (fun f _88_1510 -> ((f), ([])))
in (

let un_op = (fun f l -> (let _183_874 = (FStar_List.hd l)
in (FStar_All.pipe_left f _183_874)))
in (

let bin_op = (fun f _88_10 -> (match (_88_10) with
| (t1)::(t2)::[] -> begin
(f ((t1), (t2)))
end
| _88_1521 -> begin
(FStar_All.failwith "Impossible")
end))
in (

let enc_prop_c = (fun f l -> (

let _88_1536 = (FStar_Util.fold_map (fun decls _88_1530 -> (match (_88_1530) with
| (t, _88_1529) -> begin
(

let _88_1533 = (encode_formula t env)
in (match (_88_1533) with
| (phi, decls') -> begin
(((FStar_List.append decls decls')), (phi))
end))
end)) [] l)
in (match (_88_1536) with
| (decls, phis) -> begin
(let _183_899 = (f phis)
in ((_183_899), (decls)))
end)))
in (

let eq_op = (fun _88_11 -> (match (_88_11) with
| ((_)::(e1)::(e2)::[]) | ((_)::(_)::(e1)::(e2)::[]) -> begin
(enc (bin_op FStar_SMTEncoding_Util.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op FStar_SMTEncoding_Util.mkEq) l)
end))
in (

let mk_imp = (fun _88_12 -> (match (_88_12) with
| ((lhs, _88_1557))::((rhs, _88_1553))::[] -> begin
(

let _88_1562 = (encode_formula rhs env)
in (match (_88_1562) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _88_1565) -> begin
((l1), (decls1))
end
| _88_1569 -> begin
(

let _88_1572 = (encode_formula lhs env)
in (match (_88_1572) with
| (l2, decls2) -> begin
(let _183_904 = (FStar_SMTEncoding_Util.mkImp ((l2), (l1)))
in ((_183_904), ((FStar_List.append decls1 decls2))))
end))
end)
end))
end
| _88_1574 -> begin
(FStar_All.failwith "impossible")
end))
in (

let mk_ite = (fun _88_13 -> (match (_88_13) with
| ((guard, _88_1587))::((_then, _88_1583))::((_else, _88_1579))::[] -> begin
(

let _88_1592 = (encode_formula guard env)
in (match (_88_1592) with
| (g, decls1) -> begin
(

let _88_1595 = (encode_formula _then env)
in (match (_88_1595) with
| (t, decls2) -> begin
(

let _88_1598 = (encode_formula _else env)
in (match (_88_1598) with
| (e, decls3) -> begin
(

let res = (FStar_SMTEncoding_Util.mkITE ((g), (t), (e)))
in ((res), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end))
end))
end
| _88_1601 -> begin
(FStar_All.failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (let _183_916 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f _183_916)))
in (

let connectives = (let _183_972 = (let _183_925 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd))
in ((FStar_Syntax_Const.and_lid), (_183_925)))
in (let _183_971 = (let _183_970 = (let _183_931 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr))
in ((FStar_Syntax_Const.or_lid), (_183_931)))
in (let _183_969 = (let _183_968 = (let _183_967 = (let _183_940 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff))
in ((FStar_Syntax_Const.iff_lid), (_183_940)))
in (let _183_966 = (let _183_965 = (let _183_964 = (let _183_949 = (FStar_All.pipe_left enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot))
in ((FStar_Syntax_Const.not_lid), (_183_949)))
in (_183_964)::(((FStar_Syntax_Const.eq2_lid), (eq_op)))::(((FStar_Syntax_Const.eq3_lid), (eq_op)))::(((FStar_Syntax_Const.true_lid), ((const_op FStar_SMTEncoding_Util.mkTrue))))::(((FStar_Syntax_Const.false_lid), ((const_op FStar_SMTEncoding_Util.mkFalse))))::[])
in (((FStar_Syntax_Const.ite_lid), (mk_ite)))::_183_965)
in (_183_967)::_183_966))
in (((FStar_Syntax_Const.imp_lid), (mk_imp)))::_183_968)
in (_183_970)::_183_969))
in (_183_972)::_183_971))
in (

let rec fallback = (fun phi -> (match (phi.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(

let _88_1619 = (encode_formula phi' env)
in (match (_88_1619) with
| (phi, decls) -> begin
(let _183_975 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled (((phi), (msg), (r)))) r)
in ((_183_975), (decls)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (_88_1621) -> begin
(let _183_976 = (FStar_Syntax_Util.unmeta phi)
in (encode_formula _183_976 env))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(

let _88_1629 = (encode_match e pats FStar_SMTEncoding_Util.mkFalse env encode_formula)
in (match (_88_1629) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _88_1636; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _88_1633; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _88_1647 = (encode_let x t1 e1 e2 env encode_formula)
in (match (_88_1647) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let head = (FStar_Syntax_Util.un_uinst head)
in (match (((head.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_88_1664)::((x, _88_1661))::((t, _88_1657))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.has_type_lid) -> begin
(

let _88_1669 = (encode_term x env)
in (match (_88_1669) with
| (x, decls) -> begin
(

let _88_1672 = (encode_term t env)
in (match (_88_1672) with
| (t, decls') -> begin
(let _183_977 = (FStar_SMTEncoding_Term.mk_HasType x t)
in ((_183_977), ((FStar_List.append decls decls'))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((r, _88_1685))::((msg, _88_1681))::((phi, _88_1677))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.labeled_lid) -> begin
(match ((let _183_981 = (let _183_978 = (FStar_Syntax_Subst.compress r)
in _183_978.FStar_Syntax_Syntax.n)
in (let _183_980 = (let _183_979 = (FStar_Syntax_Subst.compress msg)
in _183_979.FStar_Syntax_Syntax.n)
in ((_183_981), (_183_980))))) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, _88_1694))) -> begin
(

let phi = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((phi), (FStar_Syntax_Syntax.Meta_labeled ((((FStar_Util.string_of_unicode s)), (r), (false))))))) None r)
in (fallback phi))
end
| _88_1701 -> begin
(fallback phi)
end)
end
| _88_1703 when (head_redex env head) -> begin
(let _183_982 = (whnf env phi)
in (encode_formula _183_982 env))
end
| _88_1705 -> begin
(

let _88_1708 = (encode_term phi env)
in (match (_88_1708) with
| (tt, decls) -> begin
(let _183_983 = (FStar_SMTEncoding_Term.mk_Valid tt)
in ((_183_983), (decls)))
end))
end))
end
| _88_1710 -> begin
(

let _88_1713 = (encode_term phi env)
in (match (_88_1713) with
| (tt, decls) -> begin
(let _183_984 = (FStar_SMTEncoding_Term.mk_Valid tt)
in ((_183_984), (decls)))
end))
end))
in (

let encode_q_body = (fun env bs ps body -> (

let _88_1725 = (encode_binders None bs env)
in (match (_88_1725) with
| (vars, guards, env, decls, _88_1724) -> begin
(

let _88_1738 = (let _183_996 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let _88_1735 = (let _183_995 = (FStar_All.pipe_right p (FStar_List.map (fun _88_1730 -> (match (_88_1730) with
| (t, _88_1729) -> begin
(encode_term t (

let _88_1731 = env
in {bindings = _88_1731.bindings; depth = _88_1731.depth; tcenv = _88_1731.tcenv; warn = _88_1731.warn; cache = _88_1731.cache; nolabels = _88_1731.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _88_1731.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _183_995 FStar_List.unzip))
in (match (_88_1735) with
| (p, decls) -> begin
((p), ((FStar_List.flatten decls)))
end)))))
in (FStar_All.pipe_right _183_996 FStar_List.unzip))
in (match (_88_1738) with
| (pats, decls') -> begin
(

let _88_1741 = (encode_formula body env)
in (match (_88_1741) with
| (body, decls'') -> begin
(

let guards = (match (pats) with
| (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (gf), (p)::[]); FStar_SMTEncoding_Term.freevars = _88_1745; FStar_SMTEncoding_Term.rng = _88_1743})::[])::[] when ((FStar_Ident.text_of_lid FStar_Syntax_Const.guard_free) = gf) -> begin
[]
end
| _88_1756 -> begin
guards
end)
in (let _183_997 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((vars), (pats), (_183_997), (body), ((FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') decls''))))))
end))
end))
end)))
in (

let _88_1758 = (debug phi)
in (

let phi = (FStar_Syntax_Util.unascribe phi)
in (

let check_pattern_vars = (fun vars pats -> (

let pats = (FStar_All.pipe_right pats (FStar_List.map (fun _88_1767 -> (match (_88_1767) with
| (x, _88_1766) -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x)
end))))
in (match (pats) with
| [] -> begin
()
end
| (hd)::tl -> begin
(

let pat_vars = (let _183_1006 = (FStar_Syntax_Free.names hd)
in (FStar_List.fold_left (fun out x -> (let _183_1005 = (FStar_Syntax_Free.names x)
in (FStar_Util.set_union out _183_1005))) _183_1006 tl))
in (match ((FStar_All.pipe_right vars (FStar_Util.find_opt (fun _88_1779 -> (match (_88_1779) with
| (b, _88_1778) -> begin
(not ((FStar_Util.set_mem b pat_vars)))
end))))) with
| None -> begin
()
end
| Some (x, _88_1783) -> begin
(

let pos = (FStar_List.fold_left (fun out t -> (FStar_Range.union_ranges out t.FStar_Syntax_Syntax.pos)) hd.FStar_Syntax_Syntax.pos tl)
in (let _183_1011 = (let _183_1010 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variable: %s" _183_1010))
in (FStar_TypeChecker_Errors.warn pos _183_1011)))
end))
end)))
in (match ((FStar_Syntax_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _88_1798 -> (match (_88_1798) with
| (l, _88_1797) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_88_1801, f) -> begin
(f arms)
end)
end
| Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
(

let _88_1811 = (FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)))
in (

let _88_1818 = (encode_q_body env vars pats body)
in (match (_88_1818) with
| (vars, pats, guard, body, decls) -> begin
(

let tm = (let _183_1029 = (let _183_1028 = (FStar_SMTEncoding_Util.mkImp ((guard), (body)))
in ((pats), (vars), (_183_1028)))
in (FStar_SMTEncoding_Util.mkForall _183_1029))
in ((tm), (decls)))
end)))
end
| Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
(

let _88_1826 = (FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)))
in (

let _88_1833 = (encode_q_body env vars pats body)
in (match (_88_1833) with
| (vars, pats, guard, body, decls) -> begin
(let _183_1032 = (let _183_1031 = (let _183_1030 = (FStar_SMTEncoding_Util.mkAnd ((guard), (body)))
in ((pats), (vars), (_183_1030)))
in (FStar_SMTEncoding_Util.mkExists _183_1031))
in ((_183_1032), (decls)))
end)))
end))))))))))))))))))


type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list); is : FStar_Ident.lident  ->  Prims.bool}


let is_Mkprims_t : prims_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkprims_t"))))


let prims : prims_t = (

let _88_1839 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (_88_1839) with
| (asym, a) -> begin
(

let _88_1842 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_88_1842) with
| (xsym, x) -> begin
(

let _88_1845 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (_88_1845) with
| (ysym, y) -> begin
(

let deffun = (fun vars body x -> (FStar_SMTEncoding_Term.DefineFun (((x), (vars), (FStar_SMTEncoding_Term.Term_sort), (body), (None))))::[])
in (

let quant = (fun vars body x -> (

let xname_decl = (let _183_1075 = (let _183_1074 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in ((x), (_183_1074), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (_183_1075))
in (

let xtok = (Prims.strcat x "@tok")
in (

let xtok_decl = FStar_SMTEncoding_Term.DeclFun (((xtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let xapp = (let _183_1077 = (let _183_1076 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((x), (_183_1076)))
in (FStar_SMTEncoding_Util.mkApp _183_1077))
in (

let xtok = (FStar_SMTEncoding_Util.mkApp ((xtok), ([])))
in (

let xtok_app = (mk_Apply xtok vars)
in (let _183_1091 = (let _183_1090 = (let _183_1089 = (let _183_1088 = (let _183_1081 = (let _183_1080 = (let _183_1079 = (let _183_1078 = (FStar_SMTEncoding_Util.mkEq ((xapp), (body)))
in ((((xapp)::[])::[]), (vars), (_183_1078)))
in (FStar_SMTEncoding_Util.mkForall _183_1079))
in ((_183_1080), (None), (Some ((Prims.strcat "primitive_" x)))))
in FStar_SMTEncoding_Term.Assume (_183_1081))
in (let _183_1087 = (let _183_1086 = (let _183_1085 = (let _183_1084 = (let _183_1083 = (let _183_1082 = (FStar_SMTEncoding_Util.mkEq ((xtok_app), (xapp)))
in ((((xtok_app)::[])::[]), (vars), (_183_1082)))
in (FStar_SMTEncoding_Util.mkForall _183_1083))
in ((_183_1084), (Some ("Name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" x)))))
in FStar_SMTEncoding_Term.Assume (_183_1085))
in (_183_1086)::[])
in (_183_1088)::_183_1087))
in (xtok_decl)::_183_1089)
in (xname_decl)::_183_1090)
in ((xtok), (_183_1091))))))))))
in (

let axy = (((asym), (FStar_SMTEncoding_Term.Term_sort)))::(((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let xy = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let qx = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let prims = (let _183_1251 = (let _183_1100 = (let _183_1099 = (let _183_1098 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _183_1098))
in (quant axy _183_1099))
in ((FStar_Syntax_Const.op_Eq), (_183_1100)))
in (let _183_1250 = (let _183_1249 = (let _183_1107 = (let _183_1106 = (let _183_1105 = (let _183_1104 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_SMTEncoding_Util.mkNot _183_1104))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _183_1105))
in (quant axy _183_1106))
in ((FStar_Syntax_Const.op_notEq), (_183_1107)))
in (let _183_1248 = (let _183_1247 = (let _183_1116 = (let _183_1115 = (let _183_1114 = (let _183_1113 = (let _183_1112 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _183_1111 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_183_1112), (_183_1111))))
in (FStar_SMTEncoding_Util.mkLT _183_1113))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _183_1114))
in (quant xy _183_1115))
in ((FStar_Syntax_Const.op_LT), (_183_1116)))
in (let _183_1246 = (let _183_1245 = (let _183_1125 = (let _183_1124 = (let _183_1123 = (let _183_1122 = (let _183_1121 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _183_1120 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_183_1121), (_183_1120))))
in (FStar_SMTEncoding_Util.mkLTE _183_1122))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _183_1123))
in (quant xy _183_1124))
in ((FStar_Syntax_Const.op_LTE), (_183_1125)))
in (let _183_1244 = (let _183_1243 = (let _183_1134 = (let _183_1133 = (let _183_1132 = (let _183_1131 = (let _183_1130 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _183_1129 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_183_1130), (_183_1129))))
in (FStar_SMTEncoding_Util.mkGT _183_1131))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _183_1132))
in (quant xy _183_1133))
in ((FStar_Syntax_Const.op_GT), (_183_1134)))
in (let _183_1242 = (let _183_1241 = (let _183_1143 = (let _183_1142 = (let _183_1141 = (let _183_1140 = (let _183_1139 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _183_1138 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_183_1139), (_183_1138))))
in (FStar_SMTEncoding_Util.mkGTE _183_1140))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _183_1141))
in (quant xy _183_1142))
in ((FStar_Syntax_Const.op_GTE), (_183_1143)))
in (let _183_1240 = (let _183_1239 = (let _183_1152 = (let _183_1151 = (let _183_1150 = (let _183_1149 = (let _183_1148 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _183_1147 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_183_1148), (_183_1147))))
in (FStar_SMTEncoding_Util.mkSub _183_1149))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _183_1150))
in (quant xy _183_1151))
in ((FStar_Syntax_Const.op_Subtraction), (_183_1152)))
in (let _183_1238 = (let _183_1237 = (let _183_1159 = (let _183_1158 = (let _183_1157 = (let _183_1156 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Util.mkMinus _183_1156))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _183_1157))
in (quant qx _183_1158))
in ((FStar_Syntax_Const.op_Minus), (_183_1159)))
in (let _183_1236 = (let _183_1235 = (let _183_1168 = (let _183_1167 = (let _183_1166 = (let _183_1165 = (let _183_1164 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _183_1163 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_183_1164), (_183_1163))))
in (FStar_SMTEncoding_Util.mkAdd _183_1165))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _183_1166))
in (quant xy _183_1167))
in ((FStar_Syntax_Const.op_Addition), (_183_1168)))
in (let _183_1234 = (let _183_1233 = (let _183_1177 = (let _183_1176 = (let _183_1175 = (let _183_1174 = (let _183_1173 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _183_1172 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_183_1173), (_183_1172))))
in (FStar_SMTEncoding_Util.mkMul _183_1174))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _183_1175))
in (quant xy _183_1176))
in ((FStar_Syntax_Const.op_Multiply), (_183_1177)))
in (let _183_1232 = (let _183_1231 = (let _183_1186 = (let _183_1185 = (let _183_1184 = (let _183_1183 = (let _183_1182 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _183_1181 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_183_1182), (_183_1181))))
in (FStar_SMTEncoding_Util.mkDiv _183_1183))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _183_1184))
in (quant xy _183_1185))
in ((FStar_Syntax_Const.op_Division), (_183_1186)))
in (let _183_1230 = (let _183_1229 = (let _183_1195 = (let _183_1194 = (let _183_1193 = (let _183_1192 = (let _183_1191 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _183_1190 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_183_1191), (_183_1190))))
in (FStar_SMTEncoding_Util.mkMod _183_1192))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _183_1193))
in (quant xy _183_1194))
in ((FStar_Syntax_Const.op_Modulus), (_183_1195)))
in (let _183_1228 = (let _183_1227 = (let _183_1204 = (let _183_1203 = (let _183_1202 = (let _183_1201 = (let _183_1200 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _183_1199 = (FStar_SMTEncoding_Term.unboxBool y)
in ((_183_1200), (_183_1199))))
in (FStar_SMTEncoding_Util.mkAnd _183_1201))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _183_1202))
in (quant xy _183_1203))
in ((FStar_Syntax_Const.op_And), (_183_1204)))
in (let _183_1226 = (let _183_1225 = (let _183_1213 = (let _183_1212 = (let _183_1211 = (let _183_1210 = (let _183_1209 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _183_1208 = (FStar_SMTEncoding_Term.unboxBool y)
in ((_183_1209), (_183_1208))))
in (FStar_SMTEncoding_Util.mkOr _183_1210))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _183_1211))
in (quant xy _183_1212))
in ((FStar_Syntax_Const.op_Or), (_183_1213)))
in (let _183_1224 = (let _183_1223 = (let _183_1220 = (let _183_1219 = (let _183_1218 = (let _183_1217 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Util.mkNot _183_1217))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _183_1218))
in (quant qx _183_1219))
in ((FStar_Syntax_Const.op_Negation), (_183_1220)))
in (_183_1223)::[])
in (_183_1225)::_183_1224))
in (_183_1227)::_183_1226))
in (_183_1229)::_183_1228))
in (_183_1231)::_183_1230))
in (_183_1233)::_183_1232))
in (_183_1235)::_183_1234))
in (_183_1237)::_183_1236))
in (_183_1239)::_183_1238))
in (_183_1241)::_183_1240))
in (_183_1243)::_183_1242))
in (_183_1245)::_183_1244))
in (_183_1247)::_183_1246))
in (_183_1249)::_183_1248))
in (_183_1251)::_183_1250))
in (

let mk = (fun l v -> (let _183_1298 = (let _183_1297 = (FStar_All.pipe_right prims (FStar_List.find (fun _88_1869 -> (match (_88_1869) with
| (l', _88_1868) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right _183_1297 (FStar_Option.map (fun _88_1873 -> (match (_88_1873) with
| (_88_1871, b) -> begin
(b v)
end)))))
in (FStar_All.pipe_right _183_1298 FStar_Option.get)))
in (

let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _88_1879 -> (match (_88_1879) with
| (l', _88_1878) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is}))))))))
end))
end))
end))


let pretype_axiom : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun tapp vars -> (

let _88_1885 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_88_1885) with
| (xxsym, xx) -> begin
(

let _88_1888 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_88_1888) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let tapp_hash = (FStar_SMTEncoding_Term.hash_of_term tapp)
in (let _183_1328 = (let _183_1327 = (let _183_1322 = (let _183_1321 = (let _183_1320 = (let _183_1319 = (let _183_1318 = (let _183_1317 = (FStar_SMTEncoding_Util.mkApp (("PreType"), ((xx)::[])))
in ((tapp), (_183_1317)))
in (FStar_SMTEncoding_Util.mkEq _183_1318))
in ((xx_has_type), (_183_1319)))
in (FStar_SMTEncoding_Util.mkImp _183_1320))
in ((((xx_has_type)::[])::[]), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars), (_183_1321)))
in (FStar_SMTEncoding_Util.mkForall _183_1322))
in (let _183_1326 = (let _183_1325 = (let _183_1324 = (let _183_1323 = (FStar_Util.digest_of_string tapp_hash)
in (Prims.strcat "pretyping_" _183_1323))
in (varops.mk_unique _183_1324))
in Some (_183_1325))
in ((_183_1327), (Some ("pretyping")), (_183_1326))))
in FStar_SMTEncoding_Term.Assume (_183_1328))))
end))
end)))


let primitive_type_axioms : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.decl Prims.list = (

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let yy = (("y"), (FStar_SMTEncoding_Term.Term_sort))
in (

let y = (FStar_SMTEncoding_Util.mkFreeV yy)
in (

let mk_unit = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (let _183_1349 = (let _183_1340 = (let _183_1339 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in ((_183_1339), (Some ("unit typing")), (Some ("unit_typing"))))
in FStar_SMTEncoding_Term.Assume (_183_1340))
in (let _183_1348 = (let _183_1347 = (let _183_1346 = (let _183_1345 = (let _183_1344 = (let _183_1343 = (let _183_1342 = (let _183_1341 = (FStar_SMTEncoding_Util.mkEq ((x), (FStar_SMTEncoding_Term.mk_Term_unit)))
in ((typing_pred), (_183_1341)))
in (FStar_SMTEncoding_Util.mkImp _183_1342))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_183_1343)))
in (mkForall_fuel _183_1344))
in ((_183_1345), (Some ("unit inversion")), (Some ("unit_inversion"))))
in FStar_SMTEncoding_Term.Assume (_183_1346))
in (_183_1347)::[])
in (_183_1349)::_183_1348))))
in (

let mk_bool = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Bool_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (let _183_1372 = (let _183_1363 = (let _183_1362 = (let _183_1361 = (let _183_1360 = (let _183_1357 = (let _183_1356 = (FStar_SMTEncoding_Term.boxBool b)
in (_183_1356)::[])
in (_183_1357)::[])
in (let _183_1359 = (let _183_1358 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType _183_1358 tt))
in ((_183_1360), ((bb)::[]), (_183_1359))))
in (FStar_SMTEncoding_Util.mkForall _183_1361))
in ((_183_1362), (Some ("bool typing")), (Some ("bool_typing"))))
in FStar_SMTEncoding_Term.Assume (_183_1363))
in (let _183_1371 = (let _183_1370 = (let _183_1369 = (let _183_1368 = (let _183_1367 = (let _183_1366 = (let _183_1365 = (let _183_1364 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in ((typing_pred), (_183_1364)))
in (FStar_SMTEncoding_Util.mkImp _183_1365))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_183_1366)))
in (mkForall_fuel _183_1367))
in ((_183_1368), (Some ("bool inversion")), (Some ("bool_inversion"))))
in FStar_SMTEncoding_Term.Assume (_183_1369))
in (_183_1370)::[])
in (_183_1372)::_183_1371))))))
in (

let mk_int = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let typing_pred_y = (FStar_SMTEncoding_Term.mk_HasType y tt)
in (

let aa = (("a"), (FStar_SMTEncoding_Term.Int_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Int_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let precedes = (let _183_1386 = (let _183_1385 = (let _183_1384 = (let _183_1383 = (let _183_1382 = (let _183_1381 = (FStar_SMTEncoding_Term.boxInt a)
in (let _183_1380 = (let _183_1379 = (FStar_SMTEncoding_Term.boxInt b)
in (_183_1379)::[])
in (_183_1381)::_183_1380))
in (tt)::_183_1382)
in (tt)::_183_1383)
in (("Prims.Precedes"), (_183_1384)))
in (FStar_SMTEncoding_Util.mkApp _183_1385))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _183_1386))
in (

let precedes_y_x = (let _183_1387 = (FStar_SMTEncoding_Util.mkApp (("Precedes"), ((y)::(x)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _183_1387))
in (let _183_1429 = (let _183_1395 = (let _183_1394 = (let _183_1393 = (let _183_1392 = (let _183_1389 = (let _183_1388 = (FStar_SMTEncoding_Term.boxInt b)
in (_183_1388)::[])
in (_183_1389)::[])
in (let _183_1391 = (let _183_1390 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType _183_1390 tt))
in ((_183_1392), ((bb)::[]), (_183_1391))))
in (FStar_SMTEncoding_Util.mkForall _183_1393))
in ((_183_1394), (Some ("int typing")), (Some ("int_typing"))))
in FStar_SMTEncoding_Term.Assume (_183_1395))
in (let _183_1428 = (let _183_1427 = (let _183_1401 = (let _183_1400 = (let _183_1399 = (let _183_1398 = (let _183_1397 = (let _183_1396 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in ((typing_pred), (_183_1396)))
in (FStar_SMTEncoding_Util.mkImp _183_1397))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_183_1398)))
in (mkForall_fuel _183_1399))
in ((_183_1400), (Some ("int inversion")), (Some ("int_inversion"))))
in FStar_SMTEncoding_Term.Assume (_183_1401))
in (let _183_1426 = (let _183_1425 = (let _183_1424 = (let _183_1423 = (let _183_1422 = (let _183_1421 = (let _183_1420 = (let _183_1419 = (let _183_1418 = (let _183_1417 = (let _183_1416 = (let _183_1415 = (let _183_1404 = (let _183_1403 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _183_1402 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((_183_1403), (_183_1402))))
in (FStar_SMTEncoding_Util.mkGT _183_1404))
in (let _183_1414 = (let _183_1413 = (let _183_1407 = (let _183_1406 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _183_1405 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((_183_1406), (_183_1405))))
in (FStar_SMTEncoding_Util.mkGTE _183_1407))
in (let _183_1412 = (let _183_1411 = (let _183_1410 = (let _183_1409 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _183_1408 = (FStar_SMTEncoding_Term.unboxInt x)
in ((_183_1409), (_183_1408))))
in (FStar_SMTEncoding_Util.mkLT _183_1410))
in (_183_1411)::[])
in (_183_1413)::_183_1412))
in (_183_1415)::_183_1414))
in (typing_pred_y)::_183_1416)
in (typing_pred)::_183_1417)
in (FStar_SMTEncoding_Util.mk_and_l _183_1418))
in ((_183_1419), (precedes_y_x)))
in (FStar_SMTEncoding_Util.mkImp _183_1420))
in ((((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[]), ((xx)::(yy)::[]), (_183_1421)))
in (mkForall_fuel _183_1422))
in ((_183_1423), (Some ("well-founded ordering on nat (alt)")), (Some ("well-founded-ordering-on-nat"))))
in FStar_SMTEncoding_Term.Assume (_183_1424))
in (_183_1425)::[])
in (_183_1427)::_183_1426))
in (_183_1429)::_183_1428)))))))))))
in (

let mk_str = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.String_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (let _183_1452 = (let _183_1443 = (let _183_1442 = (let _183_1441 = (let _183_1440 = (let _183_1437 = (let _183_1436 = (FStar_SMTEncoding_Term.boxString b)
in (_183_1436)::[])
in (_183_1437)::[])
in (let _183_1439 = (let _183_1438 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType _183_1438 tt))
in ((_183_1440), ((bb)::[]), (_183_1439))))
in (FStar_SMTEncoding_Util.mkForall _183_1441))
in ((_183_1442), (Some ("string typing")), (Some ("string_typing"))))
in FStar_SMTEncoding_Term.Assume (_183_1443))
in (let _183_1451 = (let _183_1450 = (let _183_1449 = (let _183_1448 = (let _183_1447 = (let _183_1446 = (let _183_1445 = (let _183_1444 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in ((typing_pred), (_183_1444)))
in (FStar_SMTEncoding_Util.mkImp _183_1445))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_183_1446)))
in (mkForall_fuel _183_1447))
in ((_183_1448), (Some ("string inversion")), (Some ("string_inversion"))))
in FStar_SMTEncoding_Term.Assume (_183_1449))
in (_183_1450)::[])
in (_183_1452)::_183_1451))))))
in (

let mk_ref = (fun env reft_name _88_1928 -> (

let r = (("r"), (FStar_SMTEncoding_Term.Ref_sort))
in (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let refa = (let _183_1461 = (let _183_1460 = (let _183_1459 = (FStar_SMTEncoding_Util.mkFreeV aa)
in (_183_1459)::[])
in ((reft_name), (_183_1460)))
in (FStar_SMTEncoding_Util.mkApp _183_1461))
in (

let refb = (let _183_1464 = (let _183_1463 = (let _183_1462 = (FStar_SMTEncoding_Util.mkFreeV bb)
in (_183_1462)::[])
in ((reft_name), (_183_1463)))
in (FStar_SMTEncoding_Util.mkApp _183_1464))
in (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (

let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (let _183_1483 = (let _183_1470 = (let _183_1469 = (let _183_1468 = (let _183_1467 = (let _183_1466 = (let _183_1465 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in ((typing_pred), (_183_1465)))
in (FStar_SMTEncoding_Util.mkImp _183_1466))
in ((((typing_pred)::[])::[]), ((xx)::(aa)::[]), (_183_1467)))
in (mkForall_fuel _183_1468))
in ((_183_1469), (Some ("ref inversion")), (Some ("ref_inversion"))))
in FStar_SMTEncoding_Term.Assume (_183_1470))
in (let _183_1482 = (let _183_1481 = (let _183_1480 = (let _183_1479 = (let _183_1478 = (let _183_1477 = (let _183_1476 = (let _183_1475 = (FStar_SMTEncoding_Util.mkAnd ((typing_pred), (typing_pred_b)))
in (let _183_1474 = (let _183_1473 = (let _183_1472 = (FStar_SMTEncoding_Util.mkFreeV aa)
in (let _183_1471 = (FStar_SMTEncoding_Util.mkFreeV bb)
in ((_183_1472), (_183_1471))))
in (FStar_SMTEncoding_Util.mkEq _183_1473))
in ((_183_1475), (_183_1474))))
in (FStar_SMTEncoding_Util.mkImp _183_1476))
in ((((typing_pred)::(typing_pred_b)::[])::[]), ((xx)::(aa)::(bb)::[]), (_183_1477)))
in (mkForall_fuel' (Prims.parse_int "2") _183_1478))
in ((_183_1479), (Some ("ref typing is injective")), (Some ("ref_injectivity"))))
in FStar_SMTEncoding_Term.Assume (_183_1480))
in (_183_1481)::[])
in (_183_1483)::_183_1482))))))))))
in (

let mk_true_interp = (fun env nm true_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((true_tm)::[])))
in (FStar_SMTEncoding_Term.Assume (((valid), (Some ("True interpretation")), (Some ("true_interp")))))::[]))
in (

let mk_false_interp = (fun env nm false_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((false_tm)::[])))
in (let _183_1498 = (let _183_1497 = (let _183_1496 = (FStar_SMTEncoding_Util.mkIff ((FStar_SMTEncoding_Util.mkFalse), (valid)))
in ((_183_1496), (Some ("False interpretation")), (Some ("false_interp"))))
in FStar_SMTEncoding_Term.Assume (_183_1497))
in (_183_1498)::[])))
in (

let mk_and_interp = (fun env conj _88_1950 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let valid = (let _183_1507 = (let _183_1506 = (let _183_1505 = (FStar_SMTEncoding_Util.mkApp ((conj), ((a)::(b)::[])))
in (_183_1505)::[])
in (("Valid"), (_183_1506)))
in (FStar_SMTEncoding_Util.mkApp _183_1507))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (let _183_1514 = (let _183_1513 = (let _183_1512 = (let _183_1511 = (let _183_1510 = (let _183_1509 = (let _183_1508 = (FStar_SMTEncoding_Util.mkAnd ((valid_a), (valid_b)))
in ((_183_1508), (valid)))
in (FStar_SMTEncoding_Util.mkIff _183_1509))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_183_1510)))
in (FStar_SMTEncoding_Util.mkForall _183_1511))
in ((_183_1512), (Some ("/\\ interpretation")), (Some ("l_and-interp"))))
in FStar_SMTEncoding_Term.Assume (_183_1513))
in (_183_1514)::[])))))))))
in (

let mk_or_interp = (fun env disj _88_1962 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let valid = (let _183_1523 = (let _183_1522 = (let _183_1521 = (FStar_SMTEncoding_Util.mkApp ((disj), ((a)::(b)::[])))
in (_183_1521)::[])
in (("Valid"), (_183_1522)))
in (FStar_SMTEncoding_Util.mkApp _183_1523))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (let _183_1530 = (let _183_1529 = (let _183_1528 = (let _183_1527 = (let _183_1526 = (let _183_1525 = (let _183_1524 = (FStar_SMTEncoding_Util.mkOr ((valid_a), (valid_b)))
in ((_183_1524), (valid)))
in (FStar_SMTEncoding_Util.mkIff _183_1525))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_183_1526)))
in (FStar_SMTEncoding_Util.mkForall _183_1527))
in ((_183_1528), (Some ("\\/ interpretation")), (Some ("l_or-interp"))))
in FStar_SMTEncoding_Term.Assume (_183_1529))
in (_183_1530)::[])))))))))
in (

let mk_eq2_interp = (fun env eq2 tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let yy = (("y"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let y = (FStar_SMTEncoding_Util.mkFreeV yy)
in (

let valid = (let _183_1539 = (let _183_1538 = (let _183_1537 = (FStar_SMTEncoding_Util.mkApp ((eq2), ((a)::(x)::(y)::[])))
in (_183_1537)::[])
in (("Valid"), (_183_1538)))
in (FStar_SMTEncoding_Util.mkApp _183_1539))
in (let _183_1546 = (let _183_1545 = (let _183_1544 = (let _183_1543 = (let _183_1542 = (let _183_1541 = (let _183_1540 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in ((_183_1540), (valid)))
in (FStar_SMTEncoding_Util.mkIff _183_1541))
in ((((valid)::[])::[]), ((aa)::(xx)::(yy)::[]), (_183_1542)))
in (FStar_SMTEncoding_Util.mkForall _183_1543))
in ((_183_1544), (Some ("Eq2 interpretation")), (Some ("eq2-interp"))))
in FStar_SMTEncoding_Term.Assume (_183_1545))
in (_183_1546)::[])))))))))
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

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let y = (FStar_SMTEncoding_Util.mkFreeV yy)
in (

let valid = (let _183_1555 = (let _183_1554 = (let _183_1553 = (FStar_SMTEncoding_Util.mkApp ((eq3), ((a)::(b)::(x)::(y)::[])))
in (_183_1553)::[])
in (("Valid"), (_183_1554)))
in (FStar_SMTEncoding_Util.mkApp _183_1555))
in (let _183_1562 = (let _183_1561 = (let _183_1560 = (let _183_1559 = (let _183_1558 = (let _183_1557 = (let _183_1556 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in ((_183_1556), (valid)))
in (FStar_SMTEncoding_Util.mkIff _183_1557))
in ((((valid)::[])::[]), ((aa)::(bb)::(xx)::(yy)::[]), (_183_1558)))
in (FStar_SMTEncoding_Util.mkForall _183_1559))
in ((_183_1560), (Some ("Eq3 interpretation")), (Some ("eq3-interp"))))
in FStar_SMTEncoding_Term.Assume (_183_1561))
in (_183_1562)::[])))))))))))
in (

let mk_imp_interp = (fun env imp tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let valid = (let _183_1571 = (let _183_1570 = (let _183_1569 = (FStar_SMTEncoding_Util.mkApp ((imp), ((a)::(b)::[])))
in (_183_1569)::[])
in (("Valid"), (_183_1570)))
in (FStar_SMTEncoding_Util.mkApp _183_1571))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (let _183_1578 = (let _183_1577 = (let _183_1576 = (let _183_1575 = (let _183_1574 = (let _183_1573 = (let _183_1572 = (FStar_SMTEncoding_Util.mkImp ((valid_a), (valid_b)))
in ((_183_1572), (valid)))
in (FStar_SMTEncoding_Util.mkIff _183_1573))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_183_1574)))
in (FStar_SMTEncoding_Util.mkForall _183_1575))
in ((_183_1576), (Some ("==> interpretation")), (Some ("l_imp-interp"))))
in FStar_SMTEncoding_Term.Assume (_183_1577))
in (_183_1578)::[])))))))))
in (

let mk_iff_interp = (fun env iff tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let valid = (let _183_1587 = (let _183_1586 = (let _183_1585 = (FStar_SMTEncoding_Util.mkApp ((iff), ((a)::(b)::[])))
in (_183_1585)::[])
in (("Valid"), (_183_1586)))
in (FStar_SMTEncoding_Util.mkApp _183_1587))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (let _183_1594 = (let _183_1593 = (let _183_1592 = (let _183_1591 = (let _183_1590 = (let _183_1589 = (let _183_1588 = (FStar_SMTEncoding_Util.mkIff ((valid_a), (valid_b)))
in ((_183_1588), (valid)))
in (FStar_SMTEncoding_Util.mkIff _183_1589))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_183_1590)))
in (FStar_SMTEncoding_Util.mkForall _183_1591))
in ((_183_1592), (Some ("<==> interpretation")), (Some ("l_iff-interp"))))
in FStar_SMTEncoding_Term.Assume (_183_1593))
in (_183_1594)::[])))))))))
in (

let mk_not_interp = (fun env l_not tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let valid = (let _183_1603 = (let _183_1602 = (let _183_1601 = (FStar_SMTEncoding_Util.mkApp ((l_not), ((a)::[])))
in (_183_1601)::[])
in (("Valid"), (_183_1602)))
in (FStar_SMTEncoding_Util.mkApp _183_1603))
in (

let not_valid_a = (let _183_1604 = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot _183_1604))
in (let _183_1609 = (let _183_1608 = (let _183_1607 = (let _183_1606 = (let _183_1605 = (FStar_SMTEncoding_Util.mkIff ((not_valid_a), (valid)))
in ((((valid)::[])::[]), ((aa)::[]), (_183_1605)))
in (FStar_SMTEncoding_Util.mkForall _183_1606))
in ((_183_1607), (Some ("not interpretation")), (Some ("l_not-interp"))))
in FStar_SMTEncoding_Term.Assume (_183_1608))
in (_183_1609)::[]))))))
in (

let mk_forall_interp = (fun env for_all tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let valid = (let _183_1618 = (let _183_1617 = (let _183_1616 = (FStar_SMTEncoding_Util.mkApp ((for_all), ((a)::(b)::[])))
in (_183_1616)::[])
in (("Valid"), (_183_1617)))
in (FStar_SMTEncoding_Util.mkApp _183_1618))
in (

let valid_b_x = (let _183_1621 = (let _183_1620 = (let _183_1619 = (FStar_SMTEncoding_Util.mk_ApplyTT b x)
in (_183_1619)::[])
in (("Valid"), (_183_1620)))
in (FStar_SMTEncoding_Util.mkApp _183_1621))
in (let _183_1635 = (let _183_1634 = (let _183_1633 = (let _183_1632 = (let _183_1631 = (let _183_1630 = (let _183_1629 = (let _183_1628 = (let _183_1627 = (let _183_1623 = (let _183_1622 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_183_1622)::[])
in (_183_1623)::[])
in (let _183_1626 = (let _183_1625 = (let _183_1624 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((_183_1624), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp _183_1625))
in ((_183_1627), ((xx)::[]), (_183_1626))))
in (FStar_SMTEncoding_Util.mkForall _183_1628))
in ((_183_1629), (valid)))
in (FStar_SMTEncoding_Util.mkIff _183_1630))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_183_1631)))
in (FStar_SMTEncoding_Util.mkForall _183_1632))
in ((_183_1633), (Some ("forall interpretation")), (Some ("forall-interp"))))
in FStar_SMTEncoding_Term.Assume (_183_1634))
in (_183_1635)::[]))))))))))
in (

let mk_exists_interp = (fun env for_some tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let valid = (let _183_1644 = (let _183_1643 = (let _183_1642 = (FStar_SMTEncoding_Util.mkApp ((for_some), ((a)::(b)::[])))
in (_183_1642)::[])
in (("Valid"), (_183_1643)))
in (FStar_SMTEncoding_Util.mkApp _183_1644))
in (

let valid_b_x = (let _183_1647 = (let _183_1646 = (let _183_1645 = (FStar_SMTEncoding_Util.mk_ApplyTT b x)
in (_183_1645)::[])
in (("Valid"), (_183_1646)))
in (FStar_SMTEncoding_Util.mkApp _183_1647))
in (let _183_1661 = (let _183_1660 = (let _183_1659 = (let _183_1658 = (let _183_1657 = (let _183_1656 = (let _183_1655 = (let _183_1654 = (let _183_1653 = (let _183_1649 = (let _183_1648 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_183_1648)::[])
in (_183_1649)::[])
in (let _183_1652 = (let _183_1651 = (let _183_1650 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((_183_1650), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp _183_1651))
in ((_183_1653), ((xx)::[]), (_183_1652))))
in (FStar_SMTEncoding_Util.mkExists _183_1654))
in ((_183_1655), (valid)))
in (FStar_SMTEncoding_Util.mkIff _183_1656))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_183_1657)))
in (FStar_SMTEncoding_Util.mkForall _183_1658))
in ((_183_1659), (Some ("exists interpretation")), (Some ("exists-interp"))))
in FStar_SMTEncoding_Term.Assume (_183_1660))
in (_183_1661)::[]))))))))))
in (

let mk_range_interp = (fun env range tt -> (

let range_ty = (FStar_SMTEncoding_Util.mkApp ((range), ([])))
in (let _183_1672 = (let _183_1671 = (let _183_1670 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_ty)
in (let _183_1669 = (let _183_1668 = (varops.mk_unique "typing_range_const")
in Some (_183_1668))
in ((_183_1670), (Some ("Range_const typing")), (_183_1669))))
in FStar_SMTEncoding_Term.Assume (_183_1671))
in (_183_1672)::[])))
in (

let prims = (((FStar_Syntax_Const.unit_lid), (mk_unit)))::(((FStar_Syntax_Const.bool_lid), (mk_bool)))::(((FStar_Syntax_Const.int_lid), (mk_int)))::(((FStar_Syntax_Const.string_lid), (mk_str)))::(((FStar_Syntax_Const.ref_lid), (mk_ref)))::(((FStar_Syntax_Const.true_lid), (mk_true_interp)))::(((FStar_Syntax_Const.false_lid), (mk_false_interp)))::(((FStar_Syntax_Const.and_lid), (mk_and_interp)))::(((FStar_Syntax_Const.or_lid), (mk_or_interp)))::(((FStar_Syntax_Const.eq2_lid), (mk_eq2_interp)))::(((FStar_Syntax_Const.eq3_lid), (mk_eq3_interp)))::(((FStar_Syntax_Const.imp_lid), (mk_imp_interp)))::(((FStar_Syntax_Const.iff_lid), (mk_iff_interp)))::(((FStar_Syntax_Const.not_lid), (mk_not_interp)))::(((FStar_Syntax_Const.forall_lid), (mk_forall_interp)))::(((FStar_Syntax_Const.exists_lid), (mk_exists_interp)))::(((FStar_Syntax_Const.range_lid), (mk_range_interp)))::[]
in (fun env t s tt -> (match ((FStar_Util.find_opt (fun _88_2063 -> (match (_88_2063) with
| (l, _88_2062) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_88_2066, f) -> begin
(f env s tt)
end))))))))))))))))))))))))


let encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let _88_2076 = (encode_function_type_as_formula None None t env)
in (match (_88_2076) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_SMTEncoding_Term.Assume (((form), (Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str))), (Some ((Prims.strcat "lemma_" lid.FStar_Ident.str))))))::[]))
end))))


let encode_free_var : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env fv tt t_norm quals -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if ((let _183_1889 = (FStar_Syntax_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _183_1889)) || (FStar_Syntax_Util.is_lemma t_norm)) then begin
(

let _88_2086 = (new_term_constant_and_tok_from_lid env lid)
in (match (_88_2086) with
| (vname, vtok, env) -> begin
(

let arg_sorts = (match ((let _183_1890 = (FStar_Syntax_Subst.compress t_norm)
in _183_1890.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _88_2089) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun _88_2092 -> FStar_SMTEncoding_Term.Term_sort)))
end
| _88_2095 -> begin
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

let _88_2102 = (prims.mk lid vname)
in (match (_88_2102) with
| (tok, definition) -> begin
(

let env = (push_free_var env lid vname (Some (tok)))
in ((definition), (env)))
end)))
end else begin
(

let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (

let _88_2112 = (

let _88_2107 = (curried_arrow_formals_comp t_norm)
in (match (_88_2107) with
| (args, comp) -> begin
if encode_non_total_function_typ then begin
(let _183_1892 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in ((args), (_183_1892)))
end else begin
((args), (((None), ((FStar_Syntax_Util.comp_result comp)))))
end
end))
in (match (_88_2112) with
| (formals, (pre_opt, res_t)) -> begin
(

let _88_2116 = (new_term_constant_and_tok_from_lid env lid)
in (match (_88_2116) with
| (vname, vtok, env) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
end
| _88_2119 -> begin
(FStar_SMTEncoding_Util.mkApp ((vtok), ([])))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun _88_14 -> (match (_88_14) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(

let _88_2135 = (FStar_Util.prefix vars)
in (match (_88_2135) with
| (_88_2130, (xxsym, _88_2133)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (let _183_1909 = (let _183_1908 = (let _183_1907 = (let _183_1906 = (let _183_1905 = (let _183_1904 = (let _183_1903 = (let _183_1902 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _183_1902))
in ((vapp), (_183_1903)))
in (FStar_SMTEncoding_Util.mkEq _183_1904))
in ((((vapp)::[])::[]), (vars), (_183_1905)))
in (FStar_SMTEncoding_Util.mkForall _183_1906))
in ((_183_1907), (Some ("Discriminator equation")), (Some ((Prims.strcat "disc_equation_" (escape d.FStar_Ident.str))))))
in FStar_SMTEncoding_Term.Assume (_183_1908))
in (_183_1909)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(

let _88_2147 = (FStar_Util.prefix vars)
in (match (_88_2147) with
| (_88_2142, (xxsym, _88_2145)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (

let tp_name = (mk_term_projector_name d f)
in (

let prim_app = (FStar_SMTEncoding_Util.mkApp ((tp_name), ((xx)::[])))
in (let _183_1914 = (let _183_1913 = (let _183_1912 = (let _183_1911 = (let _183_1910 = (FStar_SMTEncoding_Util.mkEq ((vapp), (prim_app)))
in ((((vapp)::[])::[]), (vars), (_183_1910)))
in (FStar_SMTEncoding_Util.mkForall _183_1911))
in ((_183_1912), (Some ("Projector equation")), (Some ((Prims.strcat "proj_equation_" tp_name)))))
in FStar_SMTEncoding_Term.Assume (_183_1913))
in (_183_1914)::[])))))
end))
end
| _88_2153 -> begin
[]
end)))))
in (

let _88_2160 = (encode_binders None formals env)
in (match (_88_2160) with
| (vars, guards, env', decls1, _88_2159) -> begin
(

let _88_2169 = (match (pre_opt) with
| None -> begin
(let _183_1915 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((_183_1915), (decls1)))
end
| Some (p) -> begin
(

let _88_2166 = (encode_formula p env')
in (match (_88_2166) with
| (g, ds) -> begin
(let _183_1916 = (FStar_SMTEncoding_Util.mk_and_l ((g)::guards))
in ((_183_1916), ((FStar_List.append decls1 ds))))
end))
end)
in (match (_88_2169) with
| (guard, decls1) -> begin
(

let vtok_app = (mk_Apply vtok_tm vars)
in (

let vapp = (let _183_1918 = (let _183_1917 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((vname), (_183_1917)))
in (FStar_SMTEncoding_Util.mkApp _183_1918))
in (

let _88_2193 = (

let vname_decl = (let _183_1921 = (let _183_1920 = (FStar_All.pipe_right formals (FStar_List.map (fun _88_2172 -> FStar_SMTEncoding_Term.Term_sort)))
in ((vname), (_183_1920), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (_183_1921))
in (

let _88_2180 = (

let env = (

let _88_2175 = env
in {bindings = _88_2175.bindings; depth = _88_2175.depth; tcenv = _88_2175.tcenv; warn = _88_2175.warn; cache = _88_2175.cache; nolabels = _88_2175.nolabels; use_zfuel_name = _88_2175.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in if (not ((head_normal env tt))) then begin
(encode_term_pred None tt env vtok_tm)
end else begin
(encode_term_pred None t_norm env vtok_tm)
end)
in (match (_88_2180) with
| (tok_typing, decls2) -> begin
(

let tok_typing = FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("function token typing")), (Some ((Prims.strcat "function_token_typing_" vname)))))
in (

let _88_2190 = (match (formals) with
| [] -> begin
(let _183_1925 = (let _183_1924 = (let _183_1923 = (FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left (fun _183_1922 -> Some (_183_1922)) _183_1923))
in (push_free_var env lid vname _183_1924))
in (((FStar_List.append decls2 ((tok_typing)::[]))), (_183_1925)))
end
| _88_2184 -> begin
(

let vtok_decl = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let vtok_fresh = (let _183_1926 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((vtok), (FStar_SMTEncoding_Term.Term_sort)) _183_1926))
in (

let name_tok_corr = (let _183_1930 = (let _183_1929 = (let _183_1928 = (let _183_1927 = (FStar_SMTEncoding_Util.mkEq ((vtok_app), (vapp)))
in ((((vtok_app)::[])::((vapp)::[])::[]), (vars), (_183_1927)))
in (FStar_SMTEncoding_Util.mkForall _183_1928))
in ((_183_1929), (Some ("Name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" vname)))))
in FStar_SMTEncoding_Term.Assume (_183_1930))
in (((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[]))), (env)))))
end)
in (match (_88_2190) with
| (tok_decl, env) -> begin
(((vname_decl)::tok_decl), (env))
end)))
end)))
in (match (_88_2193) with
| (decls2, env) -> begin
(

let _88_2201 = (

let res_t = (FStar_Syntax_Subst.compress res_t)
in (

let _88_2197 = (encode_term res_t env')
in (match (_88_2197) with
| (encoded_res_t, decls) -> begin
(let _183_1931 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in ((encoded_res_t), (_183_1931), (decls)))
end)))
in (match (_88_2201) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (let _183_1935 = (let _183_1934 = (let _183_1933 = (let _183_1932 = (FStar_SMTEncoding_Util.mkImp ((guard), (ty_pred)))
in ((((vapp)::[])::[]), (vars), (_183_1932)))
in (FStar_SMTEncoding_Util.mkForall _183_1933))
in ((_183_1934), (Some ("free var typing")), (Some ((Prims.strcat "typing_" vname)))))
in FStar_SMTEncoding_Term.Assume (_183_1935))
in (

let freshness = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New)) then begin
(let _183_1941 = (let _183_1938 = (let _183_1937 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (let _183_1936 = (varops.next_id ())
in ((vname), (_183_1937), (FStar_SMTEncoding_Term.Term_sort), (_183_1936))))
in (FStar_SMTEncoding_Term.fresh_constructor _183_1938))
in (let _183_1940 = (let _183_1939 = (pretype_axiom vapp vars)
in (_183_1939)::[])
in (_183_1941)::_183_1940))
end else begin
[]
end
in (

let g = (let _183_1946 = (let _183_1945 = (let _183_1944 = (let _183_1943 = (let _183_1942 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_183_1942)
in (FStar_List.append freshness _183_1943))
in (FStar_List.append decls3 _183_1944))
in (FStar_List.append decls2 _183_1945))
in (FStar_List.append decls1 _183_1946))
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

let _88_2212 = (encode_free_var env x t t_norm [])
in (match (_88_2212) with
| (decls, env) -> begin
(

let _88_2217 = (lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_88_2217) with
| (n, x', _88_2216) -> begin
((((n), (x'))), (decls), (env))
end))
end))
end
| Some (n, x, _88_2221) -> begin
((((n), (x))), ([]), (env))
end))


let encode_top_level_val : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env lid t quals -> (

let tt = (norm env t)
in (

let _88_2231 = (encode_free_var env lid t tt quals)
in (match (_88_2231) with
| (decls, env) -> begin
if (FStar_Syntax_Util.is_smt_lemma t) then begin
(let _183_1964 = (let _183_1963 = (encode_smt_lemma env lid tt)
in (FStar_List.append decls _183_1963))
in ((_183_1964), (env)))
end else begin
((decls), (env))
end
end))))


let encode_top_level_vals : env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _88_2237 lb -> (match (_88_2237) with
| (decls, env) -> begin
(

let _88_2241 = (let _183_1973 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env _183_1973 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (_88_2241) with
| (decls', env) -> begin
(((FStar_List.append decls decls')), (env))
end))
end)) (([]), (env)))))


let encode_top_level_let : env_t  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env _88_2245 quals -> (match (_88_2245) with
| (is_rec, bindings) -> begin
(

let eta_expand = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let _88_2255 = (FStar_Util.first_N nbinders formals)
in (match (_88_2255) with
| (formals, extra_formals) -> begin
(

let subst = (FStar_List.map2 (fun _88_2259 _88_2263 -> (match (((_88_2259), (_88_2263))) with
| ((formal, _88_2258), (binder, _88_2262)) -> begin
(let _183_1991 = (let _183_1990 = (FStar_Syntax_Syntax.bv_to_name binder)
in ((formal), (_183_1990)))
in FStar_Syntax_Syntax.NT (_183_1991))
end)) formals binders)
in (

let extra_formals = (let _183_1995 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun _88_2267 -> (match (_88_2267) with
| (x, i) -> begin
(let _183_1994 = (

let _88_2268 = x
in (let _183_1993 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _88_2268.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _88_2268.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _183_1993}))
in ((_183_1994), (i)))
end))))
in (FStar_All.pipe_right _183_1995 FStar_Syntax_Util.name_binders))
in (

let body = (let _183_2002 = (FStar_Syntax_Subst.compress body)
in (let _183_2001 = (let _183_1996 = (FStar_Syntax_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _183_1996))
in (let _183_2000 = (let _183_1999 = (let _183_1998 = (FStar_Syntax_Subst.subst subst t)
in _183_1998.FStar_Syntax_Syntax.n)
in (FStar_All.pipe_left (fun _183_1997 -> Some (_183_1997)) _183_1999))
in (FStar_Syntax_Syntax.extend_app_n _183_2002 _183_2001 _183_2000 body.FStar_Syntax_Syntax.pos))))
in (((FStar_List.append binders extra_formals)), (body)))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (

let rec aux = (fun norm t_norm -> (match ((let _183_2013 = (FStar_Syntax_Util.unascribe e)
in _183_2013.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, lopt) -> begin
(

let _88_2287 = (FStar_Syntax_Subst.open_term' binders body)
in (match (_88_2287) with
| (binders, body, opening) -> begin
(match ((let _183_2014 = (FStar_Syntax_Subst.compress t_norm)
in _183_2014.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let _88_2294 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_88_2294) with
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

let _88_2301 = (FStar_Util.first_N nformals binders)
in (match (_88_2301) with
| (bs0, rest) -> begin
(

let c = (

let subst = (FStar_List.map2 (fun _88_2305 _88_2309 -> (match (((_88_2305), (_88_2309))) with
| ((b, _88_2304), (x, _88_2308)) -> begin
(let _183_2018 = (let _183_2017 = (FStar_Syntax_Syntax.bv_to_name x)
in ((b), (_183_2017)))
in FStar_Syntax_Syntax.NT (_183_2018))
end)) bs0 formals)
in (FStar_Syntax_Subst.subst_comp subst c))
in (

let body = (FStar_Syntax_Util.abs rest body lopt)
in ((((bs0), (body), (bs0), ((FStar_Syntax_Util.comp_result c)))), (false))))
end)))
end else begin
if (nformals > nbinders) then begin
(

let _88_2315 = (eta_expand binders formals body tres)
in (match (_88_2315) with
| (binders, body) -> begin
((((binders), (body), (formals), (tres))), (false))
end))
end else begin
((((binders), (body), (formals), (tres))), (false))
end
end)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, _88_2318) -> begin
(let _183_2020 = (let _183_2019 = (aux norm x.FStar_Syntax_Syntax.sort)
in (Prims.fst _183_2019))
in ((_183_2020), (true)))
end
| _88_2322 when (not (norm)) -> begin
(

let t_norm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm)
in (aux true t_norm))
end
| _88_2325 -> begin
(let _183_2023 = (let _183_2022 = (FStar_Syntax_Print.term_to_string e)
in (let _183_2021 = (FStar_Syntax_Print.term_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str _183_2022 _183_2021)))
in (FStar_All.failwith _183_2023))
end)
end))
end
| _88_2327 -> begin
(match ((let _183_2024 = (FStar_Syntax_Subst.compress t_norm)
in _183_2024.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let _88_2334 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_88_2334) with
| (formals, c) -> begin
(

let tres = (FStar_Syntax_Util.comp_result c)
in (

let _88_2338 = (eta_expand [] formals e tres)
in (match (_88_2338) with
| (binders, body) -> begin
((((binders), (body), (formals), (tres))), (false))
end)))
end))
end
| _88_2340 -> begin
(((([]), (e), ([]), (t_norm))), (false))
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

let _88_2368 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _88_2355 lb -> (match (_88_2355) with
| (toks, typs, decls, env) -> begin
(

let _88_2357 = if (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) then begin
(Prims.raise Let_rec_unencodeable)
end else begin
()
end
in (

let t_norm = (whnf env lb.FStar_Syntax_Syntax.lbtyp)
in (

let _88_2363 = (let _183_2029 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env _183_2029 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (_88_2363) with
| (tok, decl, env) -> begin
(let _183_2032 = (let _183_2031 = (let _183_2030 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in ((_183_2030), (tok)))
in (_183_2031)::toks)
in ((_183_2032), ((t_norm)::typs), ((decl)::decls), (env)))
end))))
end)) (([]), ([]), ([]), (env))))
in (match (_88_2368) with
| (toks, typs, decls, env) -> begin
(

let toks = (FStar_List.rev toks)
in (

let decls = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (

let typs = (FStar_List.rev typs)
in (

let mk_app = (fun curry f ftok vars -> (match (vars) with
| [] -> begin
(FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
end
| _88_2379 -> begin
if curry then begin
(match (ftok) with
| Some (ftok) -> begin
(mk_Apply ftok vars)
end
| None -> begin
(let _183_2041 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply _183_2041 vars))
end)
end else begin
(let _183_2043 = (let _183_2042 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (_183_2042)))
in (FStar_SMTEncoding_Util.mkApp _183_2043))
end
end))
in if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _88_15 -> (match (_88_15) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| _88_2386 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> (let _183_2046 = (FStar_Syntax_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _183_2046)))))) then begin
((decls), (env))
end else begin
if (not (is_rec)) then begin
(match (((bindings), (typs), (toks))) with
| (({FStar_Syntax_Syntax.lbname = _88_2396; FStar_Syntax_Syntax.lbunivs = _88_2394; FStar_Syntax_Syntax.lbtyp = _88_2392; FStar_Syntax_Syntax.lbeff = _88_2390; FStar_Syntax_Syntax.lbdef = e})::[], (t_norm)::[], ((flid_fv, (f, ftok)))::[]) -> begin
(

let e = (FStar_Syntax_Subst.compress e)
in (

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let _88_2418 = (destruct_bound_function flid t_norm e)
in (match (_88_2418) with
| ((binders, body, _88_2413, _88_2415), curry) -> begin
(

let _88_2425 = (encode_binders None binders env)
in (match (_88_2425) with
| (vars, guards, env', binder_decls, _88_2424) -> begin
(

let app = (mk_app curry f ftok vars)
in (

let _88_2431 = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic)) then begin
(let _183_2048 = (FStar_SMTEncoding_Term.mk_Valid app)
in (let _183_2047 = (encode_formula body env')
in ((_183_2048), (_183_2047))))
end else begin
(let _183_2049 = (encode_term body env')
in ((app), (_183_2049)))
end
in (match (_88_2431) with
| (app, (body, decls2)) -> begin
(

let eqn = (let _183_2055 = (let _183_2054 = (let _183_2051 = (let _183_2050 = (FStar_SMTEncoding_Util.mkEq ((app), (body)))
in ((((app)::[])::[]), (vars), (_183_2050)))
in (FStar_SMTEncoding_Util.mkForall _183_2051))
in (let _183_2053 = (let _183_2052 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (_183_2052))
in ((_183_2054), (_183_2053), (Some ((Prims.strcat "equation_" f))))))
in FStar_SMTEncoding_Term.Assume (_183_2055))
in (let _183_2060 = (let _183_2059 = (let _183_2058 = (let _183_2057 = (let _183_2056 = (primitive_type_axioms env.tcenv flid f app)
in (FStar_List.append ((eqn)::[]) _183_2056))
in (FStar_List.append decls2 _183_2057))
in (FStar_List.append binder_decls _183_2058))
in (FStar_List.append decls _183_2059))
in ((_183_2060), (env))))
end)))
end))
end))))
end
| _88_2434 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(

let fuel = (let _183_2061 = (varops.fresh "fuel")
in ((_183_2061), (FStar_SMTEncoding_Term.Fuel_sort)))
in (

let fuel_tm = (FStar_SMTEncoding_Util.mkFreeV fuel)
in (

let env0 = env
in (

let _88_2452 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _88_2440 _88_2445 -> (match (((_88_2440), (_88_2445))) with
| ((gtoks, env), (flid_fv, (f, ftok))) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let g = (let _183_2064 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented")
in (varops.new_fvar _183_2064))
in (

let gtok = (let _183_2065 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented_token")
in (varops.new_fvar _183_2065))
in (

let env = (let _183_2068 = (let _183_2067 = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::[])))
in (FStar_All.pipe_left (fun _183_2066 -> Some (_183_2066)) _183_2067))
in (push_free_var env flid gtok _183_2068))
in (((((flid), (f), (ftok), (g), (gtok)))::gtoks), (env))))))
end)) (([]), (env))))
in (match (_88_2452) with
| (gtoks, env) -> begin
(

let gtoks = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env0 _88_2461 t_norm _88_2472 -> (match (((_88_2461), (_88_2472))) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = _88_2471; FStar_Syntax_Syntax.lbunivs = _88_2469; FStar_Syntax_Syntax.lbtyp = _88_2467; FStar_Syntax_Syntax.lbeff = _88_2465; FStar_Syntax_Syntax.lbdef = e}) -> begin
(

let _88_2479 = (destruct_bound_function flid t_norm e)
in (match (_88_2479) with
| ((binders, body, formals, tres), curry) -> begin
(

let _88_2480 = if curry then begin
(FStar_All.failwith "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type")
end else begin
()
end
in (

let _88_2488 = (encode_binders None binders env)
in (match (_88_2488) with
| (vars, guards, env', binder_decls, _88_2487) -> begin
(

let decl_g = (let _183_2079 = (let _183_2078 = (let _183_2077 = (FStar_List.map Prims.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::_183_2077)
in ((g), (_183_2078), (FStar_SMTEncoding_Term.Term_sort), (Some ("Fuel-instrumented function name"))))
in FStar_SMTEncoding_Term.DeclFun (_183_2079))
in (

let env0 = (push_zfuel_name env0 flid g)
in (

let decl_g_tok = FStar_SMTEncoding_Term.DeclFun (((gtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Token for fuel-instrumented partial applications"))))
in (

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let app = (let _183_2081 = (let _183_2080 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (_183_2080)))
in (FStar_SMTEncoding_Util.mkApp _183_2081))
in (

let gsapp = (let _183_2084 = (let _183_2083 = (let _183_2082 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (_183_2082)::vars_tm)
in ((g), (_183_2083)))
in (FStar_SMTEncoding_Util.mkApp _183_2084))
in (

let gmax = (let _183_2087 = (let _183_2086 = (let _183_2085 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (_183_2085)::vars_tm)
in ((g), (_183_2086)))
in (FStar_SMTEncoding_Util.mkApp _183_2087))
in (

let _88_2498 = (encode_term body env')
in (match (_88_2498) with
| (body_tm, decls2) -> begin
(

let eqn_g = (let _183_2093 = (let _183_2092 = (let _183_2089 = (let _183_2088 = (FStar_SMTEncoding_Util.mkEq ((gsapp), (body_tm)))
in ((((gsapp)::[])::[]), (Some ((Prims.parse_int "0"))), ((fuel)::vars), (_183_2088)))
in (FStar_SMTEncoding_Util.mkForall' _183_2089))
in (let _183_2091 = (let _183_2090 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (_183_2090))
in ((_183_2092), (_183_2091), (Some ((Prims.strcat "equation_with_fuel_" g))))))
in FStar_SMTEncoding_Term.Assume (_183_2093))
in (

let eqn_f = (let _183_2097 = (let _183_2096 = (let _183_2095 = (let _183_2094 = (FStar_SMTEncoding_Util.mkEq ((app), (gmax)))
in ((((app)::[])::[]), (vars), (_183_2094)))
in (FStar_SMTEncoding_Util.mkForall _183_2095))
in ((_183_2096), (Some ("Correspondence of recursive function to instrumented version")), (Some ((Prims.strcat "fuel_correspondence_" g)))))
in FStar_SMTEncoding_Term.Assume (_183_2097))
in (

let eqn_g' = (let _183_2106 = (let _183_2105 = (let _183_2104 = (let _183_2103 = (let _183_2102 = (let _183_2101 = (let _183_2100 = (let _183_2099 = (let _183_2098 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "0"))
in (_183_2098)::vars_tm)
in ((g), (_183_2099)))
in (FStar_SMTEncoding_Util.mkApp _183_2100))
in ((gsapp), (_183_2101)))
in (FStar_SMTEncoding_Util.mkEq _183_2102))
in ((((gsapp)::[])::[]), ((fuel)::vars), (_183_2103)))
in (FStar_SMTEncoding_Util.mkForall _183_2104))
in ((_183_2105), (Some ("Fuel irrelevance")), (Some ((Prims.strcat "fuel_irrelevance_" g)))))
in FStar_SMTEncoding_Term.Assume (_183_2106))
in (

let _88_2521 = (

let _88_2508 = (encode_binders None formals env0)
in (match (_88_2508) with
| (vars, v_guards, env, binder_decls, _88_2507) -> begin
(

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let gapp = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::vars_tm)))
in (

let tok_corr = (

let tok_app = (let _183_2107 = (FStar_SMTEncoding_Util.mkFreeV ((gtok), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply _183_2107 ((fuel)::vars)))
in (let _183_2111 = (let _183_2110 = (let _183_2109 = (let _183_2108 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (gapp)))
in ((((tok_app)::[])::[]), ((fuel)::vars), (_183_2108)))
in (FStar_SMTEncoding_Util.mkForall _183_2109))
in ((_183_2110), (Some ("Fuel token correspondence")), (Some ((Prims.strcat "fuel_token_correspondence_" gtok)))))
in FStar_SMTEncoding_Term.Assume (_183_2111)))
in (

let _88_2518 = (

let _88_2515 = (encode_term_pred None tres env gapp)
in (match (_88_2515) with
| (g_typing, d3) -> begin
(let _183_2119 = (let _183_2118 = (let _183_2117 = (let _183_2116 = (let _183_2115 = (let _183_2114 = (let _183_2113 = (let _183_2112 = (FStar_SMTEncoding_Util.mk_and_l v_guards)
in ((_183_2112), (g_typing)))
in (FStar_SMTEncoding_Util.mkImp _183_2113))
in ((((gapp)::[])::[]), ((fuel)::vars), (_183_2114)))
in (FStar_SMTEncoding_Util.mkForall _183_2115))
in ((_183_2116), (Some ("Typing correspondence of token to term")), (Some ((Prims.strcat "token_correspondence_" g)))))
in FStar_SMTEncoding_Term.Assume (_183_2117))
in (_183_2118)::[])
in ((d3), (_183_2119)))
end))
in (match (_88_2518) with
| (aux_decls, typing_corr) -> begin
(((FStar_List.append binder_decls aux_decls)), ((FStar_List.append typing_corr ((tok_corr)::[]))))
end)))))
end))
in (match (_88_2521) with
| (aux_decls, g_typing) -> begin
(((FStar_List.append binder_decls (FStar_List.append decls2 (FStar_List.append aux_decls ((decl_g)::(decl_g_tok)::[]))))), ((FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing)), (env0))
end)))))
end)))))))))
end)))
end))
end))
in (

let _88_2537 = (let _183_2122 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _88_2525 _88_2529 -> (match (((_88_2525), (_88_2529))) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(

let _88_2533 = (encode_one_binding env0 gtok ty bs)
in (match (_88_2533) with
| (decls', eqns', env0) -> begin
(((decls')::decls), ((FStar_List.append eqns' eqns)), (env0))
end))
end)) (((decls)::[]), ([]), (env0)) _183_2122))
in (match (_88_2537) with
| (decls, eqns, env0) -> begin
(

let _88_2546 = (let _183_2124 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _183_2124 (FStar_List.partition (fun _88_16 -> (match (_88_16) with
| FStar_SMTEncoding_Term.DeclFun (_88_2540) -> begin
true
end
| _88_2543 -> begin
false
end)))))
in (match (_88_2546) with
| (prefix_decls, rest) -> begin
(

let eqns = (FStar_List.rev eqns)
in (((FStar_List.append prefix_decls (FStar_List.append rest eqns))), (env0)))
end))
end))))
end)))))
end
end))))
end))
end
end)
with
| Let_rec_unencodeable -> begin
(

let msg = (let _183_2127 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _183_2127 (FStar_String.concat " and ")))
in (

let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in (((decl)::[]), (env))))
end))
end))


let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let _88_2550 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _183_2136 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _183_2136))
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

let _88_2558 = (encode_sigelt' env se)
in (match (_88_2558) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _183_2139 = (let _183_2138 = (let _183_2137 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (_183_2137))
in (_183_2138)::[])
in ((_183_2139), (e)))
end
| _88_2561 -> begin
(let _183_2146 = (let _183_2145 = (let _183_2141 = (let _183_2140 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_183_2140))
in (_183_2141)::g)
in (let _183_2144 = (let _183_2143 = (let _183_2142 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_183_2142))
in (_183_2143)::[])
in (FStar_List.append _183_2145 _183_2144)))
in ((_183_2146), (e)))
end)
end)))))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let should_skip = (fun l -> false)
in (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_88_2567) -> begin
(FStar_All.failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _88_2583) -> begin
if (let _183_2151 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right _183_2151 Prims.op_Negation)) then begin
(([]), (env))
end else begin
(

let close_effect_params = (fun tm -> (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
tm
end
| _88_2590 -> begin
(let _183_2157 = (let _183_2156 = (let _183_2155 = (FStar_All.pipe_left (fun _183_2154 -> Some (_183_2154)) (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid)))
in ((ed.FStar_Syntax_Syntax.binders), (tm), (_183_2155)))
in FStar_Syntax_Syntax.Tm_abs (_183_2156))
in (FStar_Syntax_Syntax.mk _183_2157 None tm.FStar_Syntax_Syntax.pos))
end))
in (

let encode_action = (fun env a -> (

let _88_2597 = (new_term_constant_and_tok_from_lid env a.FStar_Syntax_Syntax.action_name)
in (match (_88_2597) with
| (aname, atok, env) -> begin
(

let _88_2601 = (FStar_Syntax_Util.arrow_formals_comp a.FStar_Syntax_Syntax.action_typ)
in (match (_88_2601) with
| (formals, _88_2600) -> begin
(

let _88_2604 = (let _183_2162 = (close_effect_params a.FStar_Syntax_Syntax.action_defn)
in (encode_term _183_2162 env))
in (match (_88_2604) with
| (tm, decls) -> begin
(

let a_decls = (let _183_2166 = (let _183_2165 = (let _183_2164 = (FStar_All.pipe_right formals (FStar_List.map (fun _88_2605 -> FStar_SMTEncoding_Term.Term_sort)))
in ((aname), (_183_2164), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action"))))
in FStar_SMTEncoding_Term.DeclFun (_183_2165))
in (_183_2166)::(FStar_SMTEncoding_Term.DeclFun (((atok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action token")))))::[])
in (

let _88_2619 = (let _183_2168 = (FStar_All.pipe_right formals (FStar_List.map (fun _88_2611 -> (match (_88_2611) with
| (bv, _88_2610) -> begin
(

let _88_2616 = (gen_term_var env bv)
in (match (_88_2616) with
| (xxsym, xx, _88_2615) -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (xx))
end))
end))))
in (FStar_All.pipe_right _183_2168 FStar_List.split))
in (match (_88_2619) with
| (xs_sorts, xs) -> begin
(

let app = (let _183_2171 = (let _183_2170 = (let _183_2169 = (FStar_SMTEncoding_Util.mkApp ((aname), (xs)))
in (_183_2169)::[])
in (("Reify"), (_183_2170)))
in (FStar_SMTEncoding_Util.mkApp _183_2171))
in (

let a_eq = (let _183_2177 = (let _183_2176 = (let _183_2175 = (let _183_2174 = (let _183_2173 = (let _183_2172 = (mk_Apply tm xs_sorts)
in ((app), (_183_2172)))
in (FStar_SMTEncoding_Util.mkEq _183_2173))
in ((((app)::[])::[]), (xs_sorts), (_183_2174)))
in (FStar_SMTEncoding_Util.mkForall _183_2175))
in ((_183_2176), (Some ("Action equality")), (Some ((Prims.strcat aname "_equality")))))
in FStar_SMTEncoding_Term.Assume (_183_2177))
in (

let tok_correspondence = (

let tok_term = (FStar_SMTEncoding_Util.mkFreeV ((atok), (FStar_SMTEncoding_Term.Term_sort)))
in (

let tok_app = (mk_Apply tok_term xs_sorts)
in (let _183_2181 = (let _183_2180 = (let _183_2179 = (let _183_2178 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (app)))
in ((((tok_app)::[])::[]), (xs_sorts), (_183_2178)))
in (FStar_SMTEncoding_Util.mkForall _183_2179))
in ((_183_2180), (Some ("Action token correspondence")), (Some ((Prims.strcat aname "_token_correspondence")))))
in FStar_SMTEncoding_Term.Assume (_183_2181))))
in ((env), ((FStar_List.append decls (FStar_List.append a_decls ((a_eq)::(tok_correspondence)::[]))))))))
end)))
end))
end))
end)))
in (

let _88_2627 = (FStar_Util.fold_map encode_action env ed.FStar_Syntax_Syntax.actions)
in (match (_88_2627) with
| (env, decls2) -> begin
(((FStar_List.flatten decls2)), (env))
end))))
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _88_2630, _88_2632, _88_2634, _88_2636) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid) -> begin
(

let _88_2642 = (new_term_constant_and_tok_from_lid env lid)
in (match (_88_2642) with
| (tname, ttok, env) -> begin
(([]), (env))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _88_2645, t, quals, _88_2649) -> begin
(

let will_encode_definition = (not ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _88_17 -> (match (_88_17) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Irreducible) -> begin
true
end
| _88_2662 -> begin
false
end))))))
in if will_encode_definition then begin
(([]), (env))
end else begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (

let _88_2667 = (encode_top_level_val env fv t quals)
in (match (_88_2667) with
| (decls, env) -> begin
(

let tname = lid.FStar_Ident.str
in (

let tsym = (FStar_SMTEncoding_Util.mkFreeV ((tname), (FStar_SMTEncoding_Term.Term_sort)))
in (let _183_2184 = (let _183_2183 = (primitive_type_axioms env.tcenv lid tname tsym)
in (FStar_List.append decls _183_2183))
in ((_183_2184), (env)))))
end)))
end)
end
| FStar_Syntax_Syntax.Sig_assume (l, f, _88_2673, _88_2675) -> begin
(

let _88_2680 = (encode_formula f env)
in (match (_88_2680) with
| (f, decls) -> begin
(

let g = (let _183_2191 = (let _183_2190 = (let _183_2189 = (let _183_2186 = (let _183_2185 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" _183_2185))
in Some (_183_2186))
in (let _183_2188 = (let _183_2187 = (varops.mk_unique (Prims.strcat "assumption_" l.FStar_Ident.str))
in Some (_183_2187))
in ((f), (_183_2189), (_183_2188))))
in FStar_SMTEncoding_Term.Assume (_183_2190))
in (_183_2191)::[])
in (((FStar_List.append decls g)), (env)))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _88_2685, quals) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) -> begin
(

let _88_2698 = (FStar_Util.fold_map (fun env lb -> (

let lid = (let _183_2195 = (let _183_2194 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _183_2194.FStar_Syntax_Syntax.fv_name)
in _183_2195.FStar_Syntax_Syntax.v)
in if (let _183_2196 = (FStar_TypeChecker_Env.try_lookup_val_decl env.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone _183_2196)) then begin
(

let val_decl = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), (r)))
in (

let _88_2695 = (encode_sigelt' env val_decl)
in (match (_88_2695) with
| (decls, env) -> begin
((env), (decls))
end)))
end else begin
((env), ([]))
end)) env (Prims.snd lbs))
in (match (_88_2698) with
| (env, decls) -> begin
(((FStar_List.flatten decls)), (env))
end))
end
| FStar_Syntax_Syntax.Sig_let ((_88_2700, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t); FStar_Syntax_Syntax.lbunivs = _88_2708; FStar_Syntax_Syntax.lbtyp = _88_2706; FStar_Syntax_Syntax.lbeff = _88_2704; FStar_Syntax_Syntax.lbdef = _88_2702})::[]), _88_2715, _88_2717, _88_2719) when (FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Syntax_Const.b2t_lid) -> begin
(

let _88_2725 = (new_term_constant_and_tok_from_lid env b2t.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_88_2725) with
| (tname, ttok, env) -> begin
(

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let valid_b2t_x = (let _183_2199 = (let _183_2198 = (let _183_2197 = (FStar_SMTEncoding_Util.mkApp (("Prims.b2t"), ((x)::[])))
in (_183_2197)::[])
in (("Valid"), (_183_2198)))
in (FStar_SMTEncoding_Util.mkApp _183_2199))
in (

let decls = (let _183_2207 = (let _183_2206 = (let _183_2205 = (let _183_2204 = (let _183_2203 = (let _183_2202 = (let _183_2201 = (let _183_2200 = (FStar_SMTEncoding_Util.mkApp (("BoxBool_proj_0"), ((x)::[])))
in ((valid_b2t_x), (_183_2200)))
in (FStar_SMTEncoding_Util.mkEq _183_2201))
in ((((valid_b2t_x)::[])::[]), ((xx)::[]), (_183_2202)))
in (FStar_SMTEncoding_Util.mkForall _183_2203))
in ((_183_2204), (Some ("b2t def")), (Some ("b2t_def"))))
in FStar_SMTEncoding_Term.Assume (_183_2205))
in (_183_2206)::[])
in (FStar_SMTEncoding_Term.DeclFun (((tname), ((FStar_SMTEncoding_Term.Term_sort)::[]), (FStar_SMTEncoding_Term.Term_sort), (None))))::_183_2207)
in ((decls), (env))))))
end))
end
| FStar_Syntax_Syntax.Sig_let (_88_2731, _88_2733, _88_2735, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _88_18 -> (match (_88_18) with
| FStar_Syntax_Syntax.Discriminator (_88_2741) -> begin
true
end
| _88_2744 -> begin
false
end)))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let (_88_2746, _88_2748, lids, quals) when ((FStar_All.pipe_right lids (FStar_Util.for_some (fun l -> ((let _183_2210 = (FStar_List.hd l.FStar_Ident.ns)
in _183_2210.FStar_Ident.idText) = "Prims")))) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun _88_19 -> (match (_88_19) with
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
true
end
| _88_2757 -> begin
false
end))))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _88_2763, _88_2765, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _88_20 -> (match (_88_20) with
| FStar_Syntax_Syntax.Projector (_88_2771) -> begin
true
end
| _88_2774 -> begin
false
end)))) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((try_lookup_free_var env l)) with
| Some (_88_2778) -> begin
(([]), (env))
end
| None -> begin
(

let se = FStar_Syntax_Syntax.Sig_declare_typ (((l), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), ((FStar_Ident.range_of_lid l))))
in (encode_sigelt env se))
end)))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _88_2787, _88_2789, quals) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) -> begin
(match ((let _183_2213 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef)
in _183_2213.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, _88_2796) -> begin
(

let body = (FStar_Syntax_Util.mk_reify body)
in (

let tm = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None)))) None lb.FStar_Syntax_Syntax.lbdef.FStar_Syntax_Syntax.pos)
in (

let tm' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env.tcenv tm)
in (

let lb_typ = (

let _88_2804 = (FStar_Syntax_Util.arrow_formals_comp lb.FStar_Syntax_Syntax.lbtyp)
in (match (_88_2804) with
| (formals, comp) -> begin
(

let reified_typ = (FStar_TypeChecker_Util.reify_comp (

let _88_2805 = env.tcenv
in {FStar_TypeChecker_Env.solver = _88_2805.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _88_2805.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _88_2805.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _88_2805.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _88_2805.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _88_2805.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _88_2805.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _88_2805.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _88_2805.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _88_2805.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _88_2805.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _88_2805.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _88_2805.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _88_2805.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _88_2805.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _88_2805.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _88_2805.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _88_2805.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _88_2805.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _88_2805.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _88_2805.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _88_2805.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _88_2805.FStar_TypeChecker_Env.qname_and_index}) (FStar_Syntax_Util.lcomp_of_comp comp) FStar_Syntax_Syntax.U_unknown)
in (let _183_2214 = (FStar_Syntax_Syntax.mk_Total reified_typ)
in (FStar_Syntax_Util.arrow formals _183_2214)))
end))
in (

let lb = (

let _88_2809 = lb
in {FStar_Syntax_Syntax.lbname = _88_2809.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _88_2809.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lb_typ; FStar_Syntax_Syntax.lbeff = _88_2809.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = tm'})
in (encode_top_level_let env ((false), ((lb)::[])) quals))))))
end
| _88_2813 -> begin
(([]), (env))
end)
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), _88_2818, _88_2820, quals) -> begin
(encode_top_level_let env ((is_rec), (bindings)) quals)
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _88_2826, _88_2828, _88_2830) -> begin
(

let _88_2835 = (encode_signature env ses)
in (match (_88_2835) with
| (g, env) -> begin
(

let _88_2849 = (FStar_All.pipe_right g (FStar_List.partition (fun _88_21 -> (match (_88_21) with
| FStar_SMTEncoding_Term.Assume (_88_2838, Some ("inversion axiom"), _88_2842) -> begin
false
end
| _88_2846 -> begin
true
end))))
in (match (_88_2849) with
| (g', inversions) -> begin
(

let _88_2858 = (FStar_All.pipe_right g' (FStar_List.partition (fun _88_22 -> (match (_88_22) with
| FStar_SMTEncoding_Term.DeclFun (_88_2852) -> begin
true
end
| _88_2855 -> begin
false
end))))
in (match (_88_2858) with
| (decls, rest) -> begin
(((FStar_List.append decls (FStar_List.append rest inversions))), (env))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, _88_2861, tps, k, _88_2865, datas, quals, _88_2869) -> begin
(

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _88_23 -> (match (_88_23) with
| (FStar_Syntax_Syntax.Logic) | (FStar_Syntax_Syntax.Assumption) -> begin
true
end
| _88_2876 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(

let _88_2888 = c
in (match (_88_2888) with
| (name, args, _88_2883, _88_2885, _88_2887) -> begin
(let _183_2222 = (let _183_2221 = (let _183_2220 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in ((name), (_183_2220), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (_183_2221))
in (_183_2222)::[])
end))
end else begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end)
in (

let inversion_axioms = (fun tapp vars -> if (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _183_2228 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right _183_2228 FStar_Option.isNone))))) then begin
[]
end else begin
(

let _88_2895 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_88_2895) with
| (xxsym, xx) -> begin
(

let _88_2931 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _88_2898 l -> (match (_88_2898) with
| (out, decls) -> begin
(

let _88_2903 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (_88_2903) with
| (_88_2901, data_t) -> begin
(

let _88_2906 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (_88_2906) with
| (args, res) -> begin
(

let indices = (match ((let _183_2231 = (FStar_Syntax_Subst.compress res)
in _183_2231.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_88_2908, indices) -> begin
indices
end
| _88_2913 -> begin
[]
end)
in (

let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env _88_2919 -> (match (_88_2919) with
| (x, _88_2918) -> begin
(let _183_2236 = (let _183_2235 = (let _183_2234 = (mk_term_projector_name l x)
in ((_183_2234), ((xx)::[])))
in (FStar_SMTEncoding_Util.mkApp _183_2235))
in (push_term_var env x _183_2236))
end)) env))
in (

let _88_2923 = (encode_args indices env)
in (match (_88_2923) with
| (indices, decls') -> begin
(

let _88_2924 = if ((FStar_List.length indices) <> (FStar_List.length vars)) then begin
(FStar_All.failwith "Impossible")
end else begin
()
end
in (

let eqs = (let _183_2241 = (FStar_List.map2 (fun v a -> (let _183_2240 = (let _183_2239 = (FStar_SMTEncoding_Util.mkFreeV v)
in ((_183_2239), (a)))
in (FStar_SMTEncoding_Util.mkEq _183_2240))) vars indices)
in (FStar_All.pipe_right _183_2241 FStar_SMTEncoding_Util.mk_and_l))
in (let _183_2246 = (let _183_2245 = (let _183_2244 = (let _183_2243 = (let _183_2242 = (mk_data_tester env l xx)
in ((_183_2242), (eqs)))
in (FStar_SMTEncoding_Util.mkAnd _183_2243))
in ((out), (_183_2244)))
in (FStar_SMTEncoding_Util.mkOr _183_2245))
in ((_183_2246), ((FStar_List.append decls decls'))))))
end))))
end))
end))
end)) ((FStar_SMTEncoding_Util.mkFalse), ([]))))
in (match (_88_2931) with
| (data_ax, decls) -> begin
(

let _88_2934 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_88_2934) with
| (ffsym, ff) -> begin
(

let fuel_guarded_inversion = (

let xx_has_type_sfuel = if ((FStar_List.length datas) > (Prims.parse_int "1")) then begin
(let _183_2247 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((ff)::[])))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel _183_2247 xx tapp))
end else begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end
in (let _183_2254 = (let _183_2253 = (let _183_2250 = (let _183_2249 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (let _183_2248 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_sfuel), (data_ax)))
in ((((xx_has_type_sfuel)::[])::[]), (_183_2249), (_183_2248))))
in (FStar_SMTEncoding_Util.mkForall _183_2250))
in (let _183_2252 = (let _183_2251 = (varops.mk_unique (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str))
in Some (_183_2251))
in ((_183_2253), (Some ("inversion axiom")), (_183_2252))))
in FStar_SMTEncoding_Term.Assume (_183_2254)))
in (

let pattern_guarded_inversion = if ((contains_name env "Prims.inversion") && ((FStar_List.length datas) > (Prims.parse_int "1"))) then begin
(

let xx_has_type_fuel = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let pattern_guard = (FStar_SMTEncoding_Util.mkApp (("Prims.inversion"), ((tapp)::[])))
in (let _183_2262 = (let _183_2261 = (let _183_2260 = (let _183_2257 = (let _183_2256 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (let _183_2255 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_fuel), (data_ax)))
in ((((xx_has_type_fuel)::(pattern_guard)::[])::[]), (_183_2256), (_183_2255))))
in (FStar_SMTEncoding_Util.mkForall _183_2257))
in (let _183_2259 = (let _183_2258 = (varops.mk_unique (Prims.strcat "pattern_guarded_inversion_" t.FStar_Ident.str))
in Some (_183_2258))
in ((_183_2260), (Some ("inversion axiom")), (_183_2259))))
in FStar_SMTEncoding_Term.Assume (_183_2261))
in (_183_2262)::[])))
end else begin
[]
end
in (FStar_List.append decls (FStar_List.append ((fuel_guarded_inversion)::[]) pattern_guarded_inversion))))
end))
end))
end))
end)
in (

let _88_2948 = (match ((let _183_2263 = (FStar_Syntax_Subst.compress k)
in _183_2263.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
(((FStar_List.append tps formals)), ((FStar_Syntax_Util.comp_result kres)))
end
| _88_2945 -> begin
((tps), (k))
end)
in (match (_88_2948) with
| (formals, res) -> begin
(

let _88_2951 = (FStar_Syntax_Subst.open_term formals res)
in (match (_88_2951) with
| (formals, res) -> begin
(

let _88_2958 = (encode_binders None formals env)
in (match (_88_2958) with
| (vars, guards, env', binder_decls, _88_2957) -> begin
(

let _88_2962 = (new_term_constant_and_tok_from_lid env t)
in (match (_88_2962) with
| (tname, ttok, env) -> begin
(

let ttok_tm = (FStar_SMTEncoding_Util.mkApp ((ttok), ([])))
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let tapp = (let _183_2265 = (let _183_2264 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((tname), (_183_2264)))
in (FStar_SMTEncoding_Util.mkApp _183_2265))
in (

let _88_2983 = (

let tname_decl = (let _183_2269 = (let _183_2268 = (FStar_All.pipe_right vars (FStar_List.map (fun _88_2968 -> (match (_88_2968) with
| (n, s) -> begin
(((Prims.strcat tname n)), (s))
end))))
in (let _183_2267 = (varops.next_id ())
in ((tname), (_183_2268), (FStar_SMTEncoding_Term.Term_sort), (_183_2267), (false))))
in (constructor_or_logic_type_decl _183_2269))
in (

let _88_2980 = (match (vars) with
| [] -> begin
(let _183_2273 = (let _183_2272 = (let _183_2271 = (FStar_SMTEncoding_Util.mkApp ((tname), ([])))
in (FStar_All.pipe_left (fun _183_2270 -> Some (_183_2270)) _183_2271))
in (push_free_var env t tname _183_2272))
in (([]), (_183_2273)))
end
| _88_2972 -> begin
(

let ttok_decl = FStar_SMTEncoding_Term.DeclFun (((ttok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("token"))))
in (

let ttok_fresh = (let _183_2274 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ttok), (FStar_SMTEncoding_Term.Term_sort)) _183_2274))
in (

let ttok_app = (mk_Apply ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (let _183_2278 = (let _183_2277 = (let _183_2276 = (let _183_2275 = (FStar_SMTEncoding_Util.mkEq ((ttok_app), (tapp)))
in ((pats), (None), (vars), (_183_2275)))
in (FStar_SMTEncoding_Util.mkForall' _183_2276))
in ((_183_2277), (Some ("name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" ttok)))))
in FStar_SMTEncoding_Term.Assume (_183_2278))
in (((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[]), (env)))))))
end)
in (match (_88_2980) with
| (tok_decls, env) -> begin
(((FStar_List.append tname_decl tok_decls)), (env))
end)))
in (match (_88_2983) with
| (decls, env) -> begin
(

let kindingAx = (

let _88_2986 = (encode_term_pred None res env' tapp)
in (match (_88_2986) with
| (k, decls) -> begin
(

let karr = if ((FStar_List.length formals) > (Prims.parse_int "0")) then begin
(let _183_2282 = (let _183_2281 = (let _183_2280 = (let _183_2279 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _183_2279))
in ((_183_2280), (Some ("kinding")), (Some ((Prims.strcat "pre_kinding_" ttok)))))
in FStar_SMTEncoding_Term.Assume (_183_2281))
in (_183_2282)::[])
end else begin
[]
end
in (let _183_2289 = (let _183_2288 = (let _183_2287 = (let _183_2286 = (let _183_2285 = (let _183_2284 = (let _183_2283 = (FStar_SMTEncoding_Util.mkImp ((guard), (k)))
in ((((tapp)::[])::[]), (vars), (_183_2283)))
in (FStar_SMTEncoding_Util.mkForall _183_2284))
in ((_183_2285), (None), (Some ((Prims.strcat "kinding_" ttok)))))
in FStar_SMTEncoding_Term.Assume (_183_2286))
in (_183_2287)::[])
in (FStar_List.append karr _183_2288))
in (FStar_List.append decls _183_2289)))
end))
in (

let aux = (let _183_2293 = (let _183_2292 = (inversion_axioms tapp vars)
in (let _183_2291 = (let _183_2290 = (pretype_axiom tapp vars)
in (_183_2290)::[])
in (FStar_List.append _183_2292 _183_2291)))
in (FStar_List.append kindingAx _183_2293))
in (

let g = (FStar_List.append decls (FStar_List.append binder_decls aux))
in ((g), (env)))))
end)))))
end))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, _88_2993, _88_2995, _88_2997, _88_2999, _88_3001, _88_3003, _88_3005) when (FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_datacon (d, _88_3010, t, _88_3013, n_tps, quals, _88_3017, drange) -> begin
(

let _88_3024 = (new_term_constant_and_tok_from_lid env d)
in (match (_88_3024) with
| (ddconstrsym, ddtok, env) -> begin
(

let ddtok_tm = (FStar_SMTEncoding_Util.mkApp ((ddtok), ([])))
in (

let _88_3028 = (FStar_Syntax_Util.arrow_formals t)
in (match (_88_3028) with
| (formals, t_res) -> begin
(

let _88_3031 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_88_3031) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (

let _88_3038 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_88_3038) with
| (vars, guards, env', binder_decls, names) -> begin
(

let projectors = (FStar_All.pipe_right names (FStar_List.map (fun x -> (let _183_2295 = (mk_term_projector_name d x)
in ((_183_2295), (FStar_SMTEncoding_Term.Term_sort))))))
in (

let datacons = (let _183_2297 = (let _183_2296 = (varops.next_id ())
in ((ddconstrsym), (projectors), (FStar_SMTEncoding_Term.Term_sort), (_183_2296), (true)))
in (FStar_All.pipe_right _183_2297 FStar_SMTEncoding_Term.constructor_to_decl))
in (

let app = (mk_Apply ddtok_tm vars)
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (

let _88_3048 = (encode_term_pred None t env ddtok_tm)
in (match (_88_3048) with
| (tok_typing, decls3) -> begin
(

let _88_3055 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_88_3055) with
| (vars', guards', env'', decls_formals, _88_3054) -> begin
(

let _88_3060 = (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars')
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (encode_term_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_88_3060) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_SMTEncoding_Util.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _88_3064 -> begin
(let _183_2299 = (let _183_2298 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ddtok), (FStar_SMTEncoding_Term.Term_sort)) _183_2298))
in (_183_2299)::[])
end)
in (

let encode_elim = (fun _88_3067 -> (match (()) with
| () -> begin
(

let _88_3070 = (FStar_Syntax_Util.head_and_args t_res)
in (match (_88_3070) with
| (head, args) -> begin
(match ((let _183_2302 = (FStar_Syntax_Subst.compress head)
in _183_2302.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let _88_3088 = (encode_args args env')
in (match (_88_3088) with
| (encoded_args, arg_decls) -> begin
(

let _88_3103 = (FStar_List.fold_left (fun _88_3092 arg -> (match (_88_3092) with
| (env, arg_vars, eqns) -> begin
(

let _88_3098 = (let _183_2305 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in (gen_term_var env _183_2305))
in (match (_88_3098) with
| (_88_3095, xv, env) -> begin
(let _183_2307 = (let _183_2306 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (_183_2306)::eqns)
in ((env), ((xv)::arg_vars), (_183_2307)))
end))
end)) ((env'), ([]), ([])) encoded_args)
in (match (_88_3103) with
| (_88_3100, arg_vars, eqns) -> begin
(

let arg_vars = (FStar_List.rev arg_vars)
in (

let ty = (FStar_SMTEncoding_Util.mkApp ((encoded_head), (arg_vars)))
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (

let ty_pred = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp ty)
in (

let arg_binders = (FStar_List.map FStar_SMTEncoding_Term.fv_of_term arg_vars)
in (

let typing_inversion = (let _183_2314 = (let _183_2313 = (let _183_2312 = (let _183_2311 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (let _183_2310 = (let _183_2309 = (let _183_2308 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append eqns guards))
in ((ty_pred), (_183_2308)))
in (FStar_SMTEncoding_Util.mkImp _183_2309))
in ((((ty_pred)::[])::[]), (_183_2311), (_183_2310))))
in (FStar_SMTEncoding_Util.mkForall _183_2312))
in ((_183_2313), (Some ("data constructor typing elim")), (Some ((Prims.strcat "data_elim_" ddconstrsym)))))
in FStar_SMTEncoding_Term.Assume (_183_2314))
in (

let subterm_ordering = if (FStar_Ident.lid_equals d FStar_Syntax_Const.lextop_lid) then begin
(

let x = (let _183_2315 = (varops.fresh "x")
in ((_183_2315), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (let _183_2327 = (let _183_2326 = (let _183_2323 = (let _183_2322 = (let _183_2317 = (let _183_2316 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp)
in (_183_2316)::[])
in (_183_2317)::[])
in (let _183_2321 = (let _183_2320 = (let _183_2319 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (let _183_2318 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp)
in ((_183_2319), (_183_2318))))
in (FStar_SMTEncoding_Util.mkImp _183_2320))
in ((_183_2322), ((x)::[]), (_183_2321))))
in (FStar_SMTEncoding_Util.mkForall _183_2323))
in (let _183_2325 = (let _183_2324 = (varops.mk_unique "lextop")
in Some (_183_2324))
in ((_183_2326), (Some ("lextop is top")), (_183_2325))))
in FStar_SMTEncoding_Term.Assume (_183_2327))))
end else begin
(

let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
[]
end
| FStar_SMTEncoding_Term.Term_sort -> begin
(let _183_2330 = (let _183_2329 = (FStar_SMTEncoding_Util.mkFreeV v)
in (FStar_SMTEncoding_Util.mk_Precedes _183_2329 dapp))
in (_183_2330)::[])
end
| _88_3117 -> begin
(FStar_All.failwith "unexpected sort")
end))))
in (let _183_2337 = (let _183_2336 = (let _183_2335 = (let _183_2334 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (let _183_2333 = (let _183_2332 = (let _183_2331 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (_183_2331)))
in (FStar_SMTEncoding_Util.mkImp _183_2332))
in ((((ty_pred)::[])::[]), (_183_2334), (_183_2333))))
in (FStar_SMTEncoding_Util.mkForall _183_2335))
in ((_183_2336), (Some ("subterm ordering")), (Some ((Prims.strcat "subterm_ordering_" ddconstrsym)))))
in FStar_SMTEncoding_Term.Assume (_183_2337)))
end
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end))
end)))
end
| _88_3121 -> begin
(

let _88_3122 = (let _183_2340 = (let _183_2339 = (FStar_Syntax_Print.lid_to_string d)
in (let _183_2338 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _183_2339 _183_2338)))
in (FStar_TypeChecker_Errors.warn drange _183_2340))
in (([]), ([])))
end)
end))
end))
in (

let _88_3126 = (encode_elim ())
in (match (_88_3126) with
| (decls2, elim) -> begin
(

let g = (let _183_2367 = (let _183_2366 = (let _183_2365 = (let _183_2364 = (let _183_2345 = (let _183_2344 = (let _183_2343 = (let _183_2342 = (let _183_2341 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" _183_2341))
in Some (_183_2342))
in ((ddtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (_183_2343)))
in FStar_SMTEncoding_Term.DeclFun (_183_2344))
in (_183_2345)::[])
in (let _183_2363 = (let _183_2362 = (let _183_2361 = (let _183_2360 = (let _183_2359 = (let _183_2358 = (let _183_2357 = (let _183_2349 = (let _183_2348 = (let _183_2347 = (let _183_2346 = (FStar_SMTEncoding_Util.mkEq ((app), (dapp)))
in ((((app)::[])::[]), (vars), (_183_2346)))
in (FStar_SMTEncoding_Util.mkForall _183_2347))
in ((_183_2348), (Some ("equality for proxy")), (Some ((Prims.strcat "equality_tok_" ddtok)))))
in FStar_SMTEncoding_Term.Assume (_183_2349))
in (let _183_2356 = (let _183_2355 = (let _183_2354 = (let _183_2353 = (let _183_2352 = (let _183_2351 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) vars')
in (let _183_2350 = (FStar_SMTEncoding_Util.mkImp ((guard'), (ty_pred')))
in ((((ty_pred')::[])::[]), (_183_2351), (_183_2350))))
in (FStar_SMTEncoding_Util.mkForall _183_2352))
in ((_183_2353), (Some ("data constructor typing intro")), (Some ((Prims.strcat "data_typing_intro_" ddtok)))))
in FStar_SMTEncoding_Term.Assume (_183_2354))
in (_183_2355)::[])
in (_183_2357)::_183_2356))
in (FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("typing for data constructor proxy")), (Some ((Prims.strcat "typing_tok_" ddtok))))))::_183_2358)
in (FStar_List.append _183_2359 elim))
in (FStar_List.append decls_pred _183_2360))
in (FStar_List.append decls_formals _183_2361))
in (FStar_List.append proxy_fresh _183_2362))
in (FStar_List.append _183_2364 _183_2363)))
in (FStar_List.append decls3 _183_2365))
in (FStar_List.append decls2 _183_2366))
in (FStar_List.append binder_decls _183_2367))
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
and encode_signature : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _88_3132 se -> (match (_88_3132) with
| (g, env) -> begin
(

let _88_3136 = (encode_sigelt env se)
in (match (_88_3136) with
| (g', env) -> begin
(((FStar_List.append g g')), (env))
end))
end)) (([]), (env)))))


let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env bindings -> (

let encode_binding = (fun b _88_3144 -> (match (_88_3144) with
| (i, decls, env) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (_88_3146) -> begin
(((i + (Prims.parse_int "1"))), ([]), (env))
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (

let _88_3151 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _183_2382 = (FStar_Syntax_Print.bv_to_string x)
in (let _183_2381 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _183_2380 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" _183_2382 _183_2381 _183_2380))))
end else begin
()
end
in (

let _88_3155 = (encode_term t1 env)
in (match (_88_3155) with
| (t, decls') -> begin
(

let t_hash = (FStar_SMTEncoding_Term.hash_of_term t)
in (

let _88_3160 = (let _183_2387 = (let _183_2386 = (let _183_2385 = (FStar_Util.digest_of_string t_hash)
in (let _183_2384 = (let _183_2383 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _183_2383))
in (Prims.strcat _183_2385 _183_2384)))
in (Prims.strcat "x_" _183_2386))
in (new_term_constant_from_string env x _183_2387))
in (match (_88_3160) with
| (xxsym, xx, env') -> begin
(

let t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel None xx t)
in (

let caption = if (FStar_Options.log_queries ()) then begin
(let _183_2391 = (let _183_2390 = (FStar_Syntax_Print.bv_to_string x)
in (let _183_2389 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _183_2388 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _183_2390 _183_2389 _183_2388))))
in Some (_183_2391))
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
end)))
end))))
end
| FStar_TypeChecker_Env.Binding_lid (x, (_88_3168, t)) -> begin
(

let t_norm = (whnf env t)
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant None)
in (

let _88_3177 = (encode_free_var env fv t t_norm [])
in (match (_88_3177) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))))
end
| (FStar_TypeChecker_Env.Binding_sig_inst (_, se, _)) | (FStar_TypeChecker_Env.Binding_sig (_, se)) -> begin
(

let _88_3191 = (encode_sigelt env se)
in (match (_88_3191) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))
end)
end))
in (

let _88_3196 = (FStar_List.fold_right encode_binding bindings (((Prims.parse_int "0")), ([]), (env)))
in (match (_88_3196) with
| (_88_3193, decls, env) -> begin
((decls), (env))
end))))


let encode_labels = (fun labs -> (

let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _88_3203 -> (match (_88_3203) with
| (l, _88_3200, _88_3202) -> begin
FStar_SMTEncoding_Term.DeclFun ((((Prims.fst l)), ([]), (FStar_SMTEncoding_Term.Bool_sort), (None)))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _88_3210 -> (match (_88_3210) with
| (l, _88_3207, _88_3209) -> begin
(let _183_2399 = (FStar_All.pipe_left (fun _183_2395 -> FStar_SMTEncoding_Term.Echo (_183_2395)) (Prims.fst l))
in (let _183_2398 = (let _183_2397 = (let _183_2396 = (FStar_SMTEncoding_Util.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (_183_2396))
in (_183_2397)::[])
in (_183_2399)::_183_2398))
end))))
in ((prefix), (suffix)))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (let _183_2404 = (let _183_2403 = (let _183_2402 = (FStar_Util.smap_create (Prims.parse_int "100"))
in {bindings = []; depth = (Prims.parse_int "0"); tcenv = tcenv; warn = true; cache = _183_2402; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_183_2403)::[])
in (FStar_ST.op_Colon_Equals last_env _183_2404)))


let get_env : FStar_TypeChecker_Env.env  ->  env_t = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "No env; call init first!")
end
| (e)::_88_3216 -> begin
(

let _88_3219 = e
in {bindings = _88_3219.bindings; depth = _88_3219.depth; tcenv = tcenv; warn = _88_3219.warn; cache = _88_3219.cache; nolabels = _88_3219.nolabels; use_zfuel_name = _88_3219.use_zfuel_name; encode_non_total_function_typ = _88_3219.encode_non_total_function_typ})
end))


let set_env : env_t  ->  Prims.unit = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| (_88_3225)::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))


let push_env : Prims.unit  ->  Prims.unit = (fun _88_3227 -> (match (()) with
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

let _88_3233 = hd
in {bindings = _88_3233.bindings; depth = _88_3233.depth; tcenv = _88_3233.tcenv; warn = _88_3233.warn; cache = refs; nolabels = _88_3233.nolabels; use_zfuel_name = _88_3233.use_zfuel_name; encode_non_total_function_typ = _88_3233.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))


let pop_env : Prims.unit  ->  Prims.unit = (fun _88_3236 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Popping an empty stack")
end
| (_88_3240)::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))


let mark_env : Prims.unit  ->  Prims.unit = (fun _88_3242 -> (match (()) with
| () -> begin
(push_env ())
end))


let reset_mark_env : Prims.unit  ->  Prims.unit = (fun _88_3243 -> (match (()) with
| () -> begin
(pop_env ())
end))


let commit_mark_env : Prims.unit  ->  Prims.unit = (fun _88_3244 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| (hd)::(_88_3247)::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _88_3252 -> begin
(FStar_All.failwith "Impossible")
end)
end))


let init : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (

let _88_3254 = (init_env tcenv)
in (

let _88_3256 = (FStar_SMTEncoding_Z3.init ())
in (FStar_SMTEncoding_Z3.giveZ3 ((FStar_SMTEncoding_Term.DefPrelude)::[])))))


let push : Prims.string  ->  Prims.unit = (fun msg -> (

let _88_3259 = (push_env ())
in (

let _88_3261 = (varops.push ())
in (FStar_SMTEncoding_Z3.push msg))))


let pop : Prims.string  ->  Prims.unit = (fun msg -> (

let _88_3264 = (let _183_2425 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _183_2425))
in (

let _88_3266 = (varops.pop ())
in (FStar_SMTEncoding_Z3.pop msg))))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _88_3269 = (mark_env ())
in (

let _88_3271 = (varops.mark ())
in (FStar_SMTEncoding_Z3.mark msg))))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _88_3274 = (reset_mark_env ())
in (

let _88_3276 = (varops.reset_mark ())
in (FStar_SMTEncoding_Z3.reset_mark msg))))


let commit_mark = (fun msg -> (

let _88_3279 = (commit_mark_env ())
in (

let _88_3281 = (varops.commit_mark ())
in (FStar_SMTEncoding_Z3.commit_mark msg))))


let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (

let caption = (fun decls -> if (FStar_Options.log_queries ()) then begin
(let _183_2441 = (let _183_2440 = (let _183_2439 = (let _183_2438 = (let _183_2437 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _183_2437 (FStar_List.map FStar_Syntax_Print.lid_to_string)))
in (FStar_All.pipe_right _183_2438 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " _183_2439))
in FStar_SMTEncoding_Term.Caption (_183_2440))
in (_183_2441)::decls)
end else begin
decls
end)
in (

let env = (get_env tcenv)
in (

let _88_3290 = (encode_sigelt env se)
in (match (_88_3290) with
| (decls, env) -> begin
(

let _88_3291 = (set_env env)
in (let _183_2442 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 _183_2442)))
end)))))


let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let _88_3296 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(let _183_2447 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name _183_2447))
end else begin
()
end
in (

let env = (get_env tcenv)
in (

let _88_3303 = (encode_signature (

let _88_3299 = env
in {bindings = _88_3299.bindings; depth = _88_3299.depth; tcenv = _88_3299.tcenv; warn = false; cache = _88_3299.cache; nolabels = _88_3299.nolabels; use_zfuel_name = _88_3299.use_zfuel_name; encode_non_total_function_typ = _88_3299.encode_non_total_function_typ}) modul.FStar_Syntax_Syntax.exports)
in (match (_88_3303) with
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

let _88_3309 = (set_env (

let _88_3307 = env
in {bindings = _88_3307.bindings; depth = _88_3307.depth; tcenv = _88_3307.tcenv; warn = true; cache = _88_3307.cache; nolabels = _88_3307.nolabels; use_zfuel_name = _88_3307.use_zfuel_name; encode_non_total_function_typ = _88_3307.encode_non_total_function_typ}))
in (

let _88_3311 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end else begin
()
end
in (

let decls = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls)))))
end))))))


let encode_query : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_ErrorReporting.label Prims.list * FStar_SMTEncoding_Term.decl * FStar_SMTEncoding_Term.decl Prims.list) = (fun use_env_msg tcenv q -> (

let _88_3317 = (let _183_2465 = (let _183_2464 = (FStar_TypeChecker_Env.current_module tcenv)
in _183_2464.FStar_Ident.str)
in (FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name _183_2465))
in (

let env = (get_env tcenv)
in (

let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (

let _88_3342 = (

let rec aux = (fun bindings -> (match (bindings) with
| (FStar_TypeChecker_Env.Binding_var (x))::rest -> begin
(

let _88_3331 = (aux rest)
in (match (_88_3331) with
| (out, rest) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (let _183_2471 = (let _183_2470 = (FStar_Syntax_Syntax.mk_binder (

let _88_3333 = x
in {FStar_Syntax_Syntax.ppname = _88_3333.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _88_3333.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_183_2470)::out)
in ((_183_2471), (rest))))
end))
end
| _88_3336 -> begin
(([]), (bindings))
end))
in (

let _88_3339 = (aux bindings)
in (match (_88_3339) with
| (closing, bindings) -> begin
(let _183_2472 = (FStar_Syntax_Util.close_forall (FStar_List.rev closing) q)
in ((_183_2472), (bindings)))
end)))
in (match (_88_3342) with
| (q, bindings) -> begin
(

let _88_3351 = (let _183_2474 = (FStar_List.filter (fun _88_24 -> (match (_88_24) with
| FStar_TypeChecker_Env.Binding_sig (_88_3345) -> begin
false
end
| _88_3348 -> begin
true
end)) bindings)
in (encode_env_bindings env _183_2474))
in (match (_88_3351) with
| (env_decls, env) -> begin
(

let _88_3352 = if (((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTQuery")))) then begin
(let _183_2475 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" _183_2475))
end else begin
()
end
in (

let _88_3356 = (encode_formula q env)
in (match (_88_3356) with
| (phi, qdecls) -> begin
(

let _88_3361 = (let _183_2476 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg _183_2476 phi))
in (match (_88_3361) with
| (phi, labels, _88_3360) -> begin
(

let _88_3364 = (encode_labels labels)
in (match (_88_3364) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append env_decls (FStar_List.append label_prefix qdecls))
in (

let qry = (let _183_2480 = (let _183_2479 = (FStar_SMTEncoding_Util.mkNot phi)
in (let _183_2478 = (let _183_2477 = (varops.mk_unique "@query")
in Some (_183_2477))
in ((_183_2479), (Some ("query")), (_183_2478))))
in FStar_SMTEncoding_Term.Assume (_183_2480))
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

let _88_3371 = (push "query")
in (

let _88_3376 = (encode_formula q env)
in (match (_88_3376) with
| (f, _88_3375) -> begin
(

let _88_3377 = (pop "query")
in (match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _88_3381) -> begin
true
end
| _88_3385 -> begin
false
end))
end)))))




