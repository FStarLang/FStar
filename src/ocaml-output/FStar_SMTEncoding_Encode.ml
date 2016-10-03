
open Prims

let add_fuel = (fun x tl -> if (FStar_Options.unthrottle_inductives ()) then begin
tl
end else begin
(x)::tl
end)


let withenv = (fun c _90_30 -> (match (_90_30) with
| (a, b) -> begin
((a), (b), (c))
end))


let vargs = (fun args -> (FStar_List.filter (fun _90_1 -> (match (_90_1) with
| (FStar_Util.Inl (_90_34), _90_37) -> begin
false
end
| _90_40 -> begin
true
end)) args))


let subst_lcomp_opt = (fun s l -> (match (l) with
| Some (FStar_Util.Inl (l)) -> begin
(let _187_12 = (let _187_11 = (let _187_10 = (let _187_9 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp s _187_9))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _187_10))
in FStar_Util.Inl (_187_11))
in Some (_187_12))
end
| _90_47 -> begin
l
end))


let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s '\'' '_'))


let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun lid a -> (

let a = (

let _90_51 = a
in (let _187_19 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _187_19; FStar_Syntax_Syntax.index = _90_51.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _90_51.FStar_Syntax_Syntax.sort}))
in (let _187_20 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str a.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (FStar_All.pipe_left escape _187_20))))


let primitive_projector_by_pos : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (

let fail = (fun _90_58 -> (match (()) with
| () -> begin
(let _187_30 = (let _187_29 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" _187_29 lid.FStar_Ident.str))
in (FStar_All.failwith _187_30))
end))
in (

let _90_62 = (FStar_TypeChecker_Env.lookup_datacon env lid)
in (match (_90_62) with
| (_90_60, t) -> begin
(match ((let _187_31 = (FStar_Syntax_Subst.compress t)
in _187_31.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _90_70 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_90_70) with
| (binders, _90_69) -> begin
if ((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(

let b = (FStar_List.nth binders i)
in (mk_term_projector_name lid (Prims.fst b)))
end
end))
end
| _90_73 -> begin
(fail ())
end)
end))))


let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (let _187_37 = (let _187_36 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str _187_36))
in (FStar_All.pipe_left escape _187_37)))


let mk_term_projector : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun lid a -> (let _187_43 = (let _187_42 = (mk_term_projector_name lid a)
in ((_187_42), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Term.mkFreeV _187_43)))


let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_SMTEncoding_Term.term = (fun lid i -> (let _187_49 = (let _187_48 = (mk_term_projector_name_by_pos lid i)
in ((_187_48), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Term.mkFreeV _187_49)))


let mk_data_tester = (fun env l x -> (FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x))


type varops_t =
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; mark : Prims.unit  ->  Prims.unit; reset_mark : Prims.unit  ->  Prims.unit; commit_mark : Prims.unit  ->  Prims.unit; new_var : FStar_Ident.ident  ->  Prims.int  ->  Prims.string; new_fvar : FStar_Ident.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_SMTEncoding_Term.term; next_id : Prims.unit  ->  Prims.int; mk_unique : Prims.string  ->  Prims.string}


let is_Mkvarops_t : varops_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkvarops_t"))))


let varops : varops_t = (

let initial_ctr = (Prims.parse_int "100")
in (

let ctr = (FStar_Util.mk_ref initial_ctr)
in (

let new_scope = (fun _90_98 -> (match (()) with
| () -> begin
(let _187_162 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (let _187_161 = (FStar_Util.smap_create (Prims.parse_int "100"))
in ((_187_162), (_187_161))))
end))
in (

let scopes = (let _187_164 = (let _187_163 = (new_scope ())
in (_187_163)::[])
in (FStar_Util.mk_ref _187_164))
in (

let mk_unique = (fun y -> (

let y = (escape y)
in (

let y = (match ((let _187_168 = (FStar_ST.read scopes)
in (FStar_Util.find_map _187_168 (fun _90_106 -> (match (_90_106) with
| (names, _90_105) -> begin
(FStar_Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_90_109) -> begin
(

let _90_111 = (FStar_Util.incr ctr)
in (let _187_171 = (let _187_170 = (let _187_169 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _187_169))
in (Prims.strcat "__" _187_170))
in (Prims.strcat y _187_171)))
end)
in (

let top_scope = (let _187_173 = (let _187_172 = (FStar_ST.read scopes)
in (FStar_List.hd _187_172))
in (FStar_All.pipe_left Prims.fst _187_173))
in (

let _90_115 = (FStar_Util.smap_add top_scope y true)
in y)))))
in (

let new_var = (fun pp rn -> (let _187_180 = (let _187_179 = (let _187_178 = (FStar_Util.string_of_int rn)
in (Prims.strcat "__" _187_178))
in (Prims.strcat pp.FStar_Ident.idText _187_179))
in (FStar_All.pipe_left mk_unique _187_180)))
in (

let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (

let next_id = (fun _90_123 -> (match (()) with
| () -> begin
(

let _90_124 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end))
in (

let fresh = (fun pfx -> (let _187_188 = (let _187_187 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _187_187))
in (FStar_Util.format2 "%s_%s" pfx _187_188)))
in (

let string_const = (fun s -> (match ((let _187_192 = (FStar_ST.read scopes)
in (FStar_Util.find_map _187_192 (fun _90_133 -> (match (_90_133) with
| (_90_131, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))) with
| Some (f) -> begin
f
end
| None -> begin
(

let id = (next_id ())
in (

let f = (let _187_193 = (FStar_SMTEncoding_Term.mk_String_const id)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString _187_193))
in (

let top_scope = (let _187_195 = (let _187_194 = (FStar_ST.read scopes)
in (FStar_List.hd _187_194))
in (FStar_All.pipe_left Prims.snd _187_195))
in (

let _90_140 = (FStar_Util.smap_add top_scope s f)
in f))))
end))
in (

let push = (fun _90_143 -> (match (()) with
| () -> begin
(let _187_200 = (let _187_199 = (new_scope ())
in (let _187_198 = (FStar_ST.read scopes)
in (_187_199)::_187_198))
in (FStar_ST.op_Colon_Equals scopes _187_200))
end))
in (

let pop = (fun _90_145 -> (match (()) with
| () -> begin
(let _187_204 = (let _187_203 = (FStar_ST.read scopes)
in (FStar_List.tl _187_203))
in (FStar_ST.op_Colon_Equals scopes _187_204))
end))
in (

let mark = (fun _90_147 -> (match (()) with
| () -> begin
(push ())
end))
in (

let reset_mark = (fun _90_149 -> (match (()) with
| () -> begin
(pop ())
end))
in (

let commit_mark = (fun _90_151 -> (match (()) with
| () -> begin
(match ((FStar_ST.read scopes)) with
| ((hd1, hd2))::((next1, next2))::tl -> begin
(

let _90_164 = (FStar_Util.smap_fold hd1 (fun key value v -> (FStar_Util.smap_add next1 key value)) ())
in (

let _90_169 = (FStar_Util.smap_fold hd2 (fun key value v -> (FStar_Util.smap_add next2 key value)) ())
in (FStar_ST.op_Colon_Equals scopes ((((next1), (next2)))::tl))))
end
| _90_172 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id; mk_unique = mk_unique})))))))))))))))


let unmangle : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv = (fun x -> (

let _90_174 = x
in (let _187_219 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _187_219; FStar_Syntax_Syntax.index = _90_174.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _90_174.FStar_Syntax_Syntax.sort})))


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
| Binding_var (_90_178) -> begin
_90_178
end))


let ___Binding_fvar____0 = (fun projectee -> (match (projectee) with
| Binding_fvar (_90_181) -> begin
_90_181
end))


let binder_of_eithervar = (fun v -> ((v), (None)))


type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_TypeChecker_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_SMTEncoding_Term.sort Prims.list * FStar_SMTEncoding_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}


let is_Mkenv_t : env_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_t"))))


let print_env : env_t  ->  Prims.string = (fun e -> (let _187_277 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun _90_2 -> (match (_90_2) with
| Binding_var (x, _90_196) -> begin
(FStar_Syntax_Print.bv_to_string x)
end
| Binding_fvar (l, _90_201, _90_203, _90_205) -> begin
(FStar_Syntax_Print.lid_to_string l)
end))))
in (FStar_All.pipe_right _187_277 (FStar_String.concat ", "))))


let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))


let caption_t : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.string Prims.option = (fun env t -> if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _187_287 = (FStar_Syntax_Print.term_to_string t)
in Some (_187_287))
end else begin
None
end)


let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (

let xsym = (varops.fresh x)
in (let _187_292 = (FStar_SMTEncoding_Term.mkFreeV ((xsym), (s)))
in ((xsym), (_187_292)))))


let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (let _187_297 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _187_297))
in (

let y = (FStar_SMTEncoding_Term.mkFreeV ((ysym), (FStar_SMTEncoding_Term.Term_sort)))
in ((ysym), (y), ((

let _90_219 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = (env.depth + (Prims.parse_int "1")); tcenv = _90_219.tcenv; warn = _90_219.warn; cache = _90_219.cache; nolabels = _90_219.nolabels; use_zfuel_name = _90_219.use_zfuel_name; encode_non_total_function_typ = _90_219.encode_non_total_function_typ}))))))


let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (

let y = (FStar_SMTEncoding_Term.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let _90_225 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = _90_225.depth; tcenv = _90_225.tcenv; warn = _90_225.warn; cache = _90_225.cache; nolabels = _90_225.nolabels; use_zfuel_name = _90_225.use_zfuel_name; encode_non_total_function_typ = _90_225.encode_non_total_function_typ}))))))


let new_term_constant_from_string : env_t  ->  FStar_Syntax_Syntax.bv  ->  Prims.string  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x str -> (

let ysym = (varops.mk_unique str)
in (

let y = (FStar_SMTEncoding_Term.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let _90_232 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = _90_232.depth; tcenv = _90_232.tcenv; warn = _90_232.warn; cache = _90_232.cache; nolabels = _90_232.nolabels; use_zfuel_name = _90_232.use_zfuel_name; encode_non_total_function_typ = _90_232.encode_non_total_function_typ}))))))


let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (

let _90_237 = env
in {bindings = (Binding_var (((x), (t))))::env.bindings; depth = _90_237.depth; tcenv = _90_237.tcenv; warn = _90_237.warn; cache = _90_237.cache; nolabels = _90_237.nolabels; use_zfuel_name = _90_237.use_zfuel_name; encode_non_total_function_typ = _90_237.encode_non_total_function_typ}))


let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let aux = (fun a' -> (lookup_binding env (fun _90_3 -> (match (_90_3) with
| Binding_var (b, t) when (FStar_Syntax_Syntax.bv_eq b a') -> begin
Some (((b), (t)))
end
| _90_249 -> begin
None
end))))
in (match ((aux a)) with
| None -> begin
(

let a = (unmangle a)
in (match ((aux a)) with
| None -> begin
(let _187_322 = (let _187_321 = (FStar_Syntax_Print.bv_to_string a)
in (FStar_Util.format1 "Bound term variable not found (after unmangling): %s" _187_321))
in (FStar_All.failwith _187_322))
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
in (let _187_333 = (

let _90_265 = env
in (let _187_332 = (let _187_331 = (let _187_330 = (let _187_329 = (let _187_328 = (FStar_SMTEncoding_Term.mkApp ((ftok), ([])))
in (FStar_All.pipe_left (fun _187_327 -> Some (_187_327)) _187_328))
in ((x), (fname), (_187_329), (None)))
in Binding_fvar (_187_330))
in (_187_331)::env.bindings)
in {bindings = _187_332; depth = _90_265.depth; tcenv = _90_265.tcenv; warn = _90_265.warn; cache = _90_265.cache; nolabels = _90_265.nolabels; use_zfuel_name = _90_265.use_zfuel_name; encode_non_total_function_typ = _90_265.encode_non_total_function_typ}))
in ((fname), (ftok), (_187_333))))))


let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun _90_4 -> (match (_90_4) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some (((t1), (t2), (t3)))
end
| _90_277 -> begin
None
end))))


let contains_name : env_t  ->  Prims.string  ->  Prims.bool = (fun env s -> (let _187_344 = (lookup_binding env (fun _90_5 -> (match (_90_5) with
| Binding_fvar (b, t1, t2, t3) when (b.FStar_Ident.str = s) -> begin
Some (())
end
| _90_288 -> begin
None
end)))
in (FStar_All.pipe_right _187_344 FStar_Option.isSome)))


let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _187_350 = (let _187_349 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" _187_349))
in (FStar_All.failwith _187_350))
end
| Some (s) -> begin
s
end))


let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (

let _90_298 = env
in {bindings = (Binding_fvar (((x), (fname), (ftok), (None))))::env.bindings; depth = _90_298.depth; tcenv = _90_298.tcenv; warn = _90_298.warn; cache = _90_298.cache; nolabels = _90_298.nolabels; use_zfuel_name = _90_298.use_zfuel_name; encode_non_total_function_typ = _90_298.encode_non_total_function_typ}))


let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (

let _90_307 = (lookup_lid env x)
in (match (_90_307) with
| (t1, t2, _90_306) -> begin
(

let t3 = (let _187_367 = (let _187_366 = (let _187_365 = (FStar_SMTEncoding_Term.mkApp (("ZFuel"), ([])))
in (_187_365)::[])
in ((f), (_187_366)))
in (FStar_SMTEncoding_Term.mkApp _187_367))
in (

let _90_309 = env
in {bindings = (Binding_fvar (((x), (t1), (t2), (Some (t3)))))::env.bindings; depth = _90_309.depth; tcenv = _90_309.tcenv; warn = _90_309.warn; cache = _90_309.cache; nolabels = _90_309.nolabels; use_zfuel_name = _90_309.use_zfuel_name; encode_non_total_function_typ = _90_309.encode_non_total_function_typ}))
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
| _90_322 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (_90_326, (fuel)::[]) -> begin
if (let _187_373 = (let _187_372 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right _187_372 Prims.fst))
in (FStar_Util.starts_with _187_373 "fuel")) then begin
(let _187_376 = (let _187_375 = (FStar_SMTEncoding_Term.mkFreeV ((name), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_ApplyTF _187_375 fuel))
in (FStar_All.pipe_left (fun _187_374 -> Some (_187_374)) _187_376))
end else begin
Some (t)
end
end
| _90_332 -> begin
Some (t)
end)
end
| _90_334 -> begin
None
end)
end)
end))


let lookup_free_var = (fun env a -> (match ((try_lookup_free_var env a.FStar_Syntax_Syntax.v)) with
| Some (t) -> begin
t
end
| None -> begin
(let _187_380 = (let _187_379 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _187_379))
in (FStar_All.failwith _187_380))
end))


let lookup_free_var_name = (fun env a -> (

let _90_347 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_90_347) with
| (x, _90_344, _90_346) -> begin
x
end)))


let lookup_free_var_sym = (fun env a -> (

let _90_353 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_90_353) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.hash = _90_357; FStar_SMTEncoding_Term.freevars = _90_355}) when env.use_zfuel_name -> begin
((g), (zf))
end
| _90_365 -> begin
(match (sym) with
| None -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end
| Some (sym) -> begin
(match (sym.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, (fuel)::[]) -> begin
((g), ((fuel)::[]))
end
| _90_375 -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end)
end)
end)
end)))


let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun _90_6 -> (match (_90_6) with
| Binding_fvar (_90_380, nm', tok, _90_384) when (nm = nm') -> begin
tok
end
| _90_388 -> begin
None
end))))


let mkForall_fuel' = (fun n _90_393 -> (match (_90_393) with
| (pats, vars, body) -> begin
(

let fallback = (fun _90_395 -> (match (()) with
| () -> begin
(FStar_SMTEncoding_Term.mkForall ((pats), (vars), (body)))
end))
in if (FStar_Options.unthrottle_inductives ()) then begin
(fallback ())
end else begin
(

let _90_398 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_90_398) with
| (fsym, fterm) -> begin
(

let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Term.mkApp (("HasTypeFuel"), ((fterm)::args)))
end
| _90_408 -> begin
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
(let _187_397 = (add_fuel guards)
in (FStar_SMTEncoding_Term.mk_and_l _187_397))
end
| _90_421 -> begin
(let _187_398 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _187_398 FStar_List.hd))
end)
in (FStar_SMTEncoding_Term.mkImp ((guard), (body'))))
end
| _90_424 -> begin
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
(let _187_404 = (FStar_TypeChecker_Env.lookup_definition FStar_TypeChecker_Env.OnlyInline env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _187_404 FStar_Option.isNone))
end
| _90_463 -> begin
false
end)))


let head_redex : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (match ((let _187_409 = (FStar_Syntax_Util.un_uinst t)
in _187_409.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_90_467) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(let _187_410 = (FStar_TypeChecker_Env.lookup_definition FStar_TypeChecker_Env.OnlyInline env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _187_410 FStar_Option.isSome))
end
| _90_472 -> begin
false
end))


let whnf : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> if (head_normal env t) then begin
t
end else begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
end)


let norm : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t))


let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (let _187_423 = (let _187_421 = (FStar_Syntax_Syntax.null_binder t)
in (_187_421)::[])
in (let _187_422 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Util.abs _187_423 _187_422 None))))


let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(let _187_430 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out _187_430))
end
| s -> begin
(

let _90_484 = ()
in (let _187_431 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTT out _187_431)))
end)) e)))


let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Term.mk_ApplyTT e)))


let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun _90_7 -> (match (_90_7) with
| (FStar_SMTEncoding_Term.Var ("ApplyTT")) | (FStar_SMTEncoding_Term.Var ("ApplyTF")) -> begin
true
end
| _90_494 -> begin
false
end))


let is_eta : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env vars t -> (

let rec aux = (fun t xs -> (match (((t.FStar_SMTEncoding_Term.tm), (xs))) with
| (FStar_SMTEncoding_Term.App (app, (f)::({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.hash = _90_505; FStar_SMTEncoding_Term.freevars = _90_503})::[]), (x)::xs) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), _90_523) -> begin
if (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v)
end
| _90_530 -> begin
false
end)) args vars)) then begin
(tok_of_name env f)
end else begin
None
end
end
| (_90_532, []) -> begin
(

let fvs = (FStar_SMTEncoding_Term.free_variables t)
in if (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (not ((FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)))))) then begin
Some (t)
end else begin
None
end)
end
| _90_538 -> begin
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


let encode_const : FStar_Const.sconst  ->  FStar_SMTEncoding_Term.term = (fun _90_8 -> (match (_90_8) with
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
(let _187_488 = (let _187_487 = (let _187_486 = (let _187_485 = (FStar_SMTEncoding_Term.mkInteger' (FStar_Util.int_of_char c))
in (FStar_SMTEncoding_Term.boxInt _187_485))
in (_187_486)::[])
in (("FStar.Char.Char"), (_187_487)))
in (FStar_SMTEncoding_Term.mkApp _187_488))
end
| FStar_Const.Const_int (i, None) -> begin
(let _187_489 = (FStar_SMTEncoding_Term.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt _187_489))
end
| FStar_Const.Const_int (i, Some (_90_558)) -> begin
(FStar_All.failwith "Machine integers should be desugared")
end
| FStar_Const.Const_string (bytes, _90_564) -> begin
(let _187_490 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _187_490))
end
| FStar_Const.Const_range (r) -> begin
FStar_SMTEncoding_Term.mk_Range_const
end
| FStar_Const.Const_effect -> begin
FStar_SMTEncoding_Term.mk_Term_type
end
| c -> begin
(let _187_492 = (let _187_491 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" _187_491))
in (FStar_All.failwith _187_492))
end))


let as_function_typ : env_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (

let rec aux = (fun norm t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_90_578) -> begin
t
end
| FStar_Syntax_Syntax.Tm_refine (_90_581) -> begin
(let _187_501 = (FStar_Syntax_Util.unrefine t)
in (aux true _187_501))
end
| _90_584 -> begin
if norm then begin
(let _187_502 = (whnf env t)
in (aux false _187_502))
end else begin
(let _187_505 = (let _187_504 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (let _187_503 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _187_504 _187_503)))
in (FStar_All.failwith _187_505))
end
end)))
in (aux true t0)))


let curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun k -> (

let k = (FStar_Syntax_Subst.compress k)
in (match (k.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| _90_592 -> begin
(let _187_508 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (_187_508)))
end)))


let rec encode_binders : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> (

let _90_596 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _187_556 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" _187_556))
end else begin
()
end
in (

let _90_624 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _90_603 b -> (match (_90_603) with
| (vars, guards, env, decls, names) -> begin
(

let _90_618 = (

let x = (unmangle (Prims.fst b))
in (

let _90_609 = (gen_term_var env x)
in (match (_90_609) with
| (xxsym, xx, env') -> begin
(

let _90_612 = (let _187_559 = (norm env x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt _187_559 env xx))
in (match (_90_612) with
| (guard_x_t, decls') -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (guard_x_t), (env'), (decls'), (x))
end))
end)))
in (match (_90_618) with
| (v, g, env, decls', n) -> begin
(((v)::vars), ((g)::guards), (env), ((FStar_List.append decls decls')), ((n)::names))
end))
end)) (([]), ([]), (env), ([]), ([]))))
in (match (_90_624) with
| (vars, guards, env, decls, names) -> begin
(((FStar_List.rev vars)), ((FStar_List.rev guards)), (env), (decls), ((FStar_List.rev names)))
end))))
and encode_term_pred : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let _90_631 = (encode_term t env)
in (match (_90_631) with
| (t, decls) -> begin
(let _187_564 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t)
in ((_187_564), (decls)))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let _90_638 = (encode_term t env)
in (match (_90_638) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _187_569 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t)
in ((_187_569), (decls)))
end
| Some (f) -> begin
(let _187_570 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t)
in ((_187_570), (decls)))
end)
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let t0 = (FStar_Syntax_Subst.compress t)
in (

let _90_645 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _187_575 = (FStar_Syntax_Print.tag_of_term t)
in (let _187_574 = (FStar_Syntax_Print.tag_of_term t0)
in (let _187_573 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" _187_575 _187_574 _187_573))))
end else begin
()
end
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _187_580 = (let _187_579 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (let _187_578 = (FStar_Syntax_Print.tag_of_term t0)
in (let _187_577 = (FStar_Syntax_Print.term_to_string t0)
in (let _187_576 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _187_579 _187_578 _187_577 _187_576)))))
in (FStar_All.failwith _187_580))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _187_582 = (let _187_581 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" _187_581))
in (FStar_All.failwith _187_582))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, k, _90_656) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_meta (t, _90_661) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t = (lookup_term_var env x)
in ((t), ([])))
end
| FStar_Syntax_Syntax.Tm_fvar (v) -> begin
(let _187_583 = (lookup_free_var env v.FStar_Syntax_Syntax.fv_name)
in ((_187_583), ([])))
end
| FStar_Syntax_Syntax.Tm_type (_90_670) -> begin
((FStar_SMTEncoding_Term.mk_Term_type), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t, _90_674) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(let _187_584 = (encode_const c)
in ((_187_584), ([])))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _90_685 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_90_685) with
| (binders, res) -> begin
if ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res)) then begin
(

let _90_692 = (encode_binders None binders env)
in (match (_90_692) with
| (vars, guards, env', decls, _90_691) -> begin
(

let fsym = (let _187_585 = (varops.fresh "f")
in ((_187_585), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (

let app = (mk_Apply f vars)
in (

let _90_700 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post (

let _90_696 = env.tcenv
in {FStar_TypeChecker_Env.solver = _90_696.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _90_696.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _90_696.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _90_696.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _90_696.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _90_696.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _90_696.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _90_696.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _90_696.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _90_696.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _90_696.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _90_696.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _90_696.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _90_696.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _90_696.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _90_696.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _90_696.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _90_696.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _90_696.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _90_696.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _90_696.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _90_696.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _90_696.FStar_TypeChecker_Env.qname_and_index}) res)
in (match (_90_700) with
| (pre_opt, res_t) -> begin
(

let _90_703 = (encode_term_pred None res_t env' app)
in (match (_90_703) with
| (res_pred, decls') -> begin
(

let _90_712 = (match (pre_opt) with
| None -> begin
(let _187_586 = (FStar_SMTEncoding_Term.mk_and_l guards)
in ((_187_586), ([])))
end
| Some (pre) -> begin
(

let _90_709 = (encode_formula pre env')
in (match (_90_709) with
| (guard, decls0) -> begin
(let _187_587 = (FStar_SMTEncoding_Term.mk_and_l ((guard)::guards))
in ((_187_587), (decls0)))
end))
end)
in (match (_90_712) with
| (guards, guard_decls) -> begin
(

let t_interp = (let _187_589 = (let _187_588 = (FStar_SMTEncoding_Term.mkImp ((guards), (res_pred)))
in ((((app)::[])::[]), (vars), (_187_588)))
in (FStar_SMTEncoding_Term.mkForall _187_589))
in (

let cvars = (let _187_591 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right _187_591 (FStar_List.filter (fun _90_717 -> (match (_90_717) with
| (x, _90_716) -> begin
(x <> (Prims.fst fsym))
end)))))
in (

let tkey = (FStar_SMTEncoding_Term.mkForall (([]), ((fsym)::cvars), (t_interp)))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t', sorts, _90_723) -> begin
(let _187_594 = (let _187_593 = (let _187_592 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in ((t'), (_187_592)))
in (FStar_SMTEncoding_Term.mkApp _187_593))
in ((_187_594), ([])))
end
| None -> begin
(

let tsym = (let _187_596 = (let _187_595 = (FStar_Util.digest_of_string tkey.FStar_SMTEncoding_Term.hash)
in (Prims.strcat "Tm_arrow_" _187_595))
in (varops.mk_unique _187_596))
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let caption = if (FStar_Options.log_queries ()) then begin
(let _187_597 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in Some (_187_597))
end else begin
None
end
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (caption)))
in (

let t = (let _187_599 = (let _187_598 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in ((tsym), (_187_598)))
in (FStar_SMTEncoding_Term.mkApp _187_599))
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let k_assumption = (

let a_name = Some ((Prims.strcat "kinding_" tsym))
in (let _187_601 = (let _187_600 = (FStar_SMTEncoding_Term.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((_187_600), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_187_601)))
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t)
in (

let pre_typing = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in (let _187_608 = (let _187_607 = (let _187_606 = (let _187_605 = (let _187_604 = (let _187_603 = (let _187_602 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _187_602))
in ((f_has_t), (_187_603)))
in (FStar_SMTEncoding_Term.mkImp _187_604))
in ((((f_has_t)::[])::[]), ((fsym)::cvars), (_187_605)))
in (mkForall_fuel _187_606))
in ((_187_607), (Some ("pre-typing for functions")), (a_name)))
in FStar_SMTEncoding_Term.Assume (_187_608)))
in (

let t_interp = (

let a_name = Some ((Prims.strcat "interpretation_" tsym))
in (let _187_612 = (let _187_611 = (let _187_610 = (let _187_609 = (FStar_SMTEncoding_Term.mkIff ((f_has_t_z), (t_interp)))
in ((((f_has_t_z)::[])::[]), ((fsym)::cvars), (_187_609)))
in (FStar_SMTEncoding_Term.mkForall _187_610))
in ((_187_611), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_187_612)))
in (

let t_decls = (FStar_List.append ((tdecl)::decls) (FStar_List.append decls' (FStar_List.append guard_decls ((k_assumption)::(pre_typing)::(t_interp)::[]))))
in (

let _90_742 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash ((tsym), (cvar_sorts), (t_decls)))
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
in (let _187_614 = (let _187_613 = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in ((_187_613), (Some ("Typing for non-total arrows")), (a_name)))
in FStar_SMTEncoding_Term.Assume (_187_614)))
in (

let fsym = (("f"), (FStar_SMTEncoding_Term.Term_sort))
in (

let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let t_interp = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in (let _187_621 = (let _187_620 = (let _187_619 = (let _187_618 = (let _187_617 = (let _187_616 = (let _187_615 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _187_615))
in ((f_has_t), (_187_616)))
in (FStar_SMTEncoding_Term.mkImp _187_617))
in ((((f_has_t)::[])::[]), ((fsym)::[]), (_187_618)))
in (mkForall_fuel _187_619))
in ((_187_620), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_187_621)))
in ((t), ((tdecl)::(t_kinding)::(t_interp)::[]))))))))))
end
end))
end
| FStar_Syntax_Syntax.Tm_refine (_90_755) -> begin
(

let _90_775 = (match ((FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.tk = _90_762; FStar_Syntax_Syntax.pos = _90_760; FStar_Syntax_Syntax.vars = _90_758} -> begin
(

let _90_770 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) f)
in (match (_90_770) with
| (b, f) -> begin
(let _187_623 = (let _187_622 = (FStar_List.hd b)
in (Prims.fst _187_622))
in ((_187_623), (f)))
end))
end
| _90_772 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_90_775) with
| (x, f) -> begin
(

let _90_778 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (_90_778) with
| (base_t, decls) -> begin
(

let _90_782 = (gen_term_var env x)
in (match (_90_782) with
| (x, xtm, env') -> begin
(

let _90_785 = (encode_formula f env')
in (match (_90_785) with
| (refinement, decls') -> begin
(

let _90_788 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_90_788) with
| (fsym, fterm) -> begin
(

let encoding = (let _187_625 = (let _187_624 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in ((_187_624), (refinement)))
in (FStar_SMTEncoding_Term.mkAnd _187_625))
in (

let cvars = (let _187_627 = (FStar_SMTEncoding_Term.free_variables encoding)
in (FStar_All.pipe_right _187_627 (FStar_List.filter (fun _90_793 -> (match (_90_793) with
| (y, _90_792) -> begin
((y <> x) && (y <> fsym))
end)))))
in (

let xfv = ((x), (FStar_SMTEncoding_Term.Term_sort))
in (

let ffv = ((fsym), (FStar_SMTEncoding_Term.Fuel_sort))
in (

let tkey = (FStar_SMTEncoding_Term.mkForall (([]), ((ffv)::(xfv)::cvars), (encoding)))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _90_800, _90_802) -> begin
(let _187_630 = (let _187_629 = (let _187_628 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in ((t), (_187_628)))
in (FStar_SMTEncoding_Term.mkApp _187_629))
in ((_187_630), ([])))
end
| None -> begin
(

let tsym = (let _187_632 = (let _187_631 = (FStar_Util.digest_of_string tkey.FStar_SMTEncoding_Term.hash)
in (Prims.strcat "Tm_refine_" _187_631))
in (varops.mk_unique _187_632))
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let t = (let _187_634 = (let _187_633 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in ((tsym), (_187_633)))
in (FStar_SMTEncoding_Term.mkApp _187_634))
in (

let x_has_t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let t_haseq_base = (FStar_SMTEncoding_Term.mk_haseq base_t)
in (

let t_haseq_ref = (FStar_SMTEncoding_Term.mk_haseq t)
in (

let t_haseq = (let _187_638 = (let _187_637 = (let _187_636 = (let _187_635 = (FStar_SMTEncoding_Term.mkIff ((t_haseq_ref), (t_haseq_base)))
in ((((t_haseq_ref)::[])::[]), (cvars), (_187_635)))
in (FStar_SMTEncoding_Term.mkForall _187_636))
in ((_187_637), (Some ((Prims.strcat "haseq for " tsym))), (Some ((Prims.strcat "haseq" tsym)))))
in FStar_SMTEncoding_Term.Assume (_187_638))
in (

let t_kinding = (let _187_640 = (let _187_639 = (FStar_SMTEncoding_Term.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((_187_639), (Some ("refinement kinding")), (Some ((Prims.strcat "refinement_kinding_" tsym)))))
in FStar_SMTEncoding_Term.Assume (_187_640))
in (

let t_interp = (let _187_646 = (let _187_645 = (let _187_642 = (let _187_641 = (FStar_SMTEncoding_Term.mkIff ((x_has_t), (encoding)))
in ((((x_has_t)::[])::[]), ((ffv)::(xfv)::cvars), (_187_641)))
in (FStar_SMTEncoding_Term.mkForall _187_642))
in (let _187_644 = (let _187_643 = (FStar_Syntax_Print.term_to_string t0)
in Some (_187_643))
in ((_187_645), (_187_644), (Some ((Prims.strcat "refinement_interpretation_" tsym))))))
in FStar_SMTEncoding_Term.Assume (_187_646))
in (

let t_decls = (FStar_List.append decls (FStar_List.append decls' ((tdecl)::(t_kinding)::(t_interp)::(t_haseq)::[])))
in (

let _90_818 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash ((tsym), (cvar_sorts), (t_decls)))
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

let ttm = (let _187_647 = (FStar_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Term.mk_Term_uvar _187_647))
in (

let _90_827 = (encode_term_pred None k env ttm)
in (match (_90_827) with
| (t_has_k, decls) -> begin
(

let d = (let _187_653 = (let _187_652 = (let _187_651 = (let _187_650 = (let _187_649 = (let _187_648 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _187_648))
in (FStar_Util.format1 "uvar_typing_%s" _187_649))
in (varops.mk_unique _187_650))
in Some (_187_651))
in ((t_has_k), (Some ("Uvar typing")), (_187_652)))
in FStar_SMTEncoding_Term.Assume (_187_653))
in ((ttm), ((FStar_List.append decls ((d)::[])))))
end)))
end
| FStar_Syntax_Syntax.Tm_app (_90_830) -> begin
(

let _90_834 = (FStar_Syntax_Util.head_and_args t0)
in (match (_90_834) with
| (head, args_e) -> begin
(match ((let _187_655 = (let _187_654 = (FStar_Syntax_Subst.compress head)
in _187_654.FStar_Syntax_Syntax.n)
in ((_187_655), (args_e)))) with
| (_90_836, _90_838) when (head_redex env head) -> begin
(let _187_656 = (whnf env t)
in (encode_term _187_656 env))
end
| ((FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), (_)::((v1, _))::((v2, _))::[])) | ((FStar_Syntax_Syntax.Tm_fvar (fv), (_)::((v1, _))::((v2, _))::[])) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
(

let _90_878 = (encode_term v1 env)
in (match (_90_878) with
| (v1, decls1) -> begin
(

let _90_881 = (encode_term v2 env)
in (match (_90_881) with
| (v2, decls2) -> begin
(let _187_657 = (FStar_SMTEncoding_Term.mk_LexCons v1 v2)
in ((_187_657), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), (_90_890)::(_90_887)::_90_885) -> begin
(

let e0 = (let _187_661 = (let _187_660 = (let _187_659 = (let _187_658 = (FStar_List.hd args_e)
in (_187_658)::[])
in ((head), (_187_659)))
in FStar_Syntax_Syntax.Tm_app (_187_660))
in (FStar_Syntax_Syntax.mk _187_661 None head.FStar_Syntax_Syntax.pos))
in (

let e = (let _187_664 = (let _187_663 = (let _187_662 = (FStar_List.tl args_e)
in ((e0), (_187_662)))
in FStar_Syntax_Syntax.Tm_app (_187_663))
in (FStar_Syntax_Syntax.mk _187_664 None t0.FStar_Syntax_Syntax.pos))
in (encode_term e env)))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), ((arg, _90_899))::[]) -> begin
(

let _90_905 = (encode_term arg env)
in (match (_90_905) with
| (tm, decls) -> begin
(let _187_665 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Var ("Reify")), ((tm)::[])))))
in ((_187_665), (decls)))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (_90_907)), ((arg, _90_912))::[]) -> begin
(encode_term arg env)
end
| _90_917 -> begin
(

let _90_920 = (encode_args args_e env)
in (match (_90_920) with
| (args, decls) -> begin
(

let encode_partial_app = (fun ht_opt -> (

let _90_925 = (encode_term head env)
in (match (_90_925) with
| (head, decls') -> begin
(

let app_tm = (mk_Apply_args head args)
in (match (ht_opt) with
| None -> begin
((app_tm), ((FStar_List.append decls decls')))
end
| Some (formals, c) -> begin
(

let _90_934 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (_90_934) with
| (formals, rest) -> begin
(

let subst = (FStar_List.map2 (fun _90_938 _90_942 -> (match (((_90_938), (_90_942))) with
| ((bv, _90_937), (a, _90_941)) -> begin
FStar_Syntax_Syntax.NT (((bv), (a)))
end)) formals args_e)
in (

let ty = (let _187_670 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right _187_670 (FStar_Syntax_Subst.subst subst)))
in (

let _90_947 = (encode_term_pred None ty env app_tm)
in (match (_90_947) with
| (has_type, decls'') -> begin
(

let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (

let e_typing = (let _187_676 = (let _187_675 = (FStar_SMTEncoding_Term.mkForall ((((has_type)::[])::[]), (cvars), (has_type)))
in (let _187_674 = (let _187_673 = (let _187_672 = (let _187_671 = (FStar_Util.digest_of_string app_tm.FStar_SMTEncoding_Term.hash)
in (Prims.strcat "partial_app_typing_" _187_671))
in (varops.mk_unique _187_672))
in Some (_187_673))
in ((_187_675), (Some ("Partial app typing")), (_187_674))))
in FStar_SMTEncoding_Term.Assume (_187_676))
in ((app_tm), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' ((e_typing)::[]))))))))
end))))
end))
end))
end)))
in (

let encode_full_app = (fun fv -> (

let _90_954 = (lookup_free_var_sym env fv)
in (match (_90_954) with
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
(let _187_680 = (let _187_679 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _187_679 Prims.snd))
in Some (_187_680))
end
| FStar_Syntax_Syntax.Tm_ascribed (_90_986, FStar_Util.Inl (t), _90_990) -> begin
Some (t)
end
| FStar_Syntax_Syntax.Tm_ascribed (_90_994, FStar_Util.Inr (c), _90_998) -> begin
Some ((FStar_Syntax_Util.comp_result c))
end
| _90_1002 -> begin
None
end)
in (match (head_type) with
| None -> begin
(encode_partial_app None)
end
| Some (head_type) -> begin
(

let head_type = (let _187_681 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine _187_681))
in (

let _90_1010 = (curried_arrow_formals_comp head_type)
in (match (_90_1010) with
| (formals, c) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| _90_1026 -> begin
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

let _90_1035 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_90_1035) with
| (bs, body, opening) -> begin
(

let fallback = (fun _90_1037 -> (match (()) with
| () -> begin
(

let f = (varops.fresh "Tm_abs")
in (

let decl = FStar_SMTEncoding_Term.DeclFun (((f), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Imprecise function encoding"))))
in (let _187_684 = (FStar_SMTEncoding_Term.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in ((_187_684), ((decl)::[])))))
end))
in (

let is_impure = (fun _90_9 -> (match (_90_9) with
| FStar_Util.Inl (lc) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)))
end
| FStar_Util.Inr (eff) -> begin
(let _187_687 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv eff)
in (FStar_All.pipe_right _187_687 Prims.op_Negation))
end))
in (

let codomain_eff = (fun lc -> (match (lc) with
| FStar_Util.Inl (lc) -> begin
(let _187_692 = (let _187_690 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening _187_690))
in (FStar_All.pipe_right _187_692 (fun _187_691 -> Some (_187_691))))
end
| FStar_Util.Inr (eff) -> begin
(

let new_uvar = (fun _90_1053 -> (match (()) with
| () -> begin
(let _187_695 = (FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange [] FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _187_695 Prims.fst))
end))
in if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid) then begin
(let _187_698 = (let _187_696 = (new_uvar ())
in (FStar_Syntax_Syntax.mk_Total _187_696))
in (FStar_All.pipe_right _187_698 (fun _187_697 -> Some (_187_697))))
end else begin
if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid) then begin
(let _187_701 = (let _187_699 = (new_uvar ())
in (FStar_Syntax_Syntax.mk_GTotal _187_699))
in (FStar_All.pipe_right _187_701 (fun _187_700 -> Some (_187_700))))
end else begin
None
end
end)
end))
in (match (lopt) with
| None -> begin
(

let _90_1055 = (let _187_703 = (let _187_702 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s" _187_702))
in (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos _187_703))
in (fallback ()))
end
| Some (lc) -> begin
if (is_impure lc) then begin
(fallback ())
end else begin
(

let _90_1065 = (encode_binders None bs env)
in (match (_90_1065) with
| (vars, guards, envbody, decls, _90_1064) -> begin
(

let _90_1068 = (encode_term body envbody)
in (match (_90_1068) with
| (body, decls') -> begin
(

let key_body = (let _187_707 = (let _187_706 = (let _187_705 = (let _187_704 = (FStar_SMTEncoding_Term.mk_and_l guards)
in ((_187_704), (body)))
in (FStar_SMTEncoding_Term.mkImp _187_705))
in (([]), (vars), (_187_706)))
in (FStar_SMTEncoding_Term.mkForall _187_707))
in (

let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (

let tkey = (FStar_SMTEncoding_Term.mkForall (([]), (cvars), (key_body)))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _90_1074, _90_1076) -> begin
(let _187_710 = (let _187_709 = (let _187_708 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in ((t), (_187_708)))
in (FStar_SMTEncoding_Term.mkApp _187_709))
in ((_187_710), ([])))
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

let fsym = (let _187_712 = (let _187_711 = (FStar_Util.digest_of_string tkey.FStar_SMTEncoding_Term.hash)
in (Prims.strcat "Tm_abs_" _187_711))
in (varops.mk_unique _187_712))
in (

let fdecl = FStar_SMTEncoding_Term.DeclFun (((fsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let f = (let _187_714 = (let _187_713 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in ((fsym), (_187_713)))
in (FStar_SMTEncoding_Term.mkApp _187_714))
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

let _90_1094 = (encode_term_pred None tfun env f)
in (match (_90_1094) with
| (f_has_t, decls'') -> begin
(

let a_name = Some ((Prims.strcat "typing_" fsym))
in (let _187_718 = (let _187_717 = (let _187_716 = (let _187_715 = (FStar_SMTEncoding_Term.mkForall ((((f)::[])::[]), (cvars), (f_has_t)))
in ((_187_715), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_187_716))
in (_187_717)::[])
in (FStar_List.append decls'' _187_718)))
end)))
end)
in (

let interp_f = (

let a_name = Some ((Prims.strcat "interpretation_" fsym))
in (let _187_722 = (let _187_721 = (let _187_720 = (let _187_719 = (FStar_SMTEncoding_Term.mkEq ((app), (body)))
in ((((app)::[])::[]), ((FStar_List.append vars cvars)), (_187_719)))
in (FStar_SMTEncoding_Term.mkForall _187_720))
in ((_187_721), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_187_722)))
in (

let f_decls = (FStar_List.append decls (FStar_List.append decls' (FStar_List.append ((fdecl)::typing_f) ((interp_f)::[]))))
in (

let _90_1100 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash ((fsym), (cvar_sorts), (f_decls)))
in ((f), (f_decls)))))))))))
end)
end))))
end))
end))
end
end))))
end))
end
| FStar_Syntax_Syntax.Tm_let ((_90_1103, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_90_1115); FStar_Syntax_Syntax.lbunivs = _90_1113; FStar_Syntax_Syntax.lbtyp = _90_1111; FStar_Syntax_Syntax.lbeff = _90_1109; FStar_Syntax_Syntax.lbdef = _90_1107})::_90_1105), _90_1121) -> begin
(FStar_All.failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _90_1130; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _90_1127; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (_90_1140) -> begin
(

let _90_1142 = (FStar_TypeChecker_Errors.diag t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (

let e = (varops.fresh "let-rec")
in (

let decl_e = FStar_SMTEncoding_Term.DeclFun (((e), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (let _187_723 = (FStar_SMTEncoding_Term.mkFreeV ((e), (FStar_SMTEncoding_Term.Term_sort)))
in ((_187_723), ((decl_e)::[]))))))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end))))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (

let _90_1158 = (encode_term e1 env)
in (match (_90_1158) with
| (ee1, decls1) -> begin
(

let _90_1161 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) e2)
in (match (_90_1161) with
| (xs, e2) -> begin
(

let _90_1165 = (FStar_List.hd xs)
in (match (_90_1165) with
| (x, _90_1164) -> begin
(

let env' = (push_term_var env x ee1)
in (

let _90_1169 = (encode_body e2 env')
in (match (_90_1169) with
| (ee2, decls2) -> begin
((ee2), ((FStar_List.append decls1 decls2)))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (

let _90_1177 = (encode_term e env)
in (match (_90_1177) with
| (scr, decls) -> begin
(

let _90_1214 = (FStar_List.fold_right (fun b _90_1181 -> (match (_90_1181) with
| (else_case, decls) -> begin
(

let _90_1185 = (FStar_Syntax_Subst.open_branch b)
in (match (_90_1185) with
| (p, w, br) -> begin
(

let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun _90_1189 _90_1192 -> (match (((_90_1189), (_90_1192))) with
| ((env0, pattern), (else_case, decls)) -> begin
(

let guard = (pattern.guard scr)
in (

let projections = (pattern.projections scr)
in (

let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env _90_1198 -> (match (_90_1198) with
| (x, t) -> begin
(push_term_var env x t)
end)) env))
in (

let _90_1208 = (match (w) with
| None -> begin
((guard), ([]))
end
| Some (w) -> begin
(

let _90_1205 = (encode_term w env)
in (match (_90_1205) with
| (w, decls2) -> begin
(let _187_757 = (let _187_756 = (let _187_755 = (let _187_754 = (let _187_753 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Term.mkTrue)
in ((w), (_187_753)))
in (FStar_SMTEncoding_Term.mkEq _187_754))
in ((guard), (_187_755)))
in (FStar_SMTEncoding_Term.mkAnd _187_756))
in ((_187_757), (decls2)))
end))
end)
in (match (_90_1208) with
| (guard, decls2) -> begin
(

let _90_1211 = (encode_br br env)
in (match (_90_1211) with
| (br, decls3) -> begin
(let _187_758 = (FStar_SMTEncoding_Term.mkITE ((guard), (br), (else_case)))
in ((_187_758), ((FStar_List.append decls (FStar_List.append decls2 decls3)))))
end))
end)))))
end)) patterns ((else_case), (decls))))
end))
end)) pats ((default_case), (decls)))
in (match (_90_1214) with
| (match_tm, decls) -> begin
((match_tm), (decls))
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _90_1220 -> begin
(let _187_761 = (encode_one_pat env pat)
in (_187_761)::[])
end))
and encode_one_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> (

let _90_1223 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _187_764 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" _187_764))
end else begin
()
end
in (

let _90_1227 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (_90_1227) with
| (vars, pat_term) -> begin
(

let _90_1239 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun _90_1230 v -> (match (_90_1230) with
| (env, vars) -> begin
(

let _90_1236 = (gen_term_var env v)
in (match (_90_1236) with
| (xx, _90_1234, env) -> begin
((env), ((((v), (((xx), (FStar_SMTEncoding_Term.Term_sort)))))::vars))
end))
end)) ((env), ([]))))
in (match (_90_1239) with
| (env, vars) -> begin
(

let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_90_1244) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_dot_term (_)) -> begin
FStar_SMTEncoding_Term.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _187_772 = (let _187_771 = (encode_const c)
in ((scrutinee), (_187_771)))
in (FStar_SMTEncoding_Term.mkEq _187_772))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let is_f = (mk_data_tester env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _90_1266 -> (match (_90_1266) with
| (arg, _90_1265) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _187_775 = (FStar_SMTEncoding_Term.mkApp ((proj), ((scrutinee)::[])))
in (mk_guard arg _187_775)))
end))))
in (FStar_SMTEncoding_Term.mk_and_l ((is_f)::sub_term_guards))))
end))
in (

let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_90_1273) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _)) | (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_constant (_90_1283) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(let _187_783 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _90_1293 -> (match (_90_1293) with
| (arg, _90_1292) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _187_782 = (FStar_SMTEncoding_Term.mkApp ((proj), ((scrutinee)::[])))
in (mk_projections arg _187_782)))
end))))
in (FStar_All.pipe_right _187_783 FStar_List.flatten))
end))
in (

let pat_term = (fun _90_1296 -> (match (()) with
| () -> begin
(encode_term pat_term env)
end))
in (

let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in ((env), (pattern))))))
end))
end))))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (

let _90_1312 = (FStar_All.pipe_right l (FStar_List.fold_left (fun _90_1302 _90_1306 -> (match (((_90_1302), (_90_1306))) with
| ((tms, decls), (t, _90_1305)) -> begin
(

let _90_1309 = (encode_term t env)
in (match (_90_1309) with
| (t, decls') -> begin
(((t)::tms), ((FStar_List.append decls decls')))
end))
end)) (([]), ([]))))
in (match (_90_1312) with
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

let _90_1322 = (FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern")
in [])
end))
in (

let one_pat = (fun p -> (

let _90_1328 = (let _187_798 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right _187_798 FStar_Syntax_Util.head_and_args))
in (match (_90_1328) with
| (head, args) -> begin
(match ((let _187_800 = (let _187_799 = (FStar_Syntax_Util.un_uinst head)
in _187_799.FStar_Syntax_Syntax.n)
in ((_187_800), (args)))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((_90_1336, _90_1338))::((e, _90_1333))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpat_lid) -> begin
((e), (None))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, _90_1346))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatT_lid) -> begin
((e), (None))
end
| _90_1351 -> begin
(FStar_All.failwith "Unexpected pattern term")
end)
end)))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements p)
in (

let smt_pat_or = (fun t -> (

let _90_1359 = (let _187_805 = (FStar_Syntax_Util.unmeta t)
in (FStar_All.pipe_right _187_805 FStar_Syntax_Util.head_and_args))
in (match (_90_1359) with
| (head, args) -> begin
(match ((let _187_807 = (let _187_806 = (FStar_Syntax_Util.un_uinst head)
in _187_806.FStar_Syntax_Syntax.n)
in ((_187_807), (args)))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, _90_1364))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatOr_lid) -> begin
Some (e)
end
| _90_1369 -> begin
None
end)
end)))
in (match (elts) with
| (t)::[] -> begin
(match ((smt_pat_or t)) with
| Some (e) -> begin
(let _187_810 = (list_elements e)
in (FStar_All.pipe_right _187_810 (FStar_List.map (fun branch -> (let _187_809 = (list_elements branch)
in (FStar_All.pipe_right _187_809 (FStar_List.map one_pat)))))))
end
| _90_1376 -> begin
(let _187_811 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_187_811)::[])
end)
end
| _90_1378 -> begin
(let _187_812 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_187_812)::[])
end))))
in (

let _90_1421 = (match ((let _187_813 = (FStar_Syntax_Subst.compress t)
in _187_813.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _90_1385 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_90_1385) with
| (binders, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = _90_1406; FStar_Syntax_Syntax.effect_name = _90_1404; FStar_Syntax_Syntax.result_typ = _90_1402; FStar_Syntax_Syntax.effect_args = ((pre, _90_1398))::((post, _90_1394))::((pats, _90_1390))::[]; FStar_Syntax_Syntax.flags = _90_1387}) -> begin
(

let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _187_814 = (lemma_pats pats')
in ((binders), (pre), (post), (_187_814))))
end
| _90_1414 -> begin
(FStar_All.failwith "impos")
end)
end))
end
| _90_1416 -> begin
(FStar_All.failwith "Impos")
end)
in (match (_90_1421) with
| (binders, pre, post, patterns) -> begin
(

let _90_1428 = (encode_binders None binders env)
in (match (_90_1428) with
| (vars, guards, env, decls, _90_1427) -> begin
(

let _90_1441 = (let _187_818 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (

let _90_1438 = (let _187_817 = (FStar_All.pipe_right branch (FStar_List.map (fun _90_1433 -> (match (_90_1433) with
| (t, _90_1432) -> begin
(encode_term t (

let _90_1434 = env
in {bindings = _90_1434.bindings; depth = _90_1434.depth; tcenv = _90_1434.tcenv; warn = _90_1434.warn; cache = _90_1434.cache; nolabels = _90_1434.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _90_1434.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _187_817 FStar_List.unzip))
in (match (_90_1438) with
| (pats, decls) -> begin
((pats), (decls))
end)))))
in (FStar_All.pipe_right _187_818 FStar_List.unzip))
in (match (_90_1441) with
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
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _187_821 = (let _187_820 = (FStar_SMTEncoding_Term.mkFreeV l)
in (FStar_SMTEncoding_Term.mk_Precedes _187_820 e))
in (_187_821)::p))))
end
| _90_1451 -> begin
(

let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _187_827 = (FStar_SMTEncoding_Term.mk_Precedes tl e)
in (_187_827)::p))))
end
| ((x, FStar_SMTEncoding_Term.Term_sort))::vars -> begin
(let _187_829 = (let _187_828 = (FStar_SMTEncoding_Term.mkFreeV ((x), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_LexCons _187_828 tl))
in (aux _187_829 vars))
end
| _90_1463 -> begin
pats
end))
in (let _187_830 = (FStar_SMTEncoding_Term.mkFreeV (("Prims.LexTop"), (FStar_SMTEncoding_Term.Term_sort)))
in (aux _187_830 vars)))
end)
end)
in (

let env = (

let _90_1465 = env
in {bindings = _90_1465.bindings; depth = _90_1465.depth; tcenv = _90_1465.tcenv; warn = _90_1465.warn; cache = _90_1465.cache; nolabels = true; use_zfuel_name = _90_1465.use_zfuel_name; encode_non_total_function_typ = _90_1465.encode_non_total_function_typ})
in (

let _90_1470 = (let _187_831 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula _187_831 env))
in (match (_90_1470) with
| (pre, decls'') -> begin
(

let _90_1473 = (let _187_832 = (FStar_Syntax_Util.unmeta post)
in (encode_formula _187_832 env))
in (match (_90_1473) with
| (post, decls''') -> begin
(

let decls = (FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') (FStar_List.append decls'' decls''')))
in (let _187_837 = (let _187_836 = (let _187_835 = (let _187_834 = (let _187_833 = (FStar_SMTEncoding_Term.mk_and_l ((pre)::guards))
in ((_187_833), (post)))
in (FStar_SMTEncoding_Term.mkImp _187_834))
in ((pats), (vars), (_187_835)))
in (FStar_SMTEncoding_Term.mkForall _187_836))
in ((_187_837), (decls))))
end))
end)))))
end))
end))
end))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (

let debug = (fun phi -> if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _187_843 = (FStar_Syntax_Print.tag_of_term phi)
in (let _187_842 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print2 "Formula (%s)  %s\n" _187_843 _187_842)))
end else begin
()
end)
in (

let enc = (fun f l -> (

let _90_1489 = (FStar_Util.fold_map (fun decls x -> (

let _90_1486 = (encode_term (Prims.fst x) env)
in (match (_90_1486) with
| (t, decls') -> begin
(((FStar_List.append decls decls')), (t))
end))) [] l)
in (match (_90_1489) with
| (decls, args) -> begin
(let _187_859 = (f args)
in ((_187_859), (decls)))
end)))
in (

let const_op = (fun f _90_1492 -> ((f), ([])))
in (

let un_op = (fun f l -> (let _187_873 = (FStar_List.hd l)
in (FStar_All.pipe_left f _187_873)))
in (

let bin_op = (fun f _90_10 -> (match (_90_10) with
| (t1)::(t2)::[] -> begin
(f ((t1), (t2)))
end
| _90_1503 -> begin
(FStar_All.failwith "Impossible")
end))
in (

let enc_prop_c = (fun f l -> (

let _90_1518 = (FStar_Util.fold_map (fun decls _90_1512 -> (match (_90_1512) with
| (t, _90_1511) -> begin
(

let _90_1515 = (encode_formula t env)
in (match (_90_1515) with
| (phi, decls') -> begin
(((FStar_List.append decls decls')), (phi))
end))
end)) [] l)
in (match (_90_1518) with
| (decls, phis) -> begin
(let _187_898 = (f phis)
in ((_187_898), (decls)))
end)))
in (

let eq_op = (fun _90_11 -> (match (_90_11) with
| ((_)::(e1)::(e2)::[]) | ((_)::(_)::(e1)::(e2)::[]) -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) l)
end))
in (

let mk_imp = (fun _90_12 -> (match (_90_12) with
| ((lhs, _90_1539))::((rhs, _90_1535))::[] -> begin
(

let _90_1544 = (encode_formula rhs env)
in (match (_90_1544) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _90_1547) -> begin
((l1), (decls1))
end
| _90_1551 -> begin
(

let _90_1554 = (encode_formula lhs env)
in (match (_90_1554) with
| (l2, decls2) -> begin
(let _187_903 = (FStar_SMTEncoding_Term.mkImp ((l2), (l1)))
in ((_187_903), ((FStar_List.append decls1 decls2))))
end))
end)
end))
end
| _90_1556 -> begin
(FStar_All.failwith "impossible")
end))
in (

let mk_ite = (fun _90_13 -> (match (_90_13) with
| ((guard, _90_1569))::((_then, _90_1565))::((_else, _90_1561))::[] -> begin
(

let _90_1574 = (encode_formula guard env)
in (match (_90_1574) with
| (g, decls1) -> begin
(

let _90_1577 = (encode_formula _then env)
in (match (_90_1577) with
| (t, decls2) -> begin
(

let _90_1580 = (encode_formula _else env)
in (match (_90_1580) with
| (e, decls3) -> begin
(

let res = (FStar_SMTEncoding_Term.mkITE ((g), (t), (e)))
in ((res), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end))
end))
end
| _90_1583 -> begin
(FStar_All.failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (let _187_915 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f _187_915)))
in (

let connectives = (let _187_971 = (let _187_924 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkAnd))
in ((FStar_Syntax_Const.and_lid), (_187_924)))
in (let _187_970 = (let _187_969 = (let _187_930 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkOr))
in ((FStar_Syntax_Const.or_lid), (_187_930)))
in (let _187_968 = (let _187_967 = (let _187_966 = (let _187_939 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkIff))
in ((FStar_Syntax_Const.iff_lid), (_187_939)))
in (let _187_965 = (let _187_964 = (let _187_963 = (let _187_948 = (FStar_All.pipe_left enc_prop_c (un_op FStar_SMTEncoding_Term.mkNot))
in ((FStar_Syntax_Const.not_lid), (_187_948)))
in (_187_963)::(((FStar_Syntax_Const.eq2_lid), (eq_op)))::(((FStar_Syntax_Const.eq3_lid), (eq_op)))::(((FStar_Syntax_Const.true_lid), ((const_op FStar_SMTEncoding_Term.mkTrue))))::(((FStar_Syntax_Const.false_lid), ((const_op FStar_SMTEncoding_Term.mkFalse))))::[])
in (((FStar_Syntax_Const.ite_lid), (mk_ite)))::_187_964)
in (_187_966)::_187_965))
in (((FStar_Syntax_Const.imp_lid), (mk_imp)))::_187_967)
in (_187_969)::_187_968))
in (_187_971)::_187_970))
in (

let rec fallback = (fun phi -> (match (phi.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(

let _90_1601 = (encode_formula phi' env)
in (match (_90_1601) with
| (phi, decls) -> begin
(let _187_974 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled (((phi), (msg), (r)))))
in ((_187_974), (decls)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (_90_1603) -> begin
(let _187_975 = (FStar_Syntax_Util.unmeta phi)
in (encode_formula _187_975 env))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(

let _90_1611 = (encode_match e pats FStar_SMTEncoding_Term.mkFalse env encode_formula)
in (match (_90_1611) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _90_1618; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _90_1615; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _90_1629 = (encode_let x t1 e1 e2 env encode_formula)
in (match (_90_1629) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let head = (FStar_Syntax_Util.un_uinst head)
in (match (((head.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_90_1646)::((x, _90_1643))::((t, _90_1639))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.has_type_lid) -> begin
(

let _90_1651 = (encode_term x env)
in (match (_90_1651) with
| (x, decls) -> begin
(

let _90_1654 = (encode_term t env)
in (match (_90_1654) with
| (t, decls') -> begin
(let _187_976 = (FStar_SMTEncoding_Term.mk_HasType x t)
in ((_187_976), ((FStar_List.append decls decls'))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((r, _90_1667))::((msg, _90_1663))::((phi, _90_1659))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.labeled_lid) -> begin
(match ((let _187_980 = (let _187_977 = (FStar_Syntax_Subst.compress r)
in _187_977.FStar_Syntax_Syntax.n)
in (let _187_979 = (let _187_978 = (FStar_Syntax_Subst.compress msg)
in _187_978.FStar_Syntax_Syntax.n)
in ((_187_980), (_187_979))))) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, _90_1676))) -> begin
(

let phi = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((phi), (FStar_Syntax_Syntax.Meta_labeled ((((FStar_Util.string_of_unicode s)), (r), (false))))))) None r)
in (fallback phi))
end
| _90_1683 -> begin
(fallback phi)
end)
end
| _90_1685 when (head_redex env head) -> begin
(let _187_981 = (whnf env phi)
in (encode_formula _187_981 env))
end
| _90_1687 -> begin
(

let _90_1690 = (encode_term phi env)
in (match (_90_1690) with
| (tt, decls) -> begin
(let _187_982 = (FStar_SMTEncoding_Term.mk_Valid tt)
in ((_187_982), (decls)))
end))
end))
end
| _90_1692 -> begin
(

let _90_1695 = (encode_term phi env)
in (match (_90_1695) with
| (tt, decls) -> begin
(let _187_983 = (FStar_SMTEncoding_Term.mk_Valid tt)
in ((_187_983), (decls)))
end))
end))
in (

let encode_q_body = (fun env bs ps body -> (

let _90_1707 = (encode_binders None bs env)
in (match (_90_1707) with
| (vars, guards, env, decls, _90_1706) -> begin
(

let _90_1720 = (let _187_995 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let _90_1717 = (let _187_994 = (FStar_All.pipe_right p (FStar_List.map (fun _90_1712 -> (match (_90_1712) with
| (t, _90_1711) -> begin
(encode_term t (

let _90_1713 = env
in {bindings = _90_1713.bindings; depth = _90_1713.depth; tcenv = _90_1713.tcenv; warn = _90_1713.warn; cache = _90_1713.cache; nolabels = _90_1713.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _90_1713.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _187_994 FStar_List.unzip))
in (match (_90_1717) with
| (p, decls) -> begin
((p), ((FStar_List.flatten decls)))
end)))))
in (FStar_All.pipe_right _187_995 FStar_List.unzip))
in (match (_90_1720) with
| (pats, decls') -> begin
(

let _90_1723 = (encode_formula body env)
in (match (_90_1723) with
| (body, decls'') -> begin
(

let guards = (match (pats) with
| (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (gf), (p)::[]); FStar_SMTEncoding_Term.hash = _90_1727; FStar_SMTEncoding_Term.freevars = _90_1725})::[])::[] when ((FStar_Ident.text_of_lid FStar_Syntax_Const.guard_free) = gf) -> begin
[]
end
| _90_1738 -> begin
guards
end)
in (let _187_996 = (FStar_SMTEncoding_Term.mk_and_l guards)
in ((vars), (pats), (_187_996), (body), ((FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') decls''))))))
end))
end))
end)))
in (

let _90_1740 = (debug phi)
in (

let phi = (FStar_Syntax_Util.unascribe phi)
in (

let check_pattern_vars = (fun vars pats -> (

let pats = (FStar_All.pipe_right pats (FStar_List.map (fun _90_1749 -> (match (_90_1749) with
| (x, _90_1748) -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x)
end))))
in (match (pats) with
| [] -> begin
()
end
| (hd)::tl -> begin
(

let pat_vars = (let _187_1005 = (FStar_Syntax_Free.names hd)
in (FStar_List.fold_left (fun out x -> (let _187_1004 = (FStar_Syntax_Free.names x)
in (FStar_Util.set_union out _187_1004))) _187_1005 tl))
in (match ((FStar_All.pipe_right vars (FStar_Util.find_opt (fun _90_1761 -> (match (_90_1761) with
| (b, _90_1760) -> begin
(not ((FStar_Util.set_mem b pat_vars)))
end))))) with
| None -> begin
()
end
| Some (x, _90_1765) -> begin
(

let pos = (FStar_List.fold_left (fun out t -> (FStar_Range.union_ranges out t.FStar_Syntax_Syntax.pos)) hd.FStar_Syntax_Syntax.pos tl)
in (let _187_1010 = (let _187_1009 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variable: %s" _187_1009))
in (FStar_TypeChecker_Errors.warn pos _187_1010)))
end))
end)))
in (match ((FStar_Syntax_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _90_1780 -> (match (_90_1780) with
| (l, _90_1779) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_90_1783, f) -> begin
(f arms)
end)
end
| Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
(

let _90_1793 = (FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)))
in (

let _90_1800 = (encode_q_body env vars pats body)
in (match (_90_1800) with
| (vars, pats, guard, body, decls) -> begin
(

let tm = (let _187_1028 = (let _187_1027 = (FStar_SMTEncoding_Term.mkImp ((guard), (body)))
in ((pats), (vars), (_187_1027)))
in (FStar_SMTEncoding_Term.mkForall _187_1028))
in ((tm), (decls)))
end)))
end
| Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
(

let _90_1808 = (FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)))
in (

let _90_1815 = (encode_q_body env vars pats body)
in (match (_90_1815) with
| (vars, pats, guard, body, decls) -> begin
(let _187_1031 = (let _187_1030 = (let _187_1029 = (FStar_SMTEncoding_Term.mkAnd ((guard), (body)))
in ((pats), (vars), (_187_1029)))
in (FStar_SMTEncoding_Term.mkExists _187_1030))
in ((_187_1031), (decls)))
end)))
end))))))))))))))))))


type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list); is : FStar_Ident.lident  ->  Prims.bool}


let is_Mkprims_t : prims_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkprims_t"))))


let prims : prims_t = (

let _90_1821 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (_90_1821) with
| (asym, a) -> begin
(

let _90_1824 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_90_1824) with
| (xsym, x) -> begin
(

let _90_1827 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (_90_1827) with
| (ysym, y) -> begin
(

let deffun = (fun vars body x -> (FStar_SMTEncoding_Term.DefineFun (((x), (vars), (FStar_SMTEncoding_Term.Term_sort), (body), (None))))::[])
in (

let quant = (fun vars body x -> (

let xname_decl = (let _187_1074 = (let _187_1073 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in ((x), (_187_1073), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (_187_1074))
in (

let xtok = (Prims.strcat x "@tok")
in (

let xtok_decl = FStar_SMTEncoding_Term.DeclFun (((xtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let xapp = (let _187_1076 = (let _187_1075 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in ((x), (_187_1075)))
in (FStar_SMTEncoding_Term.mkApp _187_1076))
in (

let xtok = (FStar_SMTEncoding_Term.mkApp ((xtok), ([])))
in (

let xtok_app = (mk_Apply xtok vars)
in (let _187_1090 = (let _187_1089 = (let _187_1088 = (let _187_1087 = (let _187_1080 = (let _187_1079 = (let _187_1078 = (let _187_1077 = (FStar_SMTEncoding_Term.mkEq ((xapp), (body)))
in ((((xapp)::[])::[]), (vars), (_187_1077)))
in (FStar_SMTEncoding_Term.mkForall _187_1078))
in ((_187_1079), (None), (Some ((Prims.strcat "primitive_" x)))))
in FStar_SMTEncoding_Term.Assume (_187_1080))
in (let _187_1086 = (let _187_1085 = (let _187_1084 = (let _187_1083 = (let _187_1082 = (let _187_1081 = (FStar_SMTEncoding_Term.mkEq ((xtok_app), (xapp)))
in ((((xtok_app)::[])::[]), (vars), (_187_1081)))
in (FStar_SMTEncoding_Term.mkForall _187_1082))
in ((_187_1083), (Some ("Name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" x)))))
in FStar_SMTEncoding_Term.Assume (_187_1084))
in (_187_1085)::[])
in (_187_1087)::_187_1086))
in (xtok_decl)::_187_1088)
in (xname_decl)::_187_1089)
in ((xtok), (_187_1090))))))))))
in (

let axy = (((asym), (FStar_SMTEncoding_Term.Term_sort)))::(((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let xy = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let qx = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let prims = (let _187_1250 = (let _187_1099 = (let _187_1098 = (let _187_1097 = (FStar_SMTEncoding_Term.mkEq ((x), (y)))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _187_1097))
in (quant axy _187_1098))
in ((FStar_Syntax_Const.op_Eq), (_187_1099)))
in (let _187_1249 = (let _187_1248 = (let _187_1106 = (let _187_1105 = (let _187_1104 = (let _187_1103 = (FStar_SMTEncoding_Term.mkEq ((x), (y)))
in (FStar_SMTEncoding_Term.mkNot _187_1103))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _187_1104))
in (quant axy _187_1105))
in ((FStar_Syntax_Const.op_notEq), (_187_1106)))
in (let _187_1247 = (let _187_1246 = (let _187_1115 = (let _187_1114 = (let _187_1113 = (let _187_1112 = (let _187_1111 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _187_1110 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_187_1111), (_187_1110))))
in (FStar_SMTEncoding_Term.mkLT _187_1112))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _187_1113))
in (quant xy _187_1114))
in ((FStar_Syntax_Const.op_LT), (_187_1115)))
in (let _187_1245 = (let _187_1244 = (let _187_1124 = (let _187_1123 = (let _187_1122 = (let _187_1121 = (let _187_1120 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _187_1119 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_187_1120), (_187_1119))))
in (FStar_SMTEncoding_Term.mkLTE _187_1121))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _187_1122))
in (quant xy _187_1123))
in ((FStar_Syntax_Const.op_LTE), (_187_1124)))
in (let _187_1243 = (let _187_1242 = (let _187_1133 = (let _187_1132 = (let _187_1131 = (let _187_1130 = (let _187_1129 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _187_1128 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_187_1129), (_187_1128))))
in (FStar_SMTEncoding_Term.mkGT _187_1130))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _187_1131))
in (quant xy _187_1132))
in ((FStar_Syntax_Const.op_GT), (_187_1133)))
in (let _187_1241 = (let _187_1240 = (let _187_1142 = (let _187_1141 = (let _187_1140 = (let _187_1139 = (let _187_1138 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _187_1137 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_187_1138), (_187_1137))))
in (FStar_SMTEncoding_Term.mkGTE _187_1139))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _187_1140))
in (quant xy _187_1141))
in ((FStar_Syntax_Const.op_GTE), (_187_1142)))
in (let _187_1239 = (let _187_1238 = (let _187_1151 = (let _187_1150 = (let _187_1149 = (let _187_1148 = (let _187_1147 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _187_1146 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_187_1147), (_187_1146))))
in (FStar_SMTEncoding_Term.mkSub _187_1148))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _187_1149))
in (quant xy _187_1150))
in ((FStar_Syntax_Const.op_Subtraction), (_187_1151)))
in (let _187_1237 = (let _187_1236 = (let _187_1158 = (let _187_1157 = (let _187_1156 = (let _187_1155 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Term.mkMinus _187_1155))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _187_1156))
in (quant qx _187_1157))
in ((FStar_Syntax_Const.op_Minus), (_187_1158)))
in (let _187_1235 = (let _187_1234 = (let _187_1167 = (let _187_1166 = (let _187_1165 = (let _187_1164 = (let _187_1163 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _187_1162 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_187_1163), (_187_1162))))
in (FStar_SMTEncoding_Term.mkAdd _187_1164))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _187_1165))
in (quant xy _187_1166))
in ((FStar_Syntax_Const.op_Addition), (_187_1167)))
in (let _187_1233 = (let _187_1232 = (let _187_1176 = (let _187_1175 = (let _187_1174 = (let _187_1173 = (let _187_1172 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _187_1171 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_187_1172), (_187_1171))))
in (FStar_SMTEncoding_Term.mkMul _187_1173))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _187_1174))
in (quant xy _187_1175))
in ((FStar_Syntax_Const.op_Multiply), (_187_1176)))
in (let _187_1231 = (let _187_1230 = (let _187_1185 = (let _187_1184 = (let _187_1183 = (let _187_1182 = (let _187_1181 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _187_1180 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_187_1181), (_187_1180))))
in (FStar_SMTEncoding_Term.mkDiv _187_1182))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _187_1183))
in (quant xy _187_1184))
in ((FStar_Syntax_Const.op_Division), (_187_1185)))
in (let _187_1229 = (let _187_1228 = (let _187_1194 = (let _187_1193 = (let _187_1192 = (let _187_1191 = (let _187_1190 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _187_1189 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_187_1190), (_187_1189))))
in (FStar_SMTEncoding_Term.mkMod _187_1191))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _187_1192))
in (quant xy _187_1193))
in ((FStar_Syntax_Const.op_Modulus), (_187_1194)))
in (let _187_1227 = (let _187_1226 = (let _187_1203 = (let _187_1202 = (let _187_1201 = (let _187_1200 = (let _187_1199 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _187_1198 = (FStar_SMTEncoding_Term.unboxBool y)
in ((_187_1199), (_187_1198))))
in (FStar_SMTEncoding_Term.mkAnd _187_1200))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _187_1201))
in (quant xy _187_1202))
in ((FStar_Syntax_Const.op_And), (_187_1203)))
in (let _187_1225 = (let _187_1224 = (let _187_1212 = (let _187_1211 = (let _187_1210 = (let _187_1209 = (let _187_1208 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _187_1207 = (FStar_SMTEncoding_Term.unboxBool y)
in ((_187_1208), (_187_1207))))
in (FStar_SMTEncoding_Term.mkOr _187_1209))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _187_1210))
in (quant xy _187_1211))
in ((FStar_Syntax_Const.op_Or), (_187_1212)))
in (let _187_1223 = (let _187_1222 = (let _187_1219 = (let _187_1218 = (let _187_1217 = (let _187_1216 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Term.mkNot _187_1216))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _187_1217))
in (quant qx _187_1218))
in ((FStar_Syntax_Const.op_Negation), (_187_1219)))
in (_187_1222)::[])
in (_187_1224)::_187_1223))
in (_187_1226)::_187_1225))
in (_187_1228)::_187_1227))
in (_187_1230)::_187_1229))
in (_187_1232)::_187_1231))
in (_187_1234)::_187_1233))
in (_187_1236)::_187_1235))
in (_187_1238)::_187_1237))
in (_187_1240)::_187_1239))
in (_187_1242)::_187_1241))
in (_187_1244)::_187_1243))
in (_187_1246)::_187_1245))
in (_187_1248)::_187_1247))
in (_187_1250)::_187_1249))
in (

let mk = (fun l v -> (let _187_1297 = (let _187_1296 = (FStar_All.pipe_right prims (FStar_List.find (fun _90_1851 -> (match (_90_1851) with
| (l', _90_1850) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right _187_1296 (FStar_Option.map (fun _90_1855 -> (match (_90_1855) with
| (_90_1853, b) -> begin
(b v)
end)))))
in (FStar_All.pipe_right _187_1297 FStar_Option.get)))
in (

let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _90_1861 -> (match (_90_1861) with
| (l', _90_1860) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is}))))))))
end))
end))
end))


let pretype_axiom : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun tapp vars -> (

let _90_1867 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_90_1867) with
| (xxsym, xx) -> begin
(

let _90_1870 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_90_1870) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (let _187_1327 = (let _187_1326 = (let _187_1321 = (let _187_1320 = (let _187_1319 = (let _187_1318 = (let _187_1317 = (let _187_1316 = (FStar_SMTEncoding_Term.mkApp (("PreType"), ((xx)::[])))
in ((tapp), (_187_1316)))
in (FStar_SMTEncoding_Term.mkEq _187_1317))
in ((xx_has_type), (_187_1318)))
in (FStar_SMTEncoding_Term.mkImp _187_1319))
in ((((xx_has_type)::[])::[]), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars), (_187_1320)))
in (FStar_SMTEncoding_Term.mkForall _187_1321))
in (let _187_1325 = (let _187_1324 = (let _187_1323 = (let _187_1322 = (FStar_Util.digest_of_string tapp.FStar_SMTEncoding_Term.hash)
in (Prims.strcat "pretyping_" _187_1322))
in (varops.mk_unique _187_1323))
in Some (_187_1324))
in ((_187_1326), (Some ("pretyping")), (_187_1325))))
in FStar_SMTEncoding_Term.Assume (_187_1327)))
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
in (let _187_1348 = (let _187_1339 = (let _187_1338 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in ((_187_1338), (Some ("unit typing")), (Some ("unit_typing"))))
in FStar_SMTEncoding_Term.Assume (_187_1339))
in (let _187_1347 = (let _187_1346 = (let _187_1345 = (let _187_1344 = (let _187_1343 = (let _187_1342 = (let _187_1341 = (let _187_1340 = (FStar_SMTEncoding_Term.mkEq ((x), (FStar_SMTEncoding_Term.mk_Term_unit)))
in ((typing_pred), (_187_1340)))
in (FStar_SMTEncoding_Term.mkImp _187_1341))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_187_1342)))
in (mkForall_fuel _187_1343))
in ((_187_1344), (Some ("unit inversion")), (Some ("unit_inversion"))))
in FStar_SMTEncoding_Term.Assume (_187_1345))
in (_187_1346)::[])
in (_187_1348)::_187_1347))))
in (

let mk_bool = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Bool_sort))
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _187_1371 = (let _187_1362 = (let _187_1361 = (let _187_1360 = (let _187_1359 = (let _187_1356 = (let _187_1355 = (FStar_SMTEncoding_Term.boxBool b)
in (_187_1355)::[])
in (_187_1356)::[])
in (let _187_1358 = (let _187_1357 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType _187_1357 tt))
in ((_187_1359), ((bb)::[]), (_187_1358))))
in (FStar_SMTEncoding_Term.mkForall _187_1360))
in ((_187_1361), (Some ("bool typing")), (Some ("bool_typing"))))
in FStar_SMTEncoding_Term.Assume (_187_1362))
in (let _187_1370 = (let _187_1369 = (let _187_1368 = (let _187_1367 = (let _187_1366 = (let _187_1365 = (let _187_1364 = (let _187_1363 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in ((typing_pred), (_187_1363)))
in (FStar_SMTEncoding_Term.mkImp _187_1364))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_187_1365)))
in (mkForall_fuel _187_1366))
in ((_187_1367), (Some ("bool inversion")), (Some ("bool_inversion"))))
in FStar_SMTEncoding_Term.Assume (_187_1368))
in (_187_1369)::[])
in (_187_1371)::_187_1370))))))
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

let precedes = (let _187_1385 = (let _187_1384 = (let _187_1383 = (let _187_1382 = (let _187_1381 = (let _187_1380 = (FStar_SMTEncoding_Term.boxInt a)
in (let _187_1379 = (let _187_1378 = (FStar_SMTEncoding_Term.boxInt b)
in (_187_1378)::[])
in (_187_1380)::_187_1379))
in (tt)::_187_1381)
in (tt)::_187_1382)
in (("Prims.Precedes"), (_187_1383)))
in (FStar_SMTEncoding_Term.mkApp _187_1384))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _187_1385))
in (

let precedes_y_x = (let _187_1386 = (FStar_SMTEncoding_Term.mkApp (("Precedes"), ((y)::(x)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _187_1386))
in (let _187_1428 = (let _187_1394 = (let _187_1393 = (let _187_1392 = (let _187_1391 = (let _187_1388 = (let _187_1387 = (FStar_SMTEncoding_Term.boxInt b)
in (_187_1387)::[])
in (_187_1388)::[])
in (let _187_1390 = (let _187_1389 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType _187_1389 tt))
in ((_187_1391), ((bb)::[]), (_187_1390))))
in (FStar_SMTEncoding_Term.mkForall _187_1392))
in ((_187_1393), (Some ("int typing")), (Some ("int_typing"))))
in FStar_SMTEncoding_Term.Assume (_187_1394))
in (let _187_1427 = (let _187_1426 = (let _187_1400 = (let _187_1399 = (let _187_1398 = (let _187_1397 = (let _187_1396 = (let _187_1395 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in ((typing_pred), (_187_1395)))
in (FStar_SMTEncoding_Term.mkImp _187_1396))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_187_1397)))
in (mkForall_fuel _187_1398))
in ((_187_1399), (Some ("int inversion")), (Some ("int_inversion"))))
in FStar_SMTEncoding_Term.Assume (_187_1400))
in (let _187_1425 = (let _187_1424 = (let _187_1423 = (let _187_1422 = (let _187_1421 = (let _187_1420 = (let _187_1419 = (let _187_1418 = (let _187_1417 = (let _187_1416 = (let _187_1415 = (let _187_1414 = (let _187_1403 = (let _187_1402 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _187_1401 = (FStar_SMTEncoding_Term.mkInteger' (Prims.parse_int "0"))
in ((_187_1402), (_187_1401))))
in (FStar_SMTEncoding_Term.mkGT _187_1403))
in (let _187_1413 = (let _187_1412 = (let _187_1406 = (let _187_1405 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _187_1404 = (FStar_SMTEncoding_Term.mkInteger' (Prims.parse_int "0"))
in ((_187_1405), (_187_1404))))
in (FStar_SMTEncoding_Term.mkGTE _187_1406))
in (let _187_1411 = (let _187_1410 = (let _187_1409 = (let _187_1408 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _187_1407 = (FStar_SMTEncoding_Term.unboxInt x)
in ((_187_1408), (_187_1407))))
in (FStar_SMTEncoding_Term.mkLT _187_1409))
in (_187_1410)::[])
in (_187_1412)::_187_1411))
in (_187_1414)::_187_1413))
in (typing_pred_y)::_187_1415)
in (typing_pred)::_187_1416)
in (FStar_SMTEncoding_Term.mk_and_l _187_1417))
in ((_187_1418), (precedes_y_x)))
in (FStar_SMTEncoding_Term.mkImp _187_1419))
in ((((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[]), ((xx)::(yy)::[]), (_187_1420)))
in (mkForall_fuel _187_1421))
in ((_187_1422), (Some ("well-founded ordering on nat (alt)")), (Some ("well-founded-ordering-on-nat"))))
in FStar_SMTEncoding_Term.Assume (_187_1423))
in (_187_1424)::[])
in (_187_1426)::_187_1425))
in (_187_1428)::_187_1427)))))))))))
in (

let mk_str = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.String_sort))
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _187_1451 = (let _187_1442 = (let _187_1441 = (let _187_1440 = (let _187_1439 = (let _187_1436 = (let _187_1435 = (FStar_SMTEncoding_Term.boxString b)
in (_187_1435)::[])
in (_187_1436)::[])
in (let _187_1438 = (let _187_1437 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType _187_1437 tt))
in ((_187_1439), ((bb)::[]), (_187_1438))))
in (FStar_SMTEncoding_Term.mkForall _187_1440))
in ((_187_1441), (Some ("string typing")), (Some ("string_typing"))))
in FStar_SMTEncoding_Term.Assume (_187_1442))
in (let _187_1450 = (let _187_1449 = (let _187_1448 = (let _187_1447 = (let _187_1446 = (let _187_1445 = (let _187_1444 = (let _187_1443 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in ((typing_pred), (_187_1443)))
in (FStar_SMTEncoding_Term.mkImp _187_1444))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_187_1445)))
in (mkForall_fuel _187_1446))
in ((_187_1447), (Some ("string inversion")), (Some ("string_inversion"))))
in FStar_SMTEncoding_Term.Assume (_187_1448))
in (_187_1449)::[])
in (_187_1451)::_187_1450))))))
in (

let mk_ref = (fun env reft_name _90_1909 -> (

let r = (("r"), (FStar_SMTEncoding_Term.Ref_sort))
in (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let refa = (let _187_1460 = (let _187_1459 = (let _187_1458 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (_187_1458)::[])
in ((reft_name), (_187_1459)))
in (FStar_SMTEncoding_Term.mkApp _187_1460))
in (

let refb = (let _187_1463 = (let _187_1462 = (let _187_1461 = (FStar_SMTEncoding_Term.mkFreeV bb)
in (_187_1461)::[])
in ((reft_name), (_187_1462)))
in (FStar_SMTEncoding_Term.mkApp _187_1463))
in (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (

let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (let _187_1482 = (let _187_1469 = (let _187_1468 = (let _187_1467 = (let _187_1466 = (let _187_1465 = (let _187_1464 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in ((typing_pred), (_187_1464)))
in (FStar_SMTEncoding_Term.mkImp _187_1465))
in ((((typing_pred)::[])::[]), ((xx)::(aa)::[]), (_187_1466)))
in (mkForall_fuel _187_1467))
in ((_187_1468), (Some ("ref inversion")), (Some ("ref_inversion"))))
in FStar_SMTEncoding_Term.Assume (_187_1469))
in (let _187_1481 = (let _187_1480 = (let _187_1479 = (let _187_1478 = (let _187_1477 = (let _187_1476 = (let _187_1475 = (let _187_1474 = (FStar_SMTEncoding_Term.mkAnd ((typing_pred), (typing_pred_b)))
in (let _187_1473 = (let _187_1472 = (let _187_1471 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (let _187_1470 = (FStar_SMTEncoding_Term.mkFreeV bb)
in ((_187_1471), (_187_1470))))
in (FStar_SMTEncoding_Term.mkEq _187_1472))
in ((_187_1474), (_187_1473))))
in (FStar_SMTEncoding_Term.mkImp _187_1475))
in ((((typing_pred)::(typing_pred_b)::[])::[]), ((xx)::(aa)::(bb)::[]), (_187_1476)))
in (mkForall_fuel' (Prims.parse_int "2") _187_1477))
in ((_187_1478), (Some ("ref typing is injective")), (Some ("ref_injectivity"))))
in FStar_SMTEncoding_Term.Assume (_187_1479))
in (_187_1480)::[])
in (_187_1482)::_187_1481))))))))))
in (

let mk_true_interp = (fun env nm true_tm -> (

let valid = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((true_tm)::[])))
in (FStar_SMTEncoding_Term.Assume (((valid), (Some ("True interpretation")), (Some ("true_interp")))))::[]))
in (

let mk_false_interp = (fun env nm false_tm -> (

let valid = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((false_tm)::[])))
in (let _187_1497 = (let _187_1496 = (let _187_1495 = (FStar_SMTEncoding_Term.mkIff ((FStar_SMTEncoding_Term.mkFalse), (valid)))
in ((_187_1495), (Some ("False interpretation")), (Some ("false_interp"))))
in FStar_SMTEncoding_Term.Assume (_187_1496))
in (_187_1497)::[])))
in (

let mk_and_interp = (fun env conj _90_1931 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (

let valid = (let _187_1506 = (let _187_1505 = (let _187_1504 = (FStar_SMTEncoding_Term.mkApp ((conj), ((a)::(b)::[])))
in (_187_1504)::[])
in (("Valid"), (_187_1505)))
in (FStar_SMTEncoding_Term.mkApp _187_1506))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((b)::[])))
in (let _187_1513 = (let _187_1512 = (let _187_1511 = (let _187_1510 = (let _187_1509 = (let _187_1508 = (let _187_1507 = (FStar_SMTEncoding_Term.mkAnd ((valid_a), (valid_b)))
in ((_187_1507), (valid)))
in (FStar_SMTEncoding_Term.mkIff _187_1508))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_187_1509)))
in (FStar_SMTEncoding_Term.mkForall _187_1510))
in ((_187_1511), (Some ("/\\ interpretation")), (Some ("l_and-interp"))))
in FStar_SMTEncoding_Term.Assume (_187_1512))
in (_187_1513)::[])))))))))
in (

let mk_or_interp = (fun env disj _90_1943 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (

let valid = (let _187_1522 = (let _187_1521 = (let _187_1520 = (FStar_SMTEncoding_Term.mkApp ((disj), ((a)::(b)::[])))
in (_187_1520)::[])
in (("Valid"), (_187_1521)))
in (FStar_SMTEncoding_Term.mkApp _187_1522))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((b)::[])))
in (let _187_1529 = (let _187_1528 = (let _187_1527 = (let _187_1526 = (let _187_1525 = (let _187_1524 = (let _187_1523 = (FStar_SMTEncoding_Term.mkOr ((valid_a), (valid_b)))
in ((_187_1523), (valid)))
in (FStar_SMTEncoding_Term.mkIff _187_1524))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_187_1525)))
in (FStar_SMTEncoding_Term.mkForall _187_1526))
in ((_187_1527), (Some ("\\/ interpretation")), (Some ("l_or-interp"))))
in FStar_SMTEncoding_Term.Assume (_187_1528))
in (_187_1529)::[])))))))))
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

let valid = (let _187_1538 = (let _187_1537 = (let _187_1536 = (FStar_SMTEncoding_Term.mkApp ((eq2), ((a)::(x)::(y)::[])))
in (_187_1536)::[])
in (("Valid"), (_187_1537)))
in (FStar_SMTEncoding_Term.mkApp _187_1538))
in (let _187_1545 = (let _187_1544 = (let _187_1543 = (let _187_1542 = (let _187_1541 = (let _187_1540 = (let _187_1539 = (FStar_SMTEncoding_Term.mkEq ((x), (y)))
in ((_187_1539), (valid)))
in (FStar_SMTEncoding_Term.mkIff _187_1540))
in ((((valid)::[])::[]), ((aa)::(xx)::(yy)::[]), (_187_1541)))
in (FStar_SMTEncoding_Term.mkForall _187_1542))
in ((_187_1543), (Some ("Eq2 interpretation")), (Some ("eq2-interp"))))
in FStar_SMTEncoding_Term.Assume (_187_1544))
in (_187_1545)::[])))))))))
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

let valid = (let _187_1554 = (let _187_1553 = (let _187_1552 = (FStar_SMTEncoding_Term.mkApp ((eq3), ((a)::(b)::(x)::(y)::[])))
in (_187_1552)::[])
in (("Valid"), (_187_1553)))
in (FStar_SMTEncoding_Term.mkApp _187_1554))
in (let _187_1561 = (let _187_1560 = (let _187_1559 = (let _187_1558 = (let _187_1557 = (let _187_1556 = (let _187_1555 = (FStar_SMTEncoding_Term.mkEq ((x), (y)))
in ((_187_1555), (valid)))
in (FStar_SMTEncoding_Term.mkIff _187_1556))
in ((((valid)::[])::[]), ((aa)::(bb)::(xx)::(yy)::[]), (_187_1557)))
in (FStar_SMTEncoding_Term.mkForall _187_1558))
in ((_187_1559), (Some ("Eq3 interpretation")), (Some ("eq3-interp"))))
in FStar_SMTEncoding_Term.Assume (_187_1560))
in (_187_1561)::[])))))))))))
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

let valid = (let _187_1570 = (let _187_1569 = (let _187_1568 = (FStar_SMTEncoding_Term.mkApp ((imp), ((a)::(b)::[])))
in (_187_1568)::[])
in (("Valid"), (_187_1569)))
in (FStar_SMTEncoding_Term.mkApp _187_1570))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((b)::[])))
in (let _187_1577 = (let _187_1576 = (let _187_1575 = (let _187_1574 = (let _187_1573 = (let _187_1572 = (let _187_1571 = (FStar_SMTEncoding_Term.mkImp ((valid_a), (valid_b)))
in ((_187_1571), (valid)))
in (FStar_SMTEncoding_Term.mkIff _187_1572))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_187_1573)))
in (FStar_SMTEncoding_Term.mkForall _187_1574))
in ((_187_1575), (Some ("==> interpretation")), (Some ("l_imp-interp"))))
in FStar_SMTEncoding_Term.Assume (_187_1576))
in (_187_1577)::[])))))))))
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

let valid = (let _187_1586 = (let _187_1585 = (let _187_1584 = (FStar_SMTEncoding_Term.mkApp ((iff), ((a)::(b)::[])))
in (_187_1584)::[])
in (("Valid"), (_187_1585)))
in (FStar_SMTEncoding_Term.mkApp _187_1586))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((b)::[])))
in (let _187_1593 = (let _187_1592 = (let _187_1591 = (let _187_1590 = (let _187_1589 = (let _187_1588 = (let _187_1587 = (FStar_SMTEncoding_Term.mkIff ((valid_a), (valid_b)))
in ((_187_1587), (valid)))
in (FStar_SMTEncoding_Term.mkIff _187_1588))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_187_1589)))
in (FStar_SMTEncoding_Term.mkForall _187_1590))
in ((_187_1591), (Some ("<==> interpretation")), (Some ("l_iff-interp"))))
in FStar_SMTEncoding_Term.Assume (_187_1592))
in (_187_1593)::[])))))))))
in (

let mk_not_interp = (fun env l_not tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let valid = (let _187_1602 = (let _187_1601 = (let _187_1600 = (FStar_SMTEncoding_Term.mkApp ((l_not), ((a)::[])))
in (_187_1600)::[])
in (("Valid"), (_187_1601)))
in (FStar_SMTEncoding_Term.mkApp _187_1602))
in (

let not_valid_a = (let _187_1603 = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((a)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mkNot _187_1603))
in (let _187_1608 = (let _187_1607 = (let _187_1606 = (let _187_1605 = (let _187_1604 = (FStar_SMTEncoding_Term.mkIff ((not_valid_a), (valid)))
in ((((valid)::[])::[]), ((aa)::[]), (_187_1604)))
in (FStar_SMTEncoding_Term.mkForall _187_1605))
in ((_187_1606), (Some ("not interpretation")), (Some ("l_not-interp"))))
in FStar_SMTEncoding_Term.Assume (_187_1607))
in (_187_1608)::[]))))))
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

let valid = (let _187_1617 = (let _187_1616 = (let _187_1615 = (FStar_SMTEncoding_Term.mkApp ((for_all), ((a)::(b)::[])))
in (_187_1615)::[])
in (("Valid"), (_187_1616)))
in (FStar_SMTEncoding_Term.mkApp _187_1617))
in (

let valid_b_x = (let _187_1620 = (let _187_1619 = (let _187_1618 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_187_1618)::[])
in (("Valid"), (_187_1619)))
in (FStar_SMTEncoding_Term.mkApp _187_1620))
in (let _187_1634 = (let _187_1633 = (let _187_1632 = (let _187_1631 = (let _187_1630 = (let _187_1629 = (let _187_1628 = (let _187_1627 = (let _187_1626 = (let _187_1622 = (let _187_1621 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_187_1621)::[])
in (_187_1622)::[])
in (let _187_1625 = (let _187_1624 = (let _187_1623 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((_187_1623), (valid_b_x)))
in (FStar_SMTEncoding_Term.mkImp _187_1624))
in ((_187_1626), ((xx)::[]), (_187_1625))))
in (FStar_SMTEncoding_Term.mkForall _187_1627))
in ((_187_1628), (valid)))
in (FStar_SMTEncoding_Term.mkIff _187_1629))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_187_1630)))
in (FStar_SMTEncoding_Term.mkForall _187_1631))
in ((_187_1632), (Some ("forall interpretation")), (Some ("forall-interp"))))
in FStar_SMTEncoding_Term.Assume (_187_1633))
in (_187_1634)::[]))))))))))
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

let valid = (let _187_1643 = (let _187_1642 = (let _187_1641 = (FStar_SMTEncoding_Term.mkApp ((for_some), ((a)::(b)::[])))
in (_187_1641)::[])
in (("Valid"), (_187_1642)))
in (FStar_SMTEncoding_Term.mkApp _187_1643))
in (

let valid_b_x = (let _187_1646 = (let _187_1645 = (let _187_1644 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_187_1644)::[])
in (("Valid"), (_187_1645)))
in (FStar_SMTEncoding_Term.mkApp _187_1646))
in (let _187_1660 = (let _187_1659 = (let _187_1658 = (let _187_1657 = (let _187_1656 = (let _187_1655 = (let _187_1654 = (let _187_1653 = (let _187_1652 = (let _187_1648 = (let _187_1647 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_187_1647)::[])
in (_187_1648)::[])
in (let _187_1651 = (let _187_1650 = (let _187_1649 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((_187_1649), (valid_b_x)))
in (FStar_SMTEncoding_Term.mkImp _187_1650))
in ((_187_1652), ((xx)::[]), (_187_1651))))
in (FStar_SMTEncoding_Term.mkExists _187_1653))
in ((_187_1654), (valid)))
in (FStar_SMTEncoding_Term.mkIff _187_1655))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_187_1656)))
in (FStar_SMTEncoding_Term.mkForall _187_1657))
in ((_187_1658), (Some ("exists interpretation")), (Some ("exists-interp"))))
in FStar_SMTEncoding_Term.Assume (_187_1659))
in (_187_1660)::[]))))))))))
in (

let mk_range_interp = (fun env range tt -> (

let range_ty = (FStar_SMTEncoding_Term.mkApp ((range), ([])))
in (let _187_1671 = (let _187_1670 = (let _187_1669 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_ty)
in (let _187_1668 = (let _187_1667 = (varops.mk_unique "typing_range_const")
in Some (_187_1667))
in ((_187_1669), (Some ("Range_const typing")), (_187_1668))))
in FStar_SMTEncoding_Term.Assume (_187_1670))
in (_187_1671)::[])))
in (

let prims = (((FStar_Syntax_Const.unit_lid), (mk_unit)))::(((FStar_Syntax_Const.bool_lid), (mk_bool)))::(((FStar_Syntax_Const.int_lid), (mk_int)))::(((FStar_Syntax_Const.string_lid), (mk_str)))::(((FStar_Syntax_Const.ref_lid), (mk_ref)))::(((FStar_Syntax_Const.true_lid), (mk_true_interp)))::(((FStar_Syntax_Const.false_lid), (mk_false_interp)))::(((FStar_Syntax_Const.and_lid), (mk_and_interp)))::(((FStar_Syntax_Const.or_lid), (mk_or_interp)))::(((FStar_Syntax_Const.eq2_lid), (mk_eq2_interp)))::(((FStar_Syntax_Const.eq3_lid), (mk_eq3_interp)))::(((FStar_Syntax_Const.imp_lid), (mk_imp_interp)))::(((FStar_Syntax_Const.iff_lid), (mk_iff_interp)))::(((FStar_Syntax_Const.not_lid), (mk_not_interp)))::(((FStar_Syntax_Const.forall_lid), (mk_forall_interp)))::(((FStar_Syntax_Const.exists_lid), (mk_exists_interp)))::(((FStar_Syntax_Const.range_lid), (mk_range_interp)))::[]
in (fun env t s tt -> (match ((FStar_Util.find_opt (fun _90_2044 -> (match (_90_2044) with
| (l, _90_2043) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_90_2047, f) -> begin
(f env s tt)
end))))))))))))))))))))))))


let encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let _90_2057 = (encode_function_type_as_formula None None t env)
in (match (_90_2057) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_SMTEncoding_Term.Assume (((form), (Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str))), (Some ((Prims.strcat "lemma_" lid.FStar_Ident.str))))))::[]))
end))))


let encode_free_var : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env fv tt t_norm quals -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if ((let _187_1888 = (FStar_Syntax_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _187_1888)) || (FStar_Syntax_Util.is_lemma t_norm)) then begin
(

let _90_2067 = (new_term_constant_and_tok_from_lid env lid)
in (match (_90_2067) with
| (vname, vtok, env) -> begin
(

let arg_sorts = (match ((let _187_1889 = (FStar_Syntax_Subst.compress t_norm)
in _187_1889.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _90_2070) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun _90_2073 -> FStar_SMTEncoding_Term.Term_sort)))
end
| _90_2076 -> begin
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

let _90_2083 = (prims.mk lid vname)
in (match (_90_2083) with
| (tok, definition) -> begin
(

let env = (push_free_var env lid vname (Some (tok)))
in ((definition), (env)))
end)))
end else begin
(

let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (

let _90_2093 = (

let _90_2088 = (curried_arrow_formals_comp t_norm)
in (match (_90_2088) with
| (args, comp) -> begin
if encode_non_total_function_typ then begin
(let _187_1891 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in ((args), (_187_1891)))
end else begin
((args), (((None), ((FStar_Syntax_Util.comp_result comp)))))
end
end))
in (match (_90_2093) with
| (formals, (pre_opt, res_t)) -> begin
(

let _90_2097 = (new_term_constant_and_tok_from_lid env lid)
in (match (_90_2097) with
| (vname, vtok, env) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
end
| _90_2100 -> begin
(FStar_SMTEncoding_Term.mkApp ((vtok), ([])))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun _90_14 -> (match (_90_14) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(

let _90_2116 = (FStar_Util.prefix vars)
in (match (_90_2116) with
| (_90_2111, (xxsym, _90_2114)) -> begin
(

let xx = (FStar_SMTEncoding_Term.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (let _187_1908 = (let _187_1907 = (let _187_1906 = (let _187_1905 = (let _187_1904 = (let _187_1903 = (let _187_1902 = (let _187_1901 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _187_1901))
in ((vapp), (_187_1902)))
in (FStar_SMTEncoding_Term.mkEq _187_1903))
in ((((vapp)::[])::[]), (vars), (_187_1904)))
in (FStar_SMTEncoding_Term.mkForall _187_1905))
in ((_187_1906), (Some ("Discriminator equation")), (Some ((Prims.strcat "disc_equation_" (escape d.FStar_Ident.str))))))
in FStar_SMTEncoding_Term.Assume (_187_1907))
in (_187_1908)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(

let _90_2128 = (FStar_Util.prefix vars)
in (match (_90_2128) with
| (_90_2123, (xxsym, _90_2126)) -> begin
(

let xx = (FStar_SMTEncoding_Term.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (

let tp_name = (mk_term_projector_name d f)
in (

let prim_app = (FStar_SMTEncoding_Term.mkApp ((tp_name), ((xx)::[])))
in (let _187_1913 = (let _187_1912 = (let _187_1911 = (let _187_1910 = (let _187_1909 = (FStar_SMTEncoding_Term.mkEq ((vapp), (prim_app)))
in ((((vapp)::[])::[]), (vars), (_187_1909)))
in (FStar_SMTEncoding_Term.mkForall _187_1910))
in ((_187_1911), (Some ("Projector equation")), (Some ((Prims.strcat "proj_equation_" tp_name)))))
in FStar_SMTEncoding_Term.Assume (_187_1912))
in (_187_1913)::[])))))
end))
end
| _90_2134 -> begin
[]
end)))))
in (

let _90_2141 = (encode_binders None formals env)
in (match (_90_2141) with
| (vars, guards, env', decls1, _90_2140) -> begin
(

let _90_2150 = (match (pre_opt) with
| None -> begin
(let _187_1914 = (FStar_SMTEncoding_Term.mk_and_l guards)
in ((_187_1914), (decls1)))
end
| Some (p) -> begin
(

let _90_2147 = (encode_formula p env')
in (match (_90_2147) with
| (g, ds) -> begin
(let _187_1915 = (FStar_SMTEncoding_Term.mk_and_l ((g)::guards))
in ((_187_1915), ((FStar_List.append decls1 ds))))
end))
end)
in (match (_90_2150) with
| (guard, decls1) -> begin
(

let vtok_app = (mk_Apply vtok_tm vars)
in (

let vapp = (let _187_1917 = (let _187_1916 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in ((vname), (_187_1916)))
in (FStar_SMTEncoding_Term.mkApp _187_1917))
in (

let _90_2174 = (

let vname_decl = (let _187_1920 = (let _187_1919 = (FStar_All.pipe_right formals (FStar_List.map (fun _90_2153 -> FStar_SMTEncoding_Term.Term_sort)))
in ((vname), (_187_1919), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (_187_1920))
in (

let _90_2161 = (

let env = (

let _90_2156 = env
in {bindings = _90_2156.bindings; depth = _90_2156.depth; tcenv = _90_2156.tcenv; warn = _90_2156.warn; cache = _90_2156.cache; nolabels = _90_2156.nolabels; use_zfuel_name = _90_2156.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in if (not ((head_normal env tt))) then begin
(encode_term_pred None tt env vtok_tm)
end else begin
(encode_term_pred None t_norm env vtok_tm)
end)
in (match (_90_2161) with
| (tok_typing, decls2) -> begin
(

let tok_typing = FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("function token typing")), (Some ((Prims.strcat "function_token_typing_" vname)))))
in (

let _90_2171 = (match (formals) with
| [] -> begin
(let _187_1924 = (let _187_1923 = (let _187_1922 = (FStar_SMTEncoding_Term.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left (fun _187_1921 -> Some (_187_1921)) _187_1922))
in (push_free_var env lid vname _187_1923))
in (((FStar_List.append decls2 ((tok_typing)::[]))), (_187_1924)))
end
| _90_2165 -> begin
(

let vtok_decl = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let vtok_fresh = (let _187_1925 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((vtok), (FStar_SMTEncoding_Term.Term_sort)) _187_1925))
in (

let name_tok_corr = (let _187_1929 = (let _187_1928 = (let _187_1927 = (let _187_1926 = (FStar_SMTEncoding_Term.mkEq ((vtok_app), (vapp)))
in ((((vtok_app)::[])::((vapp)::[])::[]), (vars), (_187_1926)))
in (FStar_SMTEncoding_Term.mkForall _187_1927))
in ((_187_1928), (Some ("Name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" vname)))))
in FStar_SMTEncoding_Term.Assume (_187_1929))
in (((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[]))), (env)))))
end)
in (match (_90_2171) with
| (tok_decl, env) -> begin
(((vname_decl)::tok_decl), (env))
end)))
end)))
in (match (_90_2174) with
| (decls2, env) -> begin
(

let _90_2182 = (

let res_t = (FStar_Syntax_Subst.compress res_t)
in (

let _90_2178 = (encode_term res_t env')
in (match (_90_2178) with
| (encoded_res_t, decls) -> begin
(let _187_1930 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in ((encoded_res_t), (_187_1930), (decls)))
end)))
in (match (_90_2182) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (let _187_1934 = (let _187_1933 = (let _187_1932 = (let _187_1931 = (FStar_SMTEncoding_Term.mkImp ((guard), (ty_pred)))
in ((((vapp)::[])::[]), (vars), (_187_1931)))
in (FStar_SMTEncoding_Term.mkForall _187_1932))
in ((_187_1933), (Some ("free var typing")), (Some ((Prims.strcat "typing_" vname)))))
in FStar_SMTEncoding_Term.Assume (_187_1934))
in (

let freshness = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New)) then begin
(let _187_1940 = (let _187_1937 = (let _187_1936 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (let _187_1935 = (varops.next_id ())
in ((vname), (_187_1936), (FStar_SMTEncoding_Term.Term_sort), (_187_1935))))
in (FStar_SMTEncoding_Term.fresh_constructor _187_1937))
in (let _187_1939 = (let _187_1938 = (pretype_axiom vapp vars)
in (_187_1938)::[])
in (_187_1940)::_187_1939))
end else begin
[]
end
in (

let g = (let _187_1945 = (let _187_1944 = (let _187_1943 = (let _187_1942 = (let _187_1941 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_187_1941)
in (FStar_List.append freshness _187_1942))
in (FStar_List.append decls3 _187_1943))
in (FStar_List.append decls2 _187_1944))
in (FStar_List.append decls1 _187_1945))
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

let _90_2193 = (encode_free_var env x t t_norm [])
in (match (_90_2193) with
| (decls, env) -> begin
(

let _90_2198 = (lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_90_2198) with
| (n, x', _90_2197) -> begin
((((n), (x'))), (decls), (env))
end))
end))
end
| Some (n, x, _90_2202) -> begin
((((n), (x))), ([]), (env))
end))


let encode_top_level_val : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env lid t quals -> (

let tt = (norm env t)
in (

let _90_2212 = (encode_free_var env lid t tt quals)
in (match (_90_2212) with
| (decls, env) -> begin
if (FStar_Syntax_Util.is_smt_lemma t) then begin
(let _187_1963 = (let _187_1962 = (encode_smt_lemma env lid tt)
in (FStar_List.append decls _187_1962))
in ((_187_1963), (env)))
end else begin
((decls), (env))
end
end))))


let encode_top_level_vals : env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _90_2218 lb -> (match (_90_2218) with
| (decls, env) -> begin
(

let _90_2222 = (let _187_1972 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env _187_1972 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (_90_2222) with
| (decls', env) -> begin
(((FStar_List.append decls decls')), (env))
end))
end)) (([]), (env)))))


let encode_top_level_let : env_t  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env _90_2226 quals -> (match (_90_2226) with
| (is_rec, bindings) -> begin
(

let eta_expand = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let _90_2236 = (FStar_Util.first_N nbinders formals)
in (match (_90_2236) with
| (formals, extra_formals) -> begin
(

let subst = (FStar_List.map2 (fun _90_2240 _90_2244 -> (match (((_90_2240), (_90_2244))) with
| ((formal, _90_2239), (binder, _90_2243)) -> begin
(let _187_1990 = (let _187_1989 = (FStar_Syntax_Syntax.bv_to_name binder)
in ((formal), (_187_1989)))
in FStar_Syntax_Syntax.NT (_187_1990))
end)) formals binders)
in (

let extra_formals = (let _187_1994 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun _90_2248 -> (match (_90_2248) with
| (x, i) -> begin
(let _187_1993 = (

let _90_2249 = x
in (let _187_1992 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _90_2249.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _90_2249.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _187_1992}))
in ((_187_1993), (i)))
end))))
in (FStar_All.pipe_right _187_1994 FStar_Syntax_Util.name_binders))
in (

let body = (let _187_2001 = (FStar_Syntax_Subst.compress body)
in (let _187_2000 = (let _187_1995 = (FStar_Syntax_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _187_1995))
in (let _187_1999 = (let _187_1998 = (let _187_1997 = (FStar_Syntax_Subst.subst subst t)
in _187_1997.FStar_Syntax_Syntax.n)
in (FStar_All.pipe_left (fun _187_1996 -> Some (_187_1996)) _187_1998))
in (FStar_Syntax_Syntax.extend_app_n _187_2001 _187_2000 _187_1999 body.FStar_Syntax_Syntax.pos))))
in (((FStar_List.append binders extra_formals)), (body)))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (

let rec aux = (fun norm t_norm -> (match ((let _187_2012 = (FStar_Syntax_Util.unascribe e)
in _187_2012.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, lopt) -> begin
(

let _90_2268 = (FStar_Syntax_Subst.open_term' binders body)
in (match (_90_2268) with
| (binders, body, opening) -> begin
(match ((let _187_2013 = (FStar_Syntax_Subst.compress t_norm)
in _187_2013.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let _90_2275 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_90_2275) with
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

let _90_2282 = (FStar_Util.first_N nformals binders)
in (match (_90_2282) with
| (bs0, rest) -> begin
(

let c = (

let subst = (FStar_List.map2 (fun _90_2286 _90_2290 -> (match (((_90_2286), (_90_2290))) with
| ((b, _90_2285), (x, _90_2289)) -> begin
(let _187_2017 = (let _187_2016 = (FStar_Syntax_Syntax.bv_to_name x)
in ((b), (_187_2016)))
in FStar_Syntax_Syntax.NT (_187_2017))
end)) bs0 formals)
in (FStar_Syntax_Subst.subst_comp subst c))
in (

let body = (FStar_Syntax_Util.abs rest body lopt)
in ((((bs0), (body), (bs0), ((FStar_Syntax_Util.comp_result c)))), (false))))
end)))
end else begin
if (nformals > nbinders) then begin
(

let _90_2296 = (eta_expand binders formals body tres)
in (match (_90_2296) with
| (binders, body) -> begin
((((binders), (body), (formals), (tres))), (false))
end))
end else begin
((((binders), (body), (formals), (tres))), (false))
end
end)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, _90_2299) -> begin
(let _187_2019 = (let _187_2018 = (aux norm x.FStar_Syntax_Syntax.sort)
in (Prims.fst _187_2018))
in ((_187_2019), (true)))
end
| _90_2303 when (not (norm)) -> begin
(

let t_norm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm)
in (aux true t_norm))
end
| _90_2306 -> begin
(let _187_2022 = (let _187_2021 = (FStar_Syntax_Print.term_to_string e)
in (let _187_2020 = (FStar_Syntax_Print.term_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str _187_2021 _187_2020)))
in (FStar_All.failwith _187_2022))
end)
end))
end
| _90_2308 -> begin
(match ((let _187_2023 = (FStar_Syntax_Subst.compress t_norm)
in _187_2023.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let _90_2315 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_90_2315) with
| (formals, c) -> begin
(

let tres = (FStar_Syntax_Util.comp_result c)
in (

let _90_2319 = (eta_expand [] formals e tres)
in (match (_90_2319) with
| (binders, body) -> begin
((((binders), (body), (formals), (tres))), (false))
end)))
end))
end
| _90_2321 -> begin
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

let _90_2349 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _90_2336 lb -> (match (_90_2336) with
| (toks, typs, decls, env) -> begin
(

let _90_2338 = if (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) then begin
(Prims.raise Let_rec_unencodeable)
end else begin
()
end
in (

let t_norm = (whnf env lb.FStar_Syntax_Syntax.lbtyp)
in (

let _90_2344 = (let _187_2028 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env _187_2028 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (_90_2344) with
| (tok, decl, env) -> begin
(let _187_2031 = (let _187_2030 = (let _187_2029 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in ((_187_2029), (tok)))
in (_187_2030)::toks)
in ((_187_2031), ((t_norm)::typs), ((decl)::decls), (env)))
end))))
end)) (([]), ([]), ([]), (env))))
in (match (_90_2349) with
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
(FStar_SMTEncoding_Term.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
end
| _90_2360 -> begin
if curry then begin
(match (ftok) with
| Some (ftok) -> begin
(mk_Apply ftok vars)
end
| None -> begin
(let _187_2040 = (FStar_SMTEncoding_Term.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply _187_2040 vars))
end)
end else begin
(let _187_2042 = (let _187_2041 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in ((f), (_187_2041)))
in (FStar_SMTEncoding_Term.mkApp _187_2042))
end
end))
in if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _90_15 -> (match (_90_15) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| _90_2367 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> (let _187_2045 = (FStar_Syntax_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _187_2045)))))) then begin
((decls), (env))
end else begin
if (not (is_rec)) then begin
(match (((bindings), (typs), (toks))) with
| (({FStar_Syntax_Syntax.lbname = _90_2377; FStar_Syntax_Syntax.lbunivs = _90_2375; FStar_Syntax_Syntax.lbtyp = _90_2373; FStar_Syntax_Syntax.lbeff = _90_2371; FStar_Syntax_Syntax.lbdef = e})::[], (t_norm)::[], ((flid_fv, (f, ftok)))::[]) -> begin
(

let e = (FStar_Syntax_Subst.compress e)
in (

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let _90_2399 = (destruct_bound_function flid t_norm e)
in (match (_90_2399) with
| ((binders, body, _90_2394, _90_2396), curry) -> begin
(

let _90_2406 = (encode_binders None binders env)
in (match (_90_2406) with
| (vars, guards, env', binder_decls, _90_2405) -> begin
(

let app = (mk_app curry f ftok vars)
in (

let _90_2412 = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic)) then begin
(let _187_2047 = (FStar_SMTEncoding_Term.mk_Valid app)
in (let _187_2046 = (encode_formula body env')
in ((_187_2047), (_187_2046))))
end else begin
(let _187_2048 = (encode_term body env')
in ((app), (_187_2048)))
end
in (match (_90_2412) with
| (app, (body, decls2)) -> begin
(

let eqn = (let _187_2054 = (let _187_2053 = (let _187_2050 = (let _187_2049 = (FStar_SMTEncoding_Term.mkEq ((app), (body)))
in ((((app)::[])::[]), (vars), (_187_2049)))
in (FStar_SMTEncoding_Term.mkForall _187_2050))
in (let _187_2052 = (let _187_2051 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (_187_2051))
in ((_187_2053), (_187_2052), (Some ((Prims.strcat "equation_" f))))))
in FStar_SMTEncoding_Term.Assume (_187_2054))
in (let _187_2059 = (let _187_2058 = (let _187_2057 = (let _187_2056 = (let _187_2055 = (primitive_type_axioms env.tcenv flid f app)
in (FStar_List.append ((eqn)::[]) _187_2055))
in (FStar_List.append decls2 _187_2056))
in (FStar_List.append binder_decls _187_2057))
in (FStar_List.append decls _187_2058))
in ((_187_2059), (env))))
end)))
end))
end))))
end
| _90_2415 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(

let fuel = (let _187_2060 = (varops.fresh "fuel")
in ((_187_2060), (FStar_SMTEncoding_Term.Fuel_sort)))
in (

let fuel_tm = (FStar_SMTEncoding_Term.mkFreeV fuel)
in (

let env0 = env
in (

let _90_2433 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _90_2421 _90_2426 -> (match (((_90_2421), (_90_2426))) with
| ((gtoks, env), (flid_fv, (f, ftok))) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let g = (let _187_2063 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented")
in (varops.new_fvar _187_2063))
in (

let gtok = (let _187_2064 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented_token")
in (varops.new_fvar _187_2064))
in (

let env = (let _187_2067 = (let _187_2066 = (FStar_SMTEncoding_Term.mkApp ((g), ((fuel_tm)::[])))
in (FStar_All.pipe_left (fun _187_2065 -> Some (_187_2065)) _187_2066))
in (push_free_var env flid gtok _187_2067))
in (((((flid), (f), (ftok), (g), (gtok)))::gtoks), (env))))))
end)) (([]), (env))))
in (match (_90_2433) with
| (gtoks, env) -> begin
(

let gtoks = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env0 _90_2442 t_norm _90_2453 -> (match (((_90_2442), (_90_2453))) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = _90_2452; FStar_Syntax_Syntax.lbunivs = _90_2450; FStar_Syntax_Syntax.lbtyp = _90_2448; FStar_Syntax_Syntax.lbeff = _90_2446; FStar_Syntax_Syntax.lbdef = e}) -> begin
(

let _90_2460 = (destruct_bound_function flid t_norm e)
in (match (_90_2460) with
| ((binders, body, formals, tres), curry) -> begin
(

let _90_2461 = if curry then begin
(FStar_All.failwith "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type")
end else begin
()
end
in (

let _90_2469 = (encode_binders None binders env)
in (match (_90_2469) with
| (vars, guards, env', binder_decls, _90_2468) -> begin
(

let decl_g = (let _187_2078 = (let _187_2077 = (let _187_2076 = (FStar_List.map Prims.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::_187_2076)
in ((g), (_187_2077), (FStar_SMTEncoding_Term.Term_sort), (Some ("Fuel-instrumented function name"))))
in FStar_SMTEncoding_Term.DeclFun (_187_2078))
in (

let env0 = (push_zfuel_name env0 flid g)
in (

let decl_g_tok = FStar_SMTEncoding_Term.DeclFun (((gtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Token for fuel-instrumented partial applications"))))
in (

let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (

let app = (let _187_2080 = (let _187_2079 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in ((f), (_187_2079)))
in (FStar_SMTEncoding_Term.mkApp _187_2080))
in (

let gsapp = (let _187_2083 = (let _187_2082 = (let _187_2081 = (FStar_SMTEncoding_Term.mkApp (("SFuel"), ((fuel_tm)::[])))
in (_187_2081)::vars_tm)
in ((g), (_187_2082)))
in (FStar_SMTEncoding_Term.mkApp _187_2083))
in (

let gmax = (let _187_2086 = (let _187_2085 = (let _187_2084 = (FStar_SMTEncoding_Term.mkApp (("MaxFuel"), ([])))
in (_187_2084)::vars_tm)
in ((g), (_187_2085)))
in (FStar_SMTEncoding_Term.mkApp _187_2086))
in (

let _90_2479 = (encode_term body env')
in (match (_90_2479) with
| (body_tm, decls2) -> begin
(

let eqn_g = (let _187_2092 = (let _187_2091 = (let _187_2088 = (let _187_2087 = (FStar_SMTEncoding_Term.mkEq ((gsapp), (body_tm)))
in ((((gsapp)::[])::[]), (Some ((Prims.parse_int "0"))), ((fuel)::vars), (_187_2087)))
in (FStar_SMTEncoding_Term.mkForall' _187_2088))
in (let _187_2090 = (let _187_2089 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (_187_2089))
in ((_187_2091), (_187_2090), (Some ((Prims.strcat "equation_with_fuel_" g))))))
in FStar_SMTEncoding_Term.Assume (_187_2092))
in (

let eqn_f = (let _187_2096 = (let _187_2095 = (let _187_2094 = (let _187_2093 = (FStar_SMTEncoding_Term.mkEq ((app), (gmax)))
in ((((app)::[])::[]), (vars), (_187_2093)))
in (FStar_SMTEncoding_Term.mkForall _187_2094))
in ((_187_2095), (Some ("Correspondence of recursive function to instrumented version")), (Some ((Prims.strcat "fuel_correspondence_" g)))))
in FStar_SMTEncoding_Term.Assume (_187_2096))
in (

let eqn_g' = (let _187_2105 = (let _187_2104 = (let _187_2103 = (let _187_2102 = (let _187_2101 = (let _187_2100 = (let _187_2099 = (let _187_2098 = (let _187_2097 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "0"))
in (_187_2097)::vars_tm)
in ((g), (_187_2098)))
in (FStar_SMTEncoding_Term.mkApp _187_2099))
in ((gsapp), (_187_2100)))
in (FStar_SMTEncoding_Term.mkEq _187_2101))
in ((((gsapp)::[])::[]), ((fuel)::vars), (_187_2102)))
in (FStar_SMTEncoding_Term.mkForall _187_2103))
in ((_187_2104), (Some ("Fuel irrelevance")), (Some ((Prims.strcat "fuel_irrelevance_" g)))))
in FStar_SMTEncoding_Term.Assume (_187_2105))
in (

let _90_2502 = (

let _90_2489 = (encode_binders None formals env0)
in (match (_90_2489) with
| (vars, v_guards, env, binder_decls, _90_2488) -> begin
(

let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (

let gapp = (FStar_SMTEncoding_Term.mkApp ((g), ((fuel_tm)::vars_tm)))
in (

let tok_corr = (

let tok_app = (let _187_2106 = (FStar_SMTEncoding_Term.mkFreeV ((gtok), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply _187_2106 ((fuel)::vars)))
in (let _187_2110 = (let _187_2109 = (let _187_2108 = (let _187_2107 = (FStar_SMTEncoding_Term.mkEq ((tok_app), (gapp)))
in ((((tok_app)::[])::[]), ((fuel)::vars), (_187_2107)))
in (FStar_SMTEncoding_Term.mkForall _187_2108))
in ((_187_2109), (Some ("Fuel token correspondence")), (Some ((Prims.strcat "fuel_token_correspondence_" gtok)))))
in FStar_SMTEncoding_Term.Assume (_187_2110)))
in (

let _90_2499 = (

let _90_2496 = (encode_term_pred None tres env gapp)
in (match (_90_2496) with
| (g_typing, d3) -> begin
(let _187_2118 = (let _187_2117 = (let _187_2116 = (let _187_2115 = (let _187_2114 = (let _187_2113 = (let _187_2112 = (let _187_2111 = (FStar_SMTEncoding_Term.mk_and_l v_guards)
in ((_187_2111), (g_typing)))
in (FStar_SMTEncoding_Term.mkImp _187_2112))
in ((((gapp)::[])::[]), ((fuel)::vars), (_187_2113)))
in (FStar_SMTEncoding_Term.mkForall _187_2114))
in ((_187_2115), (Some ("Typing correspondence of token to term")), (Some ((Prims.strcat "token_correspondence_" g)))))
in FStar_SMTEncoding_Term.Assume (_187_2116))
in (_187_2117)::[])
in ((d3), (_187_2118)))
end))
in (match (_90_2499) with
| (aux_decls, typing_corr) -> begin
(((FStar_List.append binder_decls aux_decls)), ((FStar_List.append typing_corr ((tok_corr)::[]))))
end)))))
end))
in (match (_90_2502) with
| (aux_decls, g_typing) -> begin
(((FStar_List.append binder_decls (FStar_List.append decls2 (FStar_List.append aux_decls ((decl_g)::(decl_g_tok)::[]))))), ((FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing)), (env0))
end)))))
end)))))))))
end)))
end))
end))
in (

let _90_2518 = (let _187_2121 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _90_2506 _90_2510 -> (match (((_90_2506), (_90_2510))) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(

let _90_2514 = (encode_one_binding env0 gtok ty bs)
in (match (_90_2514) with
| (decls', eqns', env0) -> begin
(((decls')::decls), ((FStar_List.append eqns' eqns)), (env0))
end))
end)) (((decls)::[]), ([]), (env0)) _187_2121))
in (match (_90_2518) with
| (decls, eqns, env0) -> begin
(

let _90_2527 = (let _187_2123 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _187_2123 (FStar_List.partition (fun _90_16 -> (match (_90_16) with
| FStar_SMTEncoding_Term.DeclFun (_90_2521) -> begin
true
end
| _90_2524 -> begin
false
end)))))
in (match (_90_2527) with
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

let msg = (let _187_2126 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _187_2126 (FStar_String.concat " and ")))
in (

let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in (((decl)::[]), (env))))
end))
end))


let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let _90_2531 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _187_2135 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _187_2135))
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

let _90_2539 = (encode_sigelt' env se)
in (match (_90_2539) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _187_2138 = (let _187_2137 = (let _187_2136 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (_187_2136))
in (_187_2137)::[])
in ((_187_2138), (e)))
end
| _90_2542 -> begin
(let _187_2145 = (let _187_2144 = (let _187_2140 = (let _187_2139 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_187_2139))
in (_187_2140)::g)
in (let _187_2143 = (let _187_2142 = (let _187_2141 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_187_2141))
in (_187_2142)::[])
in (FStar_List.append _187_2144 _187_2143)))
in ((_187_2145), (e)))
end)
end)))))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let should_skip = (fun l -> false)
in (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_90_2548) -> begin
(FStar_All.failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _90_2564) -> begin
if (let _187_2150 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right _187_2150 Prims.op_Negation)) then begin
(([]), (env))
end else begin
(

let close_effect_params = (fun tm -> (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
tm
end
| _90_2571 -> begin
(let _187_2156 = (let _187_2155 = (let _187_2154 = (FStar_All.pipe_left (fun _187_2153 -> Some (_187_2153)) (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid)))
in ((ed.FStar_Syntax_Syntax.binders), (tm), (_187_2154)))
in FStar_Syntax_Syntax.Tm_abs (_187_2155))
in (FStar_Syntax_Syntax.mk _187_2156 None tm.FStar_Syntax_Syntax.pos))
end))
in (

let encode_action = (fun env a -> (

let _90_2578 = (new_term_constant_and_tok_from_lid env a.FStar_Syntax_Syntax.action_name)
in (match (_90_2578) with
| (aname, atok, env) -> begin
(

let _90_2582 = (FStar_Syntax_Util.arrow_formals_comp a.FStar_Syntax_Syntax.action_typ)
in (match (_90_2582) with
| (formals, _90_2581) -> begin
(

let _90_2585 = (let _187_2161 = (close_effect_params a.FStar_Syntax_Syntax.action_defn)
in (encode_term _187_2161 env))
in (match (_90_2585) with
| (tm, decls) -> begin
(

let a_decls = (let _187_2165 = (let _187_2164 = (let _187_2163 = (FStar_All.pipe_right formals (FStar_List.map (fun _90_2586 -> FStar_SMTEncoding_Term.Term_sort)))
in ((aname), (_187_2163), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action"))))
in FStar_SMTEncoding_Term.DeclFun (_187_2164))
in (_187_2165)::(FStar_SMTEncoding_Term.DeclFun (((atok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action token")))))::[])
in (

let _90_2600 = (let _187_2167 = (FStar_All.pipe_right formals (FStar_List.map (fun _90_2592 -> (match (_90_2592) with
| (bv, _90_2591) -> begin
(

let _90_2597 = (gen_term_var env bv)
in (match (_90_2597) with
| (xxsym, xx, _90_2596) -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (xx))
end))
end))))
in (FStar_All.pipe_right _187_2167 FStar_List.split))
in (match (_90_2600) with
| (xs_sorts, xs) -> begin
(

let app = (let _187_2171 = (let _187_2170 = (let _187_2169 = (let _187_2168 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Var (aname)), (xs)))))
in (_187_2168)::[])
in ((FStar_SMTEncoding_Term.Var ("Reify")), (_187_2169)))
in FStar_SMTEncoding_Term.App (_187_2170))
in (FStar_All.pipe_right _187_2171 FStar_SMTEncoding_Term.mk))
in (

let a_eq = (let _187_2177 = (let _187_2176 = (let _187_2175 = (let _187_2174 = (let _187_2173 = (let _187_2172 = (mk_Apply tm xs_sorts)
in ((app), (_187_2172)))
in (FStar_SMTEncoding_Term.mkEq _187_2173))
in ((((app)::[])::[]), (xs_sorts), (_187_2174)))
in (FStar_SMTEncoding_Term.mkForall _187_2175))
in ((_187_2176), (Some ("Action equality")), (Some ((Prims.strcat aname "_equality")))))
in FStar_SMTEncoding_Term.Assume (_187_2177))
in (

let tok_correspondence = (

let tok_term = (FStar_SMTEncoding_Term.mkFreeV ((atok), (FStar_SMTEncoding_Term.Term_sort)))
in (

let tok_app = (mk_Apply tok_term xs_sorts)
in (let _187_2181 = (let _187_2180 = (let _187_2179 = (let _187_2178 = (FStar_SMTEncoding_Term.mkEq ((tok_app), (app)))
in ((((tok_app)::[])::[]), (xs_sorts), (_187_2178)))
in (FStar_SMTEncoding_Term.mkForall _187_2179))
in ((_187_2180), (Some ("Action token correspondence")), (Some ((Prims.strcat aname "_token_correspondence")))))
in FStar_SMTEncoding_Term.Assume (_187_2181))))
in ((env), ((FStar_List.append decls (FStar_List.append a_decls ((a_eq)::(tok_correspondence)::[]))))))))
end)))
end))
end))
end)))
in (

let _90_2608 = (FStar_Util.fold_map encode_action env ed.FStar_Syntax_Syntax.actions)
in (match (_90_2608) with
| (env, decls2) -> begin
(((FStar_List.flatten decls2)), (env))
end))))
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _90_2611, _90_2613, _90_2615, _90_2617) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid) -> begin
(

let _90_2623 = (new_term_constant_and_tok_from_lid env lid)
in (match (_90_2623) with
| (tname, ttok, env) -> begin
(([]), (env))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _90_2626, t, quals, _90_2630) -> begin
(

let will_encode_definition = (not ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _90_17 -> (match (_90_17) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Irreducible) -> begin
true
end
| _90_2643 -> begin
false
end))))))
in if will_encode_definition then begin
(([]), (env))
end else begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (

let _90_2648 = (encode_top_level_val env fv t quals)
in (match (_90_2648) with
| (decls, env) -> begin
(

let tname = lid.FStar_Ident.str
in (

let tsym = (FStar_SMTEncoding_Term.mkFreeV ((tname), (FStar_SMTEncoding_Term.Term_sort)))
in (let _187_2184 = (let _187_2183 = (primitive_type_axioms env.tcenv lid tname tsym)
in (FStar_List.append decls _187_2183))
in ((_187_2184), (env)))))
end)))
end)
end
| FStar_Syntax_Syntax.Sig_assume (l, f, _90_2654, _90_2656) -> begin
(

let _90_2661 = (encode_formula f env)
in (match (_90_2661) with
| (f, decls) -> begin
(

let g = (let _187_2191 = (let _187_2190 = (let _187_2189 = (let _187_2186 = (let _187_2185 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" _187_2185))
in Some (_187_2186))
in (let _187_2188 = (let _187_2187 = (varops.mk_unique (Prims.strcat "assumption_" l.FStar_Ident.str))
in Some (_187_2187))
in ((f), (_187_2189), (_187_2188))))
in FStar_SMTEncoding_Term.Assume (_187_2190))
in (_187_2191)::[])
in (((FStar_List.append decls g)), (env)))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _90_2666, quals) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) -> begin
(

let _90_2679 = (FStar_Util.fold_map (fun env lb -> (

let lid = (let _187_2195 = (let _187_2194 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _187_2194.FStar_Syntax_Syntax.fv_name)
in _187_2195.FStar_Syntax_Syntax.v)
in if (let _187_2196 = (FStar_TypeChecker_Env.try_lookup_val_decl env.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone _187_2196)) then begin
(

let val_decl = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), (r)))
in (

let _90_2676 = (encode_sigelt' env val_decl)
in (match (_90_2676) with
| (decls, env) -> begin
((env), (decls))
end)))
end else begin
((env), ([]))
end)) env (Prims.snd lbs))
in (match (_90_2679) with
| (env, decls) -> begin
(((FStar_List.flatten decls)), (env))
end))
end
| FStar_Syntax_Syntax.Sig_let ((_90_2681, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t); FStar_Syntax_Syntax.lbunivs = _90_2689; FStar_Syntax_Syntax.lbtyp = _90_2687; FStar_Syntax_Syntax.lbeff = _90_2685; FStar_Syntax_Syntax.lbdef = _90_2683})::[]), _90_2696, _90_2698, _90_2700) when (FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Syntax_Const.b2t_lid) -> begin
(

let _90_2706 = (new_term_constant_and_tok_from_lid env b2t.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_90_2706) with
| (tname, ttok, env) -> begin
(

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (

let valid_b2t_x = (let _187_2199 = (let _187_2198 = (let _187_2197 = (FStar_SMTEncoding_Term.mkApp (("Prims.b2t"), ((x)::[])))
in (_187_2197)::[])
in (("Valid"), (_187_2198)))
in (FStar_SMTEncoding_Term.mkApp _187_2199))
in (

let decls = (let _187_2207 = (let _187_2206 = (let _187_2205 = (let _187_2204 = (let _187_2203 = (let _187_2202 = (let _187_2201 = (let _187_2200 = (FStar_SMTEncoding_Term.mkApp (("BoxBool_proj_0"), ((x)::[])))
in ((valid_b2t_x), (_187_2200)))
in (FStar_SMTEncoding_Term.mkEq _187_2201))
in ((((valid_b2t_x)::[])::[]), ((xx)::[]), (_187_2202)))
in (FStar_SMTEncoding_Term.mkForall _187_2203))
in ((_187_2204), (Some ("b2t def")), (Some ("b2t_def"))))
in FStar_SMTEncoding_Term.Assume (_187_2205))
in (_187_2206)::[])
in (FStar_SMTEncoding_Term.DeclFun (((tname), ((FStar_SMTEncoding_Term.Term_sort)::[]), (FStar_SMTEncoding_Term.Term_sort), (None))))::_187_2207)
in ((decls), (env))))))
end))
end
| FStar_Syntax_Syntax.Sig_let (_90_2712, _90_2714, _90_2716, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _90_18 -> (match (_90_18) with
| FStar_Syntax_Syntax.Discriminator (_90_2722) -> begin
true
end
| _90_2725 -> begin
false
end)))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let (_90_2727, _90_2729, lids, quals) when ((FStar_All.pipe_right lids (FStar_Util.for_some (fun l -> ((let _187_2210 = (FStar_List.hd l.FStar_Ident.ns)
in _187_2210.FStar_Ident.idText) = "Prims")))) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun _90_19 -> (match (_90_19) with
| FStar_Syntax_Syntax.Inline -> begin
true
end
| _90_2738 -> begin
false
end))))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _90_2744, _90_2746, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _90_20 -> (match (_90_20) with
| FStar_Syntax_Syntax.Projector (_90_2752) -> begin
true
end
| _90_2755 -> begin
false
end)))) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((try_lookup_free_var env l)) with
| Some (_90_2759) -> begin
(([]), (env))
end
| None -> begin
(

let se = FStar_Syntax_Syntax.Sig_declare_typ (((l), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), ((FStar_Ident.range_of_lid l))))
in (encode_sigelt env se))
end)))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _90_2768, _90_2770, quals) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) -> begin
(match ((let _187_2213 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef)
in _187_2213.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, _90_2777) -> begin
(

let body = (FStar_Syntax_Util.mk_reify body)
in (

let tm = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None)))) None lb.FStar_Syntax_Syntax.lbdef.FStar_Syntax_Syntax.pos)
in (

let tm' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env.tcenv tm)
in (

let lb_typ = (

let _90_2785 = (FStar_Syntax_Util.arrow_formals_comp lb.FStar_Syntax_Syntax.lbtyp)
in (match (_90_2785) with
| (formals, comp) -> begin
(

let reified_typ = (FStar_TypeChecker_Util.reify_comp (

let _90_2786 = env.tcenv
in {FStar_TypeChecker_Env.solver = _90_2786.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _90_2786.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _90_2786.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _90_2786.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _90_2786.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _90_2786.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _90_2786.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _90_2786.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _90_2786.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _90_2786.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _90_2786.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _90_2786.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _90_2786.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _90_2786.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _90_2786.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _90_2786.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _90_2786.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _90_2786.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _90_2786.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _90_2786.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _90_2786.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _90_2786.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _90_2786.FStar_TypeChecker_Env.qname_and_index}) (FStar_Syntax_Util.lcomp_of_comp comp) FStar_Syntax_Syntax.U_unknown)
in (let _187_2214 = (FStar_Syntax_Syntax.mk_Total reified_typ)
in (FStar_Syntax_Util.arrow formals _187_2214)))
end))
in (

let lb = (

let _90_2790 = lb
in {FStar_Syntax_Syntax.lbname = _90_2790.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _90_2790.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lb_typ; FStar_Syntax_Syntax.lbeff = _90_2790.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = tm'})
in (encode_top_level_let env ((false), ((lb)::[])) quals))))))
end
| _90_2794 -> begin
(([]), (env))
end)
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), _90_2799, _90_2801, quals) -> begin
(encode_top_level_let env ((is_rec), (bindings)) quals)
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _90_2807, _90_2809, _90_2811) -> begin
(

let _90_2816 = (encode_signature env ses)
in (match (_90_2816) with
| (g, env) -> begin
(

let _90_2830 = (FStar_All.pipe_right g (FStar_List.partition (fun _90_21 -> (match (_90_21) with
| FStar_SMTEncoding_Term.Assume (_90_2819, Some ("inversion axiom"), _90_2823) -> begin
false
end
| _90_2827 -> begin
true
end))))
in (match (_90_2830) with
| (g', inversions) -> begin
(

let _90_2839 = (FStar_All.pipe_right g' (FStar_List.partition (fun _90_22 -> (match (_90_22) with
| FStar_SMTEncoding_Term.DeclFun (_90_2833) -> begin
true
end
| _90_2836 -> begin
false
end))))
in (match (_90_2839) with
| (decls, rest) -> begin
(((FStar_List.append decls (FStar_List.append rest inversions))), (env))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, _90_2842, tps, k, _90_2846, datas, quals, _90_2850) -> begin
(

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _90_23 -> (match (_90_23) with
| (FStar_Syntax_Syntax.Logic) | (FStar_Syntax_Syntax.Assumption) -> begin
true
end
| _90_2857 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(

let _90_2869 = c
in (match (_90_2869) with
| (name, args, _90_2864, _90_2866, _90_2868) -> begin
(let _187_2222 = (let _187_2221 = (let _187_2220 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in ((name), (_187_2220), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (_187_2221))
in (_187_2222)::[])
end))
end else begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end)
in (

let inversion_axioms = (fun tapp vars -> if (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _187_2228 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right _187_2228 FStar_Option.isNone))))) then begin
[]
end else begin
(

let _90_2876 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_90_2876) with
| (xxsym, xx) -> begin
(

let _90_2912 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _90_2879 l -> (match (_90_2879) with
| (out, decls) -> begin
(

let _90_2884 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (_90_2884) with
| (_90_2882, data_t) -> begin
(

let _90_2887 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (_90_2887) with
| (args, res) -> begin
(

let indices = (match ((let _187_2231 = (FStar_Syntax_Subst.compress res)
in _187_2231.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_90_2889, indices) -> begin
indices
end
| _90_2894 -> begin
[]
end)
in (

let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env _90_2900 -> (match (_90_2900) with
| (x, _90_2899) -> begin
(let _187_2236 = (let _187_2235 = (let _187_2234 = (mk_term_projector_name l x)
in ((_187_2234), ((xx)::[])))
in (FStar_SMTEncoding_Term.mkApp _187_2235))
in (push_term_var env x _187_2236))
end)) env))
in (

let _90_2904 = (encode_args indices env)
in (match (_90_2904) with
| (indices, decls') -> begin
(

let _90_2905 = if ((FStar_List.length indices) <> (FStar_List.length vars)) then begin
(FStar_All.failwith "Impossible")
end else begin
()
end
in (

let eqs = (let _187_2241 = (FStar_List.map2 (fun v a -> (let _187_2240 = (let _187_2239 = (FStar_SMTEncoding_Term.mkFreeV v)
in ((_187_2239), (a)))
in (FStar_SMTEncoding_Term.mkEq _187_2240))) vars indices)
in (FStar_All.pipe_right _187_2241 FStar_SMTEncoding_Term.mk_and_l))
in (let _187_2246 = (let _187_2245 = (let _187_2244 = (let _187_2243 = (let _187_2242 = (mk_data_tester env l xx)
in ((_187_2242), (eqs)))
in (FStar_SMTEncoding_Term.mkAnd _187_2243))
in ((out), (_187_2244)))
in (FStar_SMTEncoding_Term.mkOr _187_2245))
in ((_187_2246), ((FStar_List.append decls decls'))))))
end))))
end))
end))
end)) ((FStar_SMTEncoding_Term.mkFalse), ([]))))
in (match (_90_2912) with
| (data_ax, decls) -> begin
(

let _90_2915 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_90_2915) with
| (ffsym, ff) -> begin
(

let fuel_guarded_inversion = (

let xx_has_type_sfuel = if ((FStar_List.length datas) > (Prims.parse_int "1")) then begin
(let _187_2247 = (FStar_SMTEncoding_Term.mkApp (("SFuel"), ((ff)::[])))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel _187_2247 xx tapp))
end else begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end
in (let _187_2254 = (let _187_2253 = (let _187_2250 = (let _187_2249 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (let _187_2248 = (FStar_SMTEncoding_Term.mkImp ((xx_has_type_sfuel), (data_ax)))
in ((((xx_has_type_sfuel)::[])::[]), (_187_2249), (_187_2248))))
in (FStar_SMTEncoding_Term.mkForall _187_2250))
in (let _187_2252 = (let _187_2251 = (varops.mk_unique (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str))
in Some (_187_2251))
in ((_187_2253), (Some ("inversion axiom")), (_187_2252))))
in FStar_SMTEncoding_Term.Assume (_187_2254)))
in (

let pattern_guarded_inversion = if ((contains_name env "Prims.inversion") && ((FStar_List.length datas) > (Prims.parse_int "1"))) then begin
(

let xx_has_type_fuel = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let pattern_guard = (FStar_SMTEncoding_Term.mkApp (("Prims.inversion"), ((tapp)::[])))
in (let _187_2262 = (let _187_2261 = (let _187_2260 = (let _187_2257 = (let _187_2256 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (let _187_2255 = (FStar_SMTEncoding_Term.mkImp ((xx_has_type_fuel), (data_ax)))
in ((((xx_has_type_fuel)::(pattern_guard)::[])::[]), (_187_2256), (_187_2255))))
in (FStar_SMTEncoding_Term.mkForall _187_2257))
in (let _187_2259 = (let _187_2258 = (varops.mk_unique (Prims.strcat "pattern_guarded_inversion_" t.FStar_Ident.str))
in Some (_187_2258))
in ((_187_2260), (Some ("inversion axiom")), (_187_2259))))
in FStar_SMTEncoding_Term.Assume (_187_2261))
in (_187_2262)::[])))
end else begin
[]
end
in (FStar_List.append decls (FStar_List.append ((fuel_guarded_inversion)::[]) pattern_guarded_inversion))))
end))
end))
end))
end)
in (

let _90_2929 = (match ((let _187_2263 = (FStar_Syntax_Subst.compress k)
in _187_2263.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
(((FStar_List.append tps formals)), ((FStar_Syntax_Util.comp_result kres)))
end
| _90_2926 -> begin
((tps), (k))
end)
in (match (_90_2929) with
| (formals, res) -> begin
(

let _90_2932 = (FStar_Syntax_Subst.open_term formals res)
in (match (_90_2932) with
| (formals, res) -> begin
(

let _90_2939 = (encode_binders None formals env)
in (match (_90_2939) with
| (vars, guards, env', binder_decls, _90_2938) -> begin
(

let _90_2943 = (new_term_constant_and_tok_from_lid env t)
in (match (_90_2943) with
| (tname, ttok, env) -> begin
(

let ttok_tm = (FStar_SMTEncoding_Term.mkApp ((ttok), ([])))
in (

let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (

let tapp = (let _187_2265 = (let _187_2264 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in ((tname), (_187_2264)))
in (FStar_SMTEncoding_Term.mkApp _187_2265))
in (

let _90_2964 = (

let tname_decl = (let _187_2269 = (let _187_2268 = (FStar_All.pipe_right vars (FStar_List.map (fun _90_2949 -> (match (_90_2949) with
| (n, s) -> begin
(((Prims.strcat tname n)), (s))
end))))
in (let _187_2267 = (varops.next_id ())
in ((tname), (_187_2268), (FStar_SMTEncoding_Term.Term_sort), (_187_2267), (false))))
in (constructor_or_logic_type_decl _187_2269))
in (

let _90_2961 = (match (vars) with
| [] -> begin
(let _187_2273 = (let _187_2272 = (let _187_2271 = (FStar_SMTEncoding_Term.mkApp ((tname), ([])))
in (FStar_All.pipe_left (fun _187_2270 -> Some (_187_2270)) _187_2271))
in (push_free_var env t tname _187_2272))
in (([]), (_187_2273)))
end
| _90_2953 -> begin
(

let ttok_decl = FStar_SMTEncoding_Term.DeclFun (((ttok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("token"))))
in (

let ttok_fresh = (let _187_2274 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ttok), (FStar_SMTEncoding_Term.Term_sort)) _187_2274))
in (

let ttok_app = (mk_Apply ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (let _187_2278 = (let _187_2277 = (let _187_2276 = (let _187_2275 = (FStar_SMTEncoding_Term.mkEq ((ttok_app), (tapp)))
in ((pats), (None), (vars), (_187_2275)))
in (FStar_SMTEncoding_Term.mkForall' _187_2276))
in ((_187_2277), (Some ("name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" ttok)))))
in FStar_SMTEncoding_Term.Assume (_187_2278))
in (((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[]), (env)))))))
end)
in (match (_90_2961) with
| (tok_decls, env) -> begin
(((FStar_List.append tname_decl tok_decls)), (env))
end)))
in (match (_90_2964) with
| (decls, env) -> begin
(

let kindingAx = (

let _90_2967 = (encode_term_pred None res env' tapp)
in (match (_90_2967) with
| (k, decls) -> begin
(

let karr = if ((FStar_List.length formals) > (Prims.parse_int "0")) then begin
(let _187_2282 = (let _187_2281 = (let _187_2280 = (let _187_2279 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _187_2279))
in ((_187_2280), (Some ("kinding")), (Some ((Prims.strcat "pre_kinding_" ttok)))))
in FStar_SMTEncoding_Term.Assume (_187_2281))
in (_187_2282)::[])
end else begin
[]
end
in (let _187_2289 = (let _187_2288 = (let _187_2287 = (let _187_2286 = (let _187_2285 = (let _187_2284 = (let _187_2283 = (FStar_SMTEncoding_Term.mkImp ((guard), (k)))
in ((((tapp)::[])::[]), (vars), (_187_2283)))
in (FStar_SMTEncoding_Term.mkForall _187_2284))
in ((_187_2285), (None), (Some ((Prims.strcat "kinding_" ttok)))))
in FStar_SMTEncoding_Term.Assume (_187_2286))
in (_187_2287)::[])
in (FStar_List.append karr _187_2288))
in (FStar_List.append decls _187_2289)))
end))
in (

let aux = (let _187_2293 = (let _187_2292 = (inversion_axioms tapp vars)
in (let _187_2291 = (let _187_2290 = (pretype_axiom tapp vars)
in (_187_2290)::[])
in (FStar_List.append _187_2292 _187_2291)))
in (FStar_List.append kindingAx _187_2293))
in (

let g = (FStar_List.append decls (FStar_List.append binder_decls aux))
in ((g), (env)))))
end)))))
end))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, _90_2974, _90_2976, _90_2978, _90_2980, _90_2982, _90_2984, _90_2986) when (FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_datacon (d, _90_2991, t, _90_2994, n_tps, quals, _90_2998, drange) -> begin
(

let _90_3005 = (new_term_constant_and_tok_from_lid env d)
in (match (_90_3005) with
| (ddconstrsym, ddtok, env) -> begin
(

let ddtok_tm = (FStar_SMTEncoding_Term.mkApp ((ddtok), ([])))
in (

let _90_3009 = (FStar_Syntax_Util.arrow_formals t)
in (match (_90_3009) with
| (formals, t_res) -> begin
(

let _90_3012 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_90_3012) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_SMTEncoding_Term.mkApp (("SFuel"), ((fuel_tm)::[])))
in (

let _90_3019 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_90_3019) with
| (vars, guards, env', binder_decls, names) -> begin
(

let projectors = (FStar_All.pipe_right names (FStar_List.map (fun x -> (let _187_2295 = (mk_term_projector_name d x)
in ((_187_2295), (FStar_SMTEncoding_Term.Term_sort))))))
in (

let datacons = (let _187_2297 = (let _187_2296 = (varops.next_id ())
in ((ddconstrsym), (projectors), (FStar_SMTEncoding_Term.Term_sort), (_187_2296), (true)))
in (FStar_All.pipe_right _187_2297 FStar_SMTEncoding_Term.constructor_to_decl))
in (

let app = (mk_Apply ddtok_tm vars)
in (

let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Term.mkApp ((ddconstrsym), (xvars)))
in (

let _90_3029 = (encode_term_pred None t env ddtok_tm)
in (match (_90_3029) with
| (tok_typing, decls3) -> begin
(

let _90_3036 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_90_3036) with
| (vars', guards', env'', decls_formals, _90_3035) -> begin
(

let _90_3041 = (

let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars')
in (

let dapp = (FStar_SMTEncoding_Term.mkApp ((ddconstrsym), (xvars)))
in (encode_term_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_90_3041) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_SMTEncoding_Term.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _90_3045 -> begin
(let _187_2299 = (let _187_2298 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ddtok), (FStar_SMTEncoding_Term.Term_sort)) _187_2298))
in (_187_2299)::[])
end)
in (

let encode_elim = (fun _90_3048 -> (match (()) with
| () -> begin
(

let _90_3051 = (FStar_Syntax_Util.head_and_args t_res)
in (match (_90_3051) with
| (head, args) -> begin
(match ((let _187_2302 = (FStar_Syntax_Subst.compress head)
in _187_2302.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let _90_3069 = (encode_args args env')
in (match (_90_3069) with
| (encoded_args, arg_decls) -> begin
(

let _90_3084 = (FStar_List.fold_left (fun _90_3073 arg -> (match (_90_3073) with
| (env, arg_vars, eqns) -> begin
(

let _90_3079 = (let _187_2305 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in (gen_term_var env _187_2305))
in (match (_90_3079) with
| (_90_3076, xv, env) -> begin
(let _187_2307 = (let _187_2306 = (FStar_SMTEncoding_Term.mkEq ((arg), (xv)))
in (_187_2306)::eqns)
in ((env), ((xv)::arg_vars), (_187_2307)))
end))
end)) ((env'), ([]), ([])) encoded_args)
in (match (_90_3084) with
| (_90_3081, arg_vars, eqns) -> begin
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

let typing_inversion = (let _187_2314 = (let _187_2313 = (let _187_2312 = (let _187_2311 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (let _187_2310 = (let _187_2309 = (let _187_2308 = (FStar_SMTEncoding_Term.mk_and_l (FStar_List.append eqns guards))
in ((ty_pred), (_187_2308)))
in (FStar_SMTEncoding_Term.mkImp _187_2309))
in ((((ty_pred)::[])::[]), (_187_2311), (_187_2310))))
in (FStar_SMTEncoding_Term.mkForall _187_2312))
in ((_187_2313), (Some ("data constructor typing elim")), (Some ((Prims.strcat "data_elim_" ddconstrsym)))))
in FStar_SMTEncoding_Term.Assume (_187_2314))
in (

let subterm_ordering = if (FStar_Ident.lid_equals d FStar_Syntax_Const.lextop_lid) then begin
(

let x = (let _187_2315 = (varops.fresh "x")
in ((_187_2315), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Term.mkFreeV x)
in (let _187_2327 = (let _187_2326 = (let _187_2323 = (let _187_2322 = (let _187_2317 = (let _187_2316 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in (_187_2316)::[])
in (_187_2317)::[])
in (let _187_2321 = (let _187_2320 = (let _187_2319 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (let _187_2318 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in ((_187_2319), (_187_2318))))
in (FStar_SMTEncoding_Term.mkImp _187_2320))
in ((_187_2322), ((x)::[]), (_187_2321))))
in (FStar_SMTEncoding_Term.mkForall _187_2323))
in (let _187_2325 = (let _187_2324 = (varops.mk_unique "lextop")
in Some (_187_2324))
in ((_187_2326), (Some ("lextop is top")), (_187_2325))))
in FStar_SMTEncoding_Term.Assume (_187_2327))))
end else begin
(

let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
[]
end
| FStar_SMTEncoding_Term.Term_sort -> begin
(let _187_2330 = (let _187_2329 = (FStar_SMTEncoding_Term.mkFreeV v)
in (FStar_SMTEncoding_Term.mk_Precedes _187_2329 dapp))
in (_187_2330)::[])
end
| _90_3098 -> begin
(FStar_All.failwith "unexpected sort")
end))))
in (let _187_2337 = (let _187_2336 = (let _187_2335 = (let _187_2334 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (let _187_2333 = (let _187_2332 = (let _187_2331 = (FStar_SMTEncoding_Term.mk_and_l prec)
in ((ty_pred), (_187_2331)))
in (FStar_SMTEncoding_Term.mkImp _187_2332))
in ((((ty_pred)::[])::[]), (_187_2334), (_187_2333))))
in (FStar_SMTEncoding_Term.mkForall _187_2335))
in ((_187_2336), (Some ("subterm ordering")), (Some ((Prims.strcat "subterm_ordering_" ddconstrsym)))))
in FStar_SMTEncoding_Term.Assume (_187_2337)))
end
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end))
end)))
end
| _90_3102 -> begin
(

let _90_3103 = (let _187_2340 = (let _187_2339 = (FStar_Syntax_Print.lid_to_string d)
in (let _187_2338 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _187_2339 _187_2338)))
in (FStar_TypeChecker_Errors.warn drange _187_2340))
in (([]), ([])))
end)
end))
end))
in (

let _90_3107 = (encode_elim ())
in (match (_90_3107) with
| (decls2, elim) -> begin
(

let g = (let _187_2367 = (let _187_2366 = (let _187_2365 = (let _187_2364 = (let _187_2345 = (let _187_2344 = (let _187_2343 = (let _187_2342 = (let _187_2341 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" _187_2341))
in Some (_187_2342))
in ((ddtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (_187_2343)))
in FStar_SMTEncoding_Term.DeclFun (_187_2344))
in (_187_2345)::[])
in (let _187_2363 = (let _187_2362 = (let _187_2361 = (let _187_2360 = (let _187_2359 = (let _187_2358 = (let _187_2357 = (let _187_2349 = (let _187_2348 = (let _187_2347 = (let _187_2346 = (FStar_SMTEncoding_Term.mkEq ((app), (dapp)))
in ((((app)::[])::[]), (vars), (_187_2346)))
in (FStar_SMTEncoding_Term.mkForall _187_2347))
in ((_187_2348), (Some ("equality for proxy")), (Some ((Prims.strcat "equality_tok_" ddtok)))))
in FStar_SMTEncoding_Term.Assume (_187_2349))
in (let _187_2356 = (let _187_2355 = (let _187_2354 = (let _187_2353 = (let _187_2352 = (let _187_2351 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) vars')
in (let _187_2350 = (FStar_SMTEncoding_Term.mkImp ((guard'), (ty_pred')))
in ((((ty_pred')::[])::[]), (_187_2351), (_187_2350))))
in (FStar_SMTEncoding_Term.mkForall _187_2352))
in ((_187_2353), (Some ("data constructor typing intro")), (Some ((Prims.strcat "data_typing_intro_" ddtok)))))
in FStar_SMTEncoding_Term.Assume (_187_2354))
in (_187_2355)::[])
in (_187_2357)::_187_2356))
in (FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("typing for data constructor proxy")), (Some ((Prims.strcat "typing_tok_" ddtok))))))::_187_2358)
in (FStar_List.append _187_2359 elim))
in (FStar_List.append decls_pred _187_2360))
in (FStar_List.append decls_formals _187_2361))
in (FStar_List.append proxy_fresh _187_2362))
in (FStar_List.append _187_2364 _187_2363)))
in (FStar_List.append decls3 _187_2365))
in (FStar_List.append decls2 _187_2366))
in (FStar_List.append binder_decls _187_2367))
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
and encode_signature : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _90_3113 se -> (match (_90_3113) with
| (g, env) -> begin
(

let _90_3117 = (encode_sigelt env se)
in (match (_90_3117) with
| (g', env) -> begin
(((FStar_List.append g g')), (env))
end))
end)) (([]), (env)))))


let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env bindings -> (

let encode_binding = (fun b _90_3125 -> (match (_90_3125) with
| (i, decls, env) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (_90_3127) -> begin
(((i + (Prims.parse_int "1"))), ([]), (env))
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (

let _90_3132 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _187_2382 = (FStar_Syntax_Print.bv_to_string x)
in (let _187_2381 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _187_2380 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" _187_2382 _187_2381 _187_2380))))
end else begin
()
end
in (

let _90_3136 = (encode_term t1 env)
in (match (_90_3136) with
| (t, decls') -> begin
(

let _90_3140 = (let _187_2387 = (let _187_2386 = (let _187_2385 = (FStar_Util.digest_of_string t.FStar_SMTEncoding_Term.hash)
in (let _187_2384 = (let _187_2383 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _187_2383))
in (Prims.strcat _187_2385 _187_2384)))
in (Prims.strcat "x_" _187_2386))
in (new_term_constant_from_string env x _187_2387))
in (match (_90_3140) with
| (xxsym, xx, env') -> begin
(

let t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel None xx t)
in (

let caption = if (FStar_Options.log_queries ()) then begin
(let _187_2391 = (let _187_2390 = (FStar_Syntax_Print.bv_to_string x)
in (let _187_2389 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _187_2388 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _187_2390 _187_2389 _187_2388))))
in Some (_187_2391))
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
| FStar_TypeChecker_Env.Binding_lid (x, (_90_3148, t)) -> begin
(

let t_norm = (whnf env t)
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant None)
in (

let _90_3157 = (encode_free_var env fv t t_norm [])
in (match (_90_3157) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))))
end
| (FStar_TypeChecker_Env.Binding_sig_inst (_, se, _)) | (FStar_TypeChecker_Env.Binding_sig (_, se)) -> begin
(

let _90_3171 = (encode_sigelt env se)
in (match (_90_3171) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))
end)
end))
in (

let _90_3176 = (FStar_List.fold_right encode_binding bindings (((Prims.parse_int "0")), ([]), (env)))
in (match (_90_3176) with
| (_90_3173, decls, env) -> begin
((decls), (env))
end))))


let encode_labels = (fun labs -> (

let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _90_3183 -> (match (_90_3183) with
| (l, _90_3180, _90_3182) -> begin
FStar_SMTEncoding_Term.DeclFun ((((Prims.fst l)), ([]), (FStar_SMTEncoding_Term.Bool_sort), (None)))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _90_3190 -> (match (_90_3190) with
| (l, _90_3187, _90_3189) -> begin
(let _187_2399 = (FStar_All.pipe_left (fun _187_2395 -> FStar_SMTEncoding_Term.Echo (_187_2395)) (Prims.fst l))
in (let _187_2398 = (let _187_2397 = (let _187_2396 = (FStar_SMTEncoding_Term.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (_187_2396))
in (_187_2397)::[])
in (_187_2399)::_187_2398))
end))))
in ((prefix), (suffix)))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (let _187_2404 = (let _187_2403 = (let _187_2402 = (FStar_Util.smap_create (Prims.parse_int "100"))
in {bindings = []; depth = (Prims.parse_int "0"); tcenv = tcenv; warn = true; cache = _187_2402; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_187_2403)::[])
in (FStar_ST.op_Colon_Equals last_env _187_2404)))


let get_env : FStar_TypeChecker_Env.env  ->  env_t = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "No env; call init first!")
end
| (e)::_90_3196 -> begin
(

let _90_3199 = e
in {bindings = _90_3199.bindings; depth = _90_3199.depth; tcenv = tcenv; warn = _90_3199.warn; cache = _90_3199.cache; nolabels = _90_3199.nolabels; use_zfuel_name = _90_3199.use_zfuel_name; encode_non_total_function_typ = _90_3199.encode_non_total_function_typ})
end))


let set_env : env_t  ->  Prims.unit = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| (_90_3205)::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))


let push_env : Prims.unit  ->  Prims.unit = (fun _90_3207 -> (match (()) with
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

let _90_3213 = hd
in {bindings = _90_3213.bindings; depth = _90_3213.depth; tcenv = _90_3213.tcenv; warn = _90_3213.warn; cache = refs; nolabels = _90_3213.nolabels; use_zfuel_name = _90_3213.use_zfuel_name; encode_non_total_function_typ = _90_3213.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))


let pop_env : Prims.unit  ->  Prims.unit = (fun _90_3216 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Popping an empty stack")
end
| (_90_3220)::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))


let mark_env : Prims.unit  ->  Prims.unit = (fun _90_3222 -> (match (()) with
| () -> begin
(push_env ())
end))


let reset_mark_env : Prims.unit  ->  Prims.unit = (fun _90_3223 -> (match (()) with
| () -> begin
(pop_env ())
end))


let commit_mark_env : Prims.unit  ->  Prims.unit = (fun _90_3224 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| (hd)::(_90_3227)::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _90_3232 -> begin
(FStar_All.failwith "Impossible")
end)
end))


let init : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (

let _90_3234 = (init_env tcenv)
in (

let _90_3236 = (FStar_SMTEncoding_Z3.init ())
in (FStar_SMTEncoding_Z3.giveZ3 ((FStar_SMTEncoding_Term.DefPrelude)::[])))))


let push : Prims.string  ->  Prims.unit = (fun msg -> (

let _90_3239 = (push_env ())
in (

let _90_3241 = (varops.push ())
in (FStar_SMTEncoding_Z3.push msg))))


let pop : Prims.string  ->  Prims.unit = (fun msg -> (

let _90_3244 = (let _187_2425 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _187_2425))
in (

let _90_3246 = (varops.pop ())
in (FStar_SMTEncoding_Z3.pop msg))))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _90_3249 = (mark_env ())
in (

let _90_3251 = (varops.mark ())
in (FStar_SMTEncoding_Z3.mark msg))))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _90_3254 = (reset_mark_env ())
in (

let _90_3256 = (varops.reset_mark ())
in (FStar_SMTEncoding_Z3.reset_mark msg))))


let commit_mark = (fun msg -> (

let _90_3259 = (commit_mark_env ())
in (

let _90_3261 = (varops.commit_mark ())
in (FStar_SMTEncoding_Z3.commit_mark msg))))


let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (

let caption = (fun decls -> if (FStar_Options.log_queries ()) then begin
(let _187_2441 = (let _187_2440 = (let _187_2439 = (let _187_2438 = (let _187_2437 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _187_2437 (FStar_List.map FStar_Syntax_Print.lid_to_string)))
in (FStar_All.pipe_right _187_2438 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " _187_2439))
in FStar_SMTEncoding_Term.Caption (_187_2440))
in (_187_2441)::decls)
end else begin
decls
end)
in (

let env = (get_env tcenv)
in (

let _90_3270 = (encode_sigelt env se)
in (match (_90_3270) with
| (decls, env) -> begin
(

let _90_3271 = (set_env env)
in (let _187_2442 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 _187_2442)))
end)))))


let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let _90_3276 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(let _187_2447 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name _187_2447))
end else begin
()
end
in (

let env = (get_env tcenv)
in (

let _90_3283 = (encode_signature (

let _90_3279 = env
in {bindings = _90_3279.bindings; depth = _90_3279.depth; tcenv = _90_3279.tcenv; warn = false; cache = _90_3279.cache; nolabels = _90_3279.nolabels; use_zfuel_name = _90_3279.use_zfuel_name; encode_non_total_function_typ = _90_3279.encode_non_total_function_typ}) modul.FStar_Syntax_Syntax.exports)
in (match (_90_3283) with
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

let _90_3289 = (set_env (

let _90_3287 = env
in {bindings = _90_3287.bindings; depth = _90_3287.depth; tcenv = _90_3287.tcenv; warn = true; cache = _90_3287.cache; nolabels = _90_3287.nolabels; use_zfuel_name = _90_3287.use_zfuel_name; encode_non_total_function_typ = _90_3287.encode_non_total_function_typ}))
in (

let _90_3291 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end else begin
()
end
in (

let decls = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls)))))
end))))))


let encode_query : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_ErrorReporting.label Prims.list * FStar_SMTEncoding_Term.decl * FStar_SMTEncoding_Term.decl Prims.list) = (fun use_env_msg tcenv q -> (

let _90_3297 = (let _187_2465 = (let _187_2464 = (FStar_TypeChecker_Env.current_module tcenv)
in _187_2464.FStar_Ident.str)
in (FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name _187_2465))
in (

let env = (get_env tcenv)
in (

let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (

let _90_3322 = (

let rec aux = (fun bindings -> (match (bindings) with
| (FStar_TypeChecker_Env.Binding_var (x))::rest -> begin
(

let _90_3311 = (aux rest)
in (match (_90_3311) with
| (out, rest) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (let _187_2471 = (let _187_2470 = (FStar_Syntax_Syntax.mk_binder (

let _90_3313 = x
in {FStar_Syntax_Syntax.ppname = _90_3313.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _90_3313.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_187_2470)::out)
in ((_187_2471), (rest))))
end))
end
| _90_3316 -> begin
(([]), (bindings))
end))
in (

let _90_3319 = (aux bindings)
in (match (_90_3319) with
| (closing, bindings) -> begin
(let _187_2472 = (FStar_Syntax_Util.close_forall (FStar_List.rev closing) q)
in ((_187_2472), (bindings)))
end)))
in (match (_90_3322) with
| (q, bindings) -> begin
(

let _90_3331 = (let _187_2474 = (FStar_List.filter (fun _90_24 -> (match (_90_24) with
| FStar_TypeChecker_Env.Binding_sig (_90_3325) -> begin
false
end
| _90_3328 -> begin
true
end)) bindings)
in (encode_env_bindings env _187_2474))
in (match (_90_3331) with
| (env_decls, env) -> begin
(

let _90_3332 = if (((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTQuery")))) then begin
(let _187_2475 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" _187_2475))
end else begin
()
end
in (

let _90_3336 = (encode_formula q env)
in (match (_90_3336) with
| (phi, qdecls) -> begin
(

let _90_3341 = (let _187_2476 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg _187_2476 phi))
in (match (_90_3341) with
| (phi, labels, _90_3340) -> begin
(

let _90_3344 = (encode_labels labels)
in (match (_90_3344) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append env_decls (FStar_List.append label_prefix qdecls))
in (

let qry = (let _187_2480 = (let _187_2479 = (FStar_SMTEncoding_Term.mkNot phi)
in (let _187_2478 = (let _187_2477 = (varops.mk_unique "@query")
in Some (_187_2477))
in ((_187_2479), (Some ("query")), (_187_2478))))
in FStar_SMTEncoding_Term.Assume (_187_2480))
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

let _90_3351 = (push "query")
in (

let _90_3356 = (encode_formula q env)
in (match (_90_3356) with
| (f, _90_3355) -> begin
(

let _90_3357 = (pop "query")
in (match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _90_3361) -> begin
true
end
| _90_3365 -> begin
false
end))
end)))))




