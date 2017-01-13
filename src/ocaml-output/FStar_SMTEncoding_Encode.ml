
open Prims

let add_fuel = (fun x tl -> if (FStar_Options.unthrottle_inductives ()) then begin
tl
end else begin
(x)::tl
end)


let withenv = (fun c _93_31 -> (match (_93_31) with
| (a, b) -> begin
((a), (b), (c))
end))


let vargs = (fun args -> (FStar_List.filter (fun _93_1 -> (match (_93_1) with
| (FStar_Util.Inl (_93_35), _93_38) -> begin
false
end
| _93_41 -> begin
true
end)) args))


let subst_lcomp_opt = (fun s l -> (match (l) with
| Some (FStar_Util.Inl (l)) -> begin
(let _194_12 = (let _194_11 = (let _194_10 = (let _194_9 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp s _194_9))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _194_10))
in FStar_Util.Inl (_194_11))
in Some (_194_12))
end
| _93_48 -> begin
l
end))


let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s '\'' '_'))


let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun lid a -> (

let a = (

let _93_52 = a
in (let _194_19 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _194_19; FStar_Syntax_Syntax.index = _93_52.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _93_52.FStar_Syntax_Syntax.sort}))
in (let _194_20 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str a.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (FStar_All.pipe_left escape _194_20))))


let primitive_projector_by_pos : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (

let fail = (fun _93_59 -> (match (()) with
| () -> begin
(let _194_30 = (let _194_29 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" _194_29 lid.FStar_Ident.str))
in (failwith _194_30))
end))
in (

let _93_63 = (FStar_TypeChecker_Env.lookup_datacon env lid)
in (match (_93_63) with
| (_93_61, t) -> begin
(match ((let _194_31 = (FStar_Syntax_Subst.compress t)
in _194_31.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _93_71 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_93_71) with
| (binders, _93_70) -> begin
if ((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(

let b = (FStar_List.nth binders i)
in (mk_term_projector_name lid (Prims.fst b)))
end
end))
end
| _93_74 -> begin
(fail ())
end)
end))))


let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (let _194_37 = (let _194_36 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str _194_36))
in (FStar_All.pipe_left escape _194_37)))


let mk_term_projector : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun lid a -> (let _194_43 = (let _194_42 = (mk_term_projector_name lid a)
in ((_194_42), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Util.mkFreeV _194_43)))


let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_SMTEncoding_Term.term = (fun lid i -> (let _194_49 = (let _194_48 = (mk_term_projector_name_by_pos lid i)
in ((_194_48), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Util.mkFreeV _194_49)))


let mk_data_tester = (fun env l x -> (FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x))


type varops_t =
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; mark : Prims.unit  ->  Prims.unit; reset_mark : Prims.unit  ->  Prims.unit; commit_mark : Prims.unit  ->  Prims.unit; new_var : FStar_Ident.ident  ->  Prims.int  ->  Prims.string; new_fvar : FStar_Ident.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_SMTEncoding_Term.term; next_id : Prims.unit  ->  Prims.int; mk_unique : Prims.string  ->  Prims.string}


let is_Mkvarops_t : varops_t  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkvarops_t"))))


let varops : varops_t = (

let initial_ctr = (Prims.parse_int "100")
in (

let ctr = (FStar_Util.mk_ref initial_ctr)
in (

let new_scope = (fun _93_99 -> (match (()) with
| () -> begin
(let _194_162 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (let _194_161 = (FStar_Util.smap_create (Prims.parse_int "100"))
in ((_194_162), (_194_161))))
end))
in (

let scopes = (let _194_164 = (let _194_163 = (new_scope ())
in (_194_163)::[])
in (FStar_Util.mk_ref _194_164))
in (

let mk_unique = (fun y -> (

let y = (escape y)
in (

let y = (match ((let _194_168 = (FStar_ST.read scopes)
in (FStar_Util.find_map _194_168 (fun _93_107 -> (match (_93_107) with
| (names, _93_106) -> begin
(FStar_Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_93_110) -> begin
(

let _93_112 = (FStar_Util.incr ctr)
in (let _194_171 = (let _194_170 = (let _194_169 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _194_169))
in (Prims.strcat "__" _194_170))
in (Prims.strcat y _194_171)))
end)
in (

let top_scope = (let _194_173 = (let _194_172 = (FStar_ST.read scopes)
in (FStar_List.hd _194_172))
in (FStar_All.pipe_left Prims.fst _194_173))
in (

let _93_116 = (FStar_Util.smap_add top_scope y true)
in y)))))
in (

let new_var = (fun pp rn -> (let _194_180 = (let _194_179 = (let _194_178 = (FStar_Util.string_of_int rn)
in (Prims.strcat "__" _194_178))
in (Prims.strcat pp.FStar_Ident.idText _194_179))
in (FStar_All.pipe_left mk_unique _194_180)))
in (

let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (

let next_id = (fun _93_124 -> (match (()) with
| () -> begin
(

let _93_125 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end))
in (

let fresh = (fun pfx -> (let _194_188 = (let _194_187 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _194_187))
in (FStar_Util.format2 "%s_%s" pfx _194_188)))
in (

let string_const = (fun s -> (match ((let _194_192 = (FStar_ST.read scopes)
in (FStar_Util.find_map _194_192 (fun _93_134 -> (match (_93_134) with
| (_93_132, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))) with
| Some (f) -> begin
f
end
| None -> begin
(

let id = (next_id ())
in (

let f = (let _194_193 = (FStar_SMTEncoding_Util.mk_String_const id)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString _194_193))
in (

let top_scope = (let _194_195 = (let _194_194 = (FStar_ST.read scopes)
in (FStar_List.hd _194_194))
in (FStar_All.pipe_left Prims.snd _194_195))
in (

let _93_141 = (FStar_Util.smap_add top_scope s f)
in f))))
end))
in (

let push = (fun _93_144 -> (match (()) with
| () -> begin
(let _194_200 = (let _194_199 = (new_scope ())
in (let _194_198 = (FStar_ST.read scopes)
in (_194_199)::_194_198))
in (FStar_ST.op_Colon_Equals scopes _194_200))
end))
in (

let pop = (fun _93_146 -> (match (()) with
| () -> begin
(let _194_204 = (let _194_203 = (FStar_ST.read scopes)
in (FStar_List.tl _194_203))
in (FStar_ST.op_Colon_Equals scopes _194_204))
end))
in (

let mark = (fun _93_148 -> (match (()) with
| () -> begin
(push ())
end))
in (

let reset_mark = (fun _93_150 -> (match (()) with
| () -> begin
(pop ())
end))
in (

let commit_mark = (fun _93_152 -> (match (()) with
| () -> begin
(match ((FStar_ST.read scopes)) with
| ((hd1, hd2))::((next1, next2))::tl -> begin
(

let _93_165 = (FStar_Util.smap_fold hd1 (fun key value v -> (FStar_Util.smap_add next1 key value)) ())
in (

let _93_170 = (FStar_Util.smap_fold hd2 (fun key value v -> (FStar_Util.smap_add next2 key value)) ())
in (FStar_ST.op_Colon_Equals scopes ((((next1), (next2)))::tl))))
end
| _93_173 -> begin
(failwith "Impossible")
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id; mk_unique = mk_unique})))))))))))))))


let unmangle : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv = (fun x -> (

let _93_175 = x
in (let _194_219 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _194_219; FStar_Syntax_Syntax.index = _93_175.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _93_175.FStar_Syntax_Syntax.sort})))


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
| Binding_var (_93_179) -> begin
_93_179
end))


let ___Binding_fvar____0 = (fun projectee -> (match (projectee) with
| Binding_fvar (_93_182) -> begin
_93_182
end))


let binder_of_eithervar = (fun v -> ((v), (None)))


type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_TypeChecker_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_SMTEncoding_Term.sort Prims.list * FStar_SMTEncoding_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}


let is_Mkenv_t : env_t  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkenv_t"))))


let print_env : env_t  ->  Prims.string = (fun e -> (let _194_277 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun _93_2 -> (match (_93_2) with
| Binding_var (x, _93_197) -> begin
(FStar_Syntax_Print.bv_to_string x)
end
| Binding_fvar (l, _93_202, _93_204, _93_206) -> begin
(FStar_Syntax_Print.lid_to_string l)
end))))
in (FStar_All.pipe_right _194_277 (FStar_String.concat ", "))))


let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))


let caption_t : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.string Prims.option = (fun env t -> if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _194_287 = (FStar_Syntax_Print.term_to_string t)
in Some (_194_287))
end else begin
None
end)


let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (

let xsym = (varops.fresh x)
in (let _194_292 = (FStar_SMTEncoding_Util.mkFreeV ((xsym), (s)))
in ((xsym), (_194_292)))))


let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (let _194_297 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _194_297))
in (

let y = (FStar_SMTEncoding_Util.mkFreeV ((ysym), (FStar_SMTEncoding_Term.Term_sort)))
in ((ysym), (y), ((

let _93_220 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = (env.depth + (Prims.parse_int "1")); tcenv = _93_220.tcenv; warn = _93_220.warn; cache = _93_220.cache; nolabels = _93_220.nolabels; use_zfuel_name = _93_220.use_zfuel_name; encode_non_total_function_typ = _93_220.encode_non_total_function_typ}))))))


let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let _93_226 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = _93_226.depth; tcenv = _93_226.tcenv; warn = _93_226.warn; cache = _93_226.cache; nolabels = _93_226.nolabels; use_zfuel_name = _93_226.use_zfuel_name; encode_non_total_function_typ = _93_226.encode_non_total_function_typ}))))))


let new_term_constant_from_string : env_t  ->  FStar_Syntax_Syntax.bv  ->  Prims.string  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x str -> (

let ysym = (varops.mk_unique str)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let _93_233 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = _93_233.depth; tcenv = _93_233.tcenv; warn = _93_233.warn; cache = _93_233.cache; nolabels = _93_233.nolabels; use_zfuel_name = _93_233.use_zfuel_name; encode_non_total_function_typ = _93_233.encode_non_total_function_typ}))))))


let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (

let _93_238 = env
in {bindings = (Binding_var (((x), (t))))::env.bindings; depth = _93_238.depth; tcenv = _93_238.tcenv; warn = _93_238.warn; cache = _93_238.cache; nolabels = _93_238.nolabels; use_zfuel_name = _93_238.use_zfuel_name; encode_non_total_function_typ = _93_238.encode_non_total_function_typ}))


let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let aux = (fun a' -> (lookup_binding env (fun _93_3 -> (match (_93_3) with
| Binding_var (b, t) when (FStar_Syntax_Syntax.bv_eq b a') -> begin
Some (((b), (t)))
end
| _93_250 -> begin
None
end))))
in (match ((aux a)) with
| None -> begin
(

let a = (unmangle a)
in (match ((aux a)) with
| None -> begin
(let _194_322 = (let _194_321 = (FStar_Syntax_Print.bv_to_string a)
in (FStar_Util.format1 "Bound term variable not found (after unmangling): %s" _194_321))
in (failwith _194_322))
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
in (let _194_333 = (

let _93_266 = env
in (let _194_332 = (let _194_331 = (let _194_330 = (let _194_329 = (let _194_328 = (FStar_SMTEncoding_Util.mkApp ((ftok), ([])))
in (FStar_All.pipe_left (fun _194_327 -> Some (_194_327)) _194_328))
in ((x), (fname), (_194_329), (None)))
in Binding_fvar (_194_330))
in (_194_331)::env.bindings)
in {bindings = _194_332; depth = _93_266.depth; tcenv = _93_266.tcenv; warn = _93_266.warn; cache = _93_266.cache; nolabels = _93_266.nolabels; use_zfuel_name = _93_266.use_zfuel_name; encode_non_total_function_typ = _93_266.encode_non_total_function_typ}))
in ((fname), (ftok), (_194_333))))))


let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun _93_4 -> (match (_93_4) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some (((t1), (t2), (t3)))
end
| _93_278 -> begin
None
end))))


let contains_name : env_t  ->  Prims.string  ->  Prims.bool = (fun env s -> (let _194_344 = (lookup_binding env (fun _93_5 -> (match (_93_5) with
| Binding_fvar (b, t1, t2, t3) when (b.FStar_Ident.str = s) -> begin
Some (())
end
| _93_289 -> begin
None
end)))
in (FStar_All.pipe_right _194_344 FStar_Option.isSome)))


let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _194_350 = (let _194_349 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" _194_349))
in (failwith _194_350))
end
| Some (s) -> begin
s
end))


let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (

let _93_299 = env
in {bindings = (Binding_fvar (((x), (fname), (ftok), (None))))::env.bindings; depth = _93_299.depth; tcenv = _93_299.tcenv; warn = _93_299.warn; cache = _93_299.cache; nolabels = _93_299.nolabels; use_zfuel_name = _93_299.use_zfuel_name; encode_non_total_function_typ = _93_299.encode_non_total_function_typ}))


let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (

let _93_308 = (lookup_lid env x)
in (match (_93_308) with
| (t1, t2, _93_307) -> begin
(

let t3 = (let _194_367 = (let _194_366 = (let _194_365 = (FStar_SMTEncoding_Util.mkApp (("ZFuel"), ([])))
in (_194_365)::[])
in ((f), (_194_366)))
in (FStar_SMTEncoding_Util.mkApp _194_367))
in (

let _93_310 = env
in {bindings = (Binding_fvar (((x), (t1), (t2), (Some (t3)))))::env.bindings; depth = _93_310.depth; tcenv = _93_310.tcenv; warn = _93_310.warn; cache = _93_310.cache; nolabels = _93_310.nolabels; use_zfuel_name = _93_310.use_zfuel_name; encode_non_total_function_typ = _93_310.encode_non_total_function_typ}))
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
| _93_323 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (_93_327, (fuel)::[]) -> begin
if (let _194_373 = (let _194_372 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right _194_372 Prims.fst))
in (FStar_Util.starts_with _194_373 "fuel")) then begin
(let _194_376 = (let _194_375 = (FStar_SMTEncoding_Util.mkFreeV ((name), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_ApplyTF _194_375 fuel))
in (FStar_All.pipe_left (fun _194_374 -> Some (_194_374)) _194_376))
end else begin
Some (t)
end
end
| _93_333 -> begin
Some (t)
end)
end
| _93_335 -> begin
None
end)
end)
end))


let lookup_free_var = (fun env a -> (match ((try_lookup_free_var env a.FStar_Syntax_Syntax.v)) with
| Some (t) -> begin
t
end
| None -> begin
(let _194_380 = (let _194_379 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _194_379))
in (failwith _194_380))
end))


let lookup_free_var_name = (fun env a -> (

let _93_348 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_93_348) with
| (x, _93_345, _93_347) -> begin
x
end)))


let lookup_free_var_sym = (fun env a -> (

let _93_354 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_93_354) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.freevars = _93_358; FStar_SMTEncoding_Term.rng = _93_356}) when env.use_zfuel_name -> begin
((g), (zf))
end
| _93_366 -> begin
(match (sym) with
| None -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end
| Some (sym) -> begin
(match (sym.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, (fuel)::[]) -> begin
((g), ((fuel)::[]))
end
| _93_376 -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end)
end)
end)
end)))


let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun _93_6 -> (match (_93_6) with
| Binding_fvar (_93_381, nm', tok, _93_385) when (nm = nm') -> begin
tok
end
| _93_389 -> begin
None
end))))


let mkForall_fuel' = (fun n _93_394 -> (match (_93_394) with
| (pats, vars, body) -> begin
(

let fallback = (fun _93_396 -> (match (()) with
| () -> begin
(FStar_SMTEncoding_Util.mkForall ((pats), (vars), (body)))
end))
in if (FStar_Options.unthrottle_inductives ()) then begin
(fallback ())
end else begin
(

let _93_399 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_93_399) with
| (fsym, fterm) -> begin
(

let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Util.mkApp (("HasTypeFuel"), ((fterm)::args)))
end
| _93_409 -> begin
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
(let _194_397 = (add_fuel guards)
in (FStar_SMTEncoding_Util.mk_and_l _194_397))
end
| _93_422 -> begin
(let _194_398 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _194_398 FStar_List.hd))
end)
in (FStar_SMTEncoding_Util.mkImp ((guard), (body'))))
end
| _93_425 -> begin
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
(let _194_404 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _194_404 FStar_Option.isNone))
end
| _93_464 -> begin
false
end)))


let head_redex : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (match ((let _194_409 = (FStar_Syntax_Util.un_uinst t)
in _194_409.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_93_468, _93_470, Some (FStar_Util.Inr (l, flags))) -> begin
(((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid)) || (FStar_List.existsb (fun _93_7 -> (match (_93_7) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| _93_481 -> begin
false
end)) flags))
end
| FStar_Syntax_Syntax.Tm_abs (_93_483, _93_485, Some (FStar_Util.Inl (lc))) -> begin
(FStar_Syntax_Util.is_tot_or_gtot_lcomp lc)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(let _194_411 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _194_411 FStar_Option.isSome))
end
| _93_494 -> begin
false
end))


let whnf : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> if (head_normal env t) then begin
t
end else begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
end)


let norm : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t))


let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (let _194_424 = (let _194_422 = (FStar_Syntax_Syntax.null_binder t)
in (_194_422)::[])
in (let _194_423 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Util.abs _194_424 _194_423 None))))


let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(let _194_431 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out _194_431))
end
| s -> begin
(

let _93_506 = ()
in (let _194_432 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Util.mk_ApplyTT out _194_432)))
end)) e)))


let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)))


let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun _93_8 -> (match (_93_8) with
| (FStar_SMTEncoding_Term.Var ("ApplyTT")) | (FStar_SMTEncoding_Term.Var ("ApplyTF")) -> begin
true
end
| _93_516 -> begin
false
end))


let is_eta : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env vars t -> (

let rec aux = (fun t xs -> (match (((t.FStar_SMTEncoding_Term.tm), (xs))) with
| (FStar_SMTEncoding_Term.App (app, (f)::({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.freevars = _93_527; FStar_SMTEncoding_Term.rng = _93_525})::[]), (x)::xs) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), _93_545) -> begin
if (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v)
end
| _93_552 -> begin
false
end)) args vars)) then begin
(tok_of_name env f)
end else begin
None
end
end
| (_93_554, []) -> begin
(

let fvs = (FStar_SMTEncoding_Term.free_variables t)
in if (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (not ((FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)))))) then begin
Some (t)
end else begin
None
end)
end
| _93_560 -> begin
None
end))
in (aux t (FStar_List.rev vars))))


type label =
(FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range)


type labels =
label Prims.list


type pattern =
{pat_vars : (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.fv) Prims.list; pat_term : Prims.unit  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t); guard : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term; projections : FStar_SMTEncoding_Term.term  ->  (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) Prims.list}


let is_Mkpattern : pattern  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkpattern"))))


exception Let_rec_unencodeable


let is_Let_rec_unencodeable = (fun _discr_ -> (match (_discr_) with
| Let_rec_unencodeable (_) -> begin
true
end
| _ -> begin
false
end))


let encode_const : FStar_Const.sconst  ->  FStar_SMTEncoding_Term.term = (fun _93_9 -> (match (_93_9) with
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
(let _194_489 = (let _194_488 = (let _194_487 = (let _194_486 = (FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c))
in (FStar_SMTEncoding_Term.boxInt _194_486))
in (_194_487)::[])
in (("FStar.Char.Char"), (_194_488)))
in (FStar_SMTEncoding_Util.mkApp _194_489))
end
| FStar_Const.Const_int (i, None) -> begin
(let _194_490 = (FStar_SMTEncoding_Util.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt _194_490))
end
| FStar_Const.Const_int (i, Some (_93_580)) -> begin
(failwith "Machine integers should be desugared")
end
| FStar_Const.Const_string (bytes, _93_586) -> begin
(let _194_491 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _194_491))
end
| FStar_Const.Const_range (r) -> begin
FStar_SMTEncoding_Term.mk_Range_const
end
| FStar_Const.Const_effect -> begin
FStar_SMTEncoding_Term.mk_Term_type
end
| c -> begin
(let _194_493 = (let _194_492 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" _194_492))
in (failwith _194_493))
end))


let as_function_typ : env_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (

let rec aux = (fun norm t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_93_600) -> begin
t
end
| FStar_Syntax_Syntax.Tm_refine (_93_603) -> begin
(let _194_502 = (FStar_Syntax_Util.unrefine t)
in (aux true _194_502))
end
| _93_606 -> begin
if norm then begin
(let _194_503 = (whnf env t)
in (aux false _194_503))
end else begin
(let _194_506 = (let _194_505 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (let _194_504 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _194_505 _194_504)))
in (failwith _194_506))
end
end)))
in (aux true t0)))


let curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun k -> (

let k = (FStar_Syntax_Subst.compress k)
in (match (k.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| _93_614 -> begin
(let _194_509 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (_194_509)))
end)))


let rec encode_binders : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> (

let _93_618 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _194_557 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" _194_557))
end else begin
()
end
in (

let _93_646 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _93_625 b -> (match (_93_625) with
| (vars, guards, env, decls, names) -> begin
(

let _93_640 = (

let x = (unmangle (Prims.fst b))
in (

let _93_631 = (gen_term_var env x)
in (match (_93_631) with
| (xxsym, xx, env') -> begin
(

let _93_634 = (let _194_560 = (norm env x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt _194_560 env xx))
in (match (_93_634) with
| (guard_x_t, decls') -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (guard_x_t), (env'), (decls'), (x))
end))
end)))
in (match (_93_640) with
| (v, g, env, decls', n) -> begin
(((v)::vars), ((g)::guards), (env), ((FStar_List.append decls decls')), ((n)::names))
end))
end)) (([]), ([]), (env), ([]), ([]))))
in (match (_93_646) with
| (vars, guards, env, decls, names) -> begin
(((FStar_List.rev vars)), ((FStar_List.rev guards)), (env), (decls), ((FStar_List.rev names)))
end))))
and encode_term_pred : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let _93_653 = (encode_term t env)
in (match (_93_653) with
| (t, decls) -> begin
(let _194_565 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t)
in ((_194_565), (decls)))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let _93_660 = (encode_term t env)
in (match (_93_660) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _194_570 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t)
in ((_194_570), (decls)))
end
| Some (f) -> begin
(let _194_571 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t)
in ((_194_571), (decls)))
end)
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let t0 = (FStar_Syntax_Subst.compress t)
in (

let _93_667 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _194_576 = (FStar_Syntax_Print.tag_of_term t)
in (let _194_575 = (FStar_Syntax_Print.tag_of_term t0)
in (let _194_574 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" _194_576 _194_575 _194_574))))
end else begin
()
end
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _194_581 = (let _194_580 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (let _194_579 = (FStar_Syntax_Print.tag_of_term t0)
in (let _194_578 = (FStar_Syntax_Print.term_to_string t0)
in (let _194_577 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _194_580 _194_579 _194_578 _194_577)))))
in (failwith _194_581))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _194_583 = (let _194_582 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" _194_582))
in (failwith _194_583))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, k, _93_678) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_meta (t, _93_683) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t = (lookup_term_var env x)
in ((t), ([])))
end
| FStar_Syntax_Syntax.Tm_fvar (v) -> begin
(let _194_584 = (lookup_free_var env v.FStar_Syntax_Syntax.fv_name)
in ((_194_584), ([])))
end
| FStar_Syntax_Syntax.Tm_type (_93_692) -> begin
((FStar_SMTEncoding_Term.mk_Term_type), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t, _93_696) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(let _194_585 = (encode_const c)
in ((_194_585), ([])))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _93_707 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_93_707) with
| (binders, res) -> begin
if ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res)) then begin
(

let _93_714 = (encode_binders None binders env)
in (match (_93_714) with
| (vars, guards, env', decls, _93_713) -> begin
(

let fsym = (let _194_586 = (varops.fresh "f")
in ((_194_586), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV fsym)
in (

let app = (mk_Apply f vars)
in (

let _93_722 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post (

let _93_718 = env.tcenv
in {FStar_TypeChecker_Env.solver = _93_718.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _93_718.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _93_718.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _93_718.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _93_718.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _93_718.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _93_718.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _93_718.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _93_718.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _93_718.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _93_718.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _93_718.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _93_718.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _93_718.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _93_718.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _93_718.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _93_718.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _93_718.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _93_718.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _93_718.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _93_718.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _93_718.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _93_718.FStar_TypeChecker_Env.qname_and_index}) res)
in (match (_93_722) with
| (pre_opt, res_t) -> begin
(

let _93_725 = (encode_term_pred None res_t env' app)
in (match (_93_725) with
| (res_pred, decls') -> begin
(

let _93_734 = (match (pre_opt) with
| None -> begin
(let _194_587 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((_194_587), ([])))
end
| Some (pre) -> begin
(

let _93_731 = (encode_formula pre env')
in (match (_93_731) with
| (guard, decls0) -> begin
(let _194_588 = (FStar_SMTEncoding_Util.mk_and_l ((guard)::guards))
in ((_194_588), (decls0)))
end))
end)
in (match (_93_734) with
| (guards, guard_decls) -> begin
(

let t_interp = (let _194_590 = (let _194_589 = (FStar_SMTEncoding_Util.mkImp ((guards), (res_pred)))
in ((((app)::[])::[]), (vars), (_194_589)))
in (FStar_SMTEncoding_Util.mkForall _194_590))
in (

let cvars = (let _194_592 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right _194_592 (FStar_List.filter (fun _93_739 -> (match (_93_739) with
| (x, _93_738) -> begin
(x <> (Prims.fst fsym))
end)))))
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), ((fsym)::cvars), (t_interp)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (match ((FStar_Util.smap_try_find env.cache tkey_hash)) with
| Some (t', sorts, _93_746) -> begin
(let _194_595 = (let _194_594 = (let _194_593 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((t'), (_194_593)))
in (FStar_SMTEncoding_Util.mkApp _194_594))
in ((_194_595), ([])))
end
| None -> begin
(

let tsym = (let _194_597 = (let _194_596 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_arrow_" _194_596))
in (varops.mk_unique _194_597))
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let caption = if (FStar_Options.log_queries ()) then begin
(let _194_598 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in Some (_194_598))
end else begin
None
end
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (caption)))
in (

let t = (let _194_600 = (let _194_599 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((tsym), (_194_599)))
in (FStar_SMTEncoding_Util.mkApp _194_600))
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let k_assumption = (

let a_name = Some ((Prims.strcat "kinding_" tsym))
in (let _194_602 = (let _194_601 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((_194_601), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_194_602)))
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t)
in (

let pre_typing = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in (let _194_609 = (let _194_608 = (let _194_607 = (let _194_606 = (let _194_605 = (let _194_604 = (let _194_603 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _194_603))
in ((f_has_t), (_194_604)))
in (FStar_SMTEncoding_Util.mkImp _194_605))
in ((((f_has_t)::[])::[]), ((fsym)::cvars), (_194_606)))
in (mkForall_fuel _194_607))
in ((_194_608), (Some ("pre-typing for functions")), (a_name)))
in FStar_SMTEncoding_Term.Assume (_194_609)))
in (

let t_interp = (

let a_name = Some ((Prims.strcat "interpretation_" tsym))
in (let _194_613 = (let _194_612 = (let _194_611 = (let _194_610 = (FStar_SMTEncoding_Util.mkIff ((f_has_t_z), (t_interp)))
in ((((f_has_t_z)::[])::[]), ((fsym)::cvars), (_194_610)))
in (FStar_SMTEncoding_Util.mkForall _194_611))
in ((_194_612), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_194_613)))
in (

let t_decls = (FStar_List.append ((tdecl)::decls) (FStar_List.append decls' (FStar_List.append guard_decls ((k_assumption)::(pre_typing)::(t_interp)::[]))))
in (

let _93_765 = (FStar_Util.smap_add env.cache tkey_hash ((tsym), (cvar_sorts), (t_decls)))
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
in (let _194_615 = (let _194_614 = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in ((_194_614), (Some ("Typing for non-total arrows")), (a_name)))
in FStar_SMTEncoding_Term.Assume (_194_615)))
in (

let fsym = (("f"), (FStar_SMTEncoding_Term.Term_sort))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV fsym)
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let t_interp = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in (let _194_622 = (let _194_621 = (let _194_620 = (let _194_619 = (let _194_618 = (let _194_617 = (let _194_616 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _194_616))
in ((f_has_t), (_194_617)))
in (FStar_SMTEncoding_Util.mkImp _194_618))
in ((((f_has_t)::[])::[]), ((fsym)::[]), (_194_619)))
in (mkForall_fuel _194_620))
in ((_194_621), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_194_622)))
in ((t), ((tdecl)::(t_kinding)::(t_interp)::[]))))))))))
end
end))
end
| FStar_Syntax_Syntax.Tm_refine (_93_778) -> begin
(

let _93_798 = (match ((FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.tk = _93_785; FStar_Syntax_Syntax.pos = _93_783; FStar_Syntax_Syntax.vars = _93_781} -> begin
(

let _93_793 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) f)
in (match (_93_793) with
| (b, f) -> begin
(let _194_624 = (let _194_623 = (FStar_List.hd b)
in (Prims.fst _194_623))
in ((_194_624), (f)))
end))
end
| _93_795 -> begin
(failwith "impossible")
end)
in (match (_93_798) with
| (x, f) -> begin
(

let _93_801 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (_93_801) with
| (base_t, decls) -> begin
(

let _93_805 = (gen_term_var env x)
in (match (_93_805) with
| (x, xtm, env') -> begin
(

let _93_808 = (encode_formula f env')
in (match (_93_808) with
| (refinement, decls') -> begin
(

let _93_811 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_93_811) with
| (fsym, fterm) -> begin
(

let encoding = (let _194_626 = (let _194_625 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in ((_194_625), (refinement)))
in (FStar_SMTEncoding_Util.mkAnd _194_626))
in (

let cvars = (let _194_628 = (FStar_SMTEncoding_Term.free_variables encoding)
in (FStar_All.pipe_right _194_628 (FStar_List.filter (fun _93_816 -> (match (_93_816) with
| (y, _93_815) -> begin
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
| Some (t, _93_824, _93_826) -> begin
(let _194_631 = (let _194_630 = (let _194_629 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((t), (_194_629)))
in (FStar_SMTEncoding_Util.mkApp _194_630))
in ((_194_631), ([])))
end
| None -> begin
(

let tsym = (let _194_633 = (let _194_632 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_refine_" _194_632))
in (varops.mk_unique _194_633))
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let t = (let _194_635 = (let _194_634 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((tsym), (_194_634)))
in (FStar_SMTEncoding_Util.mkApp _194_635))
in (

let x_has_t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let t_haseq_base = (FStar_SMTEncoding_Term.mk_haseq base_t)
in (

let t_haseq_ref = (FStar_SMTEncoding_Term.mk_haseq t)
in (

let t_haseq = (let _194_639 = (let _194_638 = (let _194_637 = (let _194_636 = (FStar_SMTEncoding_Util.mkIff ((t_haseq_ref), (t_haseq_base)))
in ((((t_haseq_ref)::[])::[]), (cvars), (_194_636)))
in (FStar_SMTEncoding_Util.mkForall _194_637))
in ((_194_638), (Some ((Prims.strcat "haseq for " tsym))), (Some ((Prims.strcat "haseq" tsym)))))
in FStar_SMTEncoding_Term.Assume (_194_639))
in (

let t_kinding = (let _194_641 = (let _194_640 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((_194_640), (Some ("refinement kinding")), (Some ((Prims.strcat "refinement_kinding_" tsym)))))
in FStar_SMTEncoding_Term.Assume (_194_641))
in (

let t_interp = (let _194_647 = (let _194_646 = (let _194_643 = (let _194_642 = (FStar_SMTEncoding_Util.mkIff ((x_has_t), (encoding)))
in ((((x_has_t)::[])::[]), ((ffv)::(xfv)::cvars), (_194_642)))
in (FStar_SMTEncoding_Util.mkForall _194_643))
in (let _194_645 = (let _194_644 = (FStar_Syntax_Print.term_to_string t0)
in Some (_194_644))
in ((_194_646), (_194_645), (Some ((Prims.strcat "refinement_interpretation_" tsym))))))
in FStar_SMTEncoding_Term.Assume (_194_647))
in (

let t_decls = (FStar_List.append decls (FStar_List.append decls' ((tdecl)::(t_kinding)::(t_interp)::(t_haseq)::[])))
in (

let _93_842 = (FStar_Util.smap_add env.cache tkey_hash ((tsym), (cvar_sorts), (t_decls)))
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

let ttm = (let _194_648 = (FStar_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Util.mk_Term_uvar _194_648))
in (

let _93_851 = (encode_term_pred None k env ttm)
in (match (_93_851) with
| (t_has_k, decls) -> begin
(

let d = (let _194_654 = (let _194_653 = (let _194_652 = (let _194_651 = (let _194_650 = (let _194_649 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _194_649))
in (FStar_Util.format1 "uvar_typing_%s" _194_650))
in (varops.mk_unique _194_651))
in Some (_194_652))
in ((t_has_k), (Some ("Uvar typing")), (_194_653)))
in FStar_SMTEncoding_Term.Assume (_194_654))
in ((ttm), ((FStar_List.append decls ((d)::[])))))
end)))
end
| FStar_Syntax_Syntax.Tm_app (_93_854) -> begin
(

let _93_858 = (FStar_Syntax_Util.head_and_args t0)
in (match (_93_858) with
| (head, args_e) -> begin
(match ((let _194_656 = (let _194_655 = (FStar_Syntax_Subst.compress head)
in _194_655.FStar_Syntax_Syntax.n)
in ((_194_656), (args_e)))) with
| (_93_860, _93_862) when (head_redex env head) -> begin
(let _194_657 = (whnf env t)
in (encode_term _194_657 env))
end
| ((FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), (_)::((v1, _))::((v2, _))::[])) | ((FStar_Syntax_Syntax.Tm_fvar (fv), (_)::((v1, _))::((v2, _))::[])) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
(

let _93_902 = (encode_term v1 env)
in (match (_93_902) with
| (v1, decls1) -> begin
(

let _93_905 = (encode_term v2 env)
in (match (_93_905) with
| (v2, decls2) -> begin
(let _194_658 = (FStar_SMTEncoding_Util.mk_LexCons v1 v2)
in ((_194_658), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), (_93_914)::(_93_911)::_93_909) -> begin
(

let e0 = (let _194_662 = (let _194_661 = (let _194_660 = (let _194_659 = (FStar_List.hd args_e)
in (_194_659)::[])
in ((head), (_194_660)))
in FStar_Syntax_Syntax.Tm_app (_194_661))
in (FStar_Syntax_Syntax.mk _194_662 None head.FStar_Syntax_Syntax.pos))
in (

let e = (let _194_665 = (let _194_664 = (let _194_663 = (FStar_List.tl args_e)
in ((e0), (_194_663)))
in FStar_Syntax_Syntax.Tm_app (_194_664))
in (FStar_Syntax_Syntax.mk _194_665 None t0.FStar_Syntax_Syntax.pos))
in (encode_term e env)))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), ((arg, _93_923))::[]) -> begin
(

let _93_929 = (encode_term arg env)
in (match (_93_929) with
| (tm, decls) -> begin
(let _194_666 = (FStar_SMTEncoding_Util.mkApp (("Reify"), ((tm)::[])))
in ((_194_666), (decls)))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (_93_931)), ((arg, _93_936))::[]) -> begin
(encode_term arg env)
end
| _93_941 -> begin
(

let _93_944 = (encode_args args_e env)
in (match (_93_944) with
| (args, decls) -> begin
(

let encode_partial_app = (fun ht_opt -> (

let _93_949 = (encode_term head env)
in (match (_93_949) with
| (head, decls') -> begin
(

let app_tm = (mk_Apply_args head args)
in (match (ht_opt) with
| None -> begin
((app_tm), ((FStar_List.append decls decls')))
end
| Some (formals, c) -> begin
(

let _93_958 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (_93_958) with
| (formals, rest) -> begin
(

let subst = (FStar_List.map2 (fun _93_962 _93_966 -> (match (((_93_962), (_93_966))) with
| ((bv, _93_961), (a, _93_965)) -> begin
FStar_Syntax_Syntax.NT (((bv), (a)))
end)) formals args_e)
in (

let ty = (let _194_671 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right _194_671 (FStar_Syntax_Subst.subst subst)))
in (

let _93_971 = (encode_term_pred None ty env app_tm)
in (match (_93_971) with
| (has_type, decls'') -> begin
(

let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (

let e_typing = (let _194_678 = (let _194_677 = (FStar_SMTEncoding_Util.mkForall ((((has_type)::[])::[]), (cvars), (has_type)))
in (let _194_676 = (let _194_675 = (let _194_674 = (let _194_673 = (let _194_672 = (FStar_SMTEncoding_Term.hash_of_term app_tm)
in (FStar_Util.digest_of_string _194_672))
in (Prims.strcat "partial_app_typing_" _194_673))
in (varops.mk_unique _194_674))
in Some (_194_675))
in ((_194_677), (Some ("Partial app typing")), (_194_676))))
in FStar_SMTEncoding_Term.Assume (_194_678))
in ((app_tm), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' ((e_typing)::[]))))))))
end))))
end))
end))
end)))
in (

let encode_full_app = (fun fv -> (

let _93_978 = (lookup_free_var_sym env fv)
in (match (_93_978) with
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
(let _194_682 = (let _194_681 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _194_681 Prims.snd))
in Some (_194_682))
end
| FStar_Syntax_Syntax.Tm_ascribed (_93_1010, FStar_Util.Inl (t), _93_1014) -> begin
Some (t)
end
| FStar_Syntax_Syntax.Tm_ascribed (_93_1018, FStar_Util.Inr (c), _93_1022) -> begin
Some ((FStar_Syntax_Util.comp_result c))
end
| _93_1026 -> begin
None
end)
in (match (head_type) with
| None -> begin
(encode_partial_app None)
end
| Some (head_type) -> begin
(

let head_type = (let _194_683 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine _194_683))
in (

let _93_1034 = (curried_arrow_formals_comp head_type)
in (match (_93_1034) with
| (formals, c) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| _93_1050 -> begin
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

let _93_1059 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_93_1059) with
| (bs, body, opening) -> begin
(

let fallback = (fun _93_1061 -> (match (()) with
| () -> begin
(

let f = (varops.fresh "Tm_abs")
in (

let decl = FStar_SMTEncoding_Term.DeclFun (((f), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Imprecise function encoding"))))
in (let _194_686 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in ((_194_686), ((decl)::[])))))
end))
in (

let is_impure = (fun _93_10 -> (match (_93_10) with
| FStar_Util.Inl (lc) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)))
end
| FStar_Util.Inr (eff, _93_1069) -> begin
(let _194_689 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv eff)
in (FStar_All.pipe_right _194_689 Prims.op_Negation))
end))
in (

let codomain_eff = (fun lc -> (match (lc) with
| FStar_Util.Inl (lc) -> begin
(let _194_694 = (let _194_692 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening _194_692))
in (FStar_All.pipe_right _194_694 (fun _194_693 -> Some (_194_693))))
end
| FStar_Util.Inr (eff, flags) -> begin
(

let new_uvar = (fun _93_1082 -> (match (()) with
| () -> begin
(let _194_697 = (FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange [] FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _194_697 Prims.fst))
end))
in if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid) then begin
(let _194_700 = (let _194_698 = (new_uvar ())
in (FStar_Syntax_Syntax.mk_Total _194_698))
in (FStar_All.pipe_right _194_700 (fun _194_699 -> Some (_194_699))))
end else begin
if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid) then begin
(let _194_703 = (let _194_701 = (new_uvar ())
in (FStar_Syntax_Syntax.mk_GTotal _194_701))
in (FStar_All.pipe_right _194_703 (fun _194_702 -> Some (_194_702))))
end else begin
None
end
end)
end))
in (match (lopt) with
| None -> begin
(

let _93_1084 = (let _194_705 = (let _194_704 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s" _194_704))
in (FStar_Errors.warn t0.FStar_Syntax_Syntax.pos _194_705))
in (fallback ()))
end
| Some (lc) -> begin
if (is_impure lc) then begin
(fallback ())
end else begin
(

let _93_1094 = (encode_binders None bs env)
in (match (_93_1094) with
| (vars, guards, envbody, decls, _93_1093) -> begin
(

let _93_1097 = (encode_term body envbody)
in (match (_93_1097) with
| (body, decls') -> begin
(

let key_body = (let _194_709 = (let _194_708 = (let _194_707 = (let _194_706 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((_194_706), (body)))
in (FStar_SMTEncoding_Util.mkImp _194_707))
in (([]), (vars), (_194_708)))
in (FStar_SMTEncoding_Util.mkForall _194_709))
in (

let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), (cvars), (key_body)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (match ((FStar_Util.smap_try_find env.cache tkey_hash)) with
| Some (t, _93_1104, _93_1106) -> begin
(let _194_712 = (let _194_711 = (let _194_710 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((t), (_194_710)))
in (FStar_SMTEncoding_Util.mkApp _194_711))
in ((_194_712), ([])))
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

let fsym = (let _194_714 = (let _194_713 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_abs_" _194_713))
in (varops.mk_unique _194_714))
in (

let fdecl = FStar_SMTEncoding_Term.DeclFun (((fsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let f = (let _194_716 = (let _194_715 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((fsym), (_194_715)))
in (FStar_SMTEncoding_Util.mkApp _194_716))
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

let _93_1124 = (encode_term_pred None tfun env f)
in (match (_93_1124) with
| (f_has_t, decls'') -> begin
(

let a_name = Some ((Prims.strcat "typing_" fsym))
in (let _194_720 = (let _194_719 = (let _194_718 = (let _194_717 = (FStar_SMTEncoding_Util.mkForall ((((f)::[])::[]), (cvars), (f_has_t)))
in ((_194_717), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_194_718))
in (_194_719)::[])
in (FStar_List.append decls'' _194_720)))
end)))
end)
in (

let interp_f = (

let a_name = Some ((Prims.strcat "interpretation_" fsym))
in (let _194_724 = (let _194_723 = (let _194_722 = (let _194_721 = (FStar_SMTEncoding_Util.mkEq ((app), (body)))
in ((((app)::[])::[]), ((FStar_List.append vars cvars)), (_194_721)))
in (FStar_SMTEncoding_Util.mkForall _194_722))
in ((_194_723), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_194_724)))
in (

let f_decls = (FStar_List.append decls (FStar_List.append decls' (FStar_List.append ((fdecl)::typing_f) ((interp_f)::[]))))
in (

let _93_1130 = (FStar_Util.smap_add env.cache tkey_hash ((fsym), (cvar_sorts), (f_decls)))
in ((f), (f_decls)))))))))))
end)
end)))))
end))
end))
end
end))))
end))
end
| FStar_Syntax_Syntax.Tm_let ((_93_1133, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_93_1145); FStar_Syntax_Syntax.lbunivs = _93_1143; FStar_Syntax_Syntax.lbtyp = _93_1141; FStar_Syntax_Syntax.lbeff = _93_1139; FStar_Syntax_Syntax.lbdef = _93_1137})::_93_1135), _93_1151) -> begin
(failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _93_1160; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _93_1157; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (_93_1170) -> begin
(

let _93_1172 = (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (

let e = (varops.fresh "let-rec")
in (

let decl_e = FStar_SMTEncoding_Term.DeclFun (((e), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (let _194_725 = (FStar_SMTEncoding_Util.mkFreeV ((e), (FStar_SMTEncoding_Term.Term_sort)))
in ((_194_725), ((decl_e)::[]))))))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end))))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (

let _93_1188 = (encode_term e1 env)
in (match (_93_1188) with
| (ee1, decls1) -> begin
(

let _93_1191 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) e2)
in (match (_93_1191) with
| (xs, e2) -> begin
(

let _93_1195 = (FStar_List.hd xs)
in (match (_93_1195) with
| (x, _93_1194) -> begin
(

let env' = (push_term_var env x ee1)
in (

let _93_1199 = (encode_body e2 env')
in (match (_93_1199) with
| (ee2, decls2) -> begin
((ee2), ((FStar_List.append decls1 decls2)))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (

let _93_1207 = (encode_term e env)
in (match (_93_1207) with
| (scr, decls) -> begin
(

let _93_1244 = (FStar_List.fold_right (fun b _93_1211 -> (match (_93_1211) with
| (else_case, decls) -> begin
(

let _93_1215 = (FStar_Syntax_Subst.open_branch b)
in (match (_93_1215) with
| (p, w, br) -> begin
(

let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun _93_1219 _93_1222 -> (match (((_93_1219), (_93_1222))) with
| ((env0, pattern), (else_case, decls)) -> begin
(

let guard = (pattern.guard scr)
in (

let projections = (pattern.projections scr)
in (

let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env _93_1228 -> (match (_93_1228) with
| (x, t) -> begin
(push_term_var env x t)
end)) env))
in (

let _93_1238 = (match (w) with
| None -> begin
((guard), ([]))
end
| Some (w) -> begin
(

let _93_1235 = (encode_term w env)
in (match (_93_1235) with
| (w, decls2) -> begin
(let _194_759 = (let _194_758 = (let _194_757 = (let _194_756 = (let _194_755 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue)
in ((w), (_194_755)))
in (FStar_SMTEncoding_Util.mkEq _194_756))
in ((guard), (_194_757)))
in (FStar_SMTEncoding_Util.mkAnd _194_758))
in ((_194_759), (decls2)))
end))
end)
in (match (_93_1238) with
| (guard, decls2) -> begin
(

let _93_1241 = (encode_br br env)
in (match (_93_1241) with
| (br, decls3) -> begin
(let _194_760 = (FStar_SMTEncoding_Util.mkITE ((guard), (br), (else_case)))
in ((_194_760), ((FStar_List.append decls (FStar_List.append decls2 decls3)))))
end))
end)))))
end)) patterns ((else_case), (decls))))
end))
end)) pats ((default_case), (decls)))
in (match (_93_1244) with
| (match_tm, decls) -> begin
((match_tm), (decls))
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _93_1250 -> begin
(let _194_763 = (encode_one_pat env pat)
in (_194_763)::[])
end))
and encode_one_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> (

let _93_1253 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _194_766 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" _194_766))
end else begin
()
end
in (

let _93_1257 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (_93_1257) with
| (vars, pat_term) -> begin
(

let _93_1269 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun _93_1260 v -> (match (_93_1260) with
| (env, vars) -> begin
(

let _93_1266 = (gen_term_var env v)
in (match (_93_1266) with
| (xx, _93_1264, env) -> begin
((env), ((((v), (((xx), (FStar_SMTEncoding_Term.Term_sort)))))::vars))
end))
end)) ((env), ([]))))
in (match (_93_1269) with
| (env, vars) -> begin
(

let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_93_1274) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_dot_term (_)) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _194_774 = (let _194_773 = (encode_const c)
in ((scrutinee), (_194_773)))
in (FStar_SMTEncoding_Util.mkEq _194_774))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let is_f = (mk_data_tester env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _93_1296 -> (match (_93_1296) with
| (arg, _93_1295) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _194_777 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_guard arg _194_777)))
end))))
in (FStar_SMTEncoding_Util.mk_and_l ((is_f)::sub_term_guards))))
end))
in (

let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_93_1303) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _)) | (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_constant (_93_1313) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(let _194_785 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _93_1323 -> (match (_93_1323) with
| (arg, _93_1322) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _194_784 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_projections arg _194_784)))
end))))
in (FStar_All.pipe_right _194_785 FStar_List.flatten))
end))
in (

let pat_term = (fun _93_1326 -> (match (()) with
| () -> begin
(encode_term pat_term env)
end))
in (

let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in ((env), (pattern))))))
end))
end))))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (

let _93_1342 = (FStar_All.pipe_right l (FStar_List.fold_left (fun _93_1332 _93_1336 -> (match (((_93_1332), (_93_1336))) with
| ((tms, decls), (t, _93_1335)) -> begin
(

let _93_1339 = (encode_term t env)
in (match (_93_1339) with
| (t, decls') -> begin
(((t)::tms), ((FStar_List.append decls decls')))
end))
end)) (([]), ([]))))
in (match (_93_1342) with
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

let _93_1352 = (FStar_Errors.warn e.FStar_Syntax_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern")
in [])
end))
in (

let one_pat = (fun p -> (

let _93_1358 = (let _194_800 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right _194_800 FStar_Syntax_Util.head_and_args))
in (match (_93_1358) with
| (head, args) -> begin
(match ((let _194_802 = (let _194_801 = (FStar_Syntax_Util.un_uinst head)
in _194_801.FStar_Syntax_Syntax.n)
in ((_194_802), (args)))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((_93_1366, _93_1368))::((e, _93_1363))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpat_lid) -> begin
((e), (None))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, _93_1376))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatT_lid) -> begin
((e), (None))
end
| _93_1381 -> begin
(failwith "Unexpected pattern term")
end)
end)))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements p)
in (

let smt_pat_or = (fun t -> (

let _93_1389 = (let _194_807 = (FStar_Syntax_Util.unmeta t)
in (FStar_All.pipe_right _194_807 FStar_Syntax_Util.head_and_args))
in (match (_93_1389) with
| (head, args) -> begin
(match ((let _194_809 = (let _194_808 = (FStar_Syntax_Util.un_uinst head)
in _194_808.FStar_Syntax_Syntax.n)
in ((_194_809), (args)))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, _93_1394))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatOr_lid) -> begin
Some (e)
end
| _93_1399 -> begin
None
end)
end)))
in (match (elts) with
| (t)::[] -> begin
(match ((smt_pat_or t)) with
| Some (e) -> begin
(let _194_812 = (list_elements e)
in (FStar_All.pipe_right _194_812 (FStar_List.map (fun branch -> (let _194_811 = (list_elements branch)
in (FStar_All.pipe_right _194_811 (FStar_List.map one_pat)))))))
end
| _93_1406 -> begin
(let _194_813 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_194_813)::[])
end)
end
| _93_1408 -> begin
(let _194_814 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_194_814)::[])
end))))
in (

let _93_1451 = (match ((let _194_815 = (FStar_Syntax_Subst.compress t)
in _194_815.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _93_1415 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_93_1415) with
| (binders, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = _93_1436; FStar_Syntax_Syntax.effect_name = _93_1434; FStar_Syntax_Syntax.result_typ = _93_1432; FStar_Syntax_Syntax.effect_args = ((pre, _93_1428))::((post, _93_1424))::((pats, _93_1420))::[]; FStar_Syntax_Syntax.flags = _93_1417}) -> begin
(

let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _194_816 = (lemma_pats pats')
in ((binders), (pre), (post), (_194_816))))
end
| _93_1444 -> begin
(failwith "impos")
end)
end))
end
| _93_1446 -> begin
(failwith "Impos")
end)
in (match (_93_1451) with
| (binders, pre, post, patterns) -> begin
(

let _93_1458 = (encode_binders None binders env)
in (match (_93_1458) with
| (vars, guards, env, decls, _93_1457) -> begin
(

let _93_1471 = (let _194_820 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (

let _93_1468 = (let _194_819 = (FStar_All.pipe_right branch (FStar_List.map (fun _93_1463 -> (match (_93_1463) with
| (t, _93_1462) -> begin
(encode_term t (

let _93_1464 = env
in {bindings = _93_1464.bindings; depth = _93_1464.depth; tcenv = _93_1464.tcenv; warn = _93_1464.warn; cache = _93_1464.cache; nolabels = _93_1464.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _93_1464.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _194_819 FStar_List.unzip))
in (match (_93_1468) with
| (pats, decls) -> begin
((pats), (decls))
end)))))
in (FStar_All.pipe_right _194_820 FStar_List.unzip))
in (match (_93_1471) with
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
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _194_823 = (let _194_822 = (FStar_SMTEncoding_Util.mkFreeV l)
in (FStar_SMTEncoding_Util.mk_Precedes _194_822 e))
in (_194_823)::p))))
end
| _93_1481 -> begin
(

let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _194_829 = (FStar_SMTEncoding_Util.mk_Precedes tl e)
in (_194_829)::p))))
end
| ((x, FStar_SMTEncoding_Term.Term_sort))::vars -> begin
(let _194_831 = (let _194_830 = (FStar_SMTEncoding_Util.mkFreeV ((x), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Util.mk_LexCons _194_830 tl))
in (aux _194_831 vars))
end
| _93_1493 -> begin
pats
end))
in (let _194_832 = (FStar_SMTEncoding_Util.mkFreeV (("Prims.LexTop"), (FStar_SMTEncoding_Term.Term_sort)))
in (aux _194_832 vars)))
end)
end)
in (

let env = (

let _93_1495 = env
in {bindings = _93_1495.bindings; depth = _93_1495.depth; tcenv = _93_1495.tcenv; warn = _93_1495.warn; cache = _93_1495.cache; nolabels = true; use_zfuel_name = _93_1495.use_zfuel_name; encode_non_total_function_typ = _93_1495.encode_non_total_function_typ})
in (

let _93_1500 = (let _194_833 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula _194_833 env))
in (match (_93_1500) with
| (pre, decls'') -> begin
(

let _93_1503 = (let _194_834 = (FStar_Syntax_Util.unmeta post)
in (encode_formula _194_834 env))
in (match (_93_1503) with
| (post, decls''') -> begin
(

let decls = (FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') (FStar_List.append decls'' decls''')))
in (let _194_839 = (let _194_838 = (let _194_837 = (let _194_836 = (let _194_835 = (FStar_SMTEncoding_Util.mk_and_l ((pre)::guards))
in ((_194_835), (post)))
in (FStar_SMTEncoding_Util.mkImp _194_836))
in ((pats), (vars), (_194_837)))
in (FStar_SMTEncoding_Util.mkForall _194_838))
in ((_194_839), (decls))))
end))
end)))))
end))
end))
end))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (

let debug = (fun phi -> if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _194_845 = (FStar_Syntax_Print.tag_of_term phi)
in (let _194_844 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print2 "Formula (%s)  %s\n" _194_845 _194_844)))
end else begin
()
end)
in (

let enc = (fun f r l -> (

let _93_1520 = (FStar_Util.fold_map (fun decls x -> (

let _93_1517 = (encode_term (Prims.fst x) env)
in (match (_93_1517) with
| (t, decls') -> begin
(((FStar_List.append decls decls')), (t))
end))) [] l)
in (match (_93_1520) with
| (decls, args) -> begin
(let _194_867 = (

let _93_1521 = (f args)
in {FStar_SMTEncoding_Term.tm = _93_1521.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = _93_1521.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((_194_867), (decls)))
end)))
in (

let const_op = (fun f r _93_1526 -> (let _194_879 = (f r)
in ((_194_879), ([]))))
in (

let un_op = (fun f l -> (let _194_889 = (FStar_List.hd l)
in (FStar_All.pipe_left f _194_889)))
in (

let bin_op = (fun f _93_11 -> (match (_93_11) with
| (t1)::(t2)::[] -> begin
(f ((t1), (t2)))
end
| _93_1537 -> begin
(failwith "Impossible")
end))
in (

let enc_prop_c = (fun f r l -> (

let _93_1553 = (FStar_Util.fold_map (fun decls _93_1547 -> (match (_93_1547) with
| (t, _93_1546) -> begin
(

let _93_1550 = (encode_formula t env)
in (match (_93_1550) with
| (phi, decls') -> begin
(((FStar_List.append decls decls')), (phi))
end))
end)) [] l)
in (match (_93_1553) with
| (decls, phis) -> begin
(let _194_920 = (

let _93_1554 = (f phis)
in {FStar_SMTEncoding_Term.tm = _93_1554.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = _93_1554.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((_194_920), (decls)))
end)))
in (

let eq_op = (fun r _93_12 -> (match (_93_12) with
| ((_)::(e1)::(e2)::[]) | ((_)::(_)::(e1)::(e2)::[]) -> begin
(enc (bin_op FStar_SMTEncoding_Util.mkEq) r ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op FStar_SMTEncoding_Util.mkEq) r l)
end))
in (

let mk_imp = (fun r _93_13 -> (match (_93_13) with
| ((lhs, _93_1579))::((rhs, _93_1575))::[] -> begin
(

let _93_1584 = (encode_formula rhs env)
in (match (_93_1584) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, _93_1587) -> begin
((l1), (decls1))
end
| _93_1591 -> begin
(

let _93_1594 = (encode_formula lhs env)
in (match (_93_1594) with
| (l2, decls2) -> begin
(let _194_937 = (FStar_SMTEncoding_Term.mkImp ((l2), (l1)) r)
in ((_194_937), ((FStar_List.append decls1 decls2))))
end))
end)
end))
end
| _93_1596 -> begin
(failwith "impossible")
end))
in (

let mk_ite = (fun r _93_14 -> (match (_93_14) with
| ((guard, _93_1610))::((_then, _93_1606))::((_else, _93_1602))::[] -> begin
(

let _93_1615 = (encode_formula guard env)
in (match (_93_1615) with
| (g, decls1) -> begin
(

let _93_1618 = (encode_formula _then env)
in (match (_93_1618) with
| (t, decls2) -> begin
(

let _93_1621 = (encode_formula _else env)
in (match (_93_1621) with
| (e, decls3) -> begin
(

let res = (FStar_SMTEncoding_Term.mkITE ((g), (t), (e)) r)
in ((res), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end))
end))
end
| _93_1624 -> begin
(failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (let _194_955 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f _194_955)))
in (

let connectives = (let _194_1058 = (let _194_971 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd))
in ((FStar_Syntax_Const.and_lid), (_194_971)))
in (let _194_1057 = (let _194_1056 = (let _194_981 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr))
in ((FStar_Syntax_Const.or_lid), (_194_981)))
in (let _194_1055 = (let _194_1054 = (let _194_1053 = (let _194_999 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff))
in ((FStar_Syntax_Const.iff_lid), (_194_999)))
in (let _194_1052 = (let _194_1051 = (let _194_1050 = (let _194_1017 = (FStar_All.pipe_left enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot))
in ((FStar_Syntax_Const.not_lid), (_194_1017)))
in (_194_1050)::(((FStar_Syntax_Const.eq2_lid), (eq_op)))::(((FStar_Syntax_Const.eq3_lid), (eq_op)))::(((FStar_Syntax_Const.true_lid), ((const_op FStar_SMTEncoding_Term.mkTrue))))::(((FStar_Syntax_Const.false_lid), ((const_op FStar_SMTEncoding_Term.mkFalse))))::[])
in (((FStar_Syntax_Const.ite_lid), (mk_ite)))::_194_1051)
in (_194_1053)::_194_1052))
in (((FStar_Syntax_Const.imp_lid), (mk_imp)))::_194_1054)
in (_194_1056)::_194_1055))
in (_194_1058)::_194_1057))
in (

let rec fallback = (fun phi -> (match (phi.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(

let _93_1641 = (encode_formula phi' env)
in (match (_93_1641) with
| (phi, decls) -> begin
(let _194_1061 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled (((phi), (msg), (r)))) r)
in ((_194_1061), (decls)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (_93_1643) -> begin
(let _194_1062 = (FStar_Syntax_Util.unmeta phi)
in (encode_formula _194_1062 env))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(

let _93_1651 = (encode_match e pats FStar_SMTEncoding_Util.mkFalse env encode_formula)
in (match (_93_1651) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _93_1658; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _93_1655; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _93_1669 = (encode_let x t1 e1 e2 env encode_formula)
in (match (_93_1669) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let head = (FStar_Syntax_Util.un_uinst head)
in (match (((head.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_93_1686)::((x, _93_1683))::((t, _93_1679))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.has_type_lid) -> begin
(

let _93_1691 = (encode_term x env)
in (match (_93_1691) with
| (x, decls) -> begin
(

let _93_1694 = (encode_term t env)
in (match (_93_1694) with
| (t, decls') -> begin
(let _194_1063 = (FStar_SMTEncoding_Term.mk_HasType x t)
in ((_194_1063), ((FStar_List.append decls decls'))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((r, _93_1707))::((msg, _93_1703))::((phi, _93_1699))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.labeled_lid) -> begin
(match ((let _194_1067 = (let _194_1064 = (FStar_Syntax_Subst.compress r)
in _194_1064.FStar_Syntax_Syntax.n)
in (let _194_1066 = (let _194_1065 = (FStar_Syntax_Subst.compress msg)
in _194_1065.FStar_Syntax_Syntax.n)
in ((_194_1067), (_194_1066))))) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, _93_1716))) -> begin
(

let phi = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((phi), (FStar_Syntax_Syntax.Meta_labeled ((((FStar_Util.string_of_unicode s)), (r), (false))))))) None r)
in (fallback phi))
end
| _93_1723 -> begin
(fallback phi)
end)
end
| _93_1725 when (head_redex env head) -> begin
(let _194_1068 = (whnf env phi)
in (encode_formula _194_1068 env))
end
| _93_1727 -> begin
(

let _93_1730 = (encode_term phi env)
in (match (_93_1730) with
| (tt, decls) -> begin
(let _194_1069 = (FStar_SMTEncoding_Term.mk_Valid (

let _93_1731 = tt
in {FStar_SMTEncoding_Term.tm = _93_1731.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = _93_1731.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi.FStar_Syntax_Syntax.pos}))
in ((_194_1069), (decls)))
end))
end))
end
| _93_1734 -> begin
(

let _93_1737 = (encode_term phi env)
in (match (_93_1737) with
| (tt, decls) -> begin
(let _194_1070 = (FStar_SMTEncoding_Term.mk_Valid (

let _93_1738 = tt
in {FStar_SMTEncoding_Term.tm = _93_1738.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = _93_1738.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi.FStar_Syntax_Syntax.pos}))
in ((_194_1070), (decls)))
end))
end))
in (

let encode_q_body = (fun env bs ps body -> (

let _93_1751 = (encode_binders None bs env)
in (match (_93_1751) with
| (vars, guards, env, decls, _93_1750) -> begin
(

let _93_1764 = (let _194_1082 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let _93_1761 = (let _194_1081 = (FStar_All.pipe_right p (FStar_List.map (fun _93_1756 -> (match (_93_1756) with
| (t, _93_1755) -> begin
(encode_term t (

let _93_1757 = env
in {bindings = _93_1757.bindings; depth = _93_1757.depth; tcenv = _93_1757.tcenv; warn = _93_1757.warn; cache = _93_1757.cache; nolabels = _93_1757.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _93_1757.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _194_1081 FStar_List.unzip))
in (match (_93_1761) with
| (p, decls) -> begin
((p), ((FStar_List.flatten decls)))
end)))))
in (FStar_All.pipe_right _194_1082 FStar_List.unzip))
in (match (_93_1764) with
| (pats, decls') -> begin
(

let _93_1767 = (encode_formula body env)
in (match (_93_1767) with
| (body, decls'') -> begin
(

let guards = (match (pats) with
| (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (gf), (p)::[]); FStar_SMTEncoding_Term.freevars = _93_1771; FStar_SMTEncoding_Term.rng = _93_1769})::[])::[] when ((FStar_Ident.text_of_lid FStar_Syntax_Const.guard_free) = gf) -> begin
[]
end
| _93_1782 -> begin
guards
end)
in (let _194_1083 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((vars), (pats), (_194_1083), (body), ((FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') decls''))))))
end))
end))
end)))
in (

let _93_1784 = (debug phi)
in (

let phi = (FStar_Syntax_Util.unascribe phi)
in (

let check_pattern_vars = (fun vars pats -> (

let pats = (FStar_All.pipe_right pats (FStar_List.map (fun _93_1793 -> (match (_93_1793) with
| (x, _93_1792) -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x)
end))))
in (match (pats) with
| [] -> begin
()
end
| (hd)::tl -> begin
(

let pat_vars = (let _194_1092 = (FStar_Syntax_Free.names hd)
in (FStar_List.fold_left (fun out x -> (let _194_1091 = (FStar_Syntax_Free.names x)
in (FStar_Util.set_union out _194_1091))) _194_1092 tl))
in (match ((FStar_All.pipe_right vars (FStar_Util.find_opt (fun _93_1805 -> (match (_93_1805) with
| (b, _93_1804) -> begin
(not ((FStar_Util.set_mem b pat_vars)))
end))))) with
| None -> begin
()
end
| Some (x, _93_1809) -> begin
(

let pos = (FStar_List.fold_left (fun out t -> (FStar_Range.union_ranges out t.FStar_Syntax_Syntax.pos)) hd.FStar_Syntax_Syntax.pos tl)
in (let _194_1097 = (let _194_1096 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "SMT pattern misses at least one bound variable: %s" _194_1096))
in (FStar_Errors.warn pos _194_1097)))
end))
end)))
in (match ((FStar_Syntax_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _93_1824 -> (match (_93_1824) with
| (l, _93_1823) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_93_1827, f) -> begin
(f phi.FStar_Syntax_Syntax.pos arms)
end)
end
| Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
(

let _93_1837 = (FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)))
in (

let _93_1844 = (encode_q_body env vars pats body)
in (match (_93_1844) with
| (vars, pats, guard, body, decls) -> begin
(

let tm = (let _194_1130 = (let _194_1129 = (FStar_SMTEncoding_Util.mkImp ((guard), (body)))
in ((pats), (vars), (_194_1129)))
in (FStar_SMTEncoding_Term.mkForall _194_1130 phi.FStar_Syntax_Syntax.pos))
in ((tm), (decls)))
end)))
end
| Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
(

let _93_1852 = (FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)))
in (

let _93_1859 = (encode_q_body env vars pats body)
in (match (_93_1859) with
| (vars, pats, guard, body, decls) -> begin
(let _194_1133 = (let _194_1132 = (let _194_1131 = (FStar_SMTEncoding_Util.mkAnd ((guard), (body)))
in ((pats), (vars), (_194_1131)))
in (FStar_SMTEncoding_Term.mkExists _194_1132 phi.FStar_Syntax_Syntax.pos))
in ((_194_1133), (decls)))
end)))
end))))))))))))))))))


type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list); is : FStar_Ident.lident  ->  Prims.bool}


let is_Mkprims_t : prims_t  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkprims_t"))))


let prims : prims_t = (

let _93_1865 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (_93_1865) with
| (asym, a) -> begin
(

let _93_1868 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_93_1868) with
| (xsym, x) -> begin
(

let _93_1871 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (_93_1871) with
| (ysym, y) -> begin
(

let quant = (fun vars body x -> (

let xname_decl = (let _194_1170 = (let _194_1169 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in ((x), (_194_1169), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (_194_1170))
in (

let xtok = (Prims.strcat x "@tok")
in (

let xtok_decl = FStar_SMTEncoding_Term.DeclFun (((xtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let xapp = (let _194_1172 = (let _194_1171 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((x), (_194_1171)))
in (FStar_SMTEncoding_Util.mkApp _194_1172))
in (

let xtok = (FStar_SMTEncoding_Util.mkApp ((xtok), ([])))
in (

let xtok_app = (mk_Apply xtok vars)
in (let _194_1186 = (let _194_1185 = (let _194_1184 = (let _194_1183 = (let _194_1176 = (let _194_1175 = (let _194_1174 = (let _194_1173 = (FStar_SMTEncoding_Util.mkEq ((xapp), (body)))
in ((((xapp)::[])::[]), (vars), (_194_1173)))
in (FStar_SMTEncoding_Util.mkForall _194_1174))
in ((_194_1175), (None), (Some ((Prims.strcat "primitive_" x)))))
in FStar_SMTEncoding_Term.Assume (_194_1176))
in (let _194_1182 = (let _194_1181 = (let _194_1180 = (let _194_1179 = (let _194_1178 = (let _194_1177 = (FStar_SMTEncoding_Util.mkEq ((xtok_app), (xapp)))
in ((((xtok_app)::[])::[]), (vars), (_194_1177)))
in (FStar_SMTEncoding_Util.mkForall _194_1178))
in ((_194_1179), (Some ("Name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" x)))))
in FStar_SMTEncoding_Term.Assume (_194_1180))
in (_194_1181)::[])
in (_194_1183)::_194_1182))
in (xtok_decl)::_194_1184)
in (xname_decl)::_194_1185)
in ((xtok), (_194_1186))))))))))
in (

let axy = (((asym), (FStar_SMTEncoding_Term.Term_sort)))::(((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let xy = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let qx = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let prims = (let _194_1346 = (let _194_1195 = (let _194_1194 = (let _194_1193 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _194_1193))
in (quant axy _194_1194))
in ((FStar_Syntax_Const.op_Eq), (_194_1195)))
in (let _194_1345 = (let _194_1344 = (let _194_1202 = (let _194_1201 = (let _194_1200 = (let _194_1199 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_SMTEncoding_Util.mkNot _194_1199))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _194_1200))
in (quant axy _194_1201))
in ((FStar_Syntax_Const.op_notEq), (_194_1202)))
in (let _194_1343 = (let _194_1342 = (let _194_1211 = (let _194_1210 = (let _194_1209 = (let _194_1208 = (let _194_1207 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _194_1206 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_194_1207), (_194_1206))))
in (FStar_SMTEncoding_Util.mkLT _194_1208))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _194_1209))
in (quant xy _194_1210))
in ((FStar_Syntax_Const.op_LT), (_194_1211)))
in (let _194_1341 = (let _194_1340 = (let _194_1220 = (let _194_1219 = (let _194_1218 = (let _194_1217 = (let _194_1216 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _194_1215 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_194_1216), (_194_1215))))
in (FStar_SMTEncoding_Util.mkLTE _194_1217))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _194_1218))
in (quant xy _194_1219))
in ((FStar_Syntax_Const.op_LTE), (_194_1220)))
in (let _194_1339 = (let _194_1338 = (let _194_1229 = (let _194_1228 = (let _194_1227 = (let _194_1226 = (let _194_1225 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _194_1224 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_194_1225), (_194_1224))))
in (FStar_SMTEncoding_Util.mkGT _194_1226))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _194_1227))
in (quant xy _194_1228))
in ((FStar_Syntax_Const.op_GT), (_194_1229)))
in (let _194_1337 = (let _194_1336 = (let _194_1238 = (let _194_1237 = (let _194_1236 = (let _194_1235 = (let _194_1234 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _194_1233 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_194_1234), (_194_1233))))
in (FStar_SMTEncoding_Util.mkGTE _194_1235))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _194_1236))
in (quant xy _194_1237))
in ((FStar_Syntax_Const.op_GTE), (_194_1238)))
in (let _194_1335 = (let _194_1334 = (let _194_1247 = (let _194_1246 = (let _194_1245 = (let _194_1244 = (let _194_1243 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _194_1242 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_194_1243), (_194_1242))))
in (FStar_SMTEncoding_Util.mkSub _194_1244))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _194_1245))
in (quant xy _194_1246))
in ((FStar_Syntax_Const.op_Subtraction), (_194_1247)))
in (let _194_1333 = (let _194_1332 = (let _194_1254 = (let _194_1253 = (let _194_1252 = (let _194_1251 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Util.mkMinus _194_1251))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _194_1252))
in (quant qx _194_1253))
in ((FStar_Syntax_Const.op_Minus), (_194_1254)))
in (let _194_1331 = (let _194_1330 = (let _194_1263 = (let _194_1262 = (let _194_1261 = (let _194_1260 = (let _194_1259 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _194_1258 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_194_1259), (_194_1258))))
in (FStar_SMTEncoding_Util.mkAdd _194_1260))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _194_1261))
in (quant xy _194_1262))
in ((FStar_Syntax_Const.op_Addition), (_194_1263)))
in (let _194_1329 = (let _194_1328 = (let _194_1272 = (let _194_1271 = (let _194_1270 = (let _194_1269 = (let _194_1268 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _194_1267 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_194_1268), (_194_1267))))
in (FStar_SMTEncoding_Util.mkMul _194_1269))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _194_1270))
in (quant xy _194_1271))
in ((FStar_Syntax_Const.op_Multiply), (_194_1272)))
in (let _194_1327 = (let _194_1326 = (let _194_1281 = (let _194_1280 = (let _194_1279 = (let _194_1278 = (let _194_1277 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _194_1276 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_194_1277), (_194_1276))))
in (FStar_SMTEncoding_Util.mkDiv _194_1278))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _194_1279))
in (quant xy _194_1280))
in ((FStar_Syntax_Const.op_Division), (_194_1281)))
in (let _194_1325 = (let _194_1324 = (let _194_1290 = (let _194_1289 = (let _194_1288 = (let _194_1287 = (let _194_1286 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _194_1285 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_194_1286), (_194_1285))))
in (FStar_SMTEncoding_Util.mkMod _194_1287))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _194_1288))
in (quant xy _194_1289))
in ((FStar_Syntax_Const.op_Modulus), (_194_1290)))
in (let _194_1323 = (let _194_1322 = (let _194_1299 = (let _194_1298 = (let _194_1297 = (let _194_1296 = (let _194_1295 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _194_1294 = (FStar_SMTEncoding_Term.unboxBool y)
in ((_194_1295), (_194_1294))))
in (FStar_SMTEncoding_Util.mkAnd _194_1296))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _194_1297))
in (quant xy _194_1298))
in ((FStar_Syntax_Const.op_And), (_194_1299)))
in (let _194_1321 = (let _194_1320 = (let _194_1308 = (let _194_1307 = (let _194_1306 = (let _194_1305 = (let _194_1304 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _194_1303 = (FStar_SMTEncoding_Term.unboxBool y)
in ((_194_1304), (_194_1303))))
in (FStar_SMTEncoding_Util.mkOr _194_1305))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _194_1306))
in (quant xy _194_1307))
in ((FStar_Syntax_Const.op_Or), (_194_1308)))
in (let _194_1319 = (let _194_1318 = (let _194_1315 = (let _194_1314 = (let _194_1313 = (let _194_1312 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Util.mkNot _194_1312))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _194_1313))
in (quant qx _194_1314))
in ((FStar_Syntax_Const.op_Negation), (_194_1315)))
in (_194_1318)::[])
in (_194_1320)::_194_1319))
in (_194_1322)::_194_1321))
in (_194_1324)::_194_1323))
in (_194_1326)::_194_1325))
in (_194_1328)::_194_1327))
in (_194_1330)::_194_1329))
in (_194_1332)::_194_1331))
in (_194_1334)::_194_1333))
in (_194_1336)::_194_1335))
in (_194_1338)::_194_1337))
in (_194_1340)::_194_1339))
in (_194_1342)::_194_1341))
in (_194_1344)::_194_1343))
in (_194_1346)::_194_1345))
in (

let mk = (fun l v -> (let _194_1393 = (let _194_1392 = (FStar_All.pipe_right prims (FStar_List.find (fun _93_1891 -> (match (_93_1891) with
| (l', _93_1890) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right _194_1392 (FStar_Option.map (fun _93_1895 -> (match (_93_1895) with
| (_93_1893, b) -> begin
(b v)
end)))))
in (FStar_All.pipe_right _194_1393 FStar_Option.get)))
in (

let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _93_1901 -> (match (_93_1901) with
| (l', _93_1900) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is})))))))
end))
end))
end))


let pretype_axiom : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun tapp vars -> (

let _93_1907 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_93_1907) with
| (xxsym, xx) -> begin
(

let _93_1910 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_93_1910) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let tapp_hash = (FStar_SMTEncoding_Term.hash_of_term tapp)
in (let _194_1423 = (let _194_1422 = (let _194_1417 = (let _194_1416 = (let _194_1415 = (let _194_1414 = (let _194_1413 = (let _194_1412 = (FStar_SMTEncoding_Util.mkApp (("PreType"), ((xx)::[])))
in ((tapp), (_194_1412)))
in (FStar_SMTEncoding_Util.mkEq _194_1413))
in ((xx_has_type), (_194_1414)))
in (FStar_SMTEncoding_Util.mkImp _194_1415))
in ((((xx_has_type)::[])::[]), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars), (_194_1416)))
in (FStar_SMTEncoding_Util.mkForall _194_1417))
in (let _194_1421 = (let _194_1420 = (let _194_1419 = (let _194_1418 = (FStar_Util.digest_of_string tapp_hash)
in (Prims.strcat "pretyping_" _194_1418))
in (varops.mk_unique _194_1419))
in Some (_194_1420))
in ((_194_1422), (Some ("pretyping")), (_194_1421))))
in FStar_SMTEncoding_Term.Assume (_194_1423))))
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
in (let _194_1444 = (let _194_1435 = (let _194_1434 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in ((_194_1434), (Some ("unit typing")), (Some ("unit_typing"))))
in FStar_SMTEncoding_Term.Assume (_194_1435))
in (let _194_1443 = (let _194_1442 = (let _194_1441 = (let _194_1440 = (let _194_1439 = (let _194_1438 = (let _194_1437 = (let _194_1436 = (FStar_SMTEncoding_Util.mkEq ((x), (FStar_SMTEncoding_Term.mk_Term_unit)))
in ((typing_pred), (_194_1436)))
in (FStar_SMTEncoding_Util.mkImp _194_1437))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_194_1438)))
in (mkForall_fuel _194_1439))
in ((_194_1440), (Some ("unit inversion")), (Some ("unit_inversion"))))
in FStar_SMTEncoding_Term.Assume (_194_1441))
in (_194_1442)::[])
in (_194_1444)::_194_1443))))
in (

let mk_bool = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Bool_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (let _194_1467 = (let _194_1458 = (let _194_1457 = (let _194_1456 = (let _194_1455 = (let _194_1452 = (let _194_1451 = (FStar_SMTEncoding_Term.boxBool b)
in (_194_1451)::[])
in (_194_1452)::[])
in (let _194_1454 = (let _194_1453 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType _194_1453 tt))
in ((_194_1455), ((bb)::[]), (_194_1454))))
in (FStar_SMTEncoding_Util.mkForall _194_1456))
in ((_194_1457), (Some ("bool typing")), (Some ("bool_typing"))))
in FStar_SMTEncoding_Term.Assume (_194_1458))
in (let _194_1466 = (let _194_1465 = (let _194_1464 = (let _194_1463 = (let _194_1462 = (let _194_1461 = (let _194_1460 = (let _194_1459 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in ((typing_pred), (_194_1459)))
in (FStar_SMTEncoding_Util.mkImp _194_1460))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_194_1461)))
in (mkForall_fuel _194_1462))
in ((_194_1463), (Some ("bool inversion")), (Some ("bool_inversion"))))
in FStar_SMTEncoding_Term.Assume (_194_1464))
in (_194_1465)::[])
in (_194_1467)::_194_1466))))))
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

let precedes = (let _194_1481 = (let _194_1480 = (let _194_1479 = (let _194_1478 = (let _194_1477 = (let _194_1476 = (FStar_SMTEncoding_Term.boxInt a)
in (let _194_1475 = (let _194_1474 = (FStar_SMTEncoding_Term.boxInt b)
in (_194_1474)::[])
in (_194_1476)::_194_1475))
in (tt)::_194_1477)
in (tt)::_194_1478)
in (("Prims.Precedes"), (_194_1479)))
in (FStar_SMTEncoding_Util.mkApp _194_1480))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _194_1481))
in (

let precedes_y_x = (let _194_1482 = (FStar_SMTEncoding_Util.mkApp (("Precedes"), ((y)::(x)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _194_1482))
in (let _194_1524 = (let _194_1490 = (let _194_1489 = (let _194_1488 = (let _194_1487 = (let _194_1484 = (let _194_1483 = (FStar_SMTEncoding_Term.boxInt b)
in (_194_1483)::[])
in (_194_1484)::[])
in (let _194_1486 = (let _194_1485 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType _194_1485 tt))
in ((_194_1487), ((bb)::[]), (_194_1486))))
in (FStar_SMTEncoding_Util.mkForall _194_1488))
in ((_194_1489), (Some ("int typing")), (Some ("int_typing"))))
in FStar_SMTEncoding_Term.Assume (_194_1490))
in (let _194_1523 = (let _194_1522 = (let _194_1496 = (let _194_1495 = (let _194_1494 = (let _194_1493 = (let _194_1492 = (let _194_1491 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in ((typing_pred), (_194_1491)))
in (FStar_SMTEncoding_Util.mkImp _194_1492))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_194_1493)))
in (mkForall_fuel _194_1494))
in ((_194_1495), (Some ("int inversion")), (Some ("int_inversion"))))
in FStar_SMTEncoding_Term.Assume (_194_1496))
in (let _194_1521 = (let _194_1520 = (let _194_1519 = (let _194_1518 = (let _194_1517 = (let _194_1516 = (let _194_1515 = (let _194_1514 = (let _194_1513 = (let _194_1512 = (let _194_1511 = (let _194_1510 = (let _194_1499 = (let _194_1498 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _194_1497 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((_194_1498), (_194_1497))))
in (FStar_SMTEncoding_Util.mkGT _194_1499))
in (let _194_1509 = (let _194_1508 = (let _194_1502 = (let _194_1501 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _194_1500 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((_194_1501), (_194_1500))))
in (FStar_SMTEncoding_Util.mkGTE _194_1502))
in (let _194_1507 = (let _194_1506 = (let _194_1505 = (let _194_1504 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _194_1503 = (FStar_SMTEncoding_Term.unboxInt x)
in ((_194_1504), (_194_1503))))
in (FStar_SMTEncoding_Util.mkLT _194_1505))
in (_194_1506)::[])
in (_194_1508)::_194_1507))
in (_194_1510)::_194_1509))
in (typing_pred_y)::_194_1511)
in (typing_pred)::_194_1512)
in (FStar_SMTEncoding_Util.mk_and_l _194_1513))
in ((_194_1514), (precedes_y_x)))
in (FStar_SMTEncoding_Util.mkImp _194_1515))
in ((((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[]), ((xx)::(yy)::[]), (_194_1516)))
in (mkForall_fuel _194_1517))
in ((_194_1518), (Some ("well-founded ordering on nat (alt)")), (Some ("well-founded-ordering-on-nat"))))
in FStar_SMTEncoding_Term.Assume (_194_1519))
in (_194_1520)::[])
in (_194_1522)::_194_1521))
in (_194_1524)::_194_1523)))))))))))
in (

let mk_str = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.String_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (let _194_1547 = (let _194_1538 = (let _194_1537 = (let _194_1536 = (let _194_1535 = (let _194_1532 = (let _194_1531 = (FStar_SMTEncoding_Term.boxString b)
in (_194_1531)::[])
in (_194_1532)::[])
in (let _194_1534 = (let _194_1533 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType _194_1533 tt))
in ((_194_1535), ((bb)::[]), (_194_1534))))
in (FStar_SMTEncoding_Util.mkForall _194_1536))
in ((_194_1537), (Some ("string typing")), (Some ("string_typing"))))
in FStar_SMTEncoding_Term.Assume (_194_1538))
in (let _194_1546 = (let _194_1545 = (let _194_1544 = (let _194_1543 = (let _194_1542 = (let _194_1541 = (let _194_1540 = (let _194_1539 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in ((typing_pred), (_194_1539)))
in (FStar_SMTEncoding_Util.mkImp _194_1540))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_194_1541)))
in (mkForall_fuel _194_1542))
in ((_194_1543), (Some ("string inversion")), (Some ("string_inversion"))))
in FStar_SMTEncoding_Term.Assume (_194_1544))
in (_194_1545)::[])
in (_194_1547)::_194_1546))))))
in (

let mk_ref = (fun env reft_name _93_1950 -> (

let r = (("r"), (FStar_SMTEncoding_Term.Ref_sort))
in (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let refa = (let _194_1556 = (let _194_1555 = (let _194_1554 = (FStar_SMTEncoding_Util.mkFreeV aa)
in (_194_1554)::[])
in ((reft_name), (_194_1555)))
in (FStar_SMTEncoding_Util.mkApp _194_1556))
in (

let refb = (let _194_1559 = (let _194_1558 = (let _194_1557 = (FStar_SMTEncoding_Util.mkFreeV bb)
in (_194_1557)::[])
in ((reft_name), (_194_1558)))
in (FStar_SMTEncoding_Util.mkApp _194_1559))
in (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (

let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (let _194_1578 = (let _194_1565 = (let _194_1564 = (let _194_1563 = (let _194_1562 = (let _194_1561 = (let _194_1560 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in ((typing_pred), (_194_1560)))
in (FStar_SMTEncoding_Util.mkImp _194_1561))
in ((((typing_pred)::[])::[]), ((xx)::(aa)::[]), (_194_1562)))
in (mkForall_fuel _194_1563))
in ((_194_1564), (Some ("ref inversion")), (Some ("ref_inversion"))))
in FStar_SMTEncoding_Term.Assume (_194_1565))
in (let _194_1577 = (let _194_1576 = (let _194_1575 = (let _194_1574 = (let _194_1573 = (let _194_1572 = (let _194_1571 = (let _194_1570 = (FStar_SMTEncoding_Util.mkAnd ((typing_pred), (typing_pred_b)))
in (let _194_1569 = (let _194_1568 = (let _194_1567 = (FStar_SMTEncoding_Util.mkFreeV aa)
in (let _194_1566 = (FStar_SMTEncoding_Util.mkFreeV bb)
in ((_194_1567), (_194_1566))))
in (FStar_SMTEncoding_Util.mkEq _194_1568))
in ((_194_1570), (_194_1569))))
in (FStar_SMTEncoding_Util.mkImp _194_1571))
in ((((typing_pred)::(typing_pred_b)::[])::[]), ((xx)::(aa)::(bb)::[]), (_194_1572)))
in (mkForall_fuel' (Prims.parse_int "2") _194_1573))
in ((_194_1574), (Some ("ref typing is injective")), (Some ("ref_injectivity"))))
in FStar_SMTEncoding_Term.Assume (_194_1575))
in (_194_1576)::[])
in (_194_1578)::_194_1577))))))))))
in (

let mk_true_interp = (fun env nm true_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((true_tm)::[])))
in (FStar_SMTEncoding_Term.Assume (((valid), (Some ("True interpretation")), (Some ("true_interp")))))::[]))
in (

let mk_false_interp = (fun env nm false_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((false_tm)::[])))
in (let _194_1593 = (let _194_1592 = (let _194_1591 = (FStar_SMTEncoding_Util.mkIff ((FStar_SMTEncoding_Util.mkFalse), (valid)))
in ((_194_1591), (Some ("False interpretation")), (Some ("false_interp"))))
in FStar_SMTEncoding_Term.Assume (_194_1592))
in (_194_1593)::[])))
in (

let mk_and_interp = (fun env conj _93_1972 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let valid = (let _194_1602 = (let _194_1601 = (let _194_1600 = (FStar_SMTEncoding_Util.mkApp ((conj), ((a)::(b)::[])))
in (_194_1600)::[])
in (("Valid"), (_194_1601)))
in (FStar_SMTEncoding_Util.mkApp _194_1602))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (let _194_1609 = (let _194_1608 = (let _194_1607 = (let _194_1606 = (let _194_1605 = (let _194_1604 = (let _194_1603 = (FStar_SMTEncoding_Util.mkAnd ((valid_a), (valid_b)))
in ((_194_1603), (valid)))
in (FStar_SMTEncoding_Util.mkIff _194_1604))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_194_1605)))
in (FStar_SMTEncoding_Util.mkForall _194_1606))
in ((_194_1607), (Some ("/\\ interpretation")), (Some ("l_and-interp"))))
in FStar_SMTEncoding_Term.Assume (_194_1608))
in (_194_1609)::[])))))))))
in (

let mk_or_interp = (fun env disj _93_1984 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let valid = (let _194_1618 = (let _194_1617 = (let _194_1616 = (FStar_SMTEncoding_Util.mkApp ((disj), ((a)::(b)::[])))
in (_194_1616)::[])
in (("Valid"), (_194_1617)))
in (FStar_SMTEncoding_Util.mkApp _194_1618))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (let _194_1625 = (let _194_1624 = (let _194_1623 = (let _194_1622 = (let _194_1621 = (let _194_1620 = (let _194_1619 = (FStar_SMTEncoding_Util.mkOr ((valid_a), (valid_b)))
in ((_194_1619), (valid)))
in (FStar_SMTEncoding_Util.mkIff _194_1620))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_194_1621)))
in (FStar_SMTEncoding_Util.mkForall _194_1622))
in ((_194_1623), (Some ("\\/ interpretation")), (Some ("l_or-interp"))))
in FStar_SMTEncoding_Term.Assume (_194_1624))
in (_194_1625)::[])))))))))
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

let valid = (let _194_1634 = (let _194_1633 = (let _194_1632 = (FStar_SMTEncoding_Util.mkApp ((eq2), ((a)::(x)::(y)::[])))
in (_194_1632)::[])
in (("Valid"), (_194_1633)))
in (FStar_SMTEncoding_Util.mkApp _194_1634))
in (let _194_1641 = (let _194_1640 = (let _194_1639 = (let _194_1638 = (let _194_1637 = (let _194_1636 = (let _194_1635 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in ((_194_1635), (valid)))
in (FStar_SMTEncoding_Util.mkIff _194_1636))
in ((((valid)::[])::[]), ((aa)::(xx)::(yy)::[]), (_194_1637)))
in (FStar_SMTEncoding_Util.mkForall _194_1638))
in ((_194_1639), (Some ("Eq2 interpretation")), (Some ("eq2-interp"))))
in FStar_SMTEncoding_Term.Assume (_194_1640))
in (_194_1641)::[])))))))))
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

let valid = (let _194_1650 = (let _194_1649 = (let _194_1648 = (FStar_SMTEncoding_Util.mkApp ((eq3), ((a)::(b)::(x)::(y)::[])))
in (_194_1648)::[])
in (("Valid"), (_194_1649)))
in (FStar_SMTEncoding_Util.mkApp _194_1650))
in (let _194_1657 = (let _194_1656 = (let _194_1655 = (let _194_1654 = (let _194_1653 = (let _194_1652 = (let _194_1651 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in ((_194_1651), (valid)))
in (FStar_SMTEncoding_Util.mkIff _194_1652))
in ((((valid)::[])::[]), ((aa)::(bb)::(xx)::(yy)::[]), (_194_1653)))
in (FStar_SMTEncoding_Util.mkForall _194_1654))
in ((_194_1655), (Some ("Eq3 interpretation")), (Some ("eq3-interp"))))
in FStar_SMTEncoding_Term.Assume (_194_1656))
in (_194_1657)::[])))))))))))
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

let valid = (let _194_1666 = (let _194_1665 = (let _194_1664 = (FStar_SMTEncoding_Util.mkApp ((imp), ((a)::(b)::[])))
in (_194_1664)::[])
in (("Valid"), (_194_1665)))
in (FStar_SMTEncoding_Util.mkApp _194_1666))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (let _194_1673 = (let _194_1672 = (let _194_1671 = (let _194_1670 = (let _194_1669 = (let _194_1668 = (let _194_1667 = (FStar_SMTEncoding_Util.mkImp ((valid_a), (valid_b)))
in ((_194_1667), (valid)))
in (FStar_SMTEncoding_Util.mkIff _194_1668))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_194_1669)))
in (FStar_SMTEncoding_Util.mkForall _194_1670))
in ((_194_1671), (Some ("==> interpretation")), (Some ("l_imp-interp"))))
in FStar_SMTEncoding_Term.Assume (_194_1672))
in (_194_1673)::[])))))))))
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

let valid = (let _194_1682 = (let _194_1681 = (let _194_1680 = (FStar_SMTEncoding_Util.mkApp ((iff), ((a)::(b)::[])))
in (_194_1680)::[])
in (("Valid"), (_194_1681)))
in (FStar_SMTEncoding_Util.mkApp _194_1682))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (let _194_1689 = (let _194_1688 = (let _194_1687 = (let _194_1686 = (let _194_1685 = (let _194_1684 = (let _194_1683 = (FStar_SMTEncoding_Util.mkIff ((valid_a), (valid_b)))
in ((_194_1683), (valid)))
in (FStar_SMTEncoding_Util.mkIff _194_1684))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_194_1685)))
in (FStar_SMTEncoding_Util.mkForall _194_1686))
in ((_194_1687), (Some ("<==> interpretation")), (Some ("l_iff-interp"))))
in FStar_SMTEncoding_Term.Assume (_194_1688))
in (_194_1689)::[])))))))))
in (

let mk_not_interp = (fun env l_not tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let valid = (let _194_1698 = (let _194_1697 = (let _194_1696 = (FStar_SMTEncoding_Util.mkApp ((l_not), ((a)::[])))
in (_194_1696)::[])
in (("Valid"), (_194_1697)))
in (FStar_SMTEncoding_Util.mkApp _194_1698))
in (

let not_valid_a = (let _194_1699 = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot _194_1699))
in (let _194_1704 = (let _194_1703 = (let _194_1702 = (let _194_1701 = (let _194_1700 = (FStar_SMTEncoding_Util.mkIff ((not_valid_a), (valid)))
in ((((valid)::[])::[]), ((aa)::[]), (_194_1700)))
in (FStar_SMTEncoding_Util.mkForall _194_1701))
in ((_194_1702), (Some ("not interpretation")), (Some ("l_not-interp"))))
in FStar_SMTEncoding_Term.Assume (_194_1703))
in (_194_1704)::[]))))))
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

let valid = (let _194_1713 = (let _194_1712 = (let _194_1711 = (FStar_SMTEncoding_Util.mkApp ((for_all), ((a)::(b)::[])))
in (_194_1711)::[])
in (("Valid"), (_194_1712)))
in (FStar_SMTEncoding_Util.mkApp _194_1713))
in (

let valid_b_x = (let _194_1716 = (let _194_1715 = (let _194_1714 = (FStar_SMTEncoding_Util.mk_ApplyTT b x)
in (_194_1714)::[])
in (("Valid"), (_194_1715)))
in (FStar_SMTEncoding_Util.mkApp _194_1716))
in (let _194_1730 = (let _194_1729 = (let _194_1728 = (let _194_1727 = (let _194_1726 = (let _194_1725 = (let _194_1724 = (let _194_1723 = (let _194_1722 = (let _194_1718 = (let _194_1717 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_194_1717)::[])
in (_194_1718)::[])
in (let _194_1721 = (let _194_1720 = (let _194_1719 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((_194_1719), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp _194_1720))
in ((_194_1722), ((xx)::[]), (_194_1721))))
in (FStar_SMTEncoding_Util.mkForall _194_1723))
in ((_194_1724), (valid)))
in (FStar_SMTEncoding_Util.mkIff _194_1725))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_194_1726)))
in (FStar_SMTEncoding_Util.mkForall _194_1727))
in ((_194_1728), (Some ("forall interpretation")), (Some ("forall-interp"))))
in FStar_SMTEncoding_Term.Assume (_194_1729))
in (_194_1730)::[]))))))))))
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

let valid = (let _194_1739 = (let _194_1738 = (let _194_1737 = (FStar_SMTEncoding_Util.mkApp ((for_some), ((a)::(b)::[])))
in (_194_1737)::[])
in (("Valid"), (_194_1738)))
in (FStar_SMTEncoding_Util.mkApp _194_1739))
in (

let valid_b_x = (let _194_1742 = (let _194_1741 = (let _194_1740 = (FStar_SMTEncoding_Util.mk_ApplyTT b x)
in (_194_1740)::[])
in (("Valid"), (_194_1741)))
in (FStar_SMTEncoding_Util.mkApp _194_1742))
in (let _194_1756 = (let _194_1755 = (let _194_1754 = (let _194_1753 = (let _194_1752 = (let _194_1751 = (let _194_1750 = (let _194_1749 = (let _194_1748 = (let _194_1744 = (let _194_1743 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_194_1743)::[])
in (_194_1744)::[])
in (let _194_1747 = (let _194_1746 = (let _194_1745 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((_194_1745), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp _194_1746))
in ((_194_1748), ((xx)::[]), (_194_1747))))
in (FStar_SMTEncoding_Util.mkExists _194_1749))
in ((_194_1750), (valid)))
in (FStar_SMTEncoding_Util.mkIff _194_1751))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_194_1752)))
in (FStar_SMTEncoding_Util.mkForall _194_1753))
in ((_194_1754), (Some ("exists interpretation")), (Some ("exists-interp"))))
in FStar_SMTEncoding_Term.Assume (_194_1755))
in (_194_1756)::[]))))))))))
in (

let mk_range_interp = (fun env range tt -> (

let range_ty = (FStar_SMTEncoding_Util.mkApp ((range), ([])))
in (let _194_1767 = (let _194_1766 = (let _194_1765 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_ty)
in (let _194_1764 = (let _194_1763 = (varops.mk_unique "typing_range_const")
in Some (_194_1763))
in ((_194_1765), (Some ("Range_const typing")), (_194_1764))))
in FStar_SMTEncoding_Term.Assume (_194_1766))
in (_194_1767)::[])))
in (

let prims = (((FStar_Syntax_Const.unit_lid), (mk_unit)))::(((FStar_Syntax_Const.bool_lid), (mk_bool)))::(((FStar_Syntax_Const.int_lid), (mk_int)))::(((FStar_Syntax_Const.string_lid), (mk_str)))::(((FStar_Syntax_Const.ref_lid), (mk_ref)))::(((FStar_Syntax_Const.true_lid), (mk_true_interp)))::(((FStar_Syntax_Const.false_lid), (mk_false_interp)))::(((FStar_Syntax_Const.and_lid), (mk_and_interp)))::(((FStar_Syntax_Const.or_lid), (mk_or_interp)))::(((FStar_Syntax_Const.eq2_lid), (mk_eq2_interp)))::(((FStar_Syntax_Const.eq3_lid), (mk_eq3_interp)))::(((FStar_Syntax_Const.imp_lid), (mk_imp_interp)))::(((FStar_Syntax_Const.iff_lid), (mk_iff_interp)))::(((FStar_Syntax_Const.not_lid), (mk_not_interp)))::(((FStar_Syntax_Const.forall_lid), (mk_forall_interp)))::(((FStar_Syntax_Const.exists_lid), (mk_exists_interp)))::(((FStar_Syntax_Const.range_lid), (mk_range_interp)))::[]
in (fun env t s tt -> (match ((FStar_Util.find_opt (fun _93_2085 -> (match (_93_2085) with
| (l, _93_2084) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_93_2088, f) -> begin
(f env s tt)
end))))))))))))))))))))))))


let encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let _93_2098 = (encode_function_type_as_formula None None t env)
in (match (_93_2098) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_SMTEncoding_Term.Assume (((form), (Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str))), (Some ((Prims.strcat "lemma_" lid.FStar_Ident.str))))))::[]))
end))))


let encode_free_var : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env fv tt t_norm quals -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if ((let _194_1984 = (FStar_Syntax_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _194_1984)) || (FStar_Syntax_Util.is_lemma t_norm)) then begin
(

let _93_2108 = (new_term_constant_and_tok_from_lid env lid)
in (match (_93_2108) with
| (vname, vtok, env) -> begin
(

let arg_sorts = (match ((let _194_1985 = (FStar_Syntax_Subst.compress t_norm)
in _194_1985.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _93_2111) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun _93_2114 -> FStar_SMTEncoding_Term.Term_sort)))
end
| _93_2117 -> begin
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

let _93_2124 = (prims.mk lid vname)
in (match (_93_2124) with
| (tok, definition) -> begin
(

let env = (push_free_var env lid vname (Some (tok)))
in ((definition), (env)))
end)))
end else begin
(

let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (

let _93_2134 = (

let _93_2129 = (curried_arrow_formals_comp t_norm)
in (match (_93_2129) with
| (args, comp) -> begin
if encode_non_total_function_typ then begin
(let _194_1987 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in ((args), (_194_1987)))
end else begin
((args), (((None), ((FStar_Syntax_Util.comp_result comp)))))
end
end))
in (match (_93_2134) with
| (formals, (pre_opt, res_t)) -> begin
(

let _93_2138 = (new_term_constant_and_tok_from_lid env lid)
in (match (_93_2138) with
| (vname, vtok, env) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
end
| _93_2141 -> begin
(FStar_SMTEncoding_Util.mkApp ((vtok), ([])))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun _93_15 -> (match (_93_15) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(

let _93_2157 = (FStar_Util.prefix vars)
in (match (_93_2157) with
| (_93_2152, (xxsym, _93_2155)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (let _194_2004 = (let _194_2003 = (let _194_2002 = (let _194_2001 = (let _194_2000 = (let _194_1999 = (let _194_1998 = (let _194_1997 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _194_1997))
in ((vapp), (_194_1998)))
in (FStar_SMTEncoding_Util.mkEq _194_1999))
in ((((vapp)::[])::[]), (vars), (_194_2000)))
in (FStar_SMTEncoding_Util.mkForall _194_2001))
in ((_194_2002), (Some ("Discriminator equation")), (Some ((Prims.strcat "disc_equation_" (escape d.FStar_Ident.str))))))
in FStar_SMTEncoding_Term.Assume (_194_2003))
in (_194_2004)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(

let _93_2169 = (FStar_Util.prefix vars)
in (match (_93_2169) with
| (_93_2164, (xxsym, _93_2167)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (

let tp_name = (mk_term_projector_name d f)
in (

let prim_app = (FStar_SMTEncoding_Util.mkApp ((tp_name), ((xx)::[])))
in (let _194_2009 = (let _194_2008 = (let _194_2007 = (let _194_2006 = (let _194_2005 = (FStar_SMTEncoding_Util.mkEq ((vapp), (prim_app)))
in ((((vapp)::[])::[]), (vars), (_194_2005)))
in (FStar_SMTEncoding_Util.mkForall _194_2006))
in ((_194_2007), (Some ("Projector equation")), (Some ((Prims.strcat "proj_equation_" tp_name)))))
in FStar_SMTEncoding_Term.Assume (_194_2008))
in (_194_2009)::[])))))
end))
end
| _93_2175 -> begin
[]
end)))))
in (

let _93_2182 = (encode_binders None formals env)
in (match (_93_2182) with
| (vars, guards, env', decls1, _93_2181) -> begin
(

let _93_2191 = (match (pre_opt) with
| None -> begin
(let _194_2010 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((_194_2010), (decls1)))
end
| Some (p) -> begin
(

let _93_2188 = (encode_formula p env')
in (match (_93_2188) with
| (g, ds) -> begin
(let _194_2011 = (FStar_SMTEncoding_Util.mk_and_l ((g)::guards))
in ((_194_2011), ((FStar_List.append decls1 ds))))
end))
end)
in (match (_93_2191) with
| (guard, decls1) -> begin
(

let vtok_app = (mk_Apply vtok_tm vars)
in (

let vapp = (let _194_2013 = (let _194_2012 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((vname), (_194_2012)))
in (FStar_SMTEncoding_Util.mkApp _194_2013))
in (

let _93_2215 = (

let vname_decl = (let _194_2016 = (let _194_2015 = (FStar_All.pipe_right formals (FStar_List.map (fun _93_2194 -> FStar_SMTEncoding_Term.Term_sort)))
in ((vname), (_194_2015), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (_194_2016))
in (

let _93_2202 = (

let env = (

let _93_2197 = env
in {bindings = _93_2197.bindings; depth = _93_2197.depth; tcenv = _93_2197.tcenv; warn = _93_2197.warn; cache = _93_2197.cache; nolabels = _93_2197.nolabels; use_zfuel_name = _93_2197.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in if (not ((head_normal env tt))) then begin
(encode_term_pred None tt env vtok_tm)
end else begin
(encode_term_pred None t_norm env vtok_tm)
end)
in (match (_93_2202) with
| (tok_typing, decls2) -> begin
(

let tok_typing = FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("function token typing")), (Some ((Prims.strcat "function_token_typing_" vname)))))
in (

let _93_2212 = (match (formals) with
| [] -> begin
(let _194_2020 = (let _194_2019 = (let _194_2018 = (FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left (fun _194_2017 -> Some (_194_2017)) _194_2018))
in (push_free_var env lid vname _194_2019))
in (((FStar_List.append decls2 ((tok_typing)::[]))), (_194_2020)))
end
| _93_2206 -> begin
(

let vtok_decl = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let vtok_fresh = (let _194_2021 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((vtok), (FStar_SMTEncoding_Term.Term_sort)) _194_2021))
in (

let name_tok_corr = (let _194_2025 = (let _194_2024 = (let _194_2023 = (let _194_2022 = (FStar_SMTEncoding_Util.mkEq ((vtok_app), (vapp)))
in ((((vtok_app)::[])::((vapp)::[])::[]), (vars), (_194_2022)))
in (FStar_SMTEncoding_Util.mkForall _194_2023))
in ((_194_2024), (Some ("Name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" vname)))))
in FStar_SMTEncoding_Term.Assume (_194_2025))
in (((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[]))), (env)))))
end)
in (match (_93_2212) with
| (tok_decl, env) -> begin
(((vname_decl)::tok_decl), (env))
end)))
end)))
in (match (_93_2215) with
| (decls2, env) -> begin
(

let _93_2223 = (

let res_t = (FStar_Syntax_Subst.compress res_t)
in (

let _93_2219 = (encode_term res_t env')
in (match (_93_2219) with
| (encoded_res_t, decls) -> begin
(let _194_2026 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in ((encoded_res_t), (_194_2026), (decls)))
end)))
in (match (_93_2223) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (let _194_2030 = (let _194_2029 = (let _194_2028 = (let _194_2027 = (FStar_SMTEncoding_Util.mkImp ((guard), (ty_pred)))
in ((((vapp)::[])::[]), (vars), (_194_2027)))
in (FStar_SMTEncoding_Util.mkForall _194_2028))
in ((_194_2029), (Some ("free var typing")), (Some ((Prims.strcat "typing_" vname)))))
in FStar_SMTEncoding_Term.Assume (_194_2030))
in (

let freshness = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New)) then begin
(let _194_2036 = (let _194_2033 = (let _194_2032 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (let _194_2031 = (varops.next_id ())
in ((vname), (_194_2032), (FStar_SMTEncoding_Term.Term_sort), (_194_2031))))
in (FStar_SMTEncoding_Term.fresh_constructor _194_2033))
in (let _194_2035 = (let _194_2034 = (pretype_axiom vapp vars)
in (_194_2034)::[])
in (_194_2036)::_194_2035))
end else begin
[]
end
in (

let g = (let _194_2041 = (let _194_2040 = (let _194_2039 = (let _194_2038 = (let _194_2037 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_194_2037)
in (FStar_List.append freshness _194_2038))
in (FStar_List.append decls3 _194_2039))
in (FStar_List.append decls2 _194_2040))
in (FStar_List.append decls1 _194_2041))
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

let _93_2234 = (encode_free_var env x t t_norm [])
in (match (_93_2234) with
| (decls, env) -> begin
(

let _93_2239 = (lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_93_2239) with
| (n, x', _93_2238) -> begin
((((n), (x'))), (decls), (env))
end))
end))
end
| Some (n, x, _93_2243) -> begin
((((n), (x))), ([]), (env))
end))


let encode_top_level_val : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env lid t quals -> (

let tt = (norm env t)
in (

let _93_2253 = (encode_free_var env lid t tt quals)
in (match (_93_2253) with
| (decls, env) -> begin
if (FStar_Syntax_Util.is_smt_lemma t) then begin
(let _194_2059 = (let _194_2058 = (encode_smt_lemma env lid tt)
in (FStar_List.append decls _194_2058))
in ((_194_2059), (env)))
end else begin
((decls), (env))
end
end))))


let encode_top_level_vals : env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _93_2259 lb -> (match (_93_2259) with
| (decls, env) -> begin
(

let _93_2263 = (let _194_2068 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env _194_2068 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (_93_2263) with
| (decls', env) -> begin
(((FStar_List.append decls decls')), (env))
end))
end)) (([]), (env)))))


let encode_top_level_let : env_t  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env _93_2267 quals -> (match (_93_2267) with
| (is_rec, bindings) -> begin
(

let eta_expand = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let _93_2277 = (FStar_Util.first_N nbinders formals)
in (match (_93_2277) with
| (formals, extra_formals) -> begin
(

let subst = (FStar_List.map2 (fun _93_2281 _93_2285 -> (match (((_93_2281), (_93_2285))) with
| ((formal, _93_2280), (binder, _93_2284)) -> begin
(let _194_2086 = (let _194_2085 = (FStar_Syntax_Syntax.bv_to_name binder)
in ((formal), (_194_2085)))
in FStar_Syntax_Syntax.NT (_194_2086))
end)) formals binders)
in (

let extra_formals = (let _194_2090 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun _93_2289 -> (match (_93_2289) with
| (x, i) -> begin
(let _194_2089 = (

let _93_2290 = x
in (let _194_2088 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _93_2290.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _93_2290.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _194_2088}))
in ((_194_2089), (i)))
end))))
in (FStar_All.pipe_right _194_2090 FStar_Syntax_Util.name_binders))
in (

let body = (let _194_2097 = (FStar_Syntax_Subst.compress body)
in (let _194_2096 = (let _194_2091 = (FStar_Syntax_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _194_2091))
in (let _194_2095 = (let _194_2094 = (let _194_2093 = (FStar_Syntax_Subst.subst subst t)
in _194_2093.FStar_Syntax_Syntax.n)
in (FStar_All.pipe_left (fun _194_2092 -> Some (_194_2092)) _194_2094))
in (FStar_Syntax_Syntax.extend_app_n _194_2097 _194_2096 _194_2095 body.FStar_Syntax_Syntax.pos))))
in (((FStar_List.append binders extra_formals)), (body)))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (

let rec aux = (fun norm t_norm -> (match ((let _194_2108 = (FStar_Syntax_Util.unascribe e)
in _194_2108.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, lopt) -> begin
(

let _93_2309 = (FStar_Syntax_Subst.open_term' binders body)
in (match (_93_2309) with
| (binders, body, opening) -> begin
(match ((let _194_2109 = (FStar_Syntax_Subst.compress t_norm)
in _194_2109.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let _93_2316 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_93_2316) with
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

let _93_2323 = (FStar_Util.first_N nformals binders)
in (match (_93_2323) with
| (bs0, rest) -> begin
(

let c = (

let subst = (FStar_List.map2 (fun _93_2327 _93_2331 -> (match (((_93_2327), (_93_2331))) with
| ((b, _93_2326), (x, _93_2330)) -> begin
(let _194_2113 = (let _194_2112 = (FStar_Syntax_Syntax.bv_to_name x)
in ((b), (_194_2112)))
in FStar_Syntax_Syntax.NT (_194_2113))
end)) bs0 formals)
in (FStar_Syntax_Subst.subst_comp subst c))
in (

let body = (FStar_Syntax_Util.abs rest body lopt)
in ((((bs0), (body), (bs0), ((FStar_Syntax_Util.comp_result c)))), (false))))
end)))
end else begin
if (nformals > nbinders) then begin
(

let _93_2337 = (eta_expand binders formals body tres)
in (match (_93_2337) with
| (binders, body) -> begin
((((binders), (body), (formals), (tres))), (false))
end))
end else begin
((((binders), (body), (formals), (tres))), (false))
end
end)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, _93_2340) -> begin
(let _194_2115 = (let _194_2114 = (aux norm x.FStar_Syntax_Syntax.sort)
in (Prims.fst _194_2114))
in ((_194_2115), (true)))
end
| _93_2344 when (not (norm)) -> begin
(

let t_norm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm)
in (aux true t_norm))
end
| _93_2347 -> begin
(let _194_2118 = (let _194_2117 = (FStar_Syntax_Print.term_to_string e)
in (let _194_2116 = (FStar_Syntax_Print.term_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str _194_2117 _194_2116)))
in (failwith _194_2118))
end)
end))
end
| _93_2349 -> begin
(match ((let _194_2119 = (FStar_Syntax_Subst.compress t_norm)
in _194_2119.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let _93_2356 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_93_2356) with
| (formals, c) -> begin
(

let tres = (FStar_Syntax_Util.comp_result c)
in (

let _93_2360 = (eta_expand [] formals e tres)
in (match (_93_2360) with
| (binders, body) -> begin
((((binders), (body), (formals), (tres))), (false))
end)))
end))
end
| _93_2362 -> begin
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

let _93_2390 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _93_2377 lb -> (match (_93_2377) with
| (toks, typs, decls, env) -> begin
(

let _93_2379 = if (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) then begin
(Prims.raise Let_rec_unencodeable)
end else begin
()
end
in (

let t_norm = (whnf env lb.FStar_Syntax_Syntax.lbtyp)
in (

let _93_2385 = (let _194_2124 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env _194_2124 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (_93_2385) with
| (tok, decl, env) -> begin
(let _194_2127 = (let _194_2126 = (let _194_2125 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in ((_194_2125), (tok)))
in (_194_2126)::toks)
in ((_194_2127), ((t_norm)::typs), ((decl)::decls), (env)))
end))))
end)) (([]), ([]), ([]), (env))))
in (match (_93_2390) with
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
| _93_2401 -> begin
if curry then begin
(match (ftok) with
| Some (ftok) -> begin
(mk_Apply ftok vars)
end
| None -> begin
(let _194_2136 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply _194_2136 vars))
end)
end else begin
(let _194_2138 = (let _194_2137 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (_194_2137)))
in (FStar_SMTEncoding_Util.mkApp _194_2138))
end
end))
in if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _93_16 -> (match (_93_16) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| _93_2408 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> (let _194_2141 = (FStar_Syntax_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _194_2141)))))) then begin
((decls), (env))
end else begin
if (not (is_rec)) then begin
(match (((bindings), (typs), (toks))) with
| (({FStar_Syntax_Syntax.lbname = _93_2418; FStar_Syntax_Syntax.lbunivs = _93_2416; FStar_Syntax_Syntax.lbtyp = _93_2414; FStar_Syntax_Syntax.lbeff = _93_2412; FStar_Syntax_Syntax.lbdef = e})::[], (t_norm)::[], ((flid_fv, (f, ftok)))::[]) -> begin
(

let e = (FStar_Syntax_Subst.compress e)
in (

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let _93_2440 = (destruct_bound_function flid t_norm e)
in (match (_93_2440) with
| ((binders, body, _93_2435, _93_2437), curry) -> begin
(

let _93_2447 = (encode_binders None binders env)
in (match (_93_2447) with
| (vars, guards, env', binder_decls, _93_2446) -> begin
(

let app = (mk_app curry f ftok vars)
in (

let _93_2453 = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic)) then begin
(let _194_2143 = (FStar_SMTEncoding_Term.mk_Valid app)
in (let _194_2142 = (encode_formula body env')
in ((_194_2143), (_194_2142))))
end else begin
(let _194_2144 = (encode_term body env')
in ((app), (_194_2144)))
end
in (match (_93_2453) with
| (app, (body, decls2)) -> begin
(

let eqn = (let _194_2150 = (let _194_2149 = (let _194_2146 = (let _194_2145 = (FStar_SMTEncoding_Util.mkEq ((app), (body)))
in ((((app)::[])::[]), (vars), (_194_2145)))
in (FStar_SMTEncoding_Util.mkForall _194_2146))
in (let _194_2148 = (let _194_2147 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (_194_2147))
in ((_194_2149), (_194_2148), (Some ((Prims.strcat "equation_" f))))))
in FStar_SMTEncoding_Term.Assume (_194_2150))
in (let _194_2155 = (let _194_2154 = (let _194_2153 = (let _194_2152 = (let _194_2151 = (primitive_type_axioms env.tcenv flid f app)
in (FStar_List.append ((eqn)::[]) _194_2151))
in (FStar_List.append decls2 _194_2152))
in (FStar_List.append binder_decls _194_2153))
in (FStar_List.append decls _194_2154))
in ((_194_2155), (env))))
end)))
end))
end))))
end
| _93_2456 -> begin
(failwith "Impossible")
end)
end else begin
(

let fuel = (let _194_2156 = (varops.fresh "fuel")
in ((_194_2156), (FStar_SMTEncoding_Term.Fuel_sort)))
in (

let fuel_tm = (FStar_SMTEncoding_Util.mkFreeV fuel)
in (

let env0 = env
in (

let _93_2474 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _93_2462 _93_2467 -> (match (((_93_2462), (_93_2467))) with
| ((gtoks, env), (flid_fv, (f, ftok))) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let g = (let _194_2159 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented")
in (varops.new_fvar _194_2159))
in (

let gtok = (let _194_2160 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented_token")
in (varops.new_fvar _194_2160))
in (

let env = (let _194_2163 = (let _194_2162 = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::[])))
in (FStar_All.pipe_left (fun _194_2161 -> Some (_194_2161)) _194_2162))
in (push_free_var env flid gtok _194_2163))
in (((((flid), (f), (ftok), (g), (gtok)))::gtoks), (env))))))
end)) (([]), (env))))
in (match (_93_2474) with
| (gtoks, env) -> begin
(

let gtoks = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env0 _93_2483 t_norm _93_2494 -> (match (((_93_2483), (_93_2494))) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = _93_2493; FStar_Syntax_Syntax.lbunivs = _93_2491; FStar_Syntax_Syntax.lbtyp = _93_2489; FStar_Syntax_Syntax.lbeff = _93_2487; FStar_Syntax_Syntax.lbdef = e}) -> begin
(

let _93_2501 = (destruct_bound_function flid t_norm e)
in (match (_93_2501) with
| ((binders, body, formals, tres), curry) -> begin
(

let _93_2502 = if curry then begin
(failwith "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type")
end else begin
()
end
in (

let _93_2510 = (encode_binders None binders env)
in (match (_93_2510) with
| (vars, guards, env', binder_decls, _93_2509) -> begin
(

let decl_g = (let _194_2174 = (let _194_2173 = (let _194_2172 = (FStar_List.map Prims.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::_194_2172)
in ((g), (_194_2173), (FStar_SMTEncoding_Term.Term_sort), (Some ("Fuel-instrumented function name"))))
in FStar_SMTEncoding_Term.DeclFun (_194_2174))
in (

let env0 = (push_zfuel_name env0 flid g)
in (

let decl_g_tok = FStar_SMTEncoding_Term.DeclFun (((gtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Token for fuel-instrumented partial applications"))))
in (

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let app = (let _194_2176 = (let _194_2175 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (_194_2175)))
in (FStar_SMTEncoding_Util.mkApp _194_2176))
in (

let gsapp = (let _194_2179 = (let _194_2178 = (let _194_2177 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (_194_2177)::vars_tm)
in ((g), (_194_2178)))
in (FStar_SMTEncoding_Util.mkApp _194_2179))
in (

let gmax = (let _194_2182 = (let _194_2181 = (let _194_2180 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (_194_2180)::vars_tm)
in ((g), (_194_2181)))
in (FStar_SMTEncoding_Util.mkApp _194_2182))
in (

let _93_2520 = (encode_term body env')
in (match (_93_2520) with
| (body_tm, decls2) -> begin
(

let eqn_g = (let _194_2188 = (let _194_2187 = (let _194_2184 = (let _194_2183 = (FStar_SMTEncoding_Util.mkEq ((gsapp), (body_tm)))
in ((((gsapp)::[])::[]), (Some ((Prims.parse_int "0"))), ((fuel)::vars), (_194_2183)))
in (FStar_SMTEncoding_Util.mkForall' _194_2184))
in (let _194_2186 = (let _194_2185 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (_194_2185))
in ((_194_2187), (_194_2186), (Some ((Prims.strcat "equation_with_fuel_" g))))))
in FStar_SMTEncoding_Term.Assume (_194_2188))
in (

let eqn_f = (let _194_2192 = (let _194_2191 = (let _194_2190 = (let _194_2189 = (FStar_SMTEncoding_Util.mkEq ((app), (gmax)))
in ((((app)::[])::[]), (vars), (_194_2189)))
in (FStar_SMTEncoding_Util.mkForall _194_2190))
in ((_194_2191), (Some ("Correspondence of recursive function to instrumented version")), (Some ((Prims.strcat "fuel_correspondence_" g)))))
in FStar_SMTEncoding_Term.Assume (_194_2192))
in (

let eqn_g' = (let _194_2201 = (let _194_2200 = (let _194_2199 = (let _194_2198 = (let _194_2197 = (let _194_2196 = (let _194_2195 = (let _194_2194 = (let _194_2193 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "0"))
in (_194_2193)::vars_tm)
in ((g), (_194_2194)))
in (FStar_SMTEncoding_Util.mkApp _194_2195))
in ((gsapp), (_194_2196)))
in (FStar_SMTEncoding_Util.mkEq _194_2197))
in ((((gsapp)::[])::[]), ((fuel)::vars), (_194_2198)))
in (FStar_SMTEncoding_Util.mkForall _194_2199))
in ((_194_2200), (Some ("Fuel irrelevance")), (Some ((Prims.strcat "fuel_irrelevance_" g)))))
in FStar_SMTEncoding_Term.Assume (_194_2201))
in (

let _93_2543 = (

let _93_2530 = (encode_binders None formals env0)
in (match (_93_2530) with
| (vars, v_guards, env, binder_decls, _93_2529) -> begin
(

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let gapp = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::vars_tm)))
in (

let tok_corr = (

let tok_app = (let _194_2202 = (FStar_SMTEncoding_Util.mkFreeV ((gtok), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply _194_2202 ((fuel)::vars)))
in (let _194_2206 = (let _194_2205 = (let _194_2204 = (let _194_2203 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (gapp)))
in ((((tok_app)::[])::[]), ((fuel)::vars), (_194_2203)))
in (FStar_SMTEncoding_Util.mkForall _194_2204))
in ((_194_2205), (Some ("Fuel token correspondence")), (Some ((Prims.strcat "fuel_token_correspondence_" gtok)))))
in FStar_SMTEncoding_Term.Assume (_194_2206)))
in (

let _93_2540 = (

let _93_2537 = (encode_term_pred None tres env gapp)
in (match (_93_2537) with
| (g_typing, d3) -> begin
(let _194_2214 = (let _194_2213 = (let _194_2212 = (let _194_2211 = (let _194_2210 = (let _194_2209 = (let _194_2208 = (let _194_2207 = (FStar_SMTEncoding_Util.mk_and_l v_guards)
in ((_194_2207), (g_typing)))
in (FStar_SMTEncoding_Util.mkImp _194_2208))
in ((((gapp)::[])::[]), ((fuel)::vars), (_194_2209)))
in (FStar_SMTEncoding_Util.mkForall _194_2210))
in ((_194_2211), (Some ("Typing correspondence of token to term")), (Some ((Prims.strcat "token_correspondence_" g)))))
in FStar_SMTEncoding_Term.Assume (_194_2212))
in (_194_2213)::[])
in ((d3), (_194_2214)))
end))
in (match (_93_2540) with
| (aux_decls, typing_corr) -> begin
(((FStar_List.append binder_decls aux_decls)), ((FStar_List.append typing_corr ((tok_corr)::[]))))
end)))))
end))
in (match (_93_2543) with
| (aux_decls, g_typing) -> begin
(((FStar_List.append binder_decls (FStar_List.append decls2 (FStar_List.append aux_decls ((decl_g)::(decl_g_tok)::[]))))), ((FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing)), (env0))
end)))))
end)))))))))
end)))
end))
end))
in (

let _93_2559 = (let _194_2217 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _93_2547 _93_2551 -> (match (((_93_2547), (_93_2551))) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(

let _93_2555 = (encode_one_binding env0 gtok ty bs)
in (match (_93_2555) with
| (decls', eqns', env0) -> begin
(((decls')::decls), ((FStar_List.append eqns' eqns)), (env0))
end))
end)) (((decls)::[]), ([]), (env0)) _194_2217))
in (match (_93_2559) with
| (decls, eqns, env0) -> begin
(

let _93_2568 = (let _194_2219 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _194_2219 (FStar_List.partition (fun _93_17 -> (match (_93_17) with
| FStar_SMTEncoding_Term.DeclFun (_93_2562) -> begin
true
end
| _93_2565 -> begin
false
end)))))
in (match (_93_2568) with
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

let msg = (let _194_2222 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _194_2222 (FStar_String.concat " and ")))
in (

let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in (((decl)::[]), (env))))
end))
end))


let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let _93_2572 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _194_2231 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _194_2231))
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

let _93_2580 = (encode_sigelt' env se)
in (match (_93_2580) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _194_2234 = (let _194_2233 = (let _194_2232 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (_194_2232))
in (_194_2233)::[])
in ((_194_2234), (e)))
end
| _93_2583 -> begin
(let _194_2241 = (let _194_2240 = (let _194_2236 = (let _194_2235 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_194_2235))
in (_194_2236)::g)
in (let _194_2239 = (let _194_2238 = (let _194_2237 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_194_2237))
in (_194_2238)::[])
in (FStar_List.append _194_2240 _194_2239)))
in ((_194_2241), (e)))
end)
end)))))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let should_skip = (fun l -> false)
in (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_93_2589) -> begin
(failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _93_2605) -> begin
if (let _194_2246 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right _194_2246 Prims.op_Negation)) then begin
(([]), (env))
end else begin
(

let close_effect_params = (fun tm -> (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
tm
end
| _93_2612 -> begin
(let _194_2252 = (let _194_2251 = (let _194_2250 = (FStar_All.pipe_left (fun _194_2249 -> Some (_194_2249)) (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[])))))
in ((ed.FStar_Syntax_Syntax.binders), (tm), (_194_2250)))
in FStar_Syntax_Syntax.Tm_abs (_194_2251))
in (FStar_Syntax_Syntax.mk _194_2252 None tm.FStar_Syntax_Syntax.pos))
end))
in (

let encode_action = (fun env a -> (

let _93_2619 = (new_term_constant_and_tok_from_lid env a.FStar_Syntax_Syntax.action_name)
in (match (_93_2619) with
| (aname, atok, env) -> begin
(

let _93_2623 = (FStar_Syntax_Util.arrow_formals_comp a.FStar_Syntax_Syntax.action_typ)
in (match (_93_2623) with
| (formals, _93_2622) -> begin
(

let _93_2626 = (let _194_2257 = (close_effect_params a.FStar_Syntax_Syntax.action_defn)
in (encode_term _194_2257 env))
in (match (_93_2626) with
| (tm, decls) -> begin
(

let a_decls = (let _194_2261 = (let _194_2260 = (let _194_2259 = (FStar_All.pipe_right formals (FStar_List.map (fun _93_2627 -> FStar_SMTEncoding_Term.Term_sort)))
in ((aname), (_194_2259), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action"))))
in FStar_SMTEncoding_Term.DeclFun (_194_2260))
in (_194_2261)::(FStar_SMTEncoding_Term.DeclFun (((atok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action token")))))::[])
in (

let _93_2641 = (let _194_2263 = (FStar_All.pipe_right formals (FStar_List.map (fun _93_2633 -> (match (_93_2633) with
| (bv, _93_2632) -> begin
(

let _93_2638 = (gen_term_var env bv)
in (match (_93_2638) with
| (xxsym, xx, _93_2637) -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (xx))
end))
end))))
in (FStar_All.pipe_right _194_2263 FStar_List.split))
in (match (_93_2641) with
| (xs_sorts, xs) -> begin
(

let app = (let _194_2266 = (let _194_2265 = (let _194_2264 = (FStar_SMTEncoding_Util.mkApp ((aname), (xs)))
in (_194_2264)::[])
in (("Reify"), (_194_2265)))
in (FStar_SMTEncoding_Util.mkApp _194_2266))
in (

let a_eq = (let _194_2272 = (let _194_2271 = (let _194_2270 = (let _194_2269 = (let _194_2268 = (let _194_2267 = (mk_Apply tm xs_sorts)
in ((app), (_194_2267)))
in (FStar_SMTEncoding_Util.mkEq _194_2268))
in ((((app)::[])::[]), (xs_sorts), (_194_2269)))
in (FStar_SMTEncoding_Util.mkForall _194_2270))
in ((_194_2271), (Some ("Action equality")), (Some ((Prims.strcat aname "_equality")))))
in FStar_SMTEncoding_Term.Assume (_194_2272))
in (

let tok_correspondence = (

let tok_term = (FStar_SMTEncoding_Util.mkFreeV ((atok), (FStar_SMTEncoding_Term.Term_sort)))
in (

let tok_app = (mk_Apply tok_term xs_sorts)
in (let _194_2276 = (let _194_2275 = (let _194_2274 = (let _194_2273 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (app)))
in ((((tok_app)::[])::[]), (xs_sorts), (_194_2273)))
in (FStar_SMTEncoding_Util.mkForall _194_2274))
in ((_194_2275), (Some ("Action token correspondence")), (Some ((Prims.strcat aname "_token_correspondence")))))
in FStar_SMTEncoding_Term.Assume (_194_2276))))
in ((env), ((FStar_List.append decls (FStar_List.append a_decls ((a_eq)::(tok_correspondence)::[]))))))))
end)))
end))
end))
end)))
in (

let _93_2649 = (FStar_Util.fold_map encode_action env ed.FStar_Syntax_Syntax.actions)
in (match (_93_2649) with
| (env, decls2) -> begin
(((FStar_List.flatten decls2)), (env))
end))))
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _93_2652, _93_2654, _93_2656, _93_2658) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid) -> begin
(

let _93_2664 = (new_term_constant_and_tok_from_lid env lid)
in (match (_93_2664) with
| (tname, ttok, env) -> begin
(([]), (env))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _93_2667, t, quals, _93_2671) -> begin
(

let will_encode_definition = (not ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _93_18 -> (match (_93_18) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Irreducible) -> begin
true
end
| _93_2684 -> begin
false
end))))))
in if will_encode_definition then begin
(([]), (env))
end else begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (

let _93_2689 = (encode_top_level_val env fv t quals)
in (match (_93_2689) with
| (decls, env) -> begin
(

let tname = lid.FStar_Ident.str
in (

let tsym = (FStar_SMTEncoding_Util.mkFreeV ((tname), (FStar_SMTEncoding_Term.Term_sort)))
in (let _194_2279 = (let _194_2278 = (primitive_type_axioms env.tcenv lid tname tsym)
in (FStar_List.append decls _194_2278))
in ((_194_2279), (env)))))
end)))
end)
end
| FStar_Syntax_Syntax.Sig_assume (l, f, _93_2695, _93_2697) -> begin
(

let _93_2702 = (encode_formula f env)
in (match (_93_2702) with
| (f, decls) -> begin
(

let g = (let _194_2286 = (let _194_2285 = (let _194_2284 = (let _194_2281 = (let _194_2280 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" _194_2280))
in Some (_194_2281))
in (let _194_2283 = (let _194_2282 = (varops.mk_unique (Prims.strcat "assumption_" l.FStar_Ident.str))
in Some (_194_2282))
in ((f), (_194_2284), (_194_2283))))
in FStar_SMTEncoding_Term.Assume (_194_2285))
in (_194_2286)::[])
in (((FStar_List.append decls g)), (env)))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _93_2707, quals, _93_2710) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) -> begin
(

let _93_2722 = (FStar_Util.fold_map (fun env lb -> (

let lid = (let _194_2290 = (let _194_2289 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _194_2289.FStar_Syntax_Syntax.fv_name)
in _194_2290.FStar_Syntax_Syntax.v)
in if (let _194_2291 = (FStar_TypeChecker_Env.try_lookup_val_decl env.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone _194_2291)) then begin
(

let val_decl = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), (r)))
in (

let _93_2719 = (encode_sigelt' env val_decl)
in (match (_93_2719) with
| (decls, env) -> begin
((env), (decls))
end)))
end else begin
((env), ([]))
end)) env (Prims.snd lbs))
in (match (_93_2722) with
| (env, decls) -> begin
(((FStar_List.flatten decls)), (env))
end))
end
| FStar_Syntax_Syntax.Sig_let ((_93_2724, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t); FStar_Syntax_Syntax.lbunivs = _93_2732; FStar_Syntax_Syntax.lbtyp = _93_2730; FStar_Syntax_Syntax.lbeff = _93_2728; FStar_Syntax_Syntax.lbdef = _93_2726})::[]), _93_2739, _93_2741, _93_2743, _93_2745) when (FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Syntax_Const.b2t_lid) -> begin
(

let _93_2751 = (new_term_constant_and_tok_from_lid env b2t.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_93_2751) with
| (tname, ttok, env) -> begin
(

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let valid_b2t_x = (let _194_2294 = (let _194_2293 = (let _194_2292 = (FStar_SMTEncoding_Util.mkApp (("Prims.b2t"), ((x)::[])))
in (_194_2292)::[])
in (("Valid"), (_194_2293)))
in (FStar_SMTEncoding_Util.mkApp _194_2294))
in (

let decls = (let _194_2302 = (let _194_2301 = (let _194_2300 = (let _194_2299 = (let _194_2298 = (let _194_2297 = (let _194_2296 = (let _194_2295 = (FStar_SMTEncoding_Util.mkApp (("BoxBool_proj_0"), ((x)::[])))
in ((valid_b2t_x), (_194_2295)))
in (FStar_SMTEncoding_Util.mkEq _194_2296))
in ((((valid_b2t_x)::[])::[]), ((xx)::[]), (_194_2297)))
in (FStar_SMTEncoding_Util.mkForall _194_2298))
in ((_194_2299), (Some ("b2t def")), (Some ("b2t_def"))))
in FStar_SMTEncoding_Term.Assume (_194_2300))
in (_194_2301)::[])
in (FStar_SMTEncoding_Term.DeclFun (((tname), ((FStar_SMTEncoding_Term.Term_sort)::[]), (FStar_SMTEncoding_Term.Term_sort), (None))))::_194_2302)
in ((decls), (env))))))
end))
end
| FStar_Syntax_Syntax.Sig_let (_93_2757, _93_2759, _93_2761, quals, _93_2764) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _93_19 -> (match (_93_19) with
| FStar_Syntax_Syntax.Discriminator (_93_2769) -> begin
true
end
| _93_2772 -> begin
false
end)))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let (_93_2774, _93_2776, lids, quals, _93_2780) when ((FStar_All.pipe_right lids (FStar_Util.for_some (fun l -> ((let _194_2305 = (FStar_List.hd l.FStar_Ident.ns)
in _194_2305.FStar_Ident.idText) = "Prims")))) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun _93_20 -> (match (_93_20) with
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
true
end
| _93_2787 -> begin
false
end))))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _93_2793, _93_2795, quals, _93_2798) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _93_21 -> (match (_93_21) with
| FStar_Syntax_Syntax.Projector (_93_2803) -> begin
true
end
| _93_2806 -> begin
false
end)))) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((try_lookup_free_var env l)) with
| Some (_93_2810) -> begin
(([]), (env))
end
| None -> begin
(

let se = FStar_Syntax_Syntax.Sig_declare_typ (((l), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), ((FStar_Ident.range_of_lid l))))
in (encode_sigelt env se))
end)))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _93_2819, _93_2821, quals, _93_2824) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) -> begin
(match ((let _194_2308 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef)
in _194_2308.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, _93_2830) -> begin
(

let body = (FStar_Syntax_Util.mk_reify body)
in (

let tm = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None)))) None lb.FStar_Syntax_Syntax.lbdef.FStar_Syntax_Syntax.pos)
in (

let tm' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env.tcenv tm)
in (

let lb_typ = (

let _93_2838 = (FStar_Syntax_Util.arrow_formals_comp lb.FStar_Syntax_Syntax.lbtyp)
in (match (_93_2838) with
| (formals, comp) -> begin
(

let reified_typ = (FStar_TypeChecker_Util.reify_comp (

let _93_2839 = env.tcenv
in {FStar_TypeChecker_Env.solver = _93_2839.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _93_2839.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _93_2839.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _93_2839.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _93_2839.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _93_2839.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _93_2839.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _93_2839.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _93_2839.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _93_2839.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _93_2839.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _93_2839.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _93_2839.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _93_2839.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _93_2839.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _93_2839.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _93_2839.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _93_2839.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _93_2839.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _93_2839.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _93_2839.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _93_2839.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _93_2839.FStar_TypeChecker_Env.qname_and_index}) (FStar_Syntax_Util.lcomp_of_comp comp) FStar_Syntax_Syntax.U_unknown)
in (let _194_2309 = (FStar_Syntax_Syntax.mk_Total reified_typ)
in (FStar_Syntax_Util.arrow formals _194_2309)))
end))
in (

let lb = (

let _93_2843 = lb
in {FStar_Syntax_Syntax.lbname = _93_2843.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _93_2843.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lb_typ; FStar_Syntax_Syntax.lbeff = _93_2843.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = tm'})
in (encode_top_level_let env ((false), ((lb)::[])) quals))))))
end
| _93_2847 -> begin
(([]), (env))
end)
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), _93_2852, _93_2854, quals, _93_2857) -> begin
(encode_top_level_let env ((is_rec), (bindings)) quals)
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _93_2862, _93_2864, _93_2866) -> begin
(

let _93_2871 = (encode_signature env ses)
in (match (_93_2871) with
| (g, env) -> begin
(

let _93_2885 = (FStar_All.pipe_right g (FStar_List.partition (fun _93_22 -> (match (_93_22) with
| FStar_SMTEncoding_Term.Assume (_93_2874, Some ("inversion axiom"), _93_2878) -> begin
false
end
| _93_2882 -> begin
true
end))))
in (match (_93_2885) with
| (g', inversions) -> begin
(

let _93_2894 = (FStar_All.pipe_right g' (FStar_List.partition (fun _93_23 -> (match (_93_23) with
| FStar_SMTEncoding_Term.DeclFun (_93_2888) -> begin
true
end
| _93_2891 -> begin
false
end))))
in (match (_93_2894) with
| (decls, rest) -> begin
(((FStar_List.append decls (FStar_List.append rest inversions))), (env))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, _93_2897, tps, k, _93_2901, datas, quals, _93_2905) -> begin
(

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _93_24 -> (match (_93_24) with
| (FStar_Syntax_Syntax.Logic) | (FStar_Syntax_Syntax.Assumption) -> begin
true
end
| _93_2912 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(

let _93_2924 = c
in (match (_93_2924) with
| (name, args, _93_2919, _93_2921, _93_2923) -> begin
(let _194_2317 = (let _194_2316 = (let _194_2315 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in ((name), (_194_2315), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (_194_2316))
in (_194_2317)::[])
end))
end else begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end)
in (

let inversion_axioms = (fun tapp vars -> if (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _194_2323 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right _194_2323 FStar_Option.isNone))))) then begin
[]
end else begin
(

let _93_2931 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_93_2931) with
| (xxsym, xx) -> begin
(

let _93_2967 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _93_2934 l -> (match (_93_2934) with
| (out, decls) -> begin
(

let _93_2939 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (_93_2939) with
| (_93_2937, data_t) -> begin
(

let _93_2942 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (_93_2942) with
| (args, res) -> begin
(

let indices = (match ((let _194_2326 = (FStar_Syntax_Subst.compress res)
in _194_2326.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_93_2944, indices) -> begin
indices
end
| _93_2949 -> begin
[]
end)
in (

let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env _93_2955 -> (match (_93_2955) with
| (x, _93_2954) -> begin
(let _194_2331 = (let _194_2330 = (let _194_2329 = (mk_term_projector_name l x)
in ((_194_2329), ((xx)::[])))
in (FStar_SMTEncoding_Util.mkApp _194_2330))
in (push_term_var env x _194_2331))
end)) env))
in (

let _93_2959 = (encode_args indices env)
in (match (_93_2959) with
| (indices, decls') -> begin
(

let _93_2960 = if ((FStar_List.length indices) <> (FStar_List.length vars)) then begin
(failwith "Impossible")
end else begin
()
end
in (

let eqs = (let _194_2336 = (FStar_List.map2 (fun v a -> (let _194_2335 = (let _194_2334 = (FStar_SMTEncoding_Util.mkFreeV v)
in ((_194_2334), (a)))
in (FStar_SMTEncoding_Util.mkEq _194_2335))) vars indices)
in (FStar_All.pipe_right _194_2336 FStar_SMTEncoding_Util.mk_and_l))
in (let _194_2341 = (let _194_2340 = (let _194_2339 = (let _194_2338 = (let _194_2337 = (mk_data_tester env l xx)
in ((_194_2337), (eqs)))
in (FStar_SMTEncoding_Util.mkAnd _194_2338))
in ((out), (_194_2339)))
in (FStar_SMTEncoding_Util.mkOr _194_2340))
in ((_194_2341), ((FStar_List.append decls decls'))))))
end))))
end))
end))
end)) ((FStar_SMTEncoding_Util.mkFalse), ([]))))
in (match (_93_2967) with
| (data_ax, decls) -> begin
(

let _93_2970 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_93_2970) with
| (ffsym, ff) -> begin
(

let fuel_guarded_inversion = (

let xx_has_type_sfuel = if ((FStar_List.length datas) > (Prims.parse_int "1")) then begin
(let _194_2342 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((ff)::[])))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel _194_2342 xx tapp))
end else begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end
in (let _194_2349 = (let _194_2348 = (let _194_2345 = (let _194_2344 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (let _194_2343 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_sfuel), (data_ax)))
in ((((xx_has_type_sfuel)::[])::[]), (_194_2344), (_194_2343))))
in (FStar_SMTEncoding_Util.mkForall _194_2345))
in (let _194_2347 = (let _194_2346 = (varops.mk_unique (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str))
in Some (_194_2346))
in ((_194_2348), (Some ("inversion axiom")), (_194_2347))))
in FStar_SMTEncoding_Term.Assume (_194_2349)))
in (

let pattern_guarded_inversion = if ((contains_name env "Prims.inversion") && ((FStar_List.length datas) > (Prims.parse_int "1"))) then begin
(

let xx_has_type_fuel = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let pattern_guard = (FStar_SMTEncoding_Util.mkApp (("Prims.inversion"), ((tapp)::[])))
in (let _194_2357 = (let _194_2356 = (let _194_2355 = (let _194_2352 = (let _194_2351 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (let _194_2350 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_fuel), (data_ax)))
in ((((xx_has_type_fuel)::(pattern_guard)::[])::[]), (_194_2351), (_194_2350))))
in (FStar_SMTEncoding_Util.mkForall _194_2352))
in (let _194_2354 = (let _194_2353 = (varops.mk_unique (Prims.strcat "pattern_guarded_inversion_" t.FStar_Ident.str))
in Some (_194_2353))
in ((_194_2355), (Some ("inversion axiom")), (_194_2354))))
in FStar_SMTEncoding_Term.Assume (_194_2356))
in (_194_2357)::[])))
end else begin
[]
end
in (FStar_List.append decls (FStar_List.append ((fuel_guarded_inversion)::[]) pattern_guarded_inversion))))
end))
end))
end))
end)
in (

let _93_2984 = (match ((let _194_2358 = (FStar_Syntax_Subst.compress k)
in _194_2358.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
(((FStar_List.append tps formals)), ((FStar_Syntax_Util.comp_result kres)))
end
| _93_2981 -> begin
((tps), (k))
end)
in (match (_93_2984) with
| (formals, res) -> begin
(

let _93_2987 = (FStar_Syntax_Subst.open_term formals res)
in (match (_93_2987) with
| (formals, res) -> begin
(

let _93_2994 = (encode_binders None formals env)
in (match (_93_2994) with
| (vars, guards, env', binder_decls, _93_2993) -> begin
(

let _93_2998 = (new_term_constant_and_tok_from_lid env t)
in (match (_93_2998) with
| (tname, ttok, env) -> begin
(

let ttok_tm = (FStar_SMTEncoding_Util.mkApp ((ttok), ([])))
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let tapp = (let _194_2360 = (let _194_2359 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((tname), (_194_2359)))
in (FStar_SMTEncoding_Util.mkApp _194_2360))
in (

let _93_3019 = (

let tname_decl = (let _194_2364 = (let _194_2363 = (FStar_All.pipe_right vars (FStar_List.map (fun _93_3004 -> (match (_93_3004) with
| (n, s) -> begin
(((Prims.strcat tname n)), (s))
end))))
in (let _194_2362 = (varops.next_id ())
in ((tname), (_194_2363), (FStar_SMTEncoding_Term.Term_sort), (_194_2362), (false))))
in (constructor_or_logic_type_decl _194_2364))
in (

let _93_3016 = (match (vars) with
| [] -> begin
(let _194_2368 = (let _194_2367 = (let _194_2366 = (FStar_SMTEncoding_Util.mkApp ((tname), ([])))
in (FStar_All.pipe_left (fun _194_2365 -> Some (_194_2365)) _194_2366))
in (push_free_var env t tname _194_2367))
in (([]), (_194_2368)))
end
| _93_3008 -> begin
(

let ttok_decl = FStar_SMTEncoding_Term.DeclFun (((ttok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("token"))))
in (

let ttok_fresh = (let _194_2369 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ttok), (FStar_SMTEncoding_Term.Term_sort)) _194_2369))
in (

let ttok_app = (mk_Apply ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (let _194_2373 = (let _194_2372 = (let _194_2371 = (let _194_2370 = (FStar_SMTEncoding_Util.mkEq ((ttok_app), (tapp)))
in ((pats), (None), (vars), (_194_2370)))
in (FStar_SMTEncoding_Util.mkForall' _194_2371))
in ((_194_2372), (Some ("name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" ttok)))))
in FStar_SMTEncoding_Term.Assume (_194_2373))
in (((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[]), (env)))))))
end)
in (match (_93_3016) with
| (tok_decls, env) -> begin
(((FStar_List.append tname_decl tok_decls)), (env))
end)))
in (match (_93_3019) with
| (decls, env) -> begin
(

let kindingAx = (

let _93_3022 = (encode_term_pred None res env' tapp)
in (match (_93_3022) with
| (k, decls) -> begin
(

let karr = if ((FStar_List.length formals) > (Prims.parse_int "0")) then begin
(let _194_2377 = (let _194_2376 = (let _194_2375 = (let _194_2374 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _194_2374))
in ((_194_2375), (Some ("kinding")), (Some ((Prims.strcat "pre_kinding_" ttok)))))
in FStar_SMTEncoding_Term.Assume (_194_2376))
in (_194_2377)::[])
end else begin
[]
end
in (let _194_2384 = (let _194_2383 = (let _194_2382 = (let _194_2381 = (let _194_2380 = (let _194_2379 = (let _194_2378 = (FStar_SMTEncoding_Util.mkImp ((guard), (k)))
in ((((tapp)::[])::[]), (vars), (_194_2378)))
in (FStar_SMTEncoding_Util.mkForall _194_2379))
in ((_194_2380), (None), (Some ((Prims.strcat "kinding_" ttok)))))
in FStar_SMTEncoding_Term.Assume (_194_2381))
in (_194_2382)::[])
in (FStar_List.append karr _194_2383))
in (FStar_List.append decls _194_2384)))
end))
in (

let aux = (let _194_2388 = (let _194_2387 = (inversion_axioms tapp vars)
in (let _194_2386 = (let _194_2385 = (pretype_axiom tapp vars)
in (_194_2385)::[])
in (FStar_List.append _194_2387 _194_2386)))
in (FStar_List.append kindingAx _194_2388))
in (

let g = (FStar_List.append decls (FStar_List.append binder_decls aux))
in ((g), (env)))))
end)))))
end))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, _93_3029, _93_3031, _93_3033, _93_3035, _93_3037, _93_3039, _93_3041) when (FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_datacon (d, _93_3046, t, _93_3049, n_tps, quals, _93_3053, drange) -> begin
(

let _93_3060 = (new_term_constant_and_tok_from_lid env d)
in (match (_93_3060) with
| (ddconstrsym, ddtok, env) -> begin
(

let ddtok_tm = (FStar_SMTEncoding_Util.mkApp ((ddtok), ([])))
in (

let _93_3064 = (FStar_Syntax_Util.arrow_formals t)
in (match (_93_3064) with
| (formals, t_res) -> begin
(

let _93_3067 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_93_3067) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (

let _93_3074 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_93_3074) with
| (vars, guards, env', binder_decls, names) -> begin
(

let projectors = (FStar_All.pipe_right names (FStar_List.map (fun x -> (let _194_2390 = (mk_term_projector_name d x)
in ((_194_2390), (FStar_SMTEncoding_Term.Term_sort))))))
in (

let datacons = (let _194_2392 = (let _194_2391 = (varops.next_id ())
in ((ddconstrsym), (projectors), (FStar_SMTEncoding_Term.Term_sort), (_194_2391), (true)))
in (FStar_All.pipe_right _194_2392 FStar_SMTEncoding_Term.constructor_to_decl))
in (

let app = (mk_Apply ddtok_tm vars)
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (

let _93_3084 = (encode_term_pred None t env ddtok_tm)
in (match (_93_3084) with
| (tok_typing, decls3) -> begin
(

let _93_3091 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_93_3091) with
| (vars', guards', env'', decls_formals, _93_3090) -> begin
(

let _93_3096 = (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars')
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (encode_term_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_93_3096) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_SMTEncoding_Util.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _93_3100 -> begin
(let _194_2394 = (let _194_2393 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ddtok), (FStar_SMTEncoding_Term.Term_sort)) _194_2393))
in (_194_2394)::[])
end)
in (

let encode_elim = (fun _93_3103 -> (match (()) with
| () -> begin
(

let _93_3106 = (FStar_Syntax_Util.head_and_args t_res)
in (match (_93_3106) with
| (head, args) -> begin
(match ((let _194_2397 = (FStar_Syntax_Subst.compress head)
in _194_2397.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let _93_3124 = (encode_args args env')
in (match (_93_3124) with
| (encoded_args, arg_decls) -> begin
(

let _93_3139 = (FStar_List.fold_left (fun _93_3128 arg -> (match (_93_3128) with
| (env, arg_vars, eqns) -> begin
(

let _93_3134 = (let _194_2400 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in (gen_term_var env _194_2400))
in (match (_93_3134) with
| (_93_3131, xv, env) -> begin
(let _194_2402 = (let _194_2401 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (_194_2401)::eqns)
in ((env), ((xv)::arg_vars), (_194_2402)))
end))
end)) ((env'), ([]), ([])) encoded_args)
in (match (_93_3139) with
| (_93_3136, arg_vars, eqns) -> begin
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

let typing_inversion = (let _194_2409 = (let _194_2408 = (let _194_2407 = (let _194_2406 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (let _194_2405 = (let _194_2404 = (let _194_2403 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append eqns guards))
in ((ty_pred), (_194_2403)))
in (FStar_SMTEncoding_Util.mkImp _194_2404))
in ((((ty_pred)::[])::[]), (_194_2406), (_194_2405))))
in (FStar_SMTEncoding_Util.mkForall _194_2407))
in ((_194_2408), (Some ("data constructor typing elim")), (Some ((Prims.strcat "data_elim_" ddconstrsym)))))
in FStar_SMTEncoding_Term.Assume (_194_2409))
in (

let subterm_ordering = if (FStar_Ident.lid_equals d FStar_Syntax_Const.lextop_lid) then begin
(

let x = (let _194_2410 = (varops.fresh "x")
in ((_194_2410), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (let _194_2422 = (let _194_2421 = (let _194_2418 = (let _194_2417 = (let _194_2412 = (let _194_2411 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp)
in (_194_2411)::[])
in (_194_2412)::[])
in (let _194_2416 = (let _194_2415 = (let _194_2414 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (let _194_2413 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp)
in ((_194_2414), (_194_2413))))
in (FStar_SMTEncoding_Util.mkImp _194_2415))
in ((_194_2417), ((x)::[]), (_194_2416))))
in (FStar_SMTEncoding_Util.mkForall _194_2418))
in (let _194_2420 = (let _194_2419 = (varops.mk_unique "lextop")
in Some (_194_2419))
in ((_194_2421), (Some ("lextop is top")), (_194_2420))))
in FStar_SMTEncoding_Term.Assume (_194_2422))))
end else begin
(

let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
[]
end
| FStar_SMTEncoding_Term.Term_sort -> begin
(let _194_2425 = (let _194_2424 = (FStar_SMTEncoding_Util.mkFreeV v)
in (FStar_SMTEncoding_Util.mk_Precedes _194_2424 dapp))
in (_194_2425)::[])
end
| _93_3153 -> begin
(failwith "unexpected sort")
end))))
in (let _194_2432 = (let _194_2431 = (let _194_2430 = (let _194_2429 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (let _194_2428 = (let _194_2427 = (let _194_2426 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (_194_2426)))
in (FStar_SMTEncoding_Util.mkImp _194_2427))
in ((((ty_pred)::[])::[]), (_194_2429), (_194_2428))))
in (FStar_SMTEncoding_Util.mkForall _194_2430))
in ((_194_2431), (Some ("subterm ordering")), (Some ((Prims.strcat "subterm_ordering_" ddconstrsym)))))
in FStar_SMTEncoding_Term.Assume (_194_2432)))
end
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end))
end)))
end
| _93_3157 -> begin
(

let _93_3158 = (let _194_2435 = (let _194_2434 = (FStar_Syntax_Print.lid_to_string d)
in (let _194_2433 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _194_2434 _194_2433)))
in (FStar_Errors.warn drange _194_2435))
in (([]), ([])))
end)
end))
end))
in (

let _93_3162 = (encode_elim ())
in (match (_93_3162) with
| (decls2, elim) -> begin
(

let g = (let _194_2462 = (let _194_2461 = (let _194_2460 = (let _194_2459 = (let _194_2440 = (let _194_2439 = (let _194_2438 = (let _194_2437 = (let _194_2436 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" _194_2436))
in Some (_194_2437))
in ((ddtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (_194_2438)))
in FStar_SMTEncoding_Term.DeclFun (_194_2439))
in (_194_2440)::[])
in (let _194_2458 = (let _194_2457 = (let _194_2456 = (let _194_2455 = (let _194_2454 = (let _194_2453 = (let _194_2452 = (let _194_2444 = (let _194_2443 = (let _194_2442 = (let _194_2441 = (FStar_SMTEncoding_Util.mkEq ((app), (dapp)))
in ((((app)::[])::[]), (vars), (_194_2441)))
in (FStar_SMTEncoding_Util.mkForall _194_2442))
in ((_194_2443), (Some ("equality for proxy")), (Some ((Prims.strcat "equality_tok_" ddtok)))))
in FStar_SMTEncoding_Term.Assume (_194_2444))
in (let _194_2451 = (let _194_2450 = (let _194_2449 = (let _194_2448 = (let _194_2447 = (let _194_2446 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) vars')
in (let _194_2445 = (FStar_SMTEncoding_Util.mkImp ((guard'), (ty_pred')))
in ((((ty_pred')::[])::[]), (_194_2446), (_194_2445))))
in (FStar_SMTEncoding_Util.mkForall _194_2447))
in ((_194_2448), (Some ("data constructor typing intro")), (Some ((Prims.strcat "data_typing_intro_" ddtok)))))
in FStar_SMTEncoding_Term.Assume (_194_2449))
in (_194_2450)::[])
in (_194_2452)::_194_2451))
in (FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("typing for data constructor proxy")), (Some ((Prims.strcat "typing_tok_" ddtok))))))::_194_2453)
in (FStar_List.append _194_2454 elim))
in (FStar_List.append decls_pred _194_2455))
in (FStar_List.append decls_formals _194_2456))
in (FStar_List.append proxy_fresh _194_2457))
in (FStar_List.append _194_2459 _194_2458)))
in (FStar_List.append decls3 _194_2460))
in (FStar_List.append decls2 _194_2461))
in (FStar_List.append binder_decls _194_2462))
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
and encode_signature : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _93_3168 se -> (match (_93_3168) with
| (g, env) -> begin
(

let _93_3172 = (encode_sigelt env se)
in (match (_93_3172) with
| (g', env) -> begin
(((FStar_List.append g g')), (env))
end))
end)) (([]), (env)))))


let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env bindings -> (

let encode_binding = (fun b _93_3180 -> (match (_93_3180) with
| (i, decls, env) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (_93_3182) -> begin
(((i + (Prims.parse_int "1"))), ([]), (env))
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (

let _93_3187 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _194_2477 = (FStar_Syntax_Print.bv_to_string x)
in (let _194_2476 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _194_2475 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" _194_2477 _194_2476 _194_2475))))
end else begin
()
end
in (

let _93_3191 = (encode_term t1 env)
in (match (_93_3191) with
| (t, decls') -> begin
(

let t_hash = (FStar_SMTEncoding_Term.hash_of_term t)
in (

let _93_3196 = (let _194_2482 = (let _194_2481 = (let _194_2480 = (FStar_Util.digest_of_string t_hash)
in (let _194_2479 = (let _194_2478 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _194_2478))
in (Prims.strcat _194_2480 _194_2479)))
in (Prims.strcat "x_" _194_2481))
in (new_term_constant_from_string env x _194_2482))
in (match (_93_3196) with
| (xxsym, xx, env') -> begin
(

let t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel None xx t)
in (

let caption = if (FStar_Options.log_queries ()) then begin
(let _194_2486 = (let _194_2485 = (FStar_Syntax_Print.bv_to_string x)
in (let _194_2484 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _194_2483 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _194_2485 _194_2484 _194_2483))))
in Some (_194_2486))
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
| FStar_TypeChecker_Env.Binding_lid (x, (_93_3204, t)) -> begin
(

let t_norm = (whnf env t)
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant None)
in (

let _93_3213 = (encode_free_var env fv t t_norm [])
in (match (_93_3213) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))))
end
| (FStar_TypeChecker_Env.Binding_sig_inst (_, se, _)) | (FStar_TypeChecker_Env.Binding_sig (_, se)) -> begin
(

let _93_3227 = (encode_sigelt env se)
in (match (_93_3227) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))
end)
end))
in (

let _93_3232 = (FStar_List.fold_right encode_binding bindings (((Prims.parse_int "0")), ([]), (env)))
in (match (_93_3232) with
| (_93_3229, decls, env) -> begin
((decls), (env))
end))))


let encode_labels = (fun labs -> (

let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _93_3239 -> (match (_93_3239) with
| (l, _93_3236, _93_3238) -> begin
FStar_SMTEncoding_Term.DeclFun ((((Prims.fst l)), ([]), (FStar_SMTEncoding_Term.Bool_sort), (None)))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _93_3246 -> (match (_93_3246) with
| (l, _93_3243, _93_3245) -> begin
(let _194_2494 = (FStar_All.pipe_left (fun _194_2490 -> FStar_SMTEncoding_Term.Echo (_194_2490)) (Prims.fst l))
in (let _194_2493 = (let _194_2492 = (let _194_2491 = (FStar_SMTEncoding_Util.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (_194_2491))
in (_194_2492)::[])
in (_194_2494)::_194_2493))
end))))
in ((prefix), (suffix)))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (let _194_2499 = (let _194_2498 = (let _194_2497 = (FStar_Util.smap_create (Prims.parse_int "100"))
in {bindings = []; depth = (Prims.parse_int "0"); tcenv = tcenv; warn = true; cache = _194_2497; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_194_2498)::[])
in (FStar_ST.op_Colon_Equals last_env _194_2499)))


let get_env : FStar_TypeChecker_Env.env  ->  env_t = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(failwith "No env; call init first!")
end
| (e)::_93_3252 -> begin
(

let _93_3255 = e
in {bindings = _93_3255.bindings; depth = _93_3255.depth; tcenv = tcenv; warn = _93_3255.warn; cache = _93_3255.cache; nolabels = _93_3255.nolabels; use_zfuel_name = _93_3255.use_zfuel_name; encode_non_total_function_typ = _93_3255.encode_non_total_function_typ})
end))


let set_env : env_t  ->  Prims.unit = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(failwith "Empty env stack")
end
| (_93_3261)::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))


let push_env : Prims.unit  ->  Prims.unit = (fun _93_3263 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(failwith "Empty env stack")
end
| (hd)::tl -> begin
(

let refs = (FStar_Util.smap_copy hd.cache)
in (

let top = (

let _93_3269 = hd
in {bindings = _93_3269.bindings; depth = _93_3269.depth; tcenv = _93_3269.tcenv; warn = _93_3269.warn; cache = refs; nolabels = _93_3269.nolabels; use_zfuel_name = _93_3269.use_zfuel_name; encode_non_total_function_typ = _93_3269.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))


let pop_env : Prims.unit  ->  Prims.unit = (fun _93_3272 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(failwith "Popping an empty stack")
end
| (_93_3276)::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))


let mark_env : Prims.unit  ->  Prims.unit = (fun _93_3278 -> (match (()) with
| () -> begin
(push_env ())
end))


let reset_mark_env : Prims.unit  ->  Prims.unit = (fun _93_3279 -> (match (()) with
| () -> begin
(pop_env ())
end))


let commit_mark_env : Prims.unit  ->  Prims.unit = (fun _93_3280 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| (hd)::(_93_3283)::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _93_3288 -> begin
(failwith "Impossible")
end)
end))


let init : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (

let _93_3290 = (init_env tcenv)
in (

let _93_3292 = (FStar_SMTEncoding_Z3.init ())
in (FStar_SMTEncoding_Z3.giveZ3 ((FStar_SMTEncoding_Term.DefPrelude)::[])))))


let push : Prims.string  ->  Prims.unit = (fun msg -> (

let _93_3295 = (push_env ())
in (

let _93_3297 = (varops.push ())
in (FStar_SMTEncoding_Z3.push msg))))


let pop : Prims.string  ->  Prims.unit = (fun msg -> (

let _93_3300 = (let _194_2520 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _194_2520))
in (

let _93_3302 = (varops.pop ())
in (FStar_SMTEncoding_Z3.pop msg))))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _93_3305 = (mark_env ())
in (

let _93_3307 = (varops.mark ())
in (FStar_SMTEncoding_Z3.mark msg))))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _93_3310 = (reset_mark_env ())
in (

let _93_3312 = (varops.reset_mark ())
in (FStar_SMTEncoding_Z3.reset_mark msg))))


let commit_mark = (fun msg -> (

let _93_3315 = (commit_mark_env ())
in (

let _93_3317 = (varops.commit_mark ())
in (FStar_SMTEncoding_Z3.commit_mark msg))))


let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (

let caption = (fun decls -> if (FStar_Options.log_queries ()) then begin
(let _194_2535 = (let _194_2534 = (let _194_2533 = (let _194_2532 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.map FStar_Syntax_Print.lid_to_string))
in (FStar_All.pipe_right _194_2532 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " _194_2533))
in FStar_SMTEncoding_Term.Caption (_194_2534))
in (_194_2535)::decls)
end else begin
decls
end)
in (

let env = (get_env tcenv)
in (

let _93_3326 = (encode_sigelt env se)
in (match (_93_3326) with
| (decls, env) -> begin
(

let _93_3327 = (set_env env)
in (let _194_2536 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 _194_2536)))
end)))))


let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let _93_3332 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(let _194_2541 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name _194_2541))
end else begin
()
end
in (

let env = (get_env tcenv)
in (

let _93_3339 = (encode_signature (

let _93_3335 = env
in {bindings = _93_3335.bindings; depth = _93_3335.depth; tcenv = _93_3335.tcenv; warn = false; cache = _93_3335.cache; nolabels = _93_3335.nolabels; use_zfuel_name = _93_3335.use_zfuel_name; encode_non_total_function_typ = _93_3335.encode_non_total_function_typ}) modul.FStar_Syntax_Syntax.exports)
in (match (_93_3339) with
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

let _93_3345 = (set_env (

let _93_3343 = env
in {bindings = _93_3343.bindings; depth = _93_3343.depth; tcenv = _93_3343.tcenv; warn = true; cache = _93_3343.cache; nolabels = _93_3343.nolabels; use_zfuel_name = _93_3343.use_zfuel_name; encode_non_total_function_typ = _93_3343.encode_non_total_function_typ}))
in (

let _93_3347 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end else begin
()
end
in (

let decls = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls)))))
end))))))


let encode_query : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_ErrorReporting.label Prims.list * FStar_SMTEncoding_Term.decl * FStar_SMTEncoding_Term.decl Prims.list) = (fun use_env_msg tcenv q -> (

let _93_3353 = (let _194_2559 = (let _194_2558 = (FStar_TypeChecker_Env.current_module tcenv)
in _194_2558.FStar_Ident.str)
in (FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name _194_2559))
in (

let env = (get_env tcenv)
in (

let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (

let _93_3378 = (

let rec aux = (fun bindings -> (match (bindings) with
| (FStar_TypeChecker_Env.Binding_var (x))::rest -> begin
(

let _93_3367 = (aux rest)
in (match (_93_3367) with
| (out, rest) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (let _194_2565 = (let _194_2564 = (FStar_Syntax_Syntax.mk_binder (

let _93_3369 = x
in {FStar_Syntax_Syntax.ppname = _93_3369.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _93_3369.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_194_2564)::out)
in ((_194_2565), (rest))))
end))
end
| _93_3372 -> begin
(([]), (bindings))
end))
in (

let _93_3375 = (aux bindings)
in (match (_93_3375) with
| (closing, bindings) -> begin
(let _194_2566 = (FStar_Syntax_Util.close_forall (FStar_List.rev closing) q)
in ((_194_2566), (bindings)))
end)))
in (match (_93_3378) with
| (q, bindings) -> begin
(

let _93_3387 = (let _194_2568 = (FStar_List.filter (fun _93_25 -> (match (_93_25) with
| FStar_TypeChecker_Env.Binding_sig (_93_3381) -> begin
false
end
| _93_3384 -> begin
true
end)) bindings)
in (encode_env_bindings env _194_2568))
in (match (_93_3387) with
| (env_decls, env) -> begin
(

let _93_3388 = if (((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTQuery")))) then begin
(let _194_2569 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" _194_2569))
end else begin
()
end
in (

let _93_3392 = (encode_formula q env)
in (match (_93_3392) with
| (phi, qdecls) -> begin
(

let _93_3395 = (let _194_2570 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg _194_2570 phi))
in (match (_93_3395) with
| (labels, phi) -> begin
(

let _93_3398 = (encode_labels labels)
in (match (_93_3398) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append env_decls (FStar_List.append label_prefix qdecls))
in (

let qry = (let _194_2574 = (let _194_2573 = (FStar_SMTEncoding_Util.mkNot phi)
in (let _194_2572 = (let _194_2571 = (varops.mk_unique "@query")
in Some (_194_2571))
in ((_194_2573), (Some ("query")), (_194_2572))))
in FStar_SMTEncoding_Term.Assume (_194_2574))
in (

let suffix = (let _194_2576 = (let _194_2575 = if (FStar_Options.print_z3_statistics ()) then begin
(FStar_SMTEncoding_Term.PrintStats)::[]
end else begin
[]
end
in (FStar_List.append _194_2575 ((FStar_SMTEncoding_Term.Echo ("Done!"))::[])))
in (FStar_List.append label_suffix _194_2576))
in ((query_prelude), (labels), (qry), (suffix)))))
end))
end))
end)))
end))
end))))))


let is_trivial : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun tcenv q -> (

let env = (get_env tcenv)
in (

let _93_3405 = (push "query")
in (

let _93_3410 = (encode_formula q env)
in (match (_93_3410) with
| (f, _93_3409) -> begin
(

let _93_3411 = (pop "query")
in (match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, _93_3415) -> begin
true
end
| _93_3419 -> begin
false
end))
end)))))




