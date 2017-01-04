
open Prims

let add_fuel = (fun x tl -> if (FStar_Options.unthrottle_inductives ()) then begin
tl
end else begin
(x)::tl
end)


let withenv = (fun c _91_31 -> (match (_91_31) with
| (a, b) -> begin
((a), (b), (c))
end))


let vargs = (fun args -> (FStar_List.filter (fun _91_1 -> (match (_91_1) with
| (FStar_Util.Inl (_91_35), _91_38) -> begin
false
end
| _91_41 -> begin
true
end)) args))


let subst_lcomp_opt = (fun s l -> (match (l) with
| Some (FStar_Util.Inl (l)) -> begin
(let _189_12 = (let _189_11 = (let _189_10 = (let _189_9 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp s _189_9))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _189_10))
in FStar_Util.Inl (_189_11))
in Some (_189_12))
end
| _91_48 -> begin
l
end))


let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s '\'' '_'))


let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun lid a -> (

let a = (

let _91_52 = a
in (let _189_19 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _189_19; FStar_Syntax_Syntax.index = _91_52.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _91_52.FStar_Syntax_Syntax.sort}))
in (let _189_20 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str a.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (FStar_All.pipe_left escape _189_20))))


let primitive_projector_by_pos : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (

let fail = (fun _91_59 -> (match (()) with
| () -> begin
(let _189_30 = (let _189_29 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" _189_29 lid.FStar_Ident.str))
in (FStar_All.failwith _189_30))
end))
in (

let _91_63 = (FStar_TypeChecker_Env.lookup_datacon env lid)
in (match (_91_63) with
| (_91_61, t) -> begin
(match ((let _189_31 = (FStar_Syntax_Subst.compress t)
in _189_31.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _91_71 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_91_71) with
| (binders, _91_70) -> begin
if ((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(

let b = (FStar_List.nth binders i)
in (mk_term_projector_name lid (Prims.fst b)))
end
end))
end
| _91_74 -> begin
(fail ())
end)
end))))


let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (let _189_37 = (let _189_36 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str _189_36))
in (FStar_All.pipe_left escape _189_37)))


let mk_term_projector : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun lid a -> (let _189_43 = (let _189_42 = (mk_term_projector_name lid a)
in ((_189_42), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Util.mkFreeV _189_43)))


let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_SMTEncoding_Term.term = (fun lid i -> (let _189_49 = (let _189_48 = (mk_term_projector_name_by_pos lid i)
in ((_189_48), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Util.mkFreeV _189_49)))


let mk_data_tester = (fun env l x -> (FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x))


type varops_t =
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; mark : Prims.unit  ->  Prims.unit; reset_mark : Prims.unit  ->  Prims.unit; commit_mark : Prims.unit  ->  Prims.unit; new_var : FStar_Ident.ident  ->  Prims.int  ->  Prims.string; new_fvar : FStar_Ident.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_SMTEncoding_Term.term; next_id : Prims.unit  ->  Prims.int; mk_unique : Prims.string  ->  Prims.string}


let is_Mkvarops_t : varops_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkvarops_t"))))


let varops : varops_t = (

let initial_ctr = (Prims.parse_int "100")
in (

let ctr = (FStar_Util.mk_ref initial_ctr)
in (

let new_scope = (fun _91_99 -> (match (()) with
| () -> begin
(let _189_162 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (let _189_161 = (FStar_Util.smap_create (Prims.parse_int "100"))
in ((_189_162), (_189_161))))
end))
in (

let scopes = (let _189_164 = (let _189_163 = (new_scope ())
in (_189_163)::[])
in (FStar_Util.mk_ref _189_164))
in (

let mk_unique = (fun y -> (

let y = (escape y)
in (

let y = (match ((let _189_168 = (FStar_ST.read scopes)
in (FStar_Util.find_map _189_168 (fun _91_107 -> (match (_91_107) with
| (names, _91_106) -> begin
(FStar_Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_91_110) -> begin
(

let _91_112 = (FStar_Util.incr ctr)
in (let _189_171 = (let _189_170 = (let _189_169 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _189_169))
in (Prims.strcat "__" _189_170))
in (Prims.strcat y _189_171)))
end)
in (

let top_scope = (let _189_173 = (let _189_172 = (FStar_ST.read scopes)
in (FStar_List.hd _189_172))
in (FStar_All.pipe_left Prims.fst _189_173))
in (

let _91_116 = (FStar_Util.smap_add top_scope y true)
in y)))))
in (

let new_var = (fun pp rn -> (let _189_180 = (let _189_179 = (let _189_178 = (FStar_Util.string_of_int rn)
in (Prims.strcat "__" _189_178))
in (Prims.strcat pp.FStar_Ident.idText _189_179))
in (FStar_All.pipe_left mk_unique _189_180)))
in (

let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (

let next_id = (fun _91_124 -> (match (()) with
| () -> begin
(

let _91_125 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end))
in (

let fresh = (fun pfx -> (let _189_188 = (let _189_187 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _189_187))
in (FStar_Util.format2 "%s_%s" pfx _189_188)))
in (

let string_const = (fun s -> (match ((let _189_192 = (FStar_ST.read scopes)
in (FStar_Util.find_map _189_192 (fun _91_134 -> (match (_91_134) with
| (_91_132, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))) with
| Some (f) -> begin
f
end
| None -> begin
(

let id = (next_id ())
in (

let f = (let _189_193 = (FStar_SMTEncoding_Util.mk_String_const id)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString _189_193))
in (

let top_scope = (let _189_195 = (let _189_194 = (FStar_ST.read scopes)
in (FStar_List.hd _189_194))
in (FStar_All.pipe_left Prims.snd _189_195))
in (

let _91_141 = (FStar_Util.smap_add top_scope s f)
in f))))
end))
in (

let push = (fun _91_144 -> (match (()) with
| () -> begin
(let _189_200 = (let _189_199 = (new_scope ())
in (let _189_198 = (FStar_ST.read scopes)
in (_189_199)::_189_198))
in (FStar_ST.op_Colon_Equals scopes _189_200))
end))
in (

let pop = (fun _91_146 -> (match (()) with
| () -> begin
(let _189_204 = (let _189_203 = (FStar_ST.read scopes)
in (FStar_List.tl _189_203))
in (FStar_ST.op_Colon_Equals scopes _189_204))
end))
in (

let mark = (fun _91_148 -> (match (()) with
| () -> begin
(push ())
end))
in (

let reset_mark = (fun _91_150 -> (match (()) with
| () -> begin
(pop ())
end))
in (

let commit_mark = (fun _91_152 -> (match (()) with
| () -> begin
(match ((FStar_ST.read scopes)) with
| ((hd1, hd2))::((next1, next2))::tl -> begin
(

let _91_165 = (FStar_Util.smap_fold hd1 (fun key value v -> (FStar_Util.smap_add next1 key value)) ())
in (

let _91_170 = (FStar_Util.smap_fold hd2 (fun key value v -> (FStar_Util.smap_add next2 key value)) ())
in (FStar_ST.op_Colon_Equals scopes ((((next1), (next2)))::tl))))
end
| _91_173 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id; mk_unique = mk_unique})))))))))))))))


let unmangle : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv = (fun x -> (

let _91_175 = x
in (let _189_219 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _189_219; FStar_Syntax_Syntax.index = _91_175.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _91_175.FStar_Syntax_Syntax.sort})))


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
| Binding_var (_91_179) -> begin
_91_179
end))


let ___Binding_fvar____0 = (fun projectee -> (match (projectee) with
| Binding_fvar (_91_182) -> begin
_91_182
end))


let binder_of_eithervar = (fun v -> ((v), (None)))


type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_TypeChecker_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_SMTEncoding_Term.sort Prims.list * FStar_SMTEncoding_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}


let is_Mkenv_t : env_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_t"))))


let print_env : env_t  ->  Prims.string = (fun e -> (let _189_277 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun _91_2 -> (match (_91_2) with
| Binding_var (x, _91_197) -> begin
(FStar_Syntax_Print.bv_to_string x)
end
| Binding_fvar (l, _91_202, _91_204, _91_206) -> begin
(FStar_Syntax_Print.lid_to_string l)
end))))
in (FStar_All.pipe_right _189_277 (FStar_String.concat ", "))))


let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))


let caption_t : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.string Prims.option = (fun env t -> if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _189_287 = (FStar_Syntax_Print.term_to_string t)
in Some (_189_287))
end else begin
None
end)


let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (

let xsym = (varops.fresh x)
in (let _189_292 = (FStar_SMTEncoding_Util.mkFreeV ((xsym), (s)))
in ((xsym), (_189_292)))))


let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (let _189_297 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _189_297))
in (

let y = (FStar_SMTEncoding_Util.mkFreeV ((ysym), (FStar_SMTEncoding_Term.Term_sort)))
in ((ysym), (y), ((

let _91_220 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = (env.depth + (Prims.parse_int "1")); tcenv = _91_220.tcenv; warn = _91_220.warn; cache = _91_220.cache; nolabels = _91_220.nolabels; use_zfuel_name = _91_220.use_zfuel_name; encode_non_total_function_typ = _91_220.encode_non_total_function_typ}))))))


let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let _91_226 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = _91_226.depth; tcenv = _91_226.tcenv; warn = _91_226.warn; cache = _91_226.cache; nolabels = _91_226.nolabels; use_zfuel_name = _91_226.use_zfuel_name; encode_non_total_function_typ = _91_226.encode_non_total_function_typ}))))))


let new_term_constant_from_string : env_t  ->  FStar_Syntax_Syntax.bv  ->  Prims.string  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x str -> (

let ysym = (varops.mk_unique str)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let _91_233 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = _91_233.depth; tcenv = _91_233.tcenv; warn = _91_233.warn; cache = _91_233.cache; nolabels = _91_233.nolabels; use_zfuel_name = _91_233.use_zfuel_name; encode_non_total_function_typ = _91_233.encode_non_total_function_typ}))))))


let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (

let _91_238 = env
in {bindings = (Binding_var (((x), (t))))::env.bindings; depth = _91_238.depth; tcenv = _91_238.tcenv; warn = _91_238.warn; cache = _91_238.cache; nolabels = _91_238.nolabels; use_zfuel_name = _91_238.use_zfuel_name; encode_non_total_function_typ = _91_238.encode_non_total_function_typ}))


let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let aux = (fun a' -> (lookup_binding env (fun _91_3 -> (match (_91_3) with
| Binding_var (b, t) when (FStar_Syntax_Syntax.bv_eq b a') -> begin
Some (((b), (t)))
end
| _91_250 -> begin
None
end))))
in (match ((aux a)) with
| None -> begin
(

let a = (unmangle a)
in (match ((aux a)) with
| None -> begin
(let _189_322 = (let _189_321 = (FStar_Syntax_Print.bv_to_string a)
in (FStar_Util.format1 "Bound term variable not found (after unmangling): %s" _189_321))
in (FStar_All.failwith _189_322))
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
in (let _189_333 = (

let _91_266 = env
in (let _189_332 = (let _189_331 = (let _189_330 = (let _189_329 = (let _189_328 = (FStar_SMTEncoding_Util.mkApp ((ftok), ([])))
in (FStar_All.pipe_left (fun _189_327 -> Some (_189_327)) _189_328))
in ((x), (fname), (_189_329), (None)))
in Binding_fvar (_189_330))
in (_189_331)::env.bindings)
in {bindings = _189_332; depth = _91_266.depth; tcenv = _91_266.tcenv; warn = _91_266.warn; cache = _91_266.cache; nolabels = _91_266.nolabels; use_zfuel_name = _91_266.use_zfuel_name; encode_non_total_function_typ = _91_266.encode_non_total_function_typ}))
in ((fname), (ftok), (_189_333))))))


let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun _91_4 -> (match (_91_4) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some (((t1), (t2), (t3)))
end
| _91_278 -> begin
None
end))))


let contains_name : env_t  ->  Prims.string  ->  Prims.bool = (fun env s -> (let _189_344 = (lookup_binding env (fun _91_5 -> (match (_91_5) with
| Binding_fvar (b, t1, t2, t3) when (b.FStar_Ident.str = s) -> begin
Some (())
end
| _91_289 -> begin
None
end)))
in (FStar_All.pipe_right _189_344 FStar_Option.isSome)))


let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _189_350 = (let _189_349 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" _189_349))
in (FStar_All.failwith _189_350))
end
| Some (s) -> begin
s
end))


let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (

let _91_299 = env
in {bindings = (Binding_fvar (((x), (fname), (ftok), (None))))::env.bindings; depth = _91_299.depth; tcenv = _91_299.tcenv; warn = _91_299.warn; cache = _91_299.cache; nolabels = _91_299.nolabels; use_zfuel_name = _91_299.use_zfuel_name; encode_non_total_function_typ = _91_299.encode_non_total_function_typ}))


let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (

let _91_308 = (lookup_lid env x)
in (match (_91_308) with
| (t1, t2, _91_307) -> begin
(

let t3 = (let _189_367 = (let _189_366 = (let _189_365 = (FStar_SMTEncoding_Util.mkApp (("ZFuel"), ([])))
in (_189_365)::[])
in ((f), (_189_366)))
in (FStar_SMTEncoding_Util.mkApp _189_367))
in (

let _91_310 = env
in {bindings = (Binding_fvar (((x), (t1), (t2), (Some (t3)))))::env.bindings; depth = _91_310.depth; tcenv = _91_310.tcenv; warn = _91_310.warn; cache = _91_310.cache; nolabels = _91_310.nolabels; use_zfuel_name = _91_310.use_zfuel_name; encode_non_total_function_typ = _91_310.encode_non_total_function_typ}))
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
| _91_323 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (_91_327, (fuel)::[]) -> begin
if (let _189_373 = (let _189_372 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right _189_372 Prims.fst))
in (FStar_Util.starts_with _189_373 "fuel")) then begin
(let _189_376 = (let _189_375 = (FStar_SMTEncoding_Util.mkFreeV ((name), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_ApplyTF _189_375 fuel))
in (FStar_All.pipe_left (fun _189_374 -> Some (_189_374)) _189_376))
end else begin
Some (t)
end
end
| _91_333 -> begin
Some (t)
end)
end
| _91_335 -> begin
None
end)
end)
end))


let lookup_free_var = (fun env a -> (match ((try_lookup_free_var env a.FStar_Syntax_Syntax.v)) with
| Some (t) -> begin
t
end
| None -> begin
(let _189_380 = (let _189_379 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _189_379))
in (FStar_All.failwith _189_380))
end))


let lookup_free_var_name = (fun env a -> (

let _91_348 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_91_348) with
| (x, _91_345, _91_347) -> begin
x
end)))


let lookup_free_var_sym = (fun env a -> (

let _91_354 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_91_354) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.freevars = _91_358; FStar_SMTEncoding_Term.rng = _91_356}) when env.use_zfuel_name -> begin
((g), (zf))
end
| _91_366 -> begin
(match (sym) with
| None -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end
| Some (sym) -> begin
(match (sym.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, (fuel)::[]) -> begin
((g), ((fuel)::[]))
end
| _91_376 -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end)
end)
end)
end)))


let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun _91_6 -> (match (_91_6) with
| Binding_fvar (_91_381, nm', tok, _91_385) when (nm = nm') -> begin
tok
end
| _91_389 -> begin
None
end))))


let mkForall_fuel' = (fun n _91_394 -> (match (_91_394) with
| (pats, vars, body) -> begin
(

let fallback = (fun _91_396 -> (match (()) with
| () -> begin
(FStar_SMTEncoding_Util.mkForall ((pats), (vars), (body)))
end))
in if (FStar_Options.unthrottle_inductives ()) then begin
(fallback ())
end else begin
(

let _91_399 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_91_399) with
| (fsym, fterm) -> begin
(

let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Util.mkApp (("HasTypeFuel"), ((fterm)::args)))
end
| _91_409 -> begin
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
(let _189_397 = (add_fuel guards)
in (FStar_SMTEncoding_Util.mk_and_l _189_397))
end
| _91_422 -> begin
(let _189_398 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _189_398 FStar_List.hd))
end)
in (FStar_SMTEncoding_Util.mkImp ((guard), (body'))))
end
| _91_425 -> begin
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
(let _189_404 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _189_404 FStar_Option.isNone))
end
| _91_464 -> begin
false
end)))


let head_redex : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (match ((let _189_409 = (FStar_Syntax_Util.un_uinst t)
in _189_409.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_91_468, _91_470, Some (FStar_Util.Inr (l, flags))) -> begin
(((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid)) || (FStar_List.existsb (fun _91_7 -> (match (_91_7) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| _91_481 -> begin
false
end)) flags))
end
| FStar_Syntax_Syntax.Tm_abs (_91_483, _91_485, Some (FStar_Util.Inl (lc))) -> begin
(FStar_Syntax_Util.is_tot_or_gtot_lcomp lc)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(let _189_411 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _189_411 FStar_Option.isSome))
end
| _91_494 -> begin
false
end))


let whnf : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> if (head_normal env t) then begin
t
end else begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
end)


let norm : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t))


let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (let _189_424 = (let _189_422 = (FStar_Syntax_Syntax.null_binder t)
in (_189_422)::[])
in (let _189_423 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Util.abs _189_424 _189_423 None))))


let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(let _189_431 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out _189_431))
end
| s -> begin
(

let _91_506 = ()
in (let _189_432 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Util.mk_ApplyTT out _189_432)))
end)) e)))


let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)))


let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun _91_8 -> (match (_91_8) with
| (FStar_SMTEncoding_Term.Var ("ApplyTT")) | (FStar_SMTEncoding_Term.Var ("ApplyTF")) -> begin
true
end
| _91_516 -> begin
false
end))


let is_eta : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env vars t -> (

let rec aux = (fun t xs -> (match (((t.FStar_SMTEncoding_Term.tm), (xs))) with
| (FStar_SMTEncoding_Term.App (app, (f)::({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.freevars = _91_527; FStar_SMTEncoding_Term.rng = _91_525})::[]), (x)::xs) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), _91_545) -> begin
if (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v)
end
| _91_552 -> begin
false
end)) args vars)) then begin
(tok_of_name env f)
end else begin
None
end
end
| (_91_554, []) -> begin
(

let fvs = (FStar_SMTEncoding_Term.free_variables t)
in if (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (not ((FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)))))) then begin
Some (t)
end else begin
None
end)
end
| _91_560 -> begin
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


let encode_const : FStar_Const.sconst  ->  FStar_SMTEncoding_Term.term = (fun _91_9 -> (match (_91_9) with
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
(let _189_489 = (let _189_488 = (let _189_487 = (let _189_486 = (FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c))
in (FStar_SMTEncoding_Term.boxInt _189_486))
in (_189_487)::[])
in (("FStar.Char.Char"), (_189_488)))
in (FStar_SMTEncoding_Util.mkApp _189_489))
end
| FStar_Const.Const_int (i, None) -> begin
(let _189_490 = (FStar_SMTEncoding_Util.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt _189_490))
end
| FStar_Const.Const_int (i, Some (_91_580)) -> begin
(FStar_All.failwith "Machine integers should be desugared")
end
| FStar_Const.Const_string (bytes, _91_586) -> begin
(let _189_491 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _189_491))
end
| FStar_Const.Const_range (r) -> begin
FStar_SMTEncoding_Term.mk_Range_const
end
| FStar_Const.Const_effect -> begin
FStar_SMTEncoding_Term.mk_Term_type
end
| c -> begin
(let _189_493 = (let _189_492 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" _189_492))
in (FStar_All.failwith _189_493))
end))


let as_function_typ : env_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (

let rec aux = (fun norm t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_91_600) -> begin
t
end
| FStar_Syntax_Syntax.Tm_refine (_91_603) -> begin
(let _189_502 = (FStar_Syntax_Util.unrefine t)
in (aux true _189_502))
end
| _91_606 -> begin
if norm then begin
(let _189_503 = (whnf env t)
in (aux false _189_503))
end else begin
(let _189_506 = (let _189_505 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (let _189_504 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _189_505 _189_504)))
in (FStar_All.failwith _189_506))
end
end)))
in (aux true t0)))


let curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun k -> (

let k = (FStar_Syntax_Subst.compress k)
in (match (k.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| _91_614 -> begin
(let _189_509 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (_189_509)))
end)))


let rec encode_binders : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> (

let _91_618 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _189_557 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" _189_557))
end else begin
()
end
in (

let _91_646 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _91_625 b -> (match (_91_625) with
| (vars, guards, env, decls, names) -> begin
(

let _91_640 = (

let x = (unmangle (Prims.fst b))
in (

let _91_631 = (gen_term_var env x)
in (match (_91_631) with
| (xxsym, xx, env') -> begin
(

let _91_634 = (let _189_560 = (norm env x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt _189_560 env xx))
in (match (_91_634) with
| (guard_x_t, decls') -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (guard_x_t), (env'), (decls'), (x))
end))
end)))
in (match (_91_640) with
| (v, g, env, decls', n) -> begin
(((v)::vars), ((g)::guards), (env), ((FStar_List.append decls decls')), ((n)::names))
end))
end)) (([]), ([]), (env), ([]), ([]))))
in (match (_91_646) with
| (vars, guards, env, decls, names) -> begin
(((FStar_List.rev vars)), ((FStar_List.rev guards)), (env), (decls), ((FStar_List.rev names)))
end))))
and encode_term_pred : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let _91_653 = (encode_term t env)
in (match (_91_653) with
| (t, decls) -> begin
(let _189_565 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t)
in ((_189_565), (decls)))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let _91_660 = (encode_term t env)
in (match (_91_660) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _189_570 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t)
in ((_189_570), (decls)))
end
| Some (f) -> begin
(let _189_571 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t)
in ((_189_571), (decls)))
end)
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let t0 = (FStar_Syntax_Subst.compress t)
in (

let _91_667 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _189_576 = (FStar_Syntax_Print.tag_of_term t)
in (let _189_575 = (FStar_Syntax_Print.tag_of_term t0)
in (let _189_574 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" _189_576 _189_575 _189_574))))
end else begin
()
end
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _189_581 = (let _189_580 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (let _189_579 = (FStar_Syntax_Print.tag_of_term t0)
in (let _189_578 = (FStar_Syntax_Print.term_to_string t0)
in (let _189_577 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _189_580 _189_579 _189_578 _189_577)))))
in (FStar_All.failwith _189_581))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _189_583 = (let _189_582 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" _189_582))
in (FStar_All.failwith _189_583))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, k, _91_678) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_meta (t, _91_683) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t = (lookup_term_var env x)
in ((t), ([])))
end
| FStar_Syntax_Syntax.Tm_fvar (v) -> begin
(let _189_584 = (lookup_free_var env v.FStar_Syntax_Syntax.fv_name)
in ((_189_584), ([])))
end
| FStar_Syntax_Syntax.Tm_type (_91_692) -> begin
((FStar_SMTEncoding_Term.mk_Term_type), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t, _91_696) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(let _189_585 = (encode_const c)
in ((_189_585), ([])))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _91_707 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_91_707) with
| (binders, res) -> begin
if ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res)) then begin
(

let _91_714 = (encode_binders None binders env)
in (match (_91_714) with
| (vars, guards, env', decls, _91_713) -> begin
(

let fsym = (let _189_586 = (varops.fresh "f")
in ((_189_586), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV fsym)
in (

let app = (mk_Apply f vars)
in (

let _91_722 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post (

let _91_718 = env.tcenv
in {FStar_TypeChecker_Env.solver = _91_718.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _91_718.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _91_718.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _91_718.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _91_718.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _91_718.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _91_718.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _91_718.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _91_718.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _91_718.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _91_718.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _91_718.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _91_718.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _91_718.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _91_718.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _91_718.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _91_718.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _91_718.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _91_718.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _91_718.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _91_718.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _91_718.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _91_718.FStar_TypeChecker_Env.qname_and_index}) res)
in (match (_91_722) with
| (pre_opt, res_t) -> begin
(

let _91_725 = (encode_term_pred None res_t env' app)
in (match (_91_725) with
| (res_pred, decls') -> begin
(

let _91_734 = (match (pre_opt) with
| None -> begin
(let _189_587 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((_189_587), ([])))
end
| Some (pre) -> begin
(

let _91_731 = (encode_formula pre env')
in (match (_91_731) with
| (guard, decls0) -> begin
(let _189_588 = (FStar_SMTEncoding_Util.mk_and_l ((guard)::guards))
in ((_189_588), (decls0)))
end))
end)
in (match (_91_734) with
| (guards, guard_decls) -> begin
(

let t_interp = (let _189_590 = (let _189_589 = (FStar_SMTEncoding_Util.mkImp ((guards), (res_pred)))
in ((((app)::[])::[]), (vars), (_189_589)))
in (FStar_SMTEncoding_Util.mkForall _189_590))
in (

let cvars = (let _189_592 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right _189_592 (FStar_List.filter (fun _91_739 -> (match (_91_739) with
| (x, _91_738) -> begin
(x <> (Prims.fst fsym))
end)))))
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), ((fsym)::cvars), (t_interp)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (match ((FStar_Util.smap_try_find env.cache tkey_hash)) with
| Some (t', sorts, _91_746) -> begin
(let _189_595 = (let _189_594 = (let _189_593 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((t'), (_189_593)))
in (FStar_SMTEncoding_Util.mkApp _189_594))
in ((_189_595), ([])))
end
| None -> begin
(

let tsym = (let _189_597 = (let _189_596 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_arrow_" _189_596))
in (varops.mk_unique _189_597))
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let caption = if (FStar_Options.log_queries ()) then begin
(let _189_598 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in Some (_189_598))
end else begin
None
end
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (caption)))
in (

let t = (let _189_600 = (let _189_599 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((tsym), (_189_599)))
in (FStar_SMTEncoding_Util.mkApp _189_600))
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let k_assumption = (

let a_name = Some ((Prims.strcat "kinding_" tsym))
in (let _189_602 = (let _189_601 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((_189_601), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_189_602)))
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t)
in (

let pre_typing = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in (let _189_609 = (let _189_608 = (let _189_607 = (let _189_606 = (let _189_605 = (let _189_604 = (let _189_603 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _189_603))
in ((f_has_t), (_189_604)))
in (FStar_SMTEncoding_Util.mkImp _189_605))
in ((((f_has_t)::[])::[]), ((fsym)::cvars), (_189_606)))
in (mkForall_fuel _189_607))
in ((_189_608), (Some ("pre-typing for functions")), (a_name)))
in FStar_SMTEncoding_Term.Assume (_189_609)))
in (

let t_interp = (

let a_name = Some ((Prims.strcat "interpretation_" tsym))
in (let _189_613 = (let _189_612 = (let _189_611 = (let _189_610 = (FStar_SMTEncoding_Util.mkIff ((f_has_t_z), (t_interp)))
in ((((f_has_t_z)::[])::[]), ((fsym)::cvars), (_189_610)))
in (FStar_SMTEncoding_Util.mkForall _189_611))
in ((_189_612), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_189_613)))
in (

let t_decls = (FStar_List.append ((tdecl)::decls) (FStar_List.append decls' (FStar_List.append guard_decls ((k_assumption)::(pre_typing)::(t_interp)::[]))))
in (

let _91_765 = (FStar_Util.smap_add env.cache tkey_hash ((tsym), (cvar_sorts), (t_decls)))
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
in (let _189_615 = (let _189_614 = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in ((_189_614), (Some ("Typing for non-total arrows")), (a_name)))
in FStar_SMTEncoding_Term.Assume (_189_615)))
in (

let fsym = (("f"), (FStar_SMTEncoding_Term.Term_sort))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV fsym)
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let t_interp = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in (let _189_622 = (let _189_621 = (let _189_620 = (let _189_619 = (let _189_618 = (let _189_617 = (let _189_616 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _189_616))
in ((f_has_t), (_189_617)))
in (FStar_SMTEncoding_Util.mkImp _189_618))
in ((((f_has_t)::[])::[]), ((fsym)::[]), (_189_619)))
in (mkForall_fuel _189_620))
in ((_189_621), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_189_622)))
in ((t), ((tdecl)::(t_kinding)::(t_interp)::[]))))))))))
end
end))
end
| FStar_Syntax_Syntax.Tm_refine (_91_778) -> begin
(

let _91_798 = (match ((FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.tk = _91_785; FStar_Syntax_Syntax.pos = _91_783; FStar_Syntax_Syntax.vars = _91_781} -> begin
(

let _91_793 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) f)
in (match (_91_793) with
| (b, f) -> begin
(let _189_624 = (let _189_623 = (FStar_List.hd b)
in (Prims.fst _189_623))
in ((_189_624), (f)))
end))
end
| _91_795 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_91_798) with
| (x, f) -> begin
(

let _91_801 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (_91_801) with
| (base_t, decls) -> begin
(

let _91_805 = (gen_term_var env x)
in (match (_91_805) with
| (x, xtm, env') -> begin
(

let _91_808 = (encode_formula f env')
in (match (_91_808) with
| (refinement, decls') -> begin
(

let _91_811 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_91_811) with
| (fsym, fterm) -> begin
(

let encoding = (let _189_626 = (let _189_625 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in ((_189_625), (refinement)))
in (FStar_SMTEncoding_Util.mkAnd _189_626))
in (

let cvars = (let _189_628 = (FStar_SMTEncoding_Term.free_variables encoding)
in (FStar_All.pipe_right _189_628 (FStar_List.filter (fun _91_816 -> (match (_91_816) with
| (y, _91_815) -> begin
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
| Some (t, _91_824, _91_826) -> begin
(let _189_631 = (let _189_630 = (let _189_629 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((t), (_189_629)))
in (FStar_SMTEncoding_Util.mkApp _189_630))
in ((_189_631), ([])))
end
| None -> begin
(

let tsym = (let _189_633 = (let _189_632 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_refine_" _189_632))
in (varops.mk_unique _189_633))
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let t = (let _189_635 = (let _189_634 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((tsym), (_189_634)))
in (FStar_SMTEncoding_Util.mkApp _189_635))
in (

let x_has_t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let t_haseq_base = (FStar_SMTEncoding_Term.mk_haseq base_t)
in (

let t_haseq_ref = (FStar_SMTEncoding_Term.mk_haseq t)
in (

let t_haseq = (let _189_639 = (let _189_638 = (let _189_637 = (let _189_636 = (FStar_SMTEncoding_Util.mkIff ((t_haseq_ref), (t_haseq_base)))
in ((((t_haseq_ref)::[])::[]), (cvars), (_189_636)))
in (FStar_SMTEncoding_Util.mkForall _189_637))
in ((_189_638), (Some ((Prims.strcat "haseq for " tsym))), (Some ((Prims.strcat "haseq" tsym)))))
in FStar_SMTEncoding_Term.Assume (_189_639))
in (

let t_kinding = (let _189_641 = (let _189_640 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((_189_640), (Some ("refinement kinding")), (Some ((Prims.strcat "refinement_kinding_" tsym)))))
in FStar_SMTEncoding_Term.Assume (_189_641))
in (

let t_interp = (let _189_647 = (let _189_646 = (let _189_643 = (let _189_642 = (FStar_SMTEncoding_Util.mkIff ((x_has_t), (encoding)))
in ((((x_has_t)::[])::[]), ((ffv)::(xfv)::cvars), (_189_642)))
in (FStar_SMTEncoding_Util.mkForall _189_643))
in (let _189_645 = (let _189_644 = (FStar_Syntax_Print.term_to_string t0)
in Some (_189_644))
in ((_189_646), (_189_645), (Some ((Prims.strcat "refinement_interpretation_" tsym))))))
in FStar_SMTEncoding_Term.Assume (_189_647))
in (

let t_decls = (FStar_List.append decls (FStar_List.append decls' ((tdecl)::(t_kinding)::(t_interp)::(t_haseq)::[])))
in (

let _91_842 = (FStar_Util.smap_add env.cache tkey_hash ((tsym), (cvar_sorts), (t_decls)))
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

let ttm = (let _189_648 = (FStar_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Util.mk_Term_uvar _189_648))
in (

let _91_851 = (encode_term_pred None k env ttm)
in (match (_91_851) with
| (t_has_k, decls) -> begin
(

let d = (let _189_654 = (let _189_653 = (let _189_652 = (let _189_651 = (let _189_650 = (let _189_649 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _189_649))
in (FStar_Util.format1 "uvar_typing_%s" _189_650))
in (varops.mk_unique _189_651))
in Some (_189_652))
in ((t_has_k), (Some ("Uvar typing")), (_189_653)))
in FStar_SMTEncoding_Term.Assume (_189_654))
in ((ttm), ((FStar_List.append decls ((d)::[])))))
end)))
end
| FStar_Syntax_Syntax.Tm_app (_91_854) -> begin
(

let _91_858 = (FStar_Syntax_Util.head_and_args t0)
in (match (_91_858) with
| (head, args_e) -> begin
(match ((let _189_656 = (let _189_655 = (FStar_Syntax_Subst.compress head)
in _189_655.FStar_Syntax_Syntax.n)
in ((_189_656), (args_e)))) with
| (_91_860, _91_862) when (head_redex env head) -> begin
(let _189_657 = (whnf env t)
in (encode_term _189_657 env))
end
| ((FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), (_)::((v1, _))::((v2, _))::[])) | ((FStar_Syntax_Syntax.Tm_fvar (fv), (_)::((v1, _))::((v2, _))::[])) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
(

let _91_902 = (encode_term v1 env)
in (match (_91_902) with
| (v1, decls1) -> begin
(

let _91_905 = (encode_term v2 env)
in (match (_91_905) with
| (v2, decls2) -> begin
(let _189_658 = (FStar_SMTEncoding_Util.mk_LexCons v1 v2)
in ((_189_658), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), (_91_914)::(_91_911)::_91_909) -> begin
(

let e0 = (let _189_662 = (let _189_661 = (let _189_660 = (let _189_659 = (FStar_List.hd args_e)
in (_189_659)::[])
in ((head), (_189_660)))
in FStar_Syntax_Syntax.Tm_app (_189_661))
in (FStar_Syntax_Syntax.mk _189_662 None head.FStar_Syntax_Syntax.pos))
in (

let e = (let _189_665 = (let _189_664 = (let _189_663 = (FStar_List.tl args_e)
in ((e0), (_189_663)))
in FStar_Syntax_Syntax.Tm_app (_189_664))
in (FStar_Syntax_Syntax.mk _189_665 None t0.FStar_Syntax_Syntax.pos))
in (encode_term e env)))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), ((arg, _91_923))::[]) -> begin
(

let _91_929 = (encode_term arg env)
in (match (_91_929) with
| (tm, decls) -> begin
(let _189_666 = (FStar_SMTEncoding_Util.mkApp (("Reify"), ((tm)::[])))
in ((_189_666), (decls)))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (_91_931)), ((arg, _91_936))::[]) -> begin
(encode_term arg env)
end
| _91_941 -> begin
(

let _91_944 = (encode_args args_e env)
in (match (_91_944) with
| (args, decls) -> begin
(

let encode_partial_app = (fun ht_opt -> (

let _91_949 = (encode_term head env)
in (match (_91_949) with
| (head, decls') -> begin
(

let app_tm = (mk_Apply_args head args)
in (match (ht_opt) with
| None -> begin
((app_tm), ((FStar_List.append decls decls')))
end
| Some (formals, c) -> begin
(

let _91_958 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (_91_958) with
| (formals, rest) -> begin
(

let subst = (FStar_List.map2 (fun _91_962 _91_966 -> (match (((_91_962), (_91_966))) with
| ((bv, _91_961), (a, _91_965)) -> begin
FStar_Syntax_Syntax.NT (((bv), (a)))
end)) formals args_e)
in (

let ty = (let _189_671 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right _189_671 (FStar_Syntax_Subst.subst subst)))
in (

let _91_971 = (encode_term_pred None ty env app_tm)
in (match (_91_971) with
| (has_type, decls'') -> begin
(

let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (

let e_typing = (let _189_678 = (let _189_677 = (FStar_SMTEncoding_Util.mkForall ((((has_type)::[])::[]), (cvars), (has_type)))
in (let _189_676 = (let _189_675 = (let _189_674 = (let _189_673 = (let _189_672 = (FStar_SMTEncoding_Term.hash_of_term app_tm)
in (FStar_Util.digest_of_string _189_672))
in (Prims.strcat "partial_app_typing_" _189_673))
in (varops.mk_unique _189_674))
in Some (_189_675))
in ((_189_677), (Some ("Partial app typing")), (_189_676))))
in FStar_SMTEncoding_Term.Assume (_189_678))
in ((app_tm), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' ((e_typing)::[]))))))))
end))))
end))
end))
end)))
in (

let encode_full_app = (fun fv -> (

let _91_978 = (lookup_free_var_sym env fv)
in (match (_91_978) with
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
(let _189_682 = (let _189_681 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _189_681 Prims.snd))
in Some (_189_682))
end
| FStar_Syntax_Syntax.Tm_ascribed (_91_1010, FStar_Util.Inl (t), _91_1014) -> begin
Some (t)
end
| FStar_Syntax_Syntax.Tm_ascribed (_91_1018, FStar_Util.Inr (c), _91_1022) -> begin
Some ((FStar_Syntax_Util.comp_result c))
end
| _91_1026 -> begin
None
end)
in (match (head_type) with
| None -> begin
(encode_partial_app None)
end
| Some (head_type) -> begin
(

let head_type = (let _189_683 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine _189_683))
in (

let _91_1034 = (curried_arrow_formals_comp head_type)
in (match (_91_1034) with
| (formals, c) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| _91_1050 -> begin
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

let _91_1059 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_91_1059) with
| (bs, body, opening) -> begin
(

let fallback = (fun _91_1061 -> (match (()) with
| () -> begin
(

let f = (varops.fresh "Tm_abs")
in (

let decl = FStar_SMTEncoding_Term.DeclFun (((f), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Imprecise function encoding"))))
in (let _189_686 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in ((_189_686), ((decl)::[])))))
end))
in (

let is_impure = (fun _91_10 -> (match (_91_10) with
| FStar_Util.Inl (lc) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)))
end
| FStar_Util.Inr (eff, _91_1069) -> begin
(let _189_689 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv eff)
in (FStar_All.pipe_right _189_689 Prims.op_Negation))
end))
in (

let codomain_eff = (fun lc -> (match (lc) with
| FStar_Util.Inl (lc) -> begin
(let _189_694 = (let _189_692 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening _189_692))
in (FStar_All.pipe_right _189_694 (fun _189_693 -> Some (_189_693))))
end
| FStar_Util.Inr (eff, flags) -> begin
(

let new_uvar = (fun _91_1082 -> (match (()) with
| () -> begin
(let _189_697 = (FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange [] FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _189_697 Prims.fst))
end))
in if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid) then begin
(let _189_700 = (let _189_698 = (new_uvar ())
in (FStar_Syntax_Syntax.mk_Total _189_698))
in (FStar_All.pipe_right _189_700 (fun _189_699 -> Some (_189_699))))
end else begin
if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid) then begin
(let _189_703 = (let _189_701 = (new_uvar ())
in (FStar_Syntax_Syntax.mk_GTotal _189_701))
in (FStar_All.pipe_right _189_703 (fun _189_702 -> Some (_189_702))))
end else begin
None
end
end)
end))
in (match (lopt) with
| None -> begin
(

let _91_1084 = (let _189_705 = (let _189_704 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s" _189_704))
in (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos _189_705))
in (fallback ()))
end
| Some (lc) -> begin
if (is_impure lc) then begin
(fallback ())
end else begin
(

let _91_1094 = (encode_binders None bs env)
in (match (_91_1094) with
| (vars, guards, envbody, decls, _91_1093) -> begin
(

let _91_1097 = (encode_term body envbody)
in (match (_91_1097) with
| (body, decls') -> begin
(

let key_body = (let _189_709 = (let _189_708 = (let _189_707 = (let _189_706 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((_189_706), (body)))
in (FStar_SMTEncoding_Util.mkImp _189_707))
in (([]), (vars), (_189_708)))
in (FStar_SMTEncoding_Util.mkForall _189_709))
in (

let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), (cvars), (key_body)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (match ((FStar_Util.smap_try_find env.cache tkey_hash)) with
| Some (t, _91_1104, _91_1106) -> begin
(let _189_712 = (let _189_711 = (let _189_710 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((t), (_189_710)))
in (FStar_SMTEncoding_Util.mkApp _189_711))
in ((_189_712), ([])))
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

let fsym = (let _189_714 = (let _189_713 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_abs_" _189_713))
in (varops.mk_unique _189_714))
in (

let fdecl = FStar_SMTEncoding_Term.DeclFun (((fsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let f = (let _189_716 = (let _189_715 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((fsym), (_189_715)))
in (FStar_SMTEncoding_Util.mkApp _189_716))
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

let _91_1124 = (encode_term_pred None tfun env f)
in (match (_91_1124) with
| (f_has_t, decls'') -> begin
(

let a_name = Some ((Prims.strcat "typing_" fsym))
in (let _189_720 = (let _189_719 = (let _189_718 = (let _189_717 = (FStar_SMTEncoding_Util.mkForall ((((f)::[])::[]), (cvars), (f_has_t)))
in ((_189_717), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_189_718))
in (_189_719)::[])
in (FStar_List.append decls'' _189_720)))
end)))
end)
in (

let interp_f = (

let a_name = Some ((Prims.strcat "interpretation_" fsym))
in (let _189_724 = (let _189_723 = (let _189_722 = (let _189_721 = (FStar_SMTEncoding_Util.mkEq ((app), (body)))
in ((((app)::[])::[]), ((FStar_List.append vars cvars)), (_189_721)))
in (FStar_SMTEncoding_Util.mkForall _189_722))
in ((_189_723), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_189_724)))
in (

let f_decls = (FStar_List.append decls (FStar_List.append decls' (FStar_List.append ((fdecl)::typing_f) ((interp_f)::[]))))
in (

let _91_1130 = (FStar_Util.smap_add env.cache tkey_hash ((fsym), (cvar_sorts), (f_decls)))
in ((f), (f_decls)))))))))))
end)
end)))))
end))
end))
end
end))))
end))
end
| FStar_Syntax_Syntax.Tm_let ((_91_1133, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_91_1145); FStar_Syntax_Syntax.lbunivs = _91_1143; FStar_Syntax_Syntax.lbtyp = _91_1141; FStar_Syntax_Syntax.lbeff = _91_1139; FStar_Syntax_Syntax.lbdef = _91_1137})::_91_1135), _91_1151) -> begin
(FStar_All.failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _91_1160; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _91_1157; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (_91_1170) -> begin
(

let _91_1172 = (FStar_TypeChecker_Errors.diag t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (

let e = (varops.fresh "let-rec")
in (

let decl_e = FStar_SMTEncoding_Term.DeclFun (((e), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (let _189_725 = (FStar_SMTEncoding_Util.mkFreeV ((e), (FStar_SMTEncoding_Term.Term_sort)))
in ((_189_725), ((decl_e)::[]))))))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end))))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (

let _91_1188 = (encode_term e1 env)
in (match (_91_1188) with
| (ee1, decls1) -> begin
(

let _91_1191 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) e2)
in (match (_91_1191) with
| (xs, e2) -> begin
(

let _91_1195 = (FStar_List.hd xs)
in (match (_91_1195) with
| (x, _91_1194) -> begin
(

let env' = (push_term_var env x ee1)
in (

let _91_1199 = (encode_body e2 env')
in (match (_91_1199) with
| (ee2, decls2) -> begin
((ee2), ((FStar_List.append decls1 decls2)))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (

let _91_1207 = (encode_term e env)
in (match (_91_1207) with
| (scr, decls) -> begin
(

let _91_1244 = (FStar_List.fold_right (fun b _91_1211 -> (match (_91_1211) with
| (else_case, decls) -> begin
(

let _91_1215 = (FStar_Syntax_Subst.open_branch b)
in (match (_91_1215) with
| (p, w, br) -> begin
(

let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun _91_1219 _91_1222 -> (match (((_91_1219), (_91_1222))) with
| ((env0, pattern), (else_case, decls)) -> begin
(

let guard = (pattern.guard scr)
in (

let projections = (pattern.projections scr)
in (

let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env _91_1228 -> (match (_91_1228) with
| (x, t) -> begin
(push_term_var env x t)
end)) env))
in (

let _91_1238 = (match (w) with
| None -> begin
((guard), ([]))
end
| Some (w) -> begin
(

let _91_1235 = (encode_term w env)
in (match (_91_1235) with
| (w, decls2) -> begin
(let _189_759 = (let _189_758 = (let _189_757 = (let _189_756 = (let _189_755 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue)
in ((w), (_189_755)))
in (FStar_SMTEncoding_Util.mkEq _189_756))
in ((guard), (_189_757)))
in (FStar_SMTEncoding_Util.mkAnd _189_758))
in ((_189_759), (decls2)))
end))
end)
in (match (_91_1238) with
| (guard, decls2) -> begin
(

let _91_1241 = (encode_br br env)
in (match (_91_1241) with
| (br, decls3) -> begin
(let _189_760 = (FStar_SMTEncoding_Util.mkITE ((guard), (br), (else_case)))
in ((_189_760), ((FStar_List.append decls (FStar_List.append decls2 decls3)))))
end))
end)))))
end)) patterns ((else_case), (decls))))
end))
end)) pats ((default_case), (decls)))
in (match (_91_1244) with
| (match_tm, decls) -> begin
((match_tm), (decls))
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _91_1250 -> begin
(let _189_763 = (encode_one_pat env pat)
in (_189_763)::[])
end))
and encode_one_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> (

let _91_1253 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _189_766 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" _189_766))
end else begin
()
end
in (

let _91_1257 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (_91_1257) with
| (vars, pat_term) -> begin
(

let _91_1269 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun _91_1260 v -> (match (_91_1260) with
| (env, vars) -> begin
(

let _91_1266 = (gen_term_var env v)
in (match (_91_1266) with
| (xx, _91_1264, env) -> begin
((env), ((((v), (((xx), (FStar_SMTEncoding_Term.Term_sort)))))::vars))
end))
end)) ((env), ([]))))
in (match (_91_1269) with
| (env, vars) -> begin
(

let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_91_1274) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_dot_term (_)) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _189_774 = (let _189_773 = (encode_const c)
in ((scrutinee), (_189_773)))
in (FStar_SMTEncoding_Util.mkEq _189_774))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let is_f = (mk_data_tester env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _91_1296 -> (match (_91_1296) with
| (arg, _91_1295) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _189_777 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_guard arg _189_777)))
end))))
in (FStar_SMTEncoding_Util.mk_and_l ((is_f)::sub_term_guards))))
end))
in (

let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_91_1303) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _)) | (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_constant (_91_1313) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(let _189_785 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _91_1323 -> (match (_91_1323) with
| (arg, _91_1322) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _189_784 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_projections arg _189_784)))
end))))
in (FStar_All.pipe_right _189_785 FStar_List.flatten))
end))
in (

let pat_term = (fun _91_1326 -> (match (()) with
| () -> begin
(encode_term pat_term env)
end))
in (

let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in ((env), (pattern))))))
end))
end))))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (

let _91_1342 = (FStar_All.pipe_right l (FStar_List.fold_left (fun _91_1332 _91_1336 -> (match (((_91_1332), (_91_1336))) with
| ((tms, decls), (t, _91_1335)) -> begin
(

let _91_1339 = (encode_term t env)
in (match (_91_1339) with
| (t, decls') -> begin
(((t)::tms), ((FStar_List.append decls decls')))
end))
end)) (([]), ([]))))
in (match (_91_1342) with
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

let _91_1352 = (FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern")
in [])
end))
in (

let one_pat = (fun p -> (

let _91_1358 = (let _189_800 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right _189_800 FStar_Syntax_Util.head_and_args))
in (match (_91_1358) with
| (head, args) -> begin
(match ((let _189_802 = (let _189_801 = (FStar_Syntax_Util.un_uinst head)
in _189_801.FStar_Syntax_Syntax.n)
in ((_189_802), (args)))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((_91_1366, _91_1368))::((e, _91_1363))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpat_lid) -> begin
((e), (None))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, _91_1376))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatT_lid) -> begin
((e), (None))
end
| _91_1381 -> begin
(FStar_All.failwith "Unexpected pattern term")
end)
end)))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements p)
in (

let smt_pat_or = (fun t -> (

let _91_1389 = (let _189_807 = (FStar_Syntax_Util.unmeta t)
in (FStar_All.pipe_right _189_807 FStar_Syntax_Util.head_and_args))
in (match (_91_1389) with
| (head, args) -> begin
(match ((let _189_809 = (let _189_808 = (FStar_Syntax_Util.un_uinst head)
in _189_808.FStar_Syntax_Syntax.n)
in ((_189_809), (args)))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, _91_1394))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatOr_lid) -> begin
Some (e)
end
| _91_1399 -> begin
None
end)
end)))
in (match (elts) with
| (t)::[] -> begin
(match ((smt_pat_or t)) with
| Some (e) -> begin
(let _189_812 = (list_elements e)
in (FStar_All.pipe_right _189_812 (FStar_List.map (fun branch -> (let _189_811 = (list_elements branch)
in (FStar_All.pipe_right _189_811 (FStar_List.map one_pat)))))))
end
| _91_1406 -> begin
(let _189_813 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_189_813)::[])
end)
end
| _91_1408 -> begin
(let _189_814 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_189_814)::[])
end))))
in (

let _91_1451 = (match ((let _189_815 = (FStar_Syntax_Subst.compress t)
in _189_815.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _91_1415 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_91_1415) with
| (binders, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = _91_1436; FStar_Syntax_Syntax.effect_name = _91_1434; FStar_Syntax_Syntax.result_typ = _91_1432; FStar_Syntax_Syntax.effect_args = ((pre, _91_1428))::((post, _91_1424))::((pats, _91_1420))::[]; FStar_Syntax_Syntax.flags = _91_1417}) -> begin
(

let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _189_816 = (lemma_pats pats')
in ((binders), (pre), (post), (_189_816))))
end
| _91_1444 -> begin
(FStar_All.failwith "impos")
end)
end))
end
| _91_1446 -> begin
(FStar_All.failwith "Impos")
end)
in (match (_91_1451) with
| (binders, pre, post, patterns) -> begin
(

let _91_1458 = (encode_binders None binders env)
in (match (_91_1458) with
| (vars, guards, env, decls, _91_1457) -> begin
(

let _91_1471 = (let _189_820 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (

let _91_1468 = (let _189_819 = (FStar_All.pipe_right branch (FStar_List.map (fun _91_1463 -> (match (_91_1463) with
| (t, _91_1462) -> begin
(encode_term t (

let _91_1464 = env
in {bindings = _91_1464.bindings; depth = _91_1464.depth; tcenv = _91_1464.tcenv; warn = _91_1464.warn; cache = _91_1464.cache; nolabels = _91_1464.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _91_1464.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _189_819 FStar_List.unzip))
in (match (_91_1468) with
| (pats, decls) -> begin
((pats), (decls))
end)))))
in (FStar_All.pipe_right _189_820 FStar_List.unzip))
in (match (_91_1471) with
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
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _189_823 = (let _189_822 = (FStar_SMTEncoding_Util.mkFreeV l)
in (FStar_SMTEncoding_Util.mk_Precedes _189_822 e))
in (_189_823)::p))))
end
| _91_1481 -> begin
(

let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _189_829 = (FStar_SMTEncoding_Util.mk_Precedes tl e)
in (_189_829)::p))))
end
| ((x, FStar_SMTEncoding_Term.Term_sort))::vars -> begin
(let _189_831 = (let _189_830 = (FStar_SMTEncoding_Util.mkFreeV ((x), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Util.mk_LexCons _189_830 tl))
in (aux _189_831 vars))
end
| _91_1493 -> begin
pats
end))
in (let _189_832 = (FStar_SMTEncoding_Util.mkFreeV (("Prims.LexTop"), (FStar_SMTEncoding_Term.Term_sort)))
in (aux _189_832 vars)))
end)
end)
in (

let env = (

let _91_1495 = env
in {bindings = _91_1495.bindings; depth = _91_1495.depth; tcenv = _91_1495.tcenv; warn = _91_1495.warn; cache = _91_1495.cache; nolabels = true; use_zfuel_name = _91_1495.use_zfuel_name; encode_non_total_function_typ = _91_1495.encode_non_total_function_typ})
in (

let _91_1500 = (let _189_833 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula _189_833 env))
in (match (_91_1500) with
| (pre, decls'') -> begin
(

let _91_1503 = (let _189_834 = (FStar_Syntax_Util.unmeta post)
in (encode_formula _189_834 env))
in (match (_91_1503) with
| (post, decls''') -> begin
(

let decls = (FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') (FStar_List.append decls'' decls''')))
in (let _189_839 = (let _189_838 = (let _189_837 = (let _189_836 = (let _189_835 = (FStar_SMTEncoding_Util.mk_and_l ((pre)::guards))
in ((_189_835), (post)))
in (FStar_SMTEncoding_Util.mkImp _189_836))
in ((pats), (vars), (_189_837)))
in (FStar_SMTEncoding_Util.mkForall _189_838))
in ((_189_839), (decls))))
end))
end)))))
end))
end))
end))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (

let debug = (fun phi -> if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _189_845 = (FStar_Syntax_Print.tag_of_term phi)
in (let _189_844 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print2 "Formula (%s)  %s\n" _189_845 _189_844)))
end else begin
()
end)
in (

let enc = (fun f r l -> (

let _91_1520 = (FStar_Util.fold_map (fun decls x -> (

let _91_1517 = (encode_term (Prims.fst x) env)
in (match (_91_1517) with
| (t, decls') -> begin
(((FStar_List.append decls decls')), (t))
end))) [] l)
in (match (_91_1520) with
| (decls, args) -> begin
(let _189_867 = (

let _91_1521 = (f args)
in {FStar_SMTEncoding_Term.tm = _91_1521.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = _91_1521.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((_189_867), (decls)))
end)))
in (

let const_op = (fun f r _91_1526 -> (let _189_879 = (f r)
in ((_189_879), ([]))))
in (

let un_op = (fun f l -> (let _189_889 = (FStar_List.hd l)
in (FStar_All.pipe_left f _189_889)))
in (

let bin_op = (fun f _91_11 -> (match (_91_11) with
| (t1)::(t2)::[] -> begin
(f ((t1), (t2)))
end
| _91_1537 -> begin
(FStar_All.failwith "Impossible")
end))
in (

let enc_prop_c = (fun f r l -> (

let _91_1553 = (FStar_Util.fold_map (fun decls _91_1547 -> (match (_91_1547) with
| (t, _91_1546) -> begin
(

let _91_1550 = (encode_formula t env)
in (match (_91_1550) with
| (phi, decls') -> begin
(((FStar_List.append decls decls')), (phi))
end))
end)) [] l)
in (match (_91_1553) with
| (decls, phis) -> begin
(let _189_920 = (

let _91_1554 = (f phis)
in {FStar_SMTEncoding_Term.tm = _91_1554.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = _91_1554.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((_189_920), (decls)))
end)))
in (

let eq_op = (fun r _91_12 -> (match (_91_12) with
| ((_)::(e1)::(e2)::[]) | ((_)::(_)::(e1)::(e2)::[]) -> begin
(enc (bin_op FStar_SMTEncoding_Util.mkEq) r ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op FStar_SMTEncoding_Util.mkEq) r l)
end))
in (

let mk_imp = (fun r _91_13 -> (match (_91_13) with
| ((lhs, _91_1579))::((rhs, _91_1575))::[] -> begin
(

let _91_1584 = (encode_formula rhs env)
in (match (_91_1584) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _91_1587) -> begin
((l1), (decls1))
end
| _91_1591 -> begin
(

let _91_1594 = (encode_formula lhs env)
in (match (_91_1594) with
| (l2, decls2) -> begin
(let _189_937 = (FStar_SMTEncoding_Term.mkImp ((l2), (l1)) r)
in ((_189_937), ((FStar_List.append decls1 decls2))))
end))
end)
end))
end
| _91_1596 -> begin
(FStar_All.failwith "impossible")
end))
in (

let mk_ite = (fun r _91_14 -> (match (_91_14) with
| ((guard, _91_1610))::((_then, _91_1606))::((_else, _91_1602))::[] -> begin
(

let _91_1615 = (encode_formula guard env)
in (match (_91_1615) with
| (g, decls1) -> begin
(

let _91_1618 = (encode_formula _then env)
in (match (_91_1618) with
| (t, decls2) -> begin
(

let _91_1621 = (encode_formula _else env)
in (match (_91_1621) with
| (e, decls3) -> begin
(

let res = (FStar_SMTEncoding_Term.mkITE ((g), (t), (e)) r)
in ((res), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end))
end))
end
| _91_1624 -> begin
(FStar_All.failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (let _189_955 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f _189_955)))
in (

let connectives = (let _189_1058 = (let _189_971 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd))
in ((FStar_Syntax_Const.and_lid), (_189_971)))
in (let _189_1057 = (let _189_1056 = (let _189_981 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr))
in ((FStar_Syntax_Const.or_lid), (_189_981)))
in (let _189_1055 = (let _189_1054 = (let _189_1053 = (let _189_999 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff))
in ((FStar_Syntax_Const.iff_lid), (_189_999)))
in (let _189_1052 = (let _189_1051 = (let _189_1050 = (let _189_1017 = (FStar_All.pipe_left enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot))
in ((FStar_Syntax_Const.not_lid), (_189_1017)))
in (_189_1050)::(((FStar_Syntax_Const.eq2_lid), (eq_op)))::(((FStar_Syntax_Const.eq3_lid), (eq_op)))::(((FStar_Syntax_Const.true_lid), ((const_op FStar_SMTEncoding_Term.mkTrue))))::(((FStar_Syntax_Const.false_lid), ((const_op FStar_SMTEncoding_Term.mkFalse))))::[])
in (((FStar_Syntax_Const.ite_lid), (mk_ite)))::_189_1051)
in (_189_1053)::_189_1052))
in (((FStar_Syntax_Const.imp_lid), (mk_imp)))::_189_1054)
in (_189_1056)::_189_1055))
in (_189_1058)::_189_1057))
in (

let rec fallback = (fun phi -> (match (phi.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(

let _91_1641 = (encode_formula phi' env)
in (match (_91_1641) with
| (phi, decls) -> begin
(let _189_1061 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled (((phi), (msg), (r)))) r)
in ((_189_1061), (decls)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (_91_1643) -> begin
(let _189_1062 = (FStar_Syntax_Util.unmeta phi)
in (encode_formula _189_1062 env))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(

let _91_1651 = (encode_match e pats FStar_SMTEncoding_Util.mkFalse env encode_formula)
in (match (_91_1651) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _91_1658; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _91_1655; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _91_1669 = (encode_let x t1 e1 e2 env encode_formula)
in (match (_91_1669) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let head = (FStar_Syntax_Util.un_uinst head)
in (match (((head.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_91_1686)::((x, _91_1683))::((t, _91_1679))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.has_type_lid) -> begin
(

let _91_1691 = (encode_term x env)
in (match (_91_1691) with
| (x, decls) -> begin
(

let _91_1694 = (encode_term t env)
in (match (_91_1694) with
| (t, decls') -> begin
(let _189_1063 = (FStar_SMTEncoding_Term.mk_HasType x t)
in ((_189_1063), ((FStar_List.append decls decls'))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((r, _91_1707))::((msg, _91_1703))::((phi, _91_1699))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.labeled_lid) -> begin
(match ((let _189_1067 = (let _189_1064 = (FStar_Syntax_Subst.compress r)
in _189_1064.FStar_Syntax_Syntax.n)
in (let _189_1066 = (let _189_1065 = (FStar_Syntax_Subst.compress msg)
in _189_1065.FStar_Syntax_Syntax.n)
in ((_189_1067), (_189_1066))))) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, _91_1716))) -> begin
(

let phi = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((phi), (FStar_Syntax_Syntax.Meta_labeled ((((FStar_Util.string_of_unicode s)), (r), (false))))))) None r)
in (fallback phi))
end
| _91_1723 -> begin
(fallback phi)
end)
end
| _91_1725 when (head_redex env head) -> begin
(let _189_1068 = (whnf env phi)
in (encode_formula _189_1068 env))
end
| _91_1727 -> begin
(

let _91_1730 = (encode_term phi env)
in (match (_91_1730) with
| (tt, decls) -> begin
(let _189_1069 = (FStar_SMTEncoding_Term.mk_Valid (

let _91_1731 = tt
in {FStar_SMTEncoding_Term.tm = _91_1731.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = _91_1731.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi.FStar_Syntax_Syntax.pos}))
in ((_189_1069), (decls)))
end))
end))
end
| _91_1734 -> begin
(

let _91_1737 = (encode_term phi env)
in (match (_91_1737) with
| (tt, decls) -> begin
(let _189_1070 = (FStar_SMTEncoding_Term.mk_Valid (

let _91_1738 = tt
in {FStar_SMTEncoding_Term.tm = _91_1738.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = _91_1738.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi.FStar_Syntax_Syntax.pos}))
in ((_189_1070), (decls)))
end))
end))
in (

let encode_q_body = (fun env bs ps body -> (

let _91_1751 = (encode_binders None bs env)
in (match (_91_1751) with
| (vars, guards, env, decls, _91_1750) -> begin
(

let _91_1764 = (let _189_1082 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let _91_1761 = (let _189_1081 = (FStar_All.pipe_right p (FStar_List.map (fun _91_1756 -> (match (_91_1756) with
| (t, _91_1755) -> begin
(encode_term t (

let _91_1757 = env
in {bindings = _91_1757.bindings; depth = _91_1757.depth; tcenv = _91_1757.tcenv; warn = _91_1757.warn; cache = _91_1757.cache; nolabels = _91_1757.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _91_1757.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _189_1081 FStar_List.unzip))
in (match (_91_1761) with
| (p, decls) -> begin
((p), ((FStar_List.flatten decls)))
end)))))
in (FStar_All.pipe_right _189_1082 FStar_List.unzip))
in (match (_91_1764) with
| (pats, decls') -> begin
(

let _91_1767 = (encode_formula body env)
in (match (_91_1767) with
| (body, decls'') -> begin
(

let guards = (match (pats) with
| (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (gf), (p)::[]); FStar_SMTEncoding_Term.freevars = _91_1771; FStar_SMTEncoding_Term.rng = _91_1769})::[])::[] when ((FStar_Ident.text_of_lid FStar_Syntax_Const.guard_free) = gf) -> begin
[]
end
| _91_1782 -> begin
guards
end)
in (let _189_1083 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((vars), (pats), (_189_1083), (body), ((FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') decls''))))))
end))
end))
end)))
in (

let _91_1784 = (debug phi)
in (

let phi = (FStar_Syntax_Util.unascribe phi)
in (

let check_pattern_vars = (fun vars pats -> (

let pats = (FStar_All.pipe_right pats (FStar_List.map (fun _91_1793 -> (match (_91_1793) with
| (x, _91_1792) -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x)
end))))
in (match (pats) with
| [] -> begin
()
end
| (hd)::tl -> begin
(

let pat_vars = (let _189_1092 = (FStar_Syntax_Free.names hd)
in (FStar_List.fold_left (fun out x -> (let _189_1091 = (FStar_Syntax_Free.names x)
in (FStar_Util.set_union out _189_1091))) _189_1092 tl))
in (match ((FStar_All.pipe_right vars (FStar_Util.find_opt (fun _91_1805 -> (match (_91_1805) with
| (b, _91_1804) -> begin
(not ((FStar_Util.set_mem b pat_vars)))
end))))) with
| None -> begin
()
end
| Some (x, _91_1809) -> begin
(

let pos = (FStar_List.fold_left (fun out t -> (FStar_Range.union_ranges out t.FStar_Syntax_Syntax.pos)) hd.FStar_Syntax_Syntax.pos tl)
in (let _189_1097 = (let _189_1096 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "SMT pattern misses at least one bound variable: %s" _189_1096))
in (FStar_TypeChecker_Errors.warn pos _189_1097)))
end))
end)))
in (match ((FStar_Syntax_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _91_1824 -> (match (_91_1824) with
| (l, _91_1823) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_91_1827, f) -> begin
(f phi.FStar_Syntax_Syntax.pos arms)
end)
end
| Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
(

let _91_1837 = (FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)))
in (

let _91_1844 = (encode_q_body env vars pats body)
in (match (_91_1844) with
| (vars, pats, guard, body, decls) -> begin
(

let tm = (let _189_1130 = (let _189_1129 = (FStar_SMTEncoding_Util.mkImp ((guard), (body)))
in ((pats), (vars), (_189_1129)))
in (FStar_SMTEncoding_Term.mkForall _189_1130 phi.FStar_Syntax_Syntax.pos))
in ((tm), (decls)))
end)))
end
| Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
(

let _91_1852 = (FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)))
in (

let _91_1859 = (encode_q_body env vars pats body)
in (match (_91_1859) with
| (vars, pats, guard, body, decls) -> begin
(let _189_1133 = (let _189_1132 = (let _189_1131 = (FStar_SMTEncoding_Util.mkAnd ((guard), (body)))
in ((pats), (vars), (_189_1131)))
in (FStar_SMTEncoding_Term.mkExists _189_1132 phi.FStar_Syntax_Syntax.pos))
in ((_189_1133), (decls)))
end)))
end))))))))))))))))))


type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list); is : FStar_Ident.lident  ->  Prims.bool}


let is_Mkprims_t : prims_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkprims_t"))))


let prims : prims_t = (

let _91_1865 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (_91_1865) with
| (asym, a) -> begin
(

let _91_1868 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_91_1868) with
| (xsym, x) -> begin
(

let _91_1871 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (_91_1871) with
| (ysym, y) -> begin
(

let quant = (fun vars body x -> (

let xname_decl = (let _189_1170 = (let _189_1169 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in ((x), (_189_1169), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (_189_1170))
in (

let xtok = (Prims.strcat x "@tok")
in (

let xtok_decl = FStar_SMTEncoding_Term.DeclFun (((xtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let xapp = (let _189_1172 = (let _189_1171 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((x), (_189_1171)))
in (FStar_SMTEncoding_Util.mkApp _189_1172))
in (

let xtok = (FStar_SMTEncoding_Util.mkApp ((xtok), ([])))
in (

let xtok_app = (mk_Apply xtok vars)
in (let _189_1186 = (let _189_1185 = (let _189_1184 = (let _189_1183 = (let _189_1176 = (let _189_1175 = (let _189_1174 = (let _189_1173 = (FStar_SMTEncoding_Util.mkEq ((xapp), (body)))
in ((((xapp)::[])::[]), (vars), (_189_1173)))
in (FStar_SMTEncoding_Util.mkForall _189_1174))
in ((_189_1175), (None), (Some ((Prims.strcat "primitive_" x)))))
in FStar_SMTEncoding_Term.Assume (_189_1176))
in (let _189_1182 = (let _189_1181 = (let _189_1180 = (let _189_1179 = (let _189_1178 = (let _189_1177 = (FStar_SMTEncoding_Util.mkEq ((xtok_app), (xapp)))
in ((((xtok_app)::[])::[]), (vars), (_189_1177)))
in (FStar_SMTEncoding_Util.mkForall _189_1178))
in ((_189_1179), (Some ("Name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" x)))))
in FStar_SMTEncoding_Term.Assume (_189_1180))
in (_189_1181)::[])
in (_189_1183)::_189_1182))
in (xtok_decl)::_189_1184)
in (xname_decl)::_189_1185)
in ((xtok), (_189_1186))))))))))
in (

let axy = (((asym), (FStar_SMTEncoding_Term.Term_sort)))::(((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let xy = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let qx = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let prims = (let _189_1346 = (let _189_1195 = (let _189_1194 = (let _189_1193 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _189_1193))
in (quant axy _189_1194))
in ((FStar_Syntax_Const.op_Eq), (_189_1195)))
in (let _189_1345 = (let _189_1344 = (let _189_1202 = (let _189_1201 = (let _189_1200 = (let _189_1199 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_SMTEncoding_Util.mkNot _189_1199))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _189_1200))
in (quant axy _189_1201))
in ((FStar_Syntax_Const.op_notEq), (_189_1202)))
in (let _189_1343 = (let _189_1342 = (let _189_1211 = (let _189_1210 = (let _189_1209 = (let _189_1208 = (let _189_1207 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _189_1206 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_189_1207), (_189_1206))))
in (FStar_SMTEncoding_Util.mkLT _189_1208))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _189_1209))
in (quant xy _189_1210))
in ((FStar_Syntax_Const.op_LT), (_189_1211)))
in (let _189_1341 = (let _189_1340 = (let _189_1220 = (let _189_1219 = (let _189_1218 = (let _189_1217 = (let _189_1216 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _189_1215 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_189_1216), (_189_1215))))
in (FStar_SMTEncoding_Util.mkLTE _189_1217))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _189_1218))
in (quant xy _189_1219))
in ((FStar_Syntax_Const.op_LTE), (_189_1220)))
in (let _189_1339 = (let _189_1338 = (let _189_1229 = (let _189_1228 = (let _189_1227 = (let _189_1226 = (let _189_1225 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _189_1224 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_189_1225), (_189_1224))))
in (FStar_SMTEncoding_Util.mkGT _189_1226))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _189_1227))
in (quant xy _189_1228))
in ((FStar_Syntax_Const.op_GT), (_189_1229)))
in (let _189_1337 = (let _189_1336 = (let _189_1238 = (let _189_1237 = (let _189_1236 = (let _189_1235 = (let _189_1234 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _189_1233 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_189_1234), (_189_1233))))
in (FStar_SMTEncoding_Util.mkGTE _189_1235))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _189_1236))
in (quant xy _189_1237))
in ((FStar_Syntax_Const.op_GTE), (_189_1238)))
in (let _189_1335 = (let _189_1334 = (let _189_1247 = (let _189_1246 = (let _189_1245 = (let _189_1244 = (let _189_1243 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _189_1242 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_189_1243), (_189_1242))))
in (FStar_SMTEncoding_Util.mkSub _189_1244))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _189_1245))
in (quant xy _189_1246))
in ((FStar_Syntax_Const.op_Subtraction), (_189_1247)))
in (let _189_1333 = (let _189_1332 = (let _189_1254 = (let _189_1253 = (let _189_1252 = (let _189_1251 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Util.mkMinus _189_1251))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _189_1252))
in (quant qx _189_1253))
in ((FStar_Syntax_Const.op_Minus), (_189_1254)))
in (let _189_1331 = (let _189_1330 = (let _189_1263 = (let _189_1262 = (let _189_1261 = (let _189_1260 = (let _189_1259 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _189_1258 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_189_1259), (_189_1258))))
in (FStar_SMTEncoding_Util.mkAdd _189_1260))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _189_1261))
in (quant xy _189_1262))
in ((FStar_Syntax_Const.op_Addition), (_189_1263)))
in (let _189_1329 = (let _189_1328 = (let _189_1272 = (let _189_1271 = (let _189_1270 = (let _189_1269 = (let _189_1268 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _189_1267 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_189_1268), (_189_1267))))
in (FStar_SMTEncoding_Util.mkMul _189_1269))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _189_1270))
in (quant xy _189_1271))
in ((FStar_Syntax_Const.op_Multiply), (_189_1272)))
in (let _189_1327 = (let _189_1326 = (let _189_1281 = (let _189_1280 = (let _189_1279 = (let _189_1278 = (let _189_1277 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _189_1276 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_189_1277), (_189_1276))))
in (FStar_SMTEncoding_Util.mkDiv _189_1278))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _189_1279))
in (quant xy _189_1280))
in ((FStar_Syntax_Const.op_Division), (_189_1281)))
in (let _189_1325 = (let _189_1324 = (let _189_1290 = (let _189_1289 = (let _189_1288 = (let _189_1287 = (let _189_1286 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _189_1285 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_189_1286), (_189_1285))))
in (FStar_SMTEncoding_Util.mkMod _189_1287))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _189_1288))
in (quant xy _189_1289))
in ((FStar_Syntax_Const.op_Modulus), (_189_1290)))
in (let _189_1323 = (let _189_1322 = (let _189_1299 = (let _189_1298 = (let _189_1297 = (let _189_1296 = (let _189_1295 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _189_1294 = (FStar_SMTEncoding_Term.unboxBool y)
in ((_189_1295), (_189_1294))))
in (FStar_SMTEncoding_Util.mkAnd _189_1296))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _189_1297))
in (quant xy _189_1298))
in ((FStar_Syntax_Const.op_And), (_189_1299)))
in (let _189_1321 = (let _189_1320 = (let _189_1308 = (let _189_1307 = (let _189_1306 = (let _189_1305 = (let _189_1304 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _189_1303 = (FStar_SMTEncoding_Term.unboxBool y)
in ((_189_1304), (_189_1303))))
in (FStar_SMTEncoding_Util.mkOr _189_1305))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _189_1306))
in (quant xy _189_1307))
in ((FStar_Syntax_Const.op_Or), (_189_1308)))
in (let _189_1319 = (let _189_1318 = (let _189_1315 = (let _189_1314 = (let _189_1313 = (let _189_1312 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Util.mkNot _189_1312))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _189_1313))
in (quant qx _189_1314))
in ((FStar_Syntax_Const.op_Negation), (_189_1315)))
in (_189_1318)::[])
in (_189_1320)::_189_1319))
in (_189_1322)::_189_1321))
in (_189_1324)::_189_1323))
in (_189_1326)::_189_1325))
in (_189_1328)::_189_1327))
in (_189_1330)::_189_1329))
in (_189_1332)::_189_1331))
in (_189_1334)::_189_1333))
in (_189_1336)::_189_1335))
in (_189_1338)::_189_1337))
in (_189_1340)::_189_1339))
in (_189_1342)::_189_1341))
in (_189_1344)::_189_1343))
in (_189_1346)::_189_1345))
in (

let mk = (fun l v -> (let _189_1393 = (let _189_1392 = (FStar_All.pipe_right prims (FStar_List.find (fun _91_1891 -> (match (_91_1891) with
| (l', _91_1890) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right _189_1392 (FStar_Option.map (fun _91_1895 -> (match (_91_1895) with
| (_91_1893, b) -> begin
(b v)
end)))))
in (FStar_All.pipe_right _189_1393 FStar_Option.get)))
in (

let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _91_1901 -> (match (_91_1901) with
| (l', _91_1900) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is})))))))
end))
end))
end))


let pretype_axiom : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun tapp vars -> (

let _91_1907 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_91_1907) with
| (xxsym, xx) -> begin
(

let _91_1910 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_91_1910) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let tapp_hash = (FStar_SMTEncoding_Term.hash_of_term tapp)
in (let _189_1423 = (let _189_1422 = (let _189_1417 = (let _189_1416 = (let _189_1415 = (let _189_1414 = (let _189_1413 = (let _189_1412 = (FStar_SMTEncoding_Util.mkApp (("PreType"), ((xx)::[])))
in ((tapp), (_189_1412)))
in (FStar_SMTEncoding_Util.mkEq _189_1413))
in ((xx_has_type), (_189_1414)))
in (FStar_SMTEncoding_Util.mkImp _189_1415))
in ((((xx_has_type)::[])::[]), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars), (_189_1416)))
in (FStar_SMTEncoding_Util.mkForall _189_1417))
in (let _189_1421 = (let _189_1420 = (let _189_1419 = (let _189_1418 = (FStar_Util.digest_of_string tapp_hash)
in (Prims.strcat "pretyping_" _189_1418))
in (varops.mk_unique _189_1419))
in Some (_189_1420))
in ((_189_1422), (Some ("pretyping")), (_189_1421))))
in FStar_SMTEncoding_Term.Assume (_189_1423))))
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
in (let _189_1444 = (let _189_1435 = (let _189_1434 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in ((_189_1434), (Some ("unit typing")), (Some ("unit_typing"))))
in FStar_SMTEncoding_Term.Assume (_189_1435))
in (let _189_1443 = (let _189_1442 = (let _189_1441 = (let _189_1440 = (let _189_1439 = (let _189_1438 = (let _189_1437 = (let _189_1436 = (FStar_SMTEncoding_Util.mkEq ((x), (FStar_SMTEncoding_Term.mk_Term_unit)))
in ((typing_pred), (_189_1436)))
in (FStar_SMTEncoding_Util.mkImp _189_1437))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_189_1438)))
in (mkForall_fuel _189_1439))
in ((_189_1440), (Some ("unit inversion")), (Some ("unit_inversion"))))
in FStar_SMTEncoding_Term.Assume (_189_1441))
in (_189_1442)::[])
in (_189_1444)::_189_1443))))
in (

let mk_bool = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Bool_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (let _189_1467 = (let _189_1458 = (let _189_1457 = (let _189_1456 = (let _189_1455 = (let _189_1452 = (let _189_1451 = (FStar_SMTEncoding_Term.boxBool b)
in (_189_1451)::[])
in (_189_1452)::[])
in (let _189_1454 = (let _189_1453 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType _189_1453 tt))
in ((_189_1455), ((bb)::[]), (_189_1454))))
in (FStar_SMTEncoding_Util.mkForall _189_1456))
in ((_189_1457), (Some ("bool typing")), (Some ("bool_typing"))))
in FStar_SMTEncoding_Term.Assume (_189_1458))
in (let _189_1466 = (let _189_1465 = (let _189_1464 = (let _189_1463 = (let _189_1462 = (let _189_1461 = (let _189_1460 = (let _189_1459 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in ((typing_pred), (_189_1459)))
in (FStar_SMTEncoding_Util.mkImp _189_1460))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_189_1461)))
in (mkForall_fuel _189_1462))
in ((_189_1463), (Some ("bool inversion")), (Some ("bool_inversion"))))
in FStar_SMTEncoding_Term.Assume (_189_1464))
in (_189_1465)::[])
in (_189_1467)::_189_1466))))))
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

let precedes = (let _189_1481 = (let _189_1480 = (let _189_1479 = (let _189_1478 = (let _189_1477 = (let _189_1476 = (FStar_SMTEncoding_Term.boxInt a)
in (let _189_1475 = (let _189_1474 = (FStar_SMTEncoding_Term.boxInt b)
in (_189_1474)::[])
in (_189_1476)::_189_1475))
in (tt)::_189_1477)
in (tt)::_189_1478)
in (("Prims.Precedes"), (_189_1479)))
in (FStar_SMTEncoding_Util.mkApp _189_1480))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _189_1481))
in (

let precedes_y_x = (let _189_1482 = (FStar_SMTEncoding_Util.mkApp (("Precedes"), ((y)::(x)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _189_1482))
in (let _189_1524 = (let _189_1490 = (let _189_1489 = (let _189_1488 = (let _189_1487 = (let _189_1484 = (let _189_1483 = (FStar_SMTEncoding_Term.boxInt b)
in (_189_1483)::[])
in (_189_1484)::[])
in (let _189_1486 = (let _189_1485 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType _189_1485 tt))
in ((_189_1487), ((bb)::[]), (_189_1486))))
in (FStar_SMTEncoding_Util.mkForall _189_1488))
in ((_189_1489), (Some ("int typing")), (Some ("int_typing"))))
in FStar_SMTEncoding_Term.Assume (_189_1490))
in (let _189_1523 = (let _189_1522 = (let _189_1496 = (let _189_1495 = (let _189_1494 = (let _189_1493 = (let _189_1492 = (let _189_1491 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in ((typing_pred), (_189_1491)))
in (FStar_SMTEncoding_Util.mkImp _189_1492))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_189_1493)))
in (mkForall_fuel _189_1494))
in ((_189_1495), (Some ("int inversion")), (Some ("int_inversion"))))
in FStar_SMTEncoding_Term.Assume (_189_1496))
in (let _189_1521 = (let _189_1520 = (let _189_1519 = (let _189_1518 = (let _189_1517 = (let _189_1516 = (let _189_1515 = (let _189_1514 = (let _189_1513 = (let _189_1512 = (let _189_1511 = (let _189_1510 = (let _189_1499 = (let _189_1498 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _189_1497 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((_189_1498), (_189_1497))))
in (FStar_SMTEncoding_Util.mkGT _189_1499))
in (let _189_1509 = (let _189_1508 = (let _189_1502 = (let _189_1501 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _189_1500 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((_189_1501), (_189_1500))))
in (FStar_SMTEncoding_Util.mkGTE _189_1502))
in (let _189_1507 = (let _189_1506 = (let _189_1505 = (let _189_1504 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _189_1503 = (FStar_SMTEncoding_Term.unboxInt x)
in ((_189_1504), (_189_1503))))
in (FStar_SMTEncoding_Util.mkLT _189_1505))
in (_189_1506)::[])
in (_189_1508)::_189_1507))
in (_189_1510)::_189_1509))
in (typing_pred_y)::_189_1511)
in (typing_pred)::_189_1512)
in (FStar_SMTEncoding_Util.mk_and_l _189_1513))
in ((_189_1514), (precedes_y_x)))
in (FStar_SMTEncoding_Util.mkImp _189_1515))
in ((((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[]), ((xx)::(yy)::[]), (_189_1516)))
in (mkForall_fuel _189_1517))
in ((_189_1518), (Some ("well-founded ordering on nat (alt)")), (Some ("well-founded-ordering-on-nat"))))
in FStar_SMTEncoding_Term.Assume (_189_1519))
in (_189_1520)::[])
in (_189_1522)::_189_1521))
in (_189_1524)::_189_1523)))))))))))
in (

let mk_str = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.String_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (let _189_1547 = (let _189_1538 = (let _189_1537 = (let _189_1536 = (let _189_1535 = (let _189_1532 = (let _189_1531 = (FStar_SMTEncoding_Term.boxString b)
in (_189_1531)::[])
in (_189_1532)::[])
in (let _189_1534 = (let _189_1533 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType _189_1533 tt))
in ((_189_1535), ((bb)::[]), (_189_1534))))
in (FStar_SMTEncoding_Util.mkForall _189_1536))
in ((_189_1537), (Some ("string typing")), (Some ("string_typing"))))
in FStar_SMTEncoding_Term.Assume (_189_1538))
in (let _189_1546 = (let _189_1545 = (let _189_1544 = (let _189_1543 = (let _189_1542 = (let _189_1541 = (let _189_1540 = (let _189_1539 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in ((typing_pred), (_189_1539)))
in (FStar_SMTEncoding_Util.mkImp _189_1540))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_189_1541)))
in (mkForall_fuel _189_1542))
in ((_189_1543), (Some ("string inversion")), (Some ("string_inversion"))))
in FStar_SMTEncoding_Term.Assume (_189_1544))
in (_189_1545)::[])
in (_189_1547)::_189_1546))))))
in (

let mk_ref = (fun env reft_name _91_1950 -> (

let r = (("r"), (FStar_SMTEncoding_Term.Ref_sort))
in (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let refa = (let _189_1556 = (let _189_1555 = (let _189_1554 = (FStar_SMTEncoding_Util.mkFreeV aa)
in (_189_1554)::[])
in ((reft_name), (_189_1555)))
in (FStar_SMTEncoding_Util.mkApp _189_1556))
in (

let refb = (let _189_1559 = (let _189_1558 = (let _189_1557 = (FStar_SMTEncoding_Util.mkFreeV bb)
in (_189_1557)::[])
in ((reft_name), (_189_1558)))
in (FStar_SMTEncoding_Util.mkApp _189_1559))
in (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (

let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (let _189_1578 = (let _189_1565 = (let _189_1564 = (let _189_1563 = (let _189_1562 = (let _189_1561 = (let _189_1560 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in ((typing_pred), (_189_1560)))
in (FStar_SMTEncoding_Util.mkImp _189_1561))
in ((((typing_pred)::[])::[]), ((xx)::(aa)::[]), (_189_1562)))
in (mkForall_fuel _189_1563))
in ((_189_1564), (Some ("ref inversion")), (Some ("ref_inversion"))))
in FStar_SMTEncoding_Term.Assume (_189_1565))
in (let _189_1577 = (let _189_1576 = (let _189_1575 = (let _189_1574 = (let _189_1573 = (let _189_1572 = (let _189_1571 = (let _189_1570 = (FStar_SMTEncoding_Util.mkAnd ((typing_pred), (typing_pred_b)))
in (let _189_1569 = (let _189_1568 = (let _189_1567 = (FStar_SMTEncoding_Util.mkFreeV aa)
in (let _189_1566 = (FStar_SMTEncoding_Util.mkFreeV bb)
in ((_189_1567), (_189_1566))))
in (FStar_SMTEncoding_Util.mkEq _189_1568))
in ((_189_1570), (_189_1569))))
in (FStar_SMTEncoding_Util.mkImp _189_1571))
in ((((typing_pred)::(typing_pred_b)::[])::[]), ((xx)::(aa)::(bb)::[]), (_189_1572)))
in (mkForall_fuel' (Prims.parse_int "2") _189_1573))
in ((_189_1574), (Some ("ref typing is injective")), (Some ("ref_injectivity"))))
in FStar_SMTEncoding_Term.Assume (_189_1575))
in (_189_1576)::[])
in (_189_1578)::_189_1577))))))))))
in (

let mk_true_interp = (fun env nm true_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((true_tm)::[])))
in (FStar_SMTEncoding_Term.Assume (((valid), (Some ("True interpretation")), (Some ("true_interp")))))::[]))
in (

let mk_false_interp = (fun env nm false_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((false_tm)::[])))
in (let _189_1593 = (let _189_1592 = (let _189_1591 = (FStar_SMTEncoding_Util.mkIff ((FStar_SMTEncoding_Util.mkFalse), (valid)))
in ((_189_1591), (Some ("False interpretation")), (Some ("false_interp"))))
in FStar_SMTEncoding_Term.Assume (_189_1592))
in (_189_1593)::[])))
in (

let mk_and_interp = (fun env conj _91_1972 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let valid = (let _189_1602 = (let _189_1601 = (let _189_1600 = (FStar_SMTEncoding_Util.mkApp ((conj), ((a)::(b)::[])))
in (_189_1600)::[])
in (("Valid"), (_189_1601)))
in (FStar_SMTEncoding_Util.mkApp _189_1602))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (let _189_1609 = (let _189_1608 = (let _189_1607 = (let _189_1606 = (let _189_1605 = (let _189_1604 = (let _189_1603 = (FStar_SMTEncoding_Util.mkAnd ((valid_a), (valid_b)))
in ((_189_1603), (valid)))
in (FStar_SMTEncoding_Util.mkIff _189_1604))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_189_1605)))
in (FStar_SMTEncoding_Util.mkForall _189_1606))
in ((_189_1607), (Some ("/\\ interpretation")), (Some ("l_and-interp"))))
in FStar_SMTEncoding_Term.Assume (_189_1608))
in (_189_1609)::[])))))))))
in (

let mk_or_interp = (fun env disj _91_1984 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let valid = (let _189_1618 = (let _189_1617 = (let _189_1616 = (FStar_SMTEncoding_Util.mkApp ((disj), ((a)::(b)::[])))
in (_189_1616)::[])
in (("Valid"), (_189_1617)))
in (FStar_SMTEncoding_Util.mkApp _189_1618))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (let _189_1625 = (let _189_1624 = (let _189_1623 = (let _189_1622 = (let _189_1621 = (let _189_1620 = (let _189_1619 = (FStar_SMTEncoding_Util.mkOr ((valid_a), (valid_b)))
in ((_189_1619), (valid)))
in (FStar_SMTEncoding_Util.mkIff _189_1620))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_189_1621)))
in (FStar_SMTEncoding_Util.mkForall _189_1622))
in ((_189_1623), (Some ("\\/ interpretation")), (Some ("l_or-interp"))))
in FStar_SMTEncoding_Term.Assume (_189_1624))
in (_189_1625)::[])))))))))
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

let valid = (let _189_1634 = (let _189_1633 = (let _189_1632 = (FStar_SMTEncoding_Util.mkApp ((eq2), ((a)::(x)::(y)::[])))
in (_189_1632)::[])
in (("Valid"), (_189_1633)))
in (FStar_SMTEncoding_Util.mkApp _189_1634))
in (let _189_1641 = (let _189_1640 = (let _189_1639 = (let _189_1638 = (let _189_1637 = (let _189_1636 = (let _189_1635 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in ((_189_1635), (valid)))
in (FStar_SMTEncoding_Util.mkIff _189_1636))
in ((((valid)::[])::[]), ((aa)::(xx)::(yy)::[]), (_189_1637)))
in (FStar_SMTEncoding_Util.mkForall _189_1638))
in ((_189_1639), (Some ("Eq2 interpretation")), (Some ("eq2-interp"))))
in FStar_SMTEncoding_Term.Assume (_189_1640))
in (_189_1641)::[])))))))))
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

let valid = (let _189_1650 = (let _189_1649 = (let _189_1648 = (FStar_SMTEncoding_Util.mkApp ((eq3), ((a)::(b)::(x)::(y)::[])))
in (_189_1648)::[])
in (("Valid"), (_189_1649)))
in (FStar_SMTEncoding_Util.mkApp _189_1650))
in (let _189_1657 = (let _189_1656 = (let _189_1655 = (let _189_1654 = (let _189_1653 = (let _189_1652 = (let _189_1651 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in ((_189_1651), (valid)))
in (FStar_SMTEncoding_Util.mkIff _189_1652))
in ((((valid)::[])::[]), ((aa)::(bb)::(xx)::(yy)::[]), (_189_1653)))
in (FStar_SMTEncoding_Util.mkForall _189_1654))
in ((_189_1655), (Some ("Eq3 interpretation")), (Some ("eq3-interp"))))
in FStar_SMTEncoding_Term.Assume (_189_1656))
in (_189_1657)::[])))))))))))
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

let valid = (let _189_1666 = (let _189_1665 = (let _189_1664 = (FStar_SMTEncoding_Util.mkApp ((imp), ((a)::(b)::[])))
in (_189_1664)::[])
in (("Valid"), (_189_1665)))
in (FStar_SMTEncoding_Util.mkApp _189_1666))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (let _189_1673 = (let _189_1672 = (let _189_1671 = (let _189_1670 = (let _189_1669 = (let _189_1668 = (let _189_1667 = (FStar_SMTEncoding_Util.mkImp ((valid_a), (valid_b)))
in ((_189_1667), (valid)))
in (FStar_SMTEncoding_Util.mkIff _189_1668))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_189_1669)))
in (FStar_SMTEncoding_Util.mkForall _189_1670))
in ((_189_1671), (Some ("==> interpretation")), (Some ("l_imp-interp"))))
in FStar_SMTEncoding_Term.Assume (_189_1672))
in (_189_1673)::[])))))))))
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

let valid = (let _189_1682 = (let _189_1681 = (let _189_1680 = (FStar_SMTEncoding_Util.mkApp ((iff), ((a)::(b)::[])))
in (_189_1680)::[])
in (("Valid"), (_189_1681)))
in (FStar_SMTEncoding_Util.mkApp _189_1682))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (let _189_1689 = (let _189_1688 = (let _189_1687 = (let _189_1686 = (let _189_1685 = (let _189_1684 = (let _189_1683 = (FStar_SMTEncoding_Util.mkIff ((valid_a), (valid_b)))
in ((_189_1683), (valid)))
in (FStar_SMTEncoding_Util.mkIff _189_1684))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_189_1685)))
in (FStar_SMTEncoding_Util.mkForall _189_1686))
in ((_189_1687), (Some ("<==> interpretation")), (Some ("l_iff-interp"))))
in FStar_SMTEncoding_Term.Assume (_189_1688))
in (_189_1689)::[])))))))))
in (

let mk_not_interp = (fun env l_not tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let valid = (let _189_1698 = (let _189_1697 = (let _189_1696 = (FStar_SMTEncoding_Util.mkApp ((l_not), ((a)::[])))
in (_189_1696)::[])
in (("Valid"), (_189_1697)))
in (FStar_SMTEncoding_Util.mkApp _189_1698))
in (

let not_valid_a = (let _189_1699 = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot _189_1699))
in (let _189_1704 = (let _189_1703 = (let _189_1702 = (let _189_1701 = (let _189_1700 = (FStar_SMTEncoding_Util.mkIff ((not_valid_a), (valid)))
in ((((valid)::[])::[]), ((aa)::[]), (_189_1700)))
in (FStar_SMTEncoding_Util.mkForall _189_1701))
in ((_189_1702), (Some ("not interpretation")), (Some ("l_not-interp"))))
in FStar_SMTEncoding_Term.Assume (_189_1703))
in (_189_1704)::[]))))))
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

let valid = (let _189_1713 = (let _189_1712 = (let _189_1711 = (FStar_SMTEncoding_Util.mkApp ((for_all), ((a)::(b)::[])))
in (_189_1711)::[])
in (("Valid"), (_189_1712)))
in (FStar_SMTEncoding_Util.mkApp _189_1713))
in (

let valid_b_x = (let _189_1716 = (let _189_1715 = (let _189_1714 = (FStar_SMTEncoding_Util.mk_ApplyTT b x)
in (_189_1714)::[])
in (("Valid"), (_189_1715)))
in (FStar_SMTEncoding_Util.mkApp _189_1716))
in (let _189_1730 = (let _189_1729 = (let _189_1728 = (let _189_1727 = (let _189_1726 = (let _189_1725 = (let _189_1724 = (let _189_1723 = (let _189_1722 = (let _189_1718 = (let _189_1717 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_189_1717)::[])
in (_189_1718)::[])
in (let _189_1721 = (let _189_1720 = (let _189_1719 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((_189_1719), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp _189_1720))
in ((_189_1722), ((xx)::[]), (_189_1721))))
in (FStar_SMTEncoding_Util.mkForall _189_1723))
in ((_189_1724), (valid)))
in (FStar_SMTEncoding_Util.mkIff _189_1725))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_189_1726)))
in (FStar_SMTEncoding_Util.mkForall _189_1727))
in ((_189_1728), (Some ("forall interpretation")), (Some ("forall-interp"))))
in FStar_SMTEncoding_Term.Assume (_189_1729))
in (_189_1730)::[]))))))))))
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

let valid = (let _189_1739 = (let _189_1738 = (let _189_1737 = (FStar_SMTEncoding_Util.mkApp ((for_some), ((a)::(b)::[])))
in (_189_1737)::[])
in (("Valid"), (_189_1738)))
in (FStar_SMTEncoding_Util.mkApp _189_1739))
in (

let valid_b_x = (let _189_1742 = (let _189_1741 = (let _189_1740 = (FStar_SMTEncoding_Util.mk_ApplyTT b x)
in (_189_1740)::[])
in (("Valid"), (_189_1741)))
in (FStar_SMTEncoding_Util.mkApp _189_1742))
in (let _189_1756 = (let _189_1755 = (let _189_1754 = (let _189_1753 = (let _189_1752 = (let _189_1751 = (let _189_1750 = (let _189_1749 = (let _189_1748 = (let _189_1744 = (let _189_1743 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_189_1743)::[])
in (_189_1744)::[])
in (let _189_1747 = (let _189_1746 = (let _189_1745 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((_189_1745), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp _189_1746))
in ((_189_1748), ((xx)::[]), (_189_1747))))
in (FStar_SMTEncoding_Util.mkExists _189_1749))
in ((_189_1750), (valid)))
in (FStar_SMTEncoding_Util.mkIff _189_1751))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_189_1752)))
in (FStar_SMTEncoding_Util.mkForall _189_1753))
in ((_189_1754), (Some ("exists interpretation")), (Some ("exists-interp"))))
in FStar_SMTEncoding_Term.Assume (_189_1755))
in (_189_1756)::[]))))))))))
in (

let mk_range_interp = (fun env range tt -> (

let range_ty = (FStar_SMTEncoding_Util.mkApp ((range), ([])))
in (let _189_1767 = (let _189_1766 = (let _189_1765 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_ty)
in (let _189_1764 = (let _189_1763 = (varops.mk_unique "typing_range_const")
in Some (_189_1763))
in ((_189_1765), (Some ("Range_const typing")), (_189_1764))))
in FStar_SMTEncoding_Term.Assume (_189_1766))
in (_189_1767)::[])))
in (

let prims = (((FStar_Syntax_Const.unit_lid), (mk_unit)))::(((FStar_Syntax_Const.bool_lid), (mk_bool)))::(((FStar_Syntax_Const.int_lid), (mk_int)))::(((FStar_Syntax_Const.string_lid), (mk_str)))::(((FStar_Syntax_Const.ref_lid), (mk_ref)))::(((FStar_Syntax_Const.true_lid), (mk_true_interp)))::(((FStar_Syntax_Const.false_lid), (mk_false_interp)))::(((FStar_Syntax_Const.and_lid), (mk_and_interp)))::(((FStar_Syntax_Const.or_lid), (mk_or_interp)))::(((FStar_Syntax_Const.eq2_lid), (mk_eq2_interp)))::(((FStar_Syntax_Const.eq3_lid), (mk_eq3_interp)))::(((FStar_Syntax_Const.imp_lid), (mk_imp_interp)))::(((FStar_Syntax_Const.iff_lid), (mk_iff_interp)))::(((FStar_Syntax_Const.not_lid), (mk_not_interp)))::(((FStar_Syntax_Const.forall_lid), (mk_forall_interp)))::(((FStar_Syntax_Const.exists_lid), (mk_exists_interp)))::(((FStar_Syntax_Const.range_lid), (mk_range_interp)))::[]
in (fun env t s tt -> (match ((FStar_Util.find_opt (fun _91_2085 -> (match (_91_2085) with
| (l, _91_2084) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_91_2088, f) -> begin
(f env s tt)
end))))))))))))))))))))))))


let encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let _91_2098 = (encode_function_type_as_formula None None t env)
in (match (_91_2098) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_SMTEncoding_Term.Assume (((form), (Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str))), (Some ((Prims.strcat "lemma_" lid.FStar_Ident.str))))))::[]))
end))))


let encode_free_var : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env fv tt t_norm quals -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if ((let _189_1984 = (FStar_Syntax_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _189_1984)) || (FStar_Syntax_Util.is_lemma t_norm)) then begin
(

let _91_2108 = (new_term_constant_and_tok_from_lid env lid)
in (match (_91_2108) with
| (vname, vtok, env) -> begin
(

let arg_sorts = (match ((let _189_1985 = (FStar_Syntax_Subst.compress t_norm)
in _189_1985.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _91_2111) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun _91_2114 -> FStar_SMTEncoding_Term.Term_sort)))
end
| _91_2117 -> begin
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

let _91_2124 = (prims.mk lid vname)
in (match (_91_2124) with
| (tok, definition) -> begin
(

let env = (push_free_var env lid vname (Some (tok)))
in ((definition), (env)))
end)))
end else begin
(

let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (

let _91_2134 = (

let _91_2129 = (curried_arrow_formals_comp t_norm)
in (match (_91_2129) with
| (args, comp) -> begin
if encode_non_total_function_typ then begin
(let _189_1987 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in ((args), (_189_1987)))
end else begin
((args), (((None), ((FStar_Syntax_Util.comp_result comp)))))
end
end))
in (match (_91_2134) with
| (formals, (pre_opt, res_t)) -> begin
(

let _91_2138 = (new_term_constant_and_tok_from_lid env lid)
in (match (_91_2138) with
| (vname, vtok, env) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
end
| _91_2141 -> begin
(FStar_SMTEncoding_Util.mkApp ((vtok), ([])))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun _91_15 -> (match (_91_15) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(

let _91_2157 = (FStar_Util.prefix vars)
in (match (_91_2157) with
| (_91_2152, (xxsym, _91_2155)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (let _189_2004 = (let _189_2003 = (let _189_2002 = (let _189_2001 = (let _189_2000 = (let _189_1999 = (let _189_1998 = (let _189_1997 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _189_1997))
in ((vapp), (_189_1998)))
in (FStar_SMTEncoding_Util.mkEq _189_1999))
in ((((vapp)::[])::[]), (vars), (_189_2000)))
in (FStar_SMTEncoding_Util.mkForall _189_2001))
in ((_189_2002), (Some ("Discriminator equation")), (Some ((Prims.strcat "disc_equation_" (escape d.FStar_Ident.str))))))
in FStar_SMTEncoding_Term.Assume (_189_2003))
in (_189_2004)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(

let _91_2169 = (FStar_Util.prefix vars)
in (match (_91_2169) with
| (_91_2164, (xxsym, _91_2167)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (

let tp_name = (mk_term_projector_name d f)
in (

let prim_app = (FStar_SMTEncoding_Util.mkApp ((tp_name), ((xx)::[])))
in (let _189_2009 = (let _189_2008 = (let _189_2007 = (let _189_2006 = (let _189_2005 = (FStar_SMTEncoding_Util.mkEq ((vapp), (prim_app)))
in ((((vapp)::[])::[]), (vars), (_189_2005)))
in (FStar_SMTEncoding_Util.mkForall _189_2006))
in ((_189_2007), (Some ("Projector equation")), (Some ((Prims.strcat "proj_equation_" tp_name)))))
in FStar_SMTEncoding_Term.Assume (_189_2008))
in (_189_2009)::[])))))
end))
end
| _91_2175 -> begin
[]
end)))))
in (

let _91_2182 = (encode_binders None formals env)
in (match (_91_2182) with
| (vars, guards, env', decls1, _91_2181) -> begin
(

let _91_2191 = (match (pre_opt) with
| None -> begin
(let _189_2010 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((_189_2010), (decls1)))
end
| Some (p) -> begin
(

let _91_2188 = (encode_formula p env')
in (match (_91_2188) with
| (g, ds) -> begin
(let _189_2011 = (FStar_SMTEncoding_Util.mk_and_l ((g)::guards))
in ((_189_2011), ((FStar_List.append decls1 ds))))
end))
end)
in (match (_91_2191) with
| (guard, decls1) -> begin
(

let vtok_app = (mk_Apply vtok_tm vars)
in (

let vapp = (let _189_2013 = (let _189_2012 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((vname), (_189_2012)))
in (FStar_SMTEncoding_Util.mkApp _189_2013))
in (

let _91_2215 = (

let vname_decl = (let _189_2016 = (let _189_2015 = (FStar_All.pipe_right formals (FStar_List.map (fun _91_2194 -> FStar_SMTEncoding_Term.Term_sort)))
in ((vname), (_189_2015), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (_189_2016))
in (

let _91_2202 = (

let env = (

let _91_2197 = env
in {bindings = _91_2197.bindings; depth = _91_2197.depth; tcenv = _91_2197.tcenv; warn = _91_2197.warn; cache = _91_2197.cache; nolabels = _91_2197.nolabels; use_zfuel_name = _91_2197.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in if (not ((head_normal env tt))) then begin
(encode_term_pred None tt env vtok_tm)
end else begin
(encode_term_pred None t_norm env vtok_tm)
end)
in (match (_91_2202) with
| (tok_typing, decls2) -> begin
(

let tok_typing = FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("function token typing")), (Some ((Prims.strcat "function_token_typing_" vname)))))
in (

let _91_2212 = (match (formals) with
| [] -> begin
(let _189_2020 = (let _189_2019 = (let _189_2018 = (FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left (fun _189_2017 -> Some (_189_2017)) _189_2018))
in (push_free_var env lid vname _189_2019))
in (((FStar_List.append decls2 ((tok_typing)::[]))), (_189_2020)))
end
| _91_2206 -> begin
(

let vtok_decl = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let vtok_fresh = (let _189_2021 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((vtok), (FStar_SMTEncoding_Term.Term_sort)) _189_2021))
in (

let name_tok_corr = (let _189_2025 = (let _189_2024 = (let _189_2023 = (let _189_2022 = (FStar_SMTEncoding_Util.mkEq ((vtok_app), (vapp)))
in ((((vtok_app)::[])::((vapp)::[])::[]), (vars), (_189_2022)))
in (FStar_SMTEncoding_Util.mkForall _189_2023))
in ((_189_2024), (Some ("Name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" vname)))))
in FStar_SMTEncoding_Term.Assume (_189_2025))
in (((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[]))), (env)))))
end)
in (match (_91_2212) with
| (tok_decl, env) -> begin
(((vname_decl)::tok_decl), (env))
end)))
end)))
in (match (_91_2215) with
| (decls2, env) -> begin
(

let _91_2223 = (

let res_t = (FStar_Syntax_Subst.compress res_t)
in (

let _91_2219 = (encode_term res_t env')
in (match (_91_2219) with
| (encoded_res_t, decls) -> begin
(let _189_2026 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in ((encoded_res_t), (_189_2026), (decls)))
end)))
in (match (_91_2223) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (let _189_2030 = (let _189_2029 = (let _189_2028 = (let _189_2027 = (FStar_SMTEncoding_Util.mkImp ((guard), (ty_pred)))
in ((((vapp)::[])::[]), (vars), (_189_2027)))
in (FStar_SMTEncoding_Util.mkForall _189_2028))
in ((_189_2029), (Some ("free var typing")), (Some ((Prims.strcat "typing_" vname)))))
in FStar_SMTEncoding_Term.Assume (_189_2030))
in (

let freshness = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New)) then begin
(let _189_2036 = (let _189_2033 = (let _189_2032 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (let _189_2031 = (varops.next_id ())
in ((vname), (_189_2032), (FStar_SMTEncoding_Term.Term_sort), (_189_2031))))
in (FStar_SMTEncoding_Term.fresh_constructor _189_2033))
in (let _189_2035 = (let _189_2034 = (pretype_axiom vapp vars)
in (_189_2034)::[])
in (_189_2036)::_189_2035))
end else begin
[]
end
in (

let g = (let _189_2041 = (let _189_2040 = (let _189_2039 = (let _189_2038 = (let _189_2037 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_189_2037)
in (FStar_List.append freshness _189_2038))
in (FStar_List.append decls3 _189_2039))
in (FStar_List.append decls2 _189_2040))
in (FStar_List.append decls1 _189_2041))
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

let _91_2234 = (encode_free_var env x t t_norm [])
in (match (_91_2234) with
| (decls, env) -> begin
(

let _91_2239 = (lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_91_2239) with
| (n, x', _91_2238) -> begin
((((n), (x'))), (decls), (env))
end))
end))
end
| Some (n, x, _91_2243) -> begin
((((n), (x))), ([]), (env))
end))


let encode_top_level_val : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env lid t quals -> (

let tt = (norm env t)
in (

let _91_2253 = (encode_free_var env lid t tt quals)
in (match (_91_2253) with
| (decls, env) -> begin
if (FStar_Syntax_Util.is_smt_lemma t) then begin
(let _189_2059 = (let _189_2058 = (encode_smt_lemma env lid tt)
in (FStar_List.append decls _189_2058))
in ((_189_2059), (env)))
end else begin
((decls), (env))
end
end))))


let encode_top_level_vals : env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _91_2259 lb -> (match (_91_2259) with
| (decls, env) -> begin
(

let _91_2263 = (let _189_2068 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env _189_2068 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (_91_2263) with
| (decls', env) -> begin
(((FStar_List.append decls decls')), (env))
end))
end)) (([]), (env)))))


let encode_top_level_let : env_t  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env _91_2267 quals -> (match (_91_2267) with
| (is_rec, bindings) -> begin
(

let eta_expand = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let _91_2277 = (FStar_Util.first_N nbinders formals)
in (match (_91_2277) with
| (formals, extra_formals) -> begin
(

let subst = (FStar_List.map2 (fun _91_2281 _91_2285 -> (match (((_91_2281), (_91_2285))) with
| ((formal, _91_2280), (binder, _91_2284)) -> begin
(let _189_2086 = (let _189_2085 = (FStar_Syntax_Syntax.bv_to_name binder)
in ((formal), (_189_2085)))
in FStar_Syntax_Syntax.NT (_189_2086))
end)) formals binders)
in (

let extra_formals = (let _189_2090 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun _91_2289 -> (match (_91_2289) with
| (x, i) -> begin
(let _189_2089 = (

let _91_2290 = x
in (let _189_2088 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _91_2290.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _91_2290.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _189_2088}))
in ((_189_2089), (i)))
end))))
in (FStar_All.pipe_right _189_2090 FStar_Syntax_Util.name_binders))
in (

let body = (let _189_2097 = (FStar_Syntax_Subst.compress body)
in (let _189_2096 = (let _189_2091 = (FStar_Syntax_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _189_2091))
in (let _189_2095 = (let _189_2094 = (let _189_2093 = (FStar_Syntax_Subst.subst subst t)
in _189_2093.FStar_Syntax_Syntax.n)
in (FStar_All.pipe_left (fun _189_2092 -> Some (_189_2092)) _189_2094))
in (FStar_Syntax_Syntax.extend_app_n _189_2097 _189_2096 _189_2095 body.FStar_Syntax_Syntax.pos))))
in (((FStar_List.append binders extra_formals)), (body)))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (

let rec aux = (fun norm t_norm -> (match ((let _189_2108 = (FStar_Syntax_Util.unascribe e)
in _189_2108.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, lopt) -> begin
(

let _91_2309 = (FStar_Syntax_Subst.open_term' binders body)
in (match (_91_2309) with
| (binders, body, opening) -> begin
(match ((let _189_2109 = (FStar_Syntax_Subst.compress t_norm)
in _189_2109.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let _91_2316 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_91_2316) with
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

let _91_2323 = (FStar_Util.first_N nformals binders)
in (match (_91_2323) with
| (bs0, rest) -> begin
(

let c = (

let subst = (FStar_List.map2 (fun _91_2327 _91_2331 -> (match (((_91_2327), (_91_2331))) with
| ((b, _91_2326), (x, _91_2330)) -> begin
(let _189_2113 = (let _189_2112 = (FStar_Syntax_Syntax.bv_to_name x)
in ((b), (_189_2112)))
in FStar_Syntax_Syntax.NT (_189_2113))
end)) bs0 formals)
in (FStar_Syntax_Subst.subst_comp subst c))
in (

let body = (FStar_Syntax_Util.abs rest body lopt)
in ((((bs0), (body), (bs0), ((FStar_Syntax_Util.comp_result c)))), (false))))
end)))
end else begin
if (nformals > nbinders) then begin
(

let _91_2337 = (eta_expand binders formals body tres)
in (match (_91_2337) with
| (binders, body) -> begin
((((binders), (body), (formals), (tres))), (false))
end))
end else begin
((((binders), (body), (formals), (tres))), (false))
end
end)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, _91_2340) -> begin
(let _189_2115 = (let _189_2114 = (aux norm x.FStar_Syntax_Syntax.sort)
in (Prims.fst _189_2114))
in ((_189_2115), (true)))
end
| _91_2344 when (not (norm)) -> begin
(

let t_norm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm)
in (aux true t_norm))
end
| _91_2347 -> begin
(let _189_2118 = (let _189_2117 = (FStar_Syntax_Print.term_to_string e)
in (let _189_2116 = (FStar_Syntax_Print.term_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str _189_2117 _189_2116)))
in (FStar_All.failwith _189_2118))
end)
end))
end
| _91_2349 -> begin
(match ((let _189_2119 = (FStar_Syntax_Subst.compress t_norm)
in _189_2119.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let _91_2356 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_91_2356) with
| (formals, c) -> begin
(

let tres = (FStar_Syntax_Util.comp_result c)
in (

let _91_2360 = (eta_expand [] formals e tres)
in (match (_91_2360) with
| (binders, body) -> begin
((((binders), (body), (formals), (tres))), (false))
end)))
end))
end
| _91_2362 -> begin
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

let _91_2390 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _91_2377 lb -> (match (_91_2377) with
| (toks, typs, decls, env) -> begin
(

let _91_2379 = if (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) then begin
(Prims.raise Let_rec_unencodeable)
end else begin
()
end
in (

let t_norm = (whnf env lb.FStar_Syntax_Syntax.lbtyp)
in (

let _91_2385 = (let _189_2124 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env _189_2124 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (_91_2385) with
| (tok, decl, env) -> begin
(let _189_2127 = (let _189_2126 = (let _189_2125 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in ((_189_2125), (tok)))
in (_189_2126)::toks)
in ((_189_2127), ((t_norm)::typs), ((decl)::decls), (env)))
end))))
end)) (([]), ([]), ([]), (env))))
in (match (_91_2390) with
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
| _91_2401 -> begin
if curry then begin
(match (ftok) with
| Some (ftok) -> begin
(mk_Apply ftok vars)
end
| None -> begin
(let _189_2136 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply _189_2136 vars))
end)
end else begin
(let _189_2138 = (let _189_2137 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (_189_2137)))
in (FStar_SMTEncoding_Util.mkApp _189_2138))
end
end))
in if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _91_16 -> (match (_91_16) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| _91_2408 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> (let _189_2141 = (FStar_Syntax_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _189_2141)))))) then begin
((decls), (env))
end else begin
if (not (is_rec)) then begin
(match (((bindings), (typs), (toks))) with
| (({FStar_Syntax_Syntax.lbname = _91_2418; FStar_Syntax_Syntax.lbunivs = _91_2416; FStar_Syntax_Syntax.lbtyp = _91_2414; FStar_Syntax_Syntax.lbeff = _91_2412; FStar_Syntax_Syntax.lbdef = e})::[], (t_norm)::[], ((flid_fv, (f, ftok)))::[]) -> begin
(

let e = (FStar_Syntax_Subst.compress e)
in (

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let _91_2440 = (destruct_bound_function flid t_norm e)
in (match (_91_2440) with
| ((binders, body, _91_2435, _91_2437), curry) -> begin
(

let _91_2447 = (encode_binders None binders env)
in (match (_91_2447) with
| (vars, guards, env', binder_decls, _91_2446) -> begin
(

let app = (mk_app curry f ftok vars)
in (

let _91_2453 = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic)) then begin
(let _189_2143 = (FStar_SMTEncoding_Term.mk_Valid app)
in (let _189_2142 = (encode_formula body env')
in ((_189_2143), (_189_2142))))
end else begin
(let _189_2144 = (encode_term body env')
in ((app), (_189_2144)))
end
in (match (_91_2453) with
| (app, (body, decls2)) -> begin
(

let eqn = (let _189_2150 = (let _189_2149 = (let _189_2146 = (let _189_2145 = (FStar_SMTEncoding_Util.mkEq ((app), (body)))
in ((((app)::[])::[]), (vars), (_189_2145)))
in (FStar_SMTEncoding_Util.mkForall _189_2146))
in (let _189_2148 = (let _189_2147 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (_189_2147))
in ((_189_2149), (_189_2148), (Some ((Prims.strcat "equation_" f))))))
in FStar_SMTEncoding_Term.Assume (_189_2150))
in (let _189_2155 = (let _189_2154 = (let _189_2153 = (let _189_2152 = (let _189_2151 = (primitive_type_axioms env.tcenv flid f app)
in (FStar_List.append ((eqn)::[]) _189_2151))
in (FStar_List.append decls2 _189_2152))
in (FStar_List.append binder_decls _189_2153))
in (FStar_List.append decls _189_2154))
in ((_189_2155), (env))))
end)))
end))
end))))
end
| _91_2456 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(

let fuel = (let _189_2156 = (varops.fresh "fuel")
in ((_189_2156), (FStar_SMTEncoding_Term.Fuel_sort)))
in (

let fuel_tm = (FStar_SMTEncoding_Util.mkFreeV fuel)
in (

let env0 = env
in (

let _91_2474 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _91_2462 _91_2467 -> (match (((_91_2462), (_91_2467))) with
| ((gtoks, env), (flid_fv, (f, ftok))) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let g = (let _189_2159 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented")
in (varops.new_fvar _189_2159))
in (

let gtok = (let _189_2160 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented_token")
in (varops.new_fvar _189_2160))
in (

let env = (let _189_2163 = (let _189_2162 = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::[])))
in (FStar_All.pipe_left (fun _189_2161 -> Some (_189_2161)) _189_2162))
in (push_free_var env flid gtok _189_2163))
in (((((flid), (f), (ftok), (g), (gtok)))::gtoks), (env))))))
end)) (([]), (env))))
in (match (_91_2474) with
| (gtoks, env) -> begin
(

let gtoks = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env0 _91_2483 t_norm _91_2494 -> (match (((_91_2483), (_91_2494))) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = _91_2493; FStar_Syntax_Syntax.lbunivs = _91_2491; FStar_Syntax_Syntax.lbtyp = _91_2489; FStar_Syntax_Syntax.lbeff = _91_2487; FStar_Syntax_Syntax.lbdef = e}) -> begin
(

let _91_2501 = (destruct_bound_function flid t_norm e)
in (match (_91_2501) with
| ((binders, body, formals, tres), curry) -> begin
(

let _91_2502 = if curry then begin
(FStar_All.failwith "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type")
end else begin
()
end
in (

let _91_2510 = (encode_binders None binders env)
in (match (_91_2510) with
| (vars, guards, env', binder_decls, _91_2509) -> begin
(

let decl_g = (let _189_2174 = (let _189_2173 = (let _189_2172 = (FStar_List.map Prims.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::_189_2172)
in ((g), (_189_2173), (FStar_SMTEncoding_Term.Term_sort), (Some ("Fuel-instrumented function name"))))
in FStar_SMTEncoding_Term.DeclFun (_189_2174))
in (

let env0 = (push_zfuel_name env0 flid g)
in (

let decl_g_tok = FStar_SMTEncoding_Term.DeclFun (((gtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Token for fuel-instrumented partial applications"))))
in (

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let app = (let _189_2176 = (let _189_2175 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (_189_2175)))
in (FStar_SMTEncoding_Util.mkApp _189_2176))
in (

let gsapp = (let _189_2179 = (let _189_2178 = (let _189_2177 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (_189_2177)::vars_tm)
in ((g), (_189_2178)))
in (FStar_SMTEncoding_Util.mkApp _189_2179))
in (

let gmax = (let _189_2182 = (let _189_2181 = (let _189_2180 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (_189_2180)::vars_tm)
in ((g), (_189_2181)))
in (FStar_SMTEncoding_Util.mkApp _189_2182))
in (

let _91_2520 = (encode_term body env')
in (match (_91_2520) with
| (body_tm, decls2) -> begin
(

let eqn_g = (let _189_2188 = (let _189_2187 = (let _189_2184 = (let _189_2183 = (FStar_SMTEncoding_Util.mkEq ((gsapp), (body_tm)))
in ((((gsapp)::[])::[]), (Some ((Prims.parse_int "0"))), ((fuel)::vars), (_189_2183)))
in (FStar_SMTEncoding_Util.mkForall' _189_2184))
in (let _189_2186 = (let _189_2185 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (_189_2185))
in ((_189_2187), (_189_2186), (Some ((Prims.strcat "equation_with_fuel_" g))))))
in FStar_SMTEncoding_Term.Assume (_189_2188))
in (

let eqn_f = (let _189_2192 = (let _189_2191 = (let _189_2190 = (let _189_2189 = (FStar_SMTEncoding_Util.mkEq ((app), (gmax)))
in ((((app)::[])::[]), (vars), (_189_2189)))
in (FStar_SMTEncoding_Util.mkForall _189_2190))
in ((_189_2191), (Some ("Correspondence of recursive function to instrumented version")), (Some ((Prims.strcat "fuel_correspondence_" g)))))
in FStar_SMTEncoding_Term.Assume (_189_2192))
in (

let eqn_g' = (let _189_2201 = (let _189_2200 = (let _189_2199 = (let _189_2198 = (let _189_2197 = (let _189_2196 = (let _189_2195 = (let _189_2194 = (let _189_2193 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "0"))
in (_189_2193)::vars_tm)
in ((g), (_189_2194)))
in (FStar_SMTEncoding_Util.mkApp _189_2195))
in ((gsapp), (_189_2196)))
in (FStar_SMTEncoding_Util.mkEq _189_2197))
in ((((gsapp)::[])::[]), ((fuel)::vars), (_189_2198)))
in (FStar_SMTEncoding_Util.mkForall _189_2199))
in ((_189_2200), (Some ("Fuel irrelevance")), (Some ((Prims.strcat "fuel_irrelevance_" g)))))
in FStar_SMTEncoding_Term.Assume (_189_2201))
in (

let _91_2543 = (

let _91_2530 = (encode_binders None formals env0)
in (match (_91_2530) with
| (vars, v_guards, env, binder_decls, _91_2529) -> begin
(

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let gapp = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::vars_tm)))
in (

let tok_corr = (

let tok_app = (let _189_2202 = (FStar_SMTEncoding_Util.mkFreeV ((gtok), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply _189_2202 ((fuel)::vars)))
in (let _189_2206 = (let _189_2205 = (let _189_2204 = (let _189_2203 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (gapp)))
in ((((tok_app)::[])::[]), ((fuel)::vars), (_189_2203)))
in (FStar_SMTEncoding_Util.mkForall _189_2204))
in ((_189_2205), (Some ("Fuel token correspondence")), (Some ((Prims.strcat "fuel_token_correspondence_" gtok)))))
in FStar_SMTEncoding_Term.Assume (_189_2206)))
in (

let _91_2540 = (

let _91_2537 = (encode_term_pred None tres env gapp)
in (match (_91_2537) with
| (g_typing, d3) -> begin
(let _189_2214 = (let _189_2213 = (let _189_2212 = (let _189_2211 = (let _189_2210 = (let _189_2209 = (let _189_2208 = (let _189_2207 = (FStar_SMTEncoding_Util.mk_and_l v_guards)
in ((_189_2207), (g_typing)))
in (FStar_SMTEncoding_Util.mkImp _189_2208))
in ((((gapp)::[])::[]), ((fuel)::vars), (_189_2209)))
in (FStar_SMTEncoding_Util.mkForall _189_2210))
in ((_189_2211), (Some ("Typing correspondence of token to term")), (Some ((Prims.strcat "token_correspondence_" g)))))
in FStar_SMTEncoding_Term.Assume (_189_2212))
in (_189_2213)::[])
in ((d3), (_189_2214)))
end))
in (match (_91_2540) with
| (aux_decls, typing_corr) -> begin
(((FStar_List.append binder_decls aux_decls)), ((FStar_List.append typing_corr ((tok_corr)::[]))))
end)))))
end))
in (match (_91_2543) with
| (aux_decls, g_typing) -> begin
(((FStar_List.append binder_decls (FStar_List.append decls2 (FStar_List.append aux_decls ((decl_g)::(decl_g_tok)::[]))))), ((FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing)), (env0))
end)))))
end)))))))))
end)))
end))
end))
in (

let _91_2559 = (let _189_2217 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _91_2547 _91_2551 -> (match (((_91_2547), (_91_2551))) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(

let _91_2555 = (encode_one_binding env0 gtok ty bs)
in (match (_91_2555) with
| (decls', eqns', env0) -> begin
(((decls')::decls), ((FStar_List.append eqns' eqns)), (env0))
end))
end)) (((decls)::[]), ([]), (env0)) _189_2217))
in (match (_91_2559) with
| (decls, eqns, env0) -> begin
(

let _91_2568 = (let _189_2219 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _189_2219 (FStar_List.partition (fun _91_17 -> (match (_91_17) with
| FStar_SMTEncoding_Term.DeclFun (_91_2562) -> begin
true
end
| _91_2565 -> begin
false
end)))))
in (match (_91_2568) with
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

let msg = (let _189_2222 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _189_2222 (FStar_String.concat " and ")))
in (

let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in (((decl)::[]), (env))))
end))
end))


let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let _91_2572 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _189_2231 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _189_2231))
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

let _91_2580 = (encode_sigelt' env se)
in (match (_91_2580) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _189_2234 = (let _189_2233 = (let _189_2232 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (_189_2232))
in (_189_2233)::[])
in ((_189_2234), (e)))
end
| _91_2583 -> begin
(let _189_2241 = (let _189_2240 = (let _189_2236 = (let _189_2235 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_189_2235))
in (_189_2236)::g)
in (let _189_2239 = (let _189_2238 = (let _189_2237 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_189_2237))
in (_189_2238)::[])
in (FStar_List.append _189_2240 _189_2239)))
in ((_189_2241), (e)))
end)
end)))))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let should_skip = (fun l -> false)
in (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_91_2589) -> begin
(FStar_All.failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _91_2605) -> begin
if (let _189_2246 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right _189_2246 Prims.op_Negation)) then begin
(([]), (env))
end else begin
(

let close_effect_params = (fun tm -> (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
tm
end
| _91_2612 -> begin
(let _189_2252 = (let _189_2251 = (let _189_2250 = (FStar_All.pipe_left (fun _189_2249 -> Some (_189_2249)) (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[])))))
in ((ed.FStar_Syntax_Syntax.binders), (tm), (_189_2250)))
in FStar_Syntax_Syntax.Tm_abs (_189_2251))
in (FStar_Syntax_Syntax.mk _189_2252 None tm.FStar_Syntax_Syntax.pos))
end))
in (

let encode_action = (fun env a -> (

let _91_2619 = (new_term_constant_and_tok_from_lid env a.FStar_Syntax_Syntax.action_name)
in (match (_91_2619) with
| (aname, atok, env) -> begin
(

let _91_2623 = (FStar_Syntax_Util.arrow_formals_comp a.FStar_Syntax_Syntax.action_typ)
in (match (_91_2623) with
| (formals, _91_2622) -> begin
(

let _91_2626 = (let _189_2257 = (close_effect_params a.FStar_Syntax_Syntax.action_defn)
in (encode_term _189_2257 env))
in (match (_91_2626) with
| (tm, decls) -> begin
(

let a_decls = (let _189_2261 = (let _189_2260 = (let _189_2259 = (FStar_All.pipe_right formals (FStar_List.map (fun _91_2627 -> FStar_SMTEncoding_Term.Term_sort)))
in ((aname), (_189_2259), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action"))))
in FStar_SMTEncoding_Term.DeclFun (_189_2260))
in (_189_2261)::(FStar_SMTEncoding_Term.DeclFun (((atok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action token")))))::[])
in (

let _91_2641 = (let _189_2263 = (FStar_All.pipe_right formals (FStar_List.map (fun _91_2633 -> (match (_91_2633) with
| (bv, _91_2632) -> begin
(

let _91_2638 = (gen_term_var env bv)
in (match (_91_2638) with
| (xxsym, xx, _91_2637) -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (xx))
end))
end))))
in (FStar_All.pipe_right _189_2263 FStar_List.split))
in (match (_91_2641) with
| (xs_sorts, xs) -> begin
(

let app = (let _189_2266 = (let _189_2265 = (let _189_2264 = (FStar_SMTEncoding_Util.mkApp ((aname), (xs)))
in (_189_2264)::[])
in (("Reify"), (_189_2265)))
in (FStar_SMTEncoding_Util.mkApp _189_2266))
in (

let a_eq = (let _189_2272 = (let _189_2271 = (let _189_2270 = (let _189_2269 = (let _189_2268 = (let _189_2267 = (mk_Apply tm xs_sorts)
in ((app), (_189_2267)))
in (FStar_SMTEncoding_Util.mkEq _189_2268))
in ((((app)::[])::[]), (xs_sorts), (_189_2269)))
in (FStar_SMTEncoding_Util.mkForall _189_2270))
in ((_189_2271), (Some ("Action equality")), (Some ((Prims.strcat aname "_equality")))))
in FStar_SMTEncoding_Term.Assume (_189_2272))
in (

let tok_correspondence = (

let tok_term = (FStar_SMTEncoding_Util.mkFreeV ((atok), (FStar_SMTEncoding_Term.Term_sort)))
in (

let tok_app = (mk_Apply tok_term xs_sorts)
in (let _189_2276 = (let _189_2275 = (let _189_2274 = (let _189_2273 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (app)))
in ((((tok_app)::[])::[]), (xs_sorts), (_189_2273)))
in (FStar_SMTEncoding_Util.mkForall _189_2274))
in ((_189_2275), (Some ("Action token correspondence")), (Some ((Prims.strcat aname "_token_correspondence")))))
in FStar_SMTEncoding_Term.Assume (_189_2276))))
in ((env), ((FStar_List.append decls (FStar_List.append a_decls ((a_eq)::(tok_correspondence)::[]))))))))
end)))
end))
end))
end)))
in (

let _91_2649 = (FStar_Util.fold_map encode_action env ed.FStar_Syntax_Syntax.actions)
in (match (_91_2649) with
| (env, decls2) -> begin
(((FStar_List.flatten decls2)), (env))
end))))
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _91_2652, _91_2654, _91_2656, _91_2658) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid) -> begin
(

let _91_2664 = (new_term_constant_and_tok_from_lid env lid)
in (match (_91_2664) with
| (tname, ttok, env) -> begin
(([]), (env))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _91_2667, t, quals, _91_2671) -> begin
(

let will_encode_definition = (not ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _91_18 -> (match (_91_18) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Irreducible) -> begin
true
end
| _91_2684 -> begin
false
end))))))
in if will_encode_definition then begin
(([]), (env))
end else begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (

let _91_2689 = (encode_top_level_val env fv t quals)
in (match (_91_2689) with
| (decls, env) -> begin
(

let tname = lid.FStar_Ident.str
in (

let tsym = (FStar_SMTEncoding_Util.mkFreeV ((tname), (FStar_SMTEncoding_Term.Term_sort)))
in (let _189_2279 = (let _189_2278 = (primitive_type_axioms env.tcenv lid tname tsym)
in (FStar_List.append decls _189_2278))
in ((_189_2279), (env)))))
end)))
end)
end
| FStar_Syntax_Syntax.Sig_assume (l, f, _91_2695, _91_2697) -> begin
(

let _91_2702 = (encode_formula f env)
in (match (_91_2702) with
| (f, decls) -> begin
(

let g = (let _189_2286 = (let _189_2285 = (let _189_2284 = (let _189_2281 = (let _189_2280 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" _189_2280))
in Some (_189_2281))
in (let _189_2283 = (let _189_2282 = (varops.mk_unique (Prims.strcat "assumption_" l.FStar_Ident.str))
in Some (_189_2282))
in ((f), (_189_2284), (_189_2283))))
in FStar_SMTEncoding_Term.Assume (_189_2285))
in (_189_2286)::[])
in (((FStar_List.append decls g)), (env)))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _91_2707, quals, _91_2710) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) -> begin
(

let _91_2722 = (FStar_Util.fold_map (fun env lb -> (

let lid = (let _189_2290 = (let _189_2289 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _189_2289.FStar_Syntax_Syntax.fv_name)
in _189_2290.FStar_Syntax_Syntax.v)
in if (let _189_2291 = (FStar_TypeChecker_Env.try_lookup_val_decl env.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone _189_2291)) then begin
(

let val_decl = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), (r)))
in (

let _91_2719 = (encode_sigelt' env val_decl)
in (match (_91_2719) with
| (decls, env) -> begin
((env), (decls))
end)))
end else begin
((env), ([]))
end)) env (Prims.snd lbs))
in (match (_91_2722) with
| (env, decls) -> begin
(((FStar_List.flatten decls)), (env))
end))
end
| FStar_Syntax_Syntax.Sig_let ((_91_2724, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t); FStar_Syntax_Syntax.lbunivs = _91_2732; FStar_Syntax_Syntax.lbtyp = _91_2730; FStar_Syntax_Syntax.lbeff = _91_2728; FStar_Syntax_Syntax.lbdef = _91_2726})::[]), _91_2739, _91_2741, _91_2743, _91_2745) when (FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Syntax_Const.b2t_lid) -> begin
(

let _91_2751 = (new_term_constant_and_tok_from_lid env b2t.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_91_2751) with
| (tname, ttok, env) -> begin
(

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let valid_b2t_x = (let _189_2294 = (let _189_2293 = (let _189_2292 = (FStar_SMTEncoding_Util.mkApp (("Prims.b2t"), ((x)::[])))
in (_189_2292)::[])
in (("Valid"), (_189_2293)))
in (FStar_SMTEncoding_Util.mkApp _189_2294))
in (

let decls = (let _189_2302 = (let _189_2301 = (let _189_2300 = (let _189_2299 = (let _189_2298 = (let _189_2297 = (let _189_2296 = (let _189_2295 = (FStar_SMTEncoding_Util.mkApp (("BoxBool_proj_0"), ((x)::[])))
in ((valid_b2t_x), (_189_2295)))
in (FStar_SMTEncoding_Util.mkEq _189_2296))
in ((((valid_b2t_x)::[])::[]), ((xx)::[]), (_189_2297)))
in (FStar_SMTEncoding_Util.mkForall _189_2298))
in ((_189_2299), (Some ("b2t def")), (Some ("b2t_def"))))
in FStar_SMTEncoding_Term.Assume (_189_2300))
in (_189_2301)::[])
in (FStar_SMTEncoding_Term.DeclFun (((tname), ((FStar_SMTEncoding_Term.Term_sort)::[]), (FStar_SMTEncoding_Term.Term_sort), (None))))::_189_2302)
in ((decls), (env))))))
end))
end
| FStar_Syntax_Syntax.Sig_let (_91_2757, _91_2759, _91_2761, quals, _91_2764) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _91_19 -> (match (_91_19) with
| FStar_Syntax_Syntax.Discriminator (_91_2769) -> begin
true
end
| _91_2772 -> begin
false
end)))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let (_91_2774, _91_2776, lids, quals, _91_2780) when ((FStar_All.pipe_right lids (FStar_Util.for_some (fun l -> ((let _189_2305 = (FStar_List.hd l.FStar_Ident.ns)
in _189_2305.FStar_Ident.idText) = "Prims")))) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun _91_20 -> (match (_91_20) with
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
true
end
| _91_2787 -> begin
false
end))))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _91_2793, _91_2795, quals, _91_2798) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _91_21 -> (match (_91_21) with
| FStar_Syntax_Syntax.Projector (_91_2803) -> begin
true
end
| _91_2806 -> begin
false
end)))) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((try_lookup_free_var env l)) with
| Some (_91_2810) -> begin
(([]), (env))
end
| None -> begin
(

let se = FStar_Syntax_Syntax.Sig_declare_typ (((l), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), ((FStar_Ident.range_of_lid l))))
in (encode_sigelt env se))
end)))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _91_2819, _91_2821, quals, _91_2824) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) -> begin
(match ((let _189_2308 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef)
in _189_2308.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, _91_2830) -> begin
(

let body = (FStar_Syntax_Util.mk_reify body)
in (

let tm = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None)))) None lb.FStar_Syntax_Syntax.lbdef.FStar_Syntax_Syntax.pos)
in (

let tm' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env.tcenv tm)
in (

let lb_typ = (

let _91_2838 = (FStar_Syntax_Util.arrow_formals_comp lb.FStar_Syntax_Syntax.lbtyp)
in (match (_91_2838) with
| (formals, comp) -> begin
(

let reified_typ = (FStar_TypeChecker_Util.reify_comp (

let _91_2839 = env.tcenv
in {FStar_TypeChecker_Env.solver = _91_2839.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _91_2839.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _91_2839.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _91_2839.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _91_2839.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _91_2839.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _91_2839.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _91_2839.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _91_2839.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _91_2839.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _91_2839.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _91_2839.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _91_2839.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _91_2839.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _91_2839.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _91_2839.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _91_2839.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _91_2839.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _91_2839.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _91_2839.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _91_2839.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _91_2839.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _91_2839.FStar_TypeChecker_Env.qname_and_index}) (FStar_Syntax_Util.lcomp_of_comp comp) FStar_Syntax_Syntax.U_unknown)
in (let _189_2309 = (FStar_Syntax_Syntax.mk_Total reified_typ)
in (FStar_Syntax_Util.arrow formals _189_2309)))
end))
in (

let lb = (

let _91_2843 = lb
in {FStar_Syntax_Syntax.lbname = _91_2843.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _91_2843.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lb_typ; FStar_Syntax_Syntax.lbeff = _91_2843.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = tm'})
in (encode_top_level_let env ((false), ((lb)::[])) quals))))))
end
| _91_2847 -> begin
(([]), (env))
end)
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), _91_2852, _91_2854, quals, _91_2857) -> begin
(encode_top_level_let env ((is_rec), (bindings)) quals)
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _91_2862, _91_2864, _91_2866) -> begin
(

let _91_2871 = (encode_signature env ses)
in (match (_91_2871) with
| (g, env) -> begin
(

let _91_2885 = (FStar_All.pipe_right g (FStar_List.partition (fun _91_22 -> (match (_91_22) with
| FStar_SMTEncoding_Term.Assume (_91_2874, Some ("inversion axiom"), _91_2878) -> begin
false
end
| _91_2882 -> begin
true
end))))
in (match (_91_2885) with
| (g', inversions) -> begin
(

let _91_2894 = (FStar_All.pipe_right g' (FStar_List.partition (fun _91_23 -> (match (_91_23) with
| FStar_SMTEncoding_Term.DeclFun (_91_2888) -> begin
true
end
| _91_2891 -> begin
false
end))))
in (match (_91_2894) with
| (decls, rest) -> begin
(((FStar_List.append decls (FStar_List.append rest inversions))), (env))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, _91_2897, tps, k, _91_2901, datas, quals, _91_2905) -> begin
(

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _91_24 -> (match (_91_24) with
| (FStar_Syntax_Syntax.Logic) | (FStar_Syntax_Syntax.Assumption) -> begin
true
end
| _91_2912 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(

let _91_2924 = c
in (match (_91_2924) with
| (name, args, _91_2919, _91_2921, _91_2923) -> begin
(let _189_2317 = (let _189_2316 = (let _189_2315 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in ((name), (_189_2315), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (_189_2316))
in (_189_2317)::[])
end))
end else begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end)
in (

let inversion_axioms = (fun tapp vars -> if (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _189_2323 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right _189_2323 FStar_Option.isNone))))) then begin
[]
end else begin
(

let _91_2931 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_91_2931) with
| (xxsym, xx) -> begin
(

let _91_2967 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _91_2934 l -> (match (_91_2934) with
| (out, decls) -> begin
(

let _91_2939 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (_91_2939) with
| (_91_2937, data_t) -> begin
(

let _91_2942 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (_91_2942) with
| (args, res) -> begin
(

let indices = (match ((let _189_2326 = (FStar_Syntax_Subst.compress res)
in _189_2326.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_91_2944, indices) -> begin
indices
end
| _91_2949 -> begin
[]
end)
in (

let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env _91_2955 -> (match (_91_2955) with
| (x, _91_2954) -> begin
(let _189_2331 = (let _189_2330 = (let _189_2329 = (mk_term_projector_name l x)
in ((_189_2329), ((xx)::[])))
in (FStar_SMTEncoding_Util.mkApp _189_2330))
in (push_term_var env x _189_2331))
end)) env))
in (

let _91_2959 = (encode_args indices env)
in (match (_91_2959) with
| (indices, decls') -> begin
(

let _91_2960 = if ((FStar_List.length indices) <> (FStar_List.length vars)) then begin
(FStar_All.failwith "Impossible")
end else begin
()
end
in (

let eqs = (let _189_2336 = (FStar_List.map2 (fun v a -> (let _189_2335 = (let _189_2334 = (FStar_SMTEncoding_Util.mkFreeV v)
in ((_189_2334), (a)))
in (FStar_SMTEncoding_Util.mkEq _189_2335))) vars indices)
in (FStar_All.pipe_right _189_2336 FStar_SMTEncoding_Util.mk_and_l))
in (let _189_2341 = (let _189_2340 = (let _189_2339 = (let _189_2338 = (let _189_2337 = (mk_data_tester env l xx)
in ((_189_2337), (eqs)))
in (FStar_SMTEncoding_Util.mkAnd _189_2338))
in ((out), (_189_2339)))
in (FStar_SMTEncoding_Util.mkOr _189_2340))
in ((_189_2341), ((FStar_List.append decls decls'))))))
end))))
end))
end))
end)) ((FStar_SMTEncoding_Util.mkFalse), ([]))))
in (match (_91_2967) with
| (data_ax, decls) -> begin
(

let _91_2970 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_91_2970) with
| (ffsym, ff) -> begin
(

let fuel_guarded_inversion = (

let xx_has_type_sfuel = if ((FStar_List.length datas) > (Prims.parse_int "1")) then begin
(let _189_2342 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((ff)::[])))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel _189_2342 xx tapp))
end else begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end
in (let _189_2349 = (let _189_2348 = (let _189_2345 = (let _189_2344 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (let _189_2343 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_sfuel), (data_ax)))
in ((((xx_has_type_sfuel)::[])::[]), (_189_2344), (_189_2343))))
in (FStar_SMTEncoding_Util.mkForall _189_2345))
in (let _189_2347 = (let _189_2346 = (varops.mk_unique (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str))
in Some (_189_2346))
in ((_189_2348), (Some ("inversion axiom")), (_189_2347))))
in FStar_SMTEncoding_Term.Assume (_189_2349)))
in (

let pattern_guarded_inversion = if ((contains_name env "Prims.inversion") && ((FStar_List.length datas) > (Prims.parse_int "1"))) then begin
(

let xx_has_type_fuel = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let pattern_guard = (FStar_SMTEncoding_Util.mkApp (("Prims.inversion"), ((tapp)::[])))
in (let _189_2357 = (let _189_2356 = (let _189_2355 = (let _189_2352 = (let _189_2351 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (let _189_2350 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_fuel), (data_ax)))
in ((((xx_has_type_fuel)::(pattern_guard)::[])::[]), (_189_2351), (_189_2350))))
in (FStar_SMTEncoding_Util.mkForall _189_2352))
in (let _189_2354 = (let _189_2353 = (varops.mk_unique (Prims.strcat "pattern_guarded_inversion_" t.FStar_Ident.str))
in Some (_189_2353))
in ((_189_2355), (Some ("inversion axiom")), (_189_2354))))
in FStar_SMTEncoding_Term.Assume (_189_2356))
in (_189_2357)::[])))
end else begin
[]
end
in (FStar_List.append decls (FStar_List.append ((fuel_guarded_inversion)::[]) pattern_guarded_inversion))))
end))
end))
end))
end)
in (

let _91_2984 = (match ((let _189_2358 = (FStar_Syntax_Subst.compress k)
in _189_2358.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
(((FStar_List.append tps formals)), ((FStar_Syntax_Util.comp_result kres)))
end
| _91_2981 -> begin
((tps), (k))
end)
in (match (_91_2984) with
| (formals, res) -> begin
(

let _91_2987 = (FStar_Syntax_Subst.open_term formals res)
in (match (_91_2987) with
| (formals, res) -> begin
(

let _91_2994 = (encode_binders None formals env)
in (match (_91_2994) with
| (vars, guards, env', binder_decls, _91_2993) -> begin
(

let _91_2998 = (new_term_constant_and_tok_from_lid env t)
in (match (_91_2998) with
| (tname, ttok, env) -> begin
(

let ttok_tm = (FStar_SMTEncoding_Util.mkApp ((ttok), ([])))
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let tapp = (let _189_2360 = (let _189_2359 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((tname), (_189_2359)))
in (FStar_SMTEncoding_Util.mkApp _189_2360))
in (

let _91_3019 = (

let tname_decl = (let _189_2364 = (let _189_2363 = (FStar_All.pipe_right vars (FStar_List.map (fun _91_3004 -> (match (_91_3004) with
| (n, s) -> begin
(((Prims.strcat tname n)), (s))
end))))
in (let _189_2362 = (varops.next_id ())
in ((tname), (_189_2363), (FStar_SMTEncoding_Term.Term_sort), (_189_2362), (false))))
in (constructor_or_logic_type_decl _189_2364))
in (

let _91_3016 = (match (vars) with
| [] -> begin
(let _189_2368 = (let _189_2367 = (let _189_2366 = (FStar_SMTEncoding_Util.mkApp ((tname), ([])))
in (FStar_All.pipe_left (fun _189_2365 -> Some (_189_2365)) _189_2366))
in (push_free_var env t tname _189_2367))
in (([]), (_189_2368)))
end
| _91_3008 -> begin
(

let ttok_decl = FStar_SMTEncoding_Term.DeclFun (((ttok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("token"))))
in (

let ttok_fresh = (let _189_2369 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ttok), (FStar_SMTEncoding_Term.Term_sort)) _189_2369))
in (

let ttok_app = (mk_Apply ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (let _189_2373 = (let _189_2372 = (let _189_2371 = (let _189_2370 = (FStar_SMTEncoding_Util.mkEq ((ttok_app), (tapp)))
in ((pats), (None), (vars), (_189_2370)))
in (FStar_SMTEncoding_Util.mkForall' _189_2371))
in ((_189_2372), (Some ("name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" ttok)))))
in FStar_SMTEncoding_Term.Assume (_189_2373))
in (((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[]), (env)))))))
end)
in (match (_91_3016) with
| (tok_decls, env) -> begin
(((FStar_List.append tname_decl tok_decls)), (env))
end)))
in (match (_91_3019) with
| (decls, env) -> begin
(

let kindingAx = (

let _91_3022 = (encode_term_pred None res env' tapp)
in (match (_91_3022) with
| (k, decls) -> begin
(

let karr = if ((FStar_List.length formals) > (Prims.parse_int "0")) then begin
(let _189_2377 = (let _189_2376 = (let _189_2375 = (let _189_2374 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _189_2374))
in ((_189_2375), (Some ("kinding")), (Some ((Prims.strcat "pre_kinding_" ttok)))))
in FStar_SMTEncoding_Term.Assume (_189_2376))
in (_189_2377)::[])
end else begin
[]
end
in (let _189_2384 = (let _189_2383 = (let _189_2382 = (let _189_2381 = (let _189_2380 = (let _189_2379 = (let _189_2378 = (FStar_SMTEncoding_Util.mkImp ((guard), (k)))
in ((((tapp)::[])::[]), (vars), (_189_2378)))
in (FStar_SMTEncoding_Util.mkForall _189_2379))
in ((_189_2380), (None), (Some ((Prims.strcat "kinding_" ttok)))))
in FStar_SMTEncoding_Term.Assume (_189_2381))
in (_189_2382)::[])
in (FStar_List.append karr _189_2383))
in (FStar_List.append decls _189_2384)))
end))
in (

let aux = (let _189_2388 = (let _189_2387 = (inversion_axioms tapp vars)
in (let _189_2386 = (let _189_2385 = (pretype_axiom tapp vars)
in (_189_2385)::[])
in (FStar_List.append _189_2387 _189_2386)))
in (FStar_List.append kindingAx _189_2388))
in (

let g = (FStar_List.append decls (FStar_List.append binder_decls aux))
in ((g), (env)))))
end)))))
end))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, _91_3029, _91_3031, _91_3033, _91_3035, _91_3037, _91_3039, _91_3041) when (FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_datacon (d, _91_3046, t, _91_3049, n_tps, quals, _91_3053, drange) -> begin
(

let _91_3060 = (new_term_constant_and_tok_from_lid env d)
in (match (_91_3060) with
| (ddconstrsym, ddtok, env) -> begin
(

let ddtok_tm = (FStar_SMTEncoding_Util.mkApp ((ddtok), ([])))
in (

let _91_3064 = (FStar_Syntax_Util.arrow_formals t)
in (match (_91_3064) with
| (formals, t_res) -> begin
(

let _91_3067 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_91_3067) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (

let _91_3074 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_91_3074) with
| (vars, guards, env', binder_decls, names) -> begin
(

let projectors = (FStar_All.pipe_right names (FStar_List.map (fun x -> (let _189_2390 = (mk_term_projector_name d x)
in ((_189_2390), (FStar_SMTEncoding_Term.Term_sort))))))
in (

let datacons = (let _189_2392 = (let _189_2391 = (varops.next_id ())
in ((ddconstrsym), (projectors), (FStar_SMTEncoding_Term.Term_sort), (_189_2391), (true)))
in (FStar_All.pipe_right _189_2392 FStar_SMTEncoding_Term.constructor_to_decl))
in (

let app = (mk_Apply ddtok_tm vars)
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (

let _91_3084 = (encode_term_pred None t env ddtok_tm)
in (match (_91_3084) with
| (tok_typing, decls3) -> begin
(

let _91_3091 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_91_3091) with
| (vars', guards', env'', decls_formals, _91_3090) -> begin
(

let _91_3096 = (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars')
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (encode_term_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_91_3096) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_SMTEncoding_Util.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _91_3100 -> begin
(let _189_2394 = (let _189_2393 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ddtok), (FStar_SMTEncoding_Term.Term_sort)) _189_2393))
in (_189_2394)::[])
end)
in (

let encode_elim = (fun _91_3103 -> (match (()) with
| () -> begin
(

let _91_3106 = (FStar_Syntax_Util.head_and_args t_res)
in (match (_91_3106) with
| (head, args) -> begin
(match ((let _189_2397 = (FStar_Syntax_Subst.compress head)
in _189_2397.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let _91_3124 = (encode_args args env')
in (match (_91_3124) with
| (encoded_args, arg_decls) -> begin
(

let _91_3139 = (FStar_List.fold_left (fun _91_3128 arg -> (match (_91_3128) with
| (env, arg_vars, eqns) -> begin
(

let _91_3134 = (let _189_2400 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in (gen_term_var env _189_2400))
in (match (_91_3134) with
| (_91_3131, xv, env) -> begin
(let _189_2402 = (let _189_2401 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (_189_2401)::eqns)
in ((env), ((xv)::arg_vars), (_189_2402)))
end))
end)) ((env'), ([]), ([])) encoded_args)
in (match (_91_3139) with
| (_91_3136, arg_vars, eqns) -> begin
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

let typing_inversion = (let _189_2409 = (let _189_2408 = (let _189_2407 = (let _189_2406 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (let _189_2405 = (let _189_2404 = (let _189_2403 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append eqns guards))
in ((ty_pred), (_189_2403)))
in (FStar_SMTEncoding_Util.mkImp _189_2404))
in ((((ty_pred)::[])::[]), (_189_2406), (_189_2405))))
in (FStar_SMTEncoding_Util.mkForall _189_2407))
in ((_189_2408), (Some ("data constructor typing elim")), (Some ((Prims.strcat "data_elim_" ddconstrsym)))))
in FStar_SMTEncoding_Term.Assume (_189_2409))
in (

let subterm_ordering = if (FStar_Ident.lid_equals d FStar_Syntax_Const.lextop_lid) then begin
(

let x = (let _189_2410 = (varops.fresh "x")
in ((_189_2410), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (let _189_2422 = (let _189_2421 = (let _189_2418 = (let _189_2417 = (let _189_2412 = (let _189_2411 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp)
in (_189_2411)::[])
in (_189_2412)::[])
in (let _189_2416 = (let _189_2415 = (let _189_2414 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (let _189_2413 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp)
in ((_189_2414), (_189_2413))))
in (FStar_SMTEncoding_Util.mkImp _189_2415))
in ((_189_2417), ((x)::[]), (_189_2416))))
in (FStar_SMTEncoding_Util.mkForall _189_2418))
in (let _189_2420 = (let _189_2419 = (varops.mk_unique "lextop")
in Some (_189_2419))
in ((_189_2421), (Some ("lextop is top")), (_189_2420))))
in FStar_SMTEncoding_Term.Assume (_189_2422))))
end else begin
(

let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
[]
end
| FStar_SMTEncoding_Term.Term_sort -> begin
(let _189_2425 = (let _189_2424 = (FStar_SMTEncoding_Util.mkFreeV v)
in (FStar_SMTEncoding_Util.mk_Precedes _189_2424 dapp))
in (_189_2425)::[])
end
| _91_3153 -> begin
(FStar_All.failwith "unexpected sort")
end))))
in (let _189_2432 = (let _189_2431 = (let _189_2430 = (let _189_2429 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (let _189_2428 = (let _189_2427 = (let _189_2426 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (_189_2426)))
in (FStar_SMTEncoding_Util.mkImp _189_2427))
in ((((ty_pred)::[])::[]), (_189_2429), (_189_2428))))
in (FStar_SMTEncoding_Util.mkForall _189_2430))
in ((_189_2431), (Some ("subterm ordering")), (Some ((Prims.strcat "subterm_ordering_" ddconstrsym)))))
in FStar_SMTEncoding_Term.Assume (_189_2432)))
end
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end))
end)))
end
| _91_3157 -> begin
(

let _91_3158 = (let _189_2435 = (let _189_2434 = (FStar_Syntax_Print.lid_to_string d)
in (let _189_2433 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _189_2434 _189_2433)))
in (FStar_TypeChecker_Errors.warn drange _189_2435))
in (([]), ([])))
end)
end))
end))
in (

let _91_3162 = (encode_elim ())
in (match (_91_3162) with
| (decls2, elim) -> begin
(

let g = (let _189_2462 = (let _189_2461 = (let _189_2460 = (let _189_2459 = (let _189_2440 = (let _189_2439 = (let _189_2438 = (let _189_2437 = (let _189_2436 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" _189_2436))
in Some (_189_2437))
in ((ddtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (_189_2438)))
in FStar_SMTEncoding_Term.DeclFun (_189_2439))
in (_189_2440)::[])
in (let _189_2458 = (let _189_2457 = (let _189_2456 = (let _189_2455 = (let _189_2454 = (let _189_2453 = (let _189_2452 = (let _189_2444 = (let _189_2443 = (let _189_2442 = (let _189_2441 = (FStar_SMTEncoding_Util.mkEq ((app), (dapp)))
in ((((app)::[])::[]), (vars), (_189_2441)))
in (FStar_SMTEncoding_Util.mkForall _189_2442))
in ((_189_2443), (Some ("equality for proxy")), (Some ((Prims.strcat "equality_tok_" ddtok)))))
in FStar_SMTEncoding_Term.Assume (_189_2444))
in (let _189_2451 = (let _189_2450 = (let _189_2449 = (let _189_2448 = (let _189_2447 = (let _189_2446 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) vars')
in (let _189_2445 = (FStar_SMTEncoding_Util.mkImp ((guard'), (ty_pred')))
in ((((ty_pred')::[])::[]), (_189_2446), (_189_2445))))
in (FStar_SMTEncoding_Util.mkForall _189_2447))
in ((_189_2448), (Some ("data constructor typing intro")), (Some ((Prims.strcat "data_typing_intro_" ddtok)))))
in FStar_SMTEncoding_Term.Assume (_189_2449))
in (_189_2450)::[])
in (_189_2452)::_189_2451))
in (FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("typing for data constructor proxy")), (Some ((Prims.strcat "typing_tok_" ddtok))))))::_189_2453)
in (FStar_List.append _189_2454 elim))
in (FStar_List.append decls_pred _189_2455))
in (FStar_List.append decls_formals _189_2456))
in (FStar_List.append proxy_fresh _189_2457))
in (FStar_List.append _189_2459 _189_2458)))
in (FStar_List.append decls3 _189_2460))
in (FStar_List.append decls2 _189_2461))
in (FStar_List.append binder_decls _189_2462))
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
and encode_signature : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _91_3168 se -> (match (_91_3168) with
| (g, env) -> begin
(

let _91_3172 = (encode_sigelt env se)
in (match (_91_3172) with
| (g', env) -> begin
(((FStar_List.append g g')), (env))
end))
end)) (([]), (env)))))


let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env bindings -> (

let encode_binding = (fun b _91_3180 -> (match (_91_3180) with
| (i, decls, env) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (_91_3182) -> begin
(((i + (Prims.parse_int "1"))), ([]), (env))
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (

let _91_3187 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _189_2477 = (FStar_Syntax_Print.bv_to_string x)
in (let _189_2476 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _189_2475 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" _189_2477 _189_2476 _189_2475))))
end else begin
()
end
in (

let _91_3191 = (encode_term t1 env)
in (match (_91_3191) with
| (t, decls') -> begin
(

let t_hash = (FStar_SMTEncoding_Term.hash_of_term t)
in (

let _91_3196 = (let _189_2482 = (let _189_2481 = (let _189_2480 = (FStar_Util.digest_of_string t_hash)
in (let _189_2479 = (let _189_2478 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _189_2478))
in (Prims.strcat _189_2480 _189_2479)))
in (Prims.strcat "x_" _189_2481))
in (new_term_constant_from_string env x _189_2482))
in (match (_91_3196) with
| (xxsym, xx, env') -> begin
(

let t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel None xx t)
in (

let caption = if (FStar_Options.log_queries ()) then begin
(let _189_2486 = (let _189_2485 = (FStar_Syntax_Print.bv_to_string x)
in (let _189_2484 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _189_2483 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _189_2485 _189_2484 _189_2483))))
in Some (_189_2486))
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
| FStar_TypeChecker_Env.Binding_lid (x, (_91_3204, t)) -> begin
(

let t_norm = (whnf env t)
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant None)
in (

let _91_3213 = (encode_free_var env fv t t_norm [])
in (match (_91_3213) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))))
end
| (FStar_TypeChecker_Env.Binding_sig_inst (_, se, _)) | (FStar_TypeChecker_Env.Binding_sig (_, se)) -> begin
(

let _91_3227 = (encode_sigelt env se)
in (match (_91_3227) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))
end)
end))
in (

let _91_3232 = (FStar_List.fold_right encode_binding bindings (((Prims.parse_int "0")), ([]), (env)))
in (match (_91_3232) with
| (_91_3229, decls, env) -> begin
((decls), (env))
end))))


let encode_labels = (fun labs -> (

let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _91_3239 -> (match (_91_3239) with
| (l, _91_3236, _91_3238) -> begin
FStar_SMTEncoding_Term.DeclFun ((((Prims.fst l)), ([]), (FStar_SMTEncoding_Term.Bool_sort), (None)))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _91_3246 -> (match (_91_3246) with
| (l, _91_3243, _91_3245) -> begin
(let _189_2494 = (FStar_All.pipe_left (fun _189_2490 -> FStar_SMTEncoding_Term.Echo (_189_2490)) (Prims.fst l))
in (let _189_2493 = (let _189_2492 = (let _189_2491 = (FStar_SMTEncoding_Util.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (_189_2491))
in (_189_2492)::[])
in (_189_2494)::_189_2493))
end))))
in ((prefix), (suffix)))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (let _189_2499 = (let _189_2498 = (let _189_2497 = (FStar_Util.smap_create (Prims.parse_int "100"))
in {bindings = []; depth = (Prims.parse_int "0"); tcenv = tcenv; warn = true; cache = _189_2497; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_189_2498)::[])
in (FStar_ST.op_Colon_Equals last_env _189_2499)))


let get_env : FStar_TypeChecker_Env.env  ->  env_t = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "No env; call init first!")
end
| (e)::_91_3252 -> begin
(

let _91_3255 = e
in {bindings = _91_3255.bindings; depth = _91_3255.depth; tcenv = tcenv; warn = _91_3255.warn; cache = _91_3255.cache; nolabels = _91_3255.nolabels; use_zfuel_name = _91_3255.use_zfuel_name; encode_non_total_function_typ = _91_3255.encode_non_total_function_typ})
end))


let set_env : env_t  ->  Prims.unit = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| (_91_3261)::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))


let push_env : Prims.unit  ->  Prims.unit = (fun _91_3263 -> (match (()) with
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

let _91_3269 = hd
in {bindings = _91_3269.bindings; depth = _91_3269.depth; tcenv = _91_3269.tcenv; warn = _91_3269.warn; cache = refs; nolabels = _91_3269.nolabels; use_zfuel_name = _91_3269.use_zfuel_name; encode_non_total_function_typ = _91_3269.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))


let pop_env : Prims.unit  ->  Prims.unit = (fun _91_3272 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Popping an empty stack")
end
| (_91_3276)::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))


let mark_env : Prims.unit  ->  Prims.unit = (fun _91_3278 -> (match (()) with
| () -> begin
(push_env ())
end))


let reset_mark_env : Prims.unit  ->  Prims.unit = (fun _91_3279 -> (match (()) with
| () -> begin
(pop_env ())
end))


let commit_mark_env : Prims.unit  ->  Prims.unit = (fun _91_3280 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| (hd)::(_91_3283)::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _91_3288 -> begin
(FStar_All.failwith "Impossible")
end)
end))


let init : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (

let _91_3290 = (init_env tcenv)
in (

let _91_3292 = (FStar_SMTEncoding_Z3.init ())
in (FStar_SMTEncoding_Z3.giveZ3 ((FStar_SMTEncoding_Term.DefPrelude)::[])))))


let push : Prims.string  ->  Prims.unit = (fun msg -> (

let _91_3295 = (push_env ())
in (

let _91_3297 = (varops.push ())
in (FStar_SMTEncoding_Z3.push msg))))


let pop : Prims.string  ->  Prims.unit = (fun msg -> (

let _91_3300 = (let _189_2520 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _189_2520))
in (

let _91_3302 = (varops.pop ())
in (FStar_SMTEncoding_Z3.pop msg))))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _91_3305 = (mark_env ())
in (

let _91_3307 = (varops.mark ())
in (FStar_SMTEncoding_Z3.mark msg))))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _91_3310 = (reset_mark_env ())
in (

let _91_3312 = (varops.reset_mark ())
in (FStar_SMTEncoding_Z3.reset_mark msg))))


let commit_mark = (fun msg -> (

let _91_3315 = (commit_mark_env ())
in (

let _91_3317 = (varops.commit_mark ())
in (FStar_SMTEncoding_Z3.commit_mark msg))))


let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (

let caption = (fun decls -> if (FStar_Options.log_queries ()) then begin
(let _189_2535 = (let _189_2534 = (let _189_2533 = (let _189_2532 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.map FStar_Syntax_Print.lid_to_string))
in (FStar_All.pipe_right _189_2532 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " _189_2533))
in FStar_SMTEncoding_Term.Caption (_189_2534))
in (_189_2535)::decls)
end else begin
decls
end)
in (

let env = (get_env tcenv)
in (

let _91_3326 = (encode_sigelt env se)
in (match (_91_3326) with
| (decls, env) -> begin
(

let _91_3327 = (set_env env)
in (let _189_2536 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 _189_2536)))
end)))))


let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let _91_3332 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(let _189_2541 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name _189_2541))
end else begin
()
end
in (

let env = (get_env tcenv)
in (

let _91_3339 = (encode_signature (

let _91_3335 = env
in {bindings = _91_3335.bindings; depth = _91_3335.depth; tcenv = _91_3335.tcenv; warn = false; cache = _91_3335.cache; nolabels = _91_3335.nolabels; use_zfuel_name = _91_3335.use_zfuel_name; encode_non_total_function_typ = _91_3335.encode_non_total_function_typ}) modul.FStar_Syntax_Syntax.exports)
in (match (_91_3339) with
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

let _91_3345 = (set_env (

let _91_3343 = env
in {bindings = _91_3343.bindings; depth = _91_3343.depth; tcenv = _91_3343.tcenv; warn = true; cache = _91_3343.cache; nolabels = _91_3343.nolabels; use_zfuel_name = _91_3343.use_zfuel_name; encode_non_total_function_typ = _91_3343.encode_non_total_function_typ}))
in (

let _91_3347 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end else begin
()
end
in (

let decls = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls)))))
end))))))


let encode_query : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_ErrorReporting.label Prims.list * FStar_SMTEncoding_Term.decl * FStar_SMTEncoding_Term.decl Prims.list) = (fun use_env_msg tcenv q -> (

let _91_3353 = (let _189_2559 = (let _189_2558 = (FStar_TypeChecker_Env.current_module tcenv)
in _189_2558.FStar_Ident.str)
in (FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name _189_2559))
in (

let env = (get_env tcenv)
in (

let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (

let _91_3378 = (

let rec aux = (fun bindings -> (match (bindings) with
| (FStar_TypeChecker_Env.Binding_var (x))::rest -> begin
(

let _91_3367 = (aux rest)
in (match (_91_3367) with
| (out, rest) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (let _189_2565 = (let _189_2564 = (FStar_Syntax_Syntax.mk_binder (

let _91_3369 = x
in {FStar_Syntax_Syntax.ppname = _91_3369.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _91_3369.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_189_2564)::out)
in ((_189_2565), (rest))))
end))
end
| _91_3372 -> begin
(([]), (bindings))
end))
in (

let _91_3375 = (aux bindings)
in (match (_91_3375) with
| (closing, bindings) -> begin
(let _189_2566 = (FStar_Syntax_Util.close_forall (FStar_List.rev closing) q)
in ((_189_2566), (bindings)))
end)))
in (match (_91_3378) with
| (q, bindings) -> begin
(

let _91_3387 = (let _189_2568 = (FStar_List.filter (fun _91_25 -> (match (_91_25) with
| FStar_TypeChecker_Env.Binding_sig (_91_3381) -> begin
false
end
| _91_3384 -> begin
true
end)) bindings)
in (encode_env_bindings env _189_2568))
in (match (_91_3387) with
| (env_decls, env) -> begin
(

let _91_3388 = if (((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTQuery")))) then begin
(let _189_2569 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" _189_2569))
end else begin
()
end
in (

let _91_3392 = (encode_formula q env)
in (match (_91_3392) with
| (phi, qdecls) -> begin
(

let _91_3395 = (let _189_2570 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg _189_2570 phi))
in (match (_91_3395) with
| (labels, phi) -> begin
(

let _91_3398 = (encode_labels labels)
in (match (_91_3398) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append env_decls (FStar_List.append label_prefix qdecls))
in (

let qry = (let _189_2574 = (let _189_2573 = (FStar_SMTEncoding_Util.mkNot phi)
in (let _189_2572 = (let _189_2571 = (varops.mk_unique "@query")
in Some (_189_2571))
in ((_189_2573), (Some ("query")), (_189_2572))))
in FStar_SMTEncoding_Term.Assume (_189_2574))
in (

let suffix = (let _189_2576 = (let _189_2575 = if (FStar_Options.print_z3_statistics ()) then begin
(FStar_SMTEncoding_Term.PrintStats)::[]
end else begin
[]
end
in (FStar_List.append _189_2575 ((FStar_SMTEncoding_Term.Echo ("Done!"))::[])))
in (FStar_List.append label_suffix _189_2576))
in ((query_prelude), (labels), (qry), (suffix)))))
end))
end))
end)))
end))
end))))))


let is_trivial : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun tcenv q -> (

let env = (get_env tcenv)
in (

let _91_3405 = (push "query")
in (

let _91_3410 = (encode_formula q env)
in (match (_91_3410) with
| (f, _91_3409) -> begin
(

let _91_3411 = (pop "query")
in (match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _91_3415) -> begin
true
end
| _91_3419 -> begin
false
end))
end)))))




