
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


let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (

let _85_230 = env
in {bindings = (Binding_var (((x), (t))))::env.bindings; depth = _85_230.depth; tcenv = _85_230.tcenv; warn = _85_230.warn; cache = _85_230.cache; nolabels = _85_230.nolabels; use_zfuel_name = _85_230.use_zfuel_name; encode_non_total_function_typ = _85_230.encode_non_total_function_typ}))


let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let aux = (fun a' -> (lookup_binding env (fun _85_3 -> (match (_85_3) with
| Binding_var (b, t) when (FStar_Syntax_Syntax.bv_eq b a') -> begin
Some (((b), (t)))
end
| _85_242 -> begin
None
end))))
in (match ((aux a)) with
| None -> begin
(

let a = (unmangle a)
in (match ((aux a)) with
| None -> begin
(let _177_316 = (let _177_315 = (FStar_Syntax_Print.bv_to_string a)
in (FStar_Util.format1 "Bound term variable not found (after unmangling): %s" _177_315))
in (FStar_All.failwith _177_316))
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
in (let _177_327 = (

let _85_258 = env
in (let _177_326 = (let _177_325 = (let _177_324 = (let _177_323 = (let _177_322 = (FStar_SMTEncoding_Term.mkApp ((ftok), ([])))
in (FStar_All.pipe_left (fun _177_321 -> Some (_177_321)) _177_322))
in ((x), (fname), (_177_323), (None)))
in Binding_fvar (_177_324))
in (_177_325)::env.bindings)
in {bindings = _177_326; depth = _85_258.depth; tcenv = _85_258.tcenv; warn = _85_258.warn; cache = _85_258.cache; nolabels = _85_258.nolabels; use_zfuel_name = _85_258.use_zfuel_name; encode_non_total_function_typ = _85_258.encode_non_total_function_typ}))
in ((fname), (ftok), (_177_327))))))


let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun _85_4 -> (match (_85_4) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some (((t1), (t2), (t3)))
end
| _85_270 -> begin
None
end))))


let contains_name : env_t  ->  Prims.string  ->  Prims.bool = (fun env s -> (let _177_338 = (lookup_binding env (fun _85_5 -> (match (_85_5) with
| Binding_fvar (b, t1, t2, t3) when (b.FStar_Ident.str = s) -> begin
Some (())
end
| _85_281 -> begin
None
end)))
in (FStar_All.pipe_right _177_338 FStar_Option.isSome)))


let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _177_344 = (let _177_343 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" _177_343))
in (FStar_All.failwith _177_344))
end
| Some (s) -> begin
s
end))


let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (

let _85_291 = env
in {bindings = (Binding_fvar (((x), (fname), (ftok), (None))))::env.bindings; depth = _85_291.depth; tcenv = _85_291.tcenv; warn = _85_291.warn; cache = _85_291.cache; nolabels = _85_291.nolabels; use_zfuel_name = _85_291.use_zfuel_name; encode_non_total_function_typ = _85_291.encode_non_total_function_typ}))


let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (

let _85_300 = (lookup_lid env x)
in (match (_85_300) with
| (t1, t2, _85_299) -> begin
(

let t3 = (let _177_361 = (let _177_360 = (let _177_359 = (FStar_SMTEncoding_Term.mkApp (("ZFuel"), ([])))
in (_177_359)::[])
in ((f), (_177_360)))
in (FStar_SMTEncoding_Term.mkApp _177_361))
in (

let _85_302 = env
in {bindings = (Binding_fvar (((x), (t1), (t2), (Some (t3)))))::env.bindings; depth = _85_302.depth; tcenv = _85_302.tcenv; warn = _85_302.warn; cache = _85_302.cache; nolabels = _85_302.nolabels; use_zfuel_name = _85_302.use_zfuel_name; encode_non_total_function_typ = _85_302.encode_non_total_function_typ}))
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
| _85_315 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (_85_319, (fuel)::[]) -> begin
if (let _177_367 = (let _177_366 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right _177_366 Prims.fst))
in (FStar_Util.starts_with _177_367 "fuel")) then begin
(let _177_370 = (let _177_369 = (FStar_SMTEncoding_Term.mkFreeV ((name), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_ApplyTF _177_369 fuel))
in (FStar_All.pipe_left (fun _177_368 -> Some (_177_368)) _177_370))
end else begin
Some (t)
end
end
| _85_325 -> begin
Some (t)
end)
end
| _85_327 -> begin
None
end)
end)
end))


let lookup_free_var = (fun env a -> (match ((try_lookup_free_var env a.FStar_Syntax_Syntax.v)) with
| Some (t) -> begin
t
end
| None -> begin
(let _177_374 = (let _177_373 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _177_373))
in (FStar_All.failwith _177_374))
end))


let lookup_free_var_name = (fun env a -> (

let _85_340 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_85_340) with
| (x, _85_337, _85_339) -> begin
x
end)))


let lookup_free_var_sym = (fun env a -> (

let _85_346 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_85_346) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.hash = _85_350; FStar_SMTEncoding_Term.freevars = _85_348}) when env.use_zfuel_name -> begin
((g), (zf))
end
| _85_358 -> begin
(match (sym) with
| None -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end
| Some (sym) -> begin
(match (sym.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, (fuel)::[]) -> begin
((g), ((fuel)::[]))
end
| _85_368 -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end)
end)
end)
end)))


let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun _85_6 -> (match (_85_6) with
| Binding_fvar (_85_373, nm', tok, _85_377) when (nm = nm') -> begin
tok
end
| _85_381 -> begin
None
end))))


let mkForall_fuel' = (fun n _85_386 -> (match (_85_386) with
| (pats, vars, body) -> begin
(

let fallback = (fun _85_388 -> (match (()) with
| () -> begin
(FStar_SMTEncoding_Term.mkForall ((pats), (vars), (body)))
end))
in if (FStar_Options.unthrottle_inductives ()) then begin
(fallback ())
end else begin
(

let _85_391 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_85_391) with
| (fsym, fterm) -> begin
(

let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Term.mkApp (("HasTypeFuel"), ((fterm)::args)))
end
| _85_401 -> begin
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
(let _177_391 = (add_fuel guards)
in (FStar_SMTEncoding_Term.mk_and_l _177_391))
end
| _85_414 -> begin
(let _177_392 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _177_392 FStar_List.hd))
end)
in (FStar_SMTEncoding_Term.mkImp ((guard), (body'))))
end
| _85_417 -> begin
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
(let _177_398 = (FStar_TypeChecker_Env.lookup_definition FStar_TypeChecker_Env.OnlyInline env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _177_398 FStar_Option.isNone))
end
| _85_456 -> begin
false
end)))


let head_redex : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (match ((let _177_403 = (FStar_Syntax_Util.un_uinst t)
in _177_403.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_85_460) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(let _177_404 = (FStar_TypeChecker_Env.lookup_definition FStar_TypeChecker_Env.OnlyInline env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _177_404 FStar_Option.isSome))
end
| _85_465 -> begin
false
end))


let whnf : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> if (head_normal env t) then begin
t
end else begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
end)


let norm : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t))


let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (let _177_417 = (let _177_415 = (FStar_Syntax_Syntax.null_binder t)
in (_177_415)::[])
in (let _177_416 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Util.abs _177_417 _177_416 None))))


let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(let _177_424 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out _177_424))
end
| s -> begin
(

let _85_477 = ()
in (let _177_425 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTT out _177_425)))
end)) e)))


let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Term.mk_ApplyTT e)))


let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun _85_7 -> (match (_85_7) with
| (FStar_SMTEncoding_Term.Var ("ApplyTT")) | (FStar_SMTEncoding_Term.Var ("ApplyTF")) -> begin
true
end
| _85_487 -> begin
false
end))


let is_eta : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env vars t -> (

let rec aux = (fun t xs -> (match (((t.FStar_SMTEncoding_Term.tm), (xs))) with
| (FStar_SMTEncoding_Term.App (app, (f)::({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.hash = _85_498; FStar_SMTEncoding_Term.freevars = _85_496})::[]), (x)::xs) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), _85_516) -> begin
if (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v)
end
| _85_523 -> begin
false
end)) args vars)) then begin
(tok_of_name env f)
end else begin
None
end
end
| (_85_525, []) -> begin
(

let fvs = (FStar_SMTEncoding_Term.free_variables t)
in if (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (not ((FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)))))) then begin
Some (t)
end else begin
None
end)
end
| _85_531 -> begin
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
(let _177_482 = (let _177_481 = (let _177_480 = (let _177_479 = (FStar_SMTEncoding_Term.mkInteger' (FStar_Util.int_of_char c))
in (FStar_SMTEncoding_Term.boxInt _177_479))
in (_177_480)::[])
in (("FStar.Char.Char"), (_177_481)))
in (FStar_SMTEncoding_Term.mkApp _177_482))
end
| FStar_Const.Const_int (i, None) -> begin
(let _177_483 = (FStar_SMTEncoding_Term.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt _177_483))
end
| FStar_Const.Const_int (i, Some (_85_551)) -> begin
(FStar_All.failwith "Machine integers should be desugared")
end
| FStar_Const.Const_string (bytes, _85_557) -> begin
(let _177_484 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _177_484))
end
| FStar_Const.Const_range (r) -> begin
FStar_SMTEncoding_Term.mk_Range_const
end
| FStar_Const.Const_effect -> begin
FStar_SMTEncoding_Term.mk_Term_type
end
| c -> begin
(let _177_486 = (let _177_485 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" _177_485))
in (FStar_All.failwith _177_486))
end))


let as_function_typ : env_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (

let rec aux = (fun norm t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_85_571) -> begin
t
end
| FStar_Syntax_Syntax.Tm_refine (_85_574) -> begin
(let _177_495 = (FStar_Syntax_Util.unrefine t)
in (aux true _177_495))
end
| _85_577 -> begin
if norm then begin
(let _177_496 = (whnf env t)
in (aux false _177_496))
end else begin
(let _177_499 = (let _177_498 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (let _177_497 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _177_498 _177_497)))
in (FStar_All.failwith _177_499))
end
end)))
in (aux true t0)))


let curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun k -> (

let k = (FStar_Syntax_Subst.compress k)
in (match (k.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| _85_585 -> begin
(let _177_502 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (_177_502)))
end)))


let rec encode_binders : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> (

let _85_589 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _177_550 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" _177_550))
end else begin
()
end
in (

let _85_617 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _85_596 b -> (match (_85_596) with
| (vars, guards, env, decls, names) -> begin
(

let _85_611 = (

let x = (unmangle (Prims.fst b))
in (

let _85_602 = (gen_term_var env x)
in (match (_85_602) with
| (xxsym, xx, env') -> begin
(

let _85_605 = (let _177_553 = (norm env x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt _177_553 env xx))
in (match (_85_605) with
| (guard_x_t, decls') -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (guard_x_t), (env'), (decls'), (x))
end))
end)))
in (match (_85_611) with
| (v, g, env, decls', n) -> begin
(((v)::vars), ((g)::guards), (env), ((FStar_List.append decls decls')), ((n)::names))
end))
end)) (([]), ([]), (env), ([]), ([]))))
in (match (_85_617) with
| (vars, guards, env, decls, names) -> begin
(((FStar_List.rev vars)), ((FStar_List.rev guards)), (env), (decls), ((FStar_List.rev names)))
end))))
and encode_term_pred : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let _85_624 = (encode_term t env)
in (match (_85_624) with
| (t, decls) -> begin
(let _177_558 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t)
in ((_177_558), (decls)))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let _85_631 = (encode_term t env)
in (match (_85_631) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _177_563 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t)
in ((_177_563), (decls)))
end
| Some (f) -> begin
(let _177_564 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t)
in ((_177_564), (decls)))
end)
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let t0 = (FStar_Syntax_Subst.compress t)
in (

let _85_638 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _177_569 = (FStar_Syntax_Print.tag_of_term t)
in (let _177_568 = (FStar_Syntax_Print.tag_of_term t0)
in (let _177_567 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" _177_569 _177_568 _177_567))))
end else begin
()
end
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _177_574 = (let _177_573 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (let _177_572 = (FStar_Syntax_Print.tag_of_term t0)
in (let _177_571 = (FStar_Syntax_Print.term_to_string t0)
in (let _177_570 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _177_573 _177_572 _177_571 _177_570)))))
in (FStar_All.failwith _177_574))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _177_576 = (let _177_575 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" _177_575))
in (FStar_All.failwith _177_576))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, k, _85_649) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_meta (t, _85_654) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t = (lookup_term_var env x)
in ((t), ([])))
end
| FStar_Syntax_Syntax.Tm_fvar (v) -> begin
(let _177_577 = (lookup_free_var env v.FStar_Syntax_Syntax.fv_name)
in ((_177_577), ([])))
end
| FStar_Syntax_Syntax.Tm_type (_85_663) -> begin
((FStar_SMTEncoding_Term.mk_Term_type), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t, _85_667) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(let _177_578 = (encode_const c)
in ((_177_578), ([])))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _85_678 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_85_678) with
| (binders, res) -> begin
if ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res)) then begin
(

let _85_685 = (encode_binders None binders env)
in (match (_85_685) with
| (vars, guards, env', decls, _85_684) -> begin
(

let fsym = (let _177_579 = (varops.fresh "f")
in ((_177_579), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (

let app = (mk_Apply f vars)
in (

let _85_693 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post (

let _85_689 = env.tcenv
in {FStar_TypeChecker_Env.solver = _85_689.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _85_689.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _85_689.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _85_689.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _85_689.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _85_689.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _85_689.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _85_689.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _85_689.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _85_689.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _85_689.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _85_689.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _85_689.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _85_689.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _85_689.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _85_689.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _85_689.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _85_689.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.type_of = _85_689.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _85_689.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _85_689.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _85_689.FStar_TypeChecker_Env.qname_and_index}) res)
in (match (_85_693) with
| (pre_opt, res_t) -> begin
(

let _85_696 = (encode_term_pred None res_t env' app)
in (match (_85_696) with
| (res_pred, decls') -> begin
(

let _85_705 = (match (pre_opt) with
| None -> begin
(let _177_580 = (FStar_SMTEncoding_Term.mk_and_l guards)
in ((_177_580), ([])))
end
| Some (pre) -> begin
(

let _85_702 = (encode_formula pre env')
in (match (_85_702) with
| (guard, decls0) -> begin
(let _177_581 = (FStar_SMTEncoding_Term.mk_and_l ((guard)::guards))
in ((_177_581), (decls0)))
end))
end)
in (match (_85_705) with
| (guards, guard_decls) -> begin
(

let t_interp = (let _177_583 = (let _177_582 = (FStar_SMTEncoding_Term.mkImp ((guards), (res_pred)))
in ((((app)::[])::[]), (vars), (_177_582)))
in (FStar_SMTEncoding_Term.mkForall _177_583))
in (

let cvars = (let _177_585 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right _177_585 (FStar_List.filter (fun _85_710 -> (match (_85_710) with
| (x, _85_709) -> begin
(x <> (Prims.fst fsym))
end)))))
in (

let tkey = (FStar_SMTEncoding_Term.mkForall (([]), ((fsym)::cvars), (t_interp)))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t', sorts, _85_716) -> begin
(let _177_588 = (let _177_587 = (let _177_586 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in ((t'), (_177_586)))
in (FStar_SMTEncoding_Term.mkApp _177_587))
in ((_177_588), ([])))
end
| None -> begin
(

let tsym = (let _177_590 = (let _177_589 = (FStar_Util.digest_of_string tkey.FStar_SMTEncoding_Term.hash)
in (Prims.strcat "Tm_arrow_" _177_589))
in (varops.mk_unique _177_590))
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let caption = if (FStar_Options.log_queries ()) then begin
(let _177_591 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in Some (_177_591))
end else begin
None
end
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (caption)))
in (

let t = (let _177_593 = (let _177_592 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in ((tsym), (_177_592)))
in (FStar_SMTEncoding_Term.mkApp _177_593))
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let k_assumption = (

let a_name = Some ((Prims.strcat "kinding_" tsym))
in (let _177_595 = (let _177_594 = (FStar_SMTEncoding_Term.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((_177_594), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_177_595)))
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t)
in (

let pre_typing = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in (let _177_602 = (let _177_601 = (let _177_600 = (let _177_599 = (let _177_598 = (let _177_597 = (let _177_596 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _177_596))
in ((f_has_t), (_177_597)))
in (FStar_SMTEncoding_Term.mkImp _177_598))
in ((((f_has_t)::[])::[]), ((fsym)::cvars), (_177_599)))
in (mkForall_fuel _177_600))
in ((_177_601), (Some ("pre-typing for functions")), (a_name)))
in FStar_SMTEncoding_Term.Assume (_177_602)))
in (

let t_interp = (

let a_name = Some ((Prims.strcat "interpretation_" tsym))
in (let _177_606 = (let _177_605 = (let _177_604 = (let _177_603 = (FStar_SMTEncoding_Term.mkIff ((f_has_t_z), (t_interp)))
in ((((f_has_t_z)::[])::[]), ((fsym)::cvars), (_177_603)))
in (FStar_SMTEncoding_Term.mkForall _177_604))
in ((_177_605), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_177_606)))
in (

let t_decls = (FStar_List.append ((tdecl)::decls) (FStar_List.append decls' (FStar_List.append guard_decls ((k_assumption)::(pre_typing)::(t_interp)::[]))))
in (

let _85_735 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash ((tsym), (cvar_sorts), (t_decls)))
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
in (let _177_608 = (let _177_607 = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in ((_177_607), (Some ("Typing for non-total arrows")), (a_name)))
in FStar_SMTEncoding_Term.Assume (_177_608)))
in (

let fsym = (("f"), (FStar_SMTEncoding_Term.Term_sort))
in (

let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let t_interp = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in (let _177_615 = (let _177_614 = (let _177_613 = (let _177_612 = (let _177_611 = (let _177_610 = (let _177_609 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _177_609))
in ((f_has_t), (_177_610)))
in (FStar_SMTEncoding_Term.mkImp _177_611))
in ((((f_has_t)::[])::[]), ((fsym)::[]), (_177_612)))
in (mkForall_fuel _177_613))
in ((_177_614), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_177_615)))
in ((t), ((tdecl)::(t_kinding)::(t_interp)::[]))))))))))
end
end))
end
| FStar_Syntax_Syntax.Tm_refine (_85_748) -> begin
(

let _85_768 = (match ((FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.tk = _85_755; FStar_Syntax_Syntax.pos = _85_753; FStar_Syntax_Syntax.vars = _85_751} -> begin
(

let _85_763 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) f)
in (match (_85_763) with
| (b, f) -> begin
(let _177_617 = (let _177_616 = (FStar_List.hd b)
in (Prims.fst _177_616))
in ((_177_617), (f)))
end))
end
| _85_765 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_85_768) with
| (x, f) -> begin
(

let _85_771 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (_85_771) with
| (base_t, decls) -> begin
(

let _85_775 = (gen_term_var env x)
in (match (_85_775) with
| (x, xtm, env') -> begin
(

let _85_778 = (encode_formula f env')
in (match (_85_778) with
| (refinement, decls') -> begin
(

let _85_781 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_85_781) with
| (fsym, fterm) -> begin
(

let encoding = (let _177_619 = (let _177_618 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in ((_177_618), (refinement)))
in (FStar_SMTEncoding_Term.mkAnd _177_619))
in (

let cvars = (let _177_621 = (FStar_SMTEncoding_Term.free_variables encoding)
in (FStar_All.pipe_right _177_621 (FStar_List.filter (fun _85_786 -> (match (_85_786) with
| (y, _85_785) -> begin
((y <> x) && (y <> fsym))
end)))))
in (

let xfv = ((x), (FStar_SMTEncoding_Term.Term_sort))
in (

let ffv = ((fsym), (FStar_SMTEncoding_Term.Fuel_sort))
in (

let tkey = (FStar_SMTEncoding_Term.mkForall (([]), ((ffv)::(xfv)::cvars), (encoding)))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _85_793, _85_795) -> begin
(let _177_624 = (let _177_623 = (let _177_622 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in ((t), (_177_622)))
in (FStar_SMTEncoding_Term.mkApp _177_623))
in ((_177_624), ([])))
end
| None -> begin
(

let tsym = (let _177_626 = (let _177_625 = (FStar_Util.digest_of_string tkey.FStar_SMTEncoding_Term.hash)
in (Prims.strcat "Tm_refine_" _177_625))
in (varops.mk_unique _177_626))
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let t = (let _177_628 = (let _177_627 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in ((tsym), (_177_627)))
in (FStar_SMTEncoding_Term.mkApp _177_628))
in (

let x_has_t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let t_haseq_base = (FStar_SMTEncoding_Term.mk_haseq base_t)
in (

let t_haseq_ref = (FStar_SMTEncoding_Term.mk_haseq t)
in (

let t_haseq = (let _177_632 = (let _177_631 = (let _177_630 = (let _177_629 = (FStar_SMTEncoding_Term.mkIff ((t_haseq_ref), (t_haseq_base)))
in ((((t_haseq_ref)::[])::[]), (cvars), (_177_629)))
in (FStar_SMTEncoding_Term.mkForall _177_630))
in ((_177_631), (Some ((Prims.strcat "haseq for " tsym))), (Some ((Prims.strcat "haseq" tsym)))))
in FStar_SMTEncoding_Term.Assume (_177_632))
in (

let t_kinding = (let _177_634 = (let _177_633 = (FStar_SMTEncoding_Term.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((_177_633), (Some ("refinement kinding")), (Some ((Prims.strcat "refinement_kinding_" tsym)))))
in FStar_SMTEncoding_Term.Assume (_177_634))
in (

let t_interp = (let _177_640 = (let _177_639 = (let _177_636 = (let _177_635 = (FStar_SMTEncoding_Term.mkIff ((x_has_t), (encoding)))
in ((((x_has_t)::[])::[]), ((ffv)::(xfv)::cvars), (_177_635)))
in (FStar_SMTEncoding_Term.mkForall _177_636))
in (let _177_638 = (let _177_637 = (FStar_Syntax_Print.term_to_string t0)
in Some (_177_637))
in ((_177_639), (_177_638), (Some ((Prims.strcat "refinement_interpretation_" tsym))))))
in FStar_SMTEncoding_Term.Assume (_177_640))
in (

let t_decls = (FStar_List.append decls (FStar_List.append decls' ((tdecl)::(t_kinding)::(t_interp)::(t_haseq)::[])))
in (

let _85_811 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash ((tsym), (cvar_sorts), (t_decls)))
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

let ttm = (let _177_641 = (FStar_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Term.mk_Term_uvar _177_641))
in (

let _85_820 = (encode_term_pred None k env ttm)
in (match (_85_820) with
| (t_has_k, decls) -> begin
(

let d = (let _177_647 = (let _177_646 = (let _177_645 = (let _177_644 = (let _177_643 = (let _177_642 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _177_642))
in (FStar_Util.format1 "uvar_typing_%s" _177_643))
in (varops.mk_unique _177_644))
in Some (_177_645))
in ((t_has_k), (Some ("Uvar typing")), (_177_646)))
in FStar_SMTEncoding_Term.Assume (_177_647))
in ((ttm), ((FStar_List.append decls ((d)::[])))))
end)))
end
| FStar_Syntax_Syntax.Tm_app (_85_823) -> begin
(

let _85_827 = (FStar_Syntax_Util.head_and_args t0)
in (match (_85_827) with
| (head, args_e) -> begin
(match ((let _177_649 = (let _177_648 = (FStar_Syntax_Subst.compress head)
in _177_648.FStar_Syntax_Syntax.n)
in ((_177_649), (args_e)))) with
| (_85_829, _85_831) when (head_redex env head) -> begin
(let _177_650 = (whnf env t)
in (encode_term _177_650 env))
end
| ((FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), (_)::((v1, _))::((v2, _))::[])) | ((FStar_Syntax_Syntax.Tm_fvar (fv), (_)::((v1, _))::((v2, _))::[])) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
(

let _85_871 = (encode_term v1 env)
in (match (_85_871) with
| (v1, decls1) -> begin
(

let _85_874 = (encode_term v2 env)
in (match (_85_874) with
| (v2, decls2) -> begin
(let _177_651 = (FStar_SMTEncoding_Term.mk_LexCons v1 v2)
in ((_177_651), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), (_85_883)::(_85_880)::_85_878) -> begin
(

let e0 = (let _177_655 = (let _177_654 = (let _177_653 = (let _177_652 = (FStar_List.hd args_e)
in (_177_652)::[])
in ((head), (_177_653)))
in FStar_Syntax_Syntax.Tm_app (_177_654))
in (FStar_Syntax_Syntax.mk _177_655 None head.FStar_Syntax_Syntax.pos))
in (

let e = (let _177_658 = (let _177_657 = (let _177_656 = (FStar_List.tl args_e)
in ((e0), (_177_656)))
in FStar_Syntax_Syntax.Tm_app (_177_657))
in (FStar_Syntax_Syntax.mk _177_658 None t0.FStar_Syntax_Syntax.pos))
in (encode_term e env)))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), ((arg, _85_892))::[]) -> begin
(

let _85_898 = (encode_term arg env)
in (match (_85_898) with
| (tm, decls) -> begin
(let _177_659 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Var ("Reify")), ((tm)::[])))))
in ((_177_659), (decls)))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (_85_900)), ((arg, _85_905))::[]) -> begin
(encode_term arg env)
end
| _85_910 -> begin
(

let _85_913 = (encode_args args_e env)
in (match (_85_913) with
| (args, decls) -> begin
(

let encode_partial_app = (fun ht_opt -> (

let _85_918 = (encode_term head env)
in (match (_85_918) with
| (head, decls') -> begin
(

let app_tm = (mk_Apply_args head args)
in (match (ht_opt) with
| None -> begin
((app_tm), ((FStar_List.append decls decls')))
end
| Some (formals, c) -> begin
(

let _85_927 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (_85_927) with
| (formals, rest) -> begin
(

let subst = (FStar_List.map2 (fun _85_931 _85_935 -> (match (((_85_931), (_85_935))) with
| ((bv, _85_930), (a, _85_934)) -> begin
FStar_Syntax_Syntax.NT (((bv), (a)))
end)) formals args_e)
in (

let ty = (let _177_664 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right _177_664 (FStar_Syntax_Subst.subst subst)))
in (

let _85_940 = (encode_term_pred None ty env app_tm)
in (match (_85_940) with
| (has_type, decls'') -> begin
(

let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (

let e_typing = (let _177_670 = (let _177_669 = (FStar_SMTEncoding_Term.mkForall ((((has_type)::[])::[]), (cvars), (has_type)))
in (let _177_668 = (let _177_667 = (let _177_666 = (let _177_665 = (FStar_Util.digest_of_string app_tm.FStar_SMTEncoding_Term.hash)
in (Prims.strcat "partial_app_typing_" _177_665))
in (varops.mk_unique _177_666))
in Some (_177_667))
in ((_177_669), (Some ("Partial app typing")), (_177_668))))
in FStar_SMTEncoding_Term.Assume (_177_670))
in ((app_tm), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' ((e_typing)::[]))))))))
end))))
end))
end))
end)))
in (

let encode_full_app = (fun fv -> (

let _85_947 = (lookup_free_var_sym env fv)
in (match (_85_947) with
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
(let _177_674 = (let _177_673 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _177_673 Prims.snd))
in Some (_177_674))
end
| FStar_Syntax_Syntax.Tm_ascribed (_85_979, FStar_Util.Inl (t), _85_983) -> begin
Some (t)
end
| FStar_Syntax_Syntax.Tm_ascribed (_85_987, FStar_Util.Inr (c), _85_991) -> begin
Some ((FStar_Syntax_Util.comp_result c))
end
| _85_995 -> begin
None
end)
in (match (head_type) with
| None -> begin
(encode_partial_app None)
end
| Some (head_type) -> begin
(

let head_type = (let _177_675 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine _177_675))
in (

let _85_1003 = (curried_arrow_formals_comp head_type)
in (match (_85_1003) with
| (formals, c) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| _85_1019 -> begin
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

let _85_1028 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_85_1028) with
| (bs, body, opening) -> begin
(

let fallback = (fun _85_1030 -> (match (()) with
| () -> begin
(

let f = (varops.fresh "Tm_abs")
in (

let decl = FStar_SMTEncoding_Term.DeclFun (((f), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Imprecise function encoding"))))
in (let _177_678 = (FStar_SMTEncoding_Term.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in ((_177_678), ((decl)::[])))))
end))
in (

let is_impure = (fun _85_9 -> (match (_85_9) with
| FStar_Util.Inl (lc) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)))
end
| FStar_Util.Inr (eff) -> begin
(let _177_681 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv eff)
in (FStar_All.pipe_right _177_681 Prims.op_Negation))
end))
in (

let codomain_eff = (fun lc -> (match (lc) with
| FStar_Util.Inl (lc) -> begin
(let _177_686 = (let _177_684 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening _177_684))
in (FStar_All.pipe_right _177_686 (fun _177_685 -> Some (_177_685))))
end
| FStar_Util.Inr (eff) -> begin
(

let new_uvar = (fun _85_1046 -> (match (()) with
| () -> begin
(let _177_689 = (FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange [] FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _177_689 Prims.fst))
end))
in if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid) then begin
(let _177_692 = (let _177_690 = (new_uvar ())
in (FStar_Syntax_Syntax.mk_Total _177_690))
in (FStar_All.pipe_right _177_692 (fun _177_691 -> Some (_177_691))))
end else begin
if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid) then begin
(let _177_695 = (let _177_693 = (new_uvar ())
in (FStar_Syntax_Syntax.mk_GTotal _177_693))
in (FStar_All.pipe_right _177_695 (fun _177_694 -> Some (_177_694))))
end else begin
None
end
end)
end))
in (match (lopt) with
| None -> begin
(

let _85_1048 = (let _177_697 = (let _177_696 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s" _177_696))
in (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos _177_697))
in (fallback ()))
end
| Some (lc) -> begin
if (is_impure lc) then begin
(fallback ())
end else begin
(

let _85_1058 = (encode_binders None bs env)
in (match (_85_1058) with
| (vars, guards, envbody, decls, _85_1057) -> begin
(

let _85_1061 = (encode_term body envbody)
in (match (_85_1061) with
| (body, decls') -> begin
(

let key_body = (let _177_701 = (let _177_700 = (let _177_699 = (let _177_698 = (FStar_SMTEncoding_Term.mk_and_l guards)
in ((_177_698), (body)))
in (FStar_SMTEncoding_Term.mkImp _177_699))
in (([]), (vars), (_177_700)))
in (FStar_SMTEncoding_Term.mkForall _177_701))
in (

let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (

let tkey = (FStar_SMTEncoding_Term.mkForall (([]), (cvars), (key_body)))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _85_1067, _85_1069) -> begin
(let _177_704 = (let _177_703 = (let _177_702 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in ((t), (_177_702)))
in (FStar_SMTEncoding_Term.mkApp _177_703))
in ((_177_704), ([])))
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

let fsym = (let _177_706 = (let _177_705 = (FStar_Util.digest_of_string tkey.FStar_SMTEncoding_Term.hash)
in (Prims.strcat "Tm_abs_" _177_705))
in (varops.mk_unique _177_706))
in (

let fdecl = FStar_SMTEncoding_Term.DeclFun (((fsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let f = (let _177_708 = (let _177_707 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in ((fsym), (_177_707)))
in (FStar_SMTEncoding_Term.mkApp _177_708))
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

let _85_1087 = (encode_term_pred None tfun env f)
in (match (_85_1087) with
| (f_has_t, decls'') -> begin
(

let a_name = Some ((Prims.strcat "typing_" fsym))
in (let _177_712 = (let _177_711 = (let _177_710 = (let _177_709 = (FStar_SMTEncoding_Term.mkForall ((((f)::[])::[]), (cvars), (f_has_t)))
in ((_177_709), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_177_710))
in (_177_711)::[])
in (FStar_List.append decls'' _177_712)))
end)))
end)
in (

let interp_f = (

let a_name = Some ((Prims.strcat "interpretation_" fsym))
in (let _177_716 = (let _177_715 = (let _177_714 = (let _177_713 = (FStar_SMTEncoding_Term.mkEq ((app), (body)))
in ((((app)::[])::[]), ((FStar_List.append vars cvars)), (_177_713)))
in (FStar_SMTEncoding_Term.mkForall _177_714))
in ((_177_715), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_177_716)))
in (

let f_decls = (FStar_List.append decls (FStar_List.append decls' (FStar_List.append ((fdecl)::typing_f) ((interp_f)::[]))))
in (

let _85_1093 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash ((fsym), (cvar_sorts), (f_decls)))
in ((f), (f_decls)))))))))))
end)
end))))
end))
end))
end
end))))
end))
end
| FStar_Syntax_Syntax.Tm_let ((_85_1096, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_85_1108); FStar_Syntax_Syntax.lbunivs = _85_1106; FStar_Syntax_Syntax.lbtyp = _85_1104; FStar_Syntax_Syntax.lbeff = _85_1102; FStar_Syntax_Syntax.lbdef = _85_1100})::_85_1098), _85_1114) -> begin
(FStar_All.failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _85_1123; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _85_1120; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (_85_1133) -> begin
(

let _85_1135 = (FStar_TypeChecker_Errors.diag t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (

let e = (varops.fresh "let-rec")
in (

let decl_e = FStar_SMTEncoding_Term.DeclFun (((e), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (let _177_717 = (FStar_SMTEncoding_Term.mkFreeV ((e), (FStar_SMTEncoding_Term.Term_sort)))
in ((_177_717), ((decl_e)::[]))))))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end))))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (

let _85_1151 = (encode_term e1 env)
in (match (_85_1151) with
| (ee1, decls1) -> begin
(

let _85_1154 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) e2)
in (match (_85_1154) with
| (xs, e2) -> begin
(

let _85_1158 = (FStar_List.hd xs)
in (match (_85_1158) with
| (x, _85_1157) -> begin
(

let env' = (push_term_var env x ee1)
in (

let _85_1162 = (encode_body e2 env')
in (match (_85_1162) with
| (ee2, decls2) -> begin
((ee2), ((FStar_List.append decls1 decls2)))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (

let _85_1170 = (encode_term e env)
in (match (_85_1170) with
| (scr, decls) -> begin
(

let _85_1207 = (FStar_List.fold_right (fun b _85_1174 -> (match (_85_1174) with
| (else_case, decls) -> begin
(

let _85_1178 = (FStar_Syntax_Subst.open_branch b)
in (match (_85_1178) with
| (p, w, br) -> begin
(

let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun _85_1182 _85_1185 -> (match (((_85_1182), (_85_1185))) with
| ((env0, pattern), (else_case, decls)) -> begin
(

let guard = (pattern.guard scr)
in (

let projections = (pattern.projections scr)
in (

let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env _85_1191 -> (match (_85_1191) with
| (x, t) -> begin
(push_term_var env x t)
end)) env))
in (

let _85_1201 = (match (w) with
| None -> begin
((guard), ([]))
end
| Some (w) -> begin
(

let _85_1198 = (encode_term w env)
in (match (_85_1198) with
| (w, decls2) -> begin
(let _177_751 = (let _177_750 = (let _177_749 = (let _177_748 = (let _177_747 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Term.mkTrue)
in ((w), (_177_747)))
in (FStar_SMTEncoding_Term.mkEq _177_748))
in ((guard), (_177_749)))
in (FStar_SMTEncoding_Term.mkAnd _177_750))
in ((_177_751), (decls2)))
end))
end)
in (match (_85_1201) with
| (guard, decls2) -> begin
(

let _85_1204 = (encode_br br env)
in (match (_85_1204) with
| (br, decls3) -> begin
(let _177_752 = (FStar_SMTEncoding_Term.mkITE ((guard), (br), (else_case)))
in ((_177_752), ((FStar_List.append decls (FStar_List.append decls2 decls3)))))
end))
end)))))
end)) patterns ((else_case), (decls))))
end))
end)) pats ((default_case), (decls)))
in (match (_85_1207) with
| (match_tm, decls) -> begin
((match_tm), (decls))
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _85_1213 -> begin
(let _177_755 = (encode_one_pat env pat)
in (_177_755)::[])
end))
and encode_one_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> (

let _85_1216 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _177_758 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" _177_758))
end else begin
()
end
in (

let _85_1220 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (_85_1220) with
| (vars, pat_term) -> begin
(

let _85_1232 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun _85_1223 v -> (match (_85_1223) with
| (env, vars) -> begin
(

let _85_1229 = (gen_term_var env v)
in (match (_85_1229) with
| (xx, _85_1227, env) -> begin
((env), ((((v), (((xx), (FStar_SMTEncoding_Term.Term_sort)))))::vars))
end))
end)) ((env), ([]))))
in (match (_85_1232) with
| (env, vars) -> begin
(

let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_85_1237) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_dot_term (_)) -> begin
FStar_SMTEncoding_Term.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _177_766 = (let _177_765 = (encode_const c)
in ((scrutinee), (_177_765)))
in (FStar_SMTEncoding_Term.mkEq _177_766))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let is_f = (mk_data_tester env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _85_1259 -> (match (_85_1259) with
| (arg, _85_1258) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _177_769 = (FStar_SMTEncoding_Term.mkApp ((proj), ((scrutinee)::[])))
in (mk_guard arg _177_769)))
end))))
in (FStar_SMTEncoding_Term.mk_and_l ((is_f)::sub_term_guards))))
end))
in (

let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_85_1266) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _)) | (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_constant (_85_1276) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(let _177_777 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _85_1286 -> (match (_85_1286) with
| (arg, _85_1285) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _177_776 = (FStar_SMTEncoding_Term.mkApp ((proj), ((scrutinee)::[])))
in (mk_projections arg _177_776)))
end))))
in (FStar_All.pipe_right _177_777 FStar_List.flatten))
end))
in (

let pat_term = (fun _85_1289 -> (match (()) with
| () -> begin
(encode_term pat_term env)
end))
in (

let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in ((env), (pattern))))))
end))
end))))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (

let _85_1305 = (FStar_All.pipe_right l (FStar_List.fold_left (fun _85_1295 _85_1299 -> (match (((_85_1295), (_85_1299))) with
| ((tms, decls), (t, _85_1298)) -> begin
(

let _85_1302 = (encode_term t env)
in (match (_85_1302) with
| (t, decls') -> begin
(((t)::tms), ((FStar_List.append decls decls')))
end))
end)) (([]), ([]))))
in (match (_85_1305) with
| (l, decls) -> begin
(((FStar_List.rev l)), (decls))
end)))
and encode_function_type_as_formula : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun induction_on new_pats t env -> (

let rec list_elements = (fun e -> (

let _85_1314 = (let _177_790 = (FStar_Syntax_Util.unmeta e)
in (FStar_Syntax_Util.head_and_args _177_790))
in (match (_85_1314) with
| (head, args) -> begin
(match ((let _177_792 = (let _177_791 = (FStar_Syntax_Util.un_uinst head)
in _177_791.FStar_Syntax_Syntax.n)
in ((_177_792), (args)))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), _85_1318) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid) -> begin
[]
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_85_1331)::((hd, _85_1328))::((tl, _85_1324))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid) -> begin
(let _177_793 = (list_elements tl)
in (hd)::_177_793)
end
| _85_1335 -> begin
(

let _85_1336 = (FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern")
in [])
end)
end)))
in (

let one_pat = (fun p -> (

let _85_1342 = (let _177_796 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right _177_796 FStar_Syntax_Util.head_and_args))
in (match (_85_1342) with
| (head, args) -> begin
(match ((let _177_798 = (let _177_797 = (FStar_Syntax_Util.un_uinst head)
in _177_797.FStar_Syntax_Syntax.n)
in ((_177_798), (args)))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((_85_1350, _85_1352))::((e, _85_1347))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpat_lid) -> begin
((e), (None))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, _85_1360))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatT_lid) -> begin
((e), (None))
end
| _85_1365 -> begin
(FStar_All.failwith "Unexpected pattern term")
end)
end)))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements p)
in (

let smt_pat_or = (fun t -> (

let _85_1373 = (let _177_803 = (FStar_Syntax_Util.unmeta t)
in (FStar_All.pipe_right _177_803 FStar_Syntax_Util.head_and_args))
in (match (_85_1373) with
| (head, args) -> begin
(match ((let _177_805 = (let _177_804 = (FStar_Syntax_Util.un_uinst head)
in _177_804.FStar_Syntax_Syntax.n)
in ((_177_805), (args)))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, _85_1378))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatOr_lid) -> begin
Some (e)
end
| _85_1383 -> begin
None
end)
end)))
in (match (elts) with
| (t)::[] -> begin
(match ((smt_pat_or t)) with
| Some (e) -> begin
(let _177_808 = (list_elements e)
in (FStar_All.pipe_right _177_808 (FStar_List.map (fun branch -> (let _177_807 = (list_elements branch)
in (FStar_All.pipe_right _177_807 (FStar_List.map one_pat)))))))
end
| _85_1390 -> begin
(let _177_809 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_177_809)::[])
end)
end
| _85_1392 -> begin
(let _177_810 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_177_810)::[])
end))))
in (

let _85_1426 = (match ((let _177_811 = (FStar_Syntax_Subst.compress t)
in _177_811.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _85_1399 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_85_1399) with
| (binders, c) -> begin
(

let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| ((pre, _85_1411))::((post, _85_1407))::((pats, _85_1403))::[] -> begin
(

let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _177_812 = (lemma_pats pats')
in ((binders), (pre), (post), (_177_812))))
end
| _85_1419 -> begin
(FStar_All.failwith "impos")
end))
end))
end
| _85_1421 -> begin
(FStar_All.failwith "Impos")
end)
in (match (_85_1426) with
| (binders, pre, post, patterns) -> begin
(

let _85_1433 = (encode_binders None binders env)
in (match (_85_1433) with
| (vars, guards, env, decls, _85_1432) -> begin
(

let _85_1446 = (let _177_816 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (

let _85_1443 = (let _177_815 = (FStar_All.pipe_right branch (FStar_List.map (fun _85_1438 -> (match (_85_1438) with
| (t, _85_1437) -> begin
(encode_term t (

let _85_1439 = env
in {bindings = _85_1439.bindings; depth = _85_1439.depth; tcenv = _85_1439.tcenv; warn = _85_1439.warn; cache = _85_1439.cache; nolabels = _85_1439.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _85_1439.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _177_815 FStar_List.unzip))
in (match (_85_1443) with
| (pats, decls) -> begin
((pats), (decls))
end)))))
in (FStar_All.pipe_right _177_816 FStar_List.unzip))
in (match (_85_1446) with
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
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _177_819 = (let _177_818 = (FStar_SMTEncoding_Term.mkFreeV l)
in (FStar_SMTEncoding_Term.mk_Precedes _177_818 e))
in (_177_819)::p))))
end
| _85_1456 -> begin
(

let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _177_825 = (FStar_SMTEncoding_Term.mk_Precedes tl e)
in (_177_825)::p))))
end
| ((x, FStar_SMTEncoding_Term.Term_sort))::vars -> begin
(let _177_827 = (let _177_826 = (FStar_SMTEncoding_Term.mkFreeV ((x), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_LexCons _177_826 tl))
in (aux _177_827 vars))
end
| _85_1468 -> begin
pats
end))
in (let _177_828 = (FStar_SMTEncoding_Term.mkFreeV (("Prims.LexTop"), (FStar_SMTEncoding_Term.Term_sort)))
in (aux _177_828 vars)))
end)
end)
in (

let env = (

let _85_1470 = env
in {bindings = _85_1470.bindings; depth = _85_1470.depth; tcenv = _85_1470.tcenv; warn = _85_1470.warn; cache = _85_1470.cache; nolabels = true; use_zfuel_name = _85_1470.use_zfuel_name; encode_non_total_function_typ = _85_1470.encode_non_total_function_typ})
in (

let _85_1475 = (let _177_829 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula _177_829 env))
in (match (_85_1475) with
| (pre, decls'') -> begin
(

let _85_1478 = (let _177_830 = (FStar_Syntax_Util.unmeta post)
in (encode_formula _177_830 env))
in (match (_85_1478) with
| (post, decls''') -> begin
(

let decls = (FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') (FStar_List.append decls'' decls''')))
in (let _177_835 = (let _177_834 = (let _177_833 = (let _177_832 = (let _177_831 = (FStar_SMTEncoding_Term.mk_and_l ((pre)::guards))
in ((_177_831), (post)))
in (FStar_SMTEncoding_Term.mkImp _177_832))
in ((pats), (vars), (_177_833)))
in (FStar_SMTEncoding_Term.mkForall _177_834))
in ((_177_835), (decls))))
end))
end)))))
end))
end))
end))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (

let debug = (fun phi -> if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _177_841 = (FStar_Syntax_Print.tag_of_term phi)
in (let _177_840 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print2 "Formula (%s)  %s\n" _177_841 _177_840)))
end else begin
()
end)
in (

let enc = (fun f l -> (

let _85_1494 = (FStar_Util.fold_map (fun decls x -> (

let _85_1491 = (encode_term (Prims.fst x) env)
in (match (_85_1491) with
| (t, decls') -> begin
(((FStar_List.append decls decls')), (t))
end))) [] l)
in (match (_85_1494) with
| (decls, args) -> begin
(let _177_857 = (f args)
in ((_177_857), (decls)))
end)))
in (

let const_op = (fun f _85_1497 -> ((f), ([])))
in (

let un_op = (fun f l -> (let _177_871 = (FStar_List.hd l)
in (FStar_All.pipe_left f _177_871)))
in (

let bin_op = (fun f _85_10 -> (match (_85_10) with
| (t1)::(t2)::[] -> begin
(f ((t1), (t2)))
end
| _85_1508 -> begin
(FStar_All.failwith "Impossible")
end))
in (

let enc_prop_c = (fun f l -> (

let _85_1523 = (FStar_Util.fold_map (fun decls _85_1517 -> (match (_85_1517) with
| (t, _85_1516) -> begin
(

let _85_1520 = (encode_formula t env)
in (match (_85_1520) with
| (phi, decls') -> begin
(((FStar_List.append decls decls')), (phi))
end))
end)) [] l)
in (match (_85_1523) with
| (decls, phis) -> begin
(let _177_896 = (f phis)
in ((_177_896), (decls)))
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
| ((lhs, _85_1544))::((rhs, _85_1540))::[] -> begin
(

let _85_1549 = (encode_formula rhs env)
in (match (_85_1549) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _85_1552) -> begin
((l1), (decls1))
end
| _85_1556 -> begin
(

let _85_1559 = (encode_formula lhs env)
in (match (_85_1559) with
| (l2, decls2) -> begin
(let _177_901 = (FStar_SMTEncoding_Term.mkImp ((l2), (l1)))
in ((_177_901), ((FStar_List.append decls1 decls2))))
end))
end)
end))
end
| _85_1561 -> begin
(FStar_All.failwith "impossible")
end))
in (

let mk_ite = (fun _85_13 -> (match (_85_13) with
| ((guard, _85_1574))::((_then, _85_1570))::((_else, _85_1566))::[] -> begin
(

let _85_1579 = (encode_formula guard env)
in (match (_85_1579) with
| (g, decls1) -> begin
(

let _85_1582 = (encode_formula _then env)
in (match (_85_1582) with
| (t, decls2) -> begin
(

let _85_1585 = (encode_formula _else env)
in (match (_85_1585) with
| (e, decls3) -> begin
(

let res = (FStar_SMTEncoding_Term.mkITE ((g), (t), (e)))
in ((res), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end))
end))
end
| _85_1588 -> begin
(FStar_All.failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (let _177_913 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f _177_913)))
in (

let connectives = (let _177_969 = (let _177_922 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkAnd))
in ((FStar_Syntax_Const.and_lid), (_177_922)))
in (let _177_968 = (let _177_967 = (let _177_928 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkOr))
in ((FStar_Syntax_Const.or_lid), (_177_928)))
in (let _177_966 = (let _177_965 = (let _177_964 = (let _177_937 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkIff))
in ((FStar_Syntax_Const.iff_lid), (_177_937)))
in (let _177_963 = (let _177_962 = (let _177_961 = (let _177_946 = (FStar_All.pipe_left enc_prop_c (un_op FStar_SMTEncoding_Term.mkNot))
in ((FStar_Syntax_Const.not_lid), (_177_946)))
in (_177_961)::(((FStar_Syntax_Const.eq2_lid), (eq_op)))::(((FStar_Syntax_Const.eq3_lid), (eq_op)))::(((FStar_Syntax_Const.true_lid), ((const_op FStar_SMTEncoding_Term.mkTrue))))::(((FStar_Syntax_Const.false_lid), ((const_op FStar_SMTEncoding_Term.mkFalse))))::[])
in (((FStar_Syntax_Const.ite_lid), (mk_ite)))::_177_962)
in (_177_964)::_177_963))
in (((FStar_Syntax_Const.imp_lid), (mk_imp)))::_177_965)
in (_177_967)::_177_966))
in (_177_969)::_177_968))
in (

let rec fallback = (fun phi -> (match (phi.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(

let _85_1606 = (encode_formula phi' env)
in (match (_85_1606) with
| (phi, decls) -> begin
(let _177_972 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled (((phi), (msg), (r)))))
in ((_177_972), (decls)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (_85_1608) -> begin
(let _177_973 = (FStar_Syntax_Util.unmeta phi)
in (encode_formula _177_973 env))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(

let _85_1616 = (encode_match e pats FStar_SMTEncoding_Term.mkFalse env encode_formula)
in (match (_85_1616) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _85_1623; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _85_1620; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _85_1634 = (encode_let x t1 e1 e2 env encode_formula)
in (match (_85_1634) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let head = (FStar_Syntax_Util.un_uinst head)
in (match (((head.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_85_1651)::((x, _85_1648))::((t, _85_1644))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.has_type_lid) -> begin
(

let _85_1656 = (encode_term x env)
in (match (_85_1656) with
| (x, decls) -> begin
(

let _85_1659 = (encode_term t env)
in (match (_85_1659) with
| (t, decls') -> begin
(let _177_974 = (FStar_SMTEncoding_Term.mk_HasType x t)
in ((_177_974), ((FStar_List.append decls decls'))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((r, _85_1672))::((msg, _85_1668))::((phi, _85_1664))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.labeled_lid) -> begin
(match ((let _177_978 = (let _177_975 = (FStar_Syntax_Subst.compress r)
in _177_975.FStar_Syntax_Syntax.n)
in (let _177_977 = (let _177_976 = (FStar_Syntax_Subst.compress msg)
in _177_976.FStar_Syntax_Syntax.n)
in ((_177_978), (_177_977))))) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, _85_1681))) -> begin
(

let phi = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((phi), (FStar_Syntax_Syntax.Meta_labeled ((((FStar_Util.string_of_unicode s)), (r), (false))))))) None r)
in (fallback phi))
end
| _85_1688 -> begin
(fallback phi)
end)
end
| _85_1690 when (head_redex env head) -> begin
(let _177_979 = (whnf env phi)
in (encode_formula _177_979 env))
end
| _85_1692 -> begin
(

let _85_1695 = (encode_term phi env)
in (match (_85_1695) with
| (tt, decls) -> begin
(let _177_980 = (FStar_SMTEncoding_Term.mk_Valid tt)
in ((_177_980), (decls)))
end))
end))
end
| _85_1697 -> begin
(

let _85_1700 = (encode_term phi env)
in (match (_85_1700) with
| (tt, decls) -> begin
(let _177_981 = (FStar_SMTEncoding_Term.mk_Valid tt)
in ((_177_981), (decls)))
end))
end))
in (

let encode_q_body = (fun env bs ps body -> (

let _85_1712 = (encode_binders None bs env)
in (match (_85_1712) with
| (vars, guards, env, decls, _85_1711) -> begin
(

let _85_1725 = (let _177_993 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let _85_1722 = (let _177_992 = (FStar_All.pipe_right p (FStar_List.map (fun _85_1717 -> (match (_85_1717) with
| (t, _85_1716) -> begin
(encode_term t (

let _85_1718 = env
in {bindings = _85_1718.bindings; depth = _85_1718.depth; tcenv = _85_1718.tcenv; warn = _85_1718.warn; cache = _85_1718.cache; nolabels = _85_1718.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _85_1718.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _177_992 FStar_List.unzip))
in (match (_85_1722) with
| (p, decls) -> begin
((p), ((FStar_List.flatten decls)))
end)))))
in (FStar_All.pipe_right _177_993 FStar_List.unzip))
in (match (_85_1725) with
| (pats, decls') -> begin
(

let _85_1728 = (encode_formula body env)
in (match (_85_1728) with
| (body, decls'') -> begin
(

let guards = (match (pats) with
| (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (gf), (p)::[]); FStar_SMTEncoding_Term.hash = _85_1732; FStar_SMTEncoding_Term.freevars = _85_1730})::[])::[] when ((FStar_Ident.text_of_lid FStar_Syntax_Const.guard_free) = gf) -> begin
[]
end
| _85_1743 -> begin
guards
end)
in (let _177_994 = (FStar_SMTEncoding_Term.mk_and_l guards)
in ((vars), (pats), (_177_994), (body), ((FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') decls''))))))
end))
end))
end)))
in (

let _85_1745 = (debug phi)
in (

let phi = (FStar_Syntax_Util.unascribe phi)
in (match ((FStar_Syntax_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _85_1757 -> (match (_85_1757) with
| (l, _85_1756) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_85_1760, f) -> begin
(f arms)
end)
end
| Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
(

let _85_1770 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _177_1011 = (FStar_All.pipe_right vars (FStar_Syntax_Print.binders_to_string "; "))
in (FStar_Util.print1 ">>>> Got QALL [%s]\n" _177_1011))
end else begin
()
end
in (

let _85_1777 = (encode_q_body env vars pats body)
in (match (_85_1777) with
| (vars, pats, guard, body, decls) -> begin
(

let tm = (let _177_1013 = (let _177_1012 = (FStar_SMTEncoding_Term.mkImp ((guard), (body)))
in ((pats), (vars), (_177_1012)))
in (FStar_SMTEncoding_Term.mkForall _177_1013))
in (

let _85_1779 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _177_1014 = (FStar_SMTEncoding_Term.termToSmt tm)
in (FStar_Util.print1 ">>>> Encoded QALL to %s\n" _177_1014))
end else begin
()
end
in ((tm), (decls))))
end)))
end
| Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
(

let _85_1792 = (encode_q_body env vars pats body)
in (match (_85_1792) with
| (vars, pats, guard, body, decls) -> begin
(let _177_1017 = (let _177_1016 = (let _177_1015 = (FStar_SMTEncoding_Term.mkAnd ((guard), (body)))
in ((pats), (vars), (_177_1015)))
in (FStar_SMTEncoding_Term.mkExists _177_1016))
in ((_177_1017), (decls)))
end))
end)))))))))))))))))


type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.decl Prims.list; is : FStar_Ident.lident  ->  Prims.bool}


let is_Mkprims_t : prims_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkprims_t"))))


let prims : prims_t = (

let _85_1798 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (_85_1798) with
| (asym, a) -> begin
(

let _85_1801 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_85_1801) with
| (xsym, x) -> begin
(

let _85_1804 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (_85_1804) with
| (ysym, y) -> begin
(

let deffun = (fun vars body x -> (FStar_SMTEncoding_Term.DefineFun (((x), (vars), (FStar_SMTEncoding_Term.Term_sort), (body), (None))))::[])
in (

let quant = (fun vars body x -> (

let t1 = (let _177_1060 = (let _177_1059 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in ((x), (_177_1059)))
in (FStar_SMTEncoding_Term.mkApp _177_1060))
in (

let vname_decl = (let _177_1062 = (let _177_1061 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in ((x), (_177_1061), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (_177_1062))
in (let _177_1068 = (let _177_1067 = (let _177_1066 = (let _177_1065 = (let _177_1064 = (let _177_1063 = (FStar_SMTEncoding_Term.mkEq ((t1), (body)))
in ((((t1)::[])::[]), (vars), (_177_1063)))
in (FStar_SMTEncoding_Term.mkForall _177_1064))
in ((_177_1065), (None), (Some ((Prims.strcat "primitive_" x)))))
in FStar_SMTEncoding_Term.Assume (_177_1066))
in (_177_1067)::[])
in (vname_decl)::_177_1068))))
in (

let axy = (((asym), (FStar_SMTEncoding_Term.Term_sort)))::(((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let xy = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let qx = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let prims = (let _177_1228 = (let _177_1077 = (let _177_1076 = (let _177_1075 = (FStar_SMTEncoding_Term.mkEq ((x), (y)))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1075))
in (quant axy _177_1076))
in ((FStar_Syntax_Const.op_Eq), (_177_1077)))
in (let _177_1227 = (let _177_1226 = (let _177_1084 = (let _177_1083 = (let _177_1082 = (let _177_1081 = (FStar_SMTEncoding_Term.mkEq ((x), (y)))
in (FStar_SMTEncoding_Term.mkNot _177_1081))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1082))
in (quant axy _177_1083))
in ((FStar_Syntax_Const.op_notEq), (_177_1084)))
in (let _177_1225 = (let _177_1224 = (let _177_1093 = (let _177_1092 = (let _177_1091 = (let _177_1090 = (let _177_1089 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1088 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_177_1089), (_177_1088))))
in (FStar_SMTEncoding_Term.mkLT _177_1090))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1091))
in (quant xy _177_1092))
in ((FStar_Syntax_Const.op_LT), (_177_1093)))
in (let _177_1223 = (let _177_1222 = (let _177_1102 = (let _177_1101 = (let _177_1100 = (let _177_1099 = (let _177_1098 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1097 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_177_1098), (_177_1097))))
in (FStar_SMTEncoding_Term.mkLTE _177_1099))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1100))
in (quant xy _177_1101))
in ((FStar_Syntax_Const.op_LTE), (_177_1102)))
in (let _177_1221 = (let _177_1220 = (let _177_1111 = (let _177_1110 = (let _177_1109 = (let _177_1108 = (let _177_1107 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1106 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_177_1107), (_177_1106))))
in (FStar_SMTEncoding_Term.mkGT _177_1108))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1109))
in (quant xy _177_1110))
in ((FStar_Syntax_Const.op_GT), (_177_1111)))
in (let _177_1219 = (let _177_1218 = (let _177_1120 = (let _177_1119 = (let _177_1118 = (let _177_1117 = (let _177_1116 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1115 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_177_1116), (_177_1115))))
in (FStar_SMTEncoding_Term.mkGTE _177_1117))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1118))
in (quant xy _177_1119))
in ((FStar_Syntax_Const.op_GTE), (_177_1120)))
in (let _177_1217 = (let _177_1216 = (let _177_1129 = (let _177_1128 = (let _177_1127 = (let _177_1126 = (let _177_1125 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1124 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_177_1125), (_177_1124))))
in (FStar_SMTEncoding_Term.mkSub _177_1126))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _177_1127))
in (quant xy _177_1128))
in ((FStar_Syntax_Const.op_Subtraction), (_177_1129)))
in (let _177_1215 = (let _177_1214 = (let _177_1136 = (let _177_1135 = (let _177_1134 = (let _177_1133 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Term.mkMinus _177_1133))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _177_1134))
in (quant qx _177_1135))
in ((FStar_Syntax_Const.op_Minus), (_177_1136)))
in (let _177_1213 = (let _177_1212 = (let _177_1145 = (let _177_1144 = (let _177_1143 = (let _177_1142 = (let _177_1141 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1140 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_177_1141), (_177_1140))))
in (FStar_SMTEncoding_Term.mkAdd _177_1142))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _177_1143))
in (quant xy _177_1144))
in ((FStar_Syntax_Const.op_Addition), (_177_1145)))
in (let _177_1211 = (let _177_1210 = (let _177_1154 = (let _177_1153 = (let _177_1152 = (let _177_1151 = (let _177_1150 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1149 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_177_1150), (_177_1149))))
in (FStar_SMTEncoding_Term.mkMul _177_1151))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _177_1152))
in (quant xy _177_1153))
in ((FStar_Syntax_Const.op_Multiply), (_177_1154)))
in (let _177_1209 = (let _177_1208 = (let _177_1163 = (let _177_1162 = (let _177_1161 = (let _177_1160 = (let _177_1159 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1158 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_177_1159), (_177_1158))))
in (FStar_SMTEncoding_Term.mkDiv _177_1160))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _177_1161))
in (quant xy _177_1162))
in ((FStar_Syntax_Const.op_Division), (_177_1163)))
in (let _177_1207 = (let _177_1206 = (let _177_1172 = (let _177_1171 = (let _177_1170 = (let _177_1169 = (let _177_1168 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1167 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_177_1168), (_177_1167))))
in (FStar_SMTEncoding_Term.mkMod _177_1169))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _177_1170))
in (quant xy _177_1171))
in ((FStar_Syntax_Const.op_Modulus), (_177_1172)))
in (let _177_1205 = (let _177_1204 = (let _177_1181 = (let _177_1180 = (let _177_1179 = (let _177_1178 = (let _177_1177 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _177_1176 = (FStar_SMTEncoding_Term.unboxBool y)
in ((_177_1177), (_177_1176))))
in (FStar_SMTEncoding_Term.mkAnd _177_1178))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1179))
in (quant xy _177_1180))
in ((FStar_Syntax_Const.op_And), (_177_1181)))
in (let _177_1203 = (let _177_1202 = (let _177_1190 = (let _177_1189 = (let _177_1188 = (let _177_1187 = (let _177_1186 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _177_1185 = (FStar_SMTEncoding_Term.unboxBool y)
in ((_177_1186), (_177_1185))))
in (FStar_SMTEncoding_Term.mkOr _177_1187))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1188))
in (quant xy _177_1189))
in ((FStar_Syntax_Const.op_Or), (_177_1190)))
in (let _177_1201 = (let _177_1200 = (let _177_1197 = (let _177_1196 = (let _177_1195 = (let _177_1194 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Term.mkNot _177_1194))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1195))
in (quant qx _177_1196))
in ((FStar_Syntax_Const.op_Negation), (_177_1197)))
in (_177_1200)::[])
in (_177_1202)::_177_1201))
in (_177_1204)::_177_1203))
in (_177_1206)::_177_1205))
in (_177_1208)::_177_1207))
in (_177_1210)::_177_1209))
in (_177_1212)::_177_1211))
in (_177_1214)::_177_1213))
in (_177_1216)::_177_1215))
in (_177_1218)::_177_1217))
in (_177_1220)::_177_1219))
in (_177_1222)::_177_1221))
in (_177_1224)::_177_1223))
in (_177_1226)::_177_1225))
in (_177_1228)::_177_1227))
in (

let mk = (fun l v -> (let _177_1260 = (FStar_All.pipe_right prims (FStar_List.filter (fun _85_1824 -> (match (_85_1824) with
| (l', _85_1823) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right _177_1260 (FStar_List.collect (fun _85_1828 -> (match (_85_1828) with
| (_85_1826, b) -> begin
(b v)
end))))))
in (

let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _85_1834 -> (match (_85_1834) with
| (l', _85_1833) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is}))))))))
end))
end))
end))


let pretype_axiom : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun tapp vars -> (

let _85_1840 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_85_1840) with
| (xxsym, xx) -> begin
(

let _85_1843 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_85_1843) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (let _177_1290 = (let _177_1289 = (let _177_1284 = (let _177_1283 = (let _177_1282 = (let _177_1281 = (let _177_1280 = (let _177_1279 = (FStar_SMTEncoding_Term.mkApp (("PreType"), ((xx)::[])))
in ((tapp), (_177_1279)))
in (FStar_SMTEncoding_Term.mkEq _177_1280))
in ((xx_has_type), (_177_1281)))
in (FStar_SMTEncoding_Term.mkImp _177_1282))
in ((((xx_has_type)::[])::[]), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars), (_177_1283)))
in (FStar_SMTEncoding_Term.mkForall _177_1284))
in (let _177_1288 = (let _177_1287 = (let _177_1286 = (let _177_1285 = (FStar_Util.digest_of_string tapp.FStar_SMTEncoding_Term.hash)
in (Prims.strcat "pretyping_" _177_1285))
in (varops.mk_unique _177_1286))
in Some (_177_1287))
in ((_177_1289), (Some ("pretyping")), (_177_1288))))
in FStar_SMTEncoding_Term.Assume (_177_1290)))
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
in (let _177_1311 = (let _177_1302 = (let _177_1301 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in ((_177_1301), (Some ("unit typing")), (Some ("unit_typing"))))
in FStar_SMTEncoding_Term.Assume (_177_1302))
in (let _177_1310 = (let _177_1309 = (let _177_1308 = (let _177_1307 = (let _177_1306 = (let _177_1305 = (let _177_1304 = (let _177_1303 = (FStar_SMTEncoding_Term.mkEq ((x), (FStar_SMTEncoding_Term.mk_Term_unit)))
in ((typing_pred), (_177_1303)))
in (FStar_SMTEncoding_Term.mkImp _177_1304))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_177_1305)))
in (mkForall_fuel _177_1306))
in ((_177_1307), (Some ("unit inversion")), (Some ("unit_inversion"))))
in FStar_SMTEncoding_Term.Assume (_177_1308))
in (_177_1309)::[])
in (_177_1311)::_177_1310))))
in (

let mk_bool = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Bool_sort))
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _177_1334 = (let _177_1325 = (let _177_1324 = (let _177_1323 = (let _177_1322 = (let _177_1319 = (let _177_1318 = (FStar_SMTEncoding_Term.boxBool b)
in (_177_1318)::[])
in (_177_1319)::[])
in (let _177_1321 = (let _177_1320 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType _177_1320 tt))
in ((_177_1322), ((bb)::[]), (_177_1321))))
in (FStar_SMTEncoding_Term.mkForall _177_1323))
in ((_177_1324), (Some ("bool typing")), (Some ("bool_typing"))))
in FStar_SMTEncoding_Term.Assume (_177_1325))
in (let _177_1333 = (let _177_1332 = (let _177_1331 = (let _177_1330 = (let _177_1329 = (let _177_1328 = (let _177_1327 = (let _177_1326 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in ((typing_pred), (_177_1326)))
in (FStar_SMTEncoding_Term.mkImp _177_1327))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_177_1328)))
in (mkForall_fuel _177_1329))
in ((_177_1330), (Some ("bool inversion")), (Some ("bool_inversion"))))
in FStar_SMTEncoding_Term.Assume (_177_1331))
in (_177_1332)::[])
in (_177_1334)::_177_1333))))))
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

let precedes = (let _177_1348 = (let _177_1347 = (let _177_1346 = (let _177_1345 = (let _177_1344 = (let _177_1343 = (FStar_SMTEncoding_Term.boxInt a)
in (let _177_1342 = (let _177_1341 = (FStar_SMTEncoding_Term.boxInt b)
in (_177_1341)::[])
in (_177_1343)::_177_1342))
in (tt)::_177_1344)
in (tt)::_177_1345)
in (("Prims.Precedes"), (_177_1346)))
in (FStar_SMTEncoding_Term.mkApp _177_1347))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _177_1348))
in (

let precedes_y_x = (let _177_1349 = (FStar_SMTEncoding_Term.mkApp (("Precedes"), ((y)::(x)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _177_1349))
in (let _177_1391 = (let _177_1357 = (let _177_1356 = (let _177_1355 = (let _177_1354 = (let _177_1351 = (let _177_1350 = (FStar_SMTEncoding_Term.boxInt b)
in (_177_1350)::[])
in (_177_1351)::[])
in (let _177_1353 = (let _177_1352 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType _177_1352 tt))
in ((_177_1354), ((bb)::[]), (_177_1353))))
in (FStar_SMTEncoding_Term.mkForall _177_1355))
in ((_177_1356), (Some ("int typing")), (Some ("int_typing"))))
in FStar_SMTEncoding_Term.Assume (_177_1357))
in (let _177_1390 = (let _177_1389 = (let _177_1363 = (let _177_1362 = (let _177_1361 = (let _177_1360 = (let _177_1359 = (let _177_1358 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in ((typing_pred), (_177_1358)))
in (FStar_SMTEncoding_Term.mkImp _177_1359))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_177_1360)))
in (mkForall_fuel _177_1361))
in ((_177_1362), (Some ("int inversion")), (Some ("int_inversion"))))
in FStar_SMTEncoding_Term.Assume (_177_1363))
in (let _177_1388 = (let _177_1387 = (let _177_1386 = (let _177_1385 = (let _177_1384 = (let _177_1383 = (let _177_1382 = (let _177_1381 = (let _177_1380 = (let _177_1379 = (let _177_1378 = (let _177_1377 = (let _177_1366 = (let _177_1365 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1364 = (FStar_SMTEncoding_Term.mkInteger' 0)
in ((_177_1365), (_177_1364))))
in (FStar_SMTEncoding_Term.mkGT _177_1366))
in (let _177_1376 = (let _177_1375 = (let _177_1369 = (let _177_1368 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _177_1367 = (FStar_SMTEncoding_Term.mkInteger' 0)
in ((_177_1368), (_177_1367))))
in (FStar_SMTEncoding_Term.mkGTE _177_1369))
in (let _177_1374 = (let _177_1373 = (let _177_1372 = (let _177_1371 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _177_1370 = (FStar_SMTEncoding_Term.unboxInt x)
in ((_177_1371), (_177_1370))))
in (FStar_SMTEncoding_Term.mkLT _177_1372))
in (_177_1373)::[])
in (_177_1375)::_177_1374))
in (_177_1377)::_177_1376))
in (typing_pred_y)::_177_1378)
in (typing_pred)::_177_1379)
in (FStar_SMTEncoding_Term.mk_and_l _177_1380))
in ((_177_1381), (precedes_y_x)))
in (FStar_SMTEncoding_Term.mkImp _177_1382))
in ((((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[]), ((xx)::(yy)::[]), (_177_1383)))
in (mkForall_fuel _177_1384))
in ((_177_1385), (Some ("well-founded ordering on nat (alt)")), (Some ("well-founded-ordering-on-nat"))))
in FStar_SMTEncoding_Term.Assume (_177_1386))
in (_177_1387)::[])
in (_177_1389)::_177_1388))
in (_177_1391)::_177_1390)))))))))))
in (

let mk_str = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.String_sort))
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _177_1414 = (let _177_1405 = (let _177_1404 = (let _177_1403 = (let _177_1402 = (let _177_1399 = (let _177_1398 = (FStar_SMTEncoding_Term.boxString b)
in (_177_1398)::[])
in (_177_1399)::[])
in (let _177_1401 = (let _177_1400 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType _177_1400 tt))
in ((_177_1402), ((bb)::[]), (_177_1401))))
in (FStar_SMTEncoding_Term.mkForall _177_1403))
in ((_177_1404), (Some ("string typing")), (Some ("string_typing"))))
in FStar_SMTEncoding_Term.Assume (_177_1405))
in (let _177_1413 = (let _177_1412 = (let _177_1411 = (let _177_1410 = (let _177_1409 = (let _177_1408 = (let _177_1407 = (let _177_1406 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in ((typing_pred), (_177_1406)))
in (FStar_SMTEncoding_Term.mkImp _177_1407))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_177_1408)))
in (mkForall_fuel _177_1409))
in ((_177_1410), (Some ("string inversion")), (Some ("string_inversion"))))
in FStar_SMTEncoding_Term.Assume (_177_1411))
in (_177_1412)::[])
in (_177_1414)::_177_1413))))))
in (

let mk_ref = (fun env reft_name _85_1882 -> (

let r = (("r"), (FStar_SMTEncoding_Term.Ref_sort))
in (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let refa = (let _177_1423 = (let _177_1422 = (let _177_1421 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (_177_1421)::[])
in ((reft_name), (_177_1422)))
in (FStar_SMTEncoding_Term.mkApp _177_1423))
in (

let refb = (let _177_1426 = (let _177_1425 = (let _177_1424 = (FStar_SMTEncoding_Term.mkFreeV bb)
in (_177_1424)::[])
in ((reft_name), (_177_1425)))
in (FStar_SMTEncoding_Term.mkApp _177_1426))
in (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (

let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (let _177_1445 = (let _177_1432 = (let _177_1431 = (let _177_1430 = (let _177_1429 = (let _177_1428 = (let _177_1427 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in ((typing_pred), (_177_1427)))
in (FStar_SMTEncoding_Term.mkImp _177_1428))
in ((((typing_pred)::[])::[]), ((xx)::(aa)::[]), (_177_1429)))
in (mkForall_fuel _177_1430))
in ((_177_1431), (Some ("ref inversion")), (Some ("ref_inversion"))))
in FStar_SMTEncoding_Term.Assume (_177_1432))
in (let _177_1444 = (let _177_1443 = (let _177_1442 = (let _177_1441 = (let _177_1440 = (let _177_1439 = (let _177_1438 = (let _177_1437 = (FStar_SMTEncoding_Term.mkAnd ((typing_pred), (typing_pred_b)))
in (let _177_1436 = (let _177_1435 = (let _177_1434 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (let _177_1433 = (FStar_SMTEncoding_Term.mkFreeV bb)
in ((_177_1434), (_177_1433))))
in (FStar_SMTEncoding_Term.mkEq _177_1435))
in ((_177_1437), (_177_1436))))
in (FStar_SMTEncoding_Term.mkImp _177_1438))
in ((((typing_pred)::(typing_pred_b)::[])::[]), ((xx)::(aa)::(bb)::[]), (_177_1439)))
in (mkForall_fuel' 2 _177_1440))
in ((_177_1441), (Some ("ref typing is injective")), (Some ("ref_injectivity"))))
in FStar_SMTEncoding_Term.Assume (_177_1442))
in (_177_1443)::[])
in (_177_1445)::_177_1444))))))))))
in (

let mk_false_interp = (fun env nm false_tm -> (

let valid = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((false_tm)::[])))
in (let _177_1454 = (let _177_1453 = (let _177_1452 = (FStar_SMTEncoding_Term.mkIff ((FStar_SMTEncoding_Term.mkFalse), (valid)))
in ((_177_1452), (Some ("False interpretation")), (Some ("false_interp"))))
in FStar_SMTEncoding_Term.Assume (_177_1453))
in (_177_1454)::[])))
in (

let mk_and_interp = (fun env conj _85_1899 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (

let valid = (let _177_1463 = (let _177_1462 = (let _177_1461 = (FStar_SMTEncoding_Term.mkApp ((conj), ((a)::(b)::[])))
in (_177_1461)::[])
in (("Valid"), (_177_1462)))
in (FStar_SMTEncoding_Term.mkApp _177_1463))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((b)::[])))
in (let _177_1470 = (let _177_1469 = (let _177_1468 = (let _177_1467 = (let _177_1466 = (let _177_1465 = (let _177_1464 = (FStar_SMTEncoding_Term.mkAnd ((valid_a), (valid_b)))
in ((_177_1464), (valid)))
in (FStar_SMTEncoding_Term.mkIff _177_1465))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_177_1466)))
in (FStar_SMTEncoding_Term.mkForall _177_1467))
in ((_177_1468), (Some ("/\\ interpretation")), (Some ("l_and-interp"))))
in FStar_SMTEncoding_Term.Assume (_177_1469))
in (_177_1470)::[])))))))))
in (

let mk_or_interp = (fun env disj _85_1911 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (

let valid = (let _177_1479 = (let _177_1478 = (let _177_1477 = (FStar_SMTEncoding_Term.mkApp ((disj), ((a)::(b)::[])))
in (_177_1477)::[])
in (("Valid"), (_177_1478)))
in (FStar_SMTEncoding_Term.mkApp _177_1479))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((b)::[])))
in (let _177_1486 = (let _177_1485 = (let _177_1484 = (let _177_1483 = (let _177_1482 = (let _177_1481 = (let _177_1480 = (FStar_SMTEncoding_Term.mkOr ((valid_a), (valid_b)))
in ((_177_1480), (valid)))
in (FStar_SMTEncoding_Term.mkIff _177_1481))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_177_1482)))
in (FStar_SMTEncoding_Term.mkForall _177_1483))
in ((_177_1484), (Some ("\\/ interpretation")), (Some ("l_or-interp"))))
in FStar_SMTEncoding_Term.Assume (_177_1485))
in (_177_1486)::[])))))))))
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

let valid = (let _177_1495 = (let _177_1494 = (let _177_1493 = (FStar_SMTEncoding_Term.mkApp ((eq2), ((a)::(x)::(y)::[])))
in (_177_1493)::[])
in (("Valid"), (_177_1494)))
in (FStar_SMTEncoding_Term.mkApp _177_1495))
in (let _177_1502 = (let _177_1501 = (let _177_1500 = (let _177_1499 = (let _177_1498 = (let _177_1497 = (let _177_1496 = (FStar_SMTEncoding_Term.mkEq ((x), (y)))
in ((_177_1496), (valid)))
in (FStar_SMTEncoding_Term.mkIff _177_1497))
in ((((valid)::[])::[]), ((aa)::(xx)::(yy)::[]), (_177_1498)))
in (FStar_SMTEncoding_Term.mkForall _177_1499))
in ((_177_1500), (Some ("Eq2 interpretation")), (Some ("eq2-interp"))))
in FStar_SMTEncoding_Term.Assume (_177_1501))
in (_177_1502)::[])))))))))
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

let valid = (let _177_1511 = (let _177_1510 = (let _177_1509 = (FStar_SMTEncoding_Term.mkApp ((eq3), ((a)::(b)::(x)::(y)::[])))
in (_177_1509)::[])
in (("Valid"), (_177_1510)))
in (FStar_SMTEncoding_Term.mkApp _177_1511))
in (let _177_1518 = (let _177_1517 = (let _177_1516 = (let _177_1515 = (let _177_1514 = (let _177_1513 = (let _177_1512 = (FStar_SMTEncoding_Term.mkEq ((x), (y)))
in ((_177_1512), (valid)))
in (FStar_SMTEncoding_Term.mkIff _177_1513))
in ((((valid)::[])::[]), ((aa)::(bb)::(xx)::(yy)::[]), (_177_1514)))
in (FStar_SMTEncoding_Term.mkForall _177_1515))
in ((_177_1516), (Some ("Eq3 interpretation")), (Some ("eq3-interp"))))
in FStar_SMTEncoding_Term.Assume (_177_1517))
in (_177_1518)::[])))))))))))
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

let valid = (let _177_1527 = (let _177_1526 = (let _177_1525 = (FStar_SMTEncoding_Term.mkApp ((imp), ((a)::(b)::[])))
in (_177_1525)::[])
in (("Valid"), (_177_1526)))
in (FStar_SMTEncoding_Term.mkApp _177_1527))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((b)::[])))
in (let _177_1534 = (let _177_1533 = (let _177_1532 = (let _177_1531 = (let _177_1530 = (let _177_1529 = (let _177_1528 = (FStar_SMTEncoding_Term.mkImp ((valid_a), (valid_b)))
in ((_177_1528), (valid)))
in (FStar_SMTEncoding_Term.mkIff _177_1529))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_177_1530)))
in (FStar_SMTEncoding_Term.mkForall _177_1531))
in ((_177_1532), (Some ("==> interpretation")), (Some ("l_imp-interp"))))
in FStar_SMTEncoding_Term.Assume (_177_1533))
in (_177_1534)::[])))))))))
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

let valid = (let _177_1543 = (let _177_1542 = (let _177_1541 = (FStar_SMTEncoding_Term.mkApp ((iff), ((a)::(b)::[])))
in (_177_1541)::[])
in (("Valid"), (_177_1542)))
in (FStar_SMTEncoding_Term.mkApp _177_1543))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((b)::[])))
in (let _177_1550 = (let _177_1549 = (let _177_1548 = (let _177_1547 = (let _177_1546 = (let _177_1545 = (let _177_1544 = (FStar_SMTEncoding_Term.mkIff ((valid_a), (valid_b)))
in ((_177_1544), (valid)))
in (FStar_SMTEncoding_Term.mkIff _177_1545))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_177_1546)))
in (FStar_SMTEncoding_Term.mkForall _177_1547))
in ((_177_1548), (Some ("<==> interpretation")), (Some ("l_iff-interp"))))
in FStar_SMTEncoding_Term.Assume (_177_1549))
in (_177_1550)::[])))))))))
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

let valid = (let _177_1559 = (let _177_1558 = (let _177_1557 = (FStar_SMTEncoding_Term.mkApp ((for_all), ((a)::(b)::[])))
in (_177_1557)::[])
in (("Valid"), (_177_1558)))
in (FStar_SMTEncoding_Term.mkApp _177_1559))
in (

let valid_b_x = (let _177_1562 = (let _177_1561 = (let _177_1560 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_177_1560)::[])
in (("Valid"), (_177_1561)))
in (FStar_SMTEncoding_Term.mkApp _177_1562))
in (let _177_1576 = (let _177_1575 = (let _177_1574 = (let _177_1573 = (let _177_1572 = (let _177_1571 = (let _177_1570 = (let _177_1569 = (let _177_1568 = (let _177_1564 = (let _177_1563 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_177_1563)::[])
in (_177_1564)::[])
in (let _177_1567 = (let _177_1566 = (let _177_1565 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((_177_1565), (valid_b_x)))
in (FStar_SMTEncoding_Term.mkImp _177_1566))
in ((_177_1568), ((xx)::[]), (_177_1567))))
in (FStar_SMTEncoding_Term.mkForall _177_1569))
in ((_177_1570), (valid)))
in (FStar_SMTEncoding_Term.mkIff _177_1571))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_177_1572)))
in (FStar_SMTEncoding_Term.mkForall _177_1573))
in ((_177_1574), (Some ("forall interpretation")), (Some ("forall-interp"))))
in FStar_SMTEncoding_Term.Assume (_177_1575))
in (_177_1576)::[]))))))))))
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

let valid = (let _177_1585 = (let _177_1584 = (let _177_1583 = (FStar_SMTEncoding_Term.mkApp ((for_some), ((a)::(b)::[])))
in (_177_1583)::[])
in (("Valid"), (_177_1584)))
in (FStar_SMTEncoding_Term.mkApp _177_1585))
in (

let valid_b_x = (let _177_1588 = (let _177_1587 = (let _177_1586 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_177_1586)::[])
in (("Valid"), (_177_1587)))
in (FStar_SMTEncoding_Term.mkApp _177_1588))
in (let _177_1602 = (let _177_1601 = (let _177_1600 = (let _177_1599 = (let _177_1598 = (let _177_1597 = (let _177_1596 = (let _177_1595 = (let _177_1594 = (let _177_1590 = (let _177_1589 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_177_1589)::[])
in (_177_1590)::[])
in (let _177_1593 = (let _177_1592 = (let _177_1591 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((_177_1591), (valid_b_x)))
in (FStar_SMTEncoding_Term.mkImp _177_1592))
in ((_177_1594), ((xx)::[]), (_177_1593))))
in (FStar_SMTEncoding_Term.mkExists _177_1595))
in ((_177_1596), (valid)))
in (FStar_SMTEncoding_Term.mkIff _177_1597))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_177_1598)))
in (FStar_SMTEncoding_Term.mkForall _177_1599))
in ((_177_1600), (Some ("exists interpretation")), (Some ("exists-interp"))))
in FStar_SMTEncoding_Term.Assume (_177_1601))
in (_177_1602)::[]))))))))))
in (

let mk_range_interp = (fun env range tt -> (

let range_ty = (FStar_SMTEncoding_Term.mkApp ((range), ([])))
in (let _177_1613 = (let _177_1612 = (let _177_1611 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_ty)
in (let _177_1610 = (let _177_1609 = (varops.fresh "typing_range_const")
in Some (_177_1609))
in ((_177_1611), (Some ("Range_const typing")), (_177_1610))))
in FStar_SMTEncoding_Term.Assume (_177_1612))
in (_177_1613)::[])))
in (

let prims = (((FStar_Syntax_Const.unit_lid), (mk_unit)))::(((FStar_Syntax_Const.bool_lid), (mk_bool)))::(((FStar_Syntax_Const.int_lid), (mk_int)))::(((FStar_Syntax_Const.string_lid), (mk_str)))::(((FStar_Syntax_Const.ref_lid), (mk_ref)))::(((FStar_Syntax_Const.false_lid), (mk_false_interp)))::(((FStar_Syntax_Const.and_lid), (mk_and_interp)))::(((FStar_Syntax_Const.or_lid), (mk_or_interp)))::(((FStar_Syntax_Const.eq2_lid), (mk_eq2_interp)))::(((FStar_Syntax_Const.eq3_lid), (mk_eq3_interp)))::(((FStar_Syntax_Const.imp_lid), (mk_imp_interp)))::(((FStar_Syntax_Const.iff_lid), (mk_iff_interp)))::(((FStar_Syntax_Const.forall_lid), (mk_forall_interp)))::(((FStar_Syntax_Const.exists_lid), (mk_exists_interp)))::(((FStar_Syntax_Const.range_lid), (mk_range_interp)))::[]
in (fun env t s tt -> (match ((FStar_Util.find_opt (fun _85_2004 -> (match (_85_2004) with
| (l, _85_2003) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_85_2007, f) -> begin
(f env s tt)
end))))))))))))))))))))))


let encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let _85_2017 = (encode_function_type_as_formula None None t env)
in (match (_85_2017) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_SMTEncoding_Term.Assume (((form), (Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str))), (Some ((Prims.strcat "lemma_" lid.FStar_Ident.str))))))::[]))
end))))


let encode_free_var : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env fv tt t_norm quals -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if ((let _177_1812 = (FStar_Syntax_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _177_1812)) || (FStar_Syntax_Util.is_lemma t_norm)) then begin
(

let _85_2027 = (new_term_constant_and_tok_from_lid env lid)
in (match (_85_2027) with
| (vname, vtok, env) -> begin
(

let arg_sorts = (match ((let _177_1813 = (FStar_Syntax_Subst.compress t_norm)
in _177_1813.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _85_2030) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun _85_2033 -> FStar_SMTEncoding_Term.Term_sort)))
end
| _85_2036 -> begin
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

let _85_2051 = (

let _85_2046 = (curried_arrow_formals_comp t_norm)
in (match (_85_2046) with
| (args, comp) -> begin
if encode_non_total_function_typ then begin
(let _177_1815 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in ((args), (_177_1815)))
end else begin
((args), (((None), ((FStar_Syntax_Util.comp_result comp)))))
end
end))
in (match (_85_2051) with
| (formals, (pre_opt, res_t)) -> begin
(

let _85_2055 = (new_term_constant_and_tok_from_lid env lid)
in (match (_85_2055) with
| (vname, vtok, env) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
end
| _85_2058 -> begin
(FStar_SMTEncoding_Term.mkApp ((vtok), ([])))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun _85_14 -> (match (_85_14) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(

let _85_2074 = (FStar_Util.prefix vars)
in (match (_85_2074) with
| (_85_2069, (xxsym, _85_2072)) -> begin
(

let xx = (FStar_SMTEncoding_Term.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (let _177_1832 = (let _177_1831 = (let _177_1830 = (let _177_1829 = (let _177_1828 = (let _177_1827 = (let _177_1826 = (let _177_1825 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1825))
in ((vapp), (_177_1826)))
in (FStar_SMTEncoding_Term.mkEq _177_1827))
in ((((vapp)::[])::[]), (vars), (_177_1828)))
in (FStar_SMTEncoding_Term.mkForall _177_1829))
in ((_177_1830), (Some ("Discriminator equation")), (Some ((Prims.strcat "disc_equation_" (escape d.FStar_Ident.str))))))
in FStar_SMTEncoding_Term.Assume (_177_1831))
in (_177_1832)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(

let _85_2086 = (FStar_Util.prefix vars)
in (match (_85_2086) with
| (_85_2081, (xxsym, _85_2084)) -> begin
(

let xx = (FStar_SMTEncoding_Term.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = 0; FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (

let tp_name = (mk_term_projector_name d f)
in (

let prim_app = (FStar_SMTEncoding_Term.mkApp ((tp_name), ((xx)::[])))
in (let _177_1837 = (let _177_1836 = (let _177_1835 = (let _177_1834 = (let _177_1833 = (FStar_SMTEncoding_Term.mkEq ((vapp), (prim_app)))
in ((((vapp)::[])::[]), (vars), (_177_1833)))
in (FStar_SMTEncoding_Term.mkForall _177_1834))
in ((_177_1835), (Some ("Projector equation")), (Some ((Prims.strcat "proj_equation_" tp_name)))))
in FStar_SMTEncoding_Term.Assume (_177_1836))
in (_177_1837)::[])))))
end))
end
| _85_2092 -> begin
[]
end)))))
in (

let _85_2099 = (encode_binders None formals env)
in (match (_85_2099) with
| (vars, guards, env', decls1, _85_2098) -> begin
(

let _85_2108 = (match (pre_opt) with
| None -> begin
(let _177_1838 = (FStar_SMTEncoding_Term.mk_and_l guards)
in ((_177_1838), (decls1)))
end
| Some (p) -> begin
(

let _85_2105 = (encode_formula p env')
in (match (_85_2105) with
| (g, ds) -> begin
(let _177_1839 = (FStar_SMTEncoding_Term.mk_and_l ((g)::guards))
in ((_177_1839), ((FStar_List.append decls1 ds))))
end))
end)
in (match (_85_2108) with
| (guard, decls1) -> begin
(

let vtok_app = (mk_Apply vtok_tm vars)
in (

let vapp = (let _177_1841 = (let _177_1840 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in ((vname), (_177_1840)))
in (FStar_SMTEncoding_Term.mkApp _177_1841))
in (

let _85_2132 = (

let vname_decl = (let _177_1844 = (let _177_1843 = (FStar_All.pipe_right formals (FStar_List.map (fun _85_2111 -> FStar_SMTEncoding_Term.Term_sort)))
in ((vname), (_177_1843), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (_177_1844))
in (

let _85_2119 = (

let env = (

let _85_2114 = env
in {bindings = _85_2114.bindings; depth = _85_2114.depth; tcenv = _85_2114.tcenv; warn = _85_2114.warn; cache = _85_2114.cache; nolabels = _85_2114.nolabels; use_zfuel_name = _85_2114.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in if (not ((head_normal env tt))) then begin
(encode_term_pred None tt env vtok_tm)
end else begin
(encode_term_pred None t_norm env vtok_tm)
end)
in (match (_85_2119) with
| (tok_typing, decls2) -> begin
(

let tok_typing = FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("function token typing")), (Some ((Prims.strcat "function_token_typing_" vname)))))
in (

let _85_2129 = (match (formals) with
| [] -> begin
(let _177_1848 = (let _177_1847 = (let _177_1846 = (FStar_SMTEncoding_Term.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left (fun _177_1845 -> Some (_177_1845)) _177_1846))
in (push_free_var env lid vname _177_1847))
in (((FStar_List.append decls2 ((tok_typing)::[]))), (_177_1848)))
end
| _85_2123 -> begin
(

let vtok_decl = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let vtok_fresh = (let _177_1849 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((vtok), (FStar_SMTEncoding_Term.Term_sort)) _177_1849))
in (

let name_tok_corr = (let _177_1853 = (let _177_1852 = (let _177_1851 = (let _177_1850 = (FStar_SMTEncoding_Term.mkEq ((vtok_app), (vapp)))
in ((((vtok_app)::[])::[]), (vars), (_177_1850)))
in (FStar_SMTEncoding_Term.mkForall _177_1851))
in ((_177_1852), (Some ("Name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" vname)))))
in FStar_SMTEncoding_Term.Assume (_177_1853))
in (((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[]))), (env)))))
end)
in (match (_85_2129) with
| (tok_decl, env) -> begin
(((vname_decl)::tok_decl), (env))
end)))
end)))
in (match (_85_2132) with
| (decls2, env) -> begin
(

let _85_2140 = (

let res_t = (FStar_Syntax_Subst.compress res_t)
in (

let _85_2136 = (encode_term res_t env')
in (match (_85_2136) with
| (encoded_res_t, decls) -> begin
(let _177_1854 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in ((encoded_res_t), (_177_1854), (decls)))
end)))
in (match (_85_2140) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (let _177_1858 = (let _177_1857 = (let _177_1856 = (let _177_1855 = (FStar_SMTEncoding_Term.mkImp ((guard), (ty_pred)))
in ((((vapp)::[])::[]), (vars), (_177_1855)))
in (FStar_SMTEncoding_Term.mkForall _177_1856))
in ((_177_1857), (Some ("free var typing")), (Some ((Prims.strcat "typing_" vname)))))
in FStar_SMTEncoding_Term.Assume (_177_1858))
in (

let freshness = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New)) then begin
(let _177_1864 = (let _177_1861 = (let _177_1860 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (let _177_1859 = (varops.next_id ())
in ((vname), (_177_1860), (FStar_SMTEncoding_Term.Term_sort), (_177_1859))))
in (FStar_SMTEncoding_Term.fresh_constructor _177_1861))
in (let _177_1863 = (let _177_1862 = (pretype_axiom vapp vars)
in (_177_1862)::[])
in (_177_1864)::_177_1863))
end else begin
[]
end
in (

let g = (let _177_1869 = (let _177_1868 = (let _177_1867 = (let _177_1866 = (let _177_1865 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_177_1865)
in (FStar_List.append freshness _177_1866))
in (FStar_List.append decls3 _177_1867))
in (FStar_List.append decls2 _177_1868))
in (FStar_List.append decls1 _177_1869))
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

let _85_2151 = (encode_free_var env x t t_norm [])
in (match (_85_2151) with
| (decls, env) -> begin
(

let _85_2156 = (lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_85_2156) with
| (n, x', _85_2155) -> begin
((((n), (x'))), (decls), (env))
end))
end))
end
| Some (n, x, _85_2160) -> begin
((((n), (x))), ([]), (env))
end))


let encode_top_level_val : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env lid t quals -> (

let tt = (norm env t)
in (

let _85_2170 = (encode_free_var env lid t tt quals)
in (match (_85_2170) with
| (decls, env) -> begin
if (FStar_Syntax_Util.is_smt_lemma t) then begin
(let _177_1887 = (let _177_1886 = (encode_smt_lemma env lid tt)
in (FStar_List.append decls _177_1886))
in ((_177_1887), (env)))
end else begin
((decls), (env))
end
end))))


let encode_top_level_vals : env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _85_2176 lb -> (match (_85_2176) with
| (decls, env) -> begin
(

let _85_2180 = (let _177_1896 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env _177_1896 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (_85_2180) with
| (decls', env) -> begin
(((FStar_List.append decls decls')), (env))
end))
end)) (([]), (env)))))


let encode_top_level_let : env_t  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env _85_2184 quals -> (match (_85_2184) with
| (is_rec, bindings) -> begin
(

let eta_expand = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let _85_2194 = (FStar_Util.first_N nbinders formals)
in (match (_85_2194) with
| (formals, extra_formals) -> begin
(

let subst = (FStar_List.map2 (fun _85_2198 _85_2202 -> (match (((_85_2198), (_85_2202))) with
| ((formal, _85_2197), (binder, _85_2201)) -> begin
(let _177_1914 = (let _177_1913 = (FStar_Syntax_Syntax.bv_to_name binder)
in ((formal), (_177_1913)))
in FStar_Syntax_Syntax.NT (_177_1914))
end)) formals binders)
in (

let extra_formals = (let _177_1918 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun _85_2206 -> (match (_85_2206) with
| (x, i) -> begin
(let _177_1917 = (

let _85_2207 = x
in (let _177_1916 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _85_2207.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _85_2207.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _177_1916}))
in ((_177_1917), (i)))
end))))
in (FStar_All.pipe_right _177_1918 FStar_Syntax_Util.name_binders))
in (

let body = (let _177_1925 = (FStar_Syntax_Subst.compress body)
in (let _177_1924 = (let _177_1919 = (FStar_Syntax_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _177_1919))
in (let _177_1923 = (let _177_1922 = (let _177_1921 = (FStar_Syntax_Subst.subst subst t)
in _177_1921.FStar_Syntax_Syntax.n)
in (FStar_All.pipe_left (fun _177_1920 -> Some (_177_1920)) _177_1922))
in (FStar_Syntax_Syntax.extend_app_n _177_1925 _177_1924 _177_1923 body.FStar_Syntax_Syntax.pos))))
in (((FStar_List.append binders extra_formals)), (body)))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (

let rec aux = (fun norm t_norm -> (match ((let _177_1936 = (FStar_Syntax_Util.unascribe e)
in _177_1936.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, lopt) -> begin
(

let _85_2226 = (FStar_Syntax_Subst.open_term' binders body)
in (match (_85_2226) with
| (binders, body, opening) -> begin
(match ((let _177_1937 = (FStar_Syntax_Subst.compress t_norm)
in _177_1937.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let _85_2233 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_85_2233) with
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

let _85_2240 = (FStar_Util.first_N nformals binders)
in (match (_85_2240) with
| (bs0, rest) -> begin
(

let c = (

let subst = (FStar_List.map2 (fun _85_2244 _85_2248 -> (match (((_85_2244), (_85_2248))) with
| ((b, _85_2243), (x, _85_2247)) -> begin
(let _177_1941 = (let _177_1940 = (FStar_Syntax_Syntax.bv_to_name x)
in ((b), (_177_1940)))
in FStar_Syntax_Syntax.NT (_177_1941))
end)) bs0 formals)
in (FStar_Syntax_Subst.subst_comp subst c))
in (

let body = (FStar_Syntax_Util.abs rest body lopt)
in ((bs0), (body), (bs0), ((FStar_Syntax_Util.comp_result c)))))
end)))
end else begin
if (nformals > nbinders) then begin
(

let _85_2254 = (eta_expand binders formals body tres)
in (match (_85_2254) with
| (binders, body) -> begin
((binders), (body), (formals), (tres))
end))
end else begin
((binders), (body), (formals), (tres))
end
end)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, _85_2257) -> begin
(aux norm x.FStar_Syntax_Syntax.sort)
end
| _85_2261 when (not (norm)) -> begin
(

let t_norm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm)
in (aux true t_norm))
end
| _85_2264 -> begin
(let _177_1944 = (let _177_1943 = (FStar_Syntax_Print.term_to_string e)
in (let _177_1942 = (FStar_Syntax_Print.term_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str _177_1943 _177_1942)))
in (FStar_All.failwith _177_1944))
end)
end))
end
| _85_2266 -> begin
(match ((let _177_1945 = (FStar_Syntax_Subst.compress t_norm)
in _177_1945.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let _85_2273 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_85_2273) with
| (formals, c) -> begin
(

let tres = (FStar_Syntax_Util.comp_result c)
in (

let _85_2277 = (eta_expand [] formals e tres)
in (match (_85_2277) with
| (binders, body) -> begin
((binders), (body), (formals), (tres))
end)))
end))
end
| _85_2279 -> begin
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

let _85_2307 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _85_2294 lb -> (match (_85_2294) with
| (toks, typs, decls, env) -> begin
(

let _85_2296 = if (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) then begin
(Prims.raise Let_rec_unencodeable)
end else begin
()
end
in (

let t_norm = (whnf env lb.FStar_Syntax_Syntax.lbtyp)
in (

let _85_2302 = (let _177_1950 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env _177_1950 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (_85_2302) with
| (tok, decl, env) -> begin
(let _177_1953 = (let _177_1952 = (let _177_1951 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in ((_177_1951), (tok)))
in (_177_1952)::toks)
in ((_177_1953), ((t_norm)::typs), ((decl)::decls), (env)))
end))))
end)) (([]), ([]), ([]), (env))))
in (match (_85_2307) with
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
| _85_2314 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> (let _177_1956 = (FStar_Syntax_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _177_1956)))))) then begin
((decls), (env))
end else begin
if (not (is_rec)) then begin
(match (((bindings), (typs), (toks))) with
| (({FStar_Syntax_Syntax.lbname = _85_2324; FStar_Syntax_Syntax.lbunivs = _85_2322; FStar_Syntax_Syntax.lbtyp = _85_2320; FStar_Syntax_Syntax.lbeff = _85_2318; FStar_Syntax_Syntax.lbdef = e})::[], (t_norm)::[], ((flid_fv, (f, ftok)))::[]) -> begin
(

let e = (FStar_Syntax_Subst.compress e)
in (

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let _85_2344 = (destruct_bound_function flid t_norm e)
in (match (_85_2344) with
| (binders, body, _85_2341, _85_2343) -> begin
(

let _85_2351 = (encode_binders None binders env)
in (match (_85_2351) with
| (vars, guards, env', binder_decls, _85_2350) -> begin
(

let app = (match (vars) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
end
| _85_2354 -> begin
(let _177_1958 = (let _177_1957 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in ((f), (_177_1957)))
in (FStar_SMTEncoding_Term.mkApp _177_1958))
end)
in (

let _85_2360 = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic)) then begin
(let _177_1960 = (FStar_SMTEncoding_Term.mk_Valid app)
in (let _177_1959 = (encode_formula body env')
in ((_177_1960), (_177_1959))))
end else begin
(let _177_1961 = (encode_term body env')
in ((app), (_177_1961)))
end
in (match (_85_2360) with
| (app, (body, decls2)) -> begin
(

let eqn = (let _177_1967 = (let _177_1966 = (let _177_1963 = (let _177_1962 = (FStar_SMTEncoding_Term.mkEq ((app), (body)))
in ((((app)::[])::[]), (vars), (_177_1962)))
in (FStar_SMTEncoding_Term.mkForall _177_1963))
in (let _177_1965 = (let _177_1964 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (_177_1964))
in ((_177_1966), (_177_1965), (Some ((Prims.strcat "equation_" f))))))
in FStar_SMTEncoding_Term.Assume (_177_1967))
in (let _177_1972 = (let _177_1971 = (let _177_1970 = (let _177_1969 = (let _177_1968 = (primitive_type_axioms env.tcenv flid f app)
in (FStar_List.append ((eqn)::[]) _177_1968))
in (FStar_List.append decls2 _177_1969))
in (FStar_List.append binder_decls _177_1970))
in (FStar_List.append decls _177_1971))
in ((_177_1972), (env))))
end)))
end))
end))))
end
| _85_2363 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(

let fuel = (let _177_1973 = (varops.fresh "fuel")
in ((_177_1973), (FStar_SMTEncoding_Term.Fuel_sort)))
in (

let fuel_tm = (FStar_SMTEncoding_Term.mkFreeV fuel)
in (

let env0 = env
in (

let _85_2381 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _85_2369 _85_2374 -> (match (((_85_2369), (_85_2374))) with
| ((gtoks, env), (flid_fv, (f, ftok))) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let g = (varops.new_fvar flid)
in (

let gtok = (varops.new_fvar flid)
in (

let env = (let _177_1978 = (let _177_1977 = (FStar_SMTEncoding_Term.mkApp ((g), ((fuel_tm)::[])))
in (FStar_All.pipe_left (fun _177_1976 -> Some (_177_1976)) _177_1977))
in (push_free_var env flid gtok _177_1978))
in (((((flid), (f), (ftok), (g), (gtok)))::gtoks), (env))))))
end)) (([]), (env))))
in (match (_85_2381) with
| (gtoks, env) -> begin
(

let gtoks = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env0 _85_2390 t_norm _85_2401 -> (match (((_85_2390), (_85_2401))) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = _85_2400; FStar_Syntax_Syntax.lbunivs = _85_2398; FStar_Syntax_Syntax.lbtyp = _85_2396; FStar_Syntax_Syntax.lbeff = _85_2394; FStar_Syntax_Syntax.lbdef = e}) -> begin
(

let _85_2406 = (destruct_bound_function flid t_norm e)
in (match (_85_2406) with
| (binders, body, formals, tres) -> begin
(

let _85_2413 = (encode_binders None binders env)
in (match (_85_2413) with
| (vars, guards, env', binder_decls, _85_2412) -> begin
(

let decl_g = (let _177_1989 = (let _177_1988 = (let _177_1987 = (FStar_List.map Prims.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::_177_1987)
in ((g), (_177_1988), (FStar_SMTEncoding_Term.Term_sort), (Some ("Fuel-instrumented function name"))))
in FStar_SMTEncoding_Term.DeclFun (_177_1989))
in (

let env0 = (push_zfuel_name env0 flid g)
in (

let decl_g_tok = FStar_SMTEncoding_Term.DeclFun (((gtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Token for fuel-instrumented partial applications"))))
in (

let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (

let app = (FStar_SMTEncoding_Term.mkApp ((f), (vars_tm)))
in (

let gsapp = (let _177_1992 = (let _177_1991 = (let _177_1990 = (FStar_SMTEncoding_Term.mkApp (("SFuel"), ((fuel_tm)::[])))
in (_177_1990)::vars_tm)
in ((g), (_177_1991)))
in (FStar_SMTEncoding_Term.mkApp _177_1992))
in (

let gmax = (let _177_1995 = (let _177_1994 = (let _177_1993 = (FStar_SMTEncoding_Term.mkApp (("MaxFuel"), ([])))
in (_177_1993)::vars_tm)
in ((g), (_177_1994)))
in (FStar_SMTEncoding_Term.mkApp _177_1995))
in (

let _85_2423 = (encode_term body env')
in (match (_85_2423) with
| (body_tm, decls2) -> begin
(

let eqn_g = (let _177_2001 = (let _177_2000 = (let _177_1997 = (let _177_1996 = (FStar_SMTEncoding_Term.mkEq ((gsapp), (body_tm)))
in ((((gsapp)::[])::[]), ((fuel)::vars), (_177_1996)))
in (FStar_SMTEncoding_Term.mkForall _177_1997))
in (let _177_1999 = (let _177_1998 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (_177_1998))
in ((_177_2000), (_177_1999), (Some ((Prims.strcat "equation_with_fuel_" g))))))
in FStar_SMTEncoding_Term.Assume (_177_2001))
in (

let eqn_f = (let _177_2005 = (let _177_2004 = (let _177_2003 = (let _177_2002 = (FStar_SMTEncoding_Term.mkEq ((app), (gmax)))
in ((((app)::[])::[]), (vars), (_177_2002)))
in (FStar_SMTEncoding_Term.mkForall _177_2003))
in ((_177_2004), (Some ("Correspondence of recursive function to instrumented version")), (Some ((Prims.strcat "fuel_correspondence_" g)))))
in FStar_SMTEncoding_Term.Assume (_177_2005))
in (

let eqn_g' = (let _177_2014 = (let _177_2013 = (let _177_2012 = (let _177_2011 = (let _177_2010 = (let _177_2009 = (let _177_2008 = (let _177_2007 = (let _177_2006 = (FStar_SMTEncoding_Term.n_fuel 0)
in (_177_2006)::vars_tm)
in ((g), (_177_2007)))
in (FStar_SMTEncoding_Term.mkApp _177_2008))
in ((gsapp), (_177_2009)))
in (FStar_SMTEncoding_Term.mkEq _177_2010))
in ((((gsapp)::[])::[]), ((fuel)::vars), (_177_2011)))
in (FStar_SMTEncoding_Term.mkForall _177_2012))
in ((_177_2013), (Some ("Fuel irrelevance")), (Some ((Prims.strcat "fuel_irrelevance_" g)))))
in FStar_SMTEncoding_Term.Assume (_177_2014))
in (

let _85_2446 = (

let _85_2433 = (encode_binders None formals env0)
in (match (_85_2433) with
| (vars, v_guards, env, binder_decls, _85_2432) -> begin
(

let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (

let gapp = (FStar_SMTEncoding_Term.mkApp ((g), ((fuel_tm)::vars_tm)))
in (

let tok_corr = (

let tok_app = (let _177_2015 = (FStar_SMTEncoding_Term.mkFreeV ((gtok), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply _177_2015 ((fuel)::vars)))
in (let _177_2019 = (let _177_2018 = (let _177_2017 = (let _177_2016 = (FStar_SMTEncoding_Term.mkEq ((tok_app), (gapp)))
in ((((tok_app)::[])::[]), ((fuel)::vars), (_177_2016)))
in (FStar_SMTEncoding_Term.mkForall _177_2017))
in ((_177_2018), (Some ("Fuel token correspondence")), (Some ((Prims.strcat "fuel_tokem_correspondence_" gtok)))))
in FStar_SMTEncoding_Term.Assume (_177_2019)))
in (

let _85_2443 = (

let _85_2440 = (encode_term_pred None tres env gapp)
in (match (_85_2440) with
| (g_typing, d3) -> begin
(let _177_2027 = (let _177_2026 = (let _177_2025 = (let _177_2024 = (let _177_2023 = (let _177_2022 = (let _177_2021 = (let _177_2020 = (FStar_SMTEncoding_Term.mk_and_l v_guards)
in ((_177_2020), (g_typing)))
in (FStar_SMTEncoding_Term.mkImp _177_2021))
in ((((gapp)::[])::[]), ((fuel)::vars), (_177_2022)))
in (FStar_SMTEncoding_Term.mkForall _177_2023))
in ((_177_2024), (Some ("Typing correspondence of token to term")), (Some ((Prims.strcat "token_correspondence_" g)))))
in FStar_SMTEncoding_Term.Assume (_177_2025))
in (_177_2026)::[])
in ((d3), (_177_2027)))
end))
in (match (_85_2443) with
| (aux_decls, typing_corr) -> begin
(((FStar_List.append binder_decls aux_decls)), ((FStar_List.append typing_corr ((tok_corr)::[]))))
end)))))
end))
in (match (_85_2446) with
| (aux_decls, g_typing) -> begin
(((FStar_List.append binder_decls (FStar_List.append decls2 (FStar_List.append aux_decls ((decl_g)::(decl_g_tok)::[]))))), ((FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing)), (env0))
end)))))
end)))))))))
end))
end))
end))
in (

let _85_2462 = (let _177_2030 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _85_2450 _85_2454 -> (match (((_85_2450), (_85_2454))) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(

let _85_2458 = (encode_one_binding env0 gtok ty bs)
in (match (_85_2458) with
| (decls', eqns', env0) -> begin
(((decls')::decls), ((FStar_List.append eqns' eqns)), (env0))
end))
end)) (((decls)::[]), ([]), (env0)) _177_2030))
in (match (_85_2462) with
| (decls, eqns, env0) -> begin
(

let _85_2471 = (let _177_2032 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _177_2032 (FStar_List.partition (fun _85_16 -> (match (_85_16) with
| FStar_SMTEncoding_Term.DeclFun (_85_2465) -> begin
true
end
| _85_2468 -> begin
false
end)))))
in (match (_85_2471) with
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

let msg = (let _177_2035 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _177_2035 (FStar_String.concat " and ")))
in (

let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in (((decl)::[]), (env))))
end))
end))


let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let _85_2475 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _177_2044 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _177_2044))
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

let _85_2483 = (encode_sigelt' env se)
in (match (_85_2483) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _177_2047 = (let _177_2046 = (let _177_2045 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (_177_2045))
in (_177_2046)::[])
in ((_177_2047), (e)))
end
| _85_2486 -> begin
(let _177_2054 = (let _177_2053 = (let _177_2049 = (let _177_2048 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_177_2048))
in (_177_2049)::g)
in (let _177_2052 = (let _177_2051 = (let _177_2050 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_177_2050))
in (_177_2051)::[])
in (FStar_List.append _177_2053 _177_2052)))
in ((_177_2054), (e)))
end)
end)))))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let should_skip = (fun l -> false)
in (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_85_2492) -> begin
(FStar_All.failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _85_2508) -> begin
if (let _177_2059 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right _177_2059 Prims.op_Negation)) then begin
(([]), (env))
end else begin
(

let encode_monad_op = (fun tm name env -> (

let repr_name = (fun ed -> (FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid ed.FStar_Syntax_Syntax.mname) (((FStar_Ident.id_of_text (Prims.strcat name "_repr")))::[]))))
in (

let _85_2521 = (let _177_2068 = (repr_name ed)
in (new_term_constant_and_tok_from_lid env _177_2068))
in (match (_85_2521) with
| (br_name, _85_2519, env) -> begin
(

let _85_2524 = (encode_term (Prims.snd tm) env)
in (match (_85_2524) with
| (tm, decls) -> begin
(

let xs = if (name = "bind") then begin
((("@x0"), (FStar_SMTEncoding_Term.Term_sort)))::((("@x1"), (FStar_SMTEncoding_Term.Term_sort)))::((("@x2"), (FStar_SMTEncoding_Term.Term_sort)))::((("@x3"), (FStar_SMTEncoding_Term.Term_sort)))::((("@x4"), (FStar_SMTEncoding_Term.Term_sort)))::((("@x5"), (FStar_SMTEncoding_Term.Term_sort)))::[]
end else begin
((("@x0"), (FStar_SMTEncoding_Term.Term_sort)))::((("@x1"), (FStar_SMTEncoding_Term.Term_sort)))::((("@x2"), (FStar_SMTEncoding_Term.Term_sort)))::[]
end
in (

let m_decl = (let _177_2070 = (let _177_2069 = (FStar_All.pipe_right xs (FStar_List.map Prims.snd))
in ((br_name), (_177_2069), (FStar_SMTEncoding_Term.Term_sort), (Some (name))))
in FStar_SMTEncoding_Term.DeclFun (_177_2070))
in (

let eqn = (

let app = (let _177_2073 = (let _177_2072 = (let _177_2071 = (FStar_All.pipe_right xs (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in ((FStar_SMTEncoding_Term.Var (br_name)), (_177_2071)))
in FStar_SMTEncoding_Term.App (_177_2072))
in (FStar_SMTEncoding_Term.mk _177_2073))
in (let _177_2079 = (let _177_2078 = (let _177_2077 = (let _177_2076 = (let _177_2075 = (let _177_2074 = (mk_Apply tm xs)
in ((app), (_177_2074)))
in (FStar_SMTEncoding_Term.mkEq _177_2075))
in ((((app)::[])::[]), (xs), (_177_2076)))
in (FStar_SMTEncoding_Term.mkForall _177_2077))
in ((_177_2078), (Some ((Prims.strcat name " equality"))), (Some ((Prims.strcat br_name "_equality")))))
in FStar_SMTEncoding_Term.Assume (_177_2079)))
in ((env), ((m_decl)::(eqn)::[])))))
end))
end))))
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

let _85_2542 = (encode_term a.FStar_Syntax_Syntax.action_defn env)
in (match (_85_2542) with
| (tm, decls) -> begin
(

let a_decls = (let _177_2087 = (let _177_2086 = (let _177_2085 = (FStar_All.pipe_right formals (FStar_List.map (fun _85_2543 -> FStar_SMTEncoding_Term.Term_sort)))
in ((aname), (_177_2085), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action"))))
in FStar_SMTEncoding_Term.DeclFun (_177_2086))
in (_177_2087)::(FStar_SMTEncoding_Term.DeclFun (((atok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action token")))))::[])
in (

let _85_2557 = (let _177_2089 = (FStar_All.pipe_right formals (FStar_List.map (fun _85_2549 -> (match (_85_2549) with
| (bv, _85_2548) -> begin
(

let _85_2554 = (gen_term_var env bv)
in (match (_85_2554) with
| (xxsym, xx, _85_2553) -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (xx))
end))
end))))
in (FStar_All.pipe_right _177_2089 FStar_List.split))
in (match (_85_2557) with
| (xs_sorts, xs) -> begin
(

let app = (let _177_2093 = (let _177_2092 = (let _177_2091 = (let _177_2090 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Var (aname)), (xs)))))
in (_177_2090)::[])
in ((FStar_SMTEncoding_Term.Var ("Reify")), (_177_2091)))
in FStar_SMTEncoding_Term.App (_177_2092))
in (FStar_All.pipe_right _177_2093 FStar_SMTEncoding_Term.mk))
in (

let a_eq = (let _177_2099 = (let _177_2098 = (let _177_2097 = (let _177_2096 = (let _177_2095 = (let _177_2094 = (mk_Apply tm xs_sorts)
in ((app), (_177_2094)))
in (FStar_SMTEncoding_Term.mkEq _177_2095))
in ((((app)::[])::[]), (xs_sorts), (_177_2096)))
in (FStar_SMTEncoding_Term.mkForall _177_2097))
in ((_177_2098), (Some ("Action equality")), (Some ((Prims.strcat aname "_equality")))))
in FStar_SMTEncoding_Term.Assume (_177_2099))
in (

let tok_correspondence = (

let tok_term = (FStar_SMTEncoding_Term.mkFreeV ((atok), (FStar_SMTEncoding_Term.Term_sort)))
in (

let tok_app = (mk_Apply tok_term xs_sorts)
in (let _177_2103 = (let _177_2102 = (let _177_2101 = (let _177_2100 = (FStar_SMTEncoding_Term.mkEq ((tok_app), (app)))
in ((((tok_app)::[])::[]), (xs_sorts), (_177_2100)))
in (FStar_SMTEncoding_Term.mkForall _177_2101))
in ((_177_2102), (Some ("Action token correspondence")), (Some ((Prims.strcat aname "_token_correspondence")))))
in FStar_SMTEncoding_Term.Assume (_177_2103))))
in ((env), ((FStar_List.append decls (FStar_List.append a_decls ((a_eq)::(tok_correspondence)::[]))))))))
end)))
end))
end))
end)))
in (

let _85_2565 = (encode_monad_op ed.FStar_Syntax_Syntax.bind_repr "bind" env)
in (match (_85_2565) with
| (env, decls0) -> begin
(

let _85_2568 = (encode_monad_op ed.FStar_Syntax_Syntax.return_repr "return" env)
in (match (_85_2568) with
| (env, decls1) -> begin
(

let _85_2571 = (FStar_Util.fold_map encode_action env ed.FStar_Syntax_Syntax.actions)
in (match (_85_2571) with
| (env, decls2) -> begin
(((FStar_List.append decls0 (FStar_List.append decls1 (FStar_List.flatten decls2)))), (env))
end))
end))
end))))
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _85_2574, _85_2576, _85_2578, _85_2580) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid) -> begin
(

let _85_2586 = (new_term_constant_and_tok_from_lid env lid)
in (match (_85_2586) with
| (tname, ttok, env) -> begin
(([]), (env))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _85_2589, t, quals, _85_2593) -> begin
(

let will_encode_definition = (not ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _85_17 -> (match (_85_17) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Irreducible) -> begin
true
end
| _85_2606 -> begin
false
end))))))
in if will_encode_definition then begin
(([]), (env))
end else begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (

let _85_2611 = (encode_top_level_val env fv t quals)
in (match (_85_2611) with
| (decls, env) -> begin
(

let tname = lid.FStar_Ident.str
in (

let tsym = (FStar_SMTEncoding_Term.mkFreeV ((tname), (FStar_SMTEncoding_Term.Term_sort)))
in (let _177_2106 = (let _177_2105 = (primitive_type_axioms env.tcenv lid tname tsym)
in (FStar_List.append decls _177_2105))
in ((_177_2106), (env)))))
end)))
end)
end
| FStar_Syntax_Syntax.Sig_assume (l, f, _85_2617, _85_2619) -> begin
(

let _85_2624 = (encode_formula f env)
in (match (_85_2624) with
| (f, decls) -> begin
(

let g = (let _177_2113 = (let _177_2112 = (let _177_2111 = (let _177_2108 = (let _177_2107 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" _177_2107))
in Some (_177_2108))
in (let _177_2110 = (let _177_2109 = (varops.fresh (Prims.strcat "assumption_" l.FStar_Ident.str))
in Some (_177_2109))
in ((f), (_177_2111), (_177_2110))))
in FStar_SMTEncoding_Term.Assume (_177_2112))
in (_177_2113)::[])
in (((FStar_List.append decls g)), (env)))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _85_2629, quals) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) -> begin
(

let _85_2642 = (FStar_Util.fold_map (fun env lb -> (

let lid = (let _177_2117 = (let _177_2116 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _177_2116.FStar_Syntax_Syntax.fv_name)
in _177_2117.FStar_Syntax_Syntax.v)
in if (let _177_2118 = (FStar_TypeChecker_Env.try_lookup_val_decl env.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone _177_2118)) then begin
(

let val_decl = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), (r)))
in (

let _85_2639 = (encode_sigelt' env val_decl)
in (match (_85_2639) with
| (decls, env) -> begin
((env), (decls))
end)))
end else begin
((env), ([]))
end)) env (Prims.snd lbs))
in (match (_85_2642) with
| (env, decls) -> begin
(((FStar_List.flatten decls)), (env))
end))
end
| FStar_Syntax_Syntax.Sig_let ((_85_2644, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t); FStar_Syntax_Syntax.lbunivs = _85_2652; FStar_Syntax_Syntax.lbtyp = _85_2650; FStar_Syntax_Syntax.lbeff = _85_2648; FStar_Syntax_Syntax.lbdef = _85_2646})::[]), _85_2659, _85_2661, _85_2663) when (FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Syntax_Const.b2t_lid) -> begin
(

let _85_2669 = (new_term_constant_and_tok_from_lid env b2t.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_85_2669) with
| (tname, ttok, env) -> begin
(

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (

let valid_b2t_x = (let _177_2121 = (let _177_2120 = (let _177_2119 = (FStar_SMTEncoding_Term.mkApp (("Prims.b2t"), ((x)::[])))
in (_177_2119)::[])
in (("Valid"), (_177_2120)))
in (FStar_SMTEncoding_Term.mkApp _177_2121))
in (

let decls = (let _177_2129 = (let _177_2128 = (let _177_2127 = (let _177_2126 = (let _177_2125 = (let _177_2124 = (let _177_2123 = (let _177_2122 = (FStar_SMTEncoding_Term.mkApp (("BoxBool_proj_0"), ((x)::[])))
in ((valid_b2t_x), (_177_2122)))
in (FStar_SMTEncoding_Term.mkEq _177_2123))
in ((((valid_b2t_x)::[])::[]), ((xx)::[]), (_177_2124)))
in (FStar_SMTEncoding_Term.mkForall _177_2125))
in ((_177_2126), (Some ("b2t def")), (Some ("b2t_def"))))
in FStar_SMTEncoding_Term.Assume (_177_2127))
in (_177_2128)::[])
in (FStar_SMTEncoding_Term.DeclFun (((tname), ((FStar_SMTEncoding_Term.Term_sort)::[]), (FStar_SMTEncoding_Term.Term_sort), (None))))::_177_2129)
in ((decls), (env))))))
end))
end
| FStar_Syntax_Syntax.Sig_let (_85_2675, _85_2677, _85_2679, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _85_18 -> (match (_85_18) with
| FStar_Syntax_Syntax.Discriminator (_85_2685) -> begin
true
end
| _85_2688 -> begin
false
end)))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let (_85_2690, _85_2692, lids, quals) when ((FStar_All.pipe_right lids (FStar_Util.for_some (fun l -> ((let _177_2132 = (FStar_List.hd l.FStar_Ident.ns)
in _177_2132.FStar_Ident.idText) = "Prims")))) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun _85_19 -> (match (_85_19) with
| FStar_Syntax_Syntax.Inline -> begin
true
end
| _85_2701 -> begin
false
end))))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _85_2707, _85_2709, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _85_20 -> (match (_85_20) with
| FStar_Syntax_Syntax.Projector (_85_2715) -> begin
true
end
| _85_2718 -> begin
false
end)))) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((try_lookup_free_var env l)) with
| Some (_85_2722) -> begin
(([]), (env))
end
| None -> begin
(

let se = FStar_Syntax_Syntax.Sig_declare_typ (((l), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), ((FStar_Ident.range_of_lid l))))
in (encode_sigelt env se))
end)))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _85_2731, _85_2733, quals) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) -> begin
(match ((let _177_2135 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef)
in _177_2135.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, _85_2740) -> begin
(

let body = (FStar_Syntax_Util.mk_reify body)
in (

let tm = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None)))) None lb.FStar_Syntax_Syntax.lbdef.FStar_Syntax_Syntax.pos)
in (

let tm' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env.tcenv tm)
in (

let lb_typ = (

let _85_2748 = (FStar_Syntax_Util.arrow_formals_comp lb.FStar_Syntax_Syntax.lbtyp)
in (match (_85_2748) with
| (formals, comp) -> begin
(

let reified_typ = (FStar_TypeChecker_Util.reify_comp (

let _85_2749 = env.tcenv
in {FStar_TypeChecker_Env.solver = _85_2749.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _85_2749.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _85_2749.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _85_2749.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _85_2749.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _85_2749.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _85_2749.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _85_2749.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _85_2749.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _85_2749.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _85_2749.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _85_2749.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _85_2749.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _85_2749.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _85_2749.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _85_2749.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _85_2749.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _85_2749.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.type_of = _85_2749.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _85_2749.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _85_2749.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _85_2749.FStar_TypeChecker_Env.qname_and_index}) (FStar_Syntax_Util.lcomp_of_comp comp) FStar_Syntax_Syntax.U_unknown)
in (let _177_2136 = (FStar_Syntax_Syntax.mk_Total reified_typ)
in (FStar_Syntax_Util.arrow formals _177_2136)))
end))
in (

let lb = (

let _85_2753 = lb
in {FStar_Syntax_Syntax.lbname = _85_2753.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _85_2753.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lb_typ; FStar_Syntax_Syntax.lbeff = _85_2753.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = tm'})
in (encode_top_level_let env ((false), ((lb)::[])) quals))))))
end
| _85_2757 -> begin
(([]), (env))
end)
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), _85_2762, _85_2764, quals) -> begin
(encode_top_level_let env ((is_rec), (bindings)) quals)
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _85_2770, _85_2772, _85_2774) -> begin
(

let _85_2779 = (encode_signature env ses)
in (match (_85_2779) with
| (g, env) -> begin
(

let _85_2793 = (FStar_All.pipe_right g (FStar_List.partition (fun _85_21 -> (match (_85_21) with
| FStar_SMTEncoding_Term.Assume (_85_2782, Some ("inversion axiom"), _85_2786) -> begin
false
end
| _85_2790 -> begin
true
end))))
in (match (_85_2793) with
| (g', inversions) -> begin
(

let _85_2802 = (FStar_All.pipe_right g' (FStar_List.partition (fun _85_22 -> (match (_85_22) with
| FStar_SMTEncoding_Term.DeclFun (_85_2796) -> begin
true
end
| _85_2799 -> begin
false
end))))
in (match (_85_2802) with
| (decls, rest) -> begin
(((FStar_List.append decls (FStar_List.append rest inversions))), (env))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, _85_2805, tps, k, _85_2809, datas, quals, _85_2813) -> begin
(

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _85_23 -> (match (_85_23) with
| (FStar_Syntax_Syntax.Logic) | (FStar_Syntax_Syntax.Assumption) -> begin
true
end
| _85_2820 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(

let _85_2832 = c
in (match (_85_2832) with
| (name, args, _85_2827, _85_2829, _85_2831) -> begin
(let _177_2144 = (let _177_2143 = (let _177_2142 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in ((name), (_177_2142), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (_177_2143))
in (_177_2144)::[])
end))
end else begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end)
in (

let inversion_axioms = (fun tapp vars -> if (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _177_2150 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right _177_2150 FStar_Option.isNone))))) then begin
[]
end else begin
(

let _85_2839 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_85_2839) with
| (xxsym, xx) -> begin
(

let _85_2875 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _85_2842 l -> (match (_85_2842) with
| (out, decls) -> begin
(

let _85_2847 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (_85_2847) with
| (_85_2845, data_t) -> begin
(

let _85_2850 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (_85_2850) with
| (args, res) -> begin
(

let indices = (match ((let _177_2153 = (FStar_Syntax_Subst.compress res)
in _177_2153.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_85_2852, indices) -> begin
indices
end
| _85_2857 -> begin
[]
end)
in (

let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env _85_2863 -> (match (_85_2863) with
| (x, _85_2862) -> begin
(let _177_2158 = (let _177_2157 = (let _177_2156 = (mk_term_projector_name l x)
in ((_177_2156), ((xx)::[])))
in (FStar_SMTEncoding_Term.mkApp _177_2157))
in (push_term_var env x _177_2158))
end)) env))
in (

let _85_2867 = (encode_args indices env)
in (match (_85_2867) with
| (indices, decls') -> begin
(

let _85_2868 = if ((FStar_List.length indices) <> (FStar_List.length vars)) then begin
(FStar_All.failwith "Impossible")
end else begin
()
end
in (

let eqs = (let _177_2163 = (FStar_List.map2 (fun v a -> (let _177_2162 = (let _177_2161 = (FStar_SMTEncoding_Term.mkFreeV v)
in ((_177_2161), (a)))
in (FStar_SMTEncoding_Term.mkEq _177_2162))) vars indices)
in (FStar_All.pipe_right _177_2163 FStar_SMTEncoding_Term.mk_and_l))
in (let _177_2168 = (let _177_2167 = (let _177_2166 = (let _177_2165 = (let _177_2164 = (mk_data_tester env l xx)
in ((_177_2164), (eqs)))
in (FStar_SMTEncoding_Term.mkAnd _177_2165))
in ((out), (_177_2166)))
in (FStar_SMTEncoding_Term.mkOr _177_2167))
in ((_177_2168), ((FStar_List.append decls decls'))))))
end))))
end))
end))
end)) ((FStar_SMTEncoding_Term.mkFalse), ([]))))
in (match (_85_2875) with
| (data_ax, decls) -> begin
(

let _85_2878 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_85_2878) with
| (ffsym, ff) -> begin
(

let fuel_guarded_inversion = (

let xx_has_type_sfuel = if ((FStar_List.length datas) > 1) then begin
(let _177_2169 = (FStar_SMTEncoding_Term.mkApp (("SFuel"), ((ff)::[])))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel _177_2169 xx tapp))
end else begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end
in (let _177_2176 = (let _177_2175 = (let _177_2172 = (let _177_2171 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (let _177_2170 = (FStar_SMTEncoding_Term.mkImp ((xx_has_type_sfuel), (data_ax)))
in ((((xx_has_type_sfuel)::[])::[]), (_177_2171), (_177_2170))))
in (FStar_SMTEncoding_Term.mkForall _177_2172))
in (let _177_2174 = (let _177_2173 = (varops.fresh (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str))
in Some (_177_2173))
in ((_177_2175), (Some ("inversion axiom")), (_177_2174))))
in FStar_SMTEncoding_Term.Assume (_177_2176)))
in (

let pattern_guarded_inversion = if ((contains_name env "Prims.inversion") && ((FStar_List.length datas) > 1)) then begin
(

let xx_has_type_fuel = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let pattern_guard = (FStar_SMTEncoding_Term.mkApp (("Prims.inversion"), ((tapp)::[])))
in (let _177_2184 = (let _177_2183 = (let _177_2182 = (let _177_2179 = (let _177_2178 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (let _177_2177 = (FStar_SMTEncoding_Term.mkImp ((xx_has_type_fuel), (data_ax)))
in ((((xx_has_type_fuel)::(pattern_guard)::[])::[]), (_177_2178), (_177_2177))))
in (FStar_SMTEncoding_Term.mkForall _177_2179))
in (let _177_2181 = (let _177_2180 = (varops.fresh (Prims.strcat "pattern_guarded_inversion_" t.FStar_Ident.str))
in Some (_177_2180))
in ((_177_2182), (Some ("inversion axiom")), (_177_2181))))
in FStar_SMTEncoding_Term.Assume (_177_2183))
in (_177_2184)::[])))
end else begin
[]
end
in (FStar_List.append decls (FStar_List.append ((fuel_guarded_inversion)::[]) pattern_guarded_inversion))))
end))
end))
end))
end)
in (

let _85_2892 = (match ((let _177_2185 = (FStar_Syntax_Subst.compress k)
in _177_2185.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
(((FStar_List.append tps formals)), ((FStar_Syntax_Util.comp_result kres)))
end
| _85_2889 -> begin
((tps), (k))
end)
in (match (_85_2892) with
| (formals, res) -> begin
(

let _85_2895 = (FStar_Syntax_Subst.open_term formals res)
in (match (_85_2895) with
| (formals, res) -> begin
(

let _85_2902 = (encode_binders None formals env)
in (match (_85_2902) with
| (vars, guards, env', binder_decls, _85_2901) -> begin
(

let _85_2906 = (new_term_constant_and_tok_from_lid env t)
in (match (_85_2906) with
| (tname, ttok, env) -> begin
(

let ttok_tm = (FStar_SMTEncoding_Term.mkApp ((ttok), ([])))
in (

let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (

let tapp = (let _177_2187 = (let _177_2186 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in ((tname), (_177_2186)))
in (FStar_SMTEncoding_Term.mkApp _177_2187))
in (

let _85_2927 = (

let tname_decl = (let _177_2191 = (let _177_2190 = (FStar_All.pipe_right vars (FStar_List.map (fun _85_2912 -> (match (_85_2912) with
| (n, s) -> begin
(((Prims.strcat tname n)), (s))
end))))
in (let _177_2189 = (varops.next_id ())
in ((tname), (_177_2190), (FStar_SMTEncoding_Term.Term_sort), (_177_2189), (false))))
in (constructor_or_logic_type_decl _177_2191))
in (

let _85_2924 = (match (vars) with
| [] -> begin
(let _177_2195 = (let _177_2194 = (let _177_2193 = (FStar_SMTEncoding_Term.mkApp ((tname), ([])))
in (FStar_All.pipe_left (fun _177_2192 -> Some (_177_2192)) _177_2193))
in (push_free_var env t tname _177_2194))
in (([]), (_177_2195)))
end
| _85_2916 -> begin
(

let ttok_decl = FStar_SMTEncoding_Term.DeclFun (((ttok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("token"))))
in (

let ttok_fresh = (let _177_2196 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ttok), (FStar_SMTEncoding_Term.Term_sort)) _177_2196))
in (

let ttok_app = (mk_Apply ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (let _177_2200 = (let _177_2199 = (let _177_2198 = (let _177_2197 = (FStar_SMTEncoding_Term.mkEq ((ttok_app), (tapp)))
in ((pats), (None), (vars), (_177_2197)))
in (FStar_SMTEncoding_Term.mkForall' _177_2198))
in ((_177_2199), (Some ("name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" ttok)))))
in FStar_SMTEncoding_Term.Assume (_177_2200))
in (((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[]), (env)))))))
end)
in (match (_85_2924) with
| (tok_decls, env) -> begin
(((FStar_List.append tname_decl tok_decls)), (env))
end)))
in (match (_85_2927) with
| (decls, env) -> begin
(

let kindingAx = (

let _85_2930 = (encode_term_pred None res env' tapp)
in (match (_85_2930) with
| (k, decls) -> begin
(

let karr = if ((FStar_List.length formals) > 0) then begin
(let _177_2204 = (let _177_2203 = (let _177_2202 = (let _177_2201 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _177_2201))
in ((_177_2202), (Some ("kinding")), (Some ((Prims.strcat "pre_kinding_" ttok)))))
in FStar_SMTEncoding_Term.Assume (_177_2203))
in (_177_2204)::[])
end else begin
[]
end
in (let _177_2211 = (let _177_2210 = (let _177_2209 = (let _177_2208 = (let _177_2207 = (let _177_2206 = (let _177_2205 = (FStar_SMTEncoding_Term.mkImp ((guard), (k)))
in ((((tapp)::[])::[]), (vars), (_177_2205)))
in (FStar_SMTEncoding_Term.mkForall _177_2206))
in ((_177_2207), (None), (Some ((Prims.strcat "kinding_" ttok)))))
in FStar_SMTEncoding_Term.Assume (_177_2208))
in (_177_2209)::[])
in (FStar_List.append karr _177_2210))
in (FStar_List.append decls _177_2211)))
end))
in (

let aux = (let _177_2215 = (let _177_2214 = (inversion_axioms tapp vars)
in (let _177_2213 = (let _177_2212 = (pretype_axiom tapp vars)
in (_177_2212)::[])
in (FStar_List.append _177_2214 _177_2213)))
in (FStar_List.append kindingAx _177_2215))
in (

let g = (FStar_List.append decls (FStar_List.append binder_decls aux))
in ((g), (env)))))
end)))))
end))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, _85_2937, _85_2939, _85_2941, _85_2943, _85_2945, _85_2947, _85_2949) when (FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_datacon (d, _85_2954, t, _85_2957, n_tps, quals, _85_2961, drange) -> begin
(

let _85_2968 = (new_term_constant_and_tok_from_lid env d)
in (match (_85_2968) with
| (ddconstrsym, ddtok, env) -> begin
(

let ddtok_tm = (FStar_SMTEncoding_Term.mkApp ((ddtok), ([])))
in (

let _85_2972 = (FStar_Syntax_Util.arrow_formals t)
in (match (_85_2972) with
| (formals, t_res) -> begin
(

let _85_2975 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_85_2975) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_SMTEncoding_Term.mkApp (("SFuel"), ((fuel_tm)::[])))
in (

let _85_2982 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_85_2982) with
| (vars, guards, env', binder_decls, names) -> begin
(

let projectors = (FStar_All.pipe_right names (FStar_List.map (fun x -> (let _177_2217 = (mk_term_projector_name d x)
in ((_177_2217), (FStar_SMTEncoding_Term.Term_sort))))))
in (

let datacons = (let _177_2219 = (let _177_2218 = (varops.next_id ())
in ((ddconstrsym), (projectors), (FStar_SMTEncoding_Term.Term_sort), (_177_2218), (true)))
in (FStar_All.pipe_right _177_2219 FStar_SMTEncoding_Term.constructor_to_decl))
in (

let app = (mk_Apply ddtok_tm vars)
in (

let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Term.mkApp ((ddconstrsym), (xvars)))
in (

let _85_2992 = (encode_term_pred None t env ddtok_tm)
in (match (_85_2992) with
| (tok_typing, decls3) -> begin
(

let _85_2999 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_85_2999) with
| (vars', guards', env'', decls_formals, _85_2998) -> begin
(

let _85_3004 = (

let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars')
in (

let dapp = (FStar_SMTEncoding_Term.mkApp ((ddconstrsym), (xvars)))
in (encode_term_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_85_3004) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_SMTEncoding_Term.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _85_3008 -> begin
(let _177_2221 = (let _177_2220 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ddtok), (FStar_SMTEncoding_Term.Term_sort)) _177_2220))
in (_177_2221)::[])
end)
in (

let encode_elim = (fun _85_3011 -> (match (()) with
| () -> begin
(

let _85_3014 = (FStar_Syntax_Util.head_and_args t_res)
in (match (_85_3014) with
| (head, args) -> begin
(match ((let _177_2224 = (FStar_Syntax_Subst.compress head)
in _177_2224.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let _85_3032 = (encode_args args env')
in (match (_85_3032) with
| (encoded_args, arg_decls) -> begin
(

let _85_3047 = (FStar_List.fold_left (fun _85_3036 arg -> (match (_85_3036) with
| (env, arg_vars, eqns) -> begin
(

let _85_3042 = (let _177_2227 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in (gen_term_var env _177_2227))
in (match (_85_3042) with
| (_85_3039, xv, env) -> begin
(let _177_2229 = (let _177_2228 = (FStar_SMTEncoding_Term.mkEq ((arg), (xv)))
in (_177_2228)::eqns)
in ((env), ((xv)::arg_vars), (_177_2229)))
end))
end)) ((env'), ([]), ([])) encoded_args)
in (match (_85_3047) with
| (_85_3044, arg_vars, eqns) -> begin
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

let typing_inversion = (let _177_2236 = (let _177_2235 = (let _177_2234 = (let _177_2233 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (let _177_2232 = (let _177_2231 = (let _177_2230 = (FStar_SMTEncoding_Term.mk_and_l (FStar_List.append eqns guards))
in ((ty_pred), (_177_2230)))
in (FStar_SMTEncoding_Term.mkImp _177_2231))
in ((((ty_pred)::[])::[]), (_177_2233), (_177_2232))))
in (FStar_SMTEncoding_Term.mkForall _177_2234))
in ((_177_2235), (Some ("data constructor typing elim")), (Some ((Prims.strcat "data_elim_" ddconstrsym)))))
in FStar_SMTEncoding_Term.Assume (_177_2236))
in (

let subterm_ordering = if (FStar_Ident.lid_equals d FStar_Syntax_Const.lextop_lid) then begin
(

let x = (let _177_2237 = (varops.fresh "x")
in ((_177_2237), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Term.mkFreeV x)
in (let _177_2249 = (let _177_2248 = (let _177_2245 = (let _177_2244 = (let _177_2239 = (let _177_2238 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in (_177_2238)::[])
in (_177_2239)::[])
in (let _177_2243 = (let _177_2242 = (let _177_2241 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (let _177_2240 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in ((_177_2241), (_177_2240))))
in (FStar_SMTEncoding_Term.mkImp _177_2242))
in ((_177_2244), ((x)::[]), (_177_2243))))
in (FStar_SMTEncoding_Term.mkForall _177_2245))
in (let _177_2247 = (let _177_2246 = (varops.fresh "lextop")
in Some (_177_2246))
in ((_177_2248), (Some ("lextop is top")), (_177_2247))))
in FStar_SMTEncoding_Term.Assume (_177_2249))))
end else begin
(

let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
[]
end
| FStar_SMTEncoding_Term.Term_sort -> begin
(let _177_2252 = (let _177_2251 = (FStar_SMTEncoding_Term.mkFreeV v)
in (FStar_SMTEncoding_Term.mk_Precedes _177_2251 dapp))
in (_177_2252)::[])
end
| _85_3061 -> begin
(FStar_All.failwith "unexpected sort")
end))))
in (let _177_2259 = (let _177_2258 = (let _177_2257 = (let _177_2256 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (let _177_2255 = (let _177_2254 = (let _177_2253 = (FStar_SMTEncoding_Term.mk_and_l prec)
in ((ty_pred), (_177_2253)))
in (FStar_SMTEncoding_Term.mkImp _177_2254))
in ((((ty_pred)::[])::[]), (_177_2256), (_177_2255))))
in (FStar_SMTEncoding_Term.mkForall _177_2257))
in ((_177_2258), (Some ("subterm ordering")), (Some ((Prims.strcat "subterm_ordering_" ddconstrsym)))))
in FStar_SMTEncoding_Term.Assume (_177_2259)))
end
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end))
end)))
end
| _85_3065 -> begin
(

let _85_3066 = (let _177_2262 = (let _177_2261 = (FStar_Syntax_Print.lid_to_string d)
in (let _177_2260 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _177_2261 _177_2260)))
in (FStar_TypeChecker_Errors.warn drange _177_2262))
in (([]), ([])))
end)
end))
end))
in (

let _85_3070 = (encode_elim ())
in (match (_85_3070) with
| (decls2, elim) -> begin
(

let g = (let _177_2289 = (let _177_2288 = (let _177_2287 = (let _177_2286 = (let _177_2267 = (let _177_2266 = (let _177_2265 = (let _177_2264 = (let _177_2263 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" _177_2263))
in Some (_177_2264))
in ((ddtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (_177_2265)))
in FStar_SMTEncoding_Term.DeclFun (_177_2266))
in (_177_2267)::[])
in (let _177_2285 = (let _177_2284 = (let _177_2283 = (let _177_2282 = (let _177_2281 = (let _177_2280 = (let _177_2279 = (let _177_2271 = (let _177_2270 = (let _177_2269 = (let _177_2268 = (FStar_SMTEncoding_Term.mkEq ((app), (dapp)))
in ((((app)::[])::[]), (vars), (_177_2268)))
in (FStar_SMTEncoding_Term.mkForall _177_2269))
in ((_177_2270), (Some ("equality for proxy")), (Some ((Prims.strcat "equality_tok_" ddtok)))))
in FStar_SMTEncoding_Term.Assume (_177_2271))
in (let _177_2278 = (let _177_2277 = (let _177_2276 = (let _177_2275 = (let _177_2274 = (let _177_2273 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) vars')
in (let _177_2272 = (FStar_SMTEncoding_Term.mkImp ((guard'), (ty_pred')))
in ((((ty_pred')::[])::[]), (_177_2273), (_177_2272))))
in (FStar_SMTEncoding_Term.mkForall _177_2274))
in ((_177_2275), (Some ("data constructor typing intro")), (Some ((Prims.strcat "data_typing_intro_" ddtok)))))
in FStar_SMTEncoding_Term.Assume (_177_2276))
in (_177_2277)::[])
in (_177_2279)::_177_2278))
in (FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("typing for data constructor proxy")), (Some ((Prims.strcat "typing_tok_" ddtok))))))::_177_2280)
in (FStar_List.append _177_2281 elim))
in (FStar_List.append decls_pred _177_2282))
in (FStar_List.append decls_formals _177_2283))
in (FStar_List.append proxy_fresh _177_2284))
in (FStar_List.append _177_2286 _177_2285)))
in (FStar_List.append decls3 _177_2287))
in (FStar_List.append decls2 _177_2288))
in (FStar_List.append binder_decls _177_2289))
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
and encode_signature : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _85_3076 se -> (match (_85_3076) with
| (g, env) -> begin
(

let _85_3080 = (encode_sigelt env se)
in (match (_85_3080) with
| (g', env) -> begin
(((FStar_List.append g g')), (env))
end))
end)) (([]), (env)))))


let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings -> (

let encode_binding = (fun b _85_3087 -> (match (_85_3087) with
| (decls, env) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (_85_3089) -> begin
(([]), (env))
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(

let _85_3096 = (new_term_constant env x)
in (match (_85_3096) with
| (xxsym, xx, env') -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (

let _85_3098 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _177_2304 = (FStar_Syntax_Print.bv_to_string x)
in (let _177_2303 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _177_2302 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" _177_2304 _177_2303 _177_2302))))
end else begin
()
end
in (

let _85_3102 = (encode_term_pred None t1 env xx)
in (match (_85_3102) with
| (t, decls') -> begin
(

let caption = if (FStar_Options.log_queries ()) then begin
(let _177_2308 = (let _177_2307 = (FStar_Syntax_Print.bv_to_string x)
in (let _177_2306 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _177_2305 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _177_2307 _177_2306 _177_2305))))
in Some (_177_2308))
end else begin
None
end
in (

let ax = (

let a_name = Some ((Prims.strcat "binder_" xxsym))
in FStar_SMTEncoding_Term.Assume (((t), (a_name), (a_name))))
in (

let g = (FStar_List.append ((FStar_SMTEncoding_Term.DeclFun (((xxsym), ([]), (FStar_SMTEncoding_Term.Term_sort), (caption))))::[]) (FStar_List.append decls' ((ax)::[])))
in (((FStar_List.append decls g)), (env')))))
end))))
end))
end
| FStar_TypeChecker_Env.Binding_lid (x, (_85_3109, t)) -> begin
(

let t_norm = (whnf env t)
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant None)
in (

let _85_3118 = (encode_free_var env fv t t_norm [])
in (match (_85_3118) with
| (g, env') -> begin
(((FStar_List.append decls g)), (env'))
end))))
end
| (FStar_TypeChecker_Env.Binding_sig_inst (_, se, _)) | (FStar_TypeChecker_Env.Binding_sig (_, se)) -> begin
(

let _85_3132 = (encode_sigelt env se)
in (match (_85_3132) with
| (g, env') -> begin
(((FStar_List.append decls g)), (env'))
end))
end)
end))
in (FStar_List.fold_right encode_binding bindings (([]), (env)))))


let encode_labels = (fun labs -> (

let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _85_3139 -> (match (_85_3139) with
| (l, _85_3136, _85_3138) -> begin
FStar_SMTEncoding_Term.DeclFun ((((Prims.fst l)), ([]), (FStar_SMTEncoding_Term.Bool_sort), (None)))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _85_3146 -> (match (_85_3146) with
| (l, _85_3143, _85_3145) -> begin
(let _177_2316 = (FStar_All.pipe_left (fun _177_2312 -> FStar_SMTEncoding_Term.Echo (_177_2312)) (Prims.fst l))
in (let _177_2315 = (let _177_2314 = (let _177_2313 = (FStar_SMTEncoding_Term.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (_177_2313))
in (_177_2314)::[])
in (_177_2316)::_177_2315))
end))))
in ((prefix), (suffix)))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (let _177_2321 = (let _177_2320 = (let _177_2319 = (FStar_Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _177_2319; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_177_2320)::[])
in (FStar_ST.op_Colon_Equals last_env _177_2321)))


let get_env : FStar_TypeChecker_Env.env  ->  env_t = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "No env; call init first!")
end
| (e)::_85_3152 -> begin
(

let _85_3155 = e
in {bindings = _85_3155.bindings; depth = _85_3155.depth; tcenv = tcenv; warn = _85_3155.warn; cache = _85_3155.cache; nolabels = _85_3155.nolabels; use_zfuel_name = _85_3155.use_zfuel_name; encode_non_total_function_typ = _85_3155.encode_non_total_function_typ})
end))


let set_env : env_t  ->  Prims.unit = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| (_85_3161)::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))


let push_env : Prims.unit  ->  Prims.unit = (fun _85_3163 -> (match (()) with
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

let _85_3169 = hd
in {bindings = _85_3169.bindings; depth = _85_3169.depth; tcenv = _85_3169.tcenv; warn = _85_3169.warn; cache = refs; nolabels = _85_3169.nolabels; use_zfuel_name = _85_3169.use_zfuel_name; encode_non_total_function_typ = _85_3169.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))


let pop_env : Prims.unit  ->  Prims.unit = (fun _85_3172 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Popping an empty stack")
end
| (_85_3176)::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))


let mark_env : Prims.unit  ->  Prims.unit = (fun _85_3178 -> (match (()) with
| () -> begin
(push_env ())
end))


let reset_mark_env : Prims.unit  ->  Prims.unit = (fun _85_3179 -> (match (()) with
| () -> begin
(pop_env ())
end))


let commit_mark_env : Prims.unit  ->  Prims.unit = (fun _85_3180 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| (hd)::(_85_3183)::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _85_3188 -> begin
(FStar_All.failwith "Impossible")
end)
end))


let init : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (

let _85_3190 = (init_env tcenv)
in (

let _85_3192 = (FStar_SMTEncoding_Z3.init ())
in (FStar_SMTEncoding_Z3.giveZ3 ((FStar_SMTEncoding_Term.DefPrelude)::[])))))


let push : Prims.string  ->  Prims.unit = (fun msg -> (

let _85_3195 = (push_env ())
in (

let _85_3197 = (varops.push ())
in (FStar_SMTEncoding_Z3.push msg))))


let pop : Prims.string  ->  Prims.unit = (fun msg -> (

let _85_3200 = (let _177_2342 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _177_2342))
in (

let _85_3202 = (varops.pop ())
in (FStar_SMTEncoding_Z3.pop msg))))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _85_3205 = (mark_env ())
in (

let _85_3207 = (varops.mark ())
in (FStar_SMTEncoding_Z3.mark msg))))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _85_3210 = (reset_mark_env ())
in (

let _85_3212 = (varops.reset_mark ())
in (FStar_SMTEncoding_Z3.reset_mark msg))))


let commit_mark = (fun msg -> (

let _85_3215 = (commit_mark_env ())
in (

let _85_3217 = (varops.commit_mark ())
in (FStar_SMTEncoding_Z3.commit_mark msg))))


let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (

let caption = (fun decls -> if (FStar_Options.log_queries ()) then begin
(let _177_2358 = (let _177_2357 = (let _177_2356 = (let _177_2355 = (let _177_2354 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _177_2354 (FStar_List.map FStar_Syntax_Print.lid_to_string)))
in (FStar_All.pipe_right _177_2355 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " _177_2356))
in FStar_SMTEncoding_Term.Caption (_177_2357))
in (_177_2358)::decls)
end else begin
decls
end)
in (

let env = (get_env tcenv)
in (

let _85_3226 = (encode_sigelt env se)
in (match (_85_3226) with
| (decls, env) -> begin
(

let _85_3227 = (set_env env)
in (let _177_2359 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 _177_2359)))
end)))))


let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let _85_3232 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(let _177_2364 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name _177_2364))
end else begin
()
end
in (

let env = (get_env tcenv)
in (

let _85_3239 = (encode_signature (

let _85_3235 = env
in {bindings = _85_3235.bindings; depth = _85_3235.depth; tcenv = _85_3235.tcenv; warn = false; cache = _85_3235.cache; nolabels = _85_3235.nolabels; use_zfuel_name = _85_3235.use_zfuel_name; encode_non_total_function_typ = _85_3235.encode_non_total_function_typ}) modul.FStar_Syntax_Syntax.exports)
in (match (_85_3239) with
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

let _85_3245 = (set_env (

let _85_3243 = env
in {bindings = _85_3243.bindings; depth = _85_3243.depth; tcenv = _85_3243.tcenv; warn = true; cache = _85_3243.cache; nolabels = _85_3243.nolabels; use_zfuel_name = _85_3243.use_zfuel_name; encode_non_total_function_typ = _85_3243.encode_non_total_function_typ}))
in (

let _85_3247 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end else begin
()
end
in (

let decls = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls)))))
end))))))


let encode_query : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_ErrorReporting.label Prims.list * FStar_SMTEncoding_Term.decl * FStar_SMTEncoding_Term.decl Prims.list) = (fun use_env_msg tcenv q -> (

let _85_3253 = (let _177_2382 = (let _177_2381 = (FStar_TypeChecker_Env.current_module tcenv)
in _177_2381.FStar_Ident.str)
in (FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name _177_2382))
in (

let env = (get_env tcenv)
in (

let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (

let _85_3278 = (

let rec aux = (fun bindings -> (match (bindings) with
| (FStar_TypeChecker_Env.Binding_var (x))::rest -> begin
(

let _85_3267 = (aux rest)
in (match (_85_3267) with
| (out, rest) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (let _177_2388 = (let _177_2387 = (FStar_Syntax_Syntax.mk_binder (

let _85_3269 = x
in {FStar_Syntax_Syntax.ppname = _85_3269.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _85_3269.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_177_2387)::out)
in ((_177_2388), (rest))))
end))
end
| _85_3272 -> begin
(([]), (bindings))
end))
in (

let _85_3275 = (aux bindings)
in (match (_85_3275) with
| (closing, bindings) -> begin
(let _177_2389 = (FStar_Syntax_Util.close_forall (FStar_List.rev closing) q)
in ((_177_2389), (bindings)))
end)))
in (match (_85_3278) with
| (q, bindings) -> begin
(

let _85_3287 = (let _177_2391 = (FStar_List.filter (fun _85_24 -> (match (_85_24) with
| FStar_TypeChecker_Env.Binding_sig (_85_3281) -> begin
false
end
| _85_3284 -> begin
true
end)) bindings)
in (encode_env_bindings env _177_2391))
in (match (_85_3287) with
| (env_decls, env) -> begin
(

let _85_3288 = if (((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTQuery")))) then begin
(let _177_2392 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" _177_2392))
end else begin
()
end
in (

let _85_3292 = (encode_formula q env)
in (match (_85_3292) with
| (phi, qdecls) -> begin
(

let _85_3297 = (let _177_2393 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg _177_2393 phi))
in (match (_85_3297) with
| (phi, labels, _85_3296) -> begin
(

let _85_3300 = (encode_labels labels)
in (match (_85_3300) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append env_decls (FStar_List.append label_prefix qdecls))
in (

let qry = (let _177_2397 = (let _177_2396 = (FStar_SMTEncoding_Term.mkNot phi)
in (let _177_2395 = (let _177_2394 = (varops.fresh "@query")
in Some (_177_2394))
in ((_177_2396), (Some ("query")), (_177_2395))))
in FStar_SMTEncoding_Term.Assume (_177_2397))
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

let _85_3307 = (push "query")
in (

let _85_3312 = (encode_formula q env)
in (match (_85_3312) with
| (f, _85_3311) -> begin
(

let _85_3313 = (pop "query")
in (match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _85_3317) -> begin
true
end
| _85_3321 -> begin
false
end))
end)))))




