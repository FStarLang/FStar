
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


let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let aux = (fun a' -> (lookup_binding env (fun _83_3 -> (match (_83_3) with
| Binding_var (b, t) when (FStar_Syntax_Syntax.bv_eq b a') -> begin
Some ((b, t))
end
| _83_239 -> begin
None
end))))
in (match ((aux a)) with
| None -> begin
(

let a = (unmangle a)
in (match ((aux a)) with
| None -> begin
(let _173_306 = (let _173_305 = (FStar_Syntax_Print.bv_to_string a)
in (FStar_Util.format1 "Bound term variable not found (after unmangling): %s" _173_305))
in (FStar_All.failwith _173_306))
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
in (let _173_317 = (

let _83_255 = env
in (let _173_316 = (let _173_315 = (let _173_314 = (let _173_313 = (let _173_312 = (FStar_SMTEncoding_Term.mkApp (ftok, []))
in (FStar_All.pipe_left (fun _173_311 -> Some (_173_311)) _173_312))
in (x, fname, _173_313, None))
in Binding_fvar (_173_314))
in (_173_315)::env.bindings)
in {bindings = _173_316; depth = _83_255.depth; tcenv = _83_255.tcenv; warn = _83_255.warn; cache = _83_255.cache; nolabels = _83_255.nolabels; use_zfuel_name = _83_255.use_zfuel_name; encode_non_total_function_typ = _83_255.encode_non_total_function_typ}))
in (fname, ftok, _173_317)))))


let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun _83_4 -> (match (_83_4) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some ((t1, t2, t3))
end
| _83_267 -> begin
None
end))))


let contains_name : env_t  ->  Prims.string  ->  Prims.bool = (fun env s -> (let _173_328 = (lookup_binding env (fun _83_5 -> (match (_83_5) with
| Binding_fvar (b, t1, t2, t3) when (b.FStar_Ident.str = s) -> begin
Some (())
end
| _83_278 -> begin
None
end)))
in (FStar_All.pipe_right _173_328 FStar_Option.isSome)))


let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _173_334 = (let _173_333 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" _173_333))
in (FStar_All.failwith _173_334))
end
| Some (s) -> begin
s
end))


let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (

let _83_288 = env
in {bindings = (Binding_fvar ((x, fname, ftok, None)))::env.bindings; depth = _83_288.depth; tcenv = _83_288.tcenv; warn = _83_288.warn; cache = _83_288.cache; nolabels = _83_288.nolabels; use_zfuel_name = _83_288.use_zfuel_name; encode_non_total_function_typ = _83_288.encode_non_total_function_typ}))


let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (

let _83_297 = (lookup_lid env x)
in (match (_83_297) with
| (t1, t2, _83_296) -> begin
(

let t3 = (let _173_351 = (let _173_350 = (let _173_349 = (FStar_SMTEncoding_Term.mkApp ("ZFuel", []))
in (_173_349)::[])
in (f, _173_350))
in (FStar_SMTEncoding_Term.mkApp _173_351))
in (

let _83_299 = env
in {bindings = (Binding_fvar ((x, t1, t2, Some (t3))))::env.bindings; depth = _83_299.depth; tcenv = _83_299.tcenv; warn = _83_299.warn; cache = _83_299.cache; nolabels = _83_299.nolabels; use_zfuel_name = _83_299.use_zfuel_name; encode_non_total_function_typ = _83_299.encode_non_total_function_typ}))
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
| _83_312 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (_83_316, (fuel)::[]) -> begin
if (let _173_357 = (let _173_356 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right _173_356 Prims.fst))
in (FStar_Util.starts_with _173_357 "fuel")) then begin
(let _173_360 = (let _173_359 = (FStar_SMTEncoding_Term.mkFreeV (name, FStar_SMTEncoding_Term.Term_sort))
in (FStar_SMTEncoding_Term.mk_ApplyTF _173_359 fuel))
in (FStar_All.pipe_left (fun _173_358 -> Some (_173_358)) _173_360))
end else begin
Some (t)
end
end
| _83_322 -> begin
Some (t)
end)
end
| _83_324 -> begin
None
end)
end)
end))


let lookup_free_var = (fun env a -> (match ((try_lookup_free_var env a.FStar_Syntax_Syntax.v)) with
| Some (t) -> begin
t
end
| None -> begin
(let _173_364 = (let _173_363 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _173_363))
in (FStar_All.failwith _173_364))
end))


let lookup_free_var_name = (fun env a -> (

let _83_337 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_83_337) with
| (x, _83_334, _83_336) -> begin
x
end)))


let lookup_free_var_sym = (fun env a -> (

let _83_343 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_83_343) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.hash = _83_347; FStar_SMTEncoding_Term.freevars = _83_345}) when env.use_zfuel_name -> begin
(g, zf)
end
| _83_355 -> begin
(match (sym) with
| None -> begin
(FStar_SMTEncoding_Term.Var (name), [])
end
| Some (sym) -> begin
(match (sym.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, (fuel)::[]) -> begin
(g, (fuel)::[])
end
| _83_365 -> begin
(FStar_SMTEncoding_Term.Var (name), [])
end)
end)
end)
end)))


let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun _83_6 -> (match (_83_6) with
| Binding_fvar (_83_370, nm', tok, _83_374) when (nm = nm') -> begin
tok
end
| _83_378 -> begin
None
end))))


let mkForall_fuel' = (fun n _83_383 -> (match (_83_383) with
| (pats, vars, body) -> begin
(

let fallback = (fun _83_385 -> (match (()) with
| () -> begin
(FStar_SMTEncoding_Term.mkForall (pats, vars, body))
end))
in if (FStar_Options.unthrottle_inductives ()) then begin
(fallback ())
end else begin
(

let _83_388 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_83_388) with
| (fsym, fterm) -> begin
(

let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Term.mkApp ("HasTypeFuel", (fterm)::args))
end
| _83_398 -> begin
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
(let _173_381 = (add_fuel guards)
in (FStar_SMTEncoding_Term.mk_and_l _173_381))
end
| _83_411 -> begin
(let _173_382 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _173_382 FStar_List.hd))
end)
in (FStar_SMTEncoding_Term.mkImp (guard, body')))
end
| _83_414 -> begin
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
(let _173_388 = (FStar_TypeChecker_Env.lookup_definition FStar_TypeChecker_Env.OnlyInline env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _173_388 FStar_Option.isNone))
end
| _83_453 -> begin
false
end)))


let head_redex : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (match ((let _173_393 = (FStar_Syntax_Util.un_uinst t)
in _173_393.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_83_457) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(let _173_394 = (FStar_TypeChecker_Env.lookup_definition FStar_TypeChecker_Env.OnlyInline env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _173_394 FStar_Option.isSome))
end
| _83_462 -> begin
false
end))


let whnf : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> if (head_normal env t) then begin
t
end else begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
end)


let norm : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t))


let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (let _173_407 = (let _173_405 = (FStar_Syntax_Syntax.null_binder t)
in (_173_405)::[])
in (let _173_406 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Util.abs _173_407 _173_406 None))))


let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(let _173_414 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out _173_414))
end
| s -> begin
(

let _83_474 = ()
in (let _173_415 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTT out _173_415)))
end)) e)))


let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Term.mk_ApplyTT e)))


let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun _83_7 -> (match (_83_7) with
| (FStar_SMTEncoding_Term.Var ("ApplyTT")) | (FStar_SMTEncoding_Term.Var ("ApplyTF")) -> begin
true
end
| _83_484 -> begin
false
end))


let is_eta : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env vars t -> (

let rec aux = (fun t xs -> (match ((t.FStar_SMTEncoding_Term.tm, xs)) with
| (FStar_SMTEncoding_Term.App (app, (f)::({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.hash = _83_495; FStar_SMTEncoding_Term.freevars = _83_493})::[]), (x)::xs) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), _83_513) -> begin
if (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v)
end
| _83_520 -> begin
false
end)) args vars)) then begin
(tok_of_name env f)
end else begin
None
end
end
| (_83_522, []) -> begin
(

let fvs = (FStar_SMTEncoding_Term.free_variables t)
in if (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (not ((FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)))))) then begin
Some (t)
end else begin
None
end)
end
| _83_528 -> begin
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
(let _173_472 = (let _173_471 = (let _173_470 = (let _173_469 = (FStar_SMTEncoding_Term.mkInteger' (FStar_Util.int_of_char c))
in (FStar_SMTEncoding_Term.boxInt _173_469))
in (_173_470)::[])
in ("FStar.Char.Char", _173_471))
in (FStar_SMTEncoding_Term.mkApp _173_472))
end
| FStar_Const.Const_int (i, None) -> begin
(let _173_473 = (FStar_SMTEncoding_Term.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt _173_473))
end
| FStar_Const.Const_int (i, Some (_83_548)) -> begin
(FStar_All.failwith "Machine integers should be desugared")
end
| FStar_Const.Const_string (bytes, _83_554) -> begin
(let _173_474 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _173_474))
end
| FStar_Const.Const_range (r) -> begin
FStar_SMTEncoding_Term.mk_Range_const
end
| FStar_Const.Const_effect -> begin
FStar_SMTEncoding_Term.mk_Term_type
end
| c -> begin
(let _173_476 = (let _173_475 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" _173_475))
in (FStar_All.failwith _173_476))
end))


let as_function_typ : env_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (

let rec aux = (fun norm t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_83_568) -> begin
t
end
| FStar_Syntax_Syntax.Tm_refine (_83_571) -> begin
(let _173_485 = (FStar_Syntax_Util.unrefine t)
in (aux true _173_485))
end
| _83_574 -> begin
if norm then begin
(let _173_486 = (whnf env t)
in (aux false _173_486))
end else begin
(let _173_489 = (let _173_488 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (let _173_487 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _173_488 _173_487)))
in (FStar_All.failwith _173_489))
end
end)))
in (aux true t0)))


let curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun k -> (

let k = (FStar_Syntax_Subst.compress k)
in (match (k.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| _83_582 -> begin
(let _173_492 = (FStar_Syntax_Syntax.mk_Total k)
in ([], _173_492))
end)))


let rec encode_binders : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> (

let _83_586 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _173_540 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" _173_540))
end else begin
()
end
in (

let _83_614 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _83_593 b -> (match (_83_593) with
| (vars, guards, env, decls, names) -> begin
(

let _83_608 = (

let x = (unmangle (Prims.fst b))
in (

let _83_599 = (gen_term_var env x)
in (match (_83_599) with
| (xxsym, xx, env') -> begin
(

let _83_602 = (let _173_543 = (norm env x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt _173_543 env xx))
in (match (_83_602) with
| (guard_x_t, decls') -> begin
((xxsym, FStar_SMTEncoding_Term.Term_sort), guard_x_t, env', decls', x)
end))
end)))
in (match (_83_608) with
| (v, g, env, decls', n) -> begin
((v)::vars, (g)::guards, env, (FStar_List.append decls decls'), (n)::names)
end))
end)) ([], [], env, [], [])))
in (match (_83_614) with
| (vars, guards, env, decls, names) -> begin
((FStar_List.rev vars), (FStar_List.rev guards), env, decls, (FStar_List.rev names))
end))))
and encode_term_pred : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let _83_621 = (encode_term t env)
in (match (_83_621) with
| (t, decls) -> begin
(let _173_548 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t)
in (_173_548, decls))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let _83_628 = (encode_term t env)
in (match (_83_628) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _173_553 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t)
in (_173_553, decls))
end
| Some (f) -> begin
(let _173_554 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t)
in (_173_554, decls))
end)
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let t0 = (FStar_Syntax_Subst.compress t)
in (

let _83_635 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _173_559 = (FStar_Syntax_Print.tag_of_term t)
in (let _173_558 = (FStar_Syntax_Print.tag_of_term t0)
in (let _173_557 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" _173_559 _173_558 _173_557))))
end else begin
()
end
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _173_564 = (let _173_563 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (let _173_562 = (FStar_Syntax_Print.tag_of_term t0)
in (let _173_561 = (FStar_Syntax_Print.term_to_string t0)
in (let _173_560 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _173_563 _173_562 _173_561 _173_560)))))
in (FStar_All.failwith _173_564))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _173_566 = (let _173_565 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" _173_565))
in (FStar_All.failwith _173_566))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, k, _83_646) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_meta (t, _83_651) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t = (lookup_term_var env x)
in (t, []))
end
| FStar_Syntax_Syntax.Tm_fvar (v) -> begin
(let _173_567 = (lookup_free_var env v.FStar_Syntax_Syntax.fv_name)
in (_173_567, []))
end
| FStar_Syntax_Syntax.Tm_type (_83_660) -> begin
(FStar_SMTEncoding_Term.mk_Term_type, [])
end
| FStar_Syntax_Syntax.Tm_uinst (t, _83_664) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(let _173_568 = (encode_const c)
in (_173_568, []))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _83_675 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_83_675) with
| (binders, res) -> begin
if ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res)) then begin
(

let _83_682 = (encode_binders None binders env)
in (match (_83_682) with
| (vars, guards, env', decls, _83_681) -> begin
(

let fsym = (let _173_569 = (varops.fresh "f")
in (_173_569, FStar_SMTEncoding_Term.Term_sort))
in (

let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (

let app = (mk_Apply f vars)
in (

let _83_688 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv res)
in (match (_83_688) with
| (pre_opt, res_t) -> begin
(

let _83_691 = (encode_term_pred None res_t env' app)
in (match (_83_691) with
| (res_pred, decls') -> begin
(

let _83_700 = (match (pre_opt) with
| None -> begin
(let _173_570 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_173_570, []))
end
| Some (pre) -> begin
(

let _83_697 = (encode_formula pre env')
in (match (_83_697) with
| (guard, decls0) -> begin
(let _173_571 = (FStar_SMTEncoding_Term.mk_and_l ((guard)::guards))
in (_173_571, decls0))
end))
end)
in (match (_83_700) with
| (guards, guard_decls) -> begin
(

let t_interp = (let _173_573 = (let _173_572 = (FStar_SMTEncoding_Term.mkImp (guards, res_pred))
in (((app)::[])::[], vars, _173_572))
in (FStar_SMTEncoding_Term.mkForall _173_573))
in (

let cvars = (let _173_575 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right _173_575 (FStar_List.filter (fun _83_705 -> (match (_83_705) with
| (x, _83_704) -> begin
(x <> (Prims.fst fsym))
end)))))
in (

let tkey = (FStar_SMTEncoding_Term.mkForall ([], (fsym)::cvars, t_interp))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t', sorts, _83_711) -> begin
(let _173_578 = (let _173_577 = (let _173_576 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in (t', _173_576))
in (FStar_SMTEncoding_Term.mkApp _173_577))
in (_173_578, []))
end
| None -> begin
(

let tsym = (varops.fresh "Tm_arrow")
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let caption = if (FStar_Options.log_queries ()) then begin
(let _173_579 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in Some (_173_579))
end else begin
None
end
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun ((tsym, cvar_sorts, FStar_SMTEncoding_Term.Term_sort, caption))
in (

let t = (let _173_581 = (let _173_580 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (tsym, _173_580))
in (FStar_SMTEncoding_Term.mkApp _173_581))
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let k_assumption = (

let a_name = Some ((Prims.strcat "kinding_" tsym))
in (let _173_583 = (let _173_582 = (FStar_SMTEncoding_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (_173_582, a_name, a_name))
in FStar_SMTEncoding_Term.Assume (_173_583)))
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t)
in (

let pre_typing = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in (let _173_590 = (let _173_589 = (let _173_588 = (let _173_587 = (let _173_586 = (let _173_585 = (let _173_584 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _173_584))
in (f_has_t, _173_585))
in (FStar_SMTEncoding_Term.mkImp _173_586))
in (((f_has_t)::[])::[], (fsym)::cvars, _173_587))
in (mkForall_fuel _173_588))
in (_173_589, Some ("pre-typing for functions"), a_name))
in FStar_SMTEncoding_Term.Assume (_173_590)))
in (

let t_interp = (

let a_name = Some ((Prims.strcat "interpretation_" tsym))
in (let _173_594 = (let _173_593 = (let _173_592 = (let _173_591 = (FStar_SMTEncoding_Term.mkIff (f_has_t_z, t_interp))
in (((f_has_t_z)::[])::[], (fsym)::cvars, _173_591))
in (FStar_SMTEncoding_Term.mkForall _173_592))
in (_173_593, a_name, a_name))
in FStar_SMTEncoding_Term.Assume (_173_594)))
in (

let t_decls = (FStar_List.append (FStar_List.append (FStar_List.append ((tdecl)::decls) decls') guard_decls) ((k_assumption)::(pre_typing)::(t_interp)::[]))
in (

let _83_730 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (tsym, cvar_sorts, t_decls))
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
in (let _173_596 = (let _173_595 = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (_173_595, Some ("Typing for non-total arrows"), a_name))
in FStar_SMTEncoding_Term.Assume (_173_596)))
in (

let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)
in (

let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let t_interp = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in (let _173_603 = (let _173_602 = (let _173_601 = (let _173_600 = (let _173_599 = (let _173_598 = (let _173_597 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _173_597))
in (f_has_t, _173_598))
in (FStar_SMTEncoding_Term.mkImp _173_599))
in (((f_has_t)::[])::[], (fsym)::[], _173_600))
in (mkForall_fuel _173_601))
in (_173_602, a_name, a_name))
in FStar_SMTEncoding_Term.Assume (_173_603)))
in (t, (tdecl)::(t_kinding)::(t_interp)::[])))))))))
end
end))
end
| FStar_Syntax_Syntax.Tm_refine (_83_743) -> begin
(

let _83_763 = (match ((FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.tk = _83_750; FStar_Syntax_Syntax.pos = _83_748; FStar_Syntax_Syntax.vars = _83_746} -> begin
(

let _83_758 = (FStar_Syntax_Subst.open_term (((x, None))::[]) f)
in (match (_83_758) with
| (b, f) -> begin
(let _173_605 = (let _173_604 = (FStar_List.hd b)
in (Prims.fst _173_604))
in (_173_605, f))
end))
end
| _83_760 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_83_763) with
| (x, f) -> begin
(

let _83_766 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (_83_766) with
| (base_t, decls) -> begin
(

let _83_770 = (gen_term_var env x)
in (match (_83_770) with
| (x, xtm, env') -> begin
(

let _83_773 = (encode_formula f env')
in (match (_83_773) with
| (refinement, decls') -> begin
(

let _83_776 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_83_776) with
| (fsym, fterm) -> begin
(

let encoding = (let _173_607 = (let _173_606 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in (_173_606, refinement))
in (FStar_SMTEncoding_Term.mkAnd _173_607))
in (

let cvars = (let _173_609 = (FStar_SMTEncoding_Term.free_variables encoding)
in (FStar_All.pipe_right _173_609 (FStar_List.filter (fun _83_781 -> (match (_83_781) with
| (y, _83_780) -> begin
((y <> x) && (y <> fsym))
end)))))
in (

let xfv = (x, FStar_SMTEncoding_Term.Term_sort)
in (

let ffv = (fsym, FStar_SMTEncoding_Term.Fuel_sort)
in (

let tkey = (FStar_SMTEncoding_Term.mkForall ([], (ffv)::(xfv)::cvars, encoding))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _83_788, _83_790) -> begin
(let _173_612 = (let _173_611 = (let _173_610 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in (t, _173_610))
in (FStar_SMTEncoding_Term.mkApp _173_611))
in (_173_612, []))
end
| None -> begin
(

let tsym = (varops.fresh "Tm_refine")
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun ((tsym, cvar_sorts, FStar_SMTEncoding_Term.Term_sort, None))
in (

let t = (let _173_614 = (let _173_613 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (tsym, _173_613))
in (FStar_SMTEncoding_Term.mkApp _173_614))
in (

let x_has_t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let t_haseq_base = (FStar_SMTEncoding_Term.mk_haseq base_t)
in (

let t_haseq_ref = (FStar_SMTEncoding_Term.mk_haseq t)
in (

let t_haseq = (let _173_618 = (let _173_617 = (let _173_616 = (let _173_615 = (FStar_SMTEncoding_Term.mkIff (t_haseq_ref, t_haseq_base))
in (((t_haseq_ref)::[])::[], cvars, _173_615))
in (FStar_SMTEncoding_Term.mkForall _173_616))
in (_173_617, Some ((Prims.strcat "haseq for " tsym)), Some ((Prims.strcat "haseq" tsym))))
in FStar_SMTEncoding_Term.Assume (_173_618))
in (

let t_kinding = (let _173_620 = (let _173_619 = (FStar_SMTEncoding_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (_173_619, Some ("refinement kinding"), Some ((Prims.strcat "refinement_kinding_" tsym))))
in FStar_SMTEncoding_Term.Assume (_173_620))
in (

let t_interp = (let _173_626 = (let _173_625 = (let _173_622 = (let _173_621 = (FStar_SMTEncoding_Term.mkIff (x_has_t, encoding))
in (((x_has_t)::[])::[], (ffv)::(xfv)::cvars, _173_621))
in (FStar_SMTEncoding_Term.mkForall _173_622))
in (let _173_624 = (let _173_623 = (FStar_Syntax_Print.term_to_string t0)
in Some (_173_623))
in (_173_625, _173_624, Some ((Prims.strcat "refinement_interpretation_" tsym)))))
in FStar_SMTEncoding_Term.Assume (_173_626))
in (

let t_decls = (FStar_List.append (FStar_List.append decls decls') ((tdecl)::(t_kinding)::(t_interp)::(t_haseq)::[]))
in (

let _83_806 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls))))))))))))))
end))))))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
(

let ttm = (let _173_627 = (FStar_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Term.mk_Term_uvar _173_627))
in (

let _83_815 = (encode_term_pred None k env ttm)
in (match (_83_815) with
| (t_has_k, decls) -> begin
(

let d = (let _173_633 = (let _173_632 = (let _173_631 = (let _173_630 = (let _173_629 = (let _173_628 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _173_628))
in (FStar_Util.format1 "@uvar_typing_%s" _173_629))
in (varops.fresh _173_630))
in Some (_173_631))
in (t_has_k, Some ("Uvar typing"), _173_632))
in FStar_SMTEncoding_Term.Assume (_173_633))
in (ttm, (FStar_List.append decls ((d)::[]))))
end)))
end
| FStar_Syntax_Syntax.Tm_app (_83_818) -> begin
(

let _83_822 = (FStar_Syntax_Util.head_and_args t0)
in (match (_83_822) with
| (head, args_e) -> begin
(match ((let _173_635 = (let _173_634 = (FStar_Syntax_Subst.compress head)
in _173_634.FStar_Syntax_Syntax.n)
in (_173_635, args_e))) with
| (_83_824, _83_826) when (head_redex env head) -> begin
(let _173_636 = (whnf env t)
in (encode_term _173_636 env))
end
| ((FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), (_)::((v1, _))::((v2, _))::[])) | ((FStar_Syntax_Syntax.Tm_fvar (fv), (_)::((v1, _))::((v2, _))::[])) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
(

let _83_866 = (encode_term v1 env)
in (match (_83_866) with
| (v1, decls1) -> begin
(

let _83_869 = (encode_term v2 env)
in (match (_83_869) with
| (v2, decls2) -> begin
(let _173_637 = (FStar_SMTEncoding_Term.mk_LexCons v1 v2)
in (_173_637, (FStar_List.append decls1 decls2)))
end))
end))
end
| _83_871 -> begin
(

let _83_874 = (encode_args args_e env)
in (match (_83_874) with
| (args, decls) -> begin
(

let encode_partial_app = (fun ht_opt -> (

let _83_879 = (encode_term head env)
in (match (_83_879) with
| (head, decls') -> begin
(

let app_tm = (mk_Apply_args head args)
in (match (ht_opt) with
| None -> begin
(app_tm, (FStar_List.append decls decls'))
end
| Some (formals, c) -> begin
(

let _83_888 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (_83_888) with
| (formals, rest) -> begin
(

let subst = (FStar_List.map2 (fun _83_892 _83_896 -> (match ((_83_892, _83_896)) with
| ((bv, _83_891), (a, _83_895)) -> begin
FStar_Syntax_Syntax.NT ((bv, a))
end)) formals args_e)
in (

let ty = (let _173_642 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right _173_642 (FStar_Syntax_Subst.subst subst)))
in (

let _83_901 = (encode_term_pred None ty env app_tm)
in (match (_83_901) with
| (has_type, decls'') -> begin
(

let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (

let e_typing = (let _173_646 = (let _173_645 = (FStar_SMTEncoding_Term.mkForall (((has_type)::[])::[], cvars, has_type))
in (let _173_644 = (let _173_643 = (varops.fresh "@partial_app_typing_")
in Some (_173_643))
in (_173_645, Some ("Partial app typing"), _173_644)))
in FStar_SMTEncoding_Term.Assume (_173_646))
in (app_tm, (FStar_List.append (FStar_List.append (FStar_List.append decls decls') decls'') ((e_typing)::[])))))
end))))
end))
end))
end)))
in (

let encode_full_app = (fun fv -> (

let _83_908 = (lookup_free_var_sym env fv)
in (match (_83_908) with
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
(let _173_650 = (let _173_649 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _173_649 Prims.snd))
in Some (_173_650))
end
| FStar_Syntax_Syntax.Tm_ascribed (_83_940, FStar_Util.Inl (t), _83_944) -> begin
Some (t)
end
| FStar_Syntax_Syntax.Tm_ascribed (_83_948, FStar_Util.Inr (c), _83_952) -> begin
Some ((FStar_Syntax_Util.comp_result c))
end
| _83_956 -> begin
None
end)
in (match (head_type) with
| None -> begin
(encode_partial_app None)
end
| Some (head_type) -> begin
(

let head_type = (let _173_651 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine _173_651))
in (

let _83_964 = (curried_arrow_formals_comp head_type)
in (match (_83_964) with
| (formals, c) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| _83_980 -> begin
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

let _83_989 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_83_989) with
| (bs, body, opening) -> begin
(

let fallback = (fun _83_991 -> (match (()) with
| () -> begin
(

let f = (varops.fresh "Tm_abs")
in (

let decl = FStar_SMTEncoding_Term.DeclFun ((f, [], FStar_SMTEncoding_Term.Term_sort, Some ("Imprecise function encoding")))
in (let _173_654 = (FStar_SMTEncoding_Term.mkFreeV (f, FStar_SMTEncoding_Term.Term_sort))
in (_173_654, (decl)::[]))))
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
(let _173_659 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening _173_659))
end
| FStar_Util.Inr (ef) -> begin
(let _173_661 = (let _173_660 = (FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange [] FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _173_660 Prims.fst))
in (FStar_Syntax_Syntax.mk_Total _173_661))
end))
in (match (lopt) with
| None -> begin
(

let _83_1007 = (let _173_663 = (let _173_662 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s" _173_662))
in (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos _173_663))
in (fallback ()))
end
| Some (lc) -> begin
if (let _173_664 = (is_pure_or_ghost lc)
in (FStar_All.pipe_left Prims.op_Negation _173_664)) then begin
(fallback ())
end else begin
(

let c = (codomain_eff lc)
in (

let _83_1018 = (encode_binders None bs env)
in (match (_83_1018) with
| (vars, guards, envbody, decls, _83_1017) -> begin
(

let _83_1021 = (encode_term body envbody)
in (match (_83_1021) with
| (body, decls') -> begin
(

let key_body = (let _173_668 = (let _173_667 = (let _173_666 = (let _173_665 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_173_665, body))
in (FStar_SMTEncoding_Term.mkImp _173_666))
in ([], vars, _173_667))
in (FStar_SMTEncoding_Term.mkForall _173_668))
in (

let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (

let tkey = (FStar_SMTEncoding_Term.mkForall ([], cvars, key_body))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _83_1027, _83_1029) -> begin
(let _173_671 = (let _173_670 = (let _173_669 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (t, _173_669))
in (FStar_SMTEncoding_Term.mkApp _173_670))
in (_173_671, []))
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

let f = (let _173_673 = (let _173_672 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (fsym, _173_672))
in (FStar_SMTEncoding_Term.mkApp _173_673))
in (

let app = (mk_Apply f vars)
in (

let tfun = (FStar_Syntax_Util.arrow bs c)
in (

let _83_1044 = (encode_term_pred None tfun env f)
in (match (_83_1044) with
| (f_has_t, decls'') -> begin
(

let typing_f = (

let a_name = Some ((Prims.strcat "typing_" fsym))
in (let _173_675 = (let _173_674 = (FStar_SMTEncoding_Term.mkForall (((f)::[])::[], cvars, f_has_t))
in (_173_674, a_name, a_name))
in FStar_SMTEncoding_Term.Assume (_173_675)))
in (

let interp_f = (

let a_name = Some ((Prims.strcat "interpretation_" fsym))
in (let _173_682 = (let _173_681 = (let _173_680 = (let _173_679 = (let _173_678 = (let _173_677 = (FStar_SMTEncoding_Term.mk_IsTyped app)
in (let _173_676 = (FStar_SMTEncoding_Term.mkEq (app, body))
in (_173_677, _173_676)))
in (FStar_SMTEncoding_Term.mkImp _173_678))
in (((app)::[])::[], (FStar_List.append vars cvars), _173_679))
in (FStar_SMTEncoding_Term.mkForall _173_680))
in (_173_681, a_name, a_name))
in FStar_SMTEncoding_Term.Assume (_173_682)))
in (

let f_decls = (FStar_List.append (FStar_List.append (FStar_List.append decls decls') ((fdecl)::decls'')) ((typing_f)::(interp_f)::[]))
in (

let _83_1050 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (fsym, cvar_sorts, f_decls))
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
| FStar_Syntax_Syntax.Tm_let ((_83_1053, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_83_1065); FStar_Syntax_Syntax.lbunivs = _83_1063; FStar_Syntax_Syntax.lbtyp = _83_1061; FStar_Syntax_Syntax.lbeff = _83_1059; FStar_Syntax_Syntax.lbdef = _83_1057})::_83_1055), _83_1071) -> begin
(FStar_All.failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _83_1080; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _83_1077; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (_83_1090) -> begin
(

let _83_1092 = (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (

let e = (varops.fresh "let-rec")
in (

let decl_e = FStar_SMTEncoding_Term.DeclFun ((e, [], FStar_SMTEncoding_Term.Term_sort, None))
in (let _173_683 = (FStar_SMTEncoding_Term.mkFreeV (e, FStar_SMTEncoding_Term.Term_sort))
in (_173_683, (decl_e)::[])))))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end))))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (

let _83_1108 = (encode_term e1 env)
in (match (_83_1108) with
| (ee1, decls1) -> begin
(

let _83_1111 = (FStar_Syntax_Subst.open_term (((x, None))::[]) e2)
in (match (_83_1111) with
| (xs, e2) -> begin
(

let _83_1115 = (FStar_List.hd xs)
in (match (_83_1115) with
| (x, _83_1114) -> begin
(

let env' = (push_term_var env x ee1)
in (

let _83_1119 = (encode_body e2 env')
in (match (_83_1119) with
| (ee2, decls2) -> begin
(ee2, (FStar_List.append decls1 decls2))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (

let _83_1127 = (encode_term e env)
in (match (_83_1127) with
| (scr, decls) -> begin
(

let _83_1164 = (FStar_List.fold_right (fun b _83_1131 -> (match (_83_1131) with
| (else_case, decls) -> begin
(

let _83_1135 = (FStar_Syntax_Subst.open_branch b)
in (match (_83_1135) with
| (p, w, br) -> begin
(

let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun _83_1139 _83_1142 -> (match ((_83_1139, _83_1142)) with
| ((env0, pattern), (else_case, decls)) -> begin
(

let guard = (pattern.guard scr)
in (

let projections = (pattern.projections scr)
in (

let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env _83_1148 -> (match (_83_1148) with
| (x, t) -> begin
(push_term_var env x t)
end)) env))
in (

let _83_1158 = (match (w) with
| None -> begin
(guard, [])
end
| Some (w) -> begin
(

let _83_1155 = (encode_term w env)
in (match (_83_1155) with
| (w, decls2) -> begin
(let _173_717 = (let _173_716 = (let _173_715 = (let _173_714 = (let _173_713 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Term.mkTrue)
in (w, _173_713))
in (FStar_SMTEncoding_Term.mkEq _173_714))
in (guard, _173_715))
in (FStar_SMTEncoding_Term.mkAnd _173_716))
in (_173_717, decls2))
end))
end)
in (match (_83_1158) with
| (guard, decls2) -> begin
(

let _83_1161 = (encode_br br env)
in (match (_83_1161) with
| (br, decls3) -> begin
(let _173_718 = (FStar_SMTEncoding_Term.mkITE (guard, br, else_case))
in (_173_718, (FStar_List.append (FStar_List.append decls decls2) decls3)))
end))
end)))))
end)) patterns (else_case, decls)))
end))
end)) pats (default_case, decls))
in (match (_83_1164) with
| (match_tm, decls) -> begin
(match_tm, decls)
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _83_1170 -> begin
(let _173_721 = (encode_one_pat env pat)
in (_173_721)::[])
end))
and encode_one_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> (

let _83_1173 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _173_724 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" _173_724))
end else begin
()
end
in (

let _83_1177 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (_83_1177) with
| (vars, pat_term) -> begin
(

let _83_1189 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun _83_1180 v -> (match (_83_1180) with
| (env, vars) -> begin
(

let _83_1186 = (gen_term_var env v)
in (match (_83_1186) with
| (xx, _83_1184, env) -> begin
(env, ((v, (xx, FStar_SMTEncoding_Term.Term_sort)))::vars)
end))
end)) (env, [])))
in (match (_83_1189) with
| (env, vars) -> begin
(

let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_83_1194) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_dot_term (_)) -> begin
FStar_SMTEncoding_Term.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _173_732 = (let _173_731 = (encode_const c)
in (scrutinee, _173_731))
in (FStar_SMTEncoding_Term.mkEq _173_732))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let is_f = (mk_data_tester env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _83_1216 -> (match (_83_1216) with
| (arg, _83_1215) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _173_735 = (FStar_SMTEncoding_Term.mkApp (proj, (scrutinee)::[]))
in (mk_guard arg _173_735)))
end))))
in (FStar_SMTEncoding_Term.mk_and_l ((is_f)::sub_term_guards))))
end))
in (

let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_83_1223) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _)) | (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
((x, scrutinee))::[]
end
| FStar_Syntax_Syntax.Pat_constant (_83_1233) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(let _173_743 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _83_1243 -> (match (_83_1243) with
| (arg, _83_1242) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _173_742 = (FStar_SMTEncoding_Term.mkApp (proj, (scrutinee)::[]))
in (mk_projections arg _173_742)))
end))))
in (FStar_All.pipe_right _173_743 FStar_List.flatten))
end))
in (

let pat_term = (fun _83_1246 -> (match (()) with
| () -> begin
(encode_term pat_term env)
end))
in (

let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in (env, pattern)))))
end))
end))))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (

let _83_1262 = (FStar_All.pipe_right l (FStar_List.fold_left (fun _83_1252 _83_1256 -> (match ((_83_1252, _83_1256)) with
| ((tms, decls), (t, _83_1255)) -> begin
(

let _83_1259 = (encode_term t env)
in (match (_83_1259) with
| (t, decls') -> begin
((t)::tms, (FStar_List.append decls decls'))
end))
end)) ([], [])))
in (match (_83_1262) with
| (l, decls) -> begin
((FStar_List.rev l), decls)
end)))
and encode_function_type_as_formula : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun induction_on new_pats t env -> (

let rec list_elements = (fun e -> (

let _83_1271 = (let _173_756 = (FStar_Syntax_Util.unmeta e)
in (FStar_Syntax_Util.head_and_args _173_756))
in (match (_83_1271) with
| (head, args) -> begin
(match ((let _173_758 = (let _173_757 = (FStar_Syntax_Util.un_uinst head)
in _173_757.FStar_Syntax_Syntax.n)
in (_173_758, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), _83_1275) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid) -> begin
[]
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_83_1288)::((hd, _83_1285))::((tl, _83_1281))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid) -> begin
(let _173_759 = (list_elements tl)
in (hd)::_173_759)
end
| _83_1292 -> begin
(

let _83_1293 = (FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern")
in [])
end)
end)))
in (

let one_pat = (fun p -> (

let _83_1299 = (let _173_762 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right _173_762 FStar_Syntax_Util.head_and_args))
in (match (_83_1299) with
| (head, args) -> begin
(match ((let _173_764 = (let _173_763 = (FStar_Syntax_Util.un_uinst head)
in _173_763.FStar_Syntax_Syntax.n)
in (_173_764, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((_83_1307, _83_1309))::((e, _83_1304))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpat_lid) -> begin
(e, None)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, _83_1317))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatT_lid) -> begin
(e, None)
end
| _83_1322 -> begin
(FStar_All.failwith "Unexpected pattern term")
end)
end)))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements p)
in (

let smt_pat_or = (fun t -> (

let _83_1330 = (let _173_769 = (FStar_Syntax_Util.unmeta t)
in (FStar_All.pipe_right _173_769 FStar_Syntax_Util.head_and_args))
in (match (_83_1330) with
| (head, args) -> begin
(match ((let _173_771 = (let _173_770 = (FStar_Syntax_Util.un_uinst head)
in _173_770.FStar_Syntax_Syntax.n)
in (_173_771, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, _83_1335))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatOr_lid) -> begin
Some (e)
end
| _83_1340 -> begin
None
end)
end)))
in (match (elts) with
| (t)::[] -> begin
(match ((smt_pat_or t)) with
| Some (e) -> begin
(let _173_774 = (list_elements e)
in (FStar_All.pipe_right _173_774 (FStar_List.map (fun branch -> (let _173_773 = (list_elements branch)
in (FStar_All.pipe_right _173_773 (FStar_List.map one_pat)))))))
end
| _83_1347 -> begin
(let _173_775 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_173_775)::[])
end)
end
| _83_1349 -> begin
(let _173_776 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_173_776)::[])
end))))
in (

let _83_1383 = (match ((let _173_777 = (FStar_Syntax_Subst.compress t)
in _173_777.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _83_1356 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_83_1356) with
| (binders, c) -> begin
(

let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| ((pre, _83_1368))::((post, _83_1364))::((pats, _83_1360))::[] -> begin
(

let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _173_778 = (lemma_pats pats')
in (binders, pre, post, _173_778)))
end
| _83_1376 -> begin
(FStar_All.failwith "impos")
end))
end))
end
| _83_1378 -> begin
(FStar_All.failwith "Impos")
end)
in (match (_83_1383) with
| (binders, pre, post, patterns) -> begin
(

let _83_1390 = (encode_binders None binders env)
in (match (_83_1390) with
| (vars, guards, env, decls, _83_1389) -> begin
(

let _83_1403 = (let _173_782 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (

let _83_1400 = (let _173_781 = (FStar_All.pipe_right branch (FStar_List.map (fun _83_1395 -> (match (_83_1395) with
| (t, _83_1394) -> begin
(encode_term t (

let _83_1396 = env
in {bindings = _83_1396.bindings; depth = _83_1396.depth; tcenv = _83_1396.tcenv; warn = _83_1396.warn; cache = _83_1396.cache; nolabels = _83_1396.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _83_1396.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _173_781 FStar_List.unzip))
in (match (_83_1400) with
| (pats, decls) -> begin
(pats, decls)
end)))))
in (FStar_All.pipe_right _173_782 FStar_List.unzip))
in (match (_83_1403) with
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
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _173_785 = (let _173_784 = (FStar_SMTEncoding_Term.mkFreeV l)
in (FStar_SMTEncoding_Term.mk_Precedes _173_784 e))
in (_173_785)::p))))
end
| _83_1413 -> begin
(

let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _173_791 = (FStar_SMTEncoding_Term.mk_Precedes tl e)
in (_173_791)::p))))
end
| ((x, FStar_SMTEncoding_Term.Term_sort))::vars -> begin
(let _173_793 = (let _173_792 = (FStar_SMTEncoding_Term.mkFreeV (x, FStar_SMTEncoding_Term.Term_sort))
in (FStar_SMTEncoding_Term.mk_LexCons _173_792 tl))
in (aux _173_793 vars))
end
| _83_1425 -> begin
pats
end))
in (let _173_794 = (FStar_SMTEncoding_Term.mkFreeV ("Prims.LexTop", FStar_SMTEncoding_Term.Term_sort))
in (aux _173_794 vars)))
end)
end)
in (

let env = (

let _83_1427 = env
in {bindings = _83_1427.bindings; depth = _83_1427.depth; tcenv = _83_1427.tcenv; warn = _83_1427.warn; cache = _83_1427.cache; nolabels = true; use_zfuel_name = _83_1427.use_zfuel_name; encode_non_total_function_typ = _83_1427.encode_non_total_function_typ})
in (

let _83_1432 = (let _173_795 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula _173_795 env))
in (match (_83_1432) with
| (pre, decls'') -> begin
(

let _83_1435 = (let _173_796 = (FStar_Syntax_Util.unmeta post)
in (encode_formula _173_796 env))
in (match (_83_1435) with
| (post, decls''') -> begin
(

let decls = (FStar_List.append (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'') decls''')
in (let _173_801 = (let _173_800 = (let _173_799 = (let _173_798 = (let _173_797 = (FStar_SMTEncoding_Term.mk_and_l ((pre)::guards))
in (_173_797, post))
in (FStar_SMTEncoding_Term.mkImp _173_798))
in (pats, vars, _173_799))
in (FStar_SMTEncoding_Term.mkForall _173_800))
in (_173_801, decls)))
end))
end)))))
end))
end))
end))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (

let debug = (fun phi -> if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _173_807 = (FStar_Syntax_Print.tag_of_term phi)
in (let _173_806 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print2 "Formula (%s)  %s\n" _173_807 _173_806)))
end else begin
()
end)
in (

let enc = (fun f l -> (

let _83_1451 = (FStar_Util.fold_map (fun decls x -> (

let _83_1448 = (encode_term (Prims.fst x) env)
in (match (_83_1448) with
| (t, decls') -> begin
((FStar_List.append decls decls'), t)
end))) [] l)
in (match (_83_1451) with
| (decls, args) -> begin
(let _173_823 = (f args)
in (_173_823, decls))
end)))
in (

let const_op = (fun f _83_1454 -> (f, []))
in (

let un_op = (fun f l -> (let _173_837 = (FStar_List.hd l)
in (FStar_All.pipe_left f _173_837)))
in (

let bin_op = (fun f _83_9 -> (match (_83_9) with
| (t1)::(t2)::[] -> begin
(f (t1, t2))
end
| _83_1465 -> begin
(FStar_All.failwith "Impossible")
end))
in (

let enc_prop_c = (fun f l -> (

let _83_1480 = (FStar_Util.fold_map (fun decls _83_1474 -> (match (_83_1474) with
| (t, _83_1473) -> begin
(

let _83_1477 = (encode_formula t env)
in (match (_83_1477) with
| (phi, decls') -> begin
((FStar_List.append decls decls'), phi)
end))
end)) [] l)
in (match (_83_1480) with
| (decls, phis) -> begin
(let _173_862 = (f phis)
in (_173_862, decls))
end)))
in (

let eq_op = (fun _83_10 -> (match (_83_10) with
| (_83_1487)::(_83_1485)::(e1)::(e2)::[] -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) l)
end))
in (

let mk_imp = (fun _83_11 -> (match (_83_11) with
| ((lhs, _83_1498))::((rhs, _83_1494))::[] -> begin
(

let _83_1503 = (encode_formula rhs env)
in (match (_83_1503) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _83_1506) -> begin
(l1, decls1)
end
| _83_1510 -> begin
(

let _83_1513 = (encode_formula lhs env)
in (match (_83_1513) with
| (l2, decls2) -> begin
(let _173_867 = (FStar_SMTEncoding_Term.mkImp (l2, l1))
in (_173_867, (FStar_List.append decls1 decls2)))
end))
end)
end))
end
| _83_1515 -> begin
(FStar_All.failwith "impossible")
end))
in (

let mk_ite = (fun _83_12 -> (match (_83_12) with
| ((guard, _83_1528))::((_then, _83_1524))::((_else, _83_1520))::[] -> begin
(

let _83_1533 = (encode_formula guard env)
in (match (_83_1533) with
| (g, decls1) -> begin
(

let _83_1536 = (encode_formula _then env)
in (match (_83_1536) with
| (t, decls2) -> begin
(

let _83_1539 = (encode_formula _else env)
in (match (_83_1539) with
| (e, decls3) -> begin
(

let res = (FStar_SMTEncoding_Term.mkITE (g, t, e))
in (res, (FStar_List.append (FStar_List.append decls1 decls2) decls3)))
end))
end))
end))
end
| _83_1542 -> begin
(FStar_All.failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (let _173_879 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f _173_879)))
in (

let connectives = (let _173_935 = (let _173_888 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkAnd))
in (FStar_Syntax_Const.and_lid, _173_888))
in (let _173_934 = (let _173_933 = (let _173_894 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkOr))
in (FStar_Syntax_Const.or_lid, _173_894))
in (let _173_932 = (let _173_931 = (let _173_930 = (let _173_903 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkIff))
in (FStar_Syntax_Const.iff_lid, _173_903))
in (let _173_929 = (let _173_928 = (let _173_927 = (let _173_912 = (FStar_All.pipe_left enc_prop_c (un_op FStar_SMTEncoding_Term.mkNot))
in (FStar_Syntax_Const.not_lid, _173_912))
in (_173_927)::((FStar_Syntax_Const.eq2_lid, eq_op))::((FStar_Syntax_Const.eq3_lid, eq_op))::((FStar_Syntax_Const.true_lid, (const_op FStar_SMTEncoding_Term.mkTrue)))::((FStar_Syntax_Const.false_lid, (const_op FStar_SMTEncoding_Term.mkFalse)))::[])
in ((FStar_Syntax_Const.ite_lid, mk_ite))::_173_928)
in (_173_930)::_173_929))
in ((FStar_Syntax_Const.imp_lid, mk_imp))::_173_931)
in (_173_933)::_173_932))
in (_173_935)::_173_934))
in (

let rec fallback = (fun phi -> (match (phi.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(

let _83_1560 = (encode_formula phi' env)
in (match (_83_1560) with
| (phi, decls) -> begin
(let _173_938 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled ((phi, msg, r))))
in (_173_938, decls))
end))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(

let _83_1567 = (encode_match e pats FStar_SMTEncoding_Term.mkFalse env encode_formula)
in (match (_83_1567) with
| (t, decls) -> begin
(t, decls)
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _83_1574; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _83_1571; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _83_1585 = (encode_let x t1 e1 e2 env encode_formula)
in (match (_83_1585) with
| (t, decls) -> begin
(t, decls)
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let head = (FStar_Syntax_Util.un_uinst head)
in (match ((head.FStar_Syntax_Syntax.n, args)) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_83_1602)::((x, _83_1599))::((t, _83_1595))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.has_type_lid) -> begin
(

let _83_1607 = (encode_term x env)
in (match (_83_1607) with
| (x, decls) -> begin
(

let _83_1610 = (encode_term t env)
in (match (_83_1610) with
| (t, decls') -> begin
(let _173_939 = (FStar_SMTEncoding_Term.mk_HasType x t)
in (_173_939, (FStar_List.append decls decls')))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((r, _83_1623))::((msg, _83_1619))::((phi, _83_1615))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.labeled_lid) -> begin
(match ((let _173_943 = (let _173_940 = (FStar_Syntax_Subst.compress r)
in _173_940.FStar_Syntax_Syntax.n)
in (let _173_942 = (let _173_941 = (FStar_Syntax_Subst.compress msg)
in _173_941.FStar_Syntax_Syntax.n)
in (_173_943, _173_942)))) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, _83_1632))) -> begin
(

let phi = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((phi, FStar_Syntax_Syntax.Meta_labeled (((FStar_Util.string_of_unicode s), r, false))))) None r)
in (fallback phi))
end
| _83_1639 -> begin
(fallback phi)
end)
end
| _83_1641 when (head_redex env head) -> begin
(let _173_944 = (whnf env phi)
in (encode_formula _173_944 env))
end
| _83_1643 -> begin
(

let _83_1646 = (encode_term phi env)
in (match (_83_1646) with
| (tt, decls) -> begin
(let _173_945 = (FStar_SMTEncoding_Term.mk_Valid tt)
in (_173_945, decls))
end))
end))
end
| _83_1648 -> begin
(

let _83_1651 = (encode_term phi env)
in (match (_83_1651) with
| (tt, decls) -> begin
(let _173_946 = (FStar_SMTEncoding_Term.mk_Valid tt)
in (_173_946, decls))
end))
end))
in (

let encode_q_body = (fun env bs ps body -> (

let _83_1663 = (encode_binders None bs env)
in (match (_83_1663) with
| (vars, guards, env, decls, _83_1662) -> begin
(

let _83_1676 = (let _173_958 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let _83_1673 = (let _173_957 = (FStar_All.pipe_right p (FStar_List.map (fun _83_1668 -> (match (_83_1668) with
| (t, _83_1667) -> begin
(encode_term t (

let _83_1669 = env
in {bindings = _83_1669.bindings; depth = _83_1669.depth; tcenv = _83_1669.tcenv; warn = _83_1669.warn; cache = _83_1669.cache; nolabels = _83_1669.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _83_1669.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _173_957 FStar_List.unzip))
in (match (_83_1673) with
| (p, decls) -> begin
(p, (FStar_List.flatten decls))
end)))))
in (FStar_All.pipe_right _173_958 FStar_List.unzip))
in (match (_83_1676) with
| (pats, decls') -> begin
(

let _83_1679 = (encode_formula body env)
in (match (_83_1679) with
| (body, decls'') -> begin
(

let guards = (match (pats) with
| (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.hash = _83_1683; FStar_SMTEncoding_Term.freevars = _83_1681})::[])::[] -> begin
[]
end
| _83_1694 -> begin
guards
end)
in (let _173_959 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (vars, pats, _173_959, body, (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls''))))
end))
end))
end)))
in (

let _83_1696 = (debug phi)
in (

let phi = (FStar_Syntax_Util.unascribe phi)
in (match ((FStar_Syntax_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _83_1708 -> (match (_83_1708) with
| (l, _83_1707) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_83_1711, f) -> begin
(f arms)
end)
end
| Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
(

let _83_1721 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _173_976 = (FStar_All.pipe_right vars (FStar_Syntax_Print.binders_to_string "; "))
in (FStar_Util.print1 ">>>> Got QALL [%s]\n" _173_976))
end else begin
()
end
in (

let _83_1728 = (encode_q_body env vars pats body)
in (match (_83_1728) with
| (vars, pats, guard, body, decls) -> begin
(

let tm = (let _173_978 = (let _173_977 = (FStar_SMTEncoding_Term.mkImp (guard, body))
in (pats, vars, _173_977))
in (FStar_SMTEncoding_Term.mkForall _173_978))
in (

let _83_1730 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _173_979 = (FStar_SMTEncoding_Term.termToSmt tm)
in (FStar_Util.print1 ">>>> Encoded QALL to %s\n" _173_979))
end else begin
()
end
in (tm, decls)))
end)))
end
| Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
(

let _83_1743 = (encode_q_body env vars pats body)
in (match (_83_1743) with
| (vars, pats, guard, body, decls) -> begin
(let _173_982 = (let _173_981 = (let _173_980 = (FStar_SMTEncoding_Term.mkAnd (guard, body))
in (pats, vars, _173_980))
in (FStar_SMTEncoding_Term.mkExists _173_981))
in (_173_982, decls))
end))
end)))))))))))))))))


type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.decl Prims.list; is : FStar_Ident.lident  ->  Prims.bool}


let is_Mkprims_t : prims_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkprims_t"))))


let prims : prims_t = (

let _83_1749 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (_83_1749) with
| (asym, a) -> begin
(

let _83_1752 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_83_1752) with
| (xsym, x) -> begin
(

let _83_1755 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (_83_1755) with
| (ysym, y) -> begin
(

let deffun = (fun vars body x -> (FStar_SMTEncoding_Term.DefineFun ((x, vars, FStar_SMTEncoding_Term.Term_sort, body, None)))::[])
in (

let quant = (fun vars body x -> (

let t1 = (let _173_1025 = (let _173_1024 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (x, _173_1024))
in (FStar_SMTEncoding_Term.mkApp _173_1025))
in (

let vname_decl = (let _173_1027 = (let _173_1026 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (x, _173_1026, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_173_1027))
in (let _173_1033 = (let _173_1032 = (let _173_1031 = (let _173_1030 = (let _173_1029 = (let _173_1028 = (FStar_SMTEncoding_Term.mkEq (t1, body))
in (((t1)::[])::[], vars, _173_1028))
in (FStar_SMTEncoding_Term.mkForall _173_1029))
in (_173_1030, None, Some ((Prims.strcat "primitive_" x))))
in FStar_SMTEncoding_Term.Assume (_173_1031))
in (_173_1032)::[])
in (vname_decl)::_173_1033))))
in (

let axy = ((asym, FStar_SMTEncoding_Term.Term_sort))::((xsym, FStar_SMTEncoding_Term.Term_sort))::((ysym, FStar_SMTEncoding_Term.Term_sort))::[]
in (

let xy = ((xsym, FStar_SMTEncoding_Term.Term_sort))::((ysym, FStar_SMTEncoding_Term.Term_sort))::[]
in (

let qx = ((xsym, FStar_SMTEncoding_Term.Term_sort))::[]
in (

let prims = (let _173_1193 = (let _173_1042 = (let _173_1041 = (let _173_1040 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _173_1040))
in (quant axy _173_1041))
in (FStar_Syntax_Const.op_Eq, _173_1042))
in (let _173_1192 = (let _173_1191 = (let _173_1049 = (let _173_1048 = (let _173_1047 = (let _173_1046 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (FStar_SMTEncoding_Term.mkNot _173_1046))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _173_1047))
in (quant axy _173_1048))
in (FStar_Syntax_Const.op_notEq, _173_1049))
in (let _173_1190 = (let _173_1189 = (let _173_1058 = (let _173_1057 = (let _173_1056 = (let _173_1055 = (let _173_1054 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _173_1053 = (FStar_SMTEncoding_Term.unboxInt y)
in (_173_1054, _173_1053)))
in (FStar_SMTEncoding_Term.mkLT _173_1055))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _173_1056))
in (quant xy _173_1057))
in (FStar_Syntax_Const.op_LT, _173_1058))
in (let _173_1188 = (let _173_1187 = (let _173_1067 = (let _173_1066 = (let _173_1065 = (let _173_1064 = (let _173_1063 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _173_1062 = (FStar_SMTEncoding_Term.unboxInt y)
in (_173_1063, _173_1062)))
in (FStar_SMTEncoding_Term.mkLTE _173_1064))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _173_1065))
in (quant xy _173_1066))
in (FStar_Syntax_Const.op_LTE, _173_1067))
in (let _173_1186 = (let _173_1185 = (let _173_1076 = (let _173_1075 = (let _173_1074 = (let _173_1073 = (let _173_1072 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _173_1071 = (FStar_SMTEncoding_Term.unboxInt y)
in (_173_1072, _173_1071)))
in (FStar_SMTEncoding_Term.mkGT _173_1073))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _173_1074))
in (quant xy _173_1075))
in (FStar_Syntax_Const.op_GT, _173_1076))
in (let _173_1184 = (let _173_1183 = (let _173_1085 = (let _173_1084 = (let _173_1083 = (let _173_1082 = (let _173_1081 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _173_1080 = (FStar_SMTEncoding_Term.unboxInt y)
in (_173_1081, _173_1080)))
in (FStar_SMTEncoding_Term.mkGTE _173_1082))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _173_1083))
in (quant xy _173_1084))
in (FStar_Syntax_Const.op_GTE, _173_1085))
in (let _173_1182 = (let _173_1181 = (let _173_1094 = (let _173_1093 = (let _173_1092 = (let _173_1091 = (let _173_1090 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _173_1089 = (FStar_SMTEncoding_Term.unboxInt y)
in (_173_1090, _173_1089)))
in (FStar_SMTEncoding_Term.mkSub _173_1091))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _173_1092))
in (quant xy _173_1093))
in (FStar_Syntax_Const.op_Subtraction, _173_1094))
in (let _173_1180 = (let _173_1179 = (let _173_1101 = (let _173_1100 = (let _173_1099 = (let _173_1098 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Term.mkMinus _173_1098))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _173_1099))
in (quant qx _173_1100))
in (FStar_Syntax_Const.op_Minus, _173_1101))
in (let _173_1178 = (let _173_1177 = (let _173_1110 = (let _173_1109 = (let _173_1108 = (let _173_1107 = (let _173_1106 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _173_1105 = (FStar_SMTEncoding_Term.unboxInt y)
in (_173_1106, _173_1105)))
in (FStar_SMTEncoding_Term.mkAdd _173_1107))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _173_1108))
in (quant xy _173_1109))
in (FStar_Syntax_Const.op_Addition, _173_1110))
in (let _173_1176 = (let _173_1175 = (let _173_1119 = (let _173_1118 = (let _173_1117 = (let _173_1116 = (let _173_1115 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _173_1114 = (FStar_SMTEncoding_Term.unboxInt y)
in (_173_1115, _173_1114)))
in (FStar_SMTEncoding_Term.mkMul _173_1116))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _173_1117))
in (quant xy _173_1118))
in (FStar_Syntax_Const.op_Multiply, _173_1119))
in (let _173_1174 = (let _173_1173 = (let _173_1128 = (let _173_1127 = (let _173_1126 = (let _173_1125 = (let _173_1124 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _173_1123 = (FStar_SMTEncoding_Term.unboxInt y)
in (_173_1124, _173_1123)))
in (FStar_SMTEncoding_Term.mkDiv _173_1125))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _173_1126))
in (quant xy _173_1127))
in (FStar_Syntax_Const.op_Division, _173_1128))
in (let _173_1172 = (let _173_1171 = (let _173_1137 = (let _173_1136 = (let _173_1135 = (let _173_1134 = (let _173_1133 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _173_1132 = (FStar_SMTEncoding_Term.unboxInt y)
in (_173_1133, _173_1132)))
in (FStar_SMTEncoding_Term.mkMod _173_1134))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _173_1135))
in (quant xy _173_1136))
in (FStar_Syntax_Const.op_Modulus, _173_1137))
in (let _173_1170 = (let _173_1169 = (let _173_1146 = (let _173_1145 = (let _173_1144 = (let _173_1143 = (let _173_1142 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _173_1141 = (FStar_SMTEncoding_Term.unboxBool y)
in (_173_1142, _173_1141)))
in (FStar_SMTEncoding_Term.mkAnd _173_1143))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _173_1144))
in (quant xy _173_1145))
in (FStar_Syntax_Const.op_And, _173_1146))
in (let _173_1168 = (let _173_1167 = (let _173_1155 = (let _173_1154 = (let _173_1153 = (let _173_1152 = (let _173_1151 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _173_1150 = (FStar_SMTEncoding_Term.unboxBool y)
in (_173_1151, _173_1150)))
in (FStar_SMTEncoding_Term.mkOr _173_1152))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _173_1153))
in (quant xy _173_1154))
in (FStar_Syntax_Const.op_Or, _173_1155))
in (let _173_1166 = (let _173_1165 = (let _173_1162 = (let _173_1161 = (let _173_1160 = (let _173_1159 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Term.mkNot _173_1159))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _173_1160))
in (quant qx _173_1161))
in (FStar_Syntax_Const.op_Negation, _173_1162))
in (_173_1165)::[])
in (_173_1167)::_173_1166))
in (_173_1169)::_173_1168))
in (_173_1171)::_173_1170))
in (_173_1173)::_173_1172))
in (_173_1175)::_173_1174))
in (_173_1177)::_173_1176))
in (_173_1179)::_173_1178))
in (_173_1181)::_173_1180))
in (_173_1183)::_173_1182))
in (_173_1185)::_173_1184))
in (_173_1187)::_173_1186))
in (_173_1189)::_173_1188))
in (_173_1191)::_173_1190))
in (_173_1193)::_173_1192))
in (

let mk = (fun l v -> (let _173_1225 = (FStar_All.pipe_right prims (FStar_List.filter (fun _83_1775 -> (match (_83_1775) with
| (l', _83_1774) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right _173_1225 (FStar_List.collect (fun _83_1779 -> (match (_83_1779) with
| (_83_1777, b) -> begin
(b v)
end))))))
in (

let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _83_1785 -> (match (_83_1785) with
| (l', _83_1784) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is}))))))))
end))
end))
end))


let pretype_axiom : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun tapp vars -> (

let _83_1791 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_83_1791) with
| (xxsym, xx) -> begin
(

let _83_1794 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_83_1794) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (let _173_1253 = (let _173_1252 = (let _173_1249 = (let _173_1248 = (let _173_1247 = (let _173_1246 = (let _173_1245 = (let _173_1244 = (FStar_SMTEncoding_Term.mkApp ("PreType", (xx)::[]))
in (tapp, _173_1244))
in (FStar_SMTEncoding_Term.mkEq _173_1245))
in (xx_has_type, _173_1246))
in (FStar_SMTEncoding_Term.mkImp _173_1247))
in (((xx_has_type)::[])::[], ((xxsym, FStar_SMTEncoding_Term.Term_sort))::((ffsym, FStar_SMTEncoding_Term.Fuel_sort))::vars, _173_1248))
in (FStar_SMTEncoding_Term.mkForall _173_1249))
in (let _173_1251 = (let _173_1250 = (varops.fresh "@pretyping_")
in Some (_173_1250))
in (_173_1252, Some ("pretyping"), _173_1251)))
in FStar_SMTEncoding_Term.Assume (_173_1253)))
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
in (let _173_1274 = (let _173_1265 = (let _173_1264 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in (_173_1264, Some ("unit typing"), Some ("unit_typing")))
in FStar_SMTEncoding_Term.Assume (_173_1265))
in (let _173_1273 = (let _173_1272 = (let _173_1271 = (let _173_1270 = (let _173_1269 = (let _173_1268 = (let _173_1267 = (let _173_1266 = (FStar_SMTEncoding_Term.mkEq (x, FStar_SMTEncoding_Term.mk_Term_unit))
in (typing_pred, _173_1266))
in (FStar_SMTEncoding_Term.mkImp _173_1267))
in (((typing_pred)::[])::[], (xx)::[], _173_1268))
in (mkForall_fuel _173_1269))
in (_173_1270, Some ("unit inversion"), Some ("unit_inversion")))
in FStar_SMTEncoding_Term.Assume (_173_1271))
in (_173_1272)::[])
in (_173_1274)::_173_1273))))
in (

let mk_bool = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _173_1297 = (let _173_1288 = (let _173_1287 = (let _173_1286 = (let _173_1285 = (let _173_1282 = (let _173_1281 = (FStar_SMTEncoding_Term.boxBool b)
in (_173_1281)::[])
in (_173_1282)::[])
in (let _173_1284 = (let _173_1283 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType _173_1283 tt))
in (_173_1285, (bb)::[], _173_1284)))
in (FStar_SMTEncoding_Term.mkForall _173_1286))
in (_173_1287, Some ("bool typing"), Some ("bool_typing")))
in FStar_SMTEncoding_Term.Assume (_173_1288))
in (let _173_1296 = (let _173_1295 = (let _173_1294 = (let _173_1293 = (let _173_1292 = (let _173_1291 = (let _173_1290 = (let _173_1289 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in (typing_pred, _173_1289))
in (FStar_SMTEncoding_Term.mkImp _173_1290))
in (((typing_pred)::[])::[], (xx)::[], _173_1291))
in (mkForall_fuel _173_1292))
in (_173_1293, Some ("bool inversion"), Some ("bool_inversion")))
in FStar_SMTEncoding_Term.Assume (_173_1294))
in (_173_1295)::[])
in (_173_1297)::_173_1296))))))
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

let precedes = (let _173_1311 = (let _173_1310 = (let _173_1309 = (let _173_1308 = (let _173_1307 = (let _173_1306 = (FStar_SMTEncoding_Term.boxInt a)
in (let _173_1305 = (let _173_1304 = (FStar_SMTEncoding_Term.boxInt b)
in (_173_1304)::[])
in (_173_1306)::_173_1305))
in (tt)::_173_1307)
in (tt)::_173_1308)
in ("Prims.Precedes", _173_1309))
in (FStar_SMTEncoding_Term.mkApp _173_1310))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _173_1311))
in (

let precedes_y_x = (let _173_1312 = (FStar_SMTEncoding_Term.mkApp ("Precedes", (y)::(x)::[]))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _173_1312))
in (let _173_1354 = (let _173_1320 = (let _173_1319 = (let _173_1318 = (let _173_1317 = (let _173_1314 = (let _173_1313 = (FStar_SMTEncoding_Term.boxInt b)
in (_173_1313)::[])
in (_173_1314)::[])
in (let _173_1316 = (let _173_1315 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType _173_1315 tt))
in (_173_1317, (bb)::[], _173_1316)))
in (FStar_SMTEncoding_Term.mkForall _173_1318))
in (_173_1319, Some ("int typing"), Some ("int_typing")))
in FStar_SMTEncoding_Term.Assume (_173_1320))
in (let _173_1353 = (let _173_1352 = (let _173_1326 = (let _173_1325 = (let _173_1324 = (let _173_1323 = (let _173_1322 = (let _173_1321 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in (typing_pred, _173_1321))
in (FStar_SMTEncoding_Term.mkImp _173_1322))
in (((typing_pred)::[])::[], (xx)::[], _173_1323))
in (mkForall_fuel _173_1324))
in (_173_1325, Some ("int inversion"), Some ("int_inversion")))
in FStar_SMTEncoding_Term.Assume (_173_1326))
in (let _173_1351 = (let _173_1350 = (let _173_1349 = (let _173_1348 = (let _173_1347 = (let _173_1346 = (let _173_1345 = (let _173_1344 = (let _173_1343 = (let _173_1342 = (let _173_1341 = (let _173_1340 = (let _173_1329 = (let _173_1328 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _173_1327 = (FStar_SMTEncoding_Term.mkInteger' 0)
in (_173_1328, _173_1327)))
in (FStar_SMTEncoding_Term.mkGT _173_1329))
in (let _173_1339 = (let _173_1338 = (let _173_1332 = (let _173_1331 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _173_1330 = (FStar_SMTEncoding_Term.mkInteger' 0)
in (_173_1331, _173_1330)))
in (FStar_SMTEncoding_Term.mkGTE _173_1332))
in (let _173_1337 = (let _173_1336 = (let _173_1335 = (let _173_1334 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _173_1333 = (FStar_SMTEncoding_Term.unboxInt x)
in (_173_1334, _173_1333)))
in (FStar_SMTEncoding_Term.mkLT _173_1335))
in (_173_1336)::[])
in (_173_1338)::_173_1337))
in (_173_1340)::_173_1339))
in (typing_pred_y)::_173_1341)
in (typing_pred)::_173_1342)
in (FStar_SMTEncoding_Term.mk_and_l _173_1343))
in (_173_1344, precedes_y_x))
in (FStar_SMTEncoding_Term.mkImp _173_1345))
in (((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[], (xx)::(yy)::[], _173_1346))
in (mkForall_fuel _173_1347))
in (_173_1348, Some ("well-founded ordering on nat (alt)"), Some ("well-founded-ordering-on-nat")))
in FStar_SMTEncoding_Term.Assume (_173_1349))
in (_173_1350)::[])
in (_173_1352)::_173_1351))
in (_173_1354)::_173_1353)))))))))))
in (

let mk_str = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = ("b", FStar_SMTEncoding_Term.String_sort)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _173_1377 = (let _173_1368 = (let _173_1367 = (let _173_1366 = (let _173_1365 = (let _173_1362 = (let _173_1361 = (FStar_SMTEncoding_Term.boxString b)
in (_173_1361)::[])
in (_173_1362)::[])
in (let _173_1364 = (let _173_1363 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType _173_1363 tt))
in (_173_1365, (bb)::[], _173_1364)))
in (FStar_SMTEncoding_Term.mkForall _173_1366))
in (_173_1367, Some ("string typing"), Some ("string_typing")))
in FStar_SMTEncoding_Term.Assume (_173_1368))
in (let _173_1376 = (let _173_1375 = (let _173_1374 = (let _173_1373 = (let _173_1372 = (let _173_1371 = (let _173_1370 = (let _173_1369 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in (typing_pred, _173_1369))
in (FStar_SMTEncoding_Term.mkImp _173_1370))
in (((typing_pred)::[])::[], (xx)::[], _173_1371))
in (mkForall_fuel _173_1372))
in (_173_1373, Some ("string inversion"), Some ("string_inversion")))
in FStar_SMTEncoding_Term.Assume (_173_1374))
in (_173_1375)::[])
in (_173_1377)::_173_1376))))))
in (

let mk_ref = (fun env reft_name _83_1833 -> (

let r = ("r", FStar_SMTEncoding_Term.Ref_sort)
in (

let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (

let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (

let refa = (let _173_1386 = (let _173_1385 = (let _173_1384 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (_173_1384)::[])
in (reft_name, _173_1385))
in (FStar_SMTEncoding_Term.mkApp _173_1386))
in (

let refb = (let _173_1389 = (let _173_1388 = (let _173_1387 = (FStar_SMTEncoding_Term.mkFreeV bb)
in (_173_1387)::[])
in (reft_name, _173_1388))
in (FStar_SMTEncoding_Term.mkApp _173_1389))
in (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (

let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (let _173_1408 = (let _173_1395 = (let _173_1394 = (let _173_1393 = (let _173_1392 = (let _173_1391 = (let _173_1390 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in (typing_pred, _173_1390))
in (FStar_SMTEncoding_Term.mkImp _173_1391))
in (((typing_pred)::[])::[], (xx)::(aa)::[], _173_1392))
in (mkForall_fuel _173_1393))
in (_173_1394, Some ("ref inversion"), Some ("ref_inversion")))
in FStar_SMTEncoding_Term.Assume (_173_1395))
in (let _173_1407 = (let _173_1406 = (let _173_1405 = (let _173_1404 = (let _173_1403 = (let _173_1402 = (let _173_1401 = (let _173_1400 = (FStar_SMTEncoding_Term.mkAnd (typing_pred, typing_pred_b))
in (let _173_1399 = (let _173_1398 = (let _173_1397 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (let _173_1396 = (FStar_SMTEncoding_Term.mkFreeV bb)
in (_173_1397, _173_1396)))
in (FStar_SMTEncoding_Term.mkEq _173_1398))
in (_173_1400, _173_1399)))
in (FStar_SMTEncoding_Term.mkImp _173_1401))
in (((typing_pred)::(typing_pred_b)::[])::[], (xx)::(aa)::(bb)::[], _173_1402))
in (mkForall_fuel' 2 _173_1403))
in (_173_1404, Some ("ref typing is injective"), Some ("ref_injectivity")))
in FStar_SMTEncoding_Term.Assume (_173_1405))
in (_173_1406)::[])
in (_173_1408)::_173_1407))))))))))
in (

let mk_false_interp = (fun env nm false_tm -> (

let valid = (FStar_SMTEncoding_Term.mkApp ("Valid", (false_tm)::[]))
in (let _173_1417 = (let _173_1416 = (let _173_1415 = (FStar_SMTEncoding_Term.mkIff (FStar_SMTEncoding_Term.mkFalse, valid))
in (_173_1415, Some ("False interpretation"), Some ("false_interp")))
in FStar_SMTEncoding_Term.Assume (_173_1416))
in (_173_1417)::[])))
in (

let mk_and_interp = (fun env conj _83_1850 -> (

let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (

let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (

let valid = (let _173_1426 = (let _173_1425 = (let _173_1424 = (FStar_SMTEncoding_Term.mkApp (conj, (a)::(b)::[]))
in (_173_1424)::[])
in ("Valid", _173_1425))
in (FStar_SMTEncoding_Term.mkApp _173_1426))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _173_1433 = (let _173_1432 = (let _173_1431 = (let _173_1430 = (let _173_1429 = (let _173_1428 = (let _173_1427 = (FStar_SMTEncoding_Term.mkAnd (valid_a, valid_b))
in (_173_1427, valid))
in (FStar_SMTEncoding_Term.mkIff _173_1428))
in (((valid)::[])::[], (aa)::(bb)::[], _173_1429))
in (FStar_SMTEncoding_Term.mkForall _173_1430))
in (_173_1431, Some ("/\\ interpretation"), Some ("l_and-interp")))
in FStar_SMTEncoding_Term.Assume (_173_1432))
in (_173_1433)::[])))))))))
in (

let mk_or_interp = (fun env disj _83_1862 -> (

let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (

let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (

let valid = (let _173_1442 = (let _173_1441 = (let _173_1440 = (FStar_SMTEncoding_Term.mkApp (disj, (a)::(b)::[]))
in (_173_1440)::[])
in ("Valid", _173_1441))
in (FStar_SMTEncoding_Term.mkApp _173_1442))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _173_1449 = (let _173_1448 = (let _173_1447 = (let _173_1446 = (let _173_1445 = (let _173_1444 = (let _173_1443 = (FStar_SMTEncoding_Term.mkOr (valid_a, valid_b))
in (_173_1443, valid))
in (FStar_SMTEncoding_Term.mkIff _173_1444))
in (((valid)::[])::[], (aa)::(bb)::[], _173_1445))
in (FStar_SMTEncoding_Term.mkForall _173_1446))
in (_173_1447, Some ("\\/ interpretation"), Some ("l_or-interp")))
in FStar_SMTEncoding_Term.Assume (_173_1448))
in (_173_1449)::[])))))))))
in (

let mk_eq2_interp = (fun env eq2 tt -> (

let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (

let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (

let yy = ("y", FStar_SMTEncoding_Term.Term_sort)
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (

let y = (FStar_SMTEncoding_Term.mkFreeV yy)
in (

let valid = (let _173_1458 = (let _173_1457 = (let _173_1456 = (FStar_SMTEncoding_Term.mkApp (eq2, (a)::(x)::(y)::[]))
in (_173_1456)::[])
in ("Valid", _173_1457))
in (FStar_SMTEncoding_Term.mkApp _173_1458))
in (let _173_1465 = (let _173_1464 = (let _173_1463 = (let _173_1462 = (let _173_1461 = (let _173_1460 = (let _173_1459 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (_173_1459, valid))
in (FStar_SMTEncoding_Term.mkIff _173_1460))
in (((valid)::[])::[], (aa)::(xx)::(yy)::[], _173_1461))
in (FStar_SMTEncoding_Term.mkForall _173_1462))
in (_173_1463, Some ("Eq2 interpretation"), Some ("eq2-interp")))
in FStar_SMTEncoding_Term.Assume (_173_1464))
in (_173_1465)::[])))))))))
in (

let mk_eq3_interp = (fun env eq3 tt -> (

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

let valid = (let _173_1474 = (let _173_1473 = (let _173_1472 = (FStar_SMTEncoding_Term.mkApp (eq3, (a)::(b)::(x)::(y)::[]))
in (_173_1472)::[])
in ("Valid", _173_1473))
in (FStar_SMTEncoding_Term.mkApp _173_1474))
in (let _173_1481 = (let _173_1480 = (let _173_1479 = (let _173_1478 = (let _173_1477 = (let _173_1476 = (let _173_1475 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (_173_1475, valid))
in (FStar_SMTEncoding_Term.mkIff _173_1476))
in (((valid)::[])::[], (aa)::(bb)::(xx)::(yy)::[], _173_1477))
in (FStar_SMTEncoding_Term.mkForall _173_1478))
in (_173_1479, Some ("Eq3 interpretation"), Some ("eq3-interp")))
in FStar_SMTEncoding_Term.Assume (_173_1480))
in (_173_1481)::[])))))))))))
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

let valid = (let _173_1490 = (let _173_1489 = (let _173_1488 = (FStar_SMTEncoding_Term.mkApp (imp, (a)::(b)::[]))
in (_173_1488)::[])
in ("Valid", _173_1489))
in (FStar_SMTEncoding_Term.mkApp _173_1490))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _173_1497 = (let _173_1496 = (let _173_1495 = (let _173_1494 = (let _173_1493 = (let _173_1492 = (let _173_1491 = (FStar_SMTEncoding_Term.mkImp (valid_a, valid_b))
in (_173_1491, valid))
in (FStar_SMTEncoding_Term.mkIff _173_1492))
in (((valid)::[])::[], (aa)::(bb)::[], _173_1493))
in (FStar_SMTEncoding_Term.mkForall _173_1494))
in (_173_1495, Some ("==> interpretation"), Some ("l_imp-interp")))
in FStar_SMTEncoding_Term.Assume (_173_1496))
in (_173_1497)::[])))))))))
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

let valid = (let _173_1506 = (let _173_1505 = (let _173_1504 = (FStar_SMTEncoding_Term.mkApp (iff, (a)::(b)::[]))
in (_173_1504)::[])
in ("Valid", _173_1505))
in (FStar_SMTEncoding_Term.mkApp _173_1506))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _173_1513 = (let _173_1512 = (let _173_1511 = (let _173_1510 = (let _173_1509 = (let _173_1508 = (let _173_1507 = (FStar_SMTEncoding_Term.mkIff (valid_a, valid_b))
in (_173_1507, valid))
in (FStar_SMTEncoding_Term.mkIff _173_1508))
in (((valid)::[])::[], (aa)::(bb)::[], _173_1509))
in (FStar_SMTEncoding_Term.mkForall _173_1510))
in (_173_1511, Some ("<==> interpretation"), Some ("l_iff-interp")))
in FStar_SMTEncoding_Term.Assume (_173_1512))
in (_173_1513)::[])))))))))
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

let valid = (let _173_1522 = (let _173_1521 = (let _173_1520 = (FStar_SMTEncoding_Term.mkApp (for_all, (a)::(b)::[]))
in (_173_1520)::[])
in ("Valid", _173_1521))
in (FStar_SMTEncoding_Term.mkApp _173_1522))
in (

let valid_b_x = (let _173_1525 = (let _173_1524 = (let _173_1523 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_173_1523)::[])
in ("Valid", _173_1524))
in (FStar_SMTEncoding_Term.mkApp _173_1525))
in (let _173_1539 = (let _173_1538 = (let _173_1537 = (let _173_1536 = (let _173_1535 = (let _173_1534 = (let _173_1533 = (let _173_1532 = (let _173_1531 = (let _173_1527 = (let _173_1526 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_173_1526)::[])
in (_173_1527)::[])
in (let _173_1530 = (let _173_1529 = (let _173_1528 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_173_1528, valid_b_x))
in (FStar_SMTEncoding_Term.mkImp _173_1529))
in (_173_1531, (xx)::[], _173_1530)))
in (FStar_SMTEncoding_Term.mkForall _173_1532))
in (_173_1533, valid))
in (FStar_SMTEncoding_Term.mkIff _173_1534))
in (((valid)::[])::[], (aa)::(bb)::[], _173_1535))
in (FStar_SMTEncoding_Term.mkForall _173_1536))
in (_173_1537, Some ("forall interpretation"), Some ("forall-interp")))
in FStar_SMTEncoding_Term.Assume (_173_1538))
in (_173_1539)::[]))))))))))
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

let valid = (let _173_1548 = (let _173_1547 = (let _173_1546 = (FStar_SMTEncoding_Term.mkApp (for_some, (a)::(b)::[]))
in (_173_1546)::[])
in ("Valid", _173_1547))
in (FStar_SMTEncoding_Term.mkApp _173_1548))
in (

let valid_b_x = (let _173_1551 = (let _173_1550 = (let _173_1549 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_173_1549)::[])
in ("Valid", _173_1550))
in (FStar_SMTEncoding_Term.mkApp _173_1551))
in (let _173_1565 = (let _173_1564 = (let _173_1563 = (let _173_1562 = (let _173_1561 = (let _173_1560 = (let _173_1559 = (let _173_1558 = (let _173_1557 = (let _173_1553 = (let _173_1552 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_173_1552)::[])
in (_173_1553)::[])
in (let _173_1556 = (let _173_1555 = (let _173_1554 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_173_1554, valid_b_x))
in (FStar_SMTEncoding_Term.mkImp _173_1555))
in (_173_1557, (xx)::[], _173_1556)))
in (FStar_SMTEncoding_Term.mkExists _173_1558))
in (_173_1559, valid))
in (FStar_SMTEncoding_Term.mkIff _173_1560))
in (((valid)::[])::[], (aa)::(bb)::[], _173_1561))
in (FStar_SMTEncoding_Term.mkForall _173_1562))
in (_173_1563, Some ("exists interpretation"), Some ("exists-interp")))
in FStar_SMTEncoding_Term.Assume (_173_1564))
in (_173_1565)::[]))))))))))
in (

let mk_range_interp = (fun env range tt -> (

let range_ty = (FStar_SMTEncoding_Term.mkApp (range, []))
in (let _173_1576 = (let _173_1575 = (let _173_1574 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_ty)
in (let _173_1573 = (let _173_1572 = (varops.fresh "typing_range_const")
in Some (_173_1572))
in (_173_1574, Some ("Range_const typing"), _173_1573)))
in FStar_SMTEncoding_Term.Assume (_173_1575))
in (_173_1576)::[])))
in (

let prims = ((FStar_Syntax_Const.unit_lid, mk_unit))::((FStar_Syntax_Const.bool_lid, mk_bool))::((FStar_Syntax_Const.int_lid, mk_int))::((FStar_Syntax_Const.string_lid, mk_str))::((FStar_Syntax_Const.ref_lid, mk_ref))::((FStar_Syntax_Const.false_lid, mk_false_interp))::((FStar_Syntax_Const.and_lid, mk_and_interp))::((FStar_Syntax_Const.or_lid, mk_or_interp))::((FStar_Syntax_Const.eq2_lid, mk_eq2_interp))::((FStar_Syntax_Const.eq3_lid, mk_eq3_interp))::((FStar_Syntax_Const.imp_lid, mk_imp_interp))::((FStar_Syntax_Const.iff_lid, mk_iff_interp))::((FStar_Syntax_Const.forall_lid, mk_forall_interp))::((FStar_Syntax_Const.exists_lid, mk_exists_interp))::((FStar_Syntax_Const.range_lid, mk_range_interp))::[]
in (fun env t s tt -> (match ((FStar_Util.find_opt (fun _83_1955 -> (match (_83_1955) with
| (l, _83_1954) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_83_1958, f) -> begin
(f env s tt)
end))))))))))))))))))))))


let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let _83_1964 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _173_1779 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _173_1779))
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

let _83_1972 = (encode_sigelt' env se)
in (match (_83_1972) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _173_1782 = (let _173_1781 = (let _173_1780 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (_173_1780))
in (_173_1781)::[])
in (_173_1782, e))
end
| _83_1975 -> begin
(let _173_1789 = (let _173_1788 = (let _173_1784 = (let _173_1783 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_173_1783))
in (_173_1784)::g)
in (let _173_1787 = (let _173_1786 = (let _173_1785 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_173_1785))
in (_173_1786)::[])
in (FStar_List.append _173_1788 _173_1787)))
in (_173_1789, e))
end)
end)))))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let should_skip = (fun l -> false)
in (

let encode_top_level_val = (fun env lid t quals -> (

let tt = (norm env t)
in (

let _83_1988 = (encode_free_var env lid t tt quals)
in (match (_83_1988) with
| (decls, env) -> begin
if (FStar_Syntax_Util.is_smt_lemma t) then begin
(let _173_1803 = (let _173_1802 = (encode_smt_lemma env lid tt)
in (FStar_List.append decls _173_1802))
in (_173_1803, env))
end else begin
(decls, env)
end
end))))
in (

let encode_top_level_vals = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _83_1995 lb -> (match (_83_1995) with
| (decls, env) -> begin
(

let _83_1999 = (let _173_1812 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env _173_1812 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (_83_1999) with
| (decls', env) -> begin
((FStar_List.append decls decls'), env)
end))
end)) ([], env))))
in (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_83_2001) -> begin
(FStar_All.failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _83_2020, _83_2022, _83_2024, _83_2026) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid) -> begin
(

let _83_2032 = (new_term_constant_and_tok_from_lid env lid)
in (match (_83_2032) with
| (tname, ttok, env) -> begin
([], env)
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _83_2035, t, quals, _83_2039) -> begin
(

let will_encode_definition = (not ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _83_13 -> (match (_83_13) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Irreducible) -> begin
true
end
| _83_2052 -> begin
false
end))))))
in if will_encode_definition then begin
([], env)
end else begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (

let _83_2057 = (encode_top_level_val env fv t quals)
in (match (_83_2057) with
| (decls, env) -> begin
(

let tname = lid.FStar_Ident.str
in (

let tsym = (FStar_SMTEncoding_Term.mkFreeV (tname, FStar_SMTEncoding_Term.Term_sort))
in (let _173_1815 = (let _173_1814 = (primitive_type_axioms env.tcenv lid tname tsym)
in (FStar_List.append decls _173_1814))
in (_173_1815, env))))
end)))
end)
end
| FStar_Syntax_Syntax.Sig_assume (l, f, _83_2063, _83_2065) -> begin
(

let _83_2070 = (encode_formula f env)
in (match (_83_2070) with
| (f, decls) -> begin
(

let g = (let _173_1822 = (let _173_1821 = (let _173_1820 = (let _173_1817 = (let _173_1816 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" _173_1816))
in Some (_173_1817))
in (let _173_1819 = (let _173_1818 = (varops.fresh (Prims.strcat "assumption_" l.FStar_Ident.str))
in Some (_173_1818))
in (f, _173_1820, _173_1819)))
in FStar_SMTEncoding_Term.Assume (_173_1821))
in (_173_1822)::[])
in ((FStar_List.append decls g), env))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _83_2075, quals) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) -> begin
(

let _83_2088 = (FStar_Util.fold_map (fun env lb -> (

let lid = (let _173_1826 = (let _173_1825 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _173_1825.FStar_Syntax_Syntax.fv_name)
in _173_1826.FStar_Syntax_Syntax.v)
in if (let _173_1827 = (FStar_TypeChecker_Env.try_lookup_val_decl env.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone _173_1827)) then begin
(

let val_decl = FStar_Syntax_Syntax.Sig_declare_typ ((lid, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, quals, r))
in (

let _83_2085 = (encode_sigelt' env val_decl)
in (match (_83_2085) with
| (decls, env) -> begin
(env, decls)
end)))
end else begin
(env, [])
end)) env (Prims.snd lbs))
in (match (_83_2088) with
| (env, decls) -> begin
((FStar_List.flatten decls), env)
end))
end
| FStar_Syntax_Syntax.Sig_let ((_83_2090, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t); FStar_Syntax_Syntax.lbunivs = _83_2098; FStar_Syntax_Syntax.lbtyp = _83_2096; FStar_Syntax_Syntax.lbeff = _83_2094; FStar_Syntax_Syntax.lbdef = _83_2092})::[]), _83_2105, _83_2107, _83_2109) when (FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Syntax_Const.b2t_lid) -> begin
(

let _83_2115 = (new_term_constant_and_tok_from_lid env b2t.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_83_2115) with
| (tname, ttok, env) -> begin
(

let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (

let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (

let valid_b2t_x = (let _173_1830 = (let _173_1829 = (let _173_1828 = (FStar_SMTEncoding_Term.mkApp ("Prims.b2t", (x)::[]))
in (_173_1828)::[])
in ("Valid", _173_1829))
in (FStar_SMTEncoding_Term.mkApp _173_1830))
in (

let decls = (let _173_1838 = (let _173_1837 = (let _173_1836 = (let _173_1835 = (let _173_1834 = (let _173_1833 = (let _173_1832 = (let _173_1831 = (FStar_SMTEncoding_Term.mkApp ("BoxBool_proj_0", (x)::[]))
in (valid_b2t_x, _173_1831))
in (FStar_SMTEncoding_Term.mkEq _173_1832))
in (((valid_b2t_x)::[])::[], (xx)::[], _173_1833))
in (FStar_SMTEncoding_Term.mkForall _173_1834))
in (_173_1835, Some ("b2t def"), Some ("b2t_def")))
in FStar_SMTEncoding_Term.Assume (_173_1836))
in (_173_1837)::[])
in (FStar_SMTEncoding_Term.DeclFun ((tname, (FStar_SMTEncoding_Term.Term_sort)::[], FStar_SMTEncoding_Term.Term_sort, None)))::_173_1838)
in (decls, env)))))
end))
end
| FStar_Syntax_Syntax.Sig_let (_83_2121, _83_2123, _83_2125, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _83_14 -> (match (_83_14) with
| (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _83_2135 -> begin
false
end)))) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _83_2141, _83_2143, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _83_15 -> (match (_83_15) with
| FStar_Syntax_Syntax.Projector (_83_2149) -> begin
true
end
| _83_2152 -> begin
false
end)))) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((try_lookup_free_var env l)) with
| Some (_83_2156) -> begin
([], env)
end
| None -> begin
(

let se = FStar_Syntax_Syntax.Sig_declare_typ ((l, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, quals, (FStar_Ident.range_of_lid l)))
in (encode_sigelt env se))
end)))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), _83_2164, _83_2166, quals) -> begin
(

let eta_expand = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let _83_2178 = (FStar_Util.first_N nbinders formals)
in (match (_83_2178) with
| (formals, extra_formals) -> begin
(

let subst = (FStar_List.map2 (fun _83_2182 _83_2186 -> (match ((_83_2182, _83_2186)) with
| ((formal, _83_2181), (binder, _83_2185)) -> begin
(let _173_1852 = (let _173_1851 = (FStar_Syntax_Syntax.bv_to_name binder)
in (formal, _173_1851))
in FStar_Syntax_Syntax.NT (_173_1852))
end)) formals binders)
in (

let extra_formals = (let _173_1856 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun _83_2190 -> (match (_83_2190) with
| (x, i) -> begin
(let _173_1855 = (

let _83_2191 = x
in (let _173_1854 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _83_2191.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _83_2191.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _173_1854}))
in (_173_1855, i))
end))))
in (FStar_All.pipe_right _173_1856 FStar_Syntax_Util.name_binders))
in (

let body = (let _173_1863 = (FStar_Syntax_Subst.compress body)
in (let _173_1862 = (let _173_1857 = (FStar_Syntax_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _173_1857))
in (let _173_1861 = (let _173_1860 = (let _173_1859 = (FStar_Syntax_Subst.subst subst t)
in _173_1859.FStar_Syntax_Syntax.n)
in (FStar_All.pipe_left (fun _173_1858 -> Some (_173_1858)) _173_1860))
in (FStar_Syntax_Syntax.extend_app_n _173_1863 _173_1862 _173_1861 body.FStar_Syntax_Syntax.pos))))
in ((FStar_List.append binders extra_formals), body))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (

let rec aux = (fun norm t_norm -> (match ((let _173_1874 = (FStar_Syntax_Util.unascribe e)
in _173_1874.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, lopt) -> begin
(

let _83_2210 = (FStar_Syntax_Subst.open_term' binders body)
in (match (_83_2210) with
| (binders, body, opening) -> begin
(match ((let _173_1875 = (FStar_Syntax_Subst.compress t_norm)
in _173_1875.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let _83_2217 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_83_2217) with
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

let _83_2224 = (FStar_Util.first_N nformals binders)
in (match (_83_2224) with
| (bs0, rest) -> begin
(

let c = (

let subst = (FStar_List.map2 (fun _83_2228 _83_2232 -> (match ((_83_2228, _83_2232)) with
| ((b, _83_2227), (x, _83_2231)) -> begin
(let _173_1879 = (let _173_1878 = (FStar_Syntax_Syntax.bv_to_name x)
in (b, _173_1878))
in FStar_Syntax_Syntax.NT (_173_1879))
end)) bs0 formals)
in (FStar_Syntax_Subst.subst_comp subst c))
in (

let body = (FStar_Syntax_Util.abs rest body lopt)
in (bs0, body, bs0, (FStar_Syntax_Util.comp_result c))))
end)))
end else begin
if (nformals > nbinders) then begin
(

let _83_2238 = (eta_expand binders formals body tres)
in (match (_83_2238) with
| (binders, body) -> begin
(binders, body, formals, tres)
end))
end else begin
(binders, body, formals, tres)
end
end)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, _83_2241) -> begin
(aux true x.FStar_Syntax_Syntax.sort)
end
| _83_2245 when (not (norm)) -> begin
(

let t_norm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm)
in (aux true t_norm))
end
| _83_2248 -> begin
(let _173_1882 = (let _173_1881 = (FStar_Syntax_Print.term_to_string e)
in (let _173_1880 = (FStar_Syntax_Print.term_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str _173_1881 _173_1880)))
in (FStar_All.failwith _173_1882))
end)
end))
end
| _83_2250 -> begin
(match ((let _173_1883 = (FStar_Syntax_Subst.compress t_norm)
in _173_1883.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let _83_2257 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_83_2257) with
| (formals, c) -> begin
(

let tres = (FStar_Syntax_Util.comp_result c)
in (

let _83_2261 = (eta_expand [] formals e tres)
in (match (_83_2261) with
| (binders, body) -> begin
(binders, body, formals, tres)
end)))
end))
end
| _83_2263 -> begin
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

let _83_2291 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _83_2278 lb -> (match (_83_2278) with
| (toks, typs, decls, env) -> begin
(

let _83_2280 = if (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) then begin
(Prims.raise Let_rec_unencodeable)
end else begin
()
end
in (

let t_norm = (whnf env lb.FStar_Syntax_Syntax.lbtyp)
in (

let _83_2286 = (let _173_1888 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env _173_1888 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (_83_2286) with
| (tok, decl, env) -> begin
(let _173_1891 = (let _173_1890 = (let _173_1889 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (_173_1889, tok))
in (_173_1890)::toks)
in (_173_1891, (t_norm)::typs, (decl)::decls, env))
end))))
end)) ([], [], [], env)))
in (match (_83_2291) with
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
| _83_2298 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> (let _173_1894 = (FStar_Syntax_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _173_1894)))))) then begin
(decls, env)
end else begin
if (not (is_rec)) then begin
(match ((bindings, typs, toks)) with
| (({FStar_Syntax_Syntax.lbname = _83_2308; FStar_Syntax_Syntax.lbunivs = _83_2306; FStar_Syntax_Syntax.lbtyp = _83_2304; FStar_Syntax_Syntax.lbeff = _83_2302; FStar_Syntax_Syntax.lbdef = e})::[], (t_norm)::[], ((flid_fv, (f, ftok)))::[]) -> begin
(

let e = (FStar_Syntax_Subst.compress e)
in (

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let _83_2328 = (destruct_bound_function flid t_norm e)
in (match (_83_2328) with
| (binders, body, _83_2325, _83_2327) -> begin
(

let _83_2335 = (encode_binders None binders env)
in (match (_83_2335) with
| (vars, guards, env', binder_decls, _83_2334) -> begin
(

let app = (match (vars) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV (f, FStar_SMTEncoding_Term.Term_sort))
end
| _83_2338 -> begin
(let _173_1896 = (let _173_1895 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (f, _173_1895))
in (FStar_SMTEncoding_Term.mkApp _173_1896))
end)
in (

let _83_2344 = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic)) then begin
(let _173_1898 = (FStar_SMTEncoding_Term.mk_Valid app)
in (let _173_1897 = (encode_formula body env')
in (_173_1898, _173_1897)))
end else begin
(let _173_1899 = (encode_term body env')
in (app, _173_1899))
end
in (match (_83_2344) with
| (app, (body, decls2)) -> begin
(

let eqn = (let _173_1905 = (let _173_1904 = (let _173_1901 = (let _173_1900 = (FStar_SMTEncoding_Term.mkEq (app, body))
in (((app)::[])::[], vars, _173_1900))
in (FStar_SMTEncoding_Term.mkForall _173_1901))
in (let _173_1903 = (let _173_1902 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (_173_1902))
in (_173_1904, _173_1903, Some ((Prims.strcat "equation_" f)))))
in FStar_SMTEncoding_Term.Assume (_173_1905))
in (let _173_1907 = (let _173_1906 = (primitive_type_axioms env.tcenv flid f app)
in (FStar_List.append (FStar_List.append (FStar_List.append (FStar_List.append decls binder_decls) decls2) ((eqn)::[])) _173_1906))
in (_173_1907, env)))
end)))
end))
end))))
end
| _83_2347 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(

let fuel = (let _173_1908 = (varops.fresh "fuel")
in (_173_1908, FStar_SMTEncoding_Term.Fuel_sort))
in (

let fuel_tm = (FStar_SMTEncoding_Term.mkFreeV fuel)
in (

let env0 = env
in (

let _83_2365 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _83_2353 _83_2358 -> (match ((_83_2353, _83_2358)) with
| ((gtoks, env), (flid_fv, (f, ftok))) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let g = (varops.new_fvar flid)
in (

let gtok = (varops.new_fvar flid)
in (

let env = (let _173_1913 = (let _173_1912 = (FStar_SMTEncoding_Term.mkApp (g, (fuel_tm)::[]))
in (FStar_All.pipe_left (fun _173_1911 -> Some (_173_1911)) _173_1912))
in (push_free_var env flid gtok _173_1913))
in (((flid, f, ftok, g, gtok))::gtoks, env)))))
end)) ([], env)))
in (match (_83_2365) with
| (gtoks, env) -> begin
(

let gtoks = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env0 _83_2374 t_norm _83_2385 -> (match ((_83_2374, _83_2385)) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = _83_2384; FStar_Syntax_Syntax.lbunivs = _83_2382; FStar_Syntax_Syntax.lbtyp = _83_2380; FStar_Syntax_Syntax.lbeff = _83_2378; FStar_Syntax_Syntax.lbdef = e}) -> begin
(

let _83_2390 = (destruct_bound_function flid t_norm e)
in (match (_83_2390) with
| (binders, body, formals, tres) -> begin
(

let _83_2397 = (encode_binders None binders env)
in (match (_83_2397) with
| (vars, guards, env', binder_decls, _83_2396) -> begin
(

let decl_g = (let _173_1924 = (let _173_1923 = (let _173_1922 = (FStar_List.map Prims.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::_173_1922)
in (g, _173_1923, FStar_SMTEncoding_Term.Term_sort, Some ("Fuel-instrumented function name")))
in FStar_SMTEncoding_Term.DeclFun (_173_1924))
in (

let env0 = (push_zfuel_name env0 flid g)
in (

let decl_g_tok = FStar_SMTEncoding_Term.DeclFun ((gtok, [], FStar_SMTEncoding_Term.Term_sort, Some ("Token for fuel-instrumented partial applications")))
in (

let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (

let app = (FStar_SMTEncoding_Term.mkApp (f, vars_tm))
in (

let gsapp = (let _173_1927 = (let _173_1926 = (let _173_1925 = (FStar_SMTEncoding_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (_173_1925)::vars_tm)
in (g, _173_1926))
in (FStar_SMTEncoding_Term.mkApp _173_1927))
in (

let gmax = (let _173_1930 = (let _173_1929 = (let _173_1928 = (FStar_SMTEncoding_Term.mkApp ("MaxFuel", []))
in (_173_1928)::vars_tm)
in (g, _173_1929))
in (FStar_SMTEncoding_Term.mkApp _173_1930))
in (

let _83_2407 = (encode_term body env')
in (match (_83_2407) with
| (body_tm, decls2) -> begin
(

let eqn_g = (let _173_1936 = (let _173_1935 = (let _173_1932 = (let _173_1931 = (FStar_SMTEncoding_Term.mkEq (gsapp, body_tm))
in (((gsapp)::[])::[], (fuel)::vars, _173_1931))
in (FStar_SMTEncoding_Term.mkForall _173_1932))
in (let _173_1934 = (let _173_1933 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (_173_1933))
in (_173_1935, _173_1934, Some ((Prims.strcat "equation_with_fuel_" g)))))
in FStar_SMTEncoding_Term.Assume (_173_1936))
in (

let eqn_f = (let _173_1940 = (let _173_1939 = (let _173_1938 = (let _173_1937 = (FStar_SMTEncoding_Term.mkEq (app, gmax))
in (((app)::[])::[], vars, _173_1937))
in (FStar_SMTEncoding_Term.mkForall _173_1938))
in (_173_1939, Some ("Correspondence of recursive function to instrumented version"), Some ((Prims.strcat "fuel_correspondence_" g))))
in FStar_SMTEncoding_Term.Assume (_173_1940))
in (

let eqn_g' = (let _173_1949 = (let _173_1948 = (let _173_1947 = (let _173_1946 = (let _173_1945 = (let _173_1944 = (let _173_1943 = (let _173_1942 = (let _173_1941 = (FStar_SMTEncoding_Term.n_fuel 0)
in (_173_1941)::vars_tm)
in (g, _173_1942))
in (FStar_SMTEncoding_Term.mkApp _173_1943))
in (gsapp, _173_1944))
in (FStar_SMTEncoding_Term.mkEq _173_1945))
in (((gsapp)::[])::[], (fuel)::vars, _173_1946))
in (FStar_SMTEncoding_Term.mkForall _173_1947))
in (_173_1948, Some ("Fuel irrelevance"), Some ((Prims.strcat "fuel_irrelevance_" g))))
in FStar_SMTEncoding_Term.Assume (_173_1949))
in (

let _83_2430 = (

let _83_2417 = (encode_binders None formals env0)
in (match (_83_2417) with
| (vars, v_guards, env, binder_decls, _83_2416) -> begin
(

let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (

let gapp = (FStar_SMTEncoding_Term.mkApp (g, (fuel_tm)::vars_tm))
in (

let tok_corr = (

let tok_app = (let _173_1950 = (FStar_SMTEncoding_Term.mkFreeV (gtok, FStar_SMTEncoding_Term.Term_sort))
in (mk_Apply _173_1950 ((fuel)::vars)))
in (let _173_1954 = (let _173_1953 = (let _173_1952 = (let _173_1951 = (FStar_SMTEncoding_Term.mkEq (tok_app, gapp))
in (((tok_app)::[])::[], (fuel)::vars, _173_1951))
in (FStar_SMTEncoding_Term.mkForall _173_1952))
in (_173_1953, Some ("Fuel token correspondence"), Some ((Prims.strcat "fuel_tokem_correspondence_" gtok))))
in FStar_SMTEncoding_Term.Assume (_173_1954)))
in (

let _83_2427 = (

let _83_2424 = (encode_term_pred None tres env gapp)
in (match (_83_2424) with
| (g_typing, d3) -> begin
(let _173_1962 = (let _173_1961 = (let _173_1960 = (let _173_1959 = (let _173_1958 = (let _173_1957 = (let _173_1956 = (let _173_1955 = (FStar_SMTEncoding_Term.mk_and_l v_guards)
in (_173_1955, g_typing))
in (FStar_SMTEncoding_Term.mkImp _173_1956))
in (((gapp)::[])::[], (fuel)::vars, _173_1957))
in (FStar_SMTEncoding_Term.mkForall _173_1958))
in (_173_1959, Some ("Typing correspondence of token to term"), Some ((Prims.strcat "token_correspondence_" g))))
in FStar_SMTEncoding_Term.Assume (_173_1960))
in (_173_1961)::[])
in (d3, _173_1962))
end))
in (match (_83_2427) with
| (aux_decls, typing_corr) -> begin
((FStar_List.append binder_decls aux_decls), (FStar_List.append typing_corr ((tok_corr)::[])))
end)))))
end))
in (match (_83_2430) with
| (aux_decls, g_typing) -> begin
((FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) aux_decls) ((decl_g)::(decl_g_tok)::[])), (FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing), env0)
end)))))
end)))))))))
end))
end))
end))
in (

let _83_2446 = (let _173_1965 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _83_2434 _83_2438 -> (match ((_83_2434, _83_2438)) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(

let _83_2442 = (encode_one_binding env0 gtok ty bs)
in (match (_83_2442) with
| (decls', eqns', env0) -> begin
((decls')::decls, (FStar_List.append eqns' eqns), env0)
end))
end)) ((decls)::[], [], env0) _173_1965))
in (match (_83_2446) with
| (decls, eqns, env0) -> begin
(

let _83_2455 = (let _173_1967 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _173_1967 (FStar_List.partition (fun _83_17 -> (match (_83_17) with
| FStar_SMTEncoding_Term.DeclFun (_83_2449) -> begin
true
end
| _83_2452 -> begin
false
end)))))
in (match (_83_2455) with
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

let msg = (let _173_1970 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _173_1970 (FStar_String.concat " and ")))
in (

let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in ((decl)::[], env)))
end))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _83_2459, _83_2461, _83_2463) -> begin
(

let _83_2468 = (encode_signature env ses)
in (match (_83_2468) with
| (g, env) -> begin
(

let _83_2482 = (FStar_All.pipe_right g (FStar_List.partition (fun _83_18 -> (match (_83_18) with
| FStar_SMTEncoding_Term.Assume (_83_2471, Some ("inversion axiom"), _83_2475) -> begin
false
end
| _83_2479 -> begin
true
end))))
in (match (_83_2482) with
| (g', inversions) -> begin
(

let _83_2491 = (FStar_All.pipe_right g' (FStar_List.partition (fun _83_19 -> (match (_83_19) with
| FStar_SMTEncoding_Term.DeclFun (_83_2485) -> begin
true
end
| _83_2488 -> begin
false
end))))
in (match (_83_2491) with
| (decls, rest) -> begin
((FStar_List.append (FStar_List.append decls rest) inversions), env)
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, _83_2494, tps, k, _83_2498, datas, quals, _83_2502) -> begin
(

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _83_20 -> (match (_83_20) with
| (FStar_Syntax_Syntax.Logic) | (FStar_Syntax_Syntax.Assumption) -> begin
true
end
| _83_2509 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(

let _83_2521 = c
in (match (_83_2521) with
| (name, args, _83_2516, _83_2518, _83_2520) -> begin
(let _173_1978 = (let _173_1977 = (let _173_1976 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in (name, _173_1976, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_173_1977))
in (_173_1978)::[])
end))
end else begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end)
in (

let inversion_axioms = (fun tapp vars -> if (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _173_1984 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right _173_1984 FStar_Option.isNone))))) then begin
[]
end else begin
(

let _83_2528 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_83_2528) with
| (xxsym, xx) -> begin
(

let _83_2564 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _83_2531 l -> (match (_83_2531) with
| (out, decls) -> begin
(

let _83_2536 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (_83_2536) with
| (_83_2534, data_t) -> begin
(

let _83_2539 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (_83_2539) with
| (args, res) -> begin
(

let indices = (match ((let _173_1987 = (FStar_Syntax_Subst.compress res)
in _173_1987.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_83_2541, indices) -> begin
indices
end
| _83_2546 -> begin
[]
end)
in (

let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env _83_2552 -> (match (_83_2552) with
| (x, _83_2551) -> begin
(let _173_1992 = (let _173_1991 = (let _173_1990 = (mk_term_projector_name l x)
in (_173_1990, (xx)::[]))
in (FStar_SMTEncoding_Term.mkApp _173_1991))
in (push_term_var env x _173_1992))
end)) env))
in (

let _83_2556 = (encode_args indices env)
in (match (_83_2556) with
| (indices, decls') -> begin
(

let _83_2557 = if ((FStar_List.length indices) <> (FStar_List.length vars)) then begin
(FStar_All.failwith "Impossible")
end else begin
()
end
in (

let eqs = (let _173_1997 = (FStar_List.map2 (fun v a -> (let _173_1996 = (let _173_1995 = (FStar_SMTEncoding_Term.mkFreeV v)
in (_173_1995, a))
in (FStar_SMTEncoding_Term.mkEq _173_1996))) vars indices)
in (FStar_All.pipe_right _173_1997 FStar_SMTEncoding_Term.mk_and_l))
in (let _173_2002 = (let _173_2001 = (let _173_2000 = (let _173_1999 = (let _173_1998 = (mk_data_tester env l xx)
in (_173_1998, eqs))
in (FStar_SMTEncoding_Term.mkAnd _173_1999))
in (out, _173_2000))
in (FStar_SMTEncoding_Term.mkOr _173_2001))
in (_173_2002, (FStar_List.append decls decls')))))
end))))
end))
end))
end)) (FStar_SMTEncoding_Term.mkFalse, [])))
in (match (_83_2564) with
| (data_ax, decls) -> begin
(

let _83_2567 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_83_2567) with
| (ffsym, ff) -> begin
(

let fuel_guarded_inversion = (

let xx_has_type_sfuel = if ((FStar_List.length datas) > 1) then begin
(let _173_2003 = (FStar_SMTEncoding_Term.mkApp ("SFuel", (ff)::[]))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel _173_2003 xx tapp))
end else begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end
in (let _173_2010 = (let _173_2009 = (let _173_2006 = (let _173_2005 = (add_fuel (ffsym, FStar_SMTEncoding_Term.Fuel_sort) (((xxsym, FStar_SMTEncoding_Term.Term_sort))::vars))
in (let _173_2004 = (FStar_SMTEncoding_Term.mkImp (xx_has_type_sfuel, data_ax))
in (((xx_has_type_sfuel)::[])::[], _173_2005, _173_2004)))
in (FStar_SMTEncoding_Term.mkForall _173_2006))
in (let _173_2008 = (let _173_2007 = (varops.fresh (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str))
in Some (_173_2007))
in (_173_2009, Some ("inversion axiom"), _173_2008)))
in FStar_SMTEncoding_Term.Assume (_173_2010)))
in (

let pattern_guarded_inversion = if ((contains_name env "Prims.inversion") && ((FStar_List.length datas) > 1)) then begin
(

let xx_has_type_fuel = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let pattern_guard = (FStar_SMTEncoding_Term.mkApp ("Prims.inversion", (tapp)::[]))
in (let _173_2018 = (let _173_2017 = (let _173_2016 = (let _173_2013 = (let _173_2012 = (add_fuel (ffsym, FStar_SMTEncoding_Term.Fuel_sort) (((xxsym, FStar_SMTEncoding_Term.Term_sort))::vars))
in (let _173_2011 = (FStar_SMTEncoding_Term.mkImp (xx_has_type_fuel, data_ax))
in (((xx_has_type_fuel)::(pattern_guard)::[])::[], _173_2012, _173_2011)))
in (FStar_SMTEncoding_Term.mkForall _173_2013))
in (let _173_2015 = (let _173_2014 = (varops.fresh (Prims.strcat "pattern_guarded_inversion_" t.FStar_Ident.str))
in Some (_173_2014))
in (_173_2016, Some ("inversion axiom"), _173_2015)))
in FStar_SMTEncoding_Term.Assume (_173_2017))
in (_173_2018)::[])))
end else begin
[]
end
in (FStar_List.append (FStar_List.append decls ((fuel_guarded_inversion)::[])) pattern_guarded_inversion)))
end))
end))
end))
end)
in (

let _83_2581 = (match ((let _173_2019 = (FStar_Syntax_Subst.compress k)
in _173_2019.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
((FStar_List.append tps formals), (FStar_Syntax_Util.comp_result kres))
end
| _83_2578 -> begin
(tps, k)
end)
in (match (_83_2581) with
| (formals, res) -> begin
(

let _83_2584 = (FStar_Syntax_Subst.open_term formals res)
in (match (_83_2584) with
| (formals, res) -> begin
(

let _83_2591 = (encode_binders None formals env)
in (match (_83_2591) with
| (vars, guards, env', binder_decls, _83_2590) -> begin
(

let _83_2595 = (new_term_constant_and_tok_from_lid env t)
in (match (_83_2595) with
| (tname, ttok, env) -> begin
(

let ttok_tm = (FStar_SMTEncoding_Term.mkApp (ttok, []))
in (

let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (

let tapp = (let _173_2021 = (let _173_2020 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (tname, _173_2020))
in (FStar_SMTEncoding_Term.mkApp _173_2021))
in (

let _83_2616 = (

let tname_decl = (let _173_2025 = (let _173_2024 = (FStar_All.pipe_right vars (FStar_List.map (fun _83_2601 -> (match (_83_2601) with
| (n, s) -> begin
((Prims.strcat tname n), s)
end))))
in (let _173_2023 = (varops.next_id ())
in (tname, _173_2024, FStar_SMTEncoding_Term.Term_sort, _173_2023, false)))
in (constructor_or_logic_type_decl _173_2025))
in (

let _83_2613 = (match (vars) with
| [] -> begin
(let _173_2029 = (let _173_2028 = (let _173_2027 = (FStar_SMTEncoding_Term.mkApp (tname, []))
in (FStar_All.pipe_left (fun _173_2026 -> Some (_173_2026)) _173_2027))
in (push_free_var env t tname _173_2028))
in ([], _173_2029))
end
| _83_2605 -> begin
(

let ttok_decl = FStar_SMTEncoding_Term.DeclFun ((ttok, [], FStar_SMTEncoding_Term.Term_sort, Some ("token")))
in (

let ttok_fresh = (let _173_2030 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (ttok, FStar_SMTEncoding_Term.Term_sort) _173_2030))
in (

let ttok_app = (mk_Apply ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (let _173_2034 = (let _173_2033 = (let _173_2032 = (let _173_2031 = (FStar_SMTEncoding_Term.mkEq (ttok_app, tapp))
in (pats, None, vars, _173_2031))
in (FStar_SMTEncoding_Term.mkForall' _173_2032))
in (_173_2033, Some ("name-token correspondence"), Some ((Prims.strcat "token_correspondence_" ttok))))
in FStar_SMTEncoding_Term.Assume (_173_2034))
in ((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[], env))))))
end)
in (match (_83_2613) with
| (tok_decls, env) -> begin
((FStar_List.append tname_decl tok_decls), env)
end)))
in (match (_83_2616) with
| (decls, env) -> begin
(

let kindingAx = (

let _83_2619 = (encode_term_pred None res env' tapp)
in (match (_83_2619) with
| (k, decls) -> begin
(

let karr = if ((FStar_List.length formals) > 0) then begin
(let _173_2038 = (let _173_2037 = (let _173_2036 = (let _173_2035 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _173_2035))
in (_173_2036, Some ("kinding"), Some ((Prims.strcat "pre_kinding_" ttok))))
in FStar_SMTEncoding_Term.Assume (_173_2037))
in (_173_2038)::[])
end else begin
[]
end
in (let _173_2044 = (let _173_2043 = (let _173_2042 = (let _173_2041 = (let _173_2040 = (let _173_2039 = (FStar_SMTEncoding_Term.mkImp (guard, k))
in (((tapp)::[])::[], vars, _173_2039))
in (FStar_SMTEncoding_Term.mkForall _173_2040))
in (_173_2041, None, Some ((Prims.strcat "kinding_" ttok))))
in FStar_SMTEncoding_Term.Assume (_173_2042))
in (_173_2043)::[])
in (FStar_List.append (FStar_List.append decls karr) _173_2044)))
end))
in (

let aux = (let _173_2048 = (let _173_2045 = (inversion_axioms tapp vars)
in (FStar_List.append kindingAx _173_2045))
in (let _173_2047 = (let _173_2046 = (pretype_axiom tapp vars)
in (_173_2046)::[])
in (FStar_List.append _173_2048 _173_2047)))
in (

let g = (FStar_List.append (FStar_List.append decls binder_decls) aux)
in (g, env))))
end)))))
end))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, _83_2626, _83_2628, _83_2630, _83_2632, _83_2634, _83_2636, _83_2638) when (FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_datacon (d, _83_2643, t, _83_2646, n_tps, quals, _83_2650, drange) -> begin
(

let _83_2657 = (new_term_constant_and_tok_from_lid env d)
in (match (_83_2657) with
| (ddconstrsym, ddtok, env) -> begin
(

let ddtok_tm = (FStar_SMTEncoding_Term.mkApp (ddtok, []))
in (

let _83_2661 = (FStar_Syntax_Util.arrow_formals t)
in (match (_83_2661) with
| (formals, t_res) -> begin
(

let _83_2664 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_83_2664) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_SMTEncoding_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (

let _83_2671 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_83_2671) with
| (vars, guards, env', binder_decls, names) -> begin
(

let projectors = (FStar_All.pipe_right names (FStar_List.map (fun x -> (let _173_2050 = (mk_term_projector_name d x)
in (_173_2050, FStar_SMTEncoding_Term.Term_sort)))))
in (

let datacons = (let _173_2052 = (let _173_2051 = (varops.next_id ())
in (ddconstrsym, projectors, FStar_SMTEncoding_Term.Term_sort, _173_2051, true))
in (FStar_All.pipe_right _173_2052 FStar_SMTEncoding_Term.constructor_to_decl))
in (

let app = (mk_Apply ddtok_tm vars)
in (

let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (

let _83_2681 = (encode_term_pred None t env ddtok_tm)
in (match (_83_2681) with
| (tok_typing, decls3) -> begin
(

let _83_2688 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_83_2688) with
| (vars', guards', env'', decls_formals, _83_2687) -> begin
(

let _83_2693 = (

let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars')
in (

let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (encode_term_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_83_2693) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_SMTEncoding_Term.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _83_2697 -> begin
(let _173_2054 = (let _173_2053 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (ddtok, FStar_SMTEncoding_Term.Term_sort) _173_2053))
in (_173_2054)::[])
end)
in (

let encode_elim = (fun _83_2700 -> (match (()) with
| () -> begin
(

let _83_2703 = (FStar_Syntax_Util.head_and_args t_res)
in (match (_83_2703) with
| (head, args) -> begin
(match ((let _173_2057 = (FStar_Syntax_Subst.compress head)
in _173_2057.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let _83_2721 = (encode_args args env')
in (match (_83_2721) with
| (encoded_args, arg_decls) -> begin
(

let _83_2736 = (FStar_List.fold_left (fun _83_2725 arg -> (match (_83_2725) with
| (env, arg_vars, eqns) -> begin
(

let _83_2731 = (let _173_2060 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in (gen_term_var env _173_2060))
in (match (_83_2731) with
| (_83_2728, xv, env) -> begin
(let _173_2062 = (let _173_2061 = (FStar_SMTEncoding_Term.mkEq (arg, xv))
in (_173_2061)::eqns)
in (env, (xv)::arg_vars, _173_2062))
end))
end)) (env', [], []) encoded_args)
in (match (_83_2736) with
| (_83_2733, arg_vars, eqns) -> begin
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

let typing_inversion = (let _173_2069 = (let _173_2068 = (let _173_2067 = (let _173_2066 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _173_2065 = (let _173_2064 = (let _173_2063 = (FStar_SMTEncoding_Term.mk_and_l (FStar_List.append eqns guards))
in (ty_pred, _173_2063))
in (FStar_SMTEncoding_Term.mkImp _173_2064))
in (((ty_pred)::[])::[], _173_2066, _173_2065)))
in (FStar_SMTEncoding_Term.mkForall _173_2067))
in (_173_2068, Some ("data constructor typing elim"), Some ((Prims.strcat "data_elim_" ddconstrsym))))
in FStar_SMTEncoding_Term.Assume (_173_2069))
in (

let subterm_ordering = if (FStar_Ident.lid_equals d FStar_Syntax_Const.lextop_lid) then begin
(

let x = (let _173_2070 = (varops.fresh "x")
in (_173_2070, FStar_SMTEncoding_Term.Term_sort))
in (

let xtm = (FStar_SMTEncoding_Term.mkFreeV x)
in (let _173_2082 = (let _173_2081 = (let _173_2078 = (let _173_2077 = (let _173_2072 = (let _173_2071 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in (_173_2071)::[])
in (_173_2072)::[])
in (let _173_2076 = (let _173_2075 = (let _173_2074 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (let _173_2073 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in (_173_2074, _173_2073)))
in (FStar_SMTEncoding_Term.mkImp _173_2075))
in (_173_2077, (x)::[], _173_2076)))
in (FStar_SMTEncoding_Term.mkForall _173_2078))
in (let _173_2080 = (let _173_2079 = (varops.fresh "lextop")
in Some (_173_2079))
in (_173_2081, Some ("lextop is top"), _173_2080)))
in FStar_SMTEncoding_Term.Assume (_173_2082))))
end else begin
(

let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
[]
end
| FStar_SMTEncoding_Term.Term_sort -> begin
(let _173_2085 = (let _173_2084 = (FStar_SMTEncoding_Term.mkFreeV v)
in (FStar_SMTEncoding_Term.mk_Precedes _173_2084 dapp))
in (_173_2085)::[])
end
| _83_2750 -> begin
(FStar_All.failwith "unexpected sort")
end))))
in (let _173_2092 = (let _173_2091 = (let _173_2090 = (let _173_2089 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _173_2088 = (let _173_2087 = (let _173_2086 = (FStar_SMTEncoding_Term.mk_and_l prec)
in (ty_pred, _173_2086))
in (FStar_SMTEncoding_Term.mkImp _173_2087))
in (((ty_pred)::[])::[], _173_2089, _173_2088)))
in (FStar_SMTEncoding_Term.mkForall _173_2090))
in (_173_2091, Some ("subterm ordering"), Some ((Prims.strcat "subterm_ordering_" ddconstrsym))))
in FStar_SMTEncoding_Term.Assume (_173_2092)))
end
in (arg_decls, (typing_inversion)::(subterm_ordering)::[])))))))))
end))
end)))
end
| _83_2754 -> begin
(

let _83_2755 = (let _173_2095 = (let _173_2094 = (FStar_Syntax_Print.lid_to_string d)
in (let _173_2093 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _173_2094 _173_2093)))
in (FStar_TypeChecker_Errors.warn drange _173_2095))
in ([], []))
end)
end))
end))
in (

let _83_2759 = (encode_elim ())
in (match (_83_2759) with
| (decls2, elim) -> begin
(

let g = (let _173_2120 = (let _173_2119 = (let _173_2104 = (let _173_2103 = (let _173_2102 = (let _173_2101 = (let _173_2100 = (let _173_2099 = (let _173_2098 = (let _173_2097 = (let _173_2096 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" _173_2096))
in Some (_173_2097))
in (ddtok, [], FStar_SMTEncoding_Term.Term_sort, _173_2098))
in FStar_SMTEncoding_Term.DeclFun (_173_2099))
in (_173_2100)::[])
in (FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) decls3) _173_2101))
in (FStar_List.append _173_2102 proxy_fresh))
in (FStar_List.append _173_2103 decls_formals))
in (FStar_List.append _173_2104 decls_pred))
in (let _173_2118 = (let _173_2117 = (let _173_2116 = (let _173_2108 = (let _173_2107 = (let _173_2106 = (let _173_2105 = (FStar_SMTEncoding_Term.mkEq (app, dapp))
in (((app)::[])::[], vars, _173_2105))
in (FStar_SMTEncoding_Term.mkForall _173_2106))
in (_173_2107, Some ("equality for proxy"), Some ((Prims.strcat "equality_tok_" ddtok))))
in FStar_SMTEncoding_Term.Assume (_173_2108))
in (let _173_2115 = (let _173_2114 = (let _173_2113 = (let _173_2112 = (let _173_2111 = (let _173_2110 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) vars')
in (let _173_2109 = (FStar_SMTEncoding_Term.mkImp (guard', ty_pred'))
in (((ty_pred')::[])::[], _173_2110, _173_2109)))
in (FStar_SMTEncoding_Term.mkForall _173_2111))
in (_173_2112, Some ("data constructor typing intro"), Some ((Prims.strcat "data_typing_intro_" ddtok))))
in FStar_SMTEncoding_Term.Assume (_173_2113))
in (_173_2114)::[])
in (_173_2116)::_173_2115))
in (FStar_SMTEncoding_Term.Assume ((tok_typing, Some ("typing for data constructor proxy"), Some ((Prims.strcat "typing_tok_" ddtok)))))::_173_2117)
in (FStar_List.append _173_2119 _173_2118)))
in (FStar_List.append _173_2120 elim))
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

let _83_2768 = (encode_free_var env x t t_norm [])
in (match (_83_2768) with
| (decls, env) -> begin
(

let _83_2773 = (lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_83_2773) with
| (n, x', _83_2772) -> begin
((n, x'), decls, env)
end))
end))
end
| Some (n, x, _83_2777) -> begin
((n, x), [], env)
end))
and encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let _83_2786 = (encode_function_type_as_formula None None t env)
in (match (_83_2786) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_SMTEncoding_Term.Assume ((form, Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str)), Some ((Prims.strcat "lemma_" lid.FStar_Ident.str)))))::[]))
end))))
and encode_free_var : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env fv tt t_norm quals -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if ((let _173_2133 = (FStar_Syntax_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _173_2133)) || (FStar_Syntax_Util.is_lemma t_norm)) then begin
(

let _83_2796 = (new_term_constant_and_tok_from_lid env lid)
in (match (_83_2796) with
| (vname, vtok, env) -> begin
(

let arg_sorts = (match ((let _173_2134 = (FStar_Syntax_Subst.compress t_norm)
in _173_2134.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _83_2799) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun _83_2802 -> FStar_SMTEncoding_Term.Term_sort)))
end
| _83_2805 -> begin
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

let _83_2820 = (

let _83_2815 = (curried_arrow_formals_comp t_norm)
in (match (_83_2815) with
| (args, comp) -> begin
if encode_non_total_function_typ then begin
(let _173_2136 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in (args, _173_2136))
end else begin
(args, (None, (FStar_Syntax_Util.comp_result comp)))
end
end))
in (match (_83_2820) with
| (formals, (pre_opt, res_t)) -> begin
(

let _83_2824 = (new_term_constant_and_tok_from_lid env lid)
in (match (_83_2824) with
| (vname, vtok, env) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV (vname, FStar_SMTEncoding_Term.Term_sort))
end
| _83_2827 -> begin
(FStar_SMTEncoding_Term.mkApp (vtok, []))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun _83_21 -> (match (_83_21) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(

let _83_2843 = (FStar_Util.prefix vars)
in (match (_83_2843) with
| (_83_2838, (xxsym, _83_2841)) -> begin
(

let xx = (FStar_SMTEncoding_Term.mkFreeV (xxsym, FStar_SMTEncoding_Term.Term_sort))
in (let _173_2153 = (let _173_2152 = (let _173_2151 = (let _173_2150 = (let _173_2149 = (let _173_2148 = (let _173_2147 = (let _173_2146 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _173_2146))
in (vapp, _173_2147))
in (FStar_SMTEncoding_Term.mkEq _173_2148))
in (((vapp)::[])::[], vars, _173_2149))
in (FStar_SMTEncoding_Term.mkForall _173_2150))
in (_173_2151, Some ("Discriminator equation"), Some ((Prims.strcat "disc_equation_" (escape d.FStar_Ident.str)))))
in FStar_SMTEncoding_Term.Assume (_173_2152))
in (_173_2153)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(

let _83_2855 = (FStar_Util.prefix vars)
in (match (_83_2855) with
| (_83_2850, (xxsym, _83_2853)) -> begin
(

let xx = (FStar_SMTEncoding_Term.mkFreeV (xxsym, FStar_SMTEncoding_Term.Term_sort))
in (

let f = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = 0; FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (

let tp_name = (mk_term_projector_name d f)
in (

let prim_app = (FStar_SMTEncoding_Term.mkApp (tp_name, (xx)::[]))
in (let _173_2158 = (let _173_2157 = (let _173_2156 = (let _173_2155 = (let _173_2154 = (FStar_SMTEncoding_Term.mkEq (vapp, prim_app))
in (((vapp)::[])::[], vars, _173_2154))
in (FStar_SMTEncoding_Term.mkForall _173_2155))
in (_173_2156, Some ("Projector equation"), Some ((Prims.strcat "proj_equation_" tp_name))))
in FStar_SMTEncoding_Term.Assume (_173_2157))
in (_173_2158)::[])))))
end))
end
| _83_2861 -> begin
[]
end)))))
in (

let _83_2868 = (encode_binders None formals env)
in (match (_83_2868) with
| (vars, guards, env', decls1, _83_2867) -> begin
(

let _83_2877 = (match (pre_opt) with
| None -> begin
(let _173_2159 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_173_2159, decls1))
end
| Some (p) -> begin
(

let _83_2874 = (encode_formula p env')
in (match (_83_2874) with
| (g, ds) -> begin
(let _173_2160 = (FStar_SMTEncoding_Term.mk_and_l ((g)::guards))
in (_173_2160, (FStar_List.append decls1 ds)))
end))
end)
in (match (_83_2877) with
| (guard, decls1) -> begin
(

let vtok_app = (mk_Apply vtok_tm vars)
in (

let vapp = (let _173_2162 = (let _173_2161 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (vname, _173_2161))
in (FStar_SMTEncoding_Term.mkApp _173_2162))
in (

let _83_2901 = (

let vname_decl = (let _173_2165 = (let _173_2164 = (FStar_All.pipe_right formals (FStar_List.map (fun _83_2880 -> FStar_SMTEncoding_Term.Term_sort)))
in (vname, _173_2164, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_173_2165))
in (

let _83_2888 = (

let env = (

let _83_2883 = env
in {bindings = _83_2883.bindings; depth = _83_2883.depth; tcenv = _83_2883.tcenv; warn = _83_2883.warn; cache = _83_2883.cache; nolabels = _83_2883.nolabels; use_zfuel_name = _83_2883.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in if (not ((head_normal env tt))) then begin
(encode_term_pred None tt env vtok_tm)
end else begin
(encode_term_pred None t_norm env vtok_tm)
end)
in (match (_83_2888) with
| (tok_typing, decls2) -> begin
(

let tok_typing = FStar_SMTEncoding_Term.Assume ((tok_typing, Some ("function token typing"), Some ((Prims.strcat "function_token_typing_" vname))))
in (

let _83_2898 = (match (formals) with
| [] -> begin
(let _173_2169 = (let _173_2168 = (let _173_2167 = (FStar_SMTEncoding_Term.mkFreeV (vname, FStar_SMTEncoding_Term.Term_sort))
in (FStar_All.pipe_left (fun _173_2166 -> Some (_173_2166)) _173_2167))
in (push_free_var env lid vname _173_2168))
in ((FStar_List.append decls2 ((tok_typing)::[])), _173_2169))
end
| _83_2892 -> begin
(

let vtok_decl = FStar_SMTEncoding_Term.DeclFun ((vtok, [], FStar_SMTEncoding_Term.Term_sort, None))
in (

let vtok_fresh = (let _173_2170 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (vtok, FStar_SMTEncoding_Term.Term_sort) _173_2170))
in (

let name_tok_corr = (let _173_2174 = (let _173_2173 = (let _173_2172 = (let _173_2171 = (FStar_SMTEncoding_Term.mkEq (vtok_app, vapp))
in (((vtok_app)::[])::[], vars, _173_2171))
in (FStar_SMTEncoding_Term.mkForall _173_2172))
in (_173_2173, Some ("Name-token correspondence"), Some ((Prims.strcat "token_correspondence_" vname))))
in FStar_SMTEncoding_Term.Assume (_173_2174))
in ((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[])), env))))
end)
in (match (_83_2898) with
| (tok_decl, env) -> begin
((vname_decl)::tok_decl, env)
end)))
end)))
in (match (_83_2901) with
| (decls2, env) -> begin
(

let _83_2909 = (

let res_t = (FStar_Syntax_Subst.compress res_t)
in (

let _83_2905 = (encode_term res_t env')
in (match (_83_2905) with
| (encoded_res_t, decls) -> begin
(let _173_2175 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in (encoded_res_t, _173_2175, decls))
end)))
in (match (_83_2909) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (let _173_2179 = (let _173_2178 = (let _173_2177 = (let _173_2176 = (FStar_SMTEncoding_Term.mkImp (guard, ty_pred))
in (((vapp)::[])::[], vars, _173_2176))
in (FStar_SMTEncoding_Term.mkForall _173_2177))
in (_173_2178, Some ("free var typing"), Some ((Prims.strcat "typing_" vname))))
in FStar_SMTEncoding_Term.Assume (_173_2179))
in (

let freshness = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New)) then begin
(let _173_2185 = (let _173_2182 = (let _173_2181 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (let _173_2180 = (varops.next_id ())
in (vname, _173_2181, FStar_SMTEncoding_Term.Term_sort, _173_2180)))
in (FStar_SMTEncoding_Term.fresh_constructor _173_2182))
in (let _173_2184 = (let _173_2183 = (pretype_axiom vapp vars)
in (_173_2183)::[])
in (_173_2185)::_173_2184))
end else begin
[]
end
in (

let g = (let _173_2187 = (let _173_2186 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_173_2186)
in (FStar_List.append (FStar_List.append (FStar_List.append (FStar_List.append decls1 decls2) decls3) freshness) _173_2187))
in (g, env))))
end))
end))))
end))
end))))
end))
end)))
end
end))
and encode_signature : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _83_2917 se -> (match (_83_2917) with
| (g, env) -> begin
(

let _83_2921 = (encode_sigelt env se)
in (match (_83_2921) with
| (g', env) -> begin
((FStar_List.append g g'), env)
end))
end)) ([], env))))


let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings -> (

let encode_binding = (fun b _83_2928 -> (match (_83_2928) with
| (decls, env) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (_83_2930) -> begin
([], env)
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(

let _83_2937 = (new_term_constant env x)
in (match (_83_2937) with
| (xxsym, xx, env') -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (

let _83_2939 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _173_2202 = (FStar_Syntax_Print.bv_to_string x)
in (let _173_2201 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _173_2200 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" _173_2202 _173_2201 _173_2200))))
end else begin
()
end
in (

let _83_2943 = (encode_term_pred None t1 env xx)
in (match (_83_2943) with
| (t, decls') -> begin
(

let caption = if (FStar_Options.log_queries ()) then begin
(let _173_2206 = (let _173_2205 = (FStar_Syntax_Print.bv_to_string x)
in (let _173_2204 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _173_2203 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _173_2205 _173_2204 _173_2203))))
in Some (_173_2206))
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
| FStar_TypeChecker_Env.Binding_lid (x, (_83_2950, t)) -> begin
(

let t_norm = (whnf env t)
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant None)
in (

let _83_2959 = (encode_free_var env fv t t_norm [])
in (match (_83_2959) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end))))
end
| (FStar_TypeChecker_Env.Binding_sig_inst (_, se, _)) | (FStar_TypeChecker_Env.Binding_sig (_, se)) -> begin
(

let _83_2973 = (encode_sigelt env se)
in (match (_83_2973) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end))
end)
end))
in (FStar_List.fold_right encode_binding bindings ([], env))))


let encode_labels = (fun labs -> (

let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _83_2980 -> (match (_83_2980) with
| (l, _83_2977, _83_2979) -> begin
FStar_SMTEncoding_Term.DeclFun (((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _83_2987 -> (match (_83_2987) with
| (l, _83_2984, _83_2986) -> begin
(let _173_2214 = (FStar_All.pipe_left (fun _173_2210 -> FStar_SMTEncoding_Term.Echo (_173_2210)) (Prims.fst l))
in (let _173_2213 = (let _173_2212 = (let _173_2211 = (FStar_SMTEncoding_Term.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (_173_2211))
in (_173_2212)::[])
in (_173_2214)::_173_2213))
end))))
in (prefix, suffix))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (let _173_2219 = (let _173_2218 = (let _173_2217 = (FStar_Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _173_2217; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_173_2218)::[])
in (FStar_ST.op_Colon_Equals last_env _173_2219)))


let get_env : FStar_TypeChecker_Env.env  ->  env_t = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "No env; call init first!")
end
| (e)::_83_2993 -> begin
(

let _83_2996 = e
in {bindings = _83_2996.bindings; depth = _83_2996.depth; tcenv = tcenv; warn = _83_2996.warn; cache = _83_2996.cache; nolabels = _83_2996.nolabels; use_zfuel_name = _83_2996.use_zfuel_name; encode_non_total_function_typ = _83_2996.encode_non_total_function_typ})
end))


let set_env : env_t  ->  Prims.unit = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| (_83_3002)::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))


let push_env : Prims.unit  ->  Prims.unit = (fun _83_3004 -> (match (()) with
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

let _83_3010 = hd
in {bindings = _83_3010.bindings; depth = _83_3010.depth; tcenv = _83_3010.tcenv; warn = _83_3010.warn; cache = refs; nolabels = _83_3010.nolabels; use_zfuel_name = _83_3010.use_zfuel_name; encode_non_total_function_typ = _83_3010.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))


let pop_env : Prims.unit  ->  Prims.unit = (fun _83_3013 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Popping an empty stack")
end
| (_83_3017)::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))


let mark_env : Prims.unit  ->  Prims.unit = (fun _83_3019 -> (match (()) with
| () -> begin
(push_env ())
end))


let reset_mark_env : Prims.unit  ->  Prims.unit = (fun _83_3020 -> (match (()) with
| () -> begin
(pop_env ())
end))


let commit_mark_env : Prims.unit  ->  Prims.unit = (fun _83_3021 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| (hd)::(_83_3024)::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _83_3029 -> begin
(FStar_All.failwith "Impossible")
end)
end))


let init : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (

let _83_3031 = (init_env tcenv)
in (

let _83_3033 = (FStar_SMTEncoding_Z3.init ())
in (FStar_SMTEncoding_Z3.giveZ3 ((FStar_SMTEncoding_Term.DefPrelude)::[])))))


let push : Prims.string  ->  Prims.unit = (fun msg -> (

let _83_3036 = (push_env ())
in (

let _83_3038 = (varops.push ())
in (FStar_SMTEncoding_Z3.push msg))))


let pop : Prims.string  ->  Prims.unit = (fun msg -> (

let _83_3041 = (let _173_2240 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _173_2240))
in (

let _83_3043 = (varops.pop ())
in (FStar_SMTEncoding_Z3.pop msg))))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _83_3046 = (mark_env ())
in (

let _83_3048 = (varops.mark ())
in (FStar_SMTEncoding_Z3.mark msg))))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _83_3051 = (reset_mark_env ())
in (

let _83_3053 = (varops.reset_mark ())
in (FStar_SMTEncoding_Z3.reset_mark msg))))


let commit_mark = (fun msg -> (

let _83_3056 = (commit_mark_env ())
in (

let _83_3058 = (varops.commit_mark ())
in (FStar_SMTEncoding_Z3.commit_mark msg))))


let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (

let caption = (fun decls -> if (FStar_Options.log_queries ()) then begin
(let _173_2256 = (let _173_2255 = (let _173_2254 = (let _173_2253 = (let _173_2252 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _173_2252 (FStar_List.map FStar_Syntax_Print.lid_to_string)))
in (FStar_All.pipe_right _173_2253 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " _173_2254))
in FStar_SMTEncoding_Term.Caption (_173_2255))
in (_173_2256)::decls)
end else begin
decls
end)
in (

let env = (get_env tcenv)
in (

let _83_3067 = (encode_sigelt env se)
in (match (_83_3067) with
| (decls, env) -> begin
(

let _83_3068 = (set_env env)
in (let _173_2257 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 _173_2257)))
end)))))


let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let _83_3073 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(let _173_2262 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name _173_2262))
end else begin
()
end
in (

let env = (get_env tcenv)
in (

let _83_3080 = (encode_signature (

let _83_3076 = env
in {bindings = _83_3076.bindings; depth = _83_3076.depth; tcenv = _83_3076.tcenv; warn = false; cache = _83_3076.cache; nolabels = _83_3076.nolabels; use_zfuel_name = _83_3076.use_zfuel_name; encode_non_total_function_typ = _83_3076.encode_non_total_function_typ}) modul.FStar_Syntax_Syntax.exports)
in (match (_83_3080) with
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

let _83_3086 = (set_env (

let _83_3084 = env
in {bindings = _83_3084.bindings; depth = _83_3084.depth; tcenv = _83_3084.tcenv; warn = true; cache = _83_3084.cache; nolabels = _83_3084.nolabels; use_zfuel_name = _83_3084.use_zfuel_name; encode_non_total_function_typ = _83_3084.encode_non_total_function_typ}))
in (

let _83_3088 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
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

let _83_3117 = (

let rec aux = (fun bindings -> (match (bindings) with
| (FStar_TypeChecker_Env.Binding_var (x))::rest -> begin
(

let _83_3106 = (aux rest)
in (match (_83_3106) with
| (out, rest) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (let _173_2284 = (let _173_2283 = (FStar_Syntax_Syntax.mk_binder (

let _83_3108 = x
in {FStar_Syntax_Syntax.ppname = _83_3108.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _83_3108.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_173_2283)::out)
in (_173_2284, rest)))
end))
end
| _83_3111 -> begin
([], bindings)
end))
in (

let _83_3114 = (aux bindings)
in (match (_83_3114) with
| (closing, bindings) -> begin
(let _173_2285 = (FStar_Syntax_Util.close_forall (FStar_List.rev closing) q)
in (_173_2285, bindings))
end)))
in (match (_83_3117) with
| (q, bindings) -> begin
(

let _83_3126 = (let _173_2287 = (FStar_List.filter (fun _83_22 -> (match (_83_22) with
| FStar_TypeChecker_Env.Binding_sig (_83_3120) -> begin
false
end
| _83_3123 -> begin
true
end)) bindings)
in (encode_env_bindings env _173_2287))
in (match (_83_3126) with
| (env_decls, env) -> begin
(

let _83_3127 = if ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) then begin
(let _173_2288 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" _173_2288))
end else begin
()
end
in (

let _83_3131 = (encode_formula q env)
in (match (_83_3131) with
| (phi, qdecls) -> begin
(

let _83_3136 = (let _173_2289 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg _173_2289 phi))
in (match (_83_3136) with
| (phi, labels, _83_3135) -> begin
(

let _83_3139 = (encode_labels labels)
in (match (_83_3139) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append (FStar_List.append env_decls label_prefix) qdecls)
in (

let qry = (let _173_2293 = (let _173_2292 = (FStar_SMTEncoding_Term.mkNot phi)
in (let _173_2291 = (let _173_2290 = (varops.fresh "@query")
in Some (_173_2290))
in (_173_2292, Some ("query"), _173_2291)))
in FStar_SMTEncoding_Term.Assume (_173_2293))
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

let _83_3146 = (push "query")
in (

let _83_3151 = (encode_formula q env)
in (match (_83_3151) with
| (f, _83_3150) -> begin
(

let _83_3152 = (pop "query")
in (match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _83_3156) -> begin
true
end
| _83_3160 -> begin
false
end))
end)))))




