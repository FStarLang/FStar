
open Prims

let add_fuel = (fun x tl -> (

let uu____16 = (FStar_Options.unthrottle_inductives ())
in (match (uu____16) with
| true -> begin
tl
end
| uu____18 -> begin
(x)::tl
end)))


let withenv = (fun c uu____39 -> (match (uu____39) with
| (a, b) -> begin
((a), (b), (c))
end))


let vargs = (fun args -> (FStar_List.filter (fun uu___108_74 -> (match (uu___108_74) with
| (FStar_Util.Inl (uu____79), uu____80) -> begin
false
end
| uu____83 -> begin
true
end)) args))


let subst_lcomp_opt = (fun s l -> (match (l) with
| Some (FStar_Util.Inl (l)) -> begin
Some (FStar_Util.Inl ((let _0_259 = (let _0_258 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp s _0_258))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _0_259))))
end
| uu____118 -> begin
l
end))


let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s '\'' '_'))


let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun lid a -> (

let a = (

let uu___133_132 = a
in (let _0_260 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _0_260; FStar_Syntax_Syntax.index = uu___133_132.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___133_132.FStar_Syntax_Syntax.sort}))
in (let _0_261 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str a.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (FStar_All.pipe_left escape _0_261))))


let primitive_projector_by_pos : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (

let fail = (fun uu____145 -> (failwith (let _0_262 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" _0_262 lid.FStar_Ident.str))))
in (

let uu____146 = (FStar_TypeChecker_Env.lookup_datacon env lid)
in (match (uu____146) with
| (uu____149, t) -> begin
(

let uu____151 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____151) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____164 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____164) with
| (binders, uu____168) -> begin
(match (((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders)))) with
| true -> begin
(fail ())
end
| uu____173 -> begin
(

let b = (FStar_List.nth binders i)
in (mk_term_projector_name lid (Prims.fst b)))
end)
end))
end
| uu____179 -> begin
(fail ())
end))
end))))


let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (let _0_264 = (let _0_263 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str _0_263))
in (FStar_All.pipe_left escape _0_264)))


let mk_term_projector : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun lid a -> (FStar_SMTEncoding_Util.mkFreeV (let _0_265 = (mk_term_projector_name lid a)
in ((_0_265), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))))


let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_SMTEncoding_Term.term = (fun lid i -> (FStar_SMTEncoding_Util.mkFreeV (let _0_266 = (mk_term_projector_name_by_pos lid i)
in ((_0_266), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))))


let mk_data_tester = (fun env l x -> (FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x))

type varops_t =
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; mark : Prims.unit  ->  Prims.unit; reset_mark : Prims.unit  ->  Prims.unit; commit_mark : Prims.unit  ->  Prims.unit; new_var : FStar_Ident.ident  ->  Prims.int  ->  Prims.string; new_fvar : FStar_Ident.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_SMTEncoding_Term.term; next_id : Prims.unit  ->  Prims.int; mk_unique : Prims.string  ->  Prims.string}


let varops : varops_t = (

let initial_ctr = (Prims.parse_int "100")
in (

let ctr = (FStar_Util.mk_ref initial_ctr)
in (

let new_scope = (fun uu____387 -> (let _0_268 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (let _0_267 = (FStar_Util.smap_create (Prims.parse_int "100"))
in ((_0_268), (_0_267)))))
in (

let scopes = (FStar_Util.mk_ref (let _0_269 = (new_scope ())
in (_0_269)::[]))
in (

let mk_unique = (fun y -> (

let y = (escape y)
in (

let y = (

let uu____417 = (let _0_270 = (FStar_ST.read scopes)
in (FStar_Util.find_map _0_270 (fun uu____430 -> (match (uu____430) with
| (names, uu____437) -> begin
(FStar_Util.smap_try_find names y)
end))))
in (match (uu____417) with
| None -> begin
y
end
| Some (uu____442) -> begin
((FStar_Util.incr ctr);
(let _0_272 = (let _0_271 = (FStar_Util.string_of_int (FStar_ST.read ctr))
in (Prims.strcat "__" _0_271))
in (Prims.strcat y _0_272));
)
end))
in (

let top_scope = (let _0_273 = (FStar_List.hd (FStar_ST.read scopes))
in (FStar_All.pipe_left Prims.fst _0_273))
in ((FStar_Util.smap_add top_scope y true);
y;
)))))
in (

let new_var = (fun pp rn -> (let _0_276 = (let _0_275 = (let _0_274 = (FStar_Util.string_of_int rn)
in (Prims.strcat "__" _0_274))
in (Prims.strcat pp.FStar_Ident.idText _0_275))
in (FStar_All.pipe_left mk_unique _0_276)))
in (

let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (

let next_id = (fun uu____484 -> ((FStar_Util.incr ctr);
(FStar_ST.read ctr);
))
in (

let fresh = (fun pfx -> (let _0_278 = (let _0_277 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _0_277))
in (FStar_Util.format2 "%s_%s" pfx _0_278)))
in (

let string_const = (fun s -> (

let uu____499 = (let _0_279 = (FStar_ST.read scopes)
in (FStar_Util.find_map _0_279 (fun uu____512 -> (match (uu____512) with
| (uu____518, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))
in (match (uu____499) with
| Some (f) -> begin
f
end
| None -> begin
(

let id = (next_id ())
in (

let f = (let _0_280 = (FStar_SMTEncoding_Util.mk_String_const id)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString _0_280))
in (

let top_scope = (let _0_281 = (FStar_List.hd (FStar_ST.read scopes))
in (FStar_All.pipe_left Prims.snd _0_281))
in ((FStar_Util.smap_add top_scope s f);
f;
))))
end)))
in (

let push = (fun uu____551 -> (let _0_284 = (let _0_283 = (new_scope ())
in (let _0_282 = (FStar_ST.read scopes)
in (_0_283)::_0_282))
in (FStar_ST.write scopes _0_284)))
in (

let pop = (fun uu____573 -> (let _0_285 = (FStar_List.tl (FStar_ST.read scopes))
in (FStar_ST.write scopes _0_285)))
in (

let mark = (fun uu____595 -> (push ()))
in (

let reset_mark = (fun uu____599 -> (pop ()))
in (

let commit_mark = (fun uu____603 -> (

let uu____604 = (FStar_ST.read scopes)
in (match (uu____604) with
| ((hd1, hd2))::((next1, next2))::tl -> begin
((FStar_Util.smap_fold hd1 (fun key value v -> (FStar_Util.smap_add next1 key value)) ());
(FStar_Util.smap_fold hd2 (fun key value v -> (FStar_Util.smap_add next2 key value)) ());
(FStar_ST.write scopes ((((next1), (next2)))::tl));
)
end
| uu____664 -> begin
(failwith "Impossible")
end)))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id; mk_unique = mk_unique})))))))))))))))


let unmangle : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv = (fun x -> (

let uu___134_673 = x
in (let _0_286 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _0_286; FStar_Syntax_Syntax.index = uu___134_673.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___134_673.FStar_Syntax_Syntax.sort})))

type binding =
| Binding_var of (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term)
| Binding_fvar of (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option)


let uu___is_Binding_var : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Binding_var (_0) -> begin
true
end
| uu____694 -> begin
false
end))


let __proj__Binding_var__item___0 : binding  ->  (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) = (fun projectee -> (match (projectee) with
| Binding_var (_0) -> begin
_0
end))


let uu___is_Binding_fvar : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Binding_fvar (_0) -> begin
true
end
| uu____718 -> begin
false
end))


let __proj__Binding_fvar__item___0 : binding  ->  (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun projectee -> (match (projectee) with
| Binding_fvar (_0) -> begin
_0
end))


let binder_of_eithervar = (fun v -> ((v), (None)))

type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_TypeChecker_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_SMTEncoding_Term.sort Prims.list * FStar_SMTEncoding_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}


let print_env : env_t  ->  Prims.string = (fun e -> (let _0_287 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun uu___109_840 -> (match (uu___109_840) with
| Binding_var (x, uu____842) -> begin
(FStar_Syntax_Print.bv_to_string x)
end
| Binding_fvar (l, uu____844, uu____845, uu____846) -> begin
(FStar_Syntax_Print.lid_to_string l)
end))))
in (FStar_All.pipe_right _0_287 (FStar_String.concat ", "))))


let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))


let caption_t : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.string Prims.option = (fun env t -> (

let uu____878 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____878) with
| true -> begin
Some ((FStar_Syntax_Print.term_to_string t))
end
| uu____880 -> begin
None
end)))


let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (

let xsym = (varops.fresh x)
in (let _0_288 = (FStar_SMTEncoding_Util.mkFreeV ((xsym), (s)))
in ((xsym), (_0_288)))))


let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (let _0_289 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _0_289))
in (

let y = (FStar_SMTEncoding_Util.mkFreeV ((ysym), (FStar_SMTEncoding_Term.Term_sort)))
in ((ysym), (y), ((

let uu___135_901 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = (env.depth + (Prims.parse_int "1")); tcenv = uu___135_901.tcenv; warn = uu___135_901.warn; cache = uu___135_901.cache; nolabels = uu___135_901.nolabels; use_zfuel_name = uu___135_901.use_zfuel_name; encode_non_total_function_typ = uu___135_901.encode_non_total_function_typ}))))))


let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let uu___136_914 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = uu___136_914.depth; tcenv = uu___136_914.tcenv; warn = uu___136_914.warn; cache = uu___136_914.cache; nolabels = uu___136_914.nolabels; use_zfuel_name = uu___136_914.use_zfuel_name; encode_non_total_function_typ = uu___136_914.encode_non_total_function_typ}))))))


let new_term_constant_from_string : env_t  ->  FStar_Syntax_Syntax.bv  ->  Prims.string  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x str -> (

let ysym = (varops.mk_unique str)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let uu___137_930 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = uu___137_930.depth; tcenv = uu___137_930.tcenv; warn = uu___137_930.warn; cache = uu___137_930.cache; nolabels = uu___137_930.nolabels; use_zfuel_name = uu___137_930.use_zfuel_name; encode_non_total_function_typ = uu___137_930.encode_non_total_function_typ}))))))


let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (

let uu___138_940 = env
in {bindings = (Binding_var (((x), (t))))::env.bindings; depth = uu___138_940.depth; tcenv = uu___138_940.tcenv; warn = uu___138_940.warn; cache = uu___138_940.cache; nolabels = uu___138_940.nolabels; use_zfuel_name = uu___138_940.use_zfuel_name; encode_non_total_function_typ = uu___138_940.encode_non_total_function_typ}))


let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let aux = (fun a' -> (lookup_binding env (fun uu___110_956 -> (match (uu___110_956) with
| Binding_var (b, t) when (FStar_Syntax_Syntax.bv_eq b a') -> begin
Some (((b), (t)))
end
| uu____964 -> begin
None
end))))
in (

let uu____967 = (aux a)
in (match (uu____967) with
| None -> begin
(

let a = (unmangle a)
in (

let uu____974 = (aux a)
in (match (uu____974) with
| None -> begin
(failwith (let _0_290 = (FStar_Syntax_Print.bv_to_string a)
in (FStar_Util.format1 "Bound term variable not found (after unmangling): %s" _0_290)))
end
| Some (b, t) -> begin
t
end)))
end
| Some (b, t) -> begin
t
end))))


let new_term_constant_and_tok_from_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * Prims.string * env_t) = (fun env x -> (

let fname = (varops.new_fvar x)
in (

let ftok = (Prims.strcat fname "@tok")
in (let _0_296 = (

let uu___139_999 = env
in (let _0_295 = (let _0_294 = Binding_fvar ((let _0_293 = (let _0_292 = (FStar_SMTEncoding_Util.mkApp ((ftok), ([])))
in (FStar_All.pipe_left (fun _0_291 -> Some (_0_291)) _0_292))
in ((x), (fname), (_0_293), (None))))
in (_0_294)::env.bindings)
in {bindings = _0_295; depth = uu___139_999.depth; tcenv = uu___139_999.tcenv; warn = uu___139_999.warn; cache = uu___139_999.cache; nolabels = uu___139_999.nolabels; use_zfuel_name = uu___139_999.use_zfuel_name; encode_non_total_function_typ = uu___139_999.encode_non_total_function_typ}))
in ((fname), (ftok), (_0_296))))))


let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun uu___111_1021 -> (match (uu___111_1021) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some (((t1), (t2), (t3)))
end
| uu____1043 -> begin
None
end))))


let contains_name : env_t  ->  Prims.string  ->  Prims.bool = (fun env s -> (let _0_297 = (lookup_binding env (fun uu___112_1056 -> (match (uu___112_1056) with
| Binding_fvar (b, t1, t2, t3) when (b.FStar_Ident.str = s) -> begin
Some (())
end
| uu____1066 -> begin
None
end)))
in (FStar_All.pipe_right _0_297 FStar_Option.isSome)))


let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun env a -> (

let uu____1078 = (try_lookup_lid env a)
in (match (uu____1078) with
| None -> begin
(failwith (let _0_298 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" _0_298)))
end
| Some (s) -> begin
s
end)))


let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (

let uu___140_1125 = env
in {bindings = (Binding_fvar (((x), (fname), (ftok), (None))))::env.bindings; depth = uu___140_1125.depth; tcenv = uu___140_1125.tcenv; warn = uu___140_1125.warn; cache = uu___140_1125.cache; nolabels = uu___140_1125.nolabels; use_zfuel_name = uu___140_1125.use_zfuel_name; encode_non_total_function_typ = uu___140_1125.encode_non_total_function_typ}))


let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (

let uu____1137 = (lookup_lid env x)
in (match (uu____1137) with
| (t1, t2, uu____1145) -> begin
(

let t3 = (FStar_SMTEncoding_Util.mkApp (let _0_300 = (let _0_299 = (FStar_SMTEncoding_Util.mkApp (("ZFuel"), ([])))
in (_0_299)::[])
in ((f), (_0_300))))
in (

let uu___141_1153 = env
in {bindings = (Binding_fvar (((x), (t1), (t2), (Some (t3)))))::env.bindings; depth = uu___141_1153.depth; tcenv = uu___141_1153.tcenv; warn = uu___141_1153.warn; cache = uu___141_1153.cache; nolabels = uu___141_1153.nolabels; use_zfuel_name = uu___141_1153.use_zfuel_name; encode_non_total_function_typ = uu___141_1153.encode_non_total_function_typ}))
end)))


let try_lookup_free_var : env_t  ->  FStar_Ident.lident  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env l -> (

let uu____1163 = (try_lookup_lid env l)
in (match (uu____1163) with
| None -> begin
None
end
| Some (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some (f) when env.use_zfuel_name -> begin
Some (f)
end
| uu____1190 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (uu____1195, (fuel)::[]) -> begin
(

let uu____1198 = (let _0_302 = (let _0_301 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right _0_301 Prims.fst))
in (FStar_Util.starts_with _0_302 "fuel"))
in (match (uu____1198) with
| true -> begin
(let _0_305 = (let _0_304 = (FStar_SMTEncoding_Util.mkFreeV ((name), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_ApplyTF _0_304 fuel))
in (FStar_All.pipe_left (fun _0_303 -> Some (_0_303)) _0_305))
end
| uu____1201 -> begin
Some (t)
end))
end
| uu____1202 -> begin
Some (t)
end)
end
| uu____1203 -> begin
None
end)
end)
end)))


let lookup_free_var = (fun env a -> (

let uu____1221 = (try_lookup_free_var env a.FStar_Syntax_Syntax.v)
in (match (uu____1221) with
| Some (t) -> begin
t
end
| None -> begin
(failwith (let _0_306 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _0_306)))
end)))


let lookup_free_var_name = (fun env a -> (

let uu____1240 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (uu____1240) with
| (x, uu____1247, uu____1248) -> begin
x
end)))


let lookup_free_var_sym = (fun env a -> (

let uu____1272 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (uu____1272) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.freevars = uu____1293; FStar_SMTEncoding_Term.rng = uu____1294}) when env.use_zfuel_name -> begin
((g), (zf))
end
| uu____1302 -> begin
(match (sym) with
| None -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end
| Some (sym) -> begin
(match (sym.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, (fuel)::[]) -> begin
((g), ((fuel)::[]))
end
| uu____1316 -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end)
end)
end)
end)))


let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun uu___113_1325 -> (match (uu___113_1325) with
| Binding_fvar (uu____1327, nm', tok, uu____1330) when (nm = nm') -> begin
tok
end
| uu____1335 -> begin
None
end))))


let mkForall_fuel' = (fun n uu____1352 -> (match (uu____1352) with
| (pats, vars, body) -> begin
(

let fallback = (fun uu____1368 -> (FStar_SMTEncoding_Util.mkForall ((pats), (vars), (body))))
in (

let uu____1371 = (FStar_Options.unthrottle_inductives ())
in (match (uu____1371) with
| true -> begin
(fallback ())
end
| uu____1372 -> begin
(

let uu____1373 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____1373) with
| (fsym, fterm) -> begin
(

let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Util.mkApp (("HasTypeFuel"), ((fterm)::args)))
end
| uu____1392 -> begin
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
(FStar_SMTEncoding_Util.mk_and_l (add_fuel guards))
end
| uu____1406 -> begin
(let _0_307 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _0_307 FStar_List.hd))
end)
in (FStar_SMTEncoding_Util.mkImp ((guard), (body'))))
end
| uu____1408 -> begin
body
end)
in (

let vars = (((fsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars
in (FStar_SMTEncoding_Util.mkForall ((pats), (vars), (body)))))))
end))
end)))
end))


let mkForall_fuel : (FStar_SMTEncoding_Term.pat Prims.list Prims.list * FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (mkForall_fuel' (Prims.parse_int "1"))


let head_normal : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let t = (FStar_Syntax_Util.unmeta t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) -> begin
true
end
| (FStar_Syntax_Syntax.Tm_fvar (fv)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(let _0_308 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _0_308 FStar_Option.isNone))
end
| uu____1461 -> begin
false
end)))


let head_redex : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let uu____1468 = (FStar_Syntax_Util.un_uinst t).FStar_Syntax_Syntax.n
in (match (uu____1468) with
| FStar_Syntax_Syntax.Tm_abs (uu____1469, uu____1470, Some (FStar_Util.Inr (l, flags))) -> begin
(((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid)) || (FStar_List.existsb (fun uu___114_1499 -> (match (uu___114_1499) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____1500 -> begin
false
end)) flags))
end
| FStar_Syntax_Syntax.Tm_abs (uu____1501, uu____1502, Some (FStar_Util.Inl (lc))) -> begin
(FStar_Syntax_Util.is_tot_or_gtot_lcomp lc)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(let _0_309 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _0_309 FStar_Option.isSome))
end
| uu____1538 -> begin
false
end)))


let whnf : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____1545 = (head_normal env t)
in (match (uu____1545) with
| true -> begin
t
end
| uu____1546 -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
end)))


let norm : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t))


let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (let _0_312 = (let _0_310 = (FStar_Syntax_Syntax.null_binder t)
in (_0_310)::[])
in (let _0_311 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Util.abs _0_312 _0_311 None))))


let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(let _0_313 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out _0_313))
end
| s -> begin
(

let _0_314 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Util.mk_ApplyTT out _0_314))
end)) e)))


let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)))


let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun uu___115_1595 -> (match (uu___115_1595) with
| (FStar_SMTEncoding_Term.Var ("ApplyTT")) | (FStar_SMTEncoding_Term.Var ("ApplyTF")) -> begin
true
end
| uu____1596 -> begin
false
end))


let is_eta : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env vars t -> (

let rec aux = (fun t xs -> (match (((t.FStar_SMTEncoding_Term.tm), (xs))) with
| (FStar_SMTEncoding_Term.App (app, (f)::({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.freevars = uu____1624; FStar_SMTEncoding_Term.rng = uu____1625})::[]), (x)::xs) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), uu____1639) -> begin
(

let uu____1644 = (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v)
end
| uu____1654 -> begin
false
end)) args vars))
in (match (uu____1644) with
| true -> begin
(tok_of_name env f)
end
| uu____1656 -> begin
None
end))
end
| (uu____1657, []) -> begin
(

let fvs = (FStar_SMTEncoding_Term.free_variables t)
in (

let uu____1660 = (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (not ((FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars))))))
in (match (uu____1660) with
| true -> begin
Some (t)
end
| uu____1663 -> begin
None
end)))
end
| uu____1664 -> begin
None
end))
in (aux t (FStar_List.rev vars))))


type label =
(FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range)


type labels =
label Prims.list

type pattern =
{pat_vars : (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.fv) Prims.list; pat_term : Prims.unit  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t); guard : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term; projections : FStar_SMTEncoding_Term.term  ->  (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) Prims.list}

exception Let_rec_unencodeable


let uu___is_Let_rec_unencodeable : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Let_rec_unencodeable -> begin
true
end
| uu____1748 -> begin
false
end))


let encode_const : FStar_Const.sconst  ->  FStar_SMTEncoding_Term.term = (fun uu___116_1751 -> (match (uu___116_1751) with
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
(FStar_SMTEncoding_Util.mkApp (let _0_316 = (let _0_315 = (FStar_SMTEncoding_Term.boxInt (FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c)))
in (_0_315)::[])
in (("FStar.Char.Char"), (_0_316))))
end
| FStar_Const.Const_int (i, None) -> begin
(FStar_SMTEncoding_Term.boxInt (FStar_SMTEncoding_Util.mkInteger i))
end
| FStar_Const.Const_int (i, Some (uu____1761)) -> begin
(failwith "Machine integers should be desugared")
end
| FStar_Const.Const_string (bytes, uu____1770) -> begin
(varops.string_const (FStar_All.pipe_left FStar_Util.string_of_bytes bytes))
end
| FStar_Const.Const_range (r) -> begin
FStar_SMTEncoding_Term.mk_Range_const
end
| FStar_Const.Const_effect -> begin
FStar_SMTEncoding_Term.mk_Term_type
end
| c -> begin
(failwith (let _0_317 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" _0_317)))
end))


let as_function_typ : env_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (

let rec aux = (fun norm t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1794) -> begin
t
end
| FStar_Syntax_Syntax.Tm_refine (uu____1802) -> begin
(let _0_318 = (FStar_Syntax_Util.unrefine t)
in (aux true _0_318))
end
| uu____1807 -> begin
(match (norm) with
| true -> begin
(let _0_319 = (whnf env t)
in (aux false _0_319))
end
| uu____1808 -> begin
(failwith (let _0_321 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (let _0_320 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _0_321 _0_320))))
end)
end)))
in (aux true t0)))


let curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun k -> (

let k = (FStar_Syntax_Subst.compress k)
in (match (k.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| uu____1829 -> begin
(let _0_322 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (_0_322)))
end)))


let rec encode_binders : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> ((

let uu____1972 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____1972) with
| true -> begin
(let _0_323 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" _0_323))
end
| uu____1973 -> begin
()
end));
(

let uu____1974 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____2010 b -> (match (uu____2010) with
| (vars, guards, env, decls, names) -> begin
(

let uu____2053 = (

let x = (unmangle (Prims.fst b))
in (

let uu____2062 = (gen_term_var env x)
in (match (uu____2062) with
| (xxsym, xx, env') -> begin
(

let uu____2076 = (let _0_324 = (norm env x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt _0_324 env xx))
in (match (uu____2076) with
| (guard_x_t, decls') -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (guard_x_t), (env'), (decls'), (x))
end))
end)))
in (match (uu____2053) with
| (v, g, env, decls', n) -> begin
(((v)::vars), ((g)::guards), (env), ((FStar_List.append decls decls')), ((n)::names))
end))
end)) (([]), ([]), (env), ([]), ([]))))
in (match (uu____1974) with
| (vars, guards, env, decls, names) -> begin
(((FStar_List.rev vars)), ((FStar_List.rev guards)), (env), (decls), ((FStar_List.rev names)))
end));
))
and encode_term_pred : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let uu____2166 = (encode_term t env)
in (match (uu____2166) with
| (t, decls) -> begin
(let _0_325 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t)
in ((_0_325), (decls)))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let uu____2180 = (encode_term t env)
in (match (uu____2180) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _0_326 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t)
in ((_0_326), (decls)))
end
| Some (f) -> begin
(let _0_327 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t)
in ((_0_327), (decls)))
end)
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let t0 = (FStar_Syntax_Subst.compress t)
in ((

let uu____2196 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____2196) with
| true -> begin
(let _0_330 = (FStar_Syntax_Print.tag_of_term t)
in (let _0_329 = (FStar_Syntax_Print.tag_of_term t0)
in (let _0_328 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" _0_330 _0_329 _0_328))))
end
| uu____2197 -> begin
()
end));
(match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(failwith (let _0_334 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (let _0_333 = (FStar_Syntax_Print.tag_of_term t0)
in (let _0_332 = (FStar_Syntax_Print.term_to_string t0)
in (let _0_331 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _0_334 _0_333 _0_332 _0_331))))))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(failwith (let _0_335 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" _0_335)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, k, uu____2208) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____2228) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t = (lookup_term_var env x)
in ((t), ([])))
end
| FStar_Syntax_Syntax.Tm_fvar (v) -> begin
(let _0_336 = (lookup_free_var env v.FStar_Syntax_Syntax.fv_name)
in ((_0_336), ([])))
end
| FStar_Syntax_Syntax.Tm_type (uu____2242) -> begin
((FStar_SMTEncoding_Term.mk_Term_type), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t, uu____2245) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(let _0_337 = (encode_const c)
in ((_0_337), ([])))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____2264 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____2264) with
| (binders, res) -> begin
(

let uu____2271 = ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res))
in (match (uu____2271) with
| true -> begin
(

let uu____2274 = (encode_binders None binders env)
in (match (uu____2274) with
| (vars, guards, env', decls, uu____2289) -> begin
(

let fsym = (let _0_338 = (varops.fresh "f")
in ((_0_338), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV fsym)
in (

let app = (mk_Apply f vars)
in (

let uu____2301 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post (

let uu___142_2305 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___142_2305.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___142_2305.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___142_2305.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___142_2305.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___142_2305.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___142_2305.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___142_2305.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___142_2305.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___142_2305.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___142_2305.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___142_2305.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___142_2305.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___142_2305.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___142_2305.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___142_2305.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___142_2305.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___142_2305.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___142_2305.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___142_2305.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___142_2305.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___142_2305.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___142_2305.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___142_2305.FStar_TypeChecker_Env.qname_and_index}) res)
in (match (uu____2301) with
| (pre_opt, res_t) -> begin
(

let uu____2312 = (encode_term_pred None res_t env' app)
in (match (uu____2312) with
| (res_pred, decls') -> begin
(

let uu____2319 = (match (pre_opt) with
| None -> begin
(let _0_339 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((_0_339), ([])))
end
| Some (pre) -> begin
(

let uu____2328 = (encode_formula pre env')
in (match (uu____2328) with
| (guard, decls0) -> begin
(let _0_340 = (FStar_SMTEncoding_Util.mk_and_l ((guard)::guards))
in ((_0_340), (decls0)))
end))
end)
in (match (uu____2319) with
| (guards, guard_decls) -> begin
(

let t_interp = (FStar_SMTEncoding_Util.mkForall (let _0_341 = (FStar_SMTEncoding_Util.mkImp ((guards), (res_pred)))
in ((((app)::[])::[]), (vars), (_0_341))))
in (

let cvars = (let _0_342 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right _0_342 (FStar_List.filter (fun uu____2357 -> (match (uu____2357) with
| (x, uu____2361) -> begin
(x <> (Prims.fst fsym))
end)))))
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), ((fsym)::cvars), (t_interp)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____2372 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____2372) with
| Some (t', sorts, uu____2388) -> begin
(let _0_344 = (FStar_SMTEncoding_Util.mkApp (let _0_343 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((t'), (_0_343))))
in ((_0_344), ([])))
end
| None -> begin
(

let tsym = (varops.mk_unique (let _0_345 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_arrow_" _0_345)))
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let caption = (

let uu____2418 = (FStar_Options.log_queries ())
in (match (uu____2418) with
| true -> begin
Some ((FStar_TypeChecker_Normalize.term_to_string env.tcenv t0))
end
| uu____2420 -> begin
None
end))
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (caption)))
in (

let t = (FStar_SMTEncoding_Util.mkApp (let _0_346 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((tsym), (_0_346))))
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let k_assumption = (

let a_name = Some ((Prims.strcat "kinding_" tsym))
in FStar_SMTEncoding_Term.Assume ((let _0_347 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((_0_347), (a_name), (a_name)))))
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t)
in (

let pre_typing = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in FStar_SMTEncoding_Term.Assume ((let _0_351 = (mkForall_fuel (let _0_350 = (FStar_SMTEncoding_Util.mkImp (let _0_349 = (let _0_348 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _0_348))
in ((f_has_t), (_0_349))))
in ((((f_has_t)::[])::[]), ((fsym)::cvars), (_0_350))))
in ((_0_351), (Some ("pre-typing for functions")), (a_name)))))
in (

let t_interp = (

let a_name = Some ((Prims.strcat "interpretation_" tsym))
in FStar_SMTEncoding_Term.Assume ((let _0_353 = (FStar_SMTEncoding_Util.mkForall (let _0_352 = (FStar_SMTEncoding_Util.mkIff ((f_has_t_z), (t_interp)))
in ((((f_has_t_z)::[])::[]), ((fsym)::cvars), (_0_352))))
in ((_0_353), (a_name), (a_name)))))
in (

let t_decls = (FStar_List.append ((tdecl)::decls) (FStar_List.append decls' (FStar_List.append guard_decls ((k_assumption)::(pre_typing)::(t_interp)::[]))))
in ((FStar_Util.smap_add env.cache tkey_hash ((tsym), (cvar_sorts), (t_decls)));
((t), (t_decls));
)))))))))))))
end))))))
end))
end))
end)))))
end))
end
| uu____2482 -> begin
(

let tsym = (varops.fresh "Non_total_Tm_arrow")
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let t = (FStar_SMTEncoding_Util.mkApp ((tsym), ([])))
in (

let t_kinding = (

let a_name = Some ((Prims.strcat "non_total_function_typing_" tsym))
in FStar_SMTEncoding_Term.Assume ((let _0_354 = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in ((_0_354), (Some ("Typing for non-total arrows")), (a_name)))))
in (

let fsym = (("f"), (FStar_SMTEncoding_Term.Term_sort))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV fsym)
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let t_interp = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in FStar_SMTEncoding_Term.Assume ((let _0_358 = (mkForall_fuel (let _0_357 = (FStar_SMTEncoding_Util.mkImp (let _0_356 = (let _0_355 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _0_355))
in ((f_has_t), (_0_356))))
in ((((f_has_t)::[])::[]), ((fsym)::[]), (_0_357))))
in ((_0_358), (a_name), (a_name)))))
in ((t), ((tdecl)::(t_kinding)::(t_interp)::[]))))))))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_refine (uu____2516) -> begin
(

let uu____2521 = (

let uu____2524 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)
in (match (uu____2524) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.tk = uu____2529; FStar_Syntax_Syntax.pos = uu____2530; FStar_Syntax_Syntax.vars = uu____2531} -> begin
(

let uu____2538 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) f)
in (match (uu____2538) with
| (b, f) -> begin
(let _0_359 = (Prims.fst (FStar_List.hd b))
in ((_0_359), (f)))
end))
end
| uu____2554 -> begin
(failwith "impossible")
end))
in (match (uu____2521) with
| (x, f) -> begin
(

let uu____2561 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (uu____2561) with
| (base_t, decls) -> begin
(

let uu____2568 = (gen_term_var env x)
in (match (uu____2568) with
| (x, xtm, env') -> begin
(

let uu____2577 = (encode_formula f env')
in (match (uu____2577) with
| (refinement, decls') -> begin
(

let uu____2584 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____2584) with
| (fsym, fterm) -> begin
(

let encoding = (FStar_SMTEncoding_Util.mkAnd (let _0_360 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in ((_0_360), (refinement))))
in (

let cvars = (let _0_361 = (FStar_SMTEncoding_Term.free_variables encoding)
in (FStar_All.pipe_right _0_361 (FStar_List.filter (fun uu____2601 -> (match (uu____2601) with
| (y, uu____2605) -> begin
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
in (

let uu____2624 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____2624) with
| Some (t, uu____2639, uu____2640) -> begin
(let _0_363 = (FStar_SMTEncoding_Util.mkApp (let _0_362 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((t), (_0_362))))
in ((_0_363), ([])))
end
| None -> begin
(

let tsym = (varops.mk_unique (let _0_364 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_refine_" _0_364)))
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let t = (FStar_SMTEncoding_Util.mkApp (let _0_365 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((tsym), (_0_365))))
in (

let x_has_t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let t_haseq_base = (FStar_SMTEncoding_Term.mk_haseq base_t)
in (

let t_haseq_ref = (FStar_SMTEncoding_Term.mk_haseq t)
in (

let t_haseq = FStar_SMTEncoding_Term.Assume ((let _0_367 = (FStar_SMTEncoding_Util.mkForall (let _0_366 = (FStar_SMTEncoding_Util.mkIff ((t_haseq_ref), (t_haseq_base)))
in ((((t_haseq_ref)::[])::[]), (cvars), (_0_366))))
in ((_0_367), (Some ((Prims.strcat "haseq for " tsym))), (Some ((Prims.strcat "haseq" tsym))))))
in (

let t_kinding = FStar_SMTEncoding_Term.Assume ((let _0_368 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((_0_368), (Some ("refinement kinding")), (Some ((Prims.strcat "refinement_kinding_" tsym))))))
in (

let t_interp = FStar_SMTEncoding_Term.Assume ((let _0_371 = (FStar_SMTEncoding_Util.mkForall (let _0_369 = (FStar_SMTEncoding_Util.mkIff ((x_has_t), (encoding)))
in ((((x_has_t)::[])::[]), ((ffv)::(xfv)::cvars), (_0_369))))
in (let _0_370 = Some ((FStar_Syntax_Print.term_to_string t0))
in ((_0_371), (_0_370), (Some ((Prims.strcat "refinement_interpretation_" tsym)))))))
in (

let t_decls = (FStar_List.append decls (FStar_List.append decls' ((tdecl)::(t_kinding)::(t_interp)::(t_haseq)::[])))
in ((FStar_Util.smap_add env.cache tkey_hash ((tsym), (cvar_sorts), (t_decls)));
((t), (t_decls));
)))))))))))))
end))))))))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
(

let ttm = (FStar_SMTEncoding_Util.mk_Term_uvar (FStar_Unionfind.uvar_id uv))
in (

let uu____2742 = (encode_term_pred None k env ttm)
in (match (uu____2742) with
| (t_has_k, decls) -> begin
(

let d = FStar_SMTEncoding_Term.Assume ((let _0_374 = Some ((varops.mk_unique (let _0_373 = (let _0_372 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _0_372))
in (FStar_Util.format1 "uvar_typing_%s" _0_373))))
in ((t_has_k), (Some ("Uvar typing")), (_0_374))))
in ((ttm), ((FStar_List.append decls ((d)::[])))))
end)))
end
| FStar_Syntax_Syntax.Tm_app (uu____2756) -> begin
(

let uu____2766 = (FStar_Syntax_Util.head_and_args t0)
in (match (uu____2766) with
| (head, args_e) -> begin
(

let uu____2794 = (let _0_375 = (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n
in ((_0_375), (args_e)))
in (match (uu____2794) with
| (uu____2809, uu____2810) when (head_redex env head) -> begin
(let _0_376 = (whnf env t)
in (encode_term _0_376 env))
end
| ((FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), (_)::((v1, _))::((v2, _))::[])) | ((FStar_Syntax_Syntax.Tm_fvar (fv), (_)::((v1, _))::((v2, _))::[])) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
(

let uu____2894 = (encode_term v1 env)
in (match (uu____2894) with
| (v1, decls1) -> begin
(

let uu____2901 = (encode_term v2 env)
in (match (uu____2901) with
| (v2, decls2) -> begin
(let _0_377 = (FStar_SMTEncoding_Util.mk_LexCons v1 v2)
in ((_0_377), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), uu____2909) -> begin
(

let e0 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_379 = (let _0_378 = (FStar_List.hd args_e)
in (_0_378)::[])
in ((head), (_0_379)))))) None head.FStar_Syntax_Syntax.pos)
in ((

let uu____2951 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____2951) with
| true -> begin
(let _0_380 = (FStar_Syntax_Print.term_to_string e0)
in (FStar_Util.print1 "Trying to normalize %s\n" _0_380))
end
| uu____2952 -> begin
()
end));
(

let e0 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env.tcenv e0)
in ((

let uu____2955 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____2955) with
| true -> begin
(let _0_381 = (FStar_Syntax_Print.term_to_string e0)
in (FStar_Util.print1 "Result of normalization %s\n" _0_381))
end
| uu____2956 -> begin
()
end));
(

let e0 = (

let uu____2958 = (

let uu____2959 = (FStar_Syntax_Subst.compress e0).FStar_Syntax_Syntax.n
in (match (uu____2959) with
| FStar_Syntax_Syntax.Tm_app (uu____2960) -> begin
false
end
| uu____2970 -> begin
true
end))
in (match (uu____2958) with
| true -> begin
e0
end
| uu____2971 -> begin
(

let uu____2972 = (FStar_Syntax_Util.head_and_args e0)
in (match (uu____2972) with
| (head, args) -> begin
(

let uu____2998 = (

let uu____2999 = (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n
in (match (uu____2999) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) -> begin
true
end
| uu____3000 -> begin
false
end))
in (match (uu____2998) with
| true -> begin
(Prims.fst (FStar_List.hd args))
end
| uu____3008 -> begin
e0
end))
end))
end))
in (

let e = (match (args_e) with
| (uu____3010)::[] -> begin
e0
end
| uu____3023 -> begin
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_382 = (FStar_List.tl args_e)
in ((e0), (_0_382)))))) None t0.FStar_Syntax_Syntax.pos)
end)
in (encode_term e env)));
));
))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____3046)), ((arg, uu____3048))::[]) -> begin
(encode_term arg env)
end
| uu____3066 -> begin
(

let uu____3074 = (encode_args args_e env)
in (match (uu____3074) with
| (args, decls) -> begin
(

let encode_partial_app = (fun ht_opt -> (

let uu____3107 = (encode_term head env)
in (match (uu____3107) with
| (head, decls') -> begin
(

let app_tm = (mk_Apply_args head args)
in (match (ht_opt) with
| None -> begin
((app_tm), ((FStar_List.append decls decls')))
end
| Some (formals, c) -> begin
(

let uu____3146 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (uu____3146) with
| (formals, rest) -> begin
(

let subst = (FStar_List.map2 (fun uu____3188 uu____3189 -> (match (((uu____3188), (uu____3189))) with
| ((bv, uu____3203), (a, uu____3205)) -> begin
FStar_Syntax_Syntax.NT (((bv), (a)))
end)) formals args_e)
in (

let ty = (let _0_383 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right _0_383 (FStar_Syntax_Subst.subst subst)))
in (

let uu____3221 = (encode_term_pred None ty env app_tm)
in (match (uu____3221) with
| (has_type, decls'') -> begin
(

let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (

let e_typing = FStar_SMTEncoding_Term.Assume ((let _0_386 = (FStar_SMTEncoding_Util.mkForall ((((has_type)::[])::[]), (cvars), (has_type)))
in (let _0_385 = Some ((varops.mk_unique (let _0_384 = (FStar_Util.digest_of_string (FStar_SMTEncoding_Term.hash_of_term app_tm))
in (Prims.strcat "partial_app_typing_" _0_384))))
in ((_0_386), (Some ("Partial app typing")), (_0_385)))))
in ((app_tm), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' ((e_typing)::[]))))))))
end))))
end))
end))
end)))
in (

let encode_full_app = (fun fv -> (

let uu____3252 = (lookup_free_var_sym env fv)
in (match (uu____3252) with
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
Some ((let _0_387 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _0_387 Prims.snd)))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____3296, FStar_Util.Inl (t), uu____3298) -> begin
Some (t)
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____3319, FStar_Util.Inr (c), uu____3321) -> begin
Some ((FStar_Syntax_Util.comp_result c))
end
| uu____3342 -> begin
None
end)
in (match (head_type) with
| None -> begin
(encode_partial_app None)
end
| Some (head_type) -> begin
(

let head_type = (let _0_388 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine _0_388))
in (

let uu____3362 = (curried_arrow_formals_comp head_type)
in (match (uu____3362) with
| (formals, c) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| uu____3387 -> begin
(match (((FStar_List.length formals) > (FStar_List.length args))) with
| true -> begin
(encode_partial_app (Some (((formals), (c)))))
end
| uu____3399 -> begin
(encode_partial_app None)
end)
end)
end)))
end)))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let uu____3432 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____3432) with
| (bs, body, opening) -> begin
(

let fallback = (fun uu____3447 -> (

let f = (varops.fresh "Tm_abs")
in (

let decl = FStar_SMTEncoding_Term.DeclFun (((f), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Imprecise function encoding"))))
in (let _0_389 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in ((_0_389), ((decl)::[]))))))
in (

let is_impure = (fun uu___117_3461 -> (match (uu___117_3461) with
| FStar_Util.Inl (lc) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)))
end
| FStar_Util.Inr (eff, uu____3472) -> begin
(let _0_390 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv eff)
in (FStar_All.pipe_right _0_390 Prims.op_Negation))
end))
in (

let codomain_eff = (fun lc -> (match (lc) with
| FStar_Util.Inl (lc) -> begin
(let _0_393 = (let _0_391 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening _0_391))
in (FStar_All.pipe_right _0_393 (fun _0_392 -> Some (_0_392))))
end
| FStar_Util.Inr (eff, flags) -> begin
(

let new_uvar = (fun uu____3509 -> (let _0_394 = (FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange [] FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _0_394 Prims.fst)))
in (match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid)) with
| true -> begin
(let _0_396 = (FStar_Syntax_Syntax.mk_Total (new_uvar ()))
in (FStar_All.pipe_right _0_396 (fun _0_395 -> Some (_0_395))))
end
| uu____3516 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid)) with
| true -> begin
(let _0_398 = (FStar_Syntax_Syntax.mk_GTotal (new_uvar ()))
in (FStar_All.pipe_right _0_398 (fun _0_397 -> Some (_0_397))))
end
| uu____3519 -> begin
None
end)
end))
end))
in (match (lopt) with
| None -> begin
((let _0_400 = (let _0_399 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)" _0_399))
in (FStar_Errors.warn t0.FStar_Syntax_Syntax.pos _0_400));
(fallback ());
)
end
| Some (lc) -> begin
(

let uu____3539 = (is_impure lc)
in (match (uu____3539) with
| true -> begin
(fallback ())
end
| uu____3542 -> begin
(

let uu____3543 = (encode_binders None bs env)
in (match (uu____3543) with
| (vars, guards, envbody, decls, uu____3558) -> begin
(

let uu____3565 = (encode_term body envbody)
in (match (uu____3565) with
| (body, decls') -> begin
(

let key_body = (FStar_SMTEncoding_Util.mkForall (let _0_402 = (FStar_SMTEncoding_Util.mkImp (let _0_401 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((_0_401), (body))))
in (([]), (vars), (_0_402))))
in (

let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), (cvars), (key_body)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____3583 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____3583) with
| Some (t, uu____3598, uu____3599) -> begin
(let _0_404 = (FStar_SMTEncoding_Util.mkApp (let _0_403 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((t), (_0_403))))
in ((_0_404), ([])))
end
| None -> begin
(

let uu____3618 = (is_eta env vars body)
in (match (uu____3618) with
| Some (t) -> begin
((t), ([]))
end
| None -> begin
(

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let fsym = (varops.mk_unique (let _0_405 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_abs_" _0_405)))
in (

let fdecl = FStar_SMTEncoding_Term.DeclFun (((fsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let f = (FStar_SMTEncoding_Util.mkApp (let _0_406 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((fsym), (_0_406))))
in (

let app = (mk_Apply f vars)
in (

let typing_f = (

let uu____3639 = (codomain_eff lc)
in (match (uu____3639) with
| None -> begin
[]
end
| Some (c) -> begin
(

let tfun = (FStar_Syntax_Util.arrow bs c)
in (

let uu____3646 = (encode_term_pred None tfun env f)
in (match (uu____3646) with
| (f_has_t, decls'') -> begin
(

let a_name = Some ((Prims.strcat "typing_" fsym))
in (let _0_409 = (let _0_408 = FStar_SMTEncoding_Term.Assume ((let _0_407 = (FStar_SMTEncoding_Util.mkForall ((((f)::[])::[]), (cvars), (f_has_t)))
in ((_0_407), (a_name), (a_name))))
in (_0_408)::[])
in (FStar_List.append decls'' _0_409)))
end)))
end))
in (

let interp_f = (

let a_name = Some ((Prims.strcat "interpretation_" fsym))
in FStar_SMTEncoding_Term.Assume ((let _0_411 = (FStar_SMTEncoding_Util.mkForall (let _0_410 = (FStar_SMTEncoding_Util.mkEq ((app), (body)))
in ((((app)::[])::[]), ((FStar_List.append vars cvars)), (_0_410))))
in ((_0_411), (a_name), (a_name)))))
in (

let f_decls = (FStar_List.append decls (FStar_List.append decls' (FStar_List.append ((fdecl)::typing_f) ((interp_f)::[]))))
in ((FStar_Util.smap_add env.cache tkey_hash ((fsym), (cvar_sorts), (f_decls)));
((f), (f_decls));
)))))))))
end))
end))))))
end))
end))
end))
end))))
end))
end
| FStar_Syntax_Syntax.Tm_let ((uu____3681, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____3682); FStar_Syntax_Syntax.lbunivs = uu____3683; FStar_Syntax_Syntax.lbtyp = uu____3684; FStar_Syntax_Syntax.lbeff = uu____3685; FStar_Syntax_Syntax.lbdef = uu____3686})::uu____3687), uu____3688) -> begin
(failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____3706; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____3708; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (uu____3724) -> begin
((FStar_Errors.diag t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts");
(

let e = (varops.fresh "let-rec")
in (

let decl_e = FStar_SMTEncoding_Term.DeclFun (((e), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (let _0_412 = (FStar_SMTEncoding_Util.mkFreeV ((e), (FStar_SMTEncoding_Term.Term_sort)))
in ((_0_412), ((decl_e)::[])))));
)
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end);
)))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (

let uu____3778 = (encode_term e1 env)
in (match (uu____3778) with
| (ee1, decls1) -> begin
(

let uu____3785 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) e2)
in (match (uu____3785) with
| (xs, e2) -> begin
(

let uu____3799 = (FStar_List.hd xs)
in (match (uu____3799) with
| (x, uu____3807) -> begin
(

let env' = (push_term_var env x ee1)
in (

let uu____3809 = (encode_body e2 env')
in (match (uu____3809) with
| (ee2, decls2) -> begin
((ee2), ((FStar_List.append decls1 decls2)))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (

let uu____3831 = (encode_term e env)
in (match (uu____3831) with
| (scr, decls) -> begin
(

let uu____3838 = (FStar_List.fold_right (fun b uu____3846 -> (match (uu____3846) with
| (else_case, decls) -> begin
(

let uu____3857 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____3857) with
| (p, w, br) -> begin
(

let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun uu____3887 uu____3888 -> (match (((uu____3887), (uu____3888))) with
| ((env0, pattern), (else_case, decls)) -> begin
(

let guard = (pattern.guard scr)
in (

let projections = (pattern.projections scr)
in (

let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env uu____3925 -> (match (uu____3925) with
| (x, t) -> begin
(push_term_var env x t)
end)) env))
in (

let uu____3930 = (match (w) with
| None -> begin
((guard), ([]))
end
| Some (w) -> begin
(

let uu____3945 = (encode_term w env)
in (match (uu____3945) with
| (w, decls2) -> begin
(let _0_415 = (FStar_SMTEncoding_Util.mkAnd (let _0_414 = (FStar_SMTEncoding_Util.mkEq (let _0_413 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue)
in ((w), (_0_413))))
in ((guard), (_0_414))))
in ((_0_415), (decls2)))
end))
end)
in (match (uu____3930) with
| (guard, decls2) -> begin
(

let uu____3960 = (encode_br br env)
in (match (uu____3960) with
| (br, decls3) -> begin
(let _0_416 = (FStar_SMTEncoding_Util.mkITE ((guard), (br), (else_case)))
in ((_0_416), ((FStar_List.append decls (FStar_List.append decls2 decls3)))))
end))
end)))))
end)) patterns ((else_case), (decls))))
end))
end)) pats ((default_case), (decls)))
in (match (uu____3838) with
| (match_tm, decls) -> begin
((match_tm), (decls))
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| uu____3991 -> begin
(let _0_417 = (encode_one_pat env pat)
in (_0_417)::[])
end))
and encode_one_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> ((

let uu____4001 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____4001) with
| true -> begin
(let _0_418 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" _0_418))
end
| uu____4002 -> begin
()
end));
(

let uu____4003 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (uu____4003) with
| (vars, pat_term) -> begin
(

let uu____4013 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun uu____4036 v -> (match (uu____4036) with
| (env, vars) -> begin
(

let uu____4064 = (gen_term_var env v)
in (match (uu____4064) with
| (xx, uu____4076, env) -> begin
((env), ((((v), (((xx), (FStar_SMTEncoding_Term.Term_sort)))))::vars))
end))
end)) ((env), ([]))))
in (match (uu____4013) with
| (env, vars) -> begin
(

let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (uu____4123) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_dot_term (_)) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(FStar_SMTEncoding_Util.mkEq (let _0_419 = (encode_const c)
in ((scrutinee), (_0_419))))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let is_f = (mk_data_tester env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____4161 -> (match (uu____4161) with
| (arg, uu____4167) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _0_420 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_guard arg _0_420)))
end))))
in (FStar_SMTEncoding_Util.mk_and_l ((is_f)::sub_term_guards))))
end))
in (

let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (uu____4195) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _)) | (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_constant (uu____4210) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(let _0_422 = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____4249 -> (match (uu____4249) with
| (arg, uu____4258) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _0_421 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_projections arg _0_421)))
end))))
in (FStar_All.pipe_right _0_422 FStar_List.flatten))
end))
in (

let pat_term = (fun uu____4276 -> (encode_term pat_term env))
in (

let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in ((env), (pattern))))))
end))
end));
))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (

let uu____4283 = (FStar_All.pipe_right l (FStar_List.fold_left (fun uu____4298 uu____4299 -> (match (((uu____4298), (uu____4299))) with
| ((tms, decls), (t, uu____4319)) -> begin
(

let uu____4330 = (encode_term t env)
in (match (uu____4330) with
| (t, decls') -> begin
(((t)::tms), ((FStar_List.append decls decls')))
end))
end)) (([]), ([]))))
in (match (uu____4283) with
| (l, decls) -> begin
(((FStar_List.rev l)), (decls))
end)))
and encode_function_type_as_formula : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun induction_on new_pats t env -> (

let list_elements = (fun e -> (

let uu____4368 = (FStar_Syntax_Util.list_elements e)
in (match (uu____4368) with
| Some (l) -> begin
l
end
| None -> begin
((FStar_Errors.warn e.FStar_Syntax_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern");
[];
)
end)))
in (

let one_pat = (fun p -> (

let uu____4386 = (let _0_423 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right _0_423 FStar_Syntax_Util.head_and_args))
in (match (uu____4386) with
| (head, args) -> begin
(

let uu____4426 = (let _0_424 = (FStar_Syntax_Util.un_uinst head).FStar_Syntax_Syntax.n
in ((_0_424), (args)))
in (match (uu____4426) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((uu____4445, uu____4446))::((e, uu____4448))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpat_lid) -> begin
((e), (None))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, uu____4479))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatT_lid) -> begin
((e), (None))
end
| uu____4500 -> begin
(failwith "Unexpected pattern term")
end))
end)))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements p)
in (

let smt_pat_or = (fun t -> (

let uu____4533 = (let _0_425 = (FStar_Syntax_Util.unmeta t)
in (FStar_All.pipe_right _0_425 FStar_Syntax_Util.head_and_args))
in (match (uu____4533) with
| (head, args) -> begin
(

let uu____4571 = (let _0_426 = (FStar_Syntax_Util.un_uinst head).FStar_Syntax_Syntax.n
in ((_0_426), (args)))
in (match (uu____4571) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, uu____4589))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatOr_lid) -> begin
Some (e)
end
| uu____4609 -> begin
None
end))
end)))
in (match (elts) with
| (t)::[] -> begin
(

let uu____4627 = (smt_pat_or t)
in (match (uu____4627) with
| Some (e) -> begin
(let _0_428 = (list_elements e)
in (FStar_All.pipe_right _0_428 (FStar_List.map (fun branch -> (let _0_427 = (list_elements branch)
in (FStar_All.pipe_right _0_427 (FStar_List.map one_pat)))))))
end
| uu____4670 -> begin
(let _0_429 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_0_429)::[])
end))
end
| uu____4698 -> begin
(let _0_430 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_0_430)::[])
end))))
in (

let uu____4724 = (

let uu____4740 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____4740) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____4768 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____4768) with
| (binders, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____4803; FStar_Syntax_Syntax.effect_name = uu____4804; FStar_Syntax_Syntax.result_typ = uu____4805; FStar_Syntax_Syntax.effect_args = ((pre, uu____4807))::((post, uu____4809))::((pats, uu____4811))::[]; FStar_Syntax_Syntax.flags = uu____4812}) -> begin
(

let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _0_431 = (lemma_pats pats')
in ((binders), (pre), (post), (_0_431))))
end
| uu____4857 -> begin
(failwith "impos")
end)
end))
end
| uu____4873 -> begin
(failwith "Impos")
end))
in (match (uu____4724) with
| (binders, pre, post, patterns) -> begin
(

let uu____4917 = (encode_binders None binders env)
in (match (uu____4917) with
| (vars, guards, env, decls, uu____4932) -> begin
(

let uu____4939 = (let _0_433 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (

let uu____4982 = (let _0_432 = (FStar_All.pipe_right branch (FStar_List.map (fun uu____5006 -> (match (uu____5006) with
| (t, uu____5013) -> begin
(encode_term t (

let uu___143_5016 = env
in {bindings = uu___143_5016.bindings; depth = uu___143_5016.depth; tcenv = uu___143_5016.tcenv; warn = uu___143_5016.warn; cache = uu___143_5016.cache; nolabels = uu___143_5016.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___143_5016.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _0_432 FStar_List.unzip))
in (match (uu____4982) with
| (pats, decls) -> begin
((pats), (decls))
end)))))
in (FStar_All.pipe_right _0_433 FStar_List.unzip))
in (match (uu____4939) with
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
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _0_435 = (let _0_434 = (FStar_SMTEncoding_Util.mkFreeV l)
in (FStar_SMTEncoding_Util.mk_Precedes _0_434 e))
in (_0_435)::p))))
end
| uu____5062 -> begin
(

let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _0_436 = (FStar_SMTEncoding_Util.mk_Precedes tl e)
in (_0_436)::p))))
end
| ((x, FStar_SMTEncoding_Term.Term_sort))::vars -> begin
(let _0_438 = (let _0_437 = (FStar_SMTEncoding_Util.mkFreeV ((x), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Util.mk_LexCons _0_437 tl))
in (aux _0_438 vars))
end
| uu____5098 -> begin
pats
end))
in (let _0_439 = (FStar_SMTEncoding_Util.mkFreeV (("Prims.LexTop"), (FStar_SMTEncoding_Term.Term_sort)))
in (aux _0_439 vars)))
end)
end)
in (

let env = (

let uu___144_5103 = env
in {bindings = uu___144_5103.bindings; depth = uu___144_5103.depth; tcenv = uu___144_5103.tcenv; warn = uu___144_5103.warn; cache = uu___144_5103.cache; nolabels = true; use_zfuel_name = uu___144_5103.use_zfuel_name; encode_non_total_function_typ = uu___144_5103.encode_non_total_function_typ})
in (

let uu____5104 = (let _0_440 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula _0_440 env))
in (match (uu____5104) with
| (pre, decls'') -> begin
(

let uu____5111 = (let _0_441 = (FStar_Syntax_Util.unmeta post)
in (encode_formula _0_441 env))
in (match (uu____5111) with
| (post, decls''') -> begin
(

let decls = (FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') (FStar_List.append decls'' decls''')))
in (let _0_444 = (FStar_SMTEncoding_Util.mkForall (let _0_443 = (FStar_SMTEncoding_Util.mkImp (let _0_442 = (FStar_SMTEncoding_Util.mk_and_l ((pre)::guards))
in ((_0_442), (post))))
in ((pats), (vars), (_0_443))))
in ((_0_444), (decls))))
end))
end)))))
end))
end))
end))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (

let debug = (fun phi -> (

let uu____5132 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____5132) with
| true -> begin
(let _0_446 = (FStar_Syntax_Print.tag_of_term phi)
in (let _0_445 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print2 "Formula (%s)  %s\n" _0_446 _0_445)))
end
| uu____5133 -> begin
()
end)))
in (

let enc = (fun f r l -> (

let uu____5159 = (FStar_Util.fold_map (fun decls x -> (

let uu____5172 = (encode_term (Prims.fst x) env)
in (match (uu____5172) with
| (t, decls') -> begin
(((FStar_List.append decls decls')), (t))
end))) [] l)
in (match (uu____5159) with
| (decls, args) -> begin
(let _0_447 = (

let uu___145_5190 = (f args)
in {FStar_SMTEncoding_Term.tm = uu___145_5190.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___145_5190.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((_0_447), (decls)))
end)))
in (

let const_op = (fun f r uu____5208 -> (let _0_448 = (f r)
in ((_0_448), ([]))))
in (

let un_op = (fun f l -> (let _0_449 = (FStar_List.hd l)
in (FStar_All.pipe_left f _0_449)))
in (

let bin_op = (fun f uu___118_5238 -> (match (uu___118_5238) with
| (t1)::(t2)::[] -> begin
(f ((t1), (t2)))
end
| uu____5246 -> begin
(failwith "Impossible")
end))
in (

let enc_prop_c = (fun f r l -> (

let uu____5273 = (FStar_Util.fold_map (fun decls uu____5282 -> (match (uu____5282) with
| (t, uu____5290) -> begin
(

let uu____5291 = (encode_formula t env)
in (match (uu____5291) with
| (phi, decls') -> begin
(((FStar_List.append decls decls')), (phi))
end))
end)) [] l)
in (match (uu____5273) with
| (decls, phis) -> begin
(let _0_450 = (

let uu___146_5309 = (f phis)
in {FStar_SMTEncoding_Term.tm = uu___146_5309.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___146_5309.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((_0_450), (decls)))
end)))
in (

let eq_op = (fun r uu___119_5324 -> (match (uu___119_5324) with
| ((_)::(e1)::(e2)::[]) | ((_)::(_)::(e1)::(e2)::[]) -> begin
((enc (bin_op FStar_SMTEncoding_Util.mkEq)) r ((e1)::(e2)::[]))
end
| l -> begin
((enc (bin_op FStar_SMTEncoding_Util.mkEq)) r l)
end))
in (

let mk_imp = (fun r uu___120_5409 -> (match (uu___120_5409) with
| ((lhs, uu____5413))::((rhs, uu____5415))::[] -> begin
(

let uu____5436 = (encode_formula rhs env)
in (match (uu____5436) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____5445) -> begin
((l1), (decls1))
end
| uu____5448 -> begin
(

let uu____5449 = (encode_formula lhs env)
in (match (uu____5449) with
| (l2, decls2) -> begin
(let _0_451 = (FStar_SMTEncoding_Term.mkImp ((l2), (l1)) r)
in ((_0_451), ((FStar_List.append decls1 decls2))))
end))
end)
end))
end
| uu____5457 -> begin
(failwith "impossible")
end))
in (

let mk_ite = (fun r uu___121_5472 -> (match (uu___121_5472) with
| ((guard, uu____5476))::((_then, uu____5478))::((_else, uu____5480))::[] -> begin
(

let uu____5509 = (encode_formula guard env)
in (match (uu____5509) with
| (g, decls1) -> begin
(

let uu____5516 = (encode_formula _then env)
in (match (uu____5516) with
| (t, decls2) -> begin
(

let uu____5523 = (encode_formula _else env)
in (match (uu____5523) with
| (e, decls3) -> begin
(

let res = (FStar_SMTEncoding_Term.mkITE ((g), (t), (e)) r)
in ((res), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end))
end))
end
| uu____5532 -> begin
(failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (f (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)))
in (

let connectives = (let _0_464 = (let _0_452 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd))
in ((FStar_Syntax_Const.and_lid), (_0_452)))
in (let _0_463 = (let _0_462 = (let _0_453 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr))
in ((FStar_Syntax_Const.or_lid), (_0_453)))
in (let _0_461 = (let _0_460 = (let _0_459 = (let _0_454 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff))
in ((FStar_Syntax_Const.iff_lid), (_0_454)))
in (let _0_458 = (let _0_457 = (let _0_456 = (let _0_455 = (FStar_All.pipe_left enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot))
in ((FStar_Syntax_Const.not_lid), (_0_455)))
in (_0_456)::(((FStar_Syntax_Const.eq2_lid), (eq_op)))::(((FStar_Syntax_Const.eq3_lid), (eq_op)))::(((FStar_Syntax_Const.true_lid), ((const_op FStar_SMTEncoding_Term.mkTrue))))::(((FStar_Syntax_Const.false_lid), ((const_op FStar_SMTEncoding_Term.mkFalse))))::[])
in (((FStar_Syntax_Const.ite_lid), (mk_ite)))::_0_457)
in (_0_459)::_0_458))
in (((FStar_Syntax_Const.imp_lid), (mk_imp)))::_0_460)
in (_0_462)::_0_461))
in (_0_464)::_0_463))
in (

let rec fallback = (fun phi -> (match (phi.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(

let uu____5770 = (encode_formula phi' env)
in (match (uu____5770) with
| (phi, decls) -> begin
(let _0_465 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled (((phi), (msg), (r)))) r)
in ((_0_465), (decls)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (uu____5777) -> begin
(let _0_466 = (FStar_Syntax_Util.unmeta phi)
in (encode_formula _0_466 env))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(

let uu____5810 = (encode_match e pats FStar_SMTEncoding_Util.mkFalse env encode_formula)
in (match (uu____5810) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____5818; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____5820; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let uu____5836 = (encode_let x t1 e1 e2 env encode_formula)
in (match (uu____5836) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let head = (FStar_Syntax_Util.un_uinst head)
in (match (((head.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____5868)::((x, uu____5870))::((t, uu____5872))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.has_type_lid) -> begin
(

let uu____5906 = (encode_term x env)
in (match (uu____5906) with
| (x, decls) -> begin
(

let uu____5913 = (encode_term t env)
in (match (uu____5913) with
| (t, decls') -> begin
(let _0_467 = (FStar_SMTEncoding_Term.mk_HasType x t)
in ((_0_467), ((FStar_List.append decls decls'))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((r, uu____5923))::((msg, uu____5925))::((phi, uu____5927))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.labeled_lid) -> begin
(

let uu____5961 = (let _0_469 = (FStar_Syntax_Subst.compress r).FStar_Syntax_Syntax.n
in (let _0_468 = (FStar_Syntax_Subst.compress msg).FStar_Syntax_Syntax.n
in ((_0_469), (_0_468))))
in (match (uu____5961) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____5968))) -> begin
(

let phi = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((phi), (FStar_Syntax_Syntax.Meta_labeled ((((FStar_Util.string_of_unicode s)), (r), (false)))))))) None r)
in (fallback phi))
end
| uu____5984 -> begin
(fallback phi)
end))
end
| uu____5987 when (head_redex env head) -> begin
(let _0_470 = (whnf env phi)
in (encode_formula _0_470 env))
end
| uu____5995 -> begin
(

let uu____6003 = (encode_term phi env)
in (match (uu____6003) with
| (tt, decls) -> begin
(let _0_471 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___147_6010 = tt
in {FStar_SMTEncoding_Term.tm = uu___147_6010.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___147_6010.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi.FStar_Syntax_Syntax.pos}))
in ((_0_471), (decls)))
end))
end))
end
| uu____6013 -> begin
(

let uu____6014 = (encode_term phi env)
in (match (uu____6014) with
| (tt, decls) -> begin
(let _0_472 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___148_6021 = tt
in {FStar_SMTEncoding_Term.tm = uu___148_6021.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___148_6021.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi.FStar_Syntax_Syntax.pos}))
in ((_0_472), (decls)))
end))
end))
in (

let encode_q_body = (fun env bs ps body -> (

let uu____6048 = (encode_binders None bs env)
in (match (uu____6048) with
| (vars, guards, env, decls, uu____6070) -> begin
(

let uu____6077 = (let _0_474 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let uu____6112 = (let _0_473 = (FStar_All.pipe_right p (FStar_List.map (fun uu____6134 -> (match (uu____6134) with
| (t, uu____6140) -> begin
(encode_term t (

let uu___149_6141 = env
in {bindings = uu___149_6141.bindings; depth = uu___149_6141.depth; tcenv = uu___149_6141.tcenv; warn = uu___149_6141.warn; cache = uu___149_6141.cache; nolabels = uu___149_6141.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___149_6141.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _0_473 FStar_List.unzip))
in (match (uu____6112) with
| (p, decls) -> begin
((p), ((FStar_List.flatten decls)))
end)))))
in (FStar_All.pipe_right _0_474 FStar_List.unzip))
in (match (uu____6077) with
| (pats, decls') -> begin
(

let uu____6175 = (encode_formula body env)
in (match (uu____6175) with
| (body, decls'') -> begin
(

let guards = (match (pats) with
| (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (gf), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____6194; FStar_SMTEncoding_Term.rng = uu____6195})::[])::[] when ((FStar_Ident.text_of_lid FStar_Syntax_Const.guard_free) = gf) -> begin
[]
end
| uu____6203 -> begin
guards
end)
in (let _0_475 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((vars), (pats), (_0_475), (body), ((FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') decls''))))))
end))
end))
end)))
in ((debug phi);
(

let phi = (FStar_Syntax_Util.unascribe phi)
in (

let check_pattern_vars = (fun vars pats -> (

let pats = (FStar_All.pipe_right pats (FStar_List.map (fun uu____6239 -> (match (uu____6239) with
| (x, uu____6243) -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x)
end))))
in (match (pats) with
| [] -> begin
()
end
| (hd)::tl -> begin
(

let pat_vars = (let _0_477 = (FStar_Syntax_Free.names hd)
in (FStar_List.fold_left (fun out x -> (let _0_476 = (FStar_Syntax_Free.names x)
in (FStar_Util.set_union out _0_476))) _0_477 tl))
in (

let uu____6253 = (FStar_All.pipe_right vars (FStar_Util.find_opt (fun uu____6265 -> (match (uu____6265) with
| (b, uu____6269) -> begin
(not ((FStar_Util.set_mem b pat_vars)))
end))))
in (match (uu____6253) with
| None -> begin
()
end
| Some (x, uu____6273) -> begin
(

let pos = (FStar_List.fold_left (fun out t -> (FStar_Range.union_ranges out t.FStar_Syntax_Syntax.pos)) hd.FStar_Syntax_Syntax.pos tl)
in (let _0_479 = (let _0_478 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "SMT pattern misses at least one bound variable: %s" _0_478))
in (FStar_Errors.warn pos _0_479)))
end)))
end)))
in (

let uu____6283 = (FStar_Syntax_Util.destruct_typ_as_formula phi)
in (match (uu____6283) with
| None -> begin
(fallback phi)
end
| Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(

let uu____6289 = (FStar_All.pipe_right connectives (FStar_List.tryFind (fun uu____6325 -> (match (uu____6325) with
| (l, uu____6335) -> begin
(FStar_Ident.lid_equals op l)
end))))
in (match (uu____6289) with
| None -> begin
(fallback phi)
end
| Some (uu____6358, f) -> begin
(f phi.FStar_Syntax_Syntax.pos arms)
end))
end
| Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____6387 = (encode_q_body env vars pats body)
in (match (uu____6387) with
| (vars, pats, guard, body, decls) -> begin
(

let tm = (let _0_481 = (let _0_480 = (FStar_SMTEncoding_Util.mkImp ((guard), (body)))
in ((pats), (vars), (_0_480)))
in (FStar_SMTEncoding_Term.mkForall _0_481 phi.FStar_Syntax_Syntax.pos))
in ((tm), (decls)))
end));
)
end
| Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____6424 = (encode_q_body env vars pats body)
in (match (uu____6424) with
| (vars, pats, guard, body, decls) -> begin
(let _0_484 = (let _0_483 = (let _0_482 = (FStar_SMTEncoding_Util.mkAnd ((guard), (body)))
in ((pats), (vars), (_0_482)))
in (FStar_SMTEncoding_Term.mkExists _0_483 phi.FStar_Syntax_Syntax.pos))
in ((_0_484), (decls)))
end));
)
end))));
)))))))))))))))

type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list); is : FStar_Ident.lident  ->  Prims.bool}


let prims : prims_t = (

let uu____6497 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____6497) with
| (asym, a) -> begin
(

let uu____6502 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____6502) with
| (xsym, x) -> begin
(

let uu____6507 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____6507) with
| (ysym, y) -> begin
(

let quant = (fun vars body x -> (

let xname_decl = FStar_SMTEncoding_Term.DeclFun ((let _0_485 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in ((x), (_0_485), (FStar_SMTEncoding_Term.Term_sort), (None))))
in (

let xtok = (Prims.strcat x "@tok")
in (

let xtok_decl = FStar_SMTEncoding_Term.DeclFun (((xtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let xapp = (FStar_SMTEncoding_Util.mkApp (let _0_486 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((x), (_0_486))))
in (

let xtok = (FStar_SMTEncoding_Util.mkApp ((xtok), ([])))
in (

let xtok_app = (mk_Apply xtok vars)
in (let _0_496 = (let _0_495 = (let _0_494 = (let _0_493 = FStar_SMTEncoding_Term.Assume ((let _0_488 = (FStar_SMTEncoding_Util.mkForall (let _0_487 = (FStar_SMTEncoding_Util.mkEq ((xapp), (body)))
in ((((xapp)::[])::[]), (vars), (_0_487))))
in ((_0_488), (None), (Some ((Prims.strcat "primitive_" x))))))
in (let _0_492 = (let _0_491 = FStar_SMTEncoding_Term.Assume ((let _0_490 = (FStar_SMTEncoding_Util.mkForall (let _0_489 = (FStar_SMTEncoding_Util.mkEq ((xtok_app), (xapp)))
in ((((xtok_app)::[])::[]), (vars), (_0_489))))
in ((_0_490), (Some ("Name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" x))))))
in (_0_491)::[])
in (_0_493)::_0_492))
in (xtok_decl)::_0_494)
in (xname_decl)::_0_495)
in ((xtok), (_0_496))))))))))
in (

let axy = (((asym), (FStar_SMTEncoding_Term.Term_sort)))::(((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let xy = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let qx = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let prims = (let _0_592 = (let _0_499 = (let _0_498 = (let _0_497 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _0_497))
in (quant axy _0_498))
in ((FStar_Syntax_Const.op_Eq), (_0_499)))
in (let _0_591 = (let _0_590 = (let _0_502 = (let _0_501 = (let _0_500 = (FStar_SMTEncoding_Util.mkNot (FStar_SMTEncoding_Util.mkEq ((x), (y))))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _0_500))
in (quant axy _0_501))
in ((FStar_Syntax_Const.op_notEq), (_0_502)))
in (let _0_589 = (let _0_588 = (let _0_507 = (let _0_506 = (let _0_505 = (FStar_SMTEncoding_Util.mkLT (let _0_504 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _0_503 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_0_504), (_0_503)))))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _0_505))
in (quant xy _0_506))
in ((FStar_Syntax_Const.op_LT), (_0_507)))
in (let _0_587 = (let _0_586 = (let _0_512 = (let _0_511 = (let _0_510 = (FStar_SMTEncoding_Util.mkLTE (let _0_509 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _0_508 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_0_509), (_0_508)))))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _0_510))
in (quant xy _0_511))
in ((FStar_Syntax_Const.op_LTE), (_0_512)))
in (let _0_585 = (let _0_584 = (let _0_517 = (let _0_516 = (let _0_515 = (FStar_SMTEncoding_Util.mkGT (let _0_514 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _0_513 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_0_514), (_0_513)))))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _0_515))
in (quant xy _0_516))
in ((FStar_Syntax_Const.op_GT), (_0_517)))
in (let _0_583 = (let _0_582 = (let _0_522 = (let _0_521 = (let _0_520 = (FStar_SMTEncoding_Util.mkGTE (let _0_519 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _0_518 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_0_519), (_0_518)))))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _0_520))
in (quant xy _0_521))
in ((FStar_Syntax_Const.op_GTE), (_0_522)))
in (let _0_581 = (let _0_580 = (let _0_527 = (let _0_526 = (let _0_525 = (FStar_SMTEncoding_Util.mkSub (let _0_524 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _0_523 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_0_524), (_0_523)))))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _0_525))
in (quant xy _0_526))
in ((FStar_Syntax_Const.op_Subtraction), (_0_527)))
in (let _0_579 = (let _0_578 = (let _0_530 = (let _0_529 = (let _0_528 = (FStar_SMTEncoding_Util.mkMinus (FStar_SMTEncoding_Term.unboxInt x))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _0_528))
in (quant qx _0_529))
in ((FStar_Syntax_Const.op_Minus), (_0_530)))
in (let _0_577 = (let _0_576 = (let _0_535 = (let _0_534 = (let _0_533 = (FStar_SMTEncoding_Util.mkAdd (let _0_532 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _0_531 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_0_532), (_0_531)))))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _0_533))
in (quant xy _0_534))
in ((FStar_Syntax_Const.op_Addition), (_0_535)))
in (let _0_575 = (let _0_574 = (let _0_540 = (let _0_539 = (let _0_538 = (FStar_SMTEncoding_Util.mkMul (let _0_537 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _0_536 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_0_537), (_0_536)))))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _0_538))
in (quant xy _0_539))
in ((FStar_Syntax_Const.op_Multiply), (_0_540)))
in (let _0_573 = (let _0_572 = (let _0_545 = (let _0_544 = (let _0_543 = (FStar_SMTEncoding_Util.mkDiv (let _0_542 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _0_541 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_0_542), (_0_541)))))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _0_543))
in (quant xy _0_544))
in ((FStar_Syntax_Const.op_Division), (_0_545)))
in (let _0_571 = (let _0_570 = (let _0_550 = (let _0_549 = (let _0_548 = (FStar_SMTEncoding_Util.mkMod (let _0_547 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _0_546 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_0_547), (_0_546)))))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _0_548))
in (quant xy _0_549))
in ((FStar_Syntax_Const.op_Modulus), (_0_550)))
in (let _0_569 = (let _0_568 = (let _0_555 = (let _0_554 = (let _0_553 = (FStar_SMTEncoding_Util.mkAnd (let _0_552 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _0_551 = (FStar_SMTEncoding_Term.unboxBool y)
in ((_0_552), (_0_551)))))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _0_553))
in (quant xy _0_554))
in ((FStar_Syntax_Const.op_And), (_0_555)))
in (let _0_567 = (let _0_566 = (let _0_560 = (let _0_559 = (let _0_558 = (FStar_SMTEncoding_Util.mkOr (let _0_557 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _0_556 = (FStar_SMTEncoding_Term.unboxBool y)
in ((_0_557), (_0_556)))))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _0_558))
in (quant xy _0_559))
in ((FStar_Syntax_Const.op_Or), (_0_560)))
in (let _0_565 = (let _0_564 = (let _0_563 = (let _0_562 = (let _0_561 = (FStar_SMTEncoding_Util.mkNot (FStar_SMTEncoding_Term.unboxBool x))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _0_561))
in (quant qx _0_562))
in ((FStar_Syntax_Const.op_Negation), (_0_563)))
in (_0_564)::[])
in (_0_566)::_0_565))
in (_0_568)::_0_567))
in (_0_570)::_0_569))
in (_0_572)::_0_571))
in (_0_574)::_0_573))
in (_0_576)::_0_575))
in (_0_578)::_0_577))
in (_0_580)::_0_579))
in (_0_582)::_0_581))
in (_0_584)::_0_583))
in (_0_586)::_0_585))
in (_0_588)::_0_587))
in (_0_590)::_0_589))
in (_0_592)::_0_591))
in (

let mk = (fun l v -> (let _0_594 = (let _0_593 = (FStar_All.pipe_right prims (FStar_List.find (fun uu____6853 -> (match (uu____6853) with
| (l', uu____6862) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right _0_593 (FStar_Option.map (fun uu____6883 -> (match (uu____6883) with
| (uu____6894, b) -> begin
(b v)
end)))))
in (FStar_All.pipe_right _0_594 FStar_Option.get)))
in (

let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun uu____6928 -> (match (uu____6928) with
| (l', uu____6937) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is})))))))
end))
end))
end))


let pretype_axiom : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun tapp vars -> (

let uu____6960 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____6960) with
| (xxsym, xx) -> begin
(

let uu____6965 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____6965) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let tapp_hash = (FStar_SMTEncoding_Term.hash_of_term tapp)
in FStar_SMTEncoding_Term.Assume ((let _0_600 = (FStar_SMTEncoding_Util.mkForall (let _0_597 = (FStar_SMTEncoding_Util.mkImp (let _0_596 = (FStar_SMTEncoding_Util.mkEq (let _0_595 = (FStar_SMTEncoding_Util.mkApp (("PreType"), ((xx)::[])))
in ((tapp), (_0_595))))
in ((xx_has_type), (_0_596))))
in ((((xx_has_type)::[])::[]), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars), (_0_597))))
in (let _0_599 = Some ((varops.mk_unique (let _0_598 = (FStar_Util.digest_of_string tapp_hash)
in (Prims.strcat "pretyping_" _0_598))))
in ((_0_600), (Some ("pretyping")), (_0_599)))))))
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
in (let _0_607 = FStar_SMTEncoding_Term.Assume ((let _0_601 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in ((_0_601), (Some ("unit typing")), (Some ("unit_typing")))))
in (let _0_606 = (let _0_605 = FStar_SMTEncoding_Term.Assume ((let _0_604 = (mkForall_fuel (let _0_603 = (FStar_SMTEncoding_Util.mkImp (let _0_602 = (FStar_SMTEncoding_Util.mkEq ((x), (FStar_SMTEncoding_Term.mk_Term_unit)))
in ((typing_pred), (_0_602))))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_0_603))))
in ((_0_604), (Some ("unit inversion")), (Some ("unit_inversion")))))
in (_0_605)::[])
in (_0_607)::_0_606))))
in (

let mk_bool = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Bool_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (let _0_619 = FStar_SMTEncoding_Term.Assume ((let _0_613 = (FStar_SMTEncoding_Util.mkForall (let _0_612 = (let _0_609 = (let _0_608 = (FStar_SMTEncoding_Term.boxBool b)
in (_0_608)::[])
in (_0_609)::[])
in (let _0_611 = (let _0_610 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType _0_610 tt))
in ((_0_612), ((bb)::[]), (_0_611)))))
in ((_0_613), (Some ("bool typing")), (Some ("bool_typing")))))
in (let _0_618 = (let _0_617 = FStar_SMTEncoding_Term.Assume ((let _0_616 = (mkForall_fuel (let _0_615 = (FStar_SMTEncoding_Util.mkImp (let _0_614 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in ((typing_pred), (_0_614))))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_0_615))))
in ((_0_616), (Some ("bool inversion")), (Some ("bool_inversion")))))
in (_0_617)::[])
in (_0_619)::_0_618))))))
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

let precedes = (let _0_626 = (FStar_SMTEncoding_Util.mkApp (let _0_625 = (let _0_624 = (let _0_623 = (let _0_622 = (FStar_SMTEncoding_Term.boxInt a)
in (let _0_621 = (let _0_620 = (FStar_SMTEncoding_Term.boxInt b)
in (_0_620)::[])
in (_0_622)::_0_621))
in (tt)::_0_623)
in (tt)::_0_624)
in (("Prims.Precedes"), (_0_625))))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _0_626))
in (

let precedes_y_x = (let _0_627 = (FStar_SMTEncoding_Util.mkApp (("Precedes"), ((y)::(x)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _0_627))
in (let _0_657 = FStar_SMTEncoding_Term.Assume ((let _0_633 = (FStar_SMTEncoding_Util.mkForall (let _0_632 = (let _0_629 = (let _0_628 = (FStar_SMTEncoding_Term.boxInt b)
in (_0_628)::[])
in (_0_629)::[])
in (let _0_631 = (let _0_630 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType _0_630 tt))
in ((_0_632), ((bb)::[]), (_0_631)))))
in ((_0_633), (Some ("int typing")), (Some ("int_typing")))))
in (let _0_656 = (let _0_655 = FStar_SMTEncoding_Term.Assume ((let _0_636 = (mkForall_fuel (let _0_635 = (FStar_SMTEncoding_Util.mkImp (let _0_634 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in ((typing_pred), (_0_634))))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_0_635))))
in ((_0_636), (Some ("int inversion")), (Some ("int_inversion")))))
in (let _0_654 = (let _0_653 = FStar_SMTEncoding_Term.Assume ((let _0_652 = (mkForall_fuel (let _0_651 = (FStar_SMTEncoding_Util.mkImp (let _0_650 = (FStar_SMTEncoding_Util.mk_and_l (let _0_649 = (let _0_648 = (let _0_647 = (FStar_SMTEncoding_Util.mkGT (let _0_638 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _0_637 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((_0_638), (_0_637)))))
in (let _0_646 = (let _0_645 = (FStar_SMTEncoding_Util.mkGTE (let _0_640 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _0_639 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((_0_640), (_0_639)))))
in (let _0_644 = (let _0_643 = (FStar_SMTEncoding_Util.mkLT (let _0_642 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _0_641 = (FStar_SMTEncoding_Term.unboxInt x)
in ((_0_642), (_0_641)))))
in (_0_643)::[])
in (_0_645)::_0_644))
in (_0_647)::_0_646))
in (typing_pred_y)::_0_648)
in (typing_pred)::_0_649))
in ((_0_650), (precedes_y_x))))
in ((((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[]), ((xx)::(yy)::[]), (_0_651))))
in ((_0_652), (Some ("well-founded ordering on nat (alt)")), (Some ("well-founded-ordering-on-nat")))))
in (_0_653)::[])
in (_0_655)::_0_654))
in (_0_657)::_0_656)))))))))))
in (

let mk_str = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.String_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (let _0_669 = FStar_SMTEncoding_Term.Assume ((let _0_663 = (FStar_SMTEncoding_Util.mkForall (let _0_662 = (let _0_659 = (let _0_658 = (FStar_SMTEncoding_Term.boxString b)
in (_0_658)::[])
in (_0_659)::[])
in (let _0_661 = (let _0_660 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType _0_660 tt))
in ((_0_662), ((bb)::[]), (_0_661)))))
in ((_0_663), (Some ("string typing")), (Some ("string_typing")))))
in (let _0_668 = (let _0_667 = FStar_SMTEncoding_Term.Assume ((let _0_666 = (mkForall_fuel (let _0_665 = (FStar_SMTEncoding_Util.mkImp (let _0_664 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in ((typing_pred), (_0_664))))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_0_665))))
in ((_0_666), (Some ("string inversion")), (Some ("string_inversion")))))
in (_0_667)::[])
in (_0_669)::_0_668))))))
in (

let mk_ref = (fun env reft_name uu____7185 -> (

let r = (("r"), (FStar_SMTEncoding_Term.Ref_sort))
in (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let refa = (FStar_SMTEncoding_Util.mkApp (let _0_671 = (let _0_670 = (FStar_SMTEncoding_Util.mkFreeV aa)
in (_0_670)::[])
in ((reft_name), (_0_671))))
in (

let refb = (FStar_SMTEncoding_Util.mkApp (let _0_673 = (let _0_672 = (FStar_SMTEncoding_Util.mkFreeV bb)
in (_0_672)::[])
in ((reft_name), (_0_673))))
in (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (

let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (let _0_686 = FStar_SMTEncoding_Term.Assume ((let _0_676 = (mkForall_fuel (let _0_675 = (FStar_SMTEncoding_Util.mkImp (let _0_674 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in ((typing_pred), (_0_674))))
in ((((typing_pred)::[])::[]), ((xx)::(aa)::[]), (_0_675))))
in ((_0_676), (Some ("ref inversion")), (Some ("ref_inversion")))))
in (let _0_685 = (let _0_684 = FStar_SMTEncoding_Term.Assume ((let _0_683 = (let _0_682 = (let _0_681 = (FStar_SMTEncoding_Util.mkImp (let _0_680 = (FStar_SMTEncoding_Util.mkAnd ((typing_pred), (typing_pred_b)))
in (let _0_679 = (FStar_SMTEncoding_Util.mkEq (let _0_678 = (FStar_SMTEncoding_Util.mkFreeV aa)
in (let _0_677 = (FStar_SMTEncoding_Util.mkFreeV bb)
in ((_0_678), (_0_677)))))
in ((_0_680), (_0_679)))))
in ((((typing_pred)::(typing_pred_b)::[])::[]), ((xx)::(aa)::(bb)::[]), (_0_681)))
in (mkForall_fuel' (Prims.parse_int "2") _0_682))
in ((_0_683), (Some ("ref typing is injective")), (Some ("ref_injectivity")))))
in (_0_684)::[])
in (_0_686)::_0_685))))))))))
in (

let mk_true_interp = (fun env nm true_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((true_tm)::[])))
in (FStar_SMTEncoding_Term.Assume (((valid), (Some ("True interpretation")), (Some ("true_interp")))))::[]))
in (

let mk_false_interp = (fun env nm false_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((false_tm)::[])))
in (let _0_688 = FStar_SMTEncoding_Term.Assume ((let _0_687 = (FStar_SMTEncoding_Util.mkIff ((FStar_SMTEncoding_Util.mkFalse), (valid)))
in ((_0_687), (Some ("False interpretation")), (Some ("false_interp")))))
in (_0_688)::[])))
in (

let mk_and_interp = (fun env conj uu____7270 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let valid = (FStar_SMTEncoding_Util.mkApp (let _0_690 = (let _0_689 = (FStar_SMTEncoding_Util.mkApp ((conj), ((a)::(b)::[])))
in (_0_689)::[])
in (("Valid"), (_0_690))))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (let _0_694 = FStar_SMTEncoding_Term.Assume ((let _0_693 = (FStar_SMTEncoding_Util.mkForall (let _0_692 = (FStar_SMTEncoding_Util.mkIff (let _0_691 = (FStar_SMTEncoding_Util.mkAnd ((valid_a), (valid_b)))
in ((_0_691), (valid))))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_0_692))))
in ((_0_693), (Some ("/\\ interpretation")), (Some ("l_and-interp")))))
in (_0_694)::[])))))))))
in (

let mk_or_interp = (fun env disj uu____7310 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let valid = (FStar_SMTEncoding_Util.mkApp (let _0_696 = (let _0_695 = (FStar_SMTEncoding_Util.mkApp ((disj), ((a)::(b)::[])))
in (_0_695)::[])
in (("Valid"), (_0_696))))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (let _0_700 = FStar_SMTEncoding_Term.Assume ((let _0_699 = (FStar_SMTEncoding_Util.mkForall (let _0_698 = (FStar_SMTEncoding_Util.mkIff (let _0_697 = (FStar_SMTEncoding_Util.mkOr ((valid_a), (valid_b)))
in ((_0_697), (valid))))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_0_698))))
in ((_0_699), (Some ("\\/ interpretation")), (Some ("l_or-interp")))))
in (_0_700)::[])))))))))
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

let valid = (FStar_SMTEncoding_Util.mkApp (let _0_702 = (let _0_701 = (FStar_SMTEncoding_Util.mkApp ((eq2), ((a)::(x)::(y)::[])))
in (_0_701)::[])
in (("Valid"), (_0_702))))
in (let _0_706 = FStar_SMTEncoding_Term.Assume ((let _0_705 = (FStar_SMTEncoding_Util.mkForall (let _0_704 = (FStar_SMTEncoding_Util.mkIff (let _0_703 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in ((_0_703), (valid))))
in ((((valid)::[])::[]), ((aa)::(xx)::(yy)::[]), (_0_704))))
in ((_0_705), (Some ("Eq2 interpretation")), (Some ("eq2-interp")))))
in (_0_706)::[])))))))))
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

let valid = (FStar_SMTEncoding_Util.mkApp (let _0_708 = (let _0_707 = (FStar_SMTEncoding_Util.mkApp ((eq3), ((a)::(b)::(x)::(y)::[])))
in (_0_707)::[])
in (("Valid"), (_0_708))))
in (let _0_712 = FStar_SMTEncoding_Term.Assume ((let _0_711 = (FStar_SMTEncoding_Util.mkForall (let _0_710 = (FStar_SMTEncoding_Util.mkIff (let _0_709 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in ((_0_709), (valid))))
in ((((valid)::[])::[]), ((aa)::(bb)::(xx)::(yy)::[]), (_0_710))))
in ((_0_711), (Some ("Eq3 interpretation")), (Some ("eq3-interp")))))
in (_0_712)::[])))))))))))
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

let valid = (FStar_SMTEncoding_Util.mkApp (let _0_714 = (let _0_713 = (FStar_SMTEncoding_Util.mkApp ((imp), ((a)::(b)::[])))
in (_0_713)::[])
in (("Valid"), (_0_714))))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (let _0_718 = FStar_SMTEncoding_Term.Assume ((let _0_717 = (FStar_SMTEncoding_Util.mkForall (let _0_716 = (FStar_SMTEncoding_Util.mkIff (let _0_715 = (FStar_SMTEncoding_Util.mkImp ((valid_a), (valid_b)))
in ((_0_715), (valid))))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_0_716))))
in ((_0_717), (Some ("==> interpretation")), (Some ("l_imp-interp")))))
in (_0_718)::[])))))))))
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

let valid = (FStar_SMTEncoding_Util.mkApp (let _0_720 = (let _0_719 = (FStar_SMTEncoding_Util.mkApp ((iff), ((a)::(b)::[])))
in (_0_719)::[])
in (("Valid"), (_0_720))))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (let _0_724 = FStar_SMTEncoding_Term.Assume ((let _0_723 = (FStar_SMTEncoding_Util.mkForall (let _0_722 = (FStar_SMTEncoding_Util.mkIff (let _0_721 = (FStar_SMTEncoding_Util.mkIff ((valid_a), (valid_b)))
in ((_0_721), (valid))))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_0_722))))
in ((_0_723), (Some ("<==> interpretation")), (Some ("l_iff-interp")))))
in (_0_724)::[])))))))))
in (

let mk_not_interp = (fun env l_not tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let valid = (FStar_SMTEncoding_Util.mkApp (let _0_726 = (let _0_725 = (FStar_SMTEncoding_Util.mkApp ((l_not), ((a)::[])))
in (_0_725)::[])
in (("Valid"), (_0_726))))
in (

let not_valid_a = (let _0_727 = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot _0_727))
in (let _0_730 = FStar_SMTEncoding_Term.Assume ((let _0_729 = (FStar_SMTEncoding_Util.mkForall (let _0_728 = (FStar_SMTEncoding_Util.mkIff ((not_valid_a), (valid)))
in ((((valid)::[])::[]), ((aa)::[]), (_0_728))))
in ((_0_729), (Some ("not interpretation")), (Some ("l_not-interp")))))
in (_0_730)::[]))))))
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

let valid = (FStar_SMTEncoding_Util.mkApp (let _0_732 = (let _0_731 = (FStar_SMTEncoding_Util.mkApp ((for_all), ((a)::(b)::[])))
in (_0_731)::[])
in (("Valid"), (_0_732))))
in (

let valid_b_x = (FStar_SMTEncoding_Util.mkApp (let _0_734 = (let _0_733 = (FStar_SMTEncoding_Util.mk_ApplyTT b x)
in (_0_733)::[])
in (("Valid"), (_0_734))))
in (let _0_743 = FStar_SMTEncoding_Term.Assume ((let _0_742 = (FStar_SMTEncoding_Util.mkForall (let _0_741 = (FStar_SMTEncoding_Util.mkIff (let _0_740 = (FStar_SMTEncoding_Util.mkForall (let _0_739 = (let _0_736 = (let _0_735 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_0_735)::[])
in (_0_736)::[])
in (let _0_738 = (FStar_SMTEncoding_Util.mkImp (let _0_737 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((_0_737), (valid_b_x))))
in ((_0_739), ((xx)::[]), (_0_738)))))
in ((_0_740), (valid))))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_0_741))))
in ((_0_742), (Some ("forall interpretation")), (Some ("forall-interp")))))
in (_0_743)::[]))))))))))
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

let valid = (FStar_SMTEncoding_Util.mkApp (let _0_745 = (let _0_744 = (FStar_SMTEncoding_Util.mkApp ((for_some), ((a)::(b)::[])))
in (_0_744)::[])
in (("Valid"), (_0_745))))
in (

let valid_b_x = (FStar_SMTEncoding_Util.mkApp (let _0_747 = (let _0_746 = (FStar_SMTEncoding_Util.mk_ApplyTT b x)
in (_0_746)::[])
in (("Valid"), (_0_747))))
in (let _0_756 = FStar_SMTEncoding_Term.Assume ((let _0_755 = (FStar_SMTEncoding_Util.mkForall (let _0_754 = (FStar_SMTEncoding_Util.mkIff (let _0_753 = (FStar_SMTEncoding_Util.mkExists (let _0_752 = (let _0_749 = (let _0_748 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_0_748)::[])
in (_0_749)::[])
in (let _0_751 = (FStar_SMTEncoding_Util.mkImp (let _0_750 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((_0_750), (valid_b_x))))
in ((_0_752), ((xx)::[]), (_0_751)))))
in ((_0_753), (valid))))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_0_754))))
in ((_0_755), (Some ("exists interpretation")), (Some ("exists-interp")))))
in (_0_756)::[]))))))))))
in (

let mk_range_interp = (fun env range tt -> (

let range_ty = (FStar_SMTEncoding_Util.mkApp ((range), ([])))
in (let _0_759 = FStar_SMTEncoding_Term.Assume ((let _0_758 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_ty)
in (let _0_757 = Some ((varops.mk_unique "typing_range_const"))
in ((_0_758), (Some ("Range_const typing")), (_0_757)))))
in (_0_759)::[])))
in (

let prims = (((FStar_Syntax_Const.unit_lid), (mk_unit)))::(((FStar_Syntax_Const.bool_lid), (mk_bool)))::(((FStar_Syntax_Const.int_lid), (mk_int)))::(((FStar_Syntax_Const.string_lid), (mk_str)))::(((FStar_Syntax_Const.ref_lid), (mk_ref)))::(((FStar_Syntax_Const.true_lid), (mk_true_interp)))::(((FStar_Syntax_Const.false_lid), (mk_false_interp)))::(((FStar_Syntax_Const.and_lid), (mk_and_interp)))::(((FStar_Syntax_Const.or_lid), (mk_or_interp)))::(((FStar_Syntax_Const.eq2_lid), (mk_eq2_interp)))::(((FStar_Syntax_Const.eq3_lid), (mk_eq3_interp)))::(((FStar_Syntax_Const.imp_lid), (mk_imp_interp)))::(((FStar_Syntax_Const.iff_lid), (mk_iff_interp)))::(((FStar_Syntax_Const.not_lid), (mk_not_interp)))::(((FStar_Syntax_Const.forall_lid), (mk_forall_interp)))::(((FStar_Syntax_Const.exists_lid), (mk_exists_interp)))::(((FStar_Syntax_Const.range_lid), (mk_range_interp)))::[]
in (fun env t s tt -> (

let uu____7923 = (FStar_Util.find_opt (fun uu____7941 -> (match (uu____7941) with
| (l, uu____7951) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)
in (match (uu____7923) with
| None -> begin
[]
end
| Some (uu____7973, f) -> begin
(f env s tt)
end)))))))))))))))))))))))))


let encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____8010 = (encode_function_type_as_formula None None t env)
in (match (uu____8010) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_SMTEncoding_Term.Assume (((form), (Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str))), (Some ((Prims.strcat "lemma_" lid.FStar_Ident.str))))))::[]))
end))))


let encode_free_var : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env fv tt t_norm quals -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____8043 = ((let _0_760 = (FStar_Syntax_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _0_760)) || (FStar_Syntax_Util.is_lemma t_norm))
in (match (uu____8043) with
| true -> begin
(

let uu____8047 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____8047) with
| (vname, vtok, env) -> begin
(

let arg_sorts = (

let uu____8059 = (FStar_Syntax_Subst.compress t_norm).FStar_Syntax_Syntax.n
in (match (uu____8059) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____8062) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun uu____8079 -> FStar_SMTEncoding_Term.Term_sort)))
end
| uu____8082 -> begin
[]
end))
in (

let d = FStar_SMTEncoding_Term.DeclFun (((vname), (arg_sorts), (FStar_SMTEncoding_Term.Term_sort), (Some ("Uninterpreted function symbol for impure function"))))
in (

let dd = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Uninterpreted name for impure function"))))
in (((d)::(dd)::[]), (env)))))
end))
end
| uu____8090 -> begin
(

let uu____8091 = (prims.is lid)
in (match (uu____8091) with
| true -> begin
(

let vname = (varops.new_fvar lid)
in (

let uu____8096 = (prims.mk lid vname)
in (match (uu____8096) with
| (tok, definition) -> begin
(

let env = (push_free_var env lid vname (Some (tok)))
in ((definition), (env)))
end)))
end
| uu____8109 -> begin
(

let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (

let uu____8111 = (

let uu____8117 = (curried_arrow_formals_comp t_norm)
in (match (uu____8117) with
| (args, comp) -> begin
(match (encode_non_total_function_typ) with
| true -> begin
(let _0_761 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in ((args), (_0_761)))
end
| uu____8135 -> begin
((args), (((None), ((FStar_Syntax_Util.comp_result comp)))))
end)
end))
in (match (uu____8111) with
| (formals, (pre_opt, res_t)) -> begin
(

let uu____8155 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____8155) with
| (vname, vtok, env) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
end
| uu____8168 -> begin
(FStar_SMTEncoding_Util.mkApp ((vtok), ([])))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun uu___122_8192 -> (match (uu___122_8192) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(

let uu____8195 = (FStar_Util.prefix vars)
in (match (uu____8195) with
| (uu____8206, (xxsym, uu____8208)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (let _0_766 = FStar_SMTEncoding_Term.Assume ((let _0_765 = (FStar_SMTEncoding_Util.mkForall (let _0_764 = (FStar_SMTEncoding_Util.mkEq (let _0_763 = (let _0_762 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _0_762))
in ((vapp), (_0_763))))
in ((((vapp)::[])::[]), (vars), (_0_764))))
in ((_0_765), (Some ("Discriminator equation")), (Some ((Prims.strcat "disc_equation_" (escape d.FStar_Ident.str)))))))
in (_0_766)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(

let uu____8229 = (FStar_Util.prefix vars)
in (match (uu____8229) with
| (uu____8240, (xxsym, uu____8242)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (

let tp_name = (mk_term_projector_name d f)
in (

let prim_app = (FStar_SMTEncoding_Util.mkApp ((tp_name), ((xx)::[])))
in (let _0_769 = FStar_SMTEncoding_Term.Assume ((let _0_768 = (FStar_SMTEncoding_Util.mkForall (let _0_767 = (FStar_SMTEncoding_Util.mkEq ((vapp), (prim_app)))
in ((((vapp)::[])::[]), (vars), (_0_767))))
in ((_0_768), (Some ("Projector equation")), (Some ((Prims.strcat "proj_equation_" tp_name))))))
in (_0_769)::[])))))
end))
end
| uu____8265 -> begin
[]
end)))))
in (

let uu____8266 = (encode_binders None formals env)
in (match (uu____8266) with
| (vars, guards, env', decls1, uu____8282) -> begin
(

let uu____8289 = (match (pre_opt) with
| None -> begin
(let _0_770 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((_0_770), (decls1)))
end
| Some (p) -> begin
(

let uu____8295 = (encode_formula p env')
in (match (uu____8295) with
| (g, ds) -> begin
(let _0_771 = (FStar_SMTEncoding_Util.mk_and_l ((g)::guards))
in ((_0_771), ((FStar_List.append decls1 ds))))
end))
end)
in (match (uu____8289) with
| (guard, decls1) -> begin
(

let vtok_app = (mk_Apply vtok_tm vars)
in (

let vapp = (FStar_SMTEncoding_Util.mkApp (let _0_772 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((vname), (_0_772))))
in (

let uu____8313 = (

let vname_decl = FStar_SMTEncoding_Term.DeclFun ((let _0_773 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____8323 -> FStar_SMTEncoding_Term.Term_sort)))
in ((vname), (_0_773), (FStar_SMTEncoding_Term.Term_sort), (None))))
in (

let uu____8326 = (

let env = (

let uu___150_8330 = env
in {bindings = uu___150_8330.bindings; depth = uu___150_8330.depth; tcenv = uu___150_8330.tcenv; warn = uu___150_8330.warn; cache = uu___150_8330.cache; nolabels = uu___150_8330.nolabels; use_zfuel_name = uu___150_8330.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in (

let uu____8331 = (not ((head_normal env tt)))
in (match (uu____8331) with
| true -> begin
(encode_term_pred None tt env vtok_tm)
end
| uu____8334 -> begin
(encode_term_pred None t_norm env vtok_tm)
end)))
in (match (uu____8326) with
| (tok_typing, decls2) -> begin
(

let tok_typing = FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("function token typing")), (Some ((Prims.strcat "function_token_typing_" vname)))))
in (

let uu____8343 = (match (formals) with
| [] -> begin
(let _0_777 = (let _0_776 = (let _0_775 = (FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left (fun _0_774 -> Some (_0_774)) _0_775))
in (push_free_var env lid vname _0_776))
in (((FStar_List.append decls2 ((tok_typing)::[]))), (_0_777)))
end
| uu____8354 -> begin
(

let vtok_decl = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let vtok_fresh = (let _0_778 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((vtok), (FStar_SMTEncoding_Term.Term_sort)) _0_778))
in (

let name_tok_corr = FStar_SMTEncoding_Term.Assume ((let _0_780 = (FStar_SMTEncoding_Util.mkForall (let _0_779 = (FStar_SMTEncoding_Util.mkEq ((vtok_app), (vapp)))
in ((((vtok_app)::[])::((vapp)::[])::[]), (vars), (_0_779))))
in ((_0_780), (Some ("Name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" vname))))))
in (((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[]))), (env)))))
end)
in (match (uu____8343) with
| (tok_decl, env) -> begin
(((vname_decl)::tok_decl), (env))
end)))
end)))
in (match (uu____8313) with
| (decls2, env) -> begin
(

let uu____8384 = (

let res_t = (FStar_Syntax_Subst.compress res_t)
in (

let uu____8389 = (encode_term res_t env')
in (match (uu____8389) with
| (encoded_res_t, decls) -> begin
(let _0_781 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in ((encoded_res_t), (_0_781), (decls)))
end)))
in (match (uu____8384) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = FStar_SMTEncoding_Term.Assume ((let _0_783 = (FStar_SMTEncoding_Util.mkForall (let _0_782 = (FStar_SMTEncoding_Util.mkImp ((guard), (ty_pred)))
in ((((vapp)::[])::[]), (vars), (_0_782))))
in ((_0_783), (Some ("free var typing")), (Some ((Prims.strcat "typing_" vname))))))
in (

let freshness = (

let uu____8413 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New))
in (match (uu____8413) with
| true -> begin
(let _0_788 = (FStar_SMTEncoding_Term.fresh_constructor (let _0_785 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (let _0_784 = (varops.next_id ())
in ((vname), (_0_785), (FStar_SMTEncoding_Term.Term_sort), (_0_784)))))
in (let _0_787 = (let _0_786 = (pretype_axiom vapp vars)
in (_0_786)::[])
in (_0_788)::_0_787))
end
| uu____8421 -> begin
[]
end))
in (

let g = (let _0_793 = (let _0_792 = (let _0_791 = (let _0_790 = (let _0_789 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_0_789)
in (FStar_List.append freshness _0_790))
in (FStar_List.append decls3 _0_791))
in (FStar_List.append decls2 _0_792))
in (FStar_List.append decls1 _0_793))
in ((g), (env)))))
end))
end))))
end))
end))))
end))
end)))
end))
end))))


let declare_top_level_let : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  ((Prims.string * FStar_SMTEncoding_Term.term Prims.option) * FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env x t t_norm -> (

let uu____8444 = (try_lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____8444) with
| None -> begin
(

let uu____8467 = (encode_free_var env x t t_norm [])
in (match (uu____8467) with
| (decls, env) -> begin
(

let uu____8482 = (lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____8482) with
| (n, x', uu____8501) -> begin
((((n), (x'))), (decls), (env))
end))
end))
end
| Some (n, x, uu____8513) -> begin
((((n), (x))), ([]), (env))
end)))


let encode_top_level_val : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env lid t quals -> (

let tt = (norm env t)
in (

let uu____8546 = (encode_free_var env lid t tt quals)
in (match (uu____8546) with
| (decls, env) -> begin
(

let uu____8557 = (FStar_Syntax_Util.is_smt_lemma t)
in (match (uu____8557) with
| true -> begin
(let _0_795 = (let _0_794 = (encode_smt_lemma env lid tt)
in (FStar_List.append decls _0_794))
in ((_0_795), (env)))
end
| uu____8562 -> begin
((decls), (env))
end))
end))))


let encode_top_level_vals : env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____8587 lb -> (match (uu____8587) with
| (decls, env) -> begin
(

let uu____8599 = (let _0_796 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env _0_796 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (uu____8599) with
| (decls', env) -> begin
(((FStar_List.append decls decls')), (env))
end))
end)) (([]), (env)))))


let encode_top_level_let : env_t  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env uu____8626 quals -> (match (uu____8626) with
| (is_rec, bindings) -> begin
(

let eta_expand = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let uu____8675 = (FStar_Util.first_N nbinders formals)
in (match (uu____8675) with
| (formals, extra_formals) -> begin
(

let subst = (FStar_List.map2 (fun uu____8715 uu____8716 -> (match (((uu____8715), (uu____8716))) with
| ((formal, uu____8726), (binder, uu____8728)) -> begin
FStar_Syntax_Syntax.NT ((let _0_797 = (FStar_Syntax_Syntax.bv_to_name binder)
in ((formal), (_0_797))))
end)) formals binders)
in (

let extra_formals = (let _0_800 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun uu____8753 -> (match (uu____8753) with
| (x, i) -> begin
(let _0_799 = (

let uu___151_8760 = x
in (let _0_798 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___151_8760.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___151_8760.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_798}))
in ((_0_799), (i)))
end))))
in (FStar_All.pipe_right _0_800 FStar_Syntax_Util.name_binders))
in (

let body = (let _0_806 = (let _0_805 = (FStar_Syntax_Subst.subst subst t).FStar_Syntax_Syntax.n
in (FStar_All.pipe_left (fun _0_804 -> Some (_0_804)) _0_805))
in ((let _0_803 = (FStar_Syntax_Subst.compress body)
in (let _0_802 = (let _0_801 = (FStar_Syntax_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _0_801))
in (FStar_Syntax_Syntax.extend_app_n _0_803 _0_802))) _0_806 body.FStar_Syntax_Syntax.pos))
in (((FStar_List.append binders extra_formals)), (body)))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (

let rec aux = (fun norm t_norm -> (

let uu____8844 = (FStar_Syntax_Util.unascribe e).FStar_Syntax_Syntax.n
in (match (uu____8844) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, lopt) -> begin
(

let uu____8884 = (FStar_Syntax_Subst.open_term' binders body)
in (match (uu____8884) with
| (binders, body, opening) -> begin
(

let uu____8905 = (FStar_Syntax_Subst.compress t_norm).FStar_Syntax_Syntax.n
in (match (uu____8905) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____8932 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____8932) with
| (formals, c) -> begin
(

let nformals = (FStar_List.length formals)
in (

let nbinders = (FStar_List.length binders)
in (

let tres = (FStar_Syntax_Util.comp_result c)
in (

let uu____8962 = ((nformals < nbinders) && (FStar_Syntax_Util.is_total_comp c))
in (match (uu____8962) with
| true -> begin
(

let lopt = (subst_lcomp_opt opening lopt)
in (

let uu____8992 = (FStar_Util.first_N nformals binders)
in (match (uu____8992) with
| (bs0, rest) -> begin
(

let c = (

let subst = (FStar_List.map2 (fun uu____9040 uu____9041 -> (match (((uu____9040), (uu____9041))) with
| ((b, uu____9051), (x, uu____9053)) -> begin
FStar_Syntax_Syntax.NT ((let _0_807 = (FStar_Syntax_Syntax.bv_to_name x)
in ((b), (_0_807))))
end)) bs0 formals)
in (FStar_Syntax_Subst.subst_comp subst c))
in (

let body = (FStar_Syntax_Util.abs rest body lopt)
in ((((bs0), (body), (bs0), ((FStar_Syntax_Util.comp_result c)))), (false))))
end)))
end
| uu____9079 -> begin
(match ((nformals > nbinders)) with
| true -> begin
(

let uu____9099 = (eta_expand binders formals body tres)
in (match (uu____9099) with
| (binders, body) -> begin
((((binders), (body), (formals), (tres))), (false))
end))
end
| uu____9151 -> begin
((((binders), (body), (formals), (tres))), (false))
end)
end)))))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____9161) -> begin
(let _0_808 = (Prims.fst (aux norm x.FStar_Syntax_Syntax.sort))
in ((_0_808), (true)))
end
| uu____9190 when (not (norm)) -> begin
(

let t_norm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm)
in (aux true t_norm))
end
| uu____9192 -> begin
(failwith (let _0_810 = (FStar_Syntax_Print.term_to_string e)
in (let _0_809 = (FStar_Syntax_Print.term_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str _0_810 _0_809))))
end))
end))
end
| uu____9207 -> begin
(

let uu____9208 = (FStar_Syntax_Subst.compress t_norm).FStar_Syntax_Syntax.n
in (match (uu____9208) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____9235 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____9235) with
| (formals, c) -> begin
(

let tres = (FStar_Syntax_Util.comp_result c)
in (

let uu____9257 = (eta_expand [] formals e tres)
in (match (uu____9257) with
| (binders, body) -> begin
((((binders), (body), (formals), (tres))), (false))
end)))
end))
end
| uu____9311 -> begin
(((([]), (e), ([]), (t_norm))), (false))
end))
end)))
in (aux false t_norm)))
in try
(match (()) with
| () -> begin
(

let uu____9339 = (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp))))
in (match (uu____9339) with
| true -> begin
(encode_top_level_vals env bindings quals)
end
| uu____9345 -> begin
(

let uu____9346 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____9387 lb -> (match (uu____9387) with
| (toks, typs, decls, env) -> begin
((

let uu____9438 = (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp)
in (match (uu____9438) with
| true -> begin
(Prims.raise Let_rec_unencodeable)
end
| uu____9439 -> begin
()
end));
(

let t_norm = (whnf env lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____9441 = (let _0_811 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env _0_811 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (uu____9441) with
| (tok, decl, env) -> begin
(let _0_814 = (let _0_813 = (let _0_812 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in ((_0_812), (tok)))
in (_0_813)::toks)
in ((_0_814), ((t_norm)::typs), ((decl)::decls), (env)))
end)));
)
end)) (([]), ([]), ([]), (env))))
in (match (uu____9346) with
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
| uu____9574 -> begin
(match (curry) with
| true -> begin
(match (ftok) with
| Some (ftok) -> begin
(mk_Apply ftok vars)
end
| None -> begin
(let _0_815 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply _0_815 vars))
end)
end
| uu____9579 -> begin
(FStar_SMTEncoding_Util.mkApp (let _0_816 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (_0_816))))
end)
end))
in (

let uu____9583 = ((FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___123_9585 -> (match (uu___123_9585) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| uu____9586 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> (let _0_817 = (FStar_Syntax_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _0_817))))))
in (match (uu____9583) with
| true -> begin
((decls), (env))
end
| uu____9593 -> begin
(match ((not (is_rec))) with
| true -> begin
(match (((bindings), (typs), (toks))) with
| (({FStar_Syntax_Syntax.lbname = uu____9608; FStar_Syntax_Syntax.lbunivs = uu____9609; FStar_Syntax_Syntax.lbtyp = uu____9610; FStar_Syntax_Syntax.lbeff = uu____9611; FStar_Syntax_Syntax.lbdef = e})::[], (t_norm)::[], ((flid_fv, (f, ftok)))::[]) -> begin
(

let e = (FStar_Syntax_Subst.compress e)
in (

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____9653 = (destruct_bound_function flid t_norm e)
in (match (uu____9653) with
| ((binders, body, uu____9673, uu____9674), curry) -> begin
(

let uu____9704 = (encode_binders None binders env)
in (match (uu____9704) with
| (vars, guards, env', binder_decls, uu____9720) -> begin
(

let app = (mk_app curry f ftok vars)
in (

let uu____9728 = (

let uu____9733 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic))
in (match (uu____9733) with
| true -> begin
(let _0_819 = (FStar_SMTEncoding_Term.mk_Valid app)
in (let _0_818 = (encode_formula body env')
in ((_0_819), (_0_818))))
end
| uu____9741 -> begin
(let _0_820 = (encode_term body env')
in ((app), (_0_820)))
end))
in (match (uu____9728) with
| (app, (body, decls2)) -> begin
(

let eqn = FStar_SMTEncoding_Term.Assume ((let _0_823 = (FStar_SMTEncoding_Util.mkForall (let _0_821 = (FStar_SMTEncoding_Util.mkEq ((app), (body)))
in ((((app)::[])::[]), (vars), (_0_821))))
in (let _0_822 = Some ((FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str))
in ((_0_823), (_0_822), (Some ((Prims.strcat "equation_" f)))))))
in (let _0_828 = (let _0_827 = (let _0_826 = (let _0_825 = (let _0_824 = (primitive_type_axioms env.tcenv flid f app)
in (FStar_List.append ((eqn)::[]) _0_824))
in (FStar_List.append decls2 _0_825))
in (FStar_List.append binder_decls _0_826))
in (FStar_List.append decls _0_827))
in ((_0_828), (env))))
end)))
end))
end))))
end
| uu____9761 -> begin
(failwith "Impossible")
end)
end
| uu____9776 -> begin
(

let fuel = (let _0_829 = (varops.fresh "fuel")
in ((_0_829), (FStar_SMTEncoding_Term.Fuel_sort)))
in (

let fuel_tm = (FStar_SMTEncoding_Util.mkFreeV fuel)
in (

let env0 = env
in (

let uu____9782 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun uu____9821 uu____9822 -> (match (((uu____9821), (uu____9822))) with
| ((gtoks, env), (flid_fv, (f, ftok))) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let g = (varops.new_fvar (FStar_Ident.lid_add_suffix flid "fuel_instrumented"))
in (

let gtok = (varops.new_fvar (FStar_Ident.lid_add_suffix flid "fuel_instrumented_token"))
in (

let env = (let _0_832 = (let _0_831 = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::[])))
in (FStar_All.pipe_left (fun _0_830 -> Some (_0_830)) _0_831))
in (push_free_var env flid gtok _0_832))
in (((((flid), (f), (ftok), (g), (gtok)))::gtoks), (env))))))
end)) (([]), (env))))
in (match (uu____9782) with
| (gtoks, env) -> begin
(

let gtoks = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env0 uu____9989 t_norm uu____9991 -> (match (((uu____9989), (uu____9991))) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = uu____10014; FStar_Syntax_Syntax.lbunivs = uu____10015; FStar_Syntax_Syntax.lbtyp = uu____10016; FStar_Syntax_Syntax.lbeff = uu____10017; FStar_Syntax_Syntax.lbdef = e}) -> begin
(

let uu____10034 = (destruct_bound_function flid t_norm e)
in (match (uu____10034) with
| ((binders, body, formals, tres), curry) -> begin
((match (curry) with
| true -> begin
(failwith "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type")
end
| uu____10088 -> begin
()
end);
(

let uu____10089 = (encode_binders None binders env)
in (match (uu____10089) with
| (vars, guards, env', binder_decls, uu____10107) -> begin
(

let decl_g = FStar_SMTEncoding_Term.DeclFun ((let _0_834 = (let _0_833 = (FStar_List.map Prims.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::_0_833)
in ((g), (_0_834), (FStar_SMTEncoding_Term.Term_sort), (Some ("Fuel-instrumented function name")))))
in (

let env0 = (push_zfuel_name env0 flid g)
in (

let decl_g_tok = FStar_SMTEncoding_Term.DeclFun (((gtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Token for fuel-instrumented partial applications"))))
in (

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let app = (FStar_SMTEncoding_Util.mkApp (let _0_835 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (_0_835))))
in (

let gsapp = (FStar_SMTEncoding_Util.mkApp (let _0_837 = (let _0_836 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (_0_836)::vars_tm)
in ((g), (_0_837))))
in (

let gmax = (FStar_SMTEncoding_Util.mkApp (let _0_839 = (let _0_838 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (_0_838)::vars_tm)
in ((g), (_0_839))))
in (

let uu____10137 = (encode_term body env')
in (match (uu____10137) with
| (body_tm, decls2) -> begin
(

let eqn_g = FStar_SMTEncoding_Term.Assume ((let _0_842 = (FStar_SMTEncoding_Util.mkForall' (let _0_840 = (FStar_SMTEncoding_Util.mkEq ((gsapp), (body_tm)))
in ((((gsapp)::[])::[]), (Some ((Prims.parse_int "0"))), ((fuel)::vars), (_0_840))))
in (let _0_841 = Some ((FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str))
in ((_0_842), (_0_841), (Some ((Prims.strcat "equation_with_fuel_" g)))))))
in (

let eqn_f = FStar_SMTEncoding_Term.Assume ((let _0_844 = (FStar_SMTEncoding_Util.mkForall (let _0_843 = (FStar_SMTEncoding_Util.mkEq ((app), (gmax)))
in ((((app)::[])::[]), (vars), (_0_843))))
in ((_0_844), (Some ("Correspondence of recursive function to instrumented version")), (Some ((Prims.strcat "fuel_correspondence_" g))))))
in (

let eqn_g' = FStar_SMTEncoding_Term.Assume ((let _0_849 = (FStar_SMTEncoding_Util.mkForall (let _0_848 = (FStar_SMTEncoding_Util.mkEq (let _0_847 = (FStar_SMTEncoding_Util.mkApp (let _0_846 = (let _0_845 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "0"))
in (_0_845)::vars_tm)
in ((g), (_0_846))))
in ((gsapp), (_0_847))))
in ((((gsapp)::[])::[]), ((fuel)::vars), (_0_848))))
in ((_0_849), (Some ("Fuel irrelevance")), (Some ((Prims.strcat "fuel_irrelevance_" g))))))
in (

let uu____10181 = (

let uu____10186 = (encode_binders None formals env0)
in (match (uu____10186) with
| (vars, v_guards, env, binder_decls, uu____10203) -> begin
(

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let gapp = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::vars_tm)))
in (

let tok_corr = (

let tok_app = (let _0_850 = (FStar_SMTEncoding_Util.mkFreeV ((gtok), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply _0_850 ((fuel)::vars)))
in FStar_SMTEncoding_Term.Assume ((let _0_852 = (FStar_SMTEncoding_Util.mkForall (let _0_851 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (gapp)))
in ((((tok_app)::[])::[]), ((fuel)::vars), (_0_851))))
in ((_0_852), (Some ("Fuel token correspondence")), (Some ((Prims.strcat "fuel_token_correspondence_" gtok)))))))
in (

let uu____10231 = (

let uu____10235 = (encode_term_pred None tres env gapp)
in (match (uu____10235) with
| (g_typing, d3) -> begin
(let _0_857 = (let _0_856 = FStar_SMTEncoding_Term.Assume ((let _0_855 = (FStar_SMTEncoding_Util.mkForall (let _0_854 = (FStar_SMTEncoding_Util.mkImp (let _0_853 = (FStar_SMTEncoding_Util.mk_and_l v_guards)
in ((_0_853), (g_typing))))
in ((((gapp)::[])::[]), ((fuel)::vars), (_0_854))))
in ((_0_855), (Some ("Typing correspondence of token to term")), (Some ((Prims.strcat "token_correspondence_" g))))))
in (_0_856)::[])
in ((d3), (_0_857)))
end))
in (match (uu____10231) with
| (aux_decls, typing_corr) -> begin
(((FStar_List.append binder_decls aux_decls)), ((FStar_List.append typing_corr ((tok_corr)::[]))))
end)))))
end))
in (match (uu____10181) with
| (aux_decls, g_typing) -> begin
(((FStar_List.append binder_decls (FStar_List.append decls2 (FStar_List.append aux_decls ((decl_g)::(decl_g_tok)::[]))))), ((FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing)), (env0))
end)))))
end)))))))))
end));
)
end))
end))
in (

let uu____10278 = (let _0_858 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun uu____10300 uu____10301 -> (match (((uu____10300), (uu____10301))) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(

let uu____10377 = (encode_one_binding env0 gtok ty bs)
in (match (uu____10377) with
| (decls', eqns', env0) -> begin
(((decls')::decls), ((FStar_List.append eqns' eqns)), (env0))
end))
end)) (((decls)::[]), ([]), (env0)) _0_858))
in (match (uu____10278) with
| (decls, eqns, env0) -> begin
(

let uu____10423 = (let _0_859 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _0_859 (FStar_List.partition (fun uu___124_10436 -> (match (uu___124_10436) with
| FStar_SMTEncoding_Term.DeclFun (uu____10437) -> begin
true
end
| uu____10443 -> begin
false
end)))))
in (match (uu____10423) with
| (prefix_decls, rest) -> begin
(

let eqns = (FStar_List.rev eqns)
in (((FStar_List.append prefix_decls (FStar_List.append rest eqns))), (env0)))
end))
end))))
end)))))
end)
end))))))
end))
end))
end)
with
| Let_rec_unencodeable -> begin
(

let msg = (let _0_860 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _0_860 (FStar_String.concat " and ")))
in (

let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in (((decl)::[]), (env))))
end))
end))


let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> ((

let uu____10492 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____10492) with
| true -> begin
(let _0_861 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _0_861))
end
| uu____10493 -> begin
()
end));
(

let nm = (match ((FStar_Syntax_Util.lid_of_sigelt se)) with
| None -> begin
""
end
| Some (l) -> begin
l.FStar_Ident.str
end)
in (

let uu____10496 = (encode_sigelt' env se)
in (match (uu____10496) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _0_863 = (let _0_862 = FStar_SMTEncoding_Term.Caption ((FStar_Util.format1 "<Skipped %s/>" nm))
in (_0_862)::[])
in ((_0_863), (e)))
end
| uu____10506 -> begin
(let _0_868 = (let _0_867 = (let _0_864 = FStar_SMTEncoding_Term.Caption ((FStar_Util.format1 "<Start encoding %s>" nm))
in (_0_864)::g)
in (let _0_866 = (let _0_865 = FStar_SMTEncoding_Term.Caption ((FStar_Util.format1 "</end encoding %s>" nm))
in (_0_865)::[])
in (FStar_List.append _0_867 _0_866)))
in ((_0_868), (e)))
end)
end)));
))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let should_skip = (fun l -> false)
in (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____10518) -> begin
(failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, uu____10529) -> begin
(

let uu____10530 = (let _0_869 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right _0_869 Prims.op_Negation))
in (match (uu____10530) with
| true -> begin
(([]), (env))
end
| uu____10535 -> begin
(

let close_effect_params = (fun tm -> (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
tm
end
| uu____10550 -> begin
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs ((let _0_871 = (FStar_All.pipe_left (fun _0_870 -> Some (_0_870)) (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[])))))
in ((ed.FStar_Syntax_Syntax.binders), (tm), (_0_871)))))) None tm.FStar_Syntax_Syntax.pos)
end))
in (

let encode_action = (fun env a -> (

let uu____10597 = (new_term_constant_and_tok_from_lid env a.FStar_Syntax_Syntax.action_name)
in (match (uu____10597) with
| (aname, atok, env) -> begin
(

let uu____10607 = (FStar_Syntax_Util.arrow_formals_comp a.FStar_Syntax_Syntax.action_typ)
in (match (uu____10607) with
| (formals, uu____10617) -> begin
(

let uu____10624 = (let _0_872 = (close_effect_params a.FStar_Syntax_Syntax.action_defn)
in (encode_term _0_872 env))
in (match (uu____10624) with
| (tm, decls) -> begin
(

let a_decls = (let _0_874 = FStar_SMTEncoding_Term.DeclFun ((let _0_873 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____10642 -> FStar_SMTEncoding_Term.Term_sort)))
in ((aname), (_0_873), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action")))))
in (_0_874)::(FStar_SMTEncoding_Term.DeclFun (((atok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action token")))))::[])
in (

let uu____10647 = (let _0_875 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____10679 -> (match (uu____10679) with
| (bv, uu____10687) -> begin
(

let uu____10688 = (gen_term_var env bv)
in (match (uu____10688) with
| (xxsym, xx, uu____10698) -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (xx))
end))
end))))
in (FStar_All.pipe_right _0_875 FStar_List.split))
in (match (uu____10647) with
| (xs_sorts, xs) -> begin
(

let app = (FStar_SMTEncoding_Util.mkApp (let _0_877 = (let _0_876 = (FStar_SMTEncoding_Util.mkApp ((aname), (xs)))
in (_0_876)::[])
in (("Reify"), (_0_877))))
in (

let a_eq = FStar_SMTEncoding_Term.Assume ((let _0_880 = (FStar_SMTEncoding_Util.mkForall (let _0_879 = (FStar_SMTEncoding_Util.mkEq (let _0_878 = (mk_Apply tm xs_sorts)
in ((app), (_0_878))))
in ((((app)::[])::[]), (xs_sorts), (_0_879))))
in ((_0_880), (Some ("Action equality")), (Some ((Prims.strcat aname "_equality"))))))
in (

let tok_correspondence = (

let tok_term = (FStar_SMTEncoding_Util.mkFreeV ((atok), (FStar_SMTEncoding_Term.Term_sort)))
in (

let tok_app = (mk_Apply tok_term xs_sorts)
in FStar_SMTEncoding_Term.Assume ((let _0_882 = (FStar_SMTEncoding_Util.mkForall (let _0_881 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (app)))
in ((((tok_app)::[])::[]), (xs_sorts), (_0_881))))
in ((_0_882), (Some ("Action token correspondence")), (Some ((Prims.strcat aname "_token_correspondence"))))))))
in ((env), ((FStar_List.append decls (FStar_List.append a_decls ((a_eq)::(tok_correspondence)::[]))))))))
end)))
end))
end))
end)))
in (

let uu____10742 = (FStar_Util.fold_map encode_action env ed.FStar_Syntax_Syntax.actions)
in (match (uu____10742) with
| (env, decls2) -> begin
(((FStar_List.flatten decls2)), (env))
end))))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____10758, uu____10759, uu____10760, uu____10761) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid) -> begin
(

let uu____10764 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____10764) with
| (tname, ttok, env) -> begin
(([]), (env))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____10775, t, quals, uu____10778) -> begin
(

let will_encode_definition = (not ((FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___125_10783 -> (match (uu___125_10783) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Irreducible) -> begin
true
end
| uu____10786 -> begin
false
end))))))
in (match (will_encode_definition) with
| true -> begin
(([]), (env))
end
| uu____10790 -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____10792 = (encode_top_level_val env fv t quals)
in (match (uu____10792) with
| (decls, env) -> begin
(

let tname = lid.FStar_Ident.str
in (

let tsym = (FStar_SMTEncoding_Util.mkFreeV ((tname), (FStar_SMTEncoding_Term.Term_sort)))
in (let _0_884 = (let _0_883 = (primitive_type_axioms env.tcenv lid tname tsym)
in (FStar_List.append decls _0_883))
in ((_0_884), (env)))))
end)))
end))
end
| FStar_Syntax_Syntax.Sig_assume (l, f, uu____10807, uu____10808) -> begin
(

let uu____10811 = (encode_formula f env)
in (match (uu____10811) with
| (f, decls) -> begin
(

let g = (let _0_888 = FStar_SMTEncoding_Term.Assume ((let _0_887 = Some ((let _0_885 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" _0_885)))
in (let _0_886 = Some ((varops.mk_unique (Prims.strcat "assumption_" l.FStar_Ident.str)))
in ((f), (_0_887), (_0_886)))))
in (_0_888)::[])
in (((FStar_List.append decls g)), (env)))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, uu____10825, quals, uu____10827) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) -> begin
(

let uu____10835 = (FStar_Util.fold_map (fun env lb -> (

let lid = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname).FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____10846 = (let _0_889 = (FStar_TypeChecker_Env.try_lookup_val_decl env.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone _0_889))
in (match (uu____10846) with
| true -> begin
(

let val_decl = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), (r)))
in (

let uu____10861 = (encode_sigelt' env val_decl)
in (match (uu____10861) with
| (decls, env) -> begin
((env), (decls))
end)))
end
| uu____10868 -> begin
((env), ([]))
end)))) env (Prims.snd lbs))
in (match (uu____10835) with
| (env, decls) -> begin
(((FStar_List.flatten decls)), (env))
end))
end
| FStar_Syntax_Syntax.Sig_let ((uu____10878, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t); FStar_Syntax_Syntax.lbunivs = uu____10880; FStar_Syntax_Syntax.lbtyp = uu____10881; FStar_Syntax_Syntax.lbeff = uu____10882; FStar_Syntax_Syntax.lbdef = uu____10883})::[]), uu____10884, uu____10885, uu____10886, uu____10887) when (FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Syntax_Const.b2t_lid) -> begin
(

let uu____10903 = (new_term_constant_and_tok_from_lid env b2t.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____10903) with
| (tname, ttok, env) -> begin
(

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let valid_b2t_x = (FStar_SMTEncoding_Util.mkApp (let _0_891 = (let _0_890 = (FStar_SMTEncoding_Util.mkApp (("Prims.b2t"), ((x)::[])))
in (_0_890)::[])
in (("Valid"), (_0_891))))
in (

let decls = (let _0_896 = (let _0_895 = FStar_SMTEncoding_Term.Assume ((let _0_894 = (FStar_SMTEncoding_Util.mkForall (let _0_893 = (FStar_SMTEncoding_Util.mkEq (let _0_892 = (FStar_SMTEncoding_Util.mkApp (("BoxBool_proj_0"), ((x)::[])))
in ((valid_b2t_x), (_0_892))))
in ((((valid_b2t_x)::[])::[]), ((xx)::[]), (_0_893))))
in ((_0_894), (Some ("b2t def")), (Some ("b2t_def")))))
in (_0_895)::[])
in (FStar_SMTEncoding_Term.DeclFun (((tname), ((FStar_SMTEncoding_Term.Term_sort)::[]), (FStar_SMTEncoding_Term.Term_sort), (None))))::_0_896)
in ((decls), (env))))))
end))
end
| FStar_Syntax_Syntax.Sig_let (uu____10942, uu____10943, uu____10944, quals, uu____10946) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___126_10954 -> (match (uu___126_10954) with
| FStar_Syntax_Syntax.Discriminator (uu____10955) -> begin
true
end
| uu____10956 -> begin
false
end)))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let (uu____10958, uu____10959, lids, quals, uu____10962) when ((FStar_All.pipe_right lids (FStar_Util.for_some (fun l -> (let _0_897 = (FStar_List.hd l.FStar_Ident.ns).FStar_Ident.idText
in (_0_897 = "Prims"))))) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___127_10972 -> (match (uu___127_10972) with
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
true
end
| uu____10973 -> begin
false
end))))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____10976, uu____10977, quals, uu____10979) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___128_10991 -> (match (uu___128_10991) with
| FStar_Syntax_Syntax.Projector (uu____10992) -> begin
true
end
| uu____10995 -> begin
false
end)))) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____11002 = (try_lookup_free_var env l)
in (match (uu____11002) with
| Some (uu____11006) -> begin
(([]), (env))
end
| None -> begin
(

let se = FStar_Syntax_Syntax.Sig_declare_typ (((l), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), ((FStar_Ident.range_of_lid l))))
in (encode_sigelt env se))
end))))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____11014, uu____11015, quals, uu____11017) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) -> begin
(

let uu____11029 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n
in (match (uu____11029) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____11034) -> begin
(

let body = (FStar_Syntax_Util.mk_reify body)
in (

let tm = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None))))) None lb.FStar_Syntax_Syntax.lbdef.FStar_Syntax_Syntax.pos)
in (

let tm' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env.tcenv tm)
in (

let lb_typ = (

let uu____11091 = (FStar_Syntax_Util.arrow_formals_comp lb.FStar_Syntax_Syntax.lbtyp)
in (match (uu____11091) with
| (formals, comp) -> begin
(

let reified_typ = (FStar_TypeChecker_Util.reify_comp (

let uu___154_11108 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___154_11108.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___154_11108.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___154_11108.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___154_11108.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___154_11108.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___154_11108.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___154_11108.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___154_11108.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___154_11108.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___154_11108.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___154_11108.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___154_11108.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___154_11108.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___154_11108.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___154_11108.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___154_11108.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___154_11108.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___154_11108.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___154_11108.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___154_11108.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___154_11108.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___154_11108.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___154_11108.FStar_TypeChecker_Env.qname_and_index}) (FStar_Syntax_Util.lcomp_of_comp comp) FStar_Syntax_Syntax.U_unknown)
in (let _0_898 = (FStar_Syntax_Syntax.mk_Total reified_typ)
in (FStar_Syntax_Util.arrow formals _0_898)))
end))
in (

let lb = (

let uu___155_11110 = lb
in {FStar_Syntax_Syntax.lbname = uu___155_11110.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___155_11110.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lb_typ; FStar_Syntax_Syntax.lbeff = uu___155_11110.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = tm'})
in ((let _0_901 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _0_900 = (FStar_Syntax_Print.term_to_string tm)
in (let _0_899 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print3 "%s: Reified %s\nto %s\n" _0_901 _0_900 _0_899))));
(encode_top_level_let env ((false), ((lb)::[])) quals);
))))))
end
| uu____11113 -> begin
(([]), (env))
end))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), uu____11117, uu____11118, quals, uu____11120) -> begin
(encode_top_level_let env ((is_rec), (bindings)) quals)
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____11134, uu____11135, uu____11136) -> begin
(

let uu____11143 = (encode_signature env ses)
in (match (uu____11143) with
| (g, env) -> begin
(

let uu____11153 = (FStar_All.pipe_right g (FStar_List.partition (fun uu___129_11163 -> (match (uu___129_11163) with
| FStar_SMTEncoding_Term.Assume (uu____11164, Some ("inversion axiom"), uu____11165) -> begin
false
end
| uu____11169 -> begin
true
end))))
in (match (uu____11153) with
| (g', inversions) -> begin
(

let uu____11178 = (FStar_All.pipe_right g' (FStar_List.partition (fun uu___130_11188 -> (match (uu___130_11188) with
| FStar_SMTEncoding_Term.DeclFun (uu____11189) -> begin
true
end
| uu____11195 -> begin
false
end))))
in (match (uu____11178) with
| (decls, rest) -> begin
(((FStar_List.append decls (FStar_List.append rest inversions))), (env))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, uu____11206, tps, k, uu____11209, datas, quals, uu____11212) -> begin
(

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___131_11221 -> (match (uu___131_11221) with
| (FStar_Syntax_Syntax.Logic) | (FStar_Syntax_Syntax.Assumption) -> begin
true
end
| uu____11222 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> (match (is_logical) with
| true -> begin
(

let uu____11245 = c
in (match (uu____11245) with
| (name, args, uu____11257, uu____11258, uu____11259) -> begin
(let _0_903 = FStar_SMTEncoding_Term.DeclFun ((let _0_902 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in ((name), (_0_902), (FStar_SMTEncoding_Term.Term_sort), (None))))
in (_0_903)::[])
end))
end
| uu____11274 -> begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end))
in (

let inversion_axioms = (fun tapp vars -> (

let uu____11289 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _0_904 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right _0_904 FStar_Option.isNone)))))
in (match (uu____11289) with
| true -> begin
[]
end
| uu____11298 -> begin
(

let uu____11299 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____11299) with
| (xxsym, xx) -> begin
(

let uu____11305 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun uu____11316 l -> (match (uu____11316) with
| (out, decls) -> begin
(

let uu____11328 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (uu____11328) with
| (uu____11334, data_t) -> begin
(

let uu____11336 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (uu____11336) with
| (args, res) -> begin
(

let indices = (

let uu____11365 = (FStar_Syntax_Subst.compress res).FStar_Syntax_Syntax.n
in (match (uu____11365) with
| FStar_Syntax_Syntax.Tm_app (uu____11371, indices) -> begin
indices
end
| uu____11387 -> begin
[]
end))
in (

let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env uu____11399 -> (match (uu____11399) with
| (x, uu____11403) -> begin
(let _0_906 = (FStar_SMTEncoding_Util.mkApp (let _0_905 = (mk_term_projector_name l x)
in ((_0_905), ((xx)::[]))))
in (push_term_var env x _0_906))
end)) env))
in (

let uu____11405 = (encode_args indices env)
in (match (uu____11405) with
| (indices, decls') -> begin
((match (((FStar_List.length indices) <> (FStar_List.length vars))) with
| true -> begin
(failwith "Impossible")
end
| uu____11423 -> begin
()
end);
(

let eqs = (let _0_908 = (FStar_List.map2 (fun v a -> (FStar_SMTEncoding_Util.mkEq (let _0_907 = (FStar_SMTEncoding_Util.mkFreeV v)
in ((_0_907), (a))))) vars indices)
in (FStar_All.pipe_right _0_908 FStar_SMTEncoding_Util.mk_and_l))
in (let _0_911 = (FStar_SMTEncoding_Util.mkOr (let _0_910 = (FStar_SMTEncoding_Util.mkAnd (let _0_909 = (mk_data_tester env l xx)
in ((_0_909), (eqs))))
in ((out), (_0_910))))
in ((_0_911), ((FStar_List.append decls decls')))));
)
end))))
end))
end))
end)) ((FStar_SMTEncoding_Util.mkFalse), ([]))))
in (match (uu____11305) with
| (data_ax, decls) -> begin
(

let uu____11439 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____11439) with
| (ffsym, ff) -> begin
(

let fuel_guarded_inversion = (

let xx_has_type_sfuel = (match (((FStar_List.length datas) > (Prims.parse_int "1"))) with
| true -> begin
(let _0_912 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((ff)::[])))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel _0_912 xx tapp))
end
| uu____11451 -> begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end)
in FStar_SMTEncoding_Term.Assume ((let _0_916 = (FStar_SMTEncoding_Util.mkForall (let _0_914 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (let _0_913 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_sfuel), (data_ax)))
in ((((xx_has_type_sfuel)::[])::[]), (_0_914), (_0_913)))))
in (let _0_915 = Some ((varops.mk_unique (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str)))
in ((_0_916), (Some ("inversion axiom")), (_0_915))))))
in (

let pattern_guarded_inversion = (

let uu____11467 = ((contains_name env "Prims.inversion") && ((FStar_List.length datas) > (Prims.parse_int "1")))
in (match (uu____11467) with
| true -> begin
(

let xx_has_type_fuel = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let pattern_guard = (FStar_SMTEncoding_Util.mkApp (("Prims.inversion"), ((tapp)::[])))
in (let _0_921 = FStar_SMTEncoding_Term.Assume ((let _0_920 = (FStar_SMTEncoding_Util.mkForall (let _0_918 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (let _0_917 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_fuel), (data_ax)))
in ((((xx_has_type_fuel)::(pattern_guard)::[])::[]), (_0_918), (_0_917)))))
in (let _0_919 = Some ((varops.mk_unique (Prims.strcat "pattern_guarded_inversion_" t.FStar_Ident.str)))
in ((_0_920), (Some ("inversion axiom")), (_0_919)))))
in (_0_921)::[])))
end
| uu____11488 -> begin
[]
end))
in (FStar_List.append decls (FStar_List.append ((fuel_guarded_inversion)::[]) pattern_guarded_inversion))))
end))
end))
end))
end)))
in (

let uu____11489 = (

let uu____11497 = (FStar_Syntax_Subst.compress k).FStar_Syntax_Syntax.n
in (match (uu____11497) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
(((FStar_List.append tps formals)), ((FStar_Syntax_Util.comp_result kres)))
end
| uu____11524 -> begin
((tps), (k))
end))
in (match (uu____11489) with
| (formals, res) -> begin
(

let uu____11539 = (FStar_Syntax_Subst.open_term formals res)
in (match (uu____11539) with
| (formals, res) -> begin
(

let uu____11546 = (encode_binders None formals env)
in (match (uu____11546) with
| (vars, guards, env', binder_decls, uu____11561) -> begin
(

let uu____11568 = (new_term_constant_and_tok_from_lid env t)
in (match (uu____11568) with
| (tname, ttok, env) -> begin
(

let ttok_tm = (FStar_SMTEncoding_Util.mkApp ((ttok), ([])))
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let tapp = (FStar_SMTEncoding_Util.mkApp (let _0_922 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((tname), (_0_922))))
in (

let uu____11584 = (

let tname_decl = (constructor_or_logic_type_decl (let _0_924 = (FStar_All.pipe_right vars (FStar_List.map (fun uu____11601 -> (match (uu____11601) with
| (n, s) -> begin
(((Prims.strcat tname n)), (s))
end))))
in (let _0_923 = (varops.next_id ())
in ((tname), (_0_924), (FStar_SMTEncoding_Term.Term_sort), (_0_923), (false)))))
in (

let uu____11608 = (match (vars) with
| [] -> begin
(let _0_928 = (let _0_927 = (let _0_926 = (FStar_SMTEncoding_Util.mkApp ((tname), ([])))
in (FStar_All.pipe_left (fun _0_925 -> Some (_0_925)) _0_926))
in (push_free_var env t tname _0_927))
in (([]), (_0_928)))
end
| uu____11618 -> begin
(

let ttok_decl = FStar_SMTEncoding_Term.DeclFun (((ttok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("token"))))
in (

let ttok_fresh = (let _0_929 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ttok), (FStar_SMTEncoding_Term.Term_sort)) _0_929))
in (

let ttok_app = (mk_Apply ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = FStar_SMTEncoding_Term.Assume ((let _0_931 = (FStar_SMTEncoding_Util.mkForall' (let _0_930 = (FStar_SMTEncoding_Util.mkEq ((ttok_app), (tapp)))
in ((pats), (None), (vars), (_0_930))))
in ((_0_931), (Some ("name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" ttok))))))
in (((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[]), (env)))))))
end)
in (match (uu____11608) with
| (tok_decls, env) -> begin
(((FStar_List.append tname_decl tok_decls)), (env))
end)))
in (match (uu____11584) with
| (decls, env) -> begin
(

let kindingAx = (

let uu____11655 = (encode_term_pred None res env' tapp)
in (match (uu____11655) with
| (k, decls) -> begin
(

let karr = (match (((FStar_List.length formals) > (Prims.parse_int "0"))) with
| true -> begin
(let _0_934 = FStar_SMTEncoding_Term.Assume ((let _0_933 = (let _0_932 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _0_932))
in ((_0_933), (Some ("kinding")), (Some ((Prims.strcat "pre_kinding_" ttok))))))
in (_0_934)::[])
end
| uu____11671 -> begin
[]
end)
in (let _0_939 = (let _0_938 = (let _0_937 = FStar_SMTEncoding_Term.Assume ((let _0_936 = (FStar_SMTEncoding_Util.mkForall (let _0_935 = (FStar_SMTEncoding_Util.mkImp ((guard), (k)))
in ((((tapp)::[])::[]), (vars), (_0_935))))
in ((_0_936), (None), (Some ((Prims.strcat "kinding_" ttok))))))
in (_0_937)::[])
in (FStar_List.append karr _0_938))
in (FStar_List.append decls _0_939)))
end))
in (

let aux = (let _0_943 = (let _0_942 = (inversion_axioms tapp vars)
in (let _0_941 = (let _0_940 = (pretype_axiom tapp vars)
in (_0_940)::[])
in (FStar_List.append _0_942 _0_941)))
in (FStar_List.append kindingAx _0_943))
in (

let g = (FStar_List.append decls (FStar_List.append binder_decls aux))
in ((g), (env)))))
end)))))
end))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____11685, uu____11686, uu____11687, uu____11688, uu____11689, uu____11690, uu____11691) when (FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____11698, t, uu____11700, n_tps, quals, uu____11703, drange) -> begin
(

let uu____11709 = (new_term_constant_and_tok_from_lid env d)
in (match (uu____11709) with
| (ddconstrsym, ddtok, env) -> begin
(

let ddtok_tm = (FStar_SMTEncoding_Util.mkApp ((ddtok), ([])))
in (

let uu____11720 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____11720) with
| (formals, t_res) -> begin
(

let uu____11742 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____11742) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (

let uu____11751 = (encode_binders (Some (fuel_tm)) formals env)
in (match (uu____11751) with
| (vars, guards, env', binder_decls, names) -> begin
(

let projectors = (FStar_All.pipe_right names (FStar_List.map (fun x -> (let _0_944 = (mk_term_projector_name d x)
in ((_0_944), (FStar_SMTEncoding_Term.Term_sort))))))
in (

let datacons = (let _0_946 = (let _0_945 = (varops.next_id ())
in ((ddconstrsym), (projectors), (FStar_SMTEncoding_Term.Term_sort), (_0_945), (true)))
in (FStar_All.pipe_right _0_946 FStar_SMTEncoding_Term.constructor_to_decl))
in (

let app = (mk_Apply ddtok_tm vars)
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (

let uu____11804 = (encode_term_pred None t env ddtok_tm)
in (match (uu____11804) with
| (tok_typing, decls3) -> begin
(

let uu____11811 = (encode_binders (Some (fuel_tm)) formals env)
in (match (uu____11811) with
| (vars', guards', env'', decls_formals, uu____11826) -> begin
(

let uu____11833 = (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars')
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (encode_term_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (uu____11833) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_SMTEncoding_Util.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| uu____11852 -> begin
(let _0_948 = (let _0_947 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ddtok), (FStar_SMTEncoding_Term.Term_sort)) _0_947))
in (_0_948)::[])
end)
in (

let encode_elim = (fun uu____11862 -> (

let uu____11863 = (FStar_Syntax_Util.head_and_args t_res)
in (match (uu____11863) with
| (head, args) -> begin
(

let uu____11892 = (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n
in (match (uu____11892) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let uu____11908 = (encode_args args env')
in (match (uu____11908) with
| (encoded_args, arg_decls) -> begin
(

let uu____11919 = (FStar_List.fold_left (fun uu____11930 arg -> (match (uu____11930) with
| (env, arg_vars, eqns) -> begin
(

let uu____11949 = (let _0_949 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in (gen_term_var env _0_949))
in (match (uu____11949) with
| (uu____11958, xv, env) -> begin
(let _0_951 = (let _0_950 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (_0_950)::eqns)
in ((env), ((xv)::arg_vars), (_0_951)))
end))
end)) ((env'), ([]), ([])) encoded_args)
in (match (uu____11919) with
| (uu____11968, arg_vars, eqns) -> begin
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

let typing_inversion = FStar_SMTEncoding_Term.Assume ((let _0_955 = (FStar_SMTEncoding_Util.mkForall (let _0_954 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (let _0_953 = (FStar_SMTEncoding_Util.mkImp (let _0_952 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append eqns guards))
in ((ty_pred), (_0_952))))
in ((((ty_pred)::[])::[]), (_0_954), (_0_953)))))
in ((_0_955), (Some ("data constructor typing elim")), (Some ((Prims.strcat "data_elim_" ddconstrsym))))))
in (

let subterm_ordering = (match ((FStar_Ident.lid_equals d FStar_Syntax_Const.lextop_lid)) with
| true -> begin
(

let x = (let _0_956 = (varops.fresh "x")
in ((_0_956), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in FStar_SMTEncoding_Term.Assume ((let _0_964 = (FStar_SMTEncoding_Util.mkForall (let _0_962 = (let _0_958 = (let _0_957 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp)
in (_0_957)::[])
in (_0_958)::[])
in (let _0_961 = (FStar_SMTEncoding_Util.mkImp (let _0_960 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (let _0_959 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp)
in ((_0_960), (_0_959)))))
in ((_0_962), ((x)::[]), (_0_961)))))
in (let _0_963 = Some ((varops.mk_unique "lextop"))
in ((_0_964), (Some ("lextop is top")), (_0_963)))))))
end
| uu____12018 -> begin
(

let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
[]
end
| FStar_SMTEncoding_Term.Term_sort -> begin
(let _0_966 = (let _0_965 = (FStar_SMTEncoding_Util.mkFreeV v)
in (FStar_SMTEncoding_Util.mk_Precedes _0_965 dapp))
in (_0_966)::[])
end
| uu____12029 -> begin
(failwith "unexpected sort")
end))))
in FStar_SMTEncoding_Term.Assume ((let _0_970 = (FStar_SMTEncoding_Util.mkForall (let _0_969 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (let _0_968 = (FStar_SMTEncoding_Util.mkImp (let _0_967 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (_0_967))))
in ((((ty_pred)::[])::[]), (_0_969), (_0_968)))))
in ((_0_970), (Some ("subterm ordering")), (Some ((Prims.strcat "subterm_ordering_" ddconstrsym)))))))
end)
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end))
end)))
end
| uu____12043 -> begin
((let _0_973 = (let _0_972 = (FStar_Syntax_Print.lid_to_string d)
in (let _0_971 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _0_972 _0_971)))
in (FStar_Errors.warn drange _0_973));
(([]), ([]));
)
end))
end)))
in (

let uu____12047 = (encode_elim ())
in (match (uu____12047) with
| (decls2, elim) -> begin
(

let g = (let _0_994 = (let _0_993 = (let _0_992 = (let _0_991 = (let _0_976 = FStar_SMTEncoding_Term.DeclFun ((let _0_975 = Some ((let _0_974 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" _0_974)))
in ((ddtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (_0_975))))
in (_0_976)::[])
in (let _0_990 = (let _0_989 = (let _0_988 = (let _0_987 = (let _0_986 = (let _0_985 = (let _0_984 = FStar_SMTEncoding_Term.Assume ((let _0_978 = (FStar_SMTEncoding_Util.mkForall (let _0_977 = (FStar_SMTEncoding_Util.mkEq ((app), (dapp)))
in ((((app)::[])::[]), (vars), (_0_977))))
in ((_0_978), (Some ("equality for proxy")), (Some ((Prims.strcat "equality_tok_" ddtok))))))
in (let _0_983 = (let _0_982 = FStar_SMTEncoding_Term.Assume ((let _0_981 = (FStar_SMTEncoding_Util.mkForall (let _0_980 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) vars')
in (let _0_979 = (FStar_SMTEncoding_Util.mkImp ((guard'), (ty_pred')))
in ((((ty_pred')::[])::[]), (_0_980), (_0_979)))))
in ((_0_981), (Some ("data constructor typing intro")), (Some ((Prims.strcat "data_typing_intro_" ddtok))))))
in (_0_982)::[])
in (_0_984)::_0_983))
in (FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("typing for data constructor proxy")), (Some ((Prims.strcat "typing_tok_" ddtok))))))::_0_985)
in (FStar_List.append _0_986 elim))
in (FStar_List.append decls_pred _0_987))
in (FStar_List.append decls_formals _0_988))
in (FStar_List.append proxy_fresh _0_989))
in (FStar_List.append _0_991 _0_990)))
in (FStar_List.append decls3 _0_992))
in (FStar_List.append decls2 _0_993))
in (FStar_List.append binder_decls _0_994))
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
and encode_signature : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun uu____12092 se -> (match (uu____12092) with
| (g, env) -> begin
(

let uu____12104 = (encode_sigelt env se)
in (match (uu____12104) with
| (g', env) -> begin
(((FStar_List.append g g')), (env))
end))
end)) (([]), (env)))))


let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env bindings -> (

let encode_binding = (fun b uu____12140 -> (match (uu____12140) with
| (i, decls, env) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (uu____12158) -> begin
(((i + (Prims.parse_int "1"))), ([]), (env))
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in ((

let uu____12163 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____12163) with
| true -> begin
(let _0_997 = (FStar_Syntax_Print.bv_to_string x)
in (let _0_996 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _0_995 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" _0_997 _0_996 _0_995))))
end
| uu____12164 -> begin
()
end));
(

let uu____12165 = (encode_term t1 env)
in (match (uu____12165) with
| (t, decls') -> begin
(

let t_hash = (FStar_SMTEncoding_Term.hash_of_term t)
in (

let uu____12175 = (let _0_1002 = (let _0_1001 = (let _0_1000 = (FStar_Util.digest_of_string t_hash)
in (let _0_999 = (let _0_998 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _0_998))
in (Prims.strcat _0_1000 _0_999)))
in (Prims.strcat "x_" _0_1001))
in (new_term_constant_from_string env x _0_1002))
in (match (uu____12175) with
| (xxsym, xx, env') -> begin
(

let t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel None xx t)
in (

let caption = (

let uu____12189 = (FStar_Options.log_queries ())
in (match (uu____12189) with
| true -> begin
Some ((let _0_1005 = (FStar_Syntax_Print.bv_to_string x)
in (let _0_1004 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _0_1003 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _0_1005 _0_1004 _0_1003)))))
end
| uu____12191 -> begin
None
end))
in (

let ax = (

let a_name = Some ((Prims.strcat "binder_" xxsym))
in FStar_SMTEncoding_Term.Assume (((t), (a_name), (a_name))))
in (

let g = (FStar_List.append ((FStar_SMTEncoding_Term.DeclFun (((xxsym), ([]), (FStar_SMTEncoding_Term.Term_sort), (caption))))::[]) (FStar_List.append decls' ((ax)::[])))
in (((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))))))
end)))
end));
))
end
| FStar_TypeChecker_Env.Binding_lid (x, (uu____12203, t)) -> begin
(

let t_norm = (whnf env t)
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____12212 = (encode_free_var env fv t t_norm [])
in (match (uu____12212) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))))
end
| (FStar_TypeChecker_Env.Binding_sig_inst (_, se, _)) | (FStar_TypeChecker_Env.Binding_sig (_, se)) -> begin
(

let uu____12231 = (encode_sigelt env se)
in (match (uu____12231) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))
end)
end))
in (

let uu____12241 = (FStar_List.fold_right encode_binding bindings (((Prims.parse_int "0")), ([]), (env)))
in (match (uu____12241) with
| (uu____12253, decls, env) -> begin
((decls), (env))
end))))


let encode_labels = (fun labs -> (

let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun uu____12298 -> (match (uu____12298) with
| (l, uu____12305, uu____12306) -> begin
FStar_SMTEncoding_Term.DeclFun ((((Prims.fst l)), ([]), (FStar_SMTEncoding_Term.Bool_sort), (None)))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun uu____12327 -> (match (uu____12327) with
| (l, uu____12335, uu____12336) -> begin
(let _0_1009 = (FStar_All.pipe_left (fun _0_1006 -> FStar_SMTEncoding_Term.Echo (_0_1006)) (Prims.fst l))
in (let _0_1008 = (let _0_1007 = FStar_SMTEncoding_Term.Eval ((FStar_SMTEncoding_Util.mkFreeV l))
in (_0_1007)::[])
in (_0_1009)::_0_1008))
end))))
in ((prefix), (suffix)))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (let _0_1012 = (let _0_1011 = (let _0_1010 = (FStar_Util.smap_create (Prims.parse_int "100"))
in {bindings = []; depth = (Prims.parse_int "0"); tcenv = tcenv; warn = true; cache = _0_1010; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_0_1011)::[])
in (FStar_ST.write last_env _0_1012)))


let get_env : FStar_TypeChecker_Env.env  ->  env_t = (fun tcenv -> (

let uu____12362 = (FStar_ST.read last_env)
in (match (uu____12362) with
| [] -> begin
(failwith "No env; call init first!")
end
| (e)::uu____12368 -> begin
(

let uu___156_12370 = e
in {bindings = uu___156_12370.bindings; depth = uu___156_12370.depth; tcenv = tcenv; warn = uu___156_12370.warn; cache = uu___156_12370.cache; nolabels = uu___156_12370.nolabels; use_zfuel_name = uu___156_12370.use_zfuel_name; encode_non_total_function_typ = uu___156_12370.encode_non_total_function_typ})
end)))


let set_env : env_t  ->  Prims.unit = (fun env -> (

let uu____12374 = (FStar_ST.read last_env)
in (match (uu____12374) with
| [] -> begin
(failwith "Empty env stack")
end
| (uu____12379)::tl -> begin
(FStar_ST.write last_env ((env)::tl))
end)))


let push_env : Prims.unit  ->  Prims.unit = (fun uu____12387 -> (

let uu____12388 = (FStar_ST.read last_env)
in (match (uu____12388) with
| [] -> begin
(failwith "Empty env stack")
end
| (hd)::tl -> begin
(

let refs = (FStar_Util.smap_copy hd.cache)
in (

let top = (

let uu___157_12409 = hd
in {bindings = uu___157_12409.bindings; depth = uu___157_12409.depth; tcenv = uu___157_12409.tcenv; warn = uu___157_12409.warn; cache = refs; nolabels = uu___157_12409.nolabels; use_zfuel_name = uu___157_12409.use_zfuel_name; encode_non_total_function_typ = uu___157_12409.encode_non_total_function_typ})
in (FStar_ST.write last_env ((top)::(hd)::tl))))
end)))


let pop_env : Prims.unit  ->  Prims.unit = (fun uu____12415 -> (

let uu____12416 = (FStar_ST.read last_env)
in (match (uu____12416) with
| [] -> begin
(failwith "Popping an empty stack")
end
| (uu____12421)::tl -> begin
(FStar_ST.write last_env tl)
end)))


let mark_env : Prims.unit  ->  Prims.unit = (fun uu____12429 -> (push_env ()))


let reset_mark_env : Prims.unit  ->  Prims.unit = (fun uu____12432 -> (pop_env ()))


let commit_mark_env : Prims.unit  ->  Prims.unit = (fun uu____12435 -> (

let uu____12436 = (FStar_ST.read last_env)
in (match (uu____12436) with
| (hd)::(uu____12442)::tl -> begin
(FStar_ST.write last_env ((hd)::tl))
end
| uu____12448 -> begin
(failwith "Impossible")
end)))


let init : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> ((init_env tcenv);
(FStar_SMTEncoding_Z3.init ());
(FStar_SMTEncoding_Z3.giveZ3 ((FStar_SMTEncoding_Term.DefPrelude)::[]));
))


let push : Prims.string  ->  Prims.unit = (fun msg -> ((push_env ());
(varops.push ());
(FStar_SMTEncoding_Z3.push msg);
))


let pop : Prims.string  ->  Prims.unit = (fun msg -> ((pop_env ());
(varops.pop ());
(FStar_SMTEncoding_Z3.pop msg);
))


let mark : Prims.string  ->  Prims.unit = (fun msg -> ((mark_env ());
(varops.mark ());
(FStar_SMTEncoding_Z3.mark msg);
))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> ((reset_mark_env ());
(varops.reset_mark ());
(FStar_SMTEncoding_Z3.reset_mark msg);
))


let commit_mark : Prims.string  ->  Prims.unit = (fun msg -> ((commit_mark_env ());
(varops.commit_mark ());
(FStar_SMTEncoding_Z3.commit_mark msg);
))


let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (

let caption = (fun decls -> (

let uu____12493 = (FStar_Options.log_queries ())
in (match (uu____12493) with
| true -> begin
(let _0_1015 = FStar_SMTEncoding_Term.Caption ((let _0_1014 = (let _0_1013 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.map FStar_Syntax_Print.lid_to_string))
in (FStar_All.pipe_right _0_1013 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " _0_1014)))
in (_0_1015)::decls)
end
| uu____12498 -> begin
decls
end)))
in (

let env = (get_env tcenv)
in (

let uu____12500 = (encode_sigelt env se)
in (match (uu____12500) with
| (decls, env) -> begin
((set_env env);
(FStar_SMTEncoding_Z3.giveZ3 (caption decls));
)
end)))))


let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____12513 -> begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in ((

let uu____12515 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____12515) with
| true -> begin
(let _0_1016 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name _0_1016))
end
| uu____12518 -> begin
()
end));
(

let env = (get_env tcenv)
in (

let uu____12520 = (encode_signature (

let uu___158_12524 = env
in {bindings = uu___158_12524.bindings; depth = uu___158_12524.depth; tcenv = uu___158_12524.tcenv; warn = false; cache = uu___158_12524.cache; nolabels = uu___158_12524.nolabels; use_zfuel_name = uu___158_12524.use_zfuel_name; encode_non_total_function_typ = uu___158_12524.encode_non_total_function_typ}) modul.FStar_Syntax_Syntax.exports)
in (match (uu____12520) with
| (decls, env) -> begin
(

let caption = (fun decls -> (

let uu____12536 = (FStar_Options.log_queries ())
in (match (uu____12536) with
| true -> begin
(

let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::decls) ((FStar_SMTEncoding_Term.Caption ((Prims.strcat "End " msg)))::[])))
end
| uu____12539 -> begin
decls
end)))
in ((set_env (

let uu___159_12541 = env
in {bindings = uu___159_12541.bindings; depth = uu___159_12541.depth; tcenv = uu___159_12541.tcenv; warn = true; cache = uu___159_12541.cache; nolabels = uu___159_12541.nolabels; use_zfuel_name = uu___159_12541.use_zfuel_name; encode_non_total_function_typ = uu___159_12541.encode_non_total_function_typ}));
(

let uu____12543 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____12543) with
| true -> begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end
| uu____12544 -> begin
()
end));
(

let decls = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls));
))
end)));
)))


let encode_query : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_ErrorReporting.label Prims.list * FStar_SMTEncoding_Term.decl * FStar_SMTEncoding_Term.decl Prims.list) = (fun use_env_msg tcenv q -> ((FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name (FStar_TypeChecker_Env.current_module tcenv).FStar_Ident.str);
(

let env = (get_env tcenv)
in (

let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (

let uu____12585 = (

let rec aux = (fun bindings -> (match (bindings) with
| (FStar_TypeChecker_Env.Binding_var (x))::rest -> begin
(

let uu____12606 = (aux rest)
in (match (uu____12606) with
| (out, rest) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (let _0_1018 = (let _0_1017 = (FStar_Syntax_Syntax.mk_binder (

let uu___160_12624 = x
in {FStar_Syntax_Syntax.ppname = uu___160_12624.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___160_12624.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_0_1017)::out)
in ((_0_1018), (rest))))
end))
end
| uu____12625 -> begin
(([]), (bindings))
end))
in (

let uu____12629 = (aux bindings)
in (match (uu____12629) with
| (closing, bindings) -> begin
(let _0_1019 = (FStar_Syntax_Util.close_forall (FStar_List.rev closing) q)
in ((_0_1019), (bindings)))
end)))
in (match (uu____12585) with
| (q, bindings) -> begin
(

let uu____12655 = (let _0_1020 = (FStar_List.filter (fun uu___132_12658 -> (match (uu___132_12658) with
| FStar_TypeChecker_Env.Binding_sig (uu____12659) -> begin
false
end
| uu____12663 -> begin
true
end)) bindings)
in (encode_env_bindings env _0_1020))
in (match (uu____12655) with
| (env_decls, env) -> begin
((

let uu____12674 = (((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTQuery"))))
in (match (uu____12674) with
| true -> begin
(let _0_1021 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" _0_1021))
end
| uu____12675 -> begin
()
end));
(

let uu____12676 = (encode_formula q env)
in (match (uu____12676) with
| (phi, qdecls) -> begin
(

let uu____12688 = (let _0_1022 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg _0_1022 phi))
in (match (uu____12688) with
| (labels, phi) -> begin
(

let uu____12700 = (encode_labels labels)
in (match (uu____12700) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append env_decls (FStar_List.append label_prefix qdecls))
in (

let qry = FStar_SMTEncoding_Term.Assume ((let _0_1024 = (FStar_SMTEncoding_Util.mkNot phi)
in (let _0_1023 = Some ((varops.mk_unique "@query"))
in ((_0_1024), (Some ("query")), (_0_1023)))))
in (

let suffix = (let _0_1026 = (let _0_1025 = (

let uu____12725 = (FStar_Options.print_z3_statistics ())
in (match (uu____12725) with
| true -> begin
(FStar_SMTEncoding_Term.PrintStats)::[]
end
| uu____12727 -> begin
[]
end))
in (FStar_List.append _0_1025 ((FStar_SMTEncoding_Term.Echo ("Done!"))::[])))
in (FStar_List.append label_suffix _0_1026))
in ((query_prelude), (labels), (qry), (suffix)))))
end))
end))
end));
)
end))
end))));
))


let is_trivial : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun tcenv q -> (

let env = (get_env tcenv)
in ((FStar_SMTEncoding_Z3.push "query");
(

let uu____12738 = (encode_formula q env)
in (match (uu____12738) with
| (f, uu____12742) -> begin
((FStar_SMTEncoding_Z3.pop "query");
(match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____12744) -> begin
true
end
| uu____12747 -> begin
false
end);
)
end));
)))




