
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
Some (FStar_Util.Inl ((let _0_247 = (let _0_246 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp s _0_246))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _0_247))))
end
| uu____121 -> begin
l
end))


let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s '\'' '_'))


let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun lid a -> (

let a = (

let uu___133_135 = a
in (let _0_248 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _0_248; FStar_Syntax_Syntax.index = uu___133_135.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___133_135.FStar_Syntax_Syntax.sort}))
in (let _0_249 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str a.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (FStar_All.pipe_left escape _0_249))))


let primitive_projector_by_pos : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (

let fail = (fun uu____148 -> (failwith (let _0_250 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" _0_250 lid.FStar_Ident.str))))
in (

let uu____149 = (FStar_TypeChecker_Env.lookup_datacon env lid)
in (match (uu____149) with
| (uu____152, t) -> begin
(

let uu____154 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____154) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____167 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____167) with
| (binders, uu____171) -> begin
(match (((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders)))) with
| true -> begin
(fail ())
end
| uu____176 -> begin
(

let b = (FStar_List.nth binders i)
in (mk_term_projector_name lid (Prims.fst b)))
end)
end))
end
| uu____182 -> begin
(fail ())
end))
end))))


let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (let _0_252 = (let _0_251 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str _0_251))
in (FStar_All.pipe_left escape _0_252)))


let mk_term_projector : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun lid a -> (FStar_SMTEncoding_Util.mkFreeV (let _0_253 = (mk_term_projector_name lid a)
in ((_0_253), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))))


let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_SMTEncoding_Term.term = (fun lid i -> (FStar_SMTEncoding_Util.mkFreeV (let _0_254 = (mk_term_projector_name_by_pos lid i)
in ((_0_254), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))))


let mk_data_tester = (fun env l x -> (FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x))

type varops_t =
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; mark : Prims.unit  ->  Prims.unit; reset_mark : Prims.unit  ->  Prims.unit; commit_mark : Prims.unit  ->  Prims.unit; new_var : FStar_Ident.ident  ->  Prims.int  ->  Prims.string; new_fvar : FStar_Ident.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_SMTEncoding_Term.term; next_id : Prims.unit  ->  Prims.int; mk_unique : Prims.string  ->  Prims.string}


let varops : varops_t = (

let initial_ctr = (Prims.parse_int "100")
in (

let ctr = (FStar_Util.mk_ref initial_ctr)
in (

let new_scope = (fun uu____390 -> (let _0_256 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (let _0_255 = (FStar_Util.smap_create (Prims.parse_int "100"))
in ((_0_256), (_0_255)))))
in (

let scopes = (FStar_Util.mk_ref (let _0_257 = (new_scope ())
in (_0_257)::[]))
in (

let mk_unique = (fun y -> (

let y = (escape y)
in (

let y = (

let uu____420 = (let _0_258 = (FStar_ST.read scopes)
in (FStar_Util.find_map _0_258 (fun uu____433 -> (match (uu____433) with
| (names, uu____440) -> begin
(FStar_Util.smap_try_find names y)
end))))
in (match (uu____420) with
| None -> begin
y
end
| Some (uu____445) -> begin
((FStar_Util.incr ctr);
(let _0_260 = (let _0_259 = (FStar_Util.string_of_int (FStar_ST.read ctr))
in (Prims.strcat "__" _0_259))
in (Prims.strcat y _0_260));
)
end))
in (

let top_scope = (let _0_261 = (FStar_List.hd (FStar_ST.read scopes))
in (FStar_All.pipe_left Prims.fst _0_261))
in ((FStar_Util.smap_add top_scope y true);
y;
)))))
in (

let new_var = (fun pp rn -> (let _0_264 = (let _0_263 = (let _0_262 = (FStar_Util.string_of_int rn)
in (Prims.strcat "__" _0_262))
in (Prims.strcat pp.FStar_Ident.idText _0_263))
in (FStar_All.pipe_left mk_unique _0_264)))
in (

let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (

let next_id = (fun uu____487 -> ((FStar_Util.incr ctr);
(FStar_ST.read ctr);
))
in (

let fresh = (fun pfx -> (let _0_266 = (let _0_265 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _0_265))
in (FStar_Util.format2 "%s_%s" pfx _0_266)))
in (

let string_const = (fun s -> (

let uu____502 = (let _0_267 = (FStar_ST.read scopes)
in (FStar_Util.find_map _0_267 (fun uu____515 -> (match (uu____515) with
| (uu____521, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))
in (match (uu____502) with
| Some (f) -> begin
f
end
| None -> begin
(

let id = (next_id ())
in (

let f = (let _0_268 = (FStar_SMTEncoding_Util.mk_String_const id)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString _0_268))
in (

let top_scope = (let _0_269 = (FStar_List.hd (FStar_ST.read scopes))
in (FStar_All.pipe_left Prims.snd _0_269))
in ((FStar_Util.smap_add top_scope s f);
f;
))))
end)))
in (

let push = (fun uu____554 -> (let _0_272 = (let _0_271 = (new_scope ())
in (let _0_270 = (FStar_ST.read scopes)
in (_0_271)::_0_270))
in (FStar_ST.write scopes _0_272)))
in (

let pop = (fun uu____576 -> (let _0_273 = (FStar_List.tl (FStar_ST.read scopes))
in (FStar_ST.write scopes _0_273)))
in (

let mark = (fun uu____598 -> (push ()))
in (

let reset_mark = (fun uu____602 -> (pop ()))
in (

let commit_mark = (fun uu____606 -> (

let uu____607 = (FStar_ST.read scopes)
in (match (uu____607) with
| ((hd1, hd2))::((next1, next2))::tl -> begin
((FStar_Util.smap_fold hd1 (fun key value v -> (FStar_Util.smap_add next1 key value)) ());
(FStar_Util.smap_fold hd2 (fun key value v -> (FStar_Util.smap_add next2 key value)) ());
(FStar_ST.write scopes ((((next1), (next2)))::tl));
)
end
| uu____667 -> begin
(failwith "Impossible")
end)))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id; mk_unique = mk_unique})))))))))))))))


let unmangle : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv = (fun x -> (

let uu___134_676 = x
in (let _0_274 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _0_274; FStar_Syntax_Syntax.index = uu___134_676.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___134_676.FStar_Syntax_Syntax.sort})))

type binding =
| Binding_var of (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term)
| Binding_fvar of (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option)


let uu___is_Binding_var : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Binding_var (_0) -> begin
true
end
| uu____697 -> begin
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
| uu____721 -> begin
false
end))


let __proj__Binding_fvar__item___0 : binding  ->  (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun projectee -> (match (projectee) with
| Binding_fvar (_0) -> begin
_0
end))


let binder_of_eithervar = (fun v -> ((v), (None)))

type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_TypeChecker_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_SMTEncoding_Term.sort Prims.list * FStar_SMTEncoding_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}


let print_env : env_t  ->  Prims.string = (fun e -> (let _0_275 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun uu___109_843 -> (match (uu___109_843) with
| Binding_var (x, uu____845) -> begin
(FStar_Syntax_Print.bv_to_string x)
end
| Binding_fvar (l, uu____847, uu____848, uu____849) -> begin
(FStar_Syntax_Print.lid_to_string l)
end))))
in (FStar_All.pipe_right _0_275 (FStar_String.concat ", "))))


let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))


let caption_t : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.string Prims.option = (fun env t -> (

let uu____881 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____881) with
| true -> begin
Some ((FStar_Syntax_Print.term_to_string t))
end
| uu____883 -> begin
None
end)))


let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (

let xsym = (varops.fresh x)
in (let _0_276 = (FStar_SMTEncoding_Util.mkFreeV ((xsym), (s)))
in ((xsym), (_0_276)))))


let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (let _0_277 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _0_277))
in (

let y = (FStar_SMTEncoding_Util.mkFreeV ((ysym), (FStar_SMTEncoding_Term.Term_sort)))
in ((ysym), (y), ((

let uu___135_904 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = (env.depth + (Prims.parse_int "1")); tcenv = uu___135_904.tcenv; warn = uu___135_904.warn; cache = uu___135_904.cache; nolabels = uu___135_904.nolabels; use_zfuel_name = uu___135_904.use_zfuel_name; encode_non_total_function_typ = uu___135_904.encode_non_total_function_typ}))))))


let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let uu___136_917 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = uu___136_917.depth; tcenv = uu___136_917.tcenv; warn = uu___136_917.warn; cache = uu___136_917.cache; nolabels = uu___136_917.nolabels; use_zfuel_name = uu___136_917.use_zfuel_name; encode_non_total_function_typ = uu___136_917.encode_non_total_function_typ}))))))


let new_term_constant_from_string : env_t  ->  FStar_Syntax_Syntax.bv  ->  Prims.string  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x str -> (

let ysym = (varops.mk_unique str)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let uu___137_933 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = uu___137_933.depth; tcenv = uu___137_933.tcenv; warn = uu___137_933.warn; cache = uu___137_933.cache; nolabels = uu___137_933.nolabels; use_zfuel_name = uu___137_933.use_zfuel_name; encode_non_total_function_typ = uu___137_933.encode_non_total_function_typ}))))))


let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (

let uu___138_943 = env
in {bindings = (Binding_var (((x), (t))))::env.bindings; depth = uu___138_943.depth; tcenv = uu___138_943.tcenv; warn = uu___138_943.warn; cache = uu___138_943.cache; nolabels = uu___138_943.nolabels; use_zfuel_name = uu___138_943.use_zfuel_name; encode_non_total_function_typ = uu___138_943.encode_non_total_function_typ}))


let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let aux = (fun a' -> (lookup_binding env (fun uu___110_959 -> (match (uu___110_959) with
| Binding_var (b, t) when (FStar_Syntax_Syntax.bv_eq b a') -> begin
Some (((b), (t)))
end
| uu____967 -> begin
None
end))))
in (

let uu____970 = (aux a)
in (match (uu____970) with
| None -> begin
(

let a = (unmangle a)
in (

let uu____977 = (aux a)
in (match (uu____977) with
| None -> begin
(failwith (let _0_278 = (FStar_Syntax_Print.bv_to_string a)
in (FStar_Util.format1 "Bound term variable not found (after unmangling): %s" _0_278)))
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
in (let _0_284 = (

let uu___139_1002 = env
in (let _0_283 = (let _0_282 = Binding_fvar ((let _0_281 = (let _0_280 = (FStar_SMTEncoding_Util.mkApp ((ftok), ([])))
in (FStar_All.pipe_left (fun _0_279 -> Some (_0_279)) _0_280))
in ((x), (fname), (_0_281), (None))))
in (_0_282)::env.bindings)
in {bindings = _0_283; depth = uu___139_1002.depth; tcenv = uu___139_1002.tcenv; warn = uu___139_1002.warn; cache = uu___139_1002.cache; nolabels = uu___139_1002.nolabels; use_zfuel_name = uu___139_1002.use_zfuel_name; encode_non_total_function_typ = uu___139_1002.encode_non_total_function_typ}))
in ((fname), (ftok), (_0_284))))))


let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun uu___111_1024 -> (match (uu___111_1024) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some (((t1), (t2), (t3)))
end
| uu____1046 -> begin
None
end))))


let contains_name : env_t  ->  Prims.string  ->  Prims.bool = (fun env s -> (let _0_285 = (lookup_binding env (fun uu___112_1059 -> (match (uu___112_1059) with
| Binding_fvar (b, t1, t2, t3) when (b.FStar_Ident.str = s) -> begin
Some (())
end
| uu____1069 -> begin
None
end)))
in (FStar_All.pipe_right _0_285 FStar_Option.isSome)))


let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun env a -> (

let uu____1081 = (try_lookup_lid env a)
in (match (uu____1081) with
| None -> begin
(failwith (let _0_286 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" _0_286)))
end
| Some (s) -> begin
s
end)))


let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (

let uu___140_1128 = env
in {bindings = (Binding_fvar (((x), (fname), (ftok), (None))))::env.bindings; depth = uu___140_1128.depth; tcenv = uu___140_1128.tcenv; warn = uu___140_1128.warn; cache = uu___140_1128.cache; nolabels = uu___140_1128.nolabels; use_zfuel_name = uu___140_1128.use_zfuel_name; encode_non_total_function_typ = uu___140_1128.encode_non_total_function_typ}))


let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (

let uu____1140 = (lookup_lid env x)
in (match (uu____1140) with
| (t1, t2, uu____1148) -> begin
(

let t3 = (FStar_SMTEncoding_Util.mkApp (let _0_288 = (let _0_287 = (FStar_SMTEncoding_Util.mkApp (("ZFuel"), ([])))
in (_0_287)::[])
in ((f), (_0_288))))
in (

let uu___141_1156 = env
in {bindings = (Binding_fvar (((x), (t1), (t2), (Some (t3)))))::env.bindings; depth = uu___141_1156.depth; tcenv = uu___141_1156.tcenv; warn = uu___141_1156.warn; cache = uu___141_1156.cache; nolabels = uu___141_1156.nolabels; use_zfuel_name = uu___141_1156.use_zfuel_name; encode_non_total_function_typ = uu___141_1156.encode_non_total_function_typ}))
end)))


let try_lookup_free_var : env_t  ->  FStar_Ident.lident  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env l -> (

let uu____1166 = (try_lookup_lid env l)
in (match (uu____1166) with
| None -> begin
None
end
| Some (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some (f) when env.use_zfuel_name -> begin
Some (f)
end
| uu____1193 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (uu____1198, (fuel)::[]) -> begin
(

let uu____1201 = (let _0_290 = (let _0_289 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right _0_289 Prims.fst))
in (FStar_Util.starts_with _0_290 "fuel"))
in (match (uu____1201) with
| true -> begin
(let _0_293 = (let _0_292 = (FStar_SMTEncoding_Util.mkFreeV ((name), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_ApplyTF _0_292 fuel))
in (FStar_All.pipe_left (fun _0_291 -> Some (_0_291)) _0_293))
end
| uu____1204 -> begin
Some (t)
end))
end
| uu____1205 -> begin
Some (t)
end)
end
| uu____1206 -> begin
None
end)
end)
end)))


let lookup_free_var = (fun env a -> (

let uu____1224 = (try_lookup_free_var env a.FStar_Syntax_Syntax.v)
in (match (uu____1224) with
| Some (t) -> begin
t
end
| None -> begin
(failwith (let _0_294 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _0_294)))
end)))


let lookup_free_var_name = (fun env a -> (

let uu____1243 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (uu____1243) with
| (x, uu____1250, uu____1251) -> begin
x
end)))


let lookup_free_var_sym = (fun env a -> (

let uu____1275 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (uu____1275) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.freevars = uu____1296; FStar_SMTEncoding_Term.rng = uu____1297}) when env.use_zfuel_name -> begin
((g), (zf))
end
| uu____1305 -> begin
(match (sym) with
| None -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end
| Some (sym) -> begin
(match (sym.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, (fuel)::[]) -> begin
((g), ((fuel)::[]))
end
| uu____1319 -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end)
end)
end)
end)))


let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun uu___113_1328 -> (match (uu___113_1328) with
| Binding_fvar (uu____1330, nm', tok, uu____1333) when (nm = nm') -> begin
tok
end
| uu____1338 -> begin
None
end))))


let mkForall_fuel' = (fun n uu____1355 -> (match (uu____1355) with
| (pats, vars, body) -> begin
(

let fallback = (fun uu____1371 -> (FStar_SMTEncoding_Util.mkForall ((pats), (vars), (body))))
in (

let uu____1374 = (FStar_Options.unthrottle_inductives ())
in (match (uu____1374) with
| true -> begin
(fallback ())
end
| uu____1375 -> begin
(

let uu____1376 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____1376) with
| (fsym, fterm) -> begin
(

let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Util.mkApp (("HasTypeFuel"), ((fterm)::args)))
end
| uu____1395 -> begin
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
| uu____1409 -> begin
(let _0_295 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _0_295 FStar_List.hd))
end)
in (FStar_SMTEncoding_Util.mkImp ((guard), (body'))))
end
| uu____1411 -> begin
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
(let _0_296 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _0_296 FStar_Option.isNone))
end
| uu____1464 -> begin
false
end)))


let head_redex : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let uu____1471 = (FStar_Syntax_Util.un_uinst t).FStar_Syntax_Syntax.n
in (match (uu____1471) with
| FStar_Syntax_Syntax.Tm_abs (uu____1472, uu____1473, Some (FStar_Util.Inr (l, flags))) -> begin
(((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid)) || (FStar_List.existsb (fun uu___114_1502 -> (match (uu___114_1502) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____1503 -> begin
false
end)) flags))
end
| FStar_Syntax_Syntax.Tm_abs (uu____1504, uu____1505, Some (FStar_Util.Inl (lc))) -> begin
(FStar_Syntax_Util.is_tot_or_gtot_lcomp lc)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(let _0_297 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _0_297 FStar_Option.isSome))
end
| uu____1541 -> begin
false
end)))


let whnf : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____1548 = (head_normal env t)
in (match (uu____1548) with
| true -> begin
t
end
| uu____1549 -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
end)))


let norm : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t))


let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (let _0_300 = (let _0_298 = (FStar_Syntax_Syntax.null_binder t)
in (_0_298)::[])
in (let _0_299 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Util.abs _0_300 _0_299 None))))


let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(let _0_301 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out _0_301))
end
| s -> begin
(

let _0_302 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Util.mk_ApplyTT out _0_302))
end)) e)))


let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)))


let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun uu___115_1598 -> (match (uu___115_1598) with
| (FStar_SMTEncoding_Term.Var ("ApplyTT")) | (FStar_SMTEncoding_Term.Var ("ApplyTF")) -> begin
true
end
| uu____1599 -> begin
false
end))


let is_eta : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env vars t -> (

let rec aux = (fun t xs -> (match (((t.FStar_SMTEncoding_Term.tm), (xs))) with
| (FStar_SMTEncoding_Term.App (app, (f)::({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.freevars = uu____1627; FStar_SMTEncoding_Term.rng = uu____1628})::[]), (x)::xs) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), uu____1642) -> begin
(

let uu____1647 = (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v)
end
| uu____1657 -> begin
false
end)) args vars))
in (match (uu____1647) with
| true -> begin
(tok_of_name env f)
end
| uu____1659 -> begin
None
end))
end
| (uu____1660, []) -> begin
(

let fvs = (FStar_SMTEncoding_Term.free_variables t)
in (

let uu____1663 = (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (not ((FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars))))))
in (match (uu____1663) with
| true -> begin
Some (t)
end
| uu____1666 -> begin
None
end)))
end
| uu____1667 -> begin
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
| uu____1751 -> begin
false
end))


let encode_const : FStar_Const.sconst  ->  FStar_SMTEncoding_Term.term = (fun uu___116_1754 -> (match (uu___116_1754) with
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
(FStar_SMTEncoding_Util.mkApp (let _0_304 = (let _0_303 = (FStar_SMTEncoding_Term.boxInt (FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c)))
in (_0_303)::[])
in (("FStar.Char.Char"), (_0_304))))
end
| FStar_Const.Const_int (i, None) -> begin
(FStar_SMTEncoding_Term.boxInt (FStar_SMTEncoding_Util.mkInteger i))
end
| FStar_Const.Const_int (i, Some (uu____1764)) -> begin
(failwith "Machine integers should be desugared")
end
| FStar_Const.Const_string (bytes, uu____1773) -> begin
(varops.string_const (FStar_All.pipe_left FStar_Util.string_of_bytes bytes))
end
| FStar_Const.Const_range (r) -> begin
FStar_SMTEncoding_Term.mk_Range_const
end
| FStar_Const.Const_effect -> begin
FStar_SMTEncoding_Term.mk_Term_type
end
| c -> begin
(failwith (let _0_305 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" _0_305)))
end))


let as_function_typ : env_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (

let rec aux = (fun norm t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1797) -> begin
t
end
| FStar_Syntax_Syntax.Tm_refine (uu____1805) -> begin
(let _0_306 = (FStar_Syntax_Util.unrefine t)
in (aux true _0_306))
end
| uu____1810 -> begin
(match (norm) with
| true -> begin
(let _0_307 = (whnf env t)
in (aux false _0_307))
end
| uu____1811 -> begin
(failwith (let _0_309 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (let _0_308 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _0_309 _0_308))))
end)
end)))
in (aux true t0)))


let curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun k -> (

let k = (FStar_Syntax_Subst.compress k)
in (match (k.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| uu____1832 -> begin
(let _0_310 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (_0_310)))
end)))


let rec encode_binders : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> ((

let uu____1975 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____1975) with
| true -> begin
(let _0_311 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" _0_311))
end
| uu____1976 -> begin
()
end));
(

let uu____1977 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____2013 b -> (match (uu____2013) with
| (vars, guards, env, decls, names) -> begin
(

let uu____2056 = (

let x = (unmangle (Prims.fst b))
in (

let uu____2065 = (gen_term_var env x)
in (match (uu____2065) with
| (xxsym, xx, env') -> begin
(

let uu____2079 = (let _0_312 = (norm env x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt _0_312 env xx))
in (match (uu____2079) with
| (guard_x_t, decls') -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (guard_x_t), (env'), (decls'), (x))
end))
end)))
in (match (uu____2056) with
| (v, g, env, decls', n) -> begin
(((v)::vars), ((g)::guards), (env), ((FStar_List.append decls decls')), ((n)::names))
end))
end)) (([]), ([]), (env), ([]), ([]))))
in (match (uu____1977) with
| (vars, guards, env, decls, names) -> begin
(((FStar_List.rev vars)), ((FStar_List.rev guards)), (env), (decls), ((FStar_List.rev names)))
end));
))
and encode_term_pred : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let uu____2169 = (encode_term t env)
in (match (uu____2169) with
| (t, decls) -> begin
(let _0_313 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t)
in ((_0_313), (decls)))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let uu____2183 = (encode_term t env)
in (match (uu____2183) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _0_314 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t)
in ((_0_314), (decls)))
end
| Some (f) -> begin
(let _0_315 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t)
in ((_0_315), (decls)))
end)
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let t0 = (FStar_Syntax_Subst.compress t)
in ((

let uu____2199 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____2199) with
| true -> begin
(let _0_318 = (FStar_Syntax_Print.tag_of_term t)
in (let _0_317 = (FStar_Syntax_Print.tag_of_term t0)
in (let _0_316 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" _0_318 _0_317 _0_316))))
end
| uu____2200 -> begin
()
end));
(match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(failwith (let _0_322 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (let _0_321 = (FStar_Syntax_Print.tag_of_term t0)
in (let _0_320 = (FStar_Syntax_Print.term_to_string t0)
in (let _0_319 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _0_322 _0_321 _0_320 _0_319))))))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(failwith (let _0_323 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" _0_323)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, k, uu____2211) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____2231) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t = (lookup_term_var env x)
in ((t), ([])))
end
| FStar_Syntax_Syntax.Tm_fvar (v) -> begin
(let _0_324 = (lookup_free_var env v.FStar_Syntax_Syntax.fv_name)
in ((_0_324), ([])))
end
| FStar_Syntax_Syntax.Tm_type (uu____2245) -> begin
((FStar_SMTEncoding_Term.mk_Term_type), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t, uu____2248) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(let _0_325 = (encode_const c)
in ((_0_325), ([])))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____2267 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____2267) with
| (binders, res) -> begin
(

let uu____2274 = ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res))
in (match (uu____2274) with
| true -> begin
(

let uu____2277 = (encode_binders None binders env)
in (match (uu____2277) with
| (vars, guards, env', decls, uu____2292) -> begin
(

let fsym = (let _0_326 = (varops.fresh "f")
in ((_0_326), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV fsym)
in (

let app = (mk_Apply f vars)
in (

let uu____2304 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post (

let uu___142_2308 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___142_2308.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___142_2308.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___142_2308.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___142_2308.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___142_2308.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___142_2308.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___142_2308.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___142_2308.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___142_2308.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___142_2308.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___142_2308.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___142_2308.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___142_2308.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___142_2308.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___142_2308.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___142_2308.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___142_2308.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___142_2308.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___142_2308.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___142_2308.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___142_2308.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___142_2308.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___142_2308.FStar_TypeChecker_Env.qname_and_index}) res)
in (match (uu____2304) with
| (pre_opt, res_t) -> begin
(

let uu____2315 = (encode_term_pred None res_t env' app)
in (match (uu____2315) with
| (res_pred, decls') -> begin
(

let uu____2322 = (match (pre_opt) with
| None -> begin
(let _0_327 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((_0_327), ([])))
end
| Some (pre) -> begin
(

let uu____2331 = (encode_formula pre env')
in (match (uu____2331) with
| (guard, decls0) -> begin
(let _0_328 = (FStar_SMTEncoding_Util.mk_and_l ((guard)::guards))
in ((_0_328), (decls0)))
end))
end)
in (match (uu____2322) with
| (guards, guard_decls) -> begin
(

let t_interp = (FStar_SMTEncoding_Util.mkForall (let _0_329 = (FStar_SMTEncoding_Util.mkImp ((guards), (res_pred)))
in ((((app)::[])::[]), (vars), (_0_329))))
in (

let cvars = (let _0_330 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right _0_330 (FStar_List.filter (fun uu____2360 -> (match (uu____2360) with
| (x, uu____2364) -> begin
(x <> (Prims.fst fsym))
end)))))
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), ((fsym)::cvars), (t_interp)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____2375 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____2375) with
| Some (t', sorts, uu____2391) -> begin
(let _0_332 = (FStar_SMTEncoding_Util.mkApp (let _0_331 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((t'), (_0_331))))
in ((_0_332), ([])))
end
| None -> begin
(

let tsym = (varops.mk_unique (let _0_333 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_arrow_" _0_333)))
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let caption = (

let uu____2421 = (FStar_Options.log_queries ())
in (match (uu____2421) with
| true -> begin
Some ((FStar_TypeChecker_Normalize.term_to_string env.tcenv t0))
end
| uu____2423 -> begin
None
end))
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (caption)))
in (

let t = (FStar_SMTEncoding_Util.mkApp (let _0_334 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((tsym), (_0_334))))
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let k_assumption = (

let a_name = Some ((Prims.strcat "kinding_" tsym))
in FStar_SMTEncoding_Term.Assume ((let _0_335 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((_0_335), (a_name), (a_name)))))
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t)
in (

let pre_typing = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in FStar_SMTEncoding_Term.Assume ((let _0_339 = (mkForall_fuel (let _0_338 = (FStar_SMTEncoding_Util.mkImp (let _0_337 = (let _0_336 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _0_336))
in ((f_has_t), (_0_337))))
in ((((f_has_t)::[])::[]), ((fsym)::cvars), (_0_338))))
in ((_0_339), (Some ("pre-typing for functions")), (a_name)))))
in (

let t_interp = (

let a_name = Some ((Prims.strcat "interpretation_" tsym))
in FStar_SMTEncoding_Term.Assume ((let _0_341 = (FStar_SMTEncoding_Util.mkForall (let _0_340 = (FStar_SMTEncoding_Util.mkIff ((f_has_t_z), (t_interp)))
in ((((f_has_t_z)::[])::[]), ((fsym)::cvars), (_0_340))))
in ((_0_341), (a_name), (a_name)))))
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
| uu____2485 -> begin
(

let tsym = (varops.fresh "Non_total_Tm_arrow")
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let t = (FStar_SMTEncoding_Util.mkApp ((tsym), ([])))
in (

let t_kinding = (

let a_name = Some ((Prims.strcat "non_total_function_typing_" tsym))
in FStar_SMTEncoding_Term.Assume ((let _0_342 = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in ((_0_342), (Some ("Typing for non-total arrows")), (a_name)))))
in (

let fsym = (("f"), (FStar_SMTEncoding_Term.Term_sort))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV fsym)
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let t_interp = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in FStar_SMTEncoding_Term.Assume ((let _0_346 = (mkForall_fuel (let _0_345 = (FStar_SMTEncoding_Util.mkImp (let _0_344 = (let _0_343 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _0_343))
in ((f_has_t), (_0_344))))
in ((((f_has_t)::[])::[]), ((fsym)::[]), (_0_345))))
in ((_0_346), (a_name), (a_name)))))
in ((t), ((tdecl)::(t_kinding)::(t_interp)::[]))))))))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_refine (uu____2519) -> begin
(

let uu____2524 = (

let uu____2527 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)
in (match (uu____2527) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.tk = uu____2532; FStar_Syntax_Syntax.pos = uu____2533; FStar_Syntax_Syntax.vars = uu____2534} -> begin
(

let uu____2541 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) f)
in (match (uu____2541) with
| (b, f) -> begin
(let _0_347 = (Prims.fst (FStar_List.hd b))
in ((_0_347), (f)))
end))
end
| uu____2557 -> begin
(failwith "impossible")
end))
in (match (uu____2524) with
| (x, f) -> begin
(

let uu____2564 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (uu____2564) with
| (base_t, decls) -> begin
(

let uu____2571 = (gen_term_var env x)
in (match (uu____2571) with
| (x, xtm, env') -> begin
(

let uu____2580 = (encode_formula f env')
in (match (uu____2580) with
| (refinement, decls') -> begin
(

let uu____2587 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____2587) with
| (fsym, fterm) -> begin
(

let encoding = (FStar_SMTEncoding_Util.mkAnd (let _0_348 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in ((_0_348), (refinement))))
in (

let cvars = (let _0_349 = (FStar_SMTEncoding_Term.free_variables encoding)
in (FStar_All.pipe_right _0_349 (FStar_List.filter (fun uu____2604 -> (match (uu____2604) with
| (y, uu____2608) -> begin
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

let uu____2627 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____2627) with
| Some (t, uu____2642, uu____2643) -> begin
(let _0_351 = (FStar_SMTEncoding_Util.mkApp (let _0_350 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((t), (_0_350))))
in ((_0_351), ([])))
end
| None -> begin
(

let tsym = (varops.mk_unique (let _0_352 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_refine_" _0_352)))
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let t = (FStar_SMTEncoding_Util.mkApp (let _0_353 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((tsym), (_0_353))))
in (

let x_has_t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let t_haseq_base = (FStar_SMTEncoding_Term.mk_haseq base_t)
in (

let t_haseq_ref = (FStar_SMTEncoding_Term.mk_haseq t)
in (

let t_haseq = FStar_SMTEncoding_Term.Assume ((let _0_355 = (FStar_SMTEncoding_Util.mkForall (let _0_354 = (FStar_SMTEncoding_Util.mkIff ((t_haseq_ref), (t_haseq_base)))
in ((((t_haseq_ref)::[])::[]), (cvars), (_0_354))))
in ((_0_355), (Some ((Prims.strcat "haseq for " tsym))), (Some ((Prims.strcat "haseq" tsym))))))
in (

let t_kinding = FStar_SMTEncoding_Term.Assume ((let _0_356 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((_0_356), (Some ("refinement kinding")), (Some ((Prims.strcat "refinement_kinding_" tsym))))))
in (

let t_interp = FStar_SMTEncoding_Term.Assume ((let _0_359 = (FStar_SMTEncoding_Util.mkForall (let _0_357 = (FStar_SMTEncoding_Util.mkIff ((x_has_t), (encoding)))
in ((((x_has_t)::[])::[]), ((ffv)::(xfv)::cvars), (_0_357))))
in (let _0_358 = Some ((FStar_Syntax_Print.term_to_string t0))
in ((_0_359), (_0_358), (Some ((Prims.strcat "refinement_interpretation_" tsym)))))))
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

let uu____2745 = (encode_term_pred None k env ttm)
in (match (uu____2745) with
| (t_has_k, decls) -> begin
(

let d = FStar_SMTEncoding_Term.Assume ((let _0_362 = Some ((varops.mk_unique (let _0_361 = (let _0_360 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _0_360))
in (FStar_Util.format1 "uvar_typing_%s" _0_361))))
in ((t_has_k), (Some ("Uvar typing")), (_0_362))))
in ((ttm), ((FStar_List.append decls ((d)::[])))))
end)))
end
| FStar_Syntax_Syntax.Tm_app (uu____2759) -> begin
(

let uu____2769 = (FStar_Syntax_Util.head_and_args t0)
in (match (uu____2769) with
| (head, args_e) -> begin
(

let uu____2797 = (let _0_363 = (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n
in ((_0_363), (args_e)))
in (match (uu____2797) with
| (uu____2812, uu____2813) when (head_redex env head) -> begin
(let _0_364 = (whnf env t)
in (encode_term _0_364 env))
end
| ((FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), (_)::((v1, _))::((v2, _))::[])) | ((FStar_Syntax_Syntax.Tm_fvar (fv), (_)::((v1, _))::((v2, _))::[])) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
(

let uu____2897 = (encode_term v1 env)
in (match (uu____2897) with
| (v1, decls1) -> begin
(

let uu____2904 = (encode_term v2 env)
in (match (uu____2904) with
| (v2, decls2) -> begin
(let _0_365 = (FStar_SMTEncoding_Util.mk_LexCons v1 v2)
in ((_0_365), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), (uu____2912)::(uu____2913)::uu____2914) -> begin
(

let e0 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_367 = (let _0_366 = (FStar_List.hd args_e)
in (_0_366)::[])
in ((head), (_0_367)))))) None head.FStar_Syntax_Syntax.pos)
in (

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_368 = (FStar_List.tl args_e)
in ((e0), (_0_368)))))) None t0.FStar_Syntax_Syntax.pos)
in (encode_term e env)))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), ((arg, uu____2994))::[]) -> begin
(

let uu____3012 = (encode_term arg env)
in (match (uu____3012) with
| (tm, decls) -> begin
(let _0_369 = (FStar_SMTEncoding_Util.mkApp (("Reify"), ((tm)::[])))
in ((_0_369), (decls)))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____3020)), ((arg, uu____3022))::[]) -> begin
(encode_term arg env)
end
| uu____3040 -> begin
(

let uu____3048 = (encode_args args_e env)
in (match (uu____3048) with
| (args, decls) -> begin
(

let encode_partial_app = (fun ht_opt -> (

let uu____3081 = (encode_term head env)
in (match (uu____3081) with
| (head, decls') -> begin
(

let app_tm = (mk_Apply_args head args)
in (match (ht_opt) with
| None -> begin
((app_tm), ((FStar_List.append decls decls')))
end
| Some (formals, c) -> begin
(

let uu____3120 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (uu____3120) with
| (formals, rest) -> begin
(

let subst = (FStar_List.map2 (fun uu____3162 uu____3163 -> (match (((uu____3162), (uu____3163))) with
| ((bv, uu____3177), (a, uu____3179)) -> begin
FStar_Syntax_Syntax.NT (((bv), (a)))
end)) formals args_e)
in (

let ty = (let _0_370 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right _0_370 (FStar_Syntax_Subst.subst subst)))
in (

let uu____3195 = (encode_term_pred None ty env app_tm)
in (match (uu____3195) with
| (has_type, decls'') -> begin
(

let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (

let e_typing = FStar_SMTEncoding_Term.Assume ((let _0_373 = (FStar_SMTEncoding_Util.mkForall ((((has_type)::[])::[]), (cvars), (has_type)))
in (let _0_372 = Some ((varops.mk_unique (let _0_371 = (FStar_Util.digest_of_string (FStar_SMTEncoding_Term.hash_of_term app_tm))
in (Prims.strcat "partial_app_typing_" _0_371))))
in ((_0_373), (Some ("Partial app typing")), (_0_372)))))
in ((app_tm), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' ((e_typing)::[]))))))))
end))))
end))
end))
end)))
in (

let encode_full_app = (fun fv -> (

let uu____3226 = (lookup_free_var_sym env fv)
in (match (uu____3226) with
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
Some ((let _0_374 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _0_374 Prims.snd)))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____3270, FStar_Util.Inl (t), uu____3272) -> begin
Some (t)
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____3293, FStar_Util.Inr (c), uu____3295) -> begin
Some ((FStar_Syntax_Util.comp_result c))
end
| uu____3316 -> begin
None
end)
in (match (head_type) with
| None -> begin
(encode_partial_app None)
end
| Some (head_type) -> begin
(

let head_type = (let _0_375 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine _0_375))
in (

let uu____3336 = (curried_arrow_formals_comp head_type)
in (match (uu____3336) with
| (formals, c) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| uu____3361 -> begin
(match (((FStar_List.length formals) > (FStar_List.length args))) with
| true -> begin
(encode_partial_app (Some (((formals), (c)))))
end
| uu____3373 -> begin
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

let uu____3406 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____3406) with
| (bs, body, opening) -> begin
(

let fallback = (fun uu____3421 -> (

let f = (varops.fresh "Tm_abs")
in (

let decl = FStar_SMTEncoding_Term.DeclFun (((f), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Imprecise function encoding"))))
in (let _0_376 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in ((_0_376), ((decl)::[]))))))
in (

let is_impure = (fun uu___117_3435 -> (match (uu___117_3435) with
| FStar_Util.Inl (lc) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)))
end
| FStar_Util.Inr (eff, uu____3446) -> begin
(let _0_377 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv eff)
in (FStar_All.pipe_right _0_377 Prims.op_Negation))
end))
in (

let codomain_eff = (fun lc -> (match (lc) with
| FStar_Util.Inl (lc) -> begin
(let _0_380 = (let _0_378 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening _0_378))
in (FStar_All.pipe_right _0_380 (fun _0_379 -> Some (_0_379))))
end
| FStar_Util.Inr (eff, flags) -> begin
(

let new_uvar = (fun uu____3483 -> (let _0_381 = (FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange [] FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _0_381 Prims.fst)))
in (match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid)) with
| true -> begin
(let _0_383 = (FStar_Syntax_Syntax.mk_Total (new_uvar ()))
in (FStar_All.pipe_right _0_383 (fun _0_382 -> Some (_0_382))))
end
| uu____3490 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid)) with
| true -> begin
(let _0_385 = (FStar_Syntax_Syntax.mk_GTotal (new_uvar ()))
in (FStar_All.pipe_right _0_385 (fun _0_384 -> Some (_0_384))))
end
| uu____3493 -> begin
None
end)
end))
end))
in (match (lopt) with
| None -> begin
((let _0_387 = (let _0_386 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s" _0_386))
in (FStar_Errors.warn t0.FStar_Syntax_Syntax.pos _0_387));
(fallback ());
)
end
| Some (lc) -> begin
(

let uu____3513 = (is_impure lc)
in (match (uu____3513) with
| true -> begin
(fallback ())
end
| uu____3516 -> begin
(

let uu____3517 = (encode_binders None bs env)
in (match (uu____3517) with
| (vars, guards, envbody, decls, uu____3532) -> begin
(

let uu____3539 = (encode_term body envbody)
in (match (uu____3539) with
| (body, decls') -> begin
(

let key_body = (FStar_SMTEncoding_Util.mkForall (let _0_389 = (FStar_SMTEncoding_Util.mkImp (let _0_388 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((_0_388), (body))))
in (([]), (vars), (_0_389))))
in (

let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), (cvars), (key_body)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____3557 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____3557) with
| Some (t, uu____3572, uu____3573) -> begin
(let _0_391 = (FStar_SMTEncoding_Util.mkApp (let _0_390 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((t), (_0_390))))
in ((_0_391), ([])))
end
| None -> begin
(

let uu____3592 = (is_eta env vars body)
in (match (uu____3592) with
| Some (t) -> begin
((t), ([]))
end
| None -> begin
(

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let fsym = (varops.mk_unique (let _0_392 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_abs_" _0_392)))
in (

let fdecl = FStar_SMTEncoding_Term.DeclFun (((fsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let f = (FStar_SMTEncoding_Util.mkApp (let _0_393 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((fsym), (_0_393))))
in (

let app = (mk_Apply f vars)
in (

let typing_f = (

let uu____3613 = (codomain_eff lc)
in (match (uu____3613) with
| None -> begin
[]
end
| Some (c) -> begin
(

let tfun = (FStar_Syntax_Util.arrow bs c)
in (

let uu____3620 = (encode_term_pred None tfun env f)
in (match (uu____3620) with
| (f_has_t, decls'') -> begin
(

let a_name = Some ((Prims.strcat "typing_" fsym))
in (let _0_396 = (let _0_395 = FStar_SMTEncoding_Term.Assume ((let _0_394 = (FStar_SMTEncoding_Util.mkForall ((((f)::[])::[]), (cvars), (f_has_t)))
in ((_0_394), (a_name), (a_name))))
in (_0_395)::[])
in (FStar_List.append decls'' _0_396)))
end)))
end))
in (

let interp_f = (

let a_name = Some ((Prims.strcat "interpretation_" fsym))
in FStar_SMTEncoding_Term.Assume ((let _0_398 = (FStar_SMTEncoding_Util.mkForall (let _0_397 = (FStar_SMTEncoding_Util.mkEq ((app), (body)))
in ((((app)::[])::[]), ((FStar_List.append vars cvars)), (_0_397))))
in ((_0_398), (a_name), (a_name)))))
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
| FStar_Syntax_Syntax.Tm_let ((uu____3655, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____3656); FStar_Syntax_Syntax.lbunivs = uu____3657; FStar_Syntax_Syntax.lbtyp = uu____3658; FStar_Syntax_Syntax.lbeff = uu____3659; FStar_Syntax_Syntax.lbdef = uu____3660})::uu____3661), uu____3662) -> begin
(failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____3680; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____3682; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (uu____3698) -> begin
((FStar_Errors.diag t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts");
(

let e = (varops.fresh "let-rec")
in (

let decl_e = FStar_SMTEncoding_Term.DeclFun (((e), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (let _0_399 = (FStar_SMTEncoding_Util.mkFreeV ((e), (FStar_SMTEncoding_Term.Term_sort)))
in ((_0_399), ((decl_e)::[])))));
)
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end);
)))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (

let uu____3752 = (encode_term e1 env)
in (match (uu____3752) with
| (ee1, decls1) -> begin
(

let uu____3759 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) e2)
in (match (uu____3759) with
| (xs, e2) -> begin
(

let uu____3773 = (FStar_List.hd xs)
in (match (uu____3773) with
| (x, uu____3781) -> begin
(

let env' = (push_term_var env x ee1)
in (

let uu____3783 = (encode_body e2 env')
in (match (uu____3783) with
| (ee2, decls2) -> begin
((ee2), ((FStar_List.append decls1 decls2)))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (

let uu____3805 = (encode_term e env)
in (match (uu____3805) with
| (scr, decls) -> begin
(

let uu____3812 = (FStar_List.fold_right (fun b uu____3820 -> (match (uu____3820) with
| (else_case, decls) -> begin
(

let uu____3831 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____3831) with
| (p, w, br) -> begin
(

let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun uu____3861 uu____3862 -> (match (((uu____3861), (uu____3862))) with
| ((env0, pattern), (else_case, decls)) -> begin
(

let guard = (pattern.guard scr)
in (

let projections = (pattern.projections scr)
in (

let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env uu____3899 -> (match (uu____3899) with
| (x, t) -> begin
(push_term_var env x t)
end)) env))
in (

let uu____3904 = (match (w) with
| None -> begin
((guard), ([]))
end
| Some (w) -> begin
(

let uu____3919 = (encode_term w env)
in (match (uu____3919) with
| (w, decls2) -> begin
(let _0_402 = (FStar_SMTEncoding_Util.mkAnd (let _0_401 = (FStar_SMTEncoding_Util.mkEq (let _0_400 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue)
in ((w), (_0_400))))
in ((guard), (_0_401))))
in ((_0_402), (decls2)))
end))
end)
in (match (uu____3904) with
| (guard, decls2) -> begin
(

let uu____3934 = (encode_br br env)
in (match (uu____3934) with
| (br, decls3) -> begin
(let _0_403 = (FStar_SMTEncoding_Util.mkITE ((guard), (br), (else_case)))
in ((_0_403), ((FStar_List.append decls (FStar_List.append decls2 decls3)))))
end))
end)))))
end)) patterns ((else_case), (decls))))
end))
end)) pats ((default_case), (decls)))
in (match (uu____3812) with
| (match_tm, decls) -> begin
((match_tm), (decls))
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| uu____3965 -> begin
(let _0_404 = (encode_one_pat env pat)
in (_0_404)::[])
end))
and encode_one_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> ((

let uu____3975 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____3975) with
| true -> begin
(let _0_405 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" _0_405))
end
| uu____3976 -> begin
()
end));
(

let uu____3977 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (uu____3977) with
| (vars, pat_term) -> begin
(

let uu____3987 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun uu____4010 v -> (match (uu____4010) with
| (env, vars) -> begin
(

let uu____4038 = (gen_term_var env v)
in (match (uu____4038) with
| (xx, uu____4050, env) -> begin
((env), ((((v), (((xx), (FStar_SMTEncoding_Term.Term_sort)))))::vars))
end))
end)) ((env), ([]))))
in (match (uu____3987) with
| (env, vars) -> begin
(

let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (uu____4097) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_dot_term (_)) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(FStar_SMTEncoding_Util.mkEq (let _0_406 = (encode_const c)
in ((scrutinee), (_0_406))))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let is_f = (mk_data_tester env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____4135 -> (match (uu____4135) with
| (arg, uu____4141) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _0_407 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_guard arg _0_407)))
end))))
in (FStar_SMTEncoding_Util.mk_and_l ((is_f)::sub_term_guards))))
end))
in (

let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (uu____4169) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _)) | (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_constant (uu____4184) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(let _0_409 = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____4223 -> (match (uu____4223) with
| (arg, uu____4232) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _0_408 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_projections arg _0_408)))
end))))
in (FStar_All.pipe_right _0_409 FStar_List.flatten))
end))
in (

let pat_term = (fun uu____4250 -> (encode_term pat_term env))
in (

let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in ((env), (pattern))))))
end))
end));
))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (

let uu____4257 = (FStar_All.pipe_right l (FStar_List.fold_left (fun uu____4272 uu____4273 -> (match (((uu____4272), (uu____4273))) with
| ((tms, decls), (t, uu____4293)) -> begin
(

let uu____4304 = (encode_term t env)
in (match (uu____4304) with
| (t, decls') -> begin
(((t)::tms), ((FStar_List.append decls decls')))
end))
end)) (([]), ([]))))
in (match (uu____4257) with
| (l, decls) -> begin
(((FStar_List.rev l)), (decls))
end)))
and encode_function_type_as_formula : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun induction_on new_pats t env -> (

let list_elements = (fun e -> (

let uu____4342 = (FStar_Syntax_Util.list_elements e)
in (match (uu____4342) with
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

let uu____4360 = (let _0_410 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right _0_410 FStar_Syntax_Util.head_and_args))
in (match (uu____4360) with
| (head, args) -> begin
(

let uu____4400 = (let _0_411 = (FStar_Syntax_Util.un_uinst head).FStar_Syntax_Syntax.n
in ((_0_411), (args)))
in (match (uu____4400) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((uu____4419, uu____4420))::((e, uu____4422))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpat_lid) -> begin
((e), (None))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, uu____4453))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatT_lid) -> begin
((e), (None))
end
| uu____4474 -> begin
(failwith "Unexpected pattern term")
end))
end)))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements p)
in (

let smt_pat_or = (fun t -> (

let uu____4507 = (let _0_412 = (FStar_Syntax_Util.unmeta t)
in (FStar_All.pipe_right _0_412 FStar_Syntax_Util.head_and_args))
in (match (uu____4507) with
| (head, args) -> begin
(

let uu____4545 = (let _0_413 = (FStar_Syntax_Util.un_uinst head).FStar_Syntax_Syntax.n
in ((_0_413), (args)))
in (match (uu____4545) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, uu____4563))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatOr_lid) -> begin
Some (e)
end
| uu____4583 -> begin
None
end))
end)))
in (match (elts) with
| (t)::[] -> begin
(

let uu____4601 = (smt_pat_or t)
in (match (uu____4601) with
| Some (e) -> begin
(let _0_415 = (list_elements e)
in (FStar_All.pipe_right _0_415 (FStar_List.map (fun branch -> (let _0_414 = (list_elements branch)
in (FStar_All.pipe_right _0_414 (FStar_List.map one_pat)))))))
end
| uu____4644 -> begin
(let _0_416 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_0_416)::[])
end))
end
| uu____4672 -> begin
(let _0_417 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_0_417)::[])
end))))
in (

let uu____4698 = (

let uu____4714 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____4714) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____4742 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____4742) with
| (binders, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____4777; FStar_Syntax_Syntax.effect_name = uu____4778; FStar_Syntax_Syntax.result_typ = uu____4779; FStar_Syntax_Syntax.effect_args = ((pre, uu____4781))::((post, uu____4783))::((pats, uu____4785))::[]; FStar_Syntax_Syntax.flags = uu____4786}) -> begin
(

let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _0_418 = (lemma_pats pats')
in ((binders), (pre), (post), (_0_418))))
end
| uu____4831 -> begin
(failwith "impos")
end)
end))
end
| uu____4847 -> begin
(failwith "Impos")
end))
in (match (uu____4698) with
| (binders, pre, post, patterns) -> begin
(

let uu____4891 = (encode_binders None binders env)
in (match (uu____4891) with
| (vars, guards, env, decls, uu____4906) -> begin
(

let uu____4913 = (let _0_420 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (

let uu____4956 = (let _0_419 = (FStar_All.pipe_right branch (FStar_List.map (fun uu____4980 -> (match (uu____4980) with
| (t, uu____4987) -> begin
(encode_term t (

let uu___143_4990 = env
in {bindings = uu___143_4990.bindings; depth = uu___143_4990.depth; tcenv = uu___143_4990.tcenv; warn = uu___143_4990.warn; cache = uu___143_4990.cache; nolabels = uu___143_4990.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___143_4990.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _0_419 FStar_List.unzip))
in (match (uu____4956) with
| (pats, decls) -> begin
((pats), (decls))
end)))))
in (FStar_All.pipe_right _0_420 FStar_List.unzip))
in (match (uu____4913) with
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
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _0_422 = (let _0_421 = (FStar_SMTEncoding_Util.mkFreeV l)
in (FStar_SMTEncoding_Util.mk_Precedes _0_421 e))
in (_0_422)::p))))
end
| uu____5036 -> begin
(

let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _0_423 = (FStar_SMTEncoding_Util.mk_Precedes tl e)
in (_0_423)::p))))
end
| ((x, FStar_SMTEncoding_Term.Term_sort))::vars -> begin
(let _0_425 = (let _0_424 = (FStar_SMTEncoding_Util.mkFreeV ((x), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Util.mk_LexCons _0_424 tl))
in (aux _0_425 vars))
end
| uu____5072 -> begin
pats
end))
in (let _0_426 = (FStar_SMTEncoding_Util.mkFreeV (("Prims.LexTop"), (FStar_SMTEncoding_Term.Term_sort)))
in (aux _0_426 vars)))
end)
end)
in (

let env = (

let uu___144_5077 = env
in {bindings = uu___144_5077.bindings; depth = uu___144_5077.depth; tcenv = uu___144_5077.tcenv; warn = uu___144_5077.warn; cache = uu___144_5077.cache; nolabels = true; use_zfuel_name = uu___144_5077.use_zfuel_name; encode_non_total_function_typ = uu___144_5077.encode_non_total_function_typ})
in (

let uu____5078 = (let _0_427 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula _0_427 env))
in (match (uu____5078) with
| (pre, decls'') -> begin
(

let uu____5085 = (let _0_428 = (FStar_Syntax_Util.unmeta post)
in (encode_formula _0_428 env))
in (match (uu____5085) with
| (post, decls''') -> begin
(

let decls = (FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') (FStar_List.append decls'' decls''')))
in (let _0_431 = (FStar_SMTEncoding_Util.mkForall (let _0_430 = (FStar_SMTEncoding_Util.mkImp (let _0_429 = (FStar_SMTEncoding_Util.mk_and_l ((pre)::guards))
in ((_0_429), (post))))
in ((pats), (vars), (_0_430))))
in ((_0_431), (decls))))
end))
end)))))
end))
end))
end))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (

let debug = (fun phi -> (

let uu____5106 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____5106) with
| true -> begin
(let _0_433 = (FStar_Syntax_Print.tag_of_term phi)
in (let _0_432 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print2 "Formula (%s)  %s\n" _0_433 _0_432)))
end
| uu____5107 -> begin
()
end)))
in (

let enc = (fun f r l -> (

let uu____5133 = (FStar_Util.fold_map (fun decls x -> (

let uu____5146 = (encode_term (Prims.fst x) env)
in (match (uu____5146) with
| (t, decls') -> begin
(((FStar_List.append decls decls')), (t))
end))) [] l)
in (match (uu____5133) with
| (decls, args) -> begin
(let _0_434 = (

let uu___145_5164 = (f args)
in {FStar_SMTEncoding_Term.tm = uu___145_5164.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___145_5164.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((_0_434), (decls)))
end)))
in (

let const_op = (fun f r uu____5182 -> (let _0_435 = (f r)
in ((_0_435), ([]))))
in (

let un_op = (fun f l -> (let _0_436 = (FStar_List.hd l)
in (FStar_All.pipe_left f _0_436)))
in (

let bin_op = (fun f uu___118_5212 -> (match (uu___118_5212) with
| (t1)::(t2)::[] -> begin
(f ((t1), (t2)))
end
| uu____5220 -> begin
(failwith "Impossible")
end))
in (

let enc_prop_c = (fun f r l -> (

let uu____5247 = (FStar_Util.fold_map (fun decls uu____5256 -> (match (uu____5256) with
| (t, uu____5264) -> begin
(

let uu____5265 = (encode_formula t env)
in (match (uu____5265) with
| (phi, decls') -> begin
(((FStar_List.append decls decls')), (phi))
end))
end)) [] l)
in (match (uu____5247) with
| (decls, phis) -> begin
(let _0_437 = (

let uu___146_5283 = (f phis)
in {FStar_SMTEncoding_Term.tm = uu___146_5283.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___146_5283.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((_0_437), (decls)))
end)))
in (

let eq_op = (fun r uu___119_5298 -> (match (uu___119_5298) with
| ((_)::(e1)::(e2)::[]) | ((_)::(_)::(e1)::(e2)::[]) -> begin
((enc (bin_op FStar_SMTEncoding_Util.mkEq)) r ((e1)::(e2)::[]))
end
| l -> begin
((enc (bin_op FStar_SMTEncoding_Util.mkEq)) r l)
end))
in (

let mk_imp = (fun r uu___120_5383 -> (match (uu___120_5383) with
| ((lhs, uu____5387))::((rhs, uu____5389))::[] -> begin
(

let uu____5410 = (encode_formula rhs env)
in (match (uu____5410) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____5419) -> begin
((l1), (decls1))
end
| uu____5422 -> begin
(

let uu____5423 = (encode_formula lhs env)
in (match (uu____5423) with
| (l2, decls2) -> begin
(let _0_438 = (FStar_SMTEncoding_Term.mkImp ((l2), (l1)) r)
in ((_0_438), ((FStar_List.append decls1 decls2))))
end))
end)
end))
end
| uu____5431 -> begin
(failwith "impossible")
end))
in (

let mk_ite = (fun r uu___121_5446 -> (match (uu___121_5446) with
| ((guard, uu____5450))::((_then, uu____5452))::((_else, uu____5454))::[] -> begin
(

let uu____5483 = (encode_formula guard env)
in (match (uu____5483) with
| (g, decls1) -> begin
(

let uu____5490 = (encode_formula _then env)
in (match (uu____5490) with
| (t, decls2) -> begin
(

let uu____5497 = (encode_formula _else env)
in (match (uu____5497) with
| (e, decls3) -> begin
(

let res = (FStar_SMTEncoding_Term.mkITE ((g), (t), (e)) r)
in ((res), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end))
end))
end
| uu____5506 -> begin
(failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (f (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)))
in (

let connectives = (let _0_451 = (let _0_439 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd))
in ((FStar_Syntax_Const.and_lid), (_0_439)))
in (let _0_450 = (let _0_449 = (let _0_440 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr))
in ((FStar_Syntax_Const.or_lid), (_0_440)))
in (let _0_448 = (let _0_447 = (let _0_446 = (let _0_441 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff))
in ((FStar_Syntax_Const.iff_lid), (_0_441)))
in (let _0_445 = (let _0_444 = (let _0_443 = (let _0_442 = (FStar_All.pipe_left enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot))
in ((FStar_Syntax_Const.not_lid), (_0_442)))
in (_0_443)::(((FStar_Syntax_Const.eq2_lid), (eq_op)))::(((FStar_Syntax_Const.eq3_lid), (eq_op)))::(((FStar_Syntax_Const.true_lid), ((const_op FStar_SMTEncoding_Term.mkTrue))))::(((FStar_Syntax_Const.false_lid), ((const_op FStar_SMTEncoding_Term.mkFalse))))::[])
in (((FStar_Syntax_Const.ite_lid), (mk_ite)))::_0_444)
in (_0_446)::_0_445))
in (((FStar_Syntax_Const.imp_lid), (mk_imp)))::_0_447)
in (_0_449)::_0_448))
in (_0_451)::_0_450))
in (

let rec fallback = (fun phi -> (match (phi.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(

let uu____5744 = (encode_formula phi' env)
in (match (uu____5744) with
| (phi, decls) -> begin
(let _0_452 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled (((phi), (msg), (r)))) r)
in ((_0_452), (decls)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (uu____5751) -> begin
(let _0_453 = (FStar_Syntax_Util.unmeta phi)
in (encode_formula _0_453 env))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(

let uu____5784 = (encode_match e pats FStar_SMTEncoding_Util.mkFalse env encode_formula)
in (match (uu____5784) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____5792; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____5794; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let uu____5810 = (encode_let x t1 e1 e2 env encode_formula)
in (match (uu____5810) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let head = (FStar_Syntax_Util.un_uinst head)
in (match (((head.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____5842)::((x, uu____5844))::((t, uu____5846))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.has_type_lid) -> begin
(

let uu____5880 = (encode_term x env)
in (match (uu____5880) with
| (x, decls) -> begin
(

let uu____5887 = (encode_term t env)
in (match (uu____5887) with
| (t, decls') -> begin
(let _0_454 = (FStar_SMTEncoding_Term.mk_HasType x t)
in ((_0_454), ((FStar_List.append decls decls'))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((r, uu____5897))::((msg, uu____5899))::((phi, uu____5901))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.labeled_lid) -> begin
(

let uu____5935 = (let _0_456 = (FStar_Syntax_Subst.compress r).FStar_Syntax_Syntax.n
in (let _0_455 = (FStar_Syntax_Subst.compress msg).FStar_Syntax_Syntax.n
in ((_0_456), (_0_455))))
in (match (uu____5935) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____5942))) -> begin
(

let phi = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((phi), (FStar_Syntax_Syntax.Meta_labeled ((((FStar_Util.string_of_unicode s)), (r), (false)))))))) None r)
in (fallback phi))
end
| uu____5958 -> begin
(fallback phi)
end))
end
| uu____5961 when (head_redex env head) -> begin
(let _0_457 = (whnf env phi)
in (encode_formula _0_457 env))
end
| uu____5969 -> begin
(

let uu____5977 = (encode_term phi env)
in (match (uu____5977) with
| (tt, decls) -> begin
(let _0_458 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___147_5984 = tt
in {FStar_SMTEncoding_Term.tm = uu___147_5984.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___147_5984.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi.FStar_Syntax_Syntax.pos}))
in ((_0_458), (decls)))
end))
end))
end
| uu____5987 -> begin
(

let uu____5988 = (encode_term phi env)
in (match (uu____5988) with
| (tt, decls) -> begin
(let _0_459 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___148_5995 = tt
in {FStar_SMTEncoding_Term.tm = uu___148_5995.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___148_5995.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi.FStar_Syntax_Syntax.pos}))
in ((_0_459), (decls)))
end))
end))
in (

let encode_q_body = (fun env bs ps body -> (

let uu____6022 = (encode_binders None bs env)
in (match (uu____6022) with
| (vars, guards, env, decls, uu____6044) -> begin
(

let uu____6051 = (let _0_461 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let uu____6086 = (let _0_460 = (FStar_All.pipe_right p (FStar_List.map (fun uu____6108 -> (match (uu____6108) with
| (t, uu____6114) -> begin
(encode_term t (

let uu___149_6115 = env
in {bindings = uu___149_6115.bindings; depth = uu___149_6115.depth; tcenv = uu___149_6115.tcenv; warn = uu___149_6115.warn; cache = uu___149_6115.cache; nolabels = uu___149_6115.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___149_6115.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _0_460 FStar_List.unzip))
in (match (uu____6086) with
| (p, decls) -> begin
((p), ((FStar_List.flatten decls)))
end)))))
in (FStar_All.pipe_right _0_461 FStar_List.unzip))
in (match (uu____6051) with
| (pats, decls') -> begin
(

let uu____6149 = (encode_formula body env)
in (match (uu____6149) with
| (body, decls'') -> begin
(

let guards = (match (pats) with
| (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (gf), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____6168; FStar_SMTEncoding_Term.rng = uu____6169})::[])::[] when ((FStar_Ident.text_of_lid FStar_Syntax_Const.guard_free) = gf) -> begin
[]
end
| uu____6177 -> begin
guards
end)
in (let _0_462 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((vars), (pats), (_0_462), (body), ((FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') decls''))))))
end))
end))
end)))
in ((debug phi);
(

let phi = (FStar_Syntax_Util.unascribe phi)
in (

let check_pattern_vars = (fun vars pats -> (

let pats = (FStar_All.pipe_right pats (FStar_List.map (fun uu____6213 -> (match (uu____6213) with
| (x, uu____6217) -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x)
end))))
in (match (pats) with
| [] -> begin
()
end
| (hd)::tl -> begin
(

let pat_vars = (let _0_464 = (FStar_Syntax_Free.names hd)
in (FStar_List.fold_left (fun out x -> (let _0_463 = (FStar_Syntax_Free.names x)
in (FStar_Util.set_union out _0_463))) _0_464 tl))
in (

let uu____6227 = (FStar_All.pipe_right vars (FStar_Util.find_opt (fun uu____6239 -> (match (uu____6239) with
| (b, uu____6243) -> begin
(not ((FStar_Util.set_mem b pat_vars)))
end))))
in (match (uu____6227) with
| None -> begin
()
end
| Some (x, uu____6247) -> begin
(

let pos = (FStar_List.fold_left (fun out t -> (FStar_Range.union_ranges out t.FStar_Syntax_Syntax.pos)) hd.FStar_Syntax_Syntax.pos tl)
in (let _0_466 = (let _0_465 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "SMT pattern misses at least one bound variable: %s" _0_465))
in (FStar_Errors.warn pos _0_466)))
end)))
end)))
in (

let uu____6257 = (FStar_Syntax_Util.destruct_typ_as_formula phi)
in (match (uu____6257) with
| None -> begin
(fallback phi)
end
| Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(

let uu____6263 = (FStar_All.pipe_right connectives (FStar_List.tryFind (fun uu____6299 -> (match (uu____6299) with
| (l, uu____6309) -> begin
(FStar_Ident.lid_equals op l)
end))))
in (match (uu____6263) with
| None -> begin
(fallback phi)
end
| Some (uu____6332, f) -> begin
(f phi.FStar_Syntax_Syntax.pos arms)
end))
end
| Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____6361 = (encode_q_body env vars pats body)
in (match (uu____6361) with
| (vars, pats, guard, body, decls) -> begin
(

let tm = (let _0_468 = (let _0_467 = (FStar_SMTEncoding_Util.mkImp ((guard), (body)))
in ((pats), (vars), (_0_467)))
in (FStar_SMTEncoding_Term.mkForall _0_468 phi.FStar_Syntax_Syntax.pos))
in ((tm), (decls)))
end));
)
end
| Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____6398 = (encode_q_body env vars pats body)
in (match (uu____6398) with
| (vars, pats, guard, body, decls) -> begin
(let _0_471 = (let _0_470 = (let _0_469 = (FStar_SMTEncoding_Util.mkAnd ((guard), (body)))
in ((pats), (vars), (_0_469)))
in (FStar_SMTEncoding_Term.mkExists _0_470 phi.FStar_Syntax_Syntax.pos))
in ((_0_471), (decls)))
end));
)
end))));
)))))))))))))))

type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list); is : FStar_Ident.lident  ->  Prims.bool}


let prims : prims_t = (

let uu____6471 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____6471) with
| (asym, a) -> begin
(

let uu____6476 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____6476) with
| (xsym, x) -> begin
(

let uu____6481 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____6481) with
| (ysym, y) -> begin
(

let quant = (fun vars body x -> (

let xname_decl = FStar_SMTEncoding_Term.DeclFun ((let _0_472 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in ((x), (_0_472), (FStar_SMTEncoding_Term.Term_sort), (None))))
in (

let xtok = (Prims.strcat x "@tok")
in (

let xtok_decl = FStar_SMTEncoding_Term.DeclFun (((xtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let xapp = (FStar_SMTEncoding_Util.mkApp (let _0_473 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((x), (_0_473))))
in (

let xtok = (FStar_SMTEncoding_Util.mkApp ((xtok), ([])))
in (

let xtok_app = (mk_Apply xtok vars)
in (let _0_483 = (let _0_482 = (let _0_481 = (let _0_480 = FStar_SMTEncoding_Term.Assume ((let _0_475 = (FStar_SMTEncoding_Util.mkForall (let _0_474 = (FStar_SMTEncoding_Util.mkEq ((xapp), (body)))
in ((((xapp)::[])::[]), (vars), (_0_474))))
in ((_0_475), (None), (Some ((Prims.strcat "primitive_" x))))))
in (let _0_479 = (let _0_478 = FStar_SMTEncoding_Term.Assume ((let _0_477 = (FStar_SMTEncoding_Util.mkForall (let _0_476 = (FStar_SMTEncoding_Util.mkEq ((xtok_app), (xapp)))
in ((((xtok_app)::[])::[]), (vars), (_0_476))))
in ((_0_477), (Some ("Name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" x))))))
in (_0_478)::[])
in (_0_480)::_0_479))
in (xtok_decl)::_0_481)
in (xname_decl)::_0_482)
in ((xtok), (_0_483))))))))))
in (

let axy = (((asym), (FStar_SMTEncoding_Term.Term_sort)))::(((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let xy = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let qx = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let prims = (let _0_579 = (let _0_486 = (let _0_485 = (let _0_484 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _0_484))
in (quant axy _0_485))
in ((FStar_Syntax_Const.op_Eq), (_0_486)))
in (let _0_578 = (let _0_577 = (let _0_489 = (let _0_488 = (let _0_487 = (FStar_SMTEncoding_Util.mkNot (FStar_SMTEncoding_Util.mkEq ((x), (y))))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _0_487))
in (quant axy _0_488))
in ((FStar_Syntax_Const.op_notEq), (_0_489)))
in (let _0_576 = (let _0_575 = (let _0_494 = (let _0_493 = (let _0_492 = (FStar_SMTEncoding_Util.mkLT (let _0_491 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _0_490 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_0_491), (_0_490)))))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _0_492))
in (quant xy _0_493))
in ((FStar_Syntax_Const.op_LT), (_0_494)))
in (let _0_574 = (let _0_573 = (let _0_499 = (let _0_498 = (let _0_497 = (FStar_SMTEncoding_Util.mkLTE (let _0_496 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _0_495 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_0_496), (_0_495)))))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _0_497))
in (quant xy _0_498))
in ((FStar_Syntax_Const.op_LTE), (_0_499)))
in (let _0_572 = (let _0_571 = (let _0_504 = (let _0_503 = (let _0_502 = (FStar_SMTEncoding_Util.mkGT (let _0_501 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _0_500 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_0_501), (_0_500)))))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _0_502))
in (quant xy _0_503))
in ((FStar_Syntax_Const.op_GT), (_0_504)))
in (let _0_570 = (let _0_569 = (let _0_509 = (let _0_508 = (let _0_507 = (FStar_SMTEncoding_Util.mkGTE (let _0_506 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _0_505 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_0_506), (_0_505)))))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _0_507))
in (quant xy _0_508))
in ((FStar_Syntax_Const.op_GTE), (_0_509)))
in (let _0_568 = (let _0_567 = (let _0_514 = (let _0_513 = (let _0_512 = (FStar_SMTEncoding_Util.mkSub (let _0_511 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _0_510 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_0_511), (_0_510)))))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _0_512))
in (quant xy _0_513))
in ((FStar_Syntax_Const.op_Subtraction), (_0_514)))
in (let _0_566 = (let _0_565 = (let _0_517 = (let _0_516 = (let _0_515 = (FStar_SMTEncoding_Util.mkMinus (FStar_SMTEncoding_Term.unboxInt x))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _0_515))
in (quant qx _0_516))
in ((FStar_Syntax_Const.op_Minus), (_0_517)))
in (let _0_564 = (let _0_563 = (let _0_522 = (let _0_521 = (let _0_520 = (FStar_SMTEncoding_Util.mkAdd (let _0_519 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _0_518 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_0_519), (_0_518)))))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _0_520))
in (quant xy _0_521))
in ((FStar_Syntax_Const.op_Addition), (_0_522)))
in (let _0_562 = (let _0_561 = (let _0_527 = (let _0_526 = (let _0_525 = (FStar_SMTEncoding_Util.mkMul (let _0_524 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _0_523 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_0_524), (_0_523)))))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _0_525))
in (quant xy _0_526))
in ((FStar_Syntax_Const.op_Multiply), (_0_527)))
in (let _0_560 = (let _0_559 = (let _0_532 = (let _0_531 = (let _0_530 = (FStar_SMTEncoding_Util.mkDiv (let _0_529 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _0_528 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_0_529), (_0_528)))))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _0_530))
in (quant xy _0_531))
in ((FStar_Syntax_Const.op_Division), (_0_532)))
in (let _0_558 = (let _0_557 = (let _0_537 = (let _0_536 = (let _0_535 = (FStar_SMTEncoding_Util.mkMod (let _0_534 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _0_533 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_0_534), (_0_533)))))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _0_535))
in (quant xy _0_536))
in ((FStar_Syntax_Const.op_Modulus), (_0_537)))
in (let _0_556 = (let _0_555 = (let _0_542 = (let _0_541 = (let _0_540 = (FStar_SMTEncoding_Util.mkAnd (let _0_539 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _0_538 = (FStar_SMTEncoding_Term.unboxBool y)
in ((_0_539), (_0_538)))))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _0_540))
in (quant xy _0_541))
in ((FStar_Syntax_Const.op_And), (_0_542)))
in (let _0_554 = (let _0_553 = (let _0_547 = (let _0_546 = (let _0_545 = (FStar_SMTEncoding_Util.mkOr (let _0_544 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _0_543 = (FStar_SMTEncoding_Term.unboxBool y)
in ((_0_544), (_0_543)))))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _0_545))
in (quant xy _0_546))
in ((FStar_Syntax_Const.op_Or), (_0_547)))
in (let _0_552 = (let _0_551 = (let _0_550 = (let _0_549 = (let _0_548 = (FStar_SMTEncoding_Util.mkNot (FStar_SMTEncoding_Term.unboxBool x))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _0_548))
in (quant qx _0_549))
in ((FStar_Syntax_Const.op_Negation), (_0_550)))
in (_0_551)::[])
in (_0_553)::_0_552))
in (_0_555)::_0_554))
in (_0_557)::_0_556))
in (_0_559)::_0_558))
in (_0_561)::_0_560))
in (_0_563)::_0_562))
in (_0_565)::_0_564))
in (_0_567)::_0_566))
in (_0_569)::_0_568))
in (_0_571)::_0_570))
in (_0_573)::_0_572))
in (_0_575)::_0_574))
in (_0_577)::_0_576))
in (_0_579)::_0_578))
in (

let mk = (fun l v -> (let _0_581 = (let _0_580 = (FStar_All.pipe_right prims (FStar_List.find (fun uu____6827 -> (match (uu____6827) with
| (l', uu____6836) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right _0_580 (FStar_Option.map (fun uu____6857 -> (match (uu____6857) with
| (uu____6868, b) -> begin
(b v)
end)))))
in (FStar_All.pipe_right _0_581 FStar_Option.get)))
in (

let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun uu____6902 -> (match (uu____6902) with
| (l', uu____6911) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is})))))))
end))
end))
end))


let pretype_axiom : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun tapp vars -> (

let uu____6934 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____6934) with
| (xxsym, xx) -> begin
(

let uu____6939 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____6939) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let tapp_hash = (FStar_SMTEncoding_Term.hash_of_term tapp)
in FStar_SMTEncoding_Term.Assume ((let _0_587 = (FStar_SMTEncoding_Util.mkForall (let _0_584 = (FStar_SMTEncoding_Util.mkImp (let _0_583 = (FStar_SMTEncoding_Util.mkEq (let _0_582 = (FStar_SMTEncoding_Util.mkApp (("PreType"), ((xx)::[])))
in ((tapp), (_0_582))))
in ((xx_has_type), (_0_583))))
in ((((xx_has_type)::[])::[]), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars), (_0_584))))
in (let _0_586 = Some ((varops.mk_unique (let _0_585 = (FStar_Util.digest_of_string tapp_hash)
in (Prims.strcat "pretyping_" _0_585))))
in ((_0_587), (Some ("pretyping")), (_0_586)))))))
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
in (let _0_594 = FStar_SMTEncoding_Term.Assume ((let _0_588 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in ((_0_588), (Some ("unit typing")), (Some ("unit_typing")))))
in (let _0_593 = (let _0_592 = FStar_SMTEncoding_Term.Assume ((let _0_591 = (mkForall_fuel (let _0_590 = (FStar_SMTEncoding_Util.mkImp (let _0_589 = (FStar_SMTEncoding_Util.mkEq ((x), (FStar_SMTEncoding_Term.mk_Term_unit)))
in ((typing_pred), (_0_589))))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_0_590))))
in ((_0_591), (Some ("unit inversion")), (Some ("unit_inversion")))))
in (_0_592)::[])
in (_0_594)::_0_593))))
in (

let mk_bool = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Bool_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (let _0_606 = FStar_SMTEncoding_Term.Assume ((let _0_600 = (FStar_SMTEncoding_Util.mkForall (let _0_599 = (let _0_596 = (let _0_595 = (FStar_SMTEncoding_Term.boxBool b)
in (_0_595)::[])
in (_0_596)::[])
in (let _0_598 = (let _0_597 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType _0_597 tt))
in ((_0_599), ((bb)::[]), (_0_598)))))
in ((_0_600), (Some ("bool typing")), (Some ("bool_typing")))))
in (let _0_605 = (let _0_604 = FStar_SMTEncoding_Term.Assume ((let _0_603 = (mkForall_fuel (let _0_602 = (FStar_SMTEncoding_Util.mkImp (let _0_601 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in ((typing_pred), (_0_601))))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_0_602))))
in ((_0_603), (Some ("bool inversion")), (Some ("bool_inversion")))))
in (_0_604)::[])
in (_0_606)::_0_605))))))
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

let precedes = (let _0_613 = (FStar_SMTEncoding_Util.mkApp (let _0_612 = (let _0_611 = (let _0_610 = (let _0_609 = (FStar_SMTEncoding_Term.boxInt a)
in (let _0_608 = (let _0_607 = (FStar_SMTEncoding_Term.boxInt b)
in (_0_607)::[])
in (_0_609)::_0_608))
in (tt)::_0_610)
in (tt)::_0_611)
in (("Prims.Precedes"), (_0_612))))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _0_613))
in (

let precedes_y_x = (let _0_614 = (FStar_SMTEncoding_Util.mkApp (("Precedes"), ((y)::(x)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _0_614))
in (let _0_644 = FStar_SMTEncoding_Term.Assume ((let _0_620 = (FStar_SMTEncoding_Util.mkForall (let _0_619 = (let _0_616 = (let _0_615 = (FStar_SMTEncoding_Term.boxInt b)
in (_0_615)::[])
in (_0_616)::[])
in (let _0_618 = (let _0_617 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType _0_617 tt))
in ((_0_619), ((bb)::[]), (_0_618)))))
in ((_0_620), (Some ("int typing")), (Some ("int_typing")))))
in (let _0_643 = (let _0_642 = FStar_SMTEncoding_Term.Assume ((let _0_623 = (mkForall_fuel (let _0_622 = (FStar_SMTEncoding_Util.mkImp (let _0_621 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in ((typing_pred), (_0_621))))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_0_622))))
in ((_0_623), (Some ("int inversion")), (Some ("int_inversion")))))
in (let _0_641 = (let _0_640 = FStar_SMTEncoding_Term.Assume ((let _0_639 = (mkForall_fuel (let _0_638 = (FStar_SMTEncoding_Util.mkImp (let _0_637 = (FStar_SMTEncoding_Util.mk_and_l (let _0_636 = (let _0_635 = (let _0_634 = (FStar_SMTEncoding_Util.mkGT (let _0_625 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _0_624 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((_0_625), (_0_624)))))
in (let _0_633 = (let _0_632 = (FStar_SMTEncoding_Util.mkGTE (let _0_627 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _0_626 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((_0_627), (_0_626)))))
in (let _0_631 = (let _0_630 = (FStar_SMTEncoding_Util.mkLT (let _0_629 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _0_628 = (FStar_SMTEncoding_Term.unboxInt x)
in ((_0_629), (_0_628)))))
in (_0_630)::[])
in (_0_632)::_0_631))
in (_0_634)::_0_633))
in (typing_pred_y)::_0_635)
in (typing_pred)::_0_636))
in ((_0_637), (precedes_y_x))))
in ((((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[]), ((xx)::(yy)::[]), (_0_638))))
in ((_0_639), (Some ("well-founded ordering on nat (alt)")), (Some ("well-founded-ordering-on-nat")))))
in (_0_640)::[])
in (_0_642)::_0_641))
in (_0_644)::_0_643)))))))))))
in (

let mk_str = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.String_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (let _0_656 = FStar_SMTEncoding_Term.Assume ((let _0_650 = (FStar_SMTEncoding_Util.mkForall (let _0_649 = (let _0_646 = (let _0_645 = (FStar_SMTEncoding_Term.boxString b)
in (_0_645)::[])
in (_0_646)::[])
in (let _0_648 = (let _0_647 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType _0_647 tt))
in ((_0_649), ((bb)::[]), (_0_648)))))
in ((_0_650), (Some ("string typing")), (Some ("string_typing")))))
in (let _0_655 = (let _0_654 = FStar_SMTEncoding_Term.Assume ((let _0_653 = (mkForall_fuel (let _0_652 = (FStar_SMTEncoding_Util.mkImp (let _0_651 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in ((typing_pred), (_0_651))))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_0_652))))
in ((_0_653), (Some ("string inversion")), (Some ("string_inversion")))))
in (_0_654)::[])
in (_0_656)::_0_655))))))
in (

let mk_ref = (fun env reft_name uu____7159 -> (

let r = (("r"), (FStar_SMTEncoding_Term.Ref_sort))
in (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let refa = (FStar_SMTEncoding_Util.mkApp (let _0_658 = (let _0_657 = (FStar_SMTEncoding_Util.mkFreeV aa)
in (_0_657)::[])
in ((reft_name), (_0_658))))
in (

let refb = (FStar_SMTEncoding_Util.mkApp (let _0_660 = (let _0_659 = (FStar_SMTEncoding_Util.mkFreeV bb)
in (_0_659)::[])
in ((reft_name), (_0_660))))
in (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (

let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (let _0_673 = FStar_SMTEncoding_Term.Assume ((let _0_663 = (mkForall_fuel (let _0_662 = (FStar_SMTEncoding_Util.mkImp (let _0_661 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in ((typing_pred), (_0_661))))
in ((((typing_pred)::[])::[]), ((xx)::(aa)::[]), (_0_662))))
in ((_0_663), (Some ("ref inversion")), (Some ("ref_inversion")))))
in (let _0_672 = (let _0_671 = FStar_SMTEncoding_Term.Assume ((let _0_670 = (let _0_669 = (let _0_668 = (FStar_SMTEncoding_Util.mkImp (let _0_667 = (FStar_SMTEncoding_Util.mkAnd ((typing_pred), (typing_pred_b)))
in (let _0_666 = (FStar_SMTEncoding_Util.mkEq (let _0_665 = (FStar_SMTEncoding_Util.mkFreeV aa)
in (let _0_664 = (FStar_SMTEncoding_Util.mkFreeV bb)
in ((_0_665), (_0_664)))))
in ((_0_667), (_0_666)))))
in ((((typing_pred)::(typing_pred_b)::[])::[]), ((xx)::(aa)::(bb)::[]), (_0_668)))
in (mkForall_fuel' (Prims.parse_int "2") _0_669))
in ((_0_670), (Some ("ref typing is injective")), (Some ("ref_injectivity")))))
in (_0_671)::[])
in (_0_673)::_0_672))))))))))
in (

let mk_true_interp = (fun env nm true_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((true_tm)::[])))
in (FStar_SMTEncoding_Term.Assume (((valid), (Some ("True interpretation")), (Some ("true_interp")))))::[]))
in (

let mk_false_interp = (fun env nm false_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((false_tm)::[])))
in (let _0_675 = FStar_SMTEncoding_Term.Assume ((let _0_674 = (FStar_SMTEncoding_Util.mkIff ((FStar_SMTEncoding_Util.mkFalse), (valid)))
in ((_0_674), (Some ("False interpretation")), (Some ("false_interp")))))
in (_0_675)::[])))
in (

let mk_and_interp = (fun env conj uu____7244 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let valid = (FStar_SMTEncoding_Util.mkApp (let _0_677 = (let _0_676 = (FStar_SMTEncoding_Util.mkApp ((conj), ((a)::(b)::[])))
in (_0_676)::[])
in (("Valid"), (_0_677))))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (let _0_681 = FStar_SMTEncoding_Term.Assume ((let _0_680 = (FStar_SMTEncoding_Util.mkForall (let _0_679 = (FStar_SMTEncoding_Util.mkIff (let _0_678 = (FStar_SMTEncoding_Util.mkAnd ((valid_a), (valid_b)))
in ((_0_678), (valid))))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_0_679))))
in ((_0_680), (Some ("/\\ interpretation")), (Some ("l_and-interp")))))
in (_0_681)::[])))))))))
in (

let mk_or_interp = (fun env disj uu____7284 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let valid = (FStar_SMTEncoding_Util.mkApp (let _0_683 = (let _0_682 = (FStar_SMTEncoding_Util.mkApp ((disj), ((a)::(b)::[])))
in (_0_682)::[])
in (("Valid"), (_0_683))))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (let _0_687 = FStar_SMTEncoding_Term.Assume ((let _0_686 = (FStar_SMTEncoding_Util.mkForall (let _0_685 = (FStar_SMTEncoding_Util.mkIff (let _0_684 = (FStar_SMTEncoding_Util.mkOr ((valid_a), (valid_b)))
in ((_0_684), (valid))))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_0_685))))
in ((_0_686), (Some ("\\/ interpretation")), (Some ("l_or-interp")))))
in (_0_687)::[])))))))))
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

let valid = (FStar_SMTEncoding_Util.mkApp (let _0_689 = (let _0_688 = (FStar_SMTEncoding_Util.mkApp ((eq2), ((a)::(x)::(y)::[])))
in (_0_688)::[])
in (("Valid"), (_0_689))))
in (let _0_693 = FStar_SMTEncoding_Term.Assume ((let _0_692 = (FStar_SMTEncoding_Util.mkForall (let _0_691 = (FStar_SMTEncoding_Util.mkIff (let _0_690 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in ((_0_690), (valid))))
in ((((valid)::[])::[]), ((aa)::(xx)::(yy)::[]), (_0_691))))
in ((_0_692), (Some ("Eq2 interpretation")), (Some ("eq2-interp")))))
in (_0_693)::[])))))))))
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

let valid = (FStar_SMTEncoding_Util.mkApp (let _0_695 = (let _0_694 = (FStar_SMTEncoding_Util.mkApp ((eq3), ((a)::(b)::(x)::(y)::[])))
in (_0_694)::[])
in (("Valid"), (_0_695))))
in (let _0_699 = FStar_SMTEncoding_Term.Assume ((let _0_698 = (FStar_SMTEncoding_Util.mkForall (let _0_697 = (FStar_SMTEncoding_Util.mkIff (let _0_696 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in ((_0_696), (valid))))
in ((((valid)::[])::[]), ((aa)::(bb)::(xx)::(yy)::[]), (_0_697))))
in ((_0_698), (Some ("Eq3 interpretation")), (Some ("eq3-interp")))))
in (_0_699)::[])))))))))))
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

let valid = (FStar_SMTEncoding_Util.mkApp (let _0_701 = (let _0_700 = (FStar_SMTEncoding_Util.mkApp ((imp), ((a)::(b)::[])))
in (_0_700)::[])
in (("Valid"), (_0_701))))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (let _0_705 = FStar_SMTEncoding_Term.Assume ((let _0_704 = (FStar_SMTEncoding_Util.mkForall (let _0_703 = (FStar_SMTEncoding_Util.mkIff (let _0_702 = (FStar_SMTEncoding_Util.mkImp ((valid_a), (valid_b)))
in ((_0_702), (valid))))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_0_703))))
in ((_0_704), (Some ("==> interpretation")), (Some ("l_imp-interp")))))
in (_0_705)::[])))))))))
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

let valid = (FStar_SMTEncoding_Util.mkApp (let _0_707 = (let _0_706 = (FStar_SMTEncoding_Util.mkApp ((iff), ((a)::(b)::[])))
in (_0_706)::[])
in (("Valid"), (_0_707))))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (let _0_711 = FStar_SMTEncoding_Term.Assume ((let _0_710 = (FStar_SMTEncoding_Util.mkForall (let _0_709 = (FStar_SMTEncoding_Util.mkIff (let _0_708 = (FStar_SMTEncoding_Util.mkIff ((valid_a), (valid_b)))
in ((_0_708), (valid))))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_0_709))))
in ((_0_710), (Some ("<==> interpretation")), (Some ("l_iff-interp")))))
in (_0_711)::[])))))))))
in (

let mk_not_interp = (fun env l_not tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let valid = (FStar_SMTEncoding_Util.mkApp (let _0_713 = (let _0_712 = (FStar_SMTEncoding_Util.mkApp ((l_not), ((a)::[])))
in (_0_712)::[])
in (("Valid"), (_0_713))))
in (

let not_valid_a = (let _0_714 = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot _0_714))
in (let _0_717 = FStar_SMTEncoding_Term.Assume ((let _0_716 = (FStar_SMTEncoding_Util.mkForall (let _0_715 = (FStar_SMTEncoding_Util.mkIff ((not_valid_a), (valid)))
in ((((valid)::[])::[]), ((aa)::[]), (_0_715))))
in ((_0_716), (Some ("not interpretation")), (Some ("l_not-interp")))))
in (_0_717)::[]))))))
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

let valid = (FStar_SMTEncoding_Util.mkApp (let _0_719 = (let _0_718 = (FStar_SMTEncoding_Util.mkApp ((for_all), ((a)::(b)::[])))
in (_0_718)::[])
in (("Valid"), (_0_719))))
in (

let valid_b_x = (FStar_SMTEncoding_Util.mkApp (let _0_721 = (let _0_720 = (FStar_SMTEncoding_Util.mk_ApplyTT b x)
in (_0_720)::[])
in (("Valid"), (_0_721))))
in (let _0_730 = FStar_SMTEncoding_Term.Assume ((let _0_729 = (FStar_SMTEncoding_Util.mkForall (let _0_728 = (FStar_SMTEncoding_Util.mkIff (let _0_727 = (FStar_SMTEncoding_Util.mkForall (let _0_726 = (let _0_723 = (let _0_722 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_0_722)::[])
in (_0_723)::[])
in (let _0_725 = (FStar_SMTEncoding_Util.mkImp (let _0_724 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((_0_724), (valid_b_x))))
in ((_0_726), ((xx)::[]), (_0_725)))))
in ((_0_727), (valid))))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_0_728))))
in ((_0_729), (Some ("forall interpretation")), (Some ("forall-interp")))))
in (_0_730)::[]))))))))))
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

let valid = (FStar_SMTEncoding_Util.mkApp (let _0_732 = (let _0_731 = (FStar_SMTEncoding_Util.mkApp ((for_some), ((a)::(b)::[])))
in (_0_731)::[])
in (("Valid"), (_0_732))))
in (

let valid_b_x = (FStar_SMTEncoding_Util.mkApp (let _0_734 = (let _0_733 = (FStar_SMTEncoding_Util.mk_ApplyTT b x)
in (_0_733)::[])
in (("Valid"), (_0_734))))
in (let _0_743 = FStar_SMTEncoding_Term.Assume ((let _0_742 = (FStar_SMTEncoding_Util.mkForall (let _0_741 = (FStar_SMTEncoding_Util.mkIff (let _0_740 = (FStar_SMTEncoding_Util.mkExists (let _0_739 = (let _0_736 = (let _0_735 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_0_735)::[])
in (_0_736)::[])
in (let _0_738 = (FStar_SMTEncoding_Util.mkImp (let _0_737 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((_0_737), (valid_b_x))))
in ((_0_739), ((xx)::[]), (_0_738)))))
in ((_0_740), (valid))))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_0_741))))
in ((_0_742), (Some ("exists interpretation")), (Some ("exists-interp")))))
in (_0_743)::[]))))))))))
in (

let mk_range_interp = (fun env range tt -> (

let range_ty = (FStar_SMTEncoding_Util.mkApp ((range), ([])))
in (let _0_746 = FStar_SMTEncoding_Term.Assume ((let _0_745 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_ty)
in (let _0_744 = Some ((varops.mk_unique "typing_range_const"))
in ((_0_745), (Some ("Range_const typing")), (_0_744)))))
in (_0_746)::[])))
in (

let prims = (((FStar_Syntax_Const.unit_lid), (mk_unit)))::(((FStar_Syntax_Const.bool_lid), (mk_bool)))::(((FStar_Syntax_Const.int_lid), (mk_int)))::(((FStar_Syntax_Const.string_lid), (mk_str)))::(((FStar_Syntax_Const.ref_lid), (mk_ref)))::(((FStar_Syntax_Const.true_lid), (mk_true_interp)))::(((FStar_Syntax_Const.false_lid), (mk_false_interp)))::(((FStar_Syntax_Const.and_lid), (mk_and_interp)))::(((FStar_Syntax_Const.or_lid), (mk_or_interp)))::(((FStar_Syntax_Const.eq2_lid), (mk_eq2_interp)))::(((FStar_Syntax_Const.eq3_lid), (mk_eq3_interp)))::(((FStar_Syntax_Const.imp_lid), (mk_imp_interp)))::(((FStar_Syntax_Const.iff_lid), (mk_iff_interp)))::(((FStar_Syntax_Const.not_lid), (mk_not_interp)))::(((FStar_Syntax_Const.forall_lid), (mk_forall_interp)))::(((FStar_Syntax_Const.exists_lid), (mk_exists_interp)))::(((FStar_Syntax_Const.range_lid), (mk_range_interp)))::[]
in (fun env t s tt -> (

let uu____7897 = (FStar_Util.find_opt (fun uu____7915 -> (match (uu____7915) with
| (l, uu____7925) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)
in (match (uu____7897) with
| None -> begin
[]
end
| Some (uu____7947, f) -> begin
(f env s tt)
end)))))))))))))))))))))))))


let encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____7984 = (encode_function_type_as_formula None None t env)
in (match (uu____7984) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_SMTEncoding_Term.Assume (((form), (Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str))), (Some ((Prims.strcat "lemma_" lid.FStar_Ident.str))))))::[]))
end))))


let encode_free_var : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env fv tt t_norm quals -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____8017 = ((let _0_747 = (FStar_Syntax_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _0_747)) || (FStar_Syntax_Util.is_lemma t_norm))
in (match (uu____8017) with
| true -> begin
(

let uu____8021 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____8021) with
| (vname, vtok, env) -> begin
(

let arg_sorts = (

let uu____8033 = (FStar_Syntax_Subst.compress t_norm).FStar_Syntax_Syntax.n
in (match (uu____8033) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____8036) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun uu____8053 -> FStar_SMTEncoding_Term.Term_sort)))
end
| uu____8056 -> begin
[]
end))
in (

let d = FStar_SMTEncoding_Term.DeclFun (((vname), (arg_sorts), (FStar_SMTEncoding_Term.Term_sort), (Some ("Uninterpreted function symbol for impure function"))))
in (

let dd = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Uninterpreted name for impure function"))))
in (((d)::(dd)::[]), (env)))))
end))
end
| uu____8064 -> begin
(

let uu____8065 = (prims.is lid)
in (match (uu____8065) with
| true -> begin
(

let vname = (varops.new_fvar lid)
in (

let uu____8070 = (prims.mk lid vname)
in (match (uu____8070) with
| (tok, definition) -> begin
(

let env = (push_free_var env lid vname (Some (tok)))
in ((definition), (env)))
end)))
end
| uu____8083 -> begin
(

let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (

let uu____8085 = (

let uu____8091 = (curried_arrow_formals_comp t_norm)
in (match (uu____8091) with
| (args, comp) -> begin
(match (encode_non_total_function_typ) with
| true -> begin
(let _0_748 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in ((args), (_0_748)))
end
| uu____8109 -> begin
((args), (((None), ((FStar_Syntax_Util.comp_result comp)))))
end)
end))
in (match (uu____8085) with
| (formals, (pre_opt, res_t)) -> begin
(

let uu____8129 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____8129) with
| (vname, vtok, env) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
end
| uu____8142 -> begin
(FStar_SMTEncoding_Util.mkApp ((vtok), ([])))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun uu___122_8166 -> (match (uu___122_8166) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(

let uu____8169 = (FStar_Util.prefix vars)
in (match (uu____8169) with
| (uu____8180, (xxsym, uu____8182)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (let _0_753 = FStar_SMTEncoding_Term.Assume ((let _0_752 = (FStar_SMTEncoding_Util.mkForall (let _0_751 = (FStar_SMTEncoding_Util.mkEq (let _0_750 = (let _0_749 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _0_749))
in ((vapp), (_0_750))))
in ((((vapp)::[])::[]), (vars), (_0_751))))
in ((_0_752), (Some ("Discriminator equation")), (Some ((Prims.strcat "disc_equation_" (escape d.FStar_Ident.str)))))))
in (_0_753)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(

let uu____8203 = (FStar_Util.prefix vars)
in (match (uu____8203) with
| (uu____8214, (xxsym, uu____8216)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (

let tp_name = (mk_term_projector_name d f)
in (

let prim_app = (FStar_SMTEncoding_Util.mkApp ((tp_name), ((xx)::[])))
in (let _0_756 = FStar_SMTEncoding_Term.Assume ((let _0_755 = (FStar_SMTEncoding_Util.mkForall (let _0_754 = (FStar_SMTEncoding_Util.mkEq ((vapp), (prim_app)))
in ((((vapp)::[])::[]), (vars), (_0_754))))
in ((_0_755), (Some ("Projector equation")), (Some ((Prims.strcat "proj_equation_" tp_name))))))
in (_0_756)::[])))))
end))
end
| uu____8239 -> begin
[]
end)))))
in (

let uu____8240 = (encode_binders None formals env)
in (match (uu____8240) with
| (vars, guards, env', decls1, uu____8256) -> begin
(

let uu____8263 = (match (pre_opt) with
| None -> begin
(let _0_757 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((_0_757), (decls1)))
end
| Some (p) -> begin
(

let uu____8269 = (encode_formula p env')
in (match (uu____8269) with
| (g, ds) -> begin
(let _0_758 = (FStar_SMTEncoding_Util.mk_and_l ((g)::guards))
in ((_0_758), ((FStar_List.append decls1 ds))))
end))
end)
in (match (uu____8263) with
| (guard, decls1) -> begin
(

let vtok_app = (mk_Apply vtok_tm vars)
in (

let vapp = (FStar_SMTEncoding_Util.mkApp (let _0_759 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((vname), (_0_759))))
in (

let uu____8287 = (

let vname_decl = FStar_SMTEncoding_Term.DeclFun ((let _0_760 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____8297 -> FStar_SMTEncoding_Term.Term_sort)))
in ((vname), (_0_760), (FStar_SMTEncoding_Term.Term_sort), (None))))
in (

let uu____8300 = (

let env = (

let uu___150_8304 = env
in {bindings = uu___150_8304.bindings; depth = uu___150_8304.depth; tcenv = uu___150_8304.tcenv; warn = uu___150_8304.warn; cache = uu___150_8304.cache; nolabels = uu___150_8304.nolabels; use_zfuel_name = uu___150_8304.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in (

let uu____8305 = (not ((head_normal env tt)))
in (match (uu____8305) with
| true -> begin
(encode_term_pred None tt env vtok_tm)
end
| uu____8308 -> begin
(encode_term_pred None t_norm env vtok_tm)
end)))
in (match (uu____8300) with
| (tok_typing, decls2) -> begin
(

let tok_typing = FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("function token typing")), (Some ((Prims.strcat "function_token_typing_" vname)))))
in (

let uu____8317 = (match (formals) with
| [] -> begin
(let _0_764 = (let _0_763 = (let _0_762 = (FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left (fun _0_761 -> Some (_0_761)) _0_762))
in (push_free_var env lid vname _0_763))
in (((FStar_List.append decls2 ((tok_typing)::[]))), (_0_764)))
end
| uu____8328 -> begin
(

let vtok_decl = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let vtok_fresh = (let _0_765 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((vtok), (FStar_SMTEncoding_Term.Term_sort)) _0_765))
in (

let name_tok_corr = FStar_SMTEncoding_Term.Assume ((let _0_767 = (FStar_SMTEncoding_Util.mkForall (let _0_766 = (FStar_SMTEncoding_Util.mkEq ((vtok_app), (vapp)))
in ((((vtok_app)::[])::((vapp)::[])::[]), (vars), (_0_766))))
in ((_0_767), (Some ("Name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" vname))))))
in (((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[]))), (env)))))
end)
in (match (uu____8317) with
| (tok_decl, env) -> begin
(((vname_decl)::tok_decl), (env))
end)))
end)))
in (match (uu____8287) with
| (decls2, env) -> begin
(

let uu____8358 = (

let res_t = (FStar_Syntax_Subst.compress res_t)
in (

let uu____8363 = (encode_term res_t env')
in (match (uu____8363) with
| (encoded_res_t, decls) -> begin
(let _0_768 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in ((encoded_res_t), (_0_768), (decls)))
end)))
in (match (uu____8358) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = FStar_SMTEncoding_Term.Assume ((let _0_770 = (FStar_SMTEncoding_Util.mkForall (let _0_769 = (FStar_SMTEncoding_Util.mkImp ((guard), (ty_pred)))
in ((((vapp)::[])::[]), (vars), (_0_769))))
in ((_0_770), (Some ("free var typing")), (Some ((Prims.strcat "typing_" vname))))))
in (

let freshness = (

let uu____8387 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New))
in (match (uu____8387) with
| true -> begin
(let _0_775 = (FStar_SMTEncoding_Term.fresh_constructor (let _0_772 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (let _0_771 = (varops.next_id ())
in ((vname), (_0_772), (FStar_SMTEncoding_Term.Term_sort), (_0_771)))))
in (let _0_774 = (let _0_773 = (pretype_axiom vapp vars)
in (_0_773)::[])
in (_0_775)::_0_774))
end
| uu____8395 -> begin
[]
end))
in (

let g = (let _0_780 = (let _0_779 = (let _0_778 = (let _0_777 = (let _0_776 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_0_776)
in (FStar_List.append freshness _0_777))
in (FStar_List.append decls3 _0_778))
in (FStar_List.append decls2 _0_779))
in (FStar_List.append decls1 _0_780))
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

let uu____8418 = (try_lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____8418) with
| None -> begin
(

let uu____8441 = (encode_free_var env x t t_norm [])
in (match (uu____8441) with
| (decls, env) -> begin
(

let uu____8456 = (lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____8456) with
| (n, x', uu____8475) -> begin
((((n), (x'))), (decls), (env))
end))
end))
end
| Some (n, x, uu____8487) -> begin
((((n), (x))), ([]), (env))
end)))


let encode_top_level_val : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env lid t quals -> (

let tt = (norm env t)
in (

let uu____8520 = (encode_free_var env lid t tt quals)
in (match (uu____8520) with
| (decls, env) -> begin
(

let uu____8531 = (FStar_Syntax_Util.is_smt_lemma t)
in (match (uu____8531) with
| true -> begin
(let _0_782 = (let _0_781 = (encode_smt_lemma env lid tt)
in (FStar_List.append decls _0_781))
in ((_0_782), (env)))
end
| uu____8536 -> begin
((decls), (env))
end))
end))))


let encode_top_level_vals : env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____8561 lb -> (match (uu____8561) with
| (decls, env) -> begin
(

let uu____8573 = (let _0_783 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env _0_783 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (uu____8573) with
| (decls', env) -> begin
(((FStar_List.append decls decls')), (env))
end))
end)) (([]), (env)))))


let encode_top_level_let : env_t  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env uu____8600 quals -> (match (uu____8600) with
| (is_rec, bindings) -> begin
(

let eta_expand = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let uu____8649 = (FStar_Util.first_N nbinders formals)
in (match (uu____8649) with
| (formals, extra_formals) -> begin
(

let subst = (FStar_List.map2 (fun uu____8689 uu____8690 -> (match (((uu____8689), (uu____8690))) with
| ((formal, uu____8700), (binder, uu____8702)) -> begin
FStar_Syntax_Syntax.NT ((let _0_784 = (FStar_Syntax_Syntax.bv_to_name binder)
in ((formal), (_0_784))))
end)) formals binders)
in (

let extra_formals = (let _0_787 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun uu____8727 -> (match (uu____8727) with
| (x, i) -> begin
(let _0_786 = (

let uu___151_8734 = x
in (let _0_785 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___151_8734.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___151_8734.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_785}))
in ((_0_786), (i)))
end))))
in (FStar_All.pipe_right _0_787 FStar_Syntax_Util.name_binders))
in (

let body = (let _0_793 = (let _0_792 = (FStar_Syntax_Subst.subst subst t).FStar_Syntax_Syntax.n
in (FStar_All.pipe_left (fun _0_791 -> Some (_0_791)) _0_792))
in ((let _0_790 = (FStar_Syntax_Subst.compress body)
in (let _0_789 = (let _0_788 = (FStar_Syntax_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _0_788))
in (FStar_Syntax_Syntax.extend_app_n _0_790 _0_789))) _0_793 body.FStar_Syntax_Syntax.pos))
in (((FStar_List.append binders extra_formals)), (body)))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (

let rec aux = (fun norm t_norm -> (

let uu____8818 = (FStar_Syntax_Util.unascribe e).FStar_Syntax_Syntax.n
in (match (uu____8818) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, lopt) -> begin
(

let uu____8858 = (FStar_Syntax_Subst.open_term' binders body)
in (match (uu____8858) with
| (binders, body, opening) -> begin
(

let uu____8879 = (FStar_Syntax_Subst.compress t_norm).FStar_Syntax_Syntax.n
in (match (uu____8879) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____8906 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____8906) with
| (formals, c) -> begin
(

let nformals = (FStar_List.length formals)
in (

let nbinders = (FStar_List.length binders)
in (

let tres = (FStar_Syntax_Util.comp_result c)
in (

let uu____8936 = ((nformals < nbinders) && (FStar_Syntax_Util.is_total_comp c))
in (match (uu____8936) with
| true -> begin
(

let lopt = (subst_lcomp_opt opening lopt)
in (

let uu____8966 = (FStar_Util.first_N nformals binders)
in (match (uu____8966) with
| (bs0, rest) -> begin
(

let c = (

let subst = (FStar_List.map2 (fun uu____9014 uu____9015 -> (match (((uu____9014), (uu____9015))) with
| ((b, uu____9025), (x, uu____9027)) -> begin
FStar_Syntax_Syntax.NT ((let _0_794 = (FStar_Syntax_Syntax.bv_to_name x)
in ((b), (_0_794))))
end)) bs0 formals)
in (FStar_Syntax_Subst.subst_comp subst c))
in (

let body = (FStar_Syntax_Util.abs rest body lopt)
in ((((bs0), (body), (bs0), ((FStar_Syntax_Util.comp_result c)))), (false))))
end)))
end
| uu____9053 -> begin
(match ((nformals > nbinders)) with
| true -> begin
(

let uu____9073 = (eta_expand binders formals body tres)
in (match (uu____9073) with
| (binders, body) -> begin
((((binders), (body), (formals), (tres))), (false))
end))
end
| uu____9125 -> begin
((((binders), (body), (formals), (tres))), (false))
end)
end)))))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____9135) -> begin
(let _0_795 = (Prims.fst (aux norm x.FStar_Syntax_Syntax.sort))
in ((_0_795), (true)))
end
| uu____9164 when (not (norm)) -> begin
(

let t_norm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm)
in (aux true t_norm))
end
| uu____9166 -> begin
(failwith (let _0_797 = (FStar_Syntax_Print.term_to_string e)
in (let _0_796 = (FStar_Syntax_Print.term_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str _0_797 _0_796))))
end))
end))
end
| uu____9181 -> begin
(

let uu____9182 = (FStar_Syntax_Subst.compress t_norm).FStar_Syntax_Syntax.n
in (match (uu____9182) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____9209 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____9209) with
| (formals, c) -> begin
(

let tres = (FStar_Syntax_Util.comp_result c)
in (

let uu____9231 = (eta_expand [] formals e tres)
in (match (uu____9231) with
| (binders, body) -> begin
((((binders), (body), (formals), (tres))), (false))
end)))
end))
end
| uu____9285 -> begin
(((([]), (e), ([]), (t_norm))), (false))
end))
end)))
in (aux false t_norm)))
in try
(match (()) with
| () -> begin
(

let uu____9313 = (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp))))
in (match (uu____9313) with
| true -> begin
(encode_top_level_vals env bindings quals)
end
| uu____9319 -> begin
(

let uu____9320 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____9361 lb -> (match (uu____9361) with
| (toks, typs, decls, env) -> begin
((

let uu____9412 = (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp)
in (match (uu____9412) with
| true -> begin
(Prims.raise Let_rec_unencodeable)
end
| uu____9413 -> begin
()
end));
(

let t_norm = (whnf env lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____9415 = (let _0_798 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env _0_798 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (uu____9415) with
| (tok, decl, env) -> begin
(let _0_801 = (let _0_800 = (let _0_799 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in ((_0_799), (tok)))
in (_0_800)::toks)
in ((_0_801), ((t_norm)::typs), ((decl)::decls), (env)))
end)));
)
end)) (([]), ([]), ([]), (env))))
in (match (uu____9320) with
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
| uu____9548 -> begin
(match (curry) with
| true -> begin
(match (ftok) with
| Some (ftok) -> begin
(mk_Apply ftok vars)
end
| None -> begin
(let _0_802 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply _0_802 vars))
end)
end
| uu____9553 -> begin
(FStar_SMTEncoding_Util.mkApp (let _0_803 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (_0_803))))
end)
end))
in (

let uu____9557 = ((FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___123_9559 -> (match (uu___123_9559) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| uu____9560 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> (let _0_804 = (FStar_Syntax_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _0_804))))))
in (match (uu____9557) with
| true -> begin
((decls), (env))
end
| uu____9567 -> begin
(match ((not (is_rec))) with
| true -> begin
(match (((bindings), (typs), (toks))) with
| (({FStar_Syntax_Syntax.lbname = uu____9582; FStar_Syntax_Syntax.lbunivs = uu____9583; FStar_Syntax_Syntax.lbtyp = uu____9584; FStar_Syntax_Syntax.lbeff = uu____9585; FStar_Syntax_Syntax.lbdef = e})::[], (t_norm)::[], ((flid_fv, (f, ftok)))::[]) -> begin
(

let e = (FStar_Syntax_Subst.compress e)
in (

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____9627 = (destruct_bound_function flid t_norm e)
in (match (uu____9627) with
| ((binders, body, uu____9647, uu____9648), curry) -> begin
(

let uu____9678 = (encode_binders None binders env)
in (match (uu____9678) with
| (vars, guards, env', binder_decls, uu____9694) -> begin
(

let app = (mk_app curry f ftok vars)
in (

let uu____9702 = (

let uu____9707 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic))
in (match (uu____9707) with
| true -> begin
(let _0_806 = (FStar_SMTEncoding_Term.mk_Valid app)
in (let _0_805 = (encode_formula body env')
in ((_0_806), (_0_805))))
end
| uu____9715 -> begin
(let _0_807 = (encode_term body env')
in ((app), (_0_807)))
end))
in (match (uu____9702) with
| (app, (body, decls2)) -> begin
(

let eqn = FStar_SMTEncoding_Term.Assume ((let _0_810 = (FStar_SMTEncoding_Util.mkForall (let _0_808 = (FStar_SMTEncoding_Util.mkEq ((app), (body)))
in ((((app)::[])::[]), (vars), (_0_808))))
in (let _0_809 = Some ((FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str))
in ((_0_810), (_0_809), (Some ((Prims.strcat "equation_" f)))))))
in (let _0_815 = (let _0_814 = (let _0_813 = (let _0_812 = (let _0_811 = (primitive_type_axioms env.tcenv flid f app)
in (FStar_List.append ((eqn)::[]) _0_811))
in (FStar_List.append decls2 _0_812))
in (FStar_List.append binder_decls _0_813))
in (FStar_List.append decls _0_814))
in ((_0_815), (env))))
end)))
end))
end))))
end
| uu____9735 -> begin
(failwith "Impossible")
end)
end
| uu____9750 -> begin
(

let fuel = (let _0_816 = (varops.fresh "fuel")
in ((_0_816), (FStar_SMTEncoding_Term.Fuel_sort)))
in (

let fuel_tm = (FStar_SMTEncoding_Util.mkFreeV fuel)
in (

let env0 = env
in (

let uu____9756 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun uu____9795 uu____9796 -> (match (((uu____9795), (uu____9796))) with
| ((gtoks, env), (flid_fv, (f, ftok))) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let g = (varops.new_fvar (FStar_Ident.lid_add_suffix flid "fuel_instrumented"))
in (

let gtok = (varops.new_fvar (FStar_Ident.lid_add_suffix flid "fuel_instrumented_token"))
in (

let env = (let _0_819 = (let _0_818 = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::[])))
in (FStar_All.pipe_left (fun _0_817 -> Some (_0_817)) _0_818))
in (push_free_var env flid gtok _0_819))
in (((((flid), (f), (ftok), (g), (gtok)))::gtoks), (env))))))
end)) (([]), (env))))
in (match (uu____9756) with
| (gtoks, env) -> begin
(

let gtoks = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env0 uu____9963 t_norm uu____9965 -> (match (((uu____9963), (uu____9965))) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = uu____9988; FStar_Syntax_Syntax.lbunivs = uu____9989; FStar_Syntax_Syntax.lbtyp = uu____9990; FStar_Syntax_Syntax.lbeff = uu____9991; FStar_Syntax_Syntax.lbdef = e}) -> begin
(

let uu____10008 = (destruct_bound_function flid t_norm e)
in (match (uu____10008) with
| ((binders, body, formals, tres), curry) -> begin
((match (curry) with
| true -> begin
(failwith "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type")
end
| uu____10062 -> begin
()
end);
(

let uu____10063 = (encode_binders None binders env)
in (match (uu____10063) with
| (vars, guards, env', binder_decls, uu____10081) -> begin
(

let decl_g = FStar_SMTEncoding_Term.DeclFun ((let _0_821 = (let _0_820 = (FStar_List.map Prims.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::_0_820)
in ((g), (_0_821), (FStar_SMTEncoding_Term.Term_sort), (Some ("Fuel-instrumented function name")))))
in (

let env0 = (push_zfuel_name env0 flid g)
in (

let decl_g_tok = FStar_SMTEncoding_Term.DeclFun (((gtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Token for fuel-instrumented partial applications"))))
in (

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let app = (FStar_SMTEncoding_Util.mkApp (let _0_822 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (_0_822))))
in (

let gsapp = (FStar_SMTEncoding_Util.mkApp (let _0_824 = (let _0_823 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (_0_823)::vars_tm)
in ((g), (_0_824))))
in (

let gmax = (FStar_SMTEncoding_Util.mkApp (let _0_826 = (let _0_825 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (_0_825)::vars_tm)
in ((g), (_0_826))))
in (

let uu____10111 = (encode_term body env')
in (match (uu____10111) with
| (body_tm, decls2) -> begin
(

let eqn_g = FStar_SMTEncoding_Term.Assume ((let _0_829 = (FStar_SMTEncoding_Util.mkForall' (let _0_827 = (FStar_SMTEncoding_Util.mkEq ((gsapp), (body_tm)))
in ((((gsapp)::[])::[]), (Some ((Prims.parse_int "0"))), ((fuel)::vars), (_0_827))))
in (let _0_828 = Some ((FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str))
in ((_0_829), (_0_828), (Some ((Prims.strcat "equation_with_fuel_" g)))))))
in (

let eqn_f = FStar_SMTEncoding_Term.Assume ((let _0_831 = (FStar_SMTEncoding_Util.mkForall (let _0_830 = (FStar_SMTEncoding_Util.mkEq ((app), (gmax)))
in ((((app)::[])::[]), (vars), (_0_830))))
in ((_0_831), (Some ("Correspondence of recursive function to instrumented version")), (Some ((Prims.strcat "fuel_correspondence_" g))))))
in (

let eqn_g' = FStar_SMTEncoding_Term.Assume ((let _0_836 = (FStar_SMTEncoding_Util.mkForall (let _0_835 = (FStar_SMTEncoding_Util.mkEq (let _0_834 = (FStar_SMTEncoding_Util.mkApp (let _0_833 = (let _0_832 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "0"))
in (_0_832)::vars_tm)
in ((g), (_0_833))))
in ((gsapp), (_0_834))))
in ((((gsapp)::[])::[]), ((fuel)::vars), (_0_835))))
in ((_0_836), (Some ("Fuel irrelevance")), (Some ((Prims.strcat "fuel_irrelevance_" g))))))
in (

let uu____10155 = (

let uu____10160 = (encode_binders None formals env0)
in (match (uu____10160) with
| (vars, v_guards, env, binder_decls, uu____10177) -> begin
(

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let gapp = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::vars_tm)))
in (

let tok_corr = (

let tok_app = (let _0_837 = (FStar_SMTEncoding_Util.mkFreeV ((gtok), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply _0_837 ((fuel)::vars)))
in FStar_SMTEncoding_Term.Assume ((let _0_839 = (FStar_SMTEncoding_Util.mkForall (let _0_838 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (gapp)))
in ((((tok_app)::[])::[]), ((fuel)::vars), (_0_838))))
in ((_0_839), (Some ("Fuel token correspondence")), (Some ((Prims.strcat "fuel_token_correspondence_" gtok)))))))
in (

let uu____10205 = (

let uu____10209 = (encode_term_pred None tres env gapp)
in (match (uu____10209) with
| (g_typing, d3) -> begin
(let _0_844 = (let _0_843 = FStar_SMTEncoding_Term.Assume ((let _0_842 = (FStar_SMTEncoding_Util.mkForall (let _0_841 = (FStar_SMTEncoding_Util.mkImp (let _0_840 = (FStar_SMTEncoding_Util.mk_and_l v_guards)
in ((_0_840), (g_typing))))
in ((((gapp)::[])::[]), ((fuel)::vars), (_0_841))))
in ((_0_842), (Some ("Typing correspondence of token to term")), (Some ((Prims.strcat "token_correspondence_" g))))))
in (_0_843)::[])
in ((d3), (_0_844)))
end))
in (match (uu____10205) with
| (aux_decls, typing_corr) -> begin
(((FStar_List.append binder_decls aux_decls)), ((FStar_List.append typing_corr ((tok_corr)::[]))))
end)))))
end))
in (match (uu____10155) with
| (aux_decls, g_typing) -> begin
(((FStar_List.append binder_decls (FStar_List.append decls2 (FStar_List.append aux_decls ((decl_g)::(decl_g_tok)::[]))))), ((FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing)), (env0))
end)))))
end)))))))))
end));
)
end))
end))
in (

let uu____10252 = (let _0_845 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun uu____10274 uu____10275 -> (match (((uu____10274), (uu____10275))) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(

let uu____10351 = (encode_one_binding env0 gtok ty bs)
in (match (uu____10351) with
| (decls', eqns', env0) -> begin
(((decls')::decls), ((FStar_List.append eqns' eqns)), (env0))
end))
end)) (((decls)::[]), ([]), (env0)) _0_845))
in (match (uu____10252) with
| (decls, eqns, env0) -> begin
(

let uu____10397 = (let _0_846 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _0_846 (FStar_List.partition (fun uu___124_10410 -> (match (uu___124_10410) with
| FStar_SMTEncoding_Term.DeclFun (uu____10411) -> begin
true
end
| uu____10417 -> begin
false
end)))))
in (match (uu____10397) with
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

let msg = (let _0_847 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _0_847 (FStar_String.concat " and ")))
in (

let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in (((decl)::[]), (env))))
end))
end))


let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> ((

let uu____10466 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____10466) with
| true -> begin
(let _0_848 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _0_848))
end
| uu____10467 -> begin
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

let uu____10470 = (encode_sigelt' env se)
in (match (uu____10470) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _0_850 = (let _0_849 = FStar_SMTEncoding_Term.Caption ((FStar_Util.format1 "<Skipped %s/>" nm))
in (_0_849)::[])
in ((_0_850), (e)))
end
| uu____10480 -> begin
(let _0_855 = (let _0_854 = (let _0_851 = FStar_SMTEncoding_Term.Caption ((FStar_Util.format1 "<Start encoding %s>" nm))
in (_0_851)::g)
in (let _0_853 = (let _0_852 = FStar_SMTEncoding_Term.Caption ((FStar_Util.format1 "</end encoding %s>" nm))
in (_0_852)::[])
in (FStar_List.append _0_854 _0_853)))
in ((_0_855), (e)))
end)
end)));
))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let should_skip = (fun l -> false)
in (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____10492) -> begin
(failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, uu____10503) -> begin
(

let uu____10504 = (let _0_856 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right _0_856 Prims.op_Negation))
in (match (uu____10504) with
| true -> begin
(([]), (env))
end
| uu____10509 -> begin
(

let close_effect_params = (fun tm -> (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
tm
end
| uu____10524 -> begin
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs ((let _0_858 = (FStar_All.pipe_left (fun _0_857 -> Some (_0_857)) (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[])))))
in ((ed.FStar_Syntax_Syntax.binders), (tm), (_0_858)))))) None tm.FStar_Syntax_Syntax.pos)
end))
in (

let encode_action = (fun env a -> (

let uu____10571 = (new_term_constant_and_tok_from_lid env a.FStar_Syntax_Syntax.action_name)
in (match (uu____10571) with
| (aname, atok, env) -> begin
(

let uu____10581 = (FStar_Syntax_Util.arrow_formals_comp a.FStar_Syntax_Syntax.action_typ)
in (match (uu____10581) with
| (formals, uu____10591) -> begin
(

let uu____10598 = (let _0_859 = (close_effect_params a.FStar_Syntax_Syntax.action_defn)
in (encode_term _0_859 env))
in (match (uu____10598) with
| (tm, decls) -> begin
(

let a_decls = (let _0_861 = FStar_SMTEncoding_Term.DeclFun ((let _0_860 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____10616 -> FStar_SMTEncoding_Term.Term_sort)))
in ((aname), (_0_860), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action")))))
in (_0_861)::(FStar_SMTEncoding_Term.DeclFun (((atok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action token")))))::[])
in (

let uu____10621 = (let _0_862 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____10653 -> (match (uu____10653) with
| (bv, uu____10661) -> begin
(

let uu____10662 = (gen_term_var env bv)
in (match (uu____10662) with
| (xxsym, xx, uu____10672) -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (xx))
end))
end))))
in (FStar_All.pipe_right _0_862 FStar_List.split))
in (match (uu____10621) with
| (xs_sorts, xs) -> begin
(

let app = (FStar_SMTEncoding_Util.mkApp (let _0_864 = (let _0_863 = (FStar_SMTEncoding_Util.mkApp ((aname), (xs)))
in (_0_863)::[])
in (("Reify"), (_0_864))))
in (

let a_eq = FStar_SMTEncoding_Term.Assume ((let _0_867 = (FStar_SMTEncoding_Util.mkForall (let _0_866 = (FStar_SMTEncoding_Util.mkEq (let _0_865 = (mk_Apply tm xs_sorts)
in ((app), (_0_865))))
in ((((app)::[])::[]), (xs_sorts), (_0_866))))
in ((_0_867), (Some ("Action equality")), (Some ((Prims.strcat aname "_equality"))))))
in (

let tok_correspondence = (

let tok_term = (FStar_SMTEncoding_Util.mkFreeV ((atok), (FStar_SMTEncoding_Term.Term_sort)))
in (

let tok_app = (mk_Apply tok_term xs_sorts)
in FStar_SMTEncoding_Term.Assume ((let _0_869 = (FStar_SMTEncoding_Util.mkForall (let _0_868 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (app)))
in ((((tok_app)::[])::[]), (xs_sorts), (_0_868))))
in ((_0_869), (Some ("Action token correspondence")), (Some ((Prims.strcat aname "_token_correspondence"))))))))
in ((env), ((FStar_List.append decls (FStar_List.append a_decls ((a_eq)::(tok_correspondence)::[]))))))))
end)))
end))
end))
end)))
in (

let uu____10716 = (FStar_Util.fold_map encode_action env ed.FStar_Syntax_Syntax.actions)
in (match (uu____10716) with
| (env, decls2) -> begin
(((FStar_List.flatten decls2)), (env))
end))))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____10732, uu____10733, uu____10734, uu____10735) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid) -> begin
(

let uu____10738 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____10738) with
| (tname, ttok, env) -> begin
(([]), (env))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____10749, t, quals, uu____10752) -> begin
(

let will_encode_definition = (not ((FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___125_10757 -> (match (uu___125_10757) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Irreducible) -> begin
true
end
| uu____10760 -> begin
false
end))))))
in (match (will_encode_definition) with
| true -> begin
(([]), (env))
end
| uu____10764 -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____10766 = (encode_top_level_val env fv t quals)
in (match (uu____10766) with
| (decls, env) -> begin
(

let tname = lid.FStar_Ident.str
in (

let tsym = (FStar_SMTEncoding_Util.mkFreeV ((tname), (FStar_SMTEncoding_Term.Term_sort)))
in (let _0_871 = (let _0_870 = (primitive_type_axioms env.tcenv lid tname tsym)
in (FStar_List.append decls _0_870))
in ((_0_871), (env)))))
end)))
end))
end
| FStar_Syntax_Syntax.Sig_assume (l, f, uu____10781, uu____10782) -> begin
(

let uu____10785 = (encode_formula f env)
in (match (uu____10785) with
| (f, decls) -> begin
(

let g = (let _0_875 = FStar_SMTEncoding_Term.Assume ((let _0_874 = Some ((let _0_872 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" _0_872)))
in (let _0_873 = Some ((varops.mk_unique (Prims.strcat "assumption_" l.FStar_Ident.str)))
in ((f), (_0_874), (_0_873)))))
in (_0_875)::[])
in (((FStar_List.append decls g)), (env)))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, uu____10799, quals, uu____10801) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) -> begin
(

let uu____10809 = (FStar_Util.fold_map (fun env lb -> (

let lid = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname).FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____10820 = (let _0_876 = (FStar_TypeChecker_Env.try_lookup_val_decl env.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone _0_876))
in (match (uu____10820) with
| true -> begin
(

let val_decl = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), (r)))
in (

let uu____10835 = (encode_sigelt' env val_decl)
in (match (uu____10835) with
| (decls, env) -> begin
((env), (decls))
end)))
end
| uu____10842 -> begin
((env), ([]))
end)))) env (Prims.snd lbs))
in (match (uu____10809) with
| (env, decls) -> begin
(((FStar_List.flatten decls)), (env))
end))
end
| FStar_Syntax_Syntax.Sig_let ((uu____10852, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t); FStar_Syntax_Syntax.lbunivs = uu____10854; FStar_Syntax_Syntax.lbtyp = uu____10855; FStar_Syntax_Syntax.lbeff = uu____10856; FStar_Syntax_Syntax.lbdef = uu____10857})::[]), uu____10858, uu____10859, uu____10860, uu____10861) when (FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Syntax_Const.b2t_lid) -> begin
(

let uu____10877 = (new_term_constant_and_tok_from_lid env b2t.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____10877) with
| (tname, ttok, env) -> begin
(

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let valid_b2t_x = (FStar_SMTEncoding_Util.mkApp (let _0_878 = (let _0_877 = (FStar_SMTEncoding_Util.mkApp (("Prims.b2t"), ((x)::[])))
in (_0_877)::[])
in (("Valid"), (_0_878))))
in (

let decls = (let _0_883 = (let _0_882 = FStar_SMTEncoding_Term.Assume ((let _0_881 = (FStar_SMTEncoding_Util.mkForall (let _0_880 = (FStar_SMTEncoding_Util.mkEq (let _0_879 = (FStar_SMTEncoding_Util.mkApp (("BoxBool_proj_0"), ((x)::[])))
in ((valid_b2t_x), (_0_879))))
in ((((valid_b2t_x)::[])::[]), ((xx)::[]), (_0_880))))
in ((_0_881), (Some ("b2t def")), (Some ("b2t_def")))))
in (_0_882)::[])
in (FStar_SMTEncoding_Term.DeclFun (((tname), ((FStar_SMTEncoding_Term.Term_sort)::[]), (FStar_SMTEncoding_Term.Term_sort), (None))))::_0_883)
in ((decls), (env))))))
end))
end
| FStar_Syntax_Syntax.Sig_let (uu____10916, uu____10917, uu____10918, quals, uu____10920) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___126_10928 -> (match (uu___126_10928) with
| FStar_Syntax_Syntax.Discriminator (uu____10929) -> begin
true
end
| uu____10930 -> begin
false
end)))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let (uu____10932, uu____10933, lids, quals, uu____10936) when ((FStar_All.pipe_right lids (FStar_Util.for_some (fun l -> (let _0_884 = (FStar_List.hd l.FStar_Ident.ns).FStar_Ident.idText
in (_0_884 = "Prims"))))) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___127_10946 -> (match (uu___127_10946) with
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
true
end
| uu____10947 -> begin
false
end))))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____10950, uu____10951, quals, uu____10953) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___128_10965 -> (match (uu___128_10965) with
| FStar_Syntax_Syntax.Projector (uu____10966) -> begin
true
end
| uu____10969 -> begin
false
end)))) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____10976 = (try_lookup_free_var env l)
in (match (uu____10976) with
| Some (uu____10980) -> begin
(([]), (env))
end
| None -> begin
(

let se = FStar_Syntax_Syntax.Sig_declare_typ (((l), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), ((FStar_Ident.range_of_lid l))))
in (encode_sigelt env se))
end))))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____10988, uu____10989, quals, uu____10991) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) -> begin
(

let uu____11003 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n
in (match (uu____11003) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____11008) -> begin
(

let body = (FStar_Syntax_Util.mk_reify body)
in (

let tm = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None))))) None lb.FStar_Syntax_Syntax.lbdef.FStar_Syntax_Syntax.pos)
in (

let tm' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env.tcenv tm)
in (

let lb_typ = (

let uu____11065 = (FStar_Syntax_Util.arrow_formals_comp lb.FStar_Syntax_Syntax.lbtyp)
in (match (uu____11065) with
| (formals, comp) -> begin
(

let reified_typ = (FStar_TypeChecker_Util.reify_comp (

let uu___154_11082 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___154_11082.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___154_11082.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___154_11082.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___154_11082.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___154_11082.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___154_11082.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___154_11082.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___154_11082.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___154_11082.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___154_11082.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___154_11082.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___154_11082.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___154_11082.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___154_11082.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___154_11082.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___154_11082.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___154_11082.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___154_11082.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___154_11082.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___154_11082.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___154_11082.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___154_11082.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___154_11082.FStar_TypeChecker_Env.qname_and_index}) (FStar_Syntax_Util.lcomp_of_comp comp) FStar_Syntax_Syntax.U_unknown)
in (let _0_885 = (FStar_Syntax_Syntax.mk_Total reified_typ)
in (FStar_Syntax_Util.arrow formals _0_885)))
end))
in (

let lb = (

let uu___155_11084 = lb
in {FStar_Syntax_Syntax.lbname = uu___155_11084.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___155_11084.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lb_typ; FStar_Syntax_Syntax.lbeff = uu___155_11084.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = tm'})
in (encode_top_level_let env ((false), ((lb)::[])) quals))))))
end
| uu____11086 -> begin
(([]), (env))
end))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), uu____11090, uu____11091, quals, uu____11093) -> begin
(encode_top_level_let env ((is_rec), (bindings)) quals)
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____11107, uu____11108, uu____11109) -> begin
(

let uu____11116 = (encode_signature env ses)
in (match (uu____11116) with
| (g, env) -> begin
(

let uu____11126 = (FStar_All.pipe_right g (FStar_List.partition (fun uu___129_11136 -> (match (uu___129_11136) with
| FStar_SMTEncoding_Term.Assume (uu____11137, Some ("inversion axiom"), uu____11138) -> begin
false
end
| uu____11142 -> begin
true
end))))
in (match (uu____11126) with
| (g', inversions) -> begin
(

let uu____11151 = (FStar_All.pipe_right g' (FStar_List.partition (fun uu___130_11161 -> (match (uu___130_11161) with
| FStar_SMTEncoding_Term.DeclFun (uu____11162) -> begin
true
end
| uu____11168 -> begin
false
end))))
in (match (uu____11151) with
| (decls, rest) -> begin
(((FStar_List.append decls (FStar_List.append rest inversions))), (env))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, uu____11179, tps, k, uu____11182, datas, quals, uu____11185) -> begin
(

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___131_11194 -> (match (uu___131_11194) with
| (FStar_Syntax_Syntax.Logic) | (FStar_Syntax_Syntax.Assumption) -> begin
true
end
| uu____11195 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> (match (is_logical) with
| true -> begin
(

let uu____11218 = c
in (match (uu____11218) with
| (name, args, uu____11230, uu____11231, uu____11232) -> begin
(let _0_887 = FStar_SMTEncoding_Term.DeclFun ((let _0_886 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in ((name), (_0_886), (FStar_SMTEncoding_Term.Term_sort), (None))))
in (_0_887)::[])
end))
end
| uu____11247 -> begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end))
in (

let inversion_axioms = (fun tapp vars -> (

let uu____11262 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _0_888 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right _0_888 FStar_Option.isNone)))))
in (match (uu____11262) with
| true -> begin
[]
end
| uu____11271 -> begin
(

let uu____11272 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____11272) with
| (xxsym, xx) -> begin
(

let uu____11278 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun uu____11289 l -> (match (uu____11289) with
| (out, decls) -> begin
(

let uu____11301 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (uu____11301) with
| (uu____11307, data_t) -> begin
(

let uu____11309 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (uu____11309) with
| (args, res) -> begin
(

let indices = (

let uu____11338 = (FStar_Syntax_Subst.compress res).FStar_Syntax_Syntax.n
in (match (uu____11338) with
| FStar_Syntax_Syntax.Tm_app (uu____11344, indices) -> begin
indices
end
| uu____11360 -> begin
[]
end))
in (

let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env uu____11372 -> (match (uu____11372) with
| (x, uu____11376) -> begin
(let _0_890 = (FStar_SMTEncoding_Util.mkApp (let _0_889 = (mk_term_projector_name l x)
in ((_0_889), ((xx)::[]))))
in (push_term_var env x _0_890))
end)) env))
in (

let uu____11378 = (encode_args indices env)
in (match (uu____11378) with
| (indices, decls') -> begin
((match (((FStar_List.length indices) <> (FStar_List.length vars))) with
| true -> begin
(failwith "Impossible")
end
| uu____11396 -> begin
()
end);
(

let eqs = (let _0_892 = (FStar_List.map2 (fun v a -> (FStar_SMTEncoding_Util.mkEq (let _0_891 = (FStar_SMTEncoding_Util.mkFreeV v)
in ((_0_891), (a))))) vars indices)
in (FStar_All.pipe_right _0_892 FStar_SMTEncoding_Util.mk_and_l))
in (let _0_895 = (FStar_SMTEncoding_Util.mkOr (let _0_894 = (FStar_SMTEncoding_Util.mkAnd (let _0_893 = (mk_data_tester env l xx)
in ((_0_893), (eqs))))
in ((out), (_0_894))))
in ((_0_895), ((FStar_List.append decls decls')))));
)
end))))
end))
end))
end)) ((FStar_SMTEncoding_Util.mkFalse), ([]))))
in (match (uu____11278) with
| (data_ax, decls) -> begin
(

let uu____11412 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____11412) with
| (ffsym, ff) -> begin
(

let fuel_guarded_inversion = (

let xx_has_type_sfuel = (match (((FStar_List.length datas) > (Prims.parse_int "1"))) with
| true -> begin
(let _0_896 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((ff)::[])))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel _0_896 xx tapp))
end
| uu____11424 -> begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end)
in FStar_SMTEncoding_Term.Assume ((let _0_900 = (FStar_SMTEncoding_Util.mkForall (let _0_898 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (let _0_897 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_sfuel), (data_ax)))
in ((((xx_has_type_sfuel)::[])::[]), (_0_898), (_0_897)))))
in (let _0_899 = Some ((varops.mk_unique (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str)))
in ((_0_900), (Some ("inversion axiom")), (_0_899))))))
in (

let pattern_guarded_inversion = (

let uu____11440 = ((contains_name env "Prims.inversion") && ((FStar_List.length datas) > (Prims.parse_int "1")))
in (match (uu____11440) with
| true -> begin
(

let xx_has_type_fuel = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let pattern_guard = (FStar_SMTEncoding_Util.mkApp (("Prims.inversion"), ((tapp)::[])))
in (let _0_905 = FStar_SMTEncoding_Term.Assume ((let _0_904 = (FStar_SMTEncoding_Util.mkForall (let _0_902 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (let _0_901 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_fuel), (data_ax)))
in ((((xx_has_type_fuel)::(pattern_guard)::[])::[]), (_0_902), (_0_901)))))
in (let _0_903 = Some ((varops.mk_unique (Prims.strcat "pattern_guarded_inversion_" t.FStar_Ident.str)))
in ((_0_904), (Some ("inversion axiom")), (_0_903)))))
in (_0_905)::[])))
end
| uu____11461 -> begin
[]
end))
in (FStar_List.append decls (FStar_List.append ((fuel_guarded_inversion)::[]) pattern_guarded_inversion))))
end))
end))
end))
end)))
in (

let uu____11462 = (

let uu____11470 = (FStar_Syntax_Subst.compress k).FStar_Syntax_Syntax.n
in (match (uu____11470) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
(((FStar_List.append tps formals)), ((FStar_Syntax_Util.comp_result kres)))
end
| uu____11497 -> begin
((tps), (k))
end))
in (match (uu____11462) with
| (formals, res) -> begin
(

let uu____11512 = (FStar_Syntax_Subst.open_term formals res)
in (match (uu____11512) with
| (formals, res) -> begin
(

let uu____11519 = (encode_binders None formals env)
in (match (uu____11519) with
| (vars, guards, env', binder_decls, uu____11534) -> begin
(

let uu____11541 = (new_term_constant_and_tok_from_lid env t)
in (match (uu____11541) with
| (tname, ttok, env) -> begin
(

let ttok_tm = (FStar_SMTEncoding_Util.mkApp ((ttok), ([])))
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let tapp = (FStar_SMTEncoding_Util.mkApp (let _0_906 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((tname), (_0_906))))
in (

let uu____11557 = (

let tname_decl = (constructor_or_logic_type_decl (let _0_908 = (FStar_All.pipe_right vars (FStar_List.map (fun uu____11574 -> (match (uu____11574) with
| (n, s) -> begin
(((Prims.strcat tname n)), (s))
end))))
in (let _0_907 = (varops.next_id ())
in ((tname), (_0_908), (FStar_SMTEncoding_Term.Term_sort), (_0_907), (false)))))
in (

let uu____11581 = (match (vars) with
| [] -> begin
(let _0_912 = (let _0_911 = (let _0_910 = (FStar_SMTEncoding_Util.mkApp ((tname), ([])))
in (FStar_All.pipe_left (fun _0_909 -> Some (_0_909)) _0_910))
in (push_free_var env t tname _0_911))
in (([]), (_0_912)))
end
| uu____11591 -> begin
(

let ttok_decl = FStar_SMTEncoding_Term.DeclFun (((ttok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("token"))))
in (

let ttok_fresh = (let _0_913 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ttok), (FStar_SMTEncoding_Term.Term_sort)) _0_913))
in (

let ttok_app = (mk_Apply ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = FStar_SMTEncoding_Term.Assume ((let _0_915 = (FStar_SMTEncoding_Util.mkForall' (let _0_914 = (FStar_SMTEncoding_Util.mkEq ((ttok_app), (tapp)))
in ((pats), (None), (vars), (_0_914))))
in ((_0_915), (Some ("name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" ttok))))))
in (((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[]), (env)))))))
end)
in (match (uu____11581) with
| (tok_decls, env) -> begin
(((FStar_List.append tname_decl tok_decls)), (env))
end)))
in (match (uu____11557) with
| (decls, env) -> begin
(

let kindingAx = (

let uu____11628 = (encode_term_pred None res env' tapp)
in (match (uu____11628) with
| (k, decls) -> begin
(

let karr = (match (((FStar_List.length formals) > (Prims.parse_int "0"))) with
| true -> begin
(let _0_918 = FStar_SMTEncoding_Term.Assume ((let _0_917 = (let _0_916 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _0_916))
in ((_0_917), (Some ("kinding")), (Some ((Prims.strcat "pre_kinding_" ttok))))))
in (_0_918)::[])
end
| uu____11644 -> begin
[]
end)
in (let _0_923 = (let _0_922 = (let _0_921 = FStar_SMTEncoding_Term.Assume ((let _0_920 = (FStar_SMTEncoding_Util.mkForall (let _0_919 = (FStar_SMTEncoding_Util.mkImp ((guard), (k)))
in ((((tapp)::[])::[]), (vars), (_0_919))))
in ((_0_920), (None), (Some ((Prims.strcat "kinding_" ttok))))))
in (_0_921)::[])
in (FStar_List.append karr _0_922))
in (FStar_List.append decls _0_923)))
end))
in (

let aux = (let _0_927 = (let _0_926 = (inversion_axioms tapp vars)
in (let _0_925 = (let _0_924 = (pretype_axiom tapp vars)
in (_0_924)::[])
in (FStar_List.append _0_926 _0_925)))
in (FStar_List.append kindingAx _0_927))
in (

let g = (FStar_List.append decls (FStar_List.append binder_decls aux))
in ((g), (env)))))
end)))))
end))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____11658, uu____11659, uu____11660, uu____11661, uu____11662, uu____11663, uu____11664) when (FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____11671, t, uu____11673, n_tps, quals, uu____11676, drange) -> begin
(

let uu____11682 = (new_term_constant_and_tok_from_lid env d)
in (match (uu____11682) with
| (ddconstrsym, ddtok, env) -> begin
(

let ddtok_tm = (FStar_SMTEncoding_Util.mkApp ((ddtok), ([])))
in (

let uu____11693 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____11693) with
| (formals, t_res) -> begin
(

let uu____11715 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____11715) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (

let uu____11724 = (encode_binders (Some (fuel_tm)) formals env)
in (match (uu____11724) with
| (vars, guards, env', binder_decls, names) -> begin
(

let projectors = (FStar_All.pipe_right names (FStar_List.map (fun x -> (let _0_928 = (mk_term_projector_name d x)
in ((_0_928), (FStar_SMTEncoding_Term.Term_sort))))))
in (

let datacons = (let _0_930 = (let _0_929 = (varops.next_id ())
in ((ddconstrsym), (projectors), (FStar_SMTEncoding_Term.Term_sort), (_0_929), (true)))
in (FStar_All.pipe_right _0_930 FStar_SMTEncoding_Term.constructor_to_decl))
in (

let app = (mk_Apply ddtok_tm vars)
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (

let uu____11777 = (encode_term_pred None t env ddtok_tm)
in (match (uu____11777) with
| (tok_typing, decls3) -> begin
(

let uu____11784 = (encode_binders (Some (fuel_tm)) formals env)
in (match (uu____11784) with
| (vars', guards', env'', decls_formals, uu____11799) -> begin
(

let uu____11806 = (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars')
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (encode_term_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (uu____11806) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_SMTEncoding_Util.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| uu____11825 -> begin
(let _0_932 = (let _0_931 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ddtok), (FStar_SMTEncoding_Term.Term_sort)) _0_931))
in (_0_932)::[])
end)
in (

let encode_elim = (fun uu____11835 -> (

let uu____11836 = (FStar_Syntax_Util.head_and_args t_res)
in (match (uu____11836) with
| (head, args) -> begin
(

let uu____11865 = (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n
in (match (uu____11865) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let uu____11881 = (encode_args args env')
in (match (uu____11881) with
| (encoded_args, arg_decls) -> begin
(

let uu____11892 = (FStar_List.fold_left (fun uu____11903 arg -> (match (uu____11903) with
| (env, arg_vars, eqns) -> begin
(

let uu____11922 = (let _0_933 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in (gen_term_var env _0_933))
in (match (uu____11922) with
| (uu____11931, xv, env) -> begin
(let _0_935 = (let _0_934 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (_0_934)::eqns)
in ((env), ((xv)::arg_vars), (_0_935)))
end))
end)) ((env'), ([]), ([])) encoded_args)
in (match (uu____11892) with
| (uu____11941, arg_vars, eqns) -> begin
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

let typing_inversion = FStar_SMTEncoding_Term.Assume ((let _0_939 = (FStar_SMTEncoding_Util.mkForall (let _0_938 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (let _0_937 = (FStar_SMTEncoding_Util.mkImp (let _0_936 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append eqns guards))
in ((ty_pred), (_0_936))))
in ((((ty_pred)::[])::[]), (_0_938), (_0_937)))))
in ((_0_939), (Some ("data constructor typing elim")), (Some ((Prims.strcat "data_elim_" ddconstrsym))))))
in (

let subterm_ordering = (match ((FStar_Ident.lid_equals d FStar_Syntax_Const.lextop_lid)) with
| true -> begin
(

let x = (let _0_940 = (varops.fresh "x")
in ((_0_940), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in FStar_SMTEncoding_Term.Assume ((let _0_948 = (FStar_SMTEncoding_Util.mkForall (let _0_946 = (let _0_942 = (let _0_941 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp)
in (_0_941)::[])
in (_0_942)::[])
in (let _0_945 = (FStar_SMTEncoding_Util.mkImp (let _0_944 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (let _0_943 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp)
in ((_0_944), (_0_943)))))
in ((_0_946), ((x)::[]), (_0_945)))))
in (let _0_947 = Some ((varops.mk_unique "lextop"))
in ((_0_948), (Some ("lextop is top")), (_0_947)))))))
end
| uu____11991 -> begin
(

let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
[]
end
| FStar_SMTEncoding_Term.Term_sort -> begin
(let _0_950 = (let _0_949 = (FStar_SMTEncoding_Util.mkFreeV v)
in (FStar_SMTEncoding_Util.mk_Precedes _0_949 dapp))
in (_0_950)::[])
end
| uu____12002 -> begin
(failwith "unexpected sort")
end))))
in FStar_SMTEncoding_Term.Assume ((let _0_954 = (FStar_SMTEncoding_Util.mkForall (let _0_953 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (let _0_952 = (FStar_SMTEncoding_Util.mkImp (let _0_951 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (_0_951))))
in ((((ty_pred)::[])::[]), (_0_953), (_0_952)))))
in ((_0_954), (Some ("subterm ordering")), (Some ((Prims.strcat "subterm_ordering_" ddconstrsym)))))))
end)
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end))
end)))
end
| uu____12016 -> begin
((let _0_957 = (let _0_956 = (FStar_Syntax_Print.lid_to_string d)
in (let _0_955 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _0_956 _0_955)))
in (FStar_Errors.warn drange _0_957));
(([]), ([]));
)
end))
end)))
in (

let uu____12020 = (encode_elim ())
in (match (uu____12020) with
| (decls2, elim) -> begin
(

let g = (let _0_978 = (let _0_977 = (let _0_976 = (let _0_975 = (let _0_960 = FStar_SMTEncoding_Term.DeclFun ((let _0_959 = Some ((let _0_958 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" _0_958)))
in ((ddtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (_0_959))))
in (_0_960)::[])
in (let _0_974 = (let _0_973 = (let _0_972 = (let _0_971 = (let _0_970 = (let _0_969 = (let _0_968 = FStar_SMTEncoding_Term.Assume ((let _0_962 = (FStar_SMTEncoding_Util.mkForall (let _0_961 = (FStar_SMTEncoding_Util.mkEq ((app), (dapp)))
in ((((app)::[])::[]), (vars), (_0_961))))
in ((_0_962), (Some ("equality for proxy")), (Some ((Prims.strcat "equality_tok_" ddtok))))))
in (let _0_967 = (let _0_966 = FStar_SMTEncoding_Term.Assume ((let _0_965 = (FStar_SMTEncoding_Util.mkForall (let _0_964 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) vars')
in (let _0_963 = (FStar_SMTEncoding_Util.mkImp ((guard'), (ty_pred')))
in ((((ty_pred')::[])::[]), (_0_964), (_0_963)))))
in ((_0_965), (Some ("data constructor typing intro")), (Some ((Prims.strcat "data_typing_intro_" ddtok))))))
in (_0_966)::[])
in (_0_968)::_0_967))
in (FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("typing for data constructor proxy")), (Some ((Prims.strcat "typing_tok_" ddtok))))))::_0_969)
in (FStar_List.append _0_970 elim))
in (FStar_List.append decls_pred _0_971))
in (FStar_List.append decls_formals _0_972))
in (FStar_List.append proxy_fresh _0_973))
in (FStar_List.append _0_975 _0_974)))
in (FStar_List.append decls3 _0_976))
in (FStar_List.append decls2 _0_977))
in (FStar_List.append binder_decls _0_978))
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
and encode_signature : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun uu____12065 se -> (match (uu____12065) with
| (g, env) -> begin
(

let uu____12077 = (encode_sigelt env se)
in (match (uu____12077) with
| (g', env) -> begin
(((FStar_List.append g g')), (env))
end))
end)) (([]), (env)))))


let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env bindings -> (

let encode_binding = (fun b uu____12113 -> (match (uu____12113) with
| (i, decls, env) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (uu____12131) -> begin
(((i + (Prims.parse_int "1"))), ([]), (env))
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in ((

let uu____12136 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____12136) with
| true -> begin
(let _0_981 = (FStar_Syntax_Print.bv_to_string x)
in (let _0_980 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _0_979 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" _0_981 _0_980 _0_979))))
end
| uu____12137 -> begin
()
end));
(

let uu____12138 = (encode_term t1 env)
in (match (uu____12138) with
| (t, decls') -> begin
(

let t_hash = (FStar_SMTEncoding_Term.hash_of_term t)
in (

let uu____12148 = (let _0_986 = (let _0_985 = (let _0_984 = (FStar_Util.digest_of_string t_hash)
in (let _0_983 = (let _0_982 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _0_982))
in (Prims.strcat _0_984 _0_983)))
in (Prims.strcat "x_" _0_985))
in (new_term_constant_from_string env x _0_986))
in (match (uu____12148) with
| (xxsym, xx, env') -> begin
(

let t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel None xx t)
in (

let caption = (

let uu____12162 = (FStar_Options.log_queries ())
in (match (uu____12162) with
| true -> begin
Some ((let _0_989 = (FStar_Syntax_Print.bv_to_string x)
in (let _0_988 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _0_987 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _0_989 _0_988 _0_987)))))
end
| uu____12164 -> begin
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
| FStar_TypeChecker_Env.Binding_lid (x, (uu____12176, t)) -> begin
(

let t_norm = (whnf env t)
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____12185 = (encode_free_var env fv t t_norm [])
in (match (uu____12185) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))))
end
| (FStar_TypeChecker_Env.Binding_sig_inst (_, se, _)) | (FStar_TypeChecker_Env.Binding_sig (_, se)) -> begin
(

let uu____12204 = (encode_sigelt env se)
in (match (uu____12204) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))
end)
end))
in (

let uu____12214 = (FStar_List.fold_right encode_binding bindings (((Prims.parse_int "0")), ([]), (env)))
in (match (uu____12214) with
| (uu____12226, decls, env) -> begin
((decls), (env))
end))))


let encode_labels = (fun labs -> (

let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun uu____12271 -> (match (uu____12271) with
| (l, uu____12278, uu____12279) -> begin
FStar_SMTEncoding_Term.DeclFun ((((Prims.fst l)), ([]), (FStar_SMTEncoding_Term.Bool_sort), (None)))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun uu____12300 -> (match (uu____12300) with
| (l, uu____12308, uu____12309) -> begin
(let _0_993 = (FStar_All.pipe_left (fun _0_990 -> FStar_SMTEncoding_Term.Echo (_0_990)) (Prims.fst l))
in (let _0_992 = (let _0_991 = FStar_SMTEncoding_Term.Eval ((FStar_SMTEncoding_Util.mkFreeV l))
in (_0_991)::[])
in (_0_993)::_0_992))
end))))
in ((prefix), (suffix)))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (let _0_996 = (let _0_995 = (let _0_994 = (FStar_Util.smap_create (Prims.parse_int "100"))
in {bindings = []; depth = (Prims.parse_int "0"); tcenv = tcenv; warn = true; cache = _0_994; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_0_995)::[])
in (FStar_ST.write last_env _0_996)))


let get_env : FStar_TypeChecker_Env.env  ->  env_t = (fun tcenv -> (

let uu____12335 = (FStar_ST.read last_env)
in (match (uu____12335) with
| [] -> begin
(failwith "No env; call init first!")
end
| (e)::uu____12341 -> begin
(

let uu___156_12343 = e
in {bindings = uu___156_12343.bindings; depth = uu___156_12343.depth; tcenv = tcenv; warn = uu___156_12343.warn; cache = uu___156_12343.cache; nolabels = uu___156_12343.nolabels; use_zfuel_name = uu___156_12343.use_zfuel_name; encode_non_total_function_typ = uu___156_12343.encode_non_total_function_typ})
end)))


let set_env : env_t  ->  Prims.unit = (fun env -> (

let uu____12347 = (FStar_ST.read last_env)
in (match (uu____12347) with
| [] -> begin
(failwith "Empty env stack")
end
| (uu____12352)::tl -> begin
(FStar_ST.write last_env ((env)::tl))
end)))


let push_env : Prims.unit  ->  Prims.unit = (fun uu____12360 -> (

let uu____12361 = (FStar_ST.read last_env)
in (match (uu____12361) with
| [] -> begin
(failwith "Empty env stack")
end
| (hd)::tl -> begin
(

let refs = (FStar_Util.smap_copy hd.cache)
in (

let top = (

let uu___157_12382 = hd
in {bindings = uu___157_12382.bindings; depth = uu___157_12382.depth; tcenv = uu___157_12382.tcenv; warn = uu___157_12382.warn; cache = refs; nolabels = uu___157_12382.nolabels; use_zfuel_name = uu___157_12382.use_zfuel_name; encode_non_total_function_typ = uu___157_12382.encode_non_total_function_typ})
in (FStar_ST.write last_env ((top)::(hd)::tl))))
end)))


let pop_env : Prims.unit  ->  Prims.unit = (fun uu____12388 -> (

let uu____12389 = (FStar_ST.read last_env)
in (match (uu____12389) with
| [] -> begin
(failwith "Popping an empty stack")
end
| (uu____12394)::tl -> begin
(FStar_ST.write last_env tl)
end)))


let mark_env : Prims.unit  ->  Prims.unit = (fun uu____12402 -> (push_env ()))


let reset_mark_env : Prims.unit  ->  Prims.unit = (fun uu____12405 -> (pop_env ()))


let commit_mark_env : Prims.unit  ->  Prims.unit = (fun uu____12408 -> (

let uu____12409 = (FStar_ST.read last_env)
in (match (uu____12409) with
| (hd)::(uu____12415)::tl -> begin
(FStar_ST.write last_env ((hd)::tl))
end
| uu____12421 -> begin
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

let uu____12466 = (FStar_Options.log_queries ())
in (match (uu____12466) with
| true -> begin
(let _0_999 = FStar_SMTEncoding_Term.Caption ((let _0_998 = (let _0_997 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.map FStar_Syntax_Print.lid_to_string))
in (FStar_All.pipe_right _0_997 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " _0_998)))
in (_0_999)::decls)
end
| uu____12471 -> begin
decls
end)))
in (

let env = (get_env tcenv)
in (

let uu____12473 = (encode_sigelt env se)
in (match (uu____12473) with
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
| uu____12486 -> begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in ((

let uu____12488 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____12488) with
| true -> begin
(let _0_1000 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name _0_1000))
end
| uu____12491 -> begin
()
end));
(

let env = (get_env tcenv)
in (

let uu____12493 = (encode_signature (

let uu___158_12497 = env
in {bindings = uu___158_12497.bindings; depth = uu___158_12497.depth; tcenv = uu___158_12497.tcenv; warn = false; cache = uu___158_12497.cache; nolabels = uu___158_12497.nolabels; use_zfuel_name = uu___158_12497.use_zfuel_name; encode_non_total_function_typ = uu___158_12497.encode_non_total_function_typ}) modul.FStar_Syntax_Syntax.exports)
in (match (uu____12493) with
| (decls, env) -> begin
(

let caption = (fun decls -> (

let uu____12509 = (FStar_Options.log_queries ())
in (match (uu____12509) with
| true -> begin
(

let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::decls) ((FStar_SMTEncoding_Term.Caption ((Prims.strcat "End " msg)))::[])))
end
| uu____12512 -> begin
decls
end)))
in ((set_env (

let uu___159_12514 = env
in {bindings = uu___159_12514.bindings; depth = uu___159_12514.depth; tcenv = uu___159_12514.tcenv; warn = true; cache = uu___159_12514.cache; nolabels = uu___159_12514.nolabels; use_zfuel_name = uu___159_12514.use_zfuel_name; encode_non_total_function_typ = uu___159_12514.encode_non_total_function_typ}));
(

let uu____12516 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____12516) with
| true -> begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end
| uu____12517 -> begin
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

let uu____12558 = (

let rec aux = (fun bindings -> (match (bindings) with
| (FStar_TypeChecker_Env.Binding_var (x))::rest -> begin
(

let uu____12579 = (aux rest)
in (match (uu____12579) with
| (out, rest) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (let _0_1002 = (let _0_1001 = (FStar_Syntax_Syntax.mk_binder (

let uu___160_12597 = x
in {FStar_Syntax_Syntax.ppname = uu___160_12597.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___160_12597.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_0_1001)::out)
in ((_0_1002), (rest))))
end))
end
| uu____12598 -> begin
(([]), (bindings))
end))
in (

let uu____12602 = (aux bindings)
in (match (uu____12602) with
| (closing, bindings) -> begin
(let _0_1003 = (FStar_Syntax_Util.close_forall (FStar_List.rev closing) q)
in ((_0_1003), (bindings)))
end)))
in (match (uu____12558) with
| (q, bindings) -> begin
(

let uu____12628 = (let _0_1004 = (FStar_List.filter (fun uu___132_12631 -> (match (uu___132_12631) with
| FStar_TypeChecker_Env.Binding_sig (uu____12632) -> begin
false
end
| uu____12636 -> begin
true
end)) bindings)
in (encode_env_bindings env _0_1004))
in (match (uu____12628) with
| (env_decls, env) -> begin
((

let uu____12647 = (((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTQuery"))))
in (match (uu____12647) with
| true -> begin
(let _0_1005 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" _0_1005))
end
| uu____12648 -> begin
()
end));
(

let uu____12649 = (encode_formula q env)
in (match (uu____12649) with
| (phi, qdecls) -> begin
(

let uu____12661 = (let _0_1006 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg _0_1006 phi))
in (match (uu____12661) with
| (labels, phi) -> begin
(

let uu____12673 = (encode_labels labels)
in (match (uu____12673) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append env_decls (FStar_List.append label_prefix qdecls))
in (

let qry = FStar_SMTEncoding_Term.Assume ((let _0_1008 = (FStar_SMTEncoding_Util.mkNot phi)
in (let _0_1007 = Some ((varops.mk_unique "@query"))
in ((_0_1008), (Some ("query")), (_0_1007)))))
in (

let suffix = (let _0_1010 = (let _0_1009 = (

let uu____12698 = (FStar_Options.print_z3_statistics ())
in (match (uu____12698) with
| true -> begin
(FStar_SMTEncoding_Term.PrintStats)::[]
end
| uu____12700 -> begin
[]
end))
in (FStar_List.append _0_1009 ((FStar_SMTEncoding_Term.Echo ("Done!"))::[])))
in (FStar_List.append label_suffix _0_1010))
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

let uu____12711 = (encode_formula q env)
in (match (uu____12711) with
| (f, uu____12715) -> begin
((FStar_SMTEncoding_Z3.pop "query");
(match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____12717) -> begin
true
end
| uu____12720 -> begin
false
end);
)
end));
)))




