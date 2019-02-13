
open Prims
open FStar_Pervasives
exception Inner_let_rec


let uu___is_Inner_let_rec : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Inner_let_rec -> begin
true
end
| uu____9 -> begin
false
end))


let add_fuel : 'Auu____18 . 'Auu____18  ->  'Auu____18 Prims.list  ->  'Auu____18 Prims.list = (fun x tl1 -> (

let uu____35 = (FStar_Options.unthrottle_inductives ())
in (match (uu____35) with
| true -> begin
tl1
end
| uu____40 -> begin
(x)::tl1
end)))


let withenv : 'Auu____53 'Auu____54 'Auu____55 . 'Auu____53  ->  ('Auu____54 * 'Auu____55)  ->  ('Auu____54 * 'Auu____55 * 'Auu____53) = (fun c uu____75 -> (match (uu____75) with
| (a, b) -> begin
((a), (b), (c))
end))


let vargs : 'Auu____91 'Auu____92 'Auu____93 . (('Auu____91, 'Auu____92) FStar_Util.either * 'Auu____93) Prims.list  ->  (('Auu____91, 'Auu____92) FStar_Util.either * 'Auu____93) Prims.list = (fun args -> (FStar_List.filter (fun uu___269_140 -> (match (uu___269_140) with
| (FStar_Util.Inl (uu____150), uu____151) -> begin
false
end
| uu____157 -> begin
true
end)) args))


let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s 39 (*'*) 95 (*_*)))


let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun lid a -> (

let uu____190 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str a.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (FStar_All.pipe_left escape uu____190)))


let primitive_projector_by_pos : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (

let fail1 = (fun uu____220 -> (

let uu____221 = (FStar_Util.format2 "Projector %s on data constructor %s not found" (Prims.string_of_int i) lid.FStar_Ident.str)
in (failwith uu____221)))
in (

let uu____225 = (FStar_TypeChecker_Env.lookup_datacon env lid)
in (match (uu____225) with
| (uu____231, t) -> begin
(

let uu____233 = (

let uu____234 = (FStar_Syntax_Subst.compress t)
in uu____234.FStar_Syntax_Syntax.n)
in (match (uu____233) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____260 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____260) with
| (binders, uu____267) -> begin
(match (((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders)))) with
| true -> begin
(fail1 ())
end
| uu____277 -> begin
(

let b = (FStar_List.nth binders i)
in (mk_term_projector_name lid (FStar_Pervasives_Native.fst b)))
end)
end))
end
| uu____294 -> begin
(fail1 ())
end))
end))))


let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (

let uu____309 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str (Prims.string_of_int i))
in (FStar_All.pipe_left escape uu____309)))


let mk_term_projector : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun lid a -> (

let uu____325 = (

let uu____326 = (

let uu____332 = (mk_term_projector_name lid a)
in ((uu____332), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Term.mk_fv uu____326))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____325)))


let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_SMTEncoding_Term.term = (fun lid i -> (

let uu____348 = (

let uu____349 = (

let uu____355 = (mk_term_projector_name_by_pos lid i)
in ((uu____355), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Term.mk_fv uu____349))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____348)))


let mk_data_tester : 'Auu____367 . 'Auu____367  ->  FStar_Ident.lident  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (fun env l x -> (FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x))

type varops_t =
{push : unit  ->  unit; pop : unit  ->  unit; snapshot : unit  ->  (Prims.int * unit); rollback : Prims.int FStar_Pervasives_Native.option  ->  unit; new_var : FStar_Ident.ident  ->  Prims.int  ->  Prims.string; new_fvar : FStar_Ident.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_SMTEncoding_Term.term; next_id : unit  ->  Prims.int; mk_unique : Prims.string  ->  Prims.string}


let __proj__Mkvarops_t__item__push : varops_t  ->  unit  ->  unit = (fun projectee -> (match (projectee) with
| {push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; string_const = string_const; next_id = next_id1; mk_unique = mk_unique} -> begin
push1
end))


let __proj__Mkvarops_t__item__pop : varops_t  ->  unit  ->  unit = (fun projectee -> (match (projectee) with
| {push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; string_const = string_const; next_id = next_id1; mk_unique = mk_unique} -> begin
pop1
end))


let __proj__Mkvarops_t__item__snapshot : varops_t  ->  unit  ->  (Prims.int * unit) = (fun projectee -> (match (projectee) with
| {push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; string_const = string_const; next_id = next_id1; mk_unique = mk_unique} -> begin
snapshot1
end))


let __proj__Mkvarops_t__item__rollback : varops_t  ->  Prims.int FStar_Pervasives_Native.option  ->  unit = (fun projectee -> (match (projectee) with
| {push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; string_const = string_const; next_id = next_id1; mk_unique = mk_unique} -> begin
rollback1
end))


let __proj__Mkvarops_t__item__new_var : varops_t  ->  FStar_Ident.ident  ->  Prims.int  ->  Prims.string = (fun projectee -> (match (projectee) with
| {push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; string_const = string_const; next_id = next_id1; mk_unique = mk_unique} -> begin
new_var
end))


let __proj__Mkvarops_t__item__new_fvar : varops_t  ->  FStar_Ident.lident  ->  Prims.string = (fun projectee -> (match (projectee) with
| {push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; string_const = string_const; next_id = next_id1; mk_unique = mk_unique} -> begin
new_fvar
end))


let __proj__Mkvarops_t__item__fresh : varops_t  ->  Prims.string  ->  Prims.string = (fun projectee -> (match (projectee) with
| {push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; string_const = string_const; next_id = next_id1; mk_unique = mk_unique} -> begin
fresh1
end))


let __proj__Mkvarops_t__item__string_const : varops_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term = (fun projectee -> (match (projectee) with
| {push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; string_const = string_const; next_id = next_id1; mk_unique = mk_unique} -> begin
string_const
end))


let __proj__Mkvarops_t__item__next_id : varops_t  ->  unit  ->  Prims.int = (fun projectee -> (match (projectee) with
| {push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; string_const = string_const; next_id = next_id1; mk_unique = mk_unique} -> begin
next_id1
end))


let __proj__Mkvarops_t__item__mk_unique : varops_t  ->  Prims.string  ->  Prims.string = (fun projectee -> (match (projectee) with
| {push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; string_const = string_const; next_id = next_id1; mk_unique = mk_unique} -> begin
mk_unique
end))


let varops : varops_t = (

let initial_ctr = (Prims.parse_int "100")
in (

let ctr = (FStar_Util.mk_ref initial_ctr)
in (

let new_scope = (fun uu____1299 -> (

let uu____1300 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (

let uu____1306 = (FStar_Util.smap_create (Prims.parse_int "100"))
in ((uu____1300), (uu____1306)))))
in (

let scopes = (

let uu____1329 = (

let uu____1341 = (new_scope ())
in (uu____1341)::[])
in (FStar_Util.mk_ref uu____1329))
in (

let mk_unique = (fun y -> (

let y1 = (escape y)
in (

let y2 = (

let uu____1393 = (

let uu____1397 = (FStar_ST.op_Bang scopes)
in (FStar_Util.find_map uu____1397 (fun uu____1485 -> (match (uu____1485) with
| (names1, uu____1499) -> begin
(FStar_Util.smap_try_find names1 y1)
end))))
in (match (uu____1393) with
| FStar_Pervasives_Native.None -> begin
y1
end
| FStar_Pervasives_Native.Some (uu____1513) -> begin
((FStar_Util.incr ctr);
(

let uu____1550 = (

let uu____1552 = (

let uu____1554 = (FStar_ST.op_Bang ctr)
in (Prims.string_of_int uu____1554))
in (Prims.strcat "__" uu____1552))
in (Prims.strcat y1 uu____1550));
)
end))
in (

let top_scope = (

let uu____1604 = (

let uu____1614 = (FStar_ST.op_Bang scopes)
in (FStar_List.hd uu____1614))
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1604))
in ((FStar_Util.smap_add top_scope y2 true);
y2;
)))))
in (

let new_var = (fun pp rn -> (FStar_All.pipe_left mk_unique (Prims.strcat pp.FStar_Ident.idText (Prims.strcat "__" (Prims.string_of_int rn)))))
in (

let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (

let next_id1 = (fun uu____1748 -> ((FStar_Util.incr ctr);
(FStar_ST.op_Bang ctr);
))
in (

let fresh1 = (fun pfx -> (

let uu____1835 = (

let uu____1837 = (next_id1 ())
in (FStar_All.pipe_left Prims.string_of_int uu____1837))
in (FStar_Util.format2 "%s_%s" pfx uu____1835)))
in (

let string_const = (fun s -> (

let uu____1850 = (

let uu____1853 = (FStar_ST.op_Bang scopes)
in (FStar_Util.find_map uu____1853 (fun uu____1940 -> (match (uu____1940) with
| (uu____1952, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))
in (match (uu____1850) with
| FStar_Pervasives_Native.Some (f) -> begin
f
end
| FStar_Pervasives_Native.None -> begin
(

let id1 = (next_id1 ())
in (

let f = (

let uu____1968 = (FStar_SMTEncoding_Util.mk_String_const id1)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1968))
in (

let top_scope = (

let uu____1972 = (

let uu____1982 = (FStar_ST.op_Bang scopes)
in (FStar_List.hd uu____1982))
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1972))
in ((FStar_Util.smap_add top_scope s f);
f;
))))
end)))
in (

let push1 = (fun uu____2088 -> (

let uu____2089 = (

let uu____2101 = (new_scope ())
in (

let uu____2111 = (FStar_ST.op_Bang scopes)
in (uu____2101)::uu____2111))
in (FStar_ST.op_Colon_Equals scopes uu____2089)))
in (

let pop1 = (fun uu____2263 -> (

let uu____2264 = (

let uu____2276 = (FStar_ST.op_Bang scopes)
in (FStar_List.tl uu____2276))
in (FStar_ST.op_Colon_Equals scopes uu____2264)))
in (

let snapshot1 = (fun uu____2433 -> (FStar_Common.snapshot push1 scopes ()))
in (

let rollback1 = (fun depth -> (FStar_Common.rollback pop1 scopes depth))
in {push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; string_const = string_const; next_id = next_id1; mk_unique = mk_unique}))))))))))))))

type fvar_binding =
{fvar_lid : FStar_Ident.lident; smt_arity : Prims.int; smt_id : Prims.string; smt_token : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option; smt_fuel_partial_app : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option; fvb_thunked : Prims.bool}


let __proj__Mkfvar_binding__item__fvar_lid : fvar_binding  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {fvar_lid = fvar_lid; smt_arity = smt_arity; smt_id = smt_id; smt_token = smt_token; smt_fuel_partial_app = smt_fuel_partial_app; fvb_thunked = fvb_thunked} -> begin
fvar_lid
end))


let __proj__Mkfvar_binding__item__smt_arity : fvar_binding  ->  Prims.int = (fun projectee -> (match (projectee) with
| {fvar_lid = fvar_lid; smt_arity = smt_arity; smt_id = smt_id; smt_token = smt_token; smt_fuel_partial_app = smt_fuel_partial_app; fvb_thunked = fvb_thunked} -> begin
smt_arity
end))


let __proj__Mkfvar_binding__item__smt_id : fvar_binding  ->  Prims.string = (fun projectee -> (match (projectee) with
| {fvar_lid = fvar_lid; smt_arity = smt_arity; smt_id = smt_id; smt_token = smt_token; smt_fuel_partial_app = smt_fuel_partial_app; fvb_thunked = fvb_thunked} -> begin
smt_id
end))


let __proj__Mkfvar_binding__item__smt_token : fvar_binding  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {fvar_lid = fvar_lid; smt_arity = smt_arity; smt_id = smt_id; smt_token = smt_token; smt_fuel_partial_app = smt_fuel_partial_app; fvb_thunked = fvb_thunked} -> begin
smt_token
end))


let __proj__Mkfvar_binding__item__smt_fuel_partial_app : fvar_binding  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {fvar_lid = fvar_lid; smt_arity = smt_arity; smt_id = smt_id; smt_token = smt_token; smt_fuel_partial_app = smt_fuel_partial_app; fvb_thunked = fvb_thunked} -> begin
smt_fuel_partial_app
end))


let __proj__Mkfvar_binding__item__fvb_thunked : fvar_binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {fvar_lid = fvar_lid; smt_arity = smt_arity; smt_id = smt_id; smt_token = smt_token; smt_fuel_partial_app = smt_fuel_partial_app; fvb_thunked = fvb_thunked} -> begin
fvb_thunked
end))


let check_valid_fvb : fvar_binding  ->  unit = (fun fvb -> (match ((((FStar_Option.isSome fvb.smt_token) || (FStar_Option.isSome fvb.smt_fuel_partial_app)) && fvb.fvb_thunked)) with
| true -> begin
(

let uu____2680 = (

let uu____2682 = (FStar_Ident.string_of_lid fvb.fvar_lid)
in (FStar_Util.format1 "Unexpected thunked SMT symbol: %s" uu____2682))
in (failwith uu____2680))
end
| uu____2685 -> begin
(match ((fvb.fvb_thunked && (Prims.op_disEquality fvb.smt_arity (Prims.parse_int "0")))) with
| true -> begin
(

let uu____2690 = (

let uu____2692 = (FStar_Ident.string_of_lid fvb.fvar_lid)
in (FStar_Util.format1 "Unexpected arity of thunked SMT symbol: %s" uu____2692))
in (failwith uu____2690))
end
| uu____2695 -> begin
()
end)
end))


let binder_of_eithervar : 'Auu____2704 'Auu____2705 . 'Auu____2704  ->  ('Auu____2704 * 'Auu____2705 FStar_Pervasives_Native.option) = (fun v1 -> ((v1), (FStar_Pervasives_Native.None)))

type cache_entry =
{cache_symbol_name : Prims.string; cache_symbol_arg_sorts : FStar_SMTEncoding_Term.sort Prims.list; cache_symbol_decls : FStar_SMTEncoding_Term.decl Prims.list; cache_symbol_assumption_names : Prims.string Prims.list}


let __proj__Mkcache_entry__item__cache_symbol_name : cache_entry  ->  Prims.string = (fun projectee -> (match (projectee) with
| {cache_symbol_name = cache_symbol_name; cache_symbol_arg_sorts = cache_symbol_arg_sorts; cache_symbol_decls = cache_symbol_decls; cache_symbol_assumption_names = cache_symbol_assumption_names} -> begin
cache_symbol_name
end))


let __proj__Mkcache_entry__item__cache_symbol_arg_sorts : cache_entry  ->  FStar_SMTEncoding_Term.sort Prims.list = (fun projectee -> (match (projectee) with
| {cache_symbol_name = cache_symbol_name; cache_symbol_arg_sorts = cache_symbol_arg_sorts; cache_symbol_decls = cache_symbol_decls; cache_symbol_assumption_names = cache_symbol_assumption_names} -> begin
cache_symbol_arg_sorts
end))


let __proj__Mkcache_entry__item__cache_symbol_decls : cache_entry  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun projectee -> (match (projectee) with
| {cache_symbol_name = cache_symbol_name; cache_symbol_arg_sorts = cache_symbol_arg_sorts; cache_symbol_decls = cache_symbol_decls; cache_symbol_assumption_names = cache_symbol_assumption_names} -> begin
cache_symbol_decls
end))


let __proj__Mkcache_entry__item__cache_symbol_assumption_names : cache_entry  ->  Prims.string Prims.list = (fun projectee -> (match (projectee) with
| {cache_symbol_name = cache_symbol_name; cache_symbol_arg_sorts = cache_symbol_arg_sorts; cache_symbol_decls = cache_symbol_decls; cache_symbol_assumption_names = cache_symbol_assumption_names} -> begin
cache_symbol_assumption_names
end))

type env_t =
{bvar_bindings : (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) FStar_Util.pimap FStar_Util.psmap; fvar_bindings : fvar_binding FStar_Util.psmap; depth : Prims.int; tcenv : FStar_TypeChecker_Env.env; warn : Prims.bool; cache : cache_entry FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool; current_module_name : Prims.string; encoding_quantifier : Prims.bool}


let __proj__Mkenv_t__item__bvar_bindings : env_t  ->  (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) FStar_Util.pimap FStar_Util.psmap = (fun projectee -> (match (projectee) with
| {bvar_bindings = bvar_bindings; fvar_bindings = fvar_bindings; depth = depth; tcenv = tcenv; warn = warn; cache = cache; nolabels = nolabels; use_zfuel_name = use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = current_module_name; encoding_quantifier = encoding_quantifier} -> begin
bvar_bindings
end))


let __proj__Mkenv_t__item__fvar_bindings : env_t  ->  fvar_binding FStar_Util.psmap = (fun projectee -> (match (projectee) with
| {bvar_bindings = bvar_bindings; fvar_bindings = fvar_bindings; depth = depth; tcenv = tcenv; warn = warn; cache = cache; nolabels = nolabels; use_zfuel_name = use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = current_module_name; encoding_quantifier = encoding_quantifier} -> begin
fvar_bindings
end))


let __proj__Mkenv_t__item__depth : env_t  ->  Prims.int = (fun projectee -> (match (projectee) with
| {bvar_bindings = bvar_bindings; fvar_bindings = fvar_bindings; depth = depth; tcenv = tcenv; warn = warn; cache = cache; nolabels = nolabels; use_zfuel_name = use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = current_module_name; encoding_quantifier = encoding_quantifier} -> begin
depth
end))


let __proj__Mkenv_t__item__tcenv : env_t  ->  FStar_TypeChecker_Env.env = (fun projectee -> (match (projectee) with
| {bvar_bindings = bvar_bindings; fvar_bindings = fvar_bindings; depth = depth; tcenv = tcenv; warn = warn; cache = cache; nolabels = nolabels; use_zfuel_name = use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = current_module_name; encoding_quantifier = encoding_quantifier} -> begin
tcenv
end))


let __proj__Mkenv_t__item__warn : env_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {bvar_bindings = bvar_bindings; fvar_bindings = fvar_bindings; depth = depth; tcenv = tcenv; warn = warn; cache = cache; nolabels = nolabels; use_zfuel_name = use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = current_module_name; encoding_quantifier = encoding_quantifier} -> begin
warn
end))


let __proj__Mkenv_t__item__cache : env_t  ->  cache_entry FStar_Util.smap = (fun projectee -> (match (projectee) with
| {bvar_bindings = bvar_bindings; fvar_bindings = fvar_bindings; depth = depth; tcenv = tcenv; warn = warn; cache = cache; nolabels = nolabels; use_zfuel_name = use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = current_module_name; encoding_quantifier = encoding_quantifier} -> begin
cache
end))


let __proj__Mkenv_t__item__nolabels : env_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {bvar_bindings = bvar_bindings; fvar_bindings = fvar_bindings; depth = depth; tcenv = tcenv; warn = warn; cache = cache; nolabels = nolabels; use_zfuel_name = use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = current_module_name; encoding_quantifier = encoding_quantifier} -> begin
nolabels
end))


let __proj__Mkenv_t__item__use_zfuel_name : env_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {bvar_bindings = bvar_bindings; fvar_bindings = fvar_bindings; depth = depth; tcenv = tcenv; warn = warn; cache = cache; nolabels = nolabels; use_zfuel_name = use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = current_module_name; encoding_quantifier = encoding_quantifier} -> begin
use_zfuel_name
end))


let __proj__Mkenv_t__item__encode_non_total_function_typ : env_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {bvar_bindings = bvar_bindings; fvar_bindings = fvar_bindings; depth = depth; tcenv = tcenv; warn = warn; cache = cache; nolabels = nolabels; use_zfuel_name = use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = current_module_name; encoding_quantifier = encoding_quantifier} -> begin
encode_non_total_function_typ
end))


let __proj__Mkenv_t__item__current_module_name : env_t  ->  Prims.string = (fun projectee -> (match (projectee) with
| {bvar_bindings = bvar_bindings; fvar_bindings = fvar_bindings; depth = depth; tcenv = tcenv; warn = warn; cache = cache; nolabels = nolabels; use_zfuel_name = use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = current_module_name; encoding_quantifier = encoding_quantifier} -> begin
current_module_name
end))


let __proj__Mkenv_t__item__encoding_quantifier : env_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {bvar_bindings = bvar_bindings; fvar_bindings = fvar_bindings; depth = depth; tcenv = tcenv; warn = warn; cache = cache; nolabels = nolabels; use_zfuel_name = use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = current_module_name; encoding_quantifier = encoding_quantifier} -> begin
encoding_quantifier
end))


let mk_cache_entry : 'Auu____3354 . 'Auu____3354  ->  Prims.string  ->  FStar_SMTEncoding_Term.sort Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  cache_entry = (fun env tsym cvar_sorts t_decls1 -> (

let names1 = (FStar_All.pipe_right t_decls1 (FStar_List.collect (fun uu___270_3397 -> (match (uu___270_3397) with
| FStar_SMTEncoding_Term.Assume (a) -> begin
(a.FStar_SMTEncoding_Term.assumption_name)::[]
end
| uu____3404 -> begin
[]
end))))
in {cache_symbol_name = tsym; cache_symbol_arg_sorts = cvar_sorts; cache_symbol_decls = t_decls1; cache_symbol_assumption_names = names1}))


let use_cache_entry : cache_entry  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun ce -> (FStar_SMTEncoding_Term.RetainAssumptions (ce.cache_symbol_assumption_names))::[])


let print_env : env_t  ->  Prims.string = (fun e -> (

let bvars = (FStar_Util.psmap_fold e.bvar_bindings (fun _k pi acc -> (FStar_Util.pimap_fold pi (fun _i uu____3464 acc1 -> (match (uu____3464) with
| (x, _term) -> begin
(

let uu____3479 = (FStar_Syntax_Print.bv_to_string x)
in (uu____3479)::acc1)
end)) acc)) [])
in (

let allvars = (FStar_Util.psmap_fold e.fvar_bindings (fun _k fvb acc -> (fvb.fvar_lid)::acc) [])
in (

let last_fvar = (match ((FStar_List.rev allvars)) with
| [] -> begin
""
end
| (l)::uu____3502 -> begin
(

let uu____3505 = (FStar_Syntax_Print.lid_to_string l)
in (Prims.strcat "...," uu____3505))
end)
in (FStar_String.concat ", " ((last_fvar)::bvars))))))


let lookup_bvar_binding : env_t  ->  FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.option = (fun env bv -> (

let uu____3527 = (FStar_Util.psmap_try_find env.bvar_bindings bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (match (uu____3527) with
| FStar_Pervasives_Native.Some (bvs) -> begin
(FStar_Util.pimap_try_find bvs bv.FStar_Syntax_Syntax.index)
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)))


let lookup_fvar_binding : env_t  ->  FStar_Ident.lident  ->  fvar_binding FStar_Pervasives_Native.option = (fun env lid -> (FStar_Util.psmap_try_find env.fvar_bindings lid.FStar_Ident.str))


let add_bvar_binding : 'Auu____3595 . (FStar_Syntax_Syntax.bv * 'Auu____3595)  ->  (FStar_Syntax_Syntax.bv * 'Auu____3595) FStar_Util.pimap FStar_Util.psmap  ->  (FStar_Syntax_Syntax.bv * 'Auu____3595) FStar_Util.pimap FStar_Util.psmap = (fun bvb bvbs -> (FStar_Util.psmap_modify bvbs (FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.ppname.FStar_Ident.idText (fun pimap_opt -> (

let uu____3655 = (

let uu____3662 = (FStar_Util.pimap_empty ())
in (FStar_Util.dflt uu____3662 pimap_opt))
in (FStar_Util.pimap_add uu____3655 (FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.index bvb)))))


let add_fvar_binding : fvar_binding  ->  fvar_binding FStar_Util.psmap  ->  fvar_binding FStar_Util.psmap = (fun fvb fvbs -> (FStar_Util.psmap_add fvbs fvb.fvar_lid.FStar_Ident.str fvb))


let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (

let xsym = (varops.fresh x)
in (

let uu____3720 = (

let uu____3721 = (FStar_SMTEncoding_Term.mk_fv ((xsym), (s)))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____3721))
in ((xsym), (uu____3720)))))


let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (Prims.strcat "@x" (Prims.string_of_int env.depth))
in (

let y = (

let uu____3746 = (FStar_SMTEncoding_Term.mk_fv ((ysym), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____3746))
in (

let uu____3748 = (

let uu___271_3749 = env
in (

let uu____3750 = (add_bvar_binding ((x), (y)) env.bvar_bindings)
in {bvar_bindings = uu____3750; fvar_bindings = uu___271_3749.fvar_bindings; depth = (env.depth + (Prims.parse_int "1")); tcenv = uu___271_3749.tcenv; warn = uu___271_3749.warn; cache = uu___271_3749.cache; nolabels = uu___271_3749.nolabels; use_zfuel_name = uu___271_3749.use_zfuel_name; encode_non_total_function_typ = uu___271_3749.encode_non_total_function_typ; current_module_name = uu___271_3749.current_module_name; encoding_quantifier = uu___271_3749.encoding_quantifier}))
in ((ysym), (y), (uu____3748))))))


let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in (

let uu____3785 = (

let uu___272_3786 = env
in (

let uu____3787 = (add_bvar_binding ((x), (y)) env.bvar_bindings)
in {bvar_bindings = uu____3787; fvar_bindings = uu___272_3786.fvar_bindings; depth = uu___272_3786.depth; tcenv = uu___272_3786.tcenv; warn = uu___272_3786.warn; cache = uu___272_3786.cache; nolabels = uu___272_3786.nolabels; use_zfuel_name = uu___272_3786.use_zfuel_name; encode_non_total_function_typ = uu___272_3786.encode_non_total_function_typ; current_module_name = uu___272_3786.current_module_name; encoding_quantifier = uu___272_3786.encoding_quantifier}))
in ((ysym), (y), (uu____3785))))))


let new_term_constant_from_string : env_t  ->  FStar_Syntax_Syntax.bv  ->  Prims.string  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x str -> (

let ysym = (varops.mk_unique str)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in (

let uu____3828 = (

let uu___273_3829 = env
in (

let uu____3830 = (add_bvar_binding ((x), (y)) env.bvar_bindings)
in {bvar_bindings = uu____3830; fvar_bindings = uu___273_3829.fvar_bindings; depth = uu___273_3829.depth; tcenv = uu___273_3829.tcenv; warn = uu___273_3829.warn; cache = uu___273_3829.cache; nolabels = uu___273_3829.nolabels; use_zfuel_name = uu___273_3829.use_zfuel_name; encode_non_total_function_typ = uu___273_3829.encode_non_total_function_typ; current_module_name = uu___273_3829.current_module_name; encoding_quantifier = uu___273_3829.encoding_quantifier}))
in ((ysym), (y), (uu____3828))))))


let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (

let uu___274_3856 = env
in (

let uu____3857 = (add_bvar_binding ((x), (t)) env.bvar_bindings)
in {bvar_bindings = uu____3857; fvar_bindings = uu___274_3856.fvar_bindings; depth = uu___274_3856.depth; tcenv = uu___274_3856.tcenv; warn = uu___274_3856.warn; cache = uu___274_3856.cache; nolabels = uu___274_3856.nolabels; use_zfuel_name = uu___274_3856.use_zfuel_name; encode_non_total_function_typ = uu___274_3856.encode_non_total_function_typ; current_module_name = uu___274_3856.current_module_name; encoding_quantifier = uu___274_3856.encoding_quantifier})))


let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let uu____3877 = (lookup_bvar_binding env a)
in (match (uu____3877) with
| FStar_Pervasives_Native.None -> begin
(

let uu____3888 = (lookup_bvar_binding env a)
in (match (uu____3888) with
| FStar_Pervasives_Native.None -> begin
(

let uu____3899 = (

let uu____3901 = (FStar_Syntax_Print.bv_to_string a)
in (

let uu____3903 = (print_env env)
in (FStar_Util.format2 "Bound term variable not found  %s in environment: %s" uu____3901 uu____3903)))
in (failwith uu____3899))
end
| FStar_Pervasives_Native.Some (b, t) -> begin
t
end))
end
| FStar_Pervasives_Native.Some (b, t) -> begin
t
end)))


let mk_fvb : FStar_Ident.lident  ->  Prims.string  ->  Prims.int  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  Prims.bool  ->  fvar_binding = (fun lid fname arity ftok fuel_partial_app thunked -> (

let fvb = {fvar_lid = lid; smt_arity = arity; smt_id = fname; smt_token = ftok; smt_fuel_partial_app = fuel_partial_app; fvb_thunked = thunked}
in ((check_valid_fvb fvb);
fvb;
)))


let new_term_constant_and_tok_from_lid_aux : env_t  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.bool  ->  (Prims.string * Prims.string FStar_Pervasives_Native.option * env_t) = (fun env x arity thunked -> (

let fname = (varops.new_fvar x)
in (

let uu____4002 = (match (thunked) with
| true -> begin
((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None))
end
| uu____4028 -> begin
(

let ftok_name = (Prims.strcat fname "@tok")
in (

let ftok = (FStar_SMTEncoding_Util.mkApp ((ftok_name), ([])))
in ((FStar_Pervasives_Native.Some (ftok_name)), (FStar_Pervasives_Native.Some (ftok)))))
end)
in (match (uu____4002) with
| (ftok_name, ftok) -> begin
(

let fvb = (mk_fvb x fname arity ftok FStar_Pervasives_Native.None thunked)
in (

let uu____4066 = (

let uu___275_4067 = env
in (

let uu____4068 = (add_fvar_binding fvb env.fvar_bindings)
in {bvar_bindings = uu___275_4067.bvar_bindings; fvar_bindings = uu____4068; depth = uu___275_4067.depth; tcenv = uu___275_4067.tcenv; warn = uu___275_4067.warn; cache = uu___275_4067.cache; nolabels = uu___275_4067.nolabels; use_zfuel_name = uu___275_4067.use_zfuel_name; encode_non_total_function_typ = uu___275_4067.encode_non_total_function_typ; current_module_name = uu___275_4067.current_module_name; encoding_quantifier = uu___275_4067.encoding_quantifier}))
in ((fname), (ftok_name), (uu____4066))))
end))))


let new_term_constant_and_tok_from_lid : env_t  ->  FStar_Ident.lident  ->  Prims.int  ->  (Prims.string * Prims.string * env_t) = (fun env x arity -> (

let uu____4101 = (new_term_constant_and_tok_from_lid_aux env x arity false)
in (match (uu____4101) with
| (fname, ftok_name_opt, env1) -> begin
(

let uu____4132 = (FStar_Option.get ftok_name_opt)
in ((fname), (uu____4132), (env1)))
end)))


let new_term_constant_and_tok_from_lid_maybe_thunked : env_t  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.bool  ->  (Prims.string * Prims.string FStar_Pervasives_Native.option * env_t) = (fun env x arity th -> (new_term_constant_and_tok_from_lid_aux env x arity th))


let lookup_lid : env_t  ->  FStar_Ident.lident  ->  fvar_binding = (fun env a -> (

let uu____4183 = (lookup_fvar_binding env a)
in (match (uu____4183) with
| FStar_Pervasives_Native.None -> begin
(

let uu____4186 = (

let uu____4188 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" uu____4188))
in (failwith uu____4186))
end
| FStar_Pervasives_Native.Some (s) -> begin
((check_valid_fvb s);
s;
)
end)))


let push_free_var_maybe_thunked : env_t  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  Prims.bool  ->  env_t = (fun env x arity fname ftok thunked -> (

let fvb = (mk_fvb x fname arity ftok FStar_Pervasives_Native.None thunked)
in (

let uu___276_4235 = env
in (

let uu____4236 = (add_fvar_binding fvb env.fvar_bindings)
in {bvar_bindings = uu___276_4235.bvar_bindings; fvar_bindings = uu____4236; depth = uu___276_4235.depth; tcenv = uu___276_4235.tcenv; warn = uu___276_4235.warn; cache = uu___276_4235.cache; nolabels = uu___276_4235.nolabels; use_zfuel_name = uu___276_4235.use_zfuel_name; encode_non_total_function_typ = uu___276_4235.encode_non_total_function_typ; current_module_name = uu___276_4235.current_module_name; encoding_quantifier = uu___276_4235.encoding_quantifier}))))


let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  env_t = (fun env x arity fname ftok -> (push_free_var_maybe_thunked env x arity fname ftok false))


let push_free_var_thunk : env_t  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  env_t = (fun env x arity fname ftok -> (push_free_var_maybe_thunked env x arity fname ftok (Prims.op_Equality arity (Prims.parse_int "0"))))


let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (

let fvb = (lookup_lid env x)
in (

let t3 = (

let uu____4330 = (

let uu____4338 = (

let uu____4341 = (FStar_SMTEncoding_Util.mkApp (("ZFuel"), ([])))
in (uu____4341)::[])
in ((f), (uu____4338)))
in (FStar_SMTEncoding_Util.mkApp uu____4330))
in (

let fvb1 = (mk_fvb x fvb.smt_id fvb.smt_arity fvb.smt_token (FStar_Pervasives_Native.Some (t3)) false)
in (

let uu___277_4351 = env
in (

let uu____4352 = (add_fvar_binding fvb1 env.fvar_bindings)
in {bvar_bindings = uu___277_4351.bvar_bindings; fvar_bindings = uu____4352; depth = uu___277_4351.depth; tcenv = uu___277_4351.tcenv; warn = uu___277_4351.warn; cache = uu___277_4351.cache; nolabels = uu___277_4351.nolabels; use_zfuel_name = uu___277_4351.use_zfuel_name; encode_non_total_function_typ = uu___277_4351.encode_non_total_function_typ; current_module_name = uu___277_4351.current_module_name; encoding_quantifier = uu___277_4351.encoding_quantifier}))))))


let force_thunk : fvar_binding  ->  FStar_SMTEncoding_Term.term = (fun fvb -> ((match (((not (fvb.fvb_thunked)) || (Prims.op_disEquality fvb.smt_arity (Prims.parse_int "0")))) with
| true -> begin
(failwith "Forcing a non-thunk in the SMT encoding")
end
| uu____4366 -> begin
()
end);
(FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV ((fvb.smt_id), (FStar_SMTEncoding_Term.Term_sort), (true)));
))


let try_lookup_free_var : env_t  ->  FStar_Ident.lident  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun env l -> (

let uu____4384 = (lookup_fvar_binding env l)
in (match (uu____4384) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (fvb) -> begin
(match (fvb.fvb_thunked) with
| true -> begin
(

let uu____4393 = (force_thunk fvb)
in FStar_Pervasives_Native.Some (uu____4393))
end
| uu____4394 -> begin
(match (fvb.smt_fuel_partial_app) with
| FStar_Pervasives_Native.Some (f) when env.use_zfuel_name -> begin
FStar_Pervasives_Native.Some (f)
end
| uu____4399 -> begin
(match (fvb.smt_token) with
| FStar_Pervasives_Native.Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (uu____4407, (fuel)::[]) -> begin
(

let uu____4411 = (

let uu____4413 = (

let uu____4415 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right uu____4415 FStar_SMTEncoding_Term.fv_name))
in (FStar_Util.starts_with uu____4413 "fuel"))
in (match (uu____4411) with
| true -> begin
(

let uu____4421 = (

let uu____4422 = (

let uu____4423 = (FStar_SMTEncoding_Term.mk_fv ((fvb.smt_id), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____4423))
in (FStar_SMTEncoding_Term.mk_ApplyTF uu____4422 fuel))
in (FStar_All.pipe_left (fun _0_1 -> FStar_Pervasives_Native.Some (_0_1)) uu____4421))
end
| uu____4427 -> begin
FStar_Pervasives_Native.Some (t)
end))
end
| uu____4429 -> begin
FStar_Pervasives_Native.Some (t)
end)
end
| uu____4430 -> begin
FStar_Pervasives_Native.None
end)
end)
end)
end)))


let lookup_free_var : env_t  ->  FStar_Ident.lid FStar_Syntax_Syntax.withinfo_t  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let uu____4448 = (try_lookup_free_var env a.FStar_Syntax_Syntax.v)
in (match (uu____4448) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let uu____4452 = (

let uu____4454 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" uu____4454))
in (failwith uu____4452))
end)))


let lookup_free_var_name : env_t  ->  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t  ->  fvar_binding = (fun env a -> (lookup_lid env a.FStar_Syntax_Syntax.v))


let lookup_free_var_sym : env_t  ->  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t  ->  ((FStar_SMTEncoding_Term.op, FStar_SMTEncoding_Term.term) FStar_Util.either * FStar_SMTEncoding_Term.term Prims.list * Prims.int) = (fun env a -> (

let fvb = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (fvb.smt_fuel_partial_app) with
| FStar_Pervasives_Native.Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.freevars = uu____4516; FStar_SMTEncoding_Term.rng = uu____4517}) when env.use_zfuel_name -> begin
((FStar_Util.Inl (g)), (zf), ((fvb.smt_arity + (Prims.parse_int "1"))))
end
| uu____4542 -> begin
(match (fvb.smt_token) with
| FStar_Pervasives_Native.None when fvb.fvb_thunked -> begin
(

let uu____4558 = (

let uu____4563 = (force_thunk fvb)
in FStar_Util.Inr (uu____4563))
in ((uu____4558), ([]), (fvb.smt_arity)))
end
| FStar_Pervasives_Native.None -> begin
((FStar_Util.Inl (FStar_SMTEncoding_Term.Var (fvb.smt_id))), ([]), (fvb.smt_arity))
end
| FStar_Pervasives_Native.Some (sym) -> begin
(match (sym.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, (fuel)::[]) -> begin
((FStar_Util.Inl (g)), ((fuel)::[]), ((fvb.smt_arity + (Prims.parse_int "1"))))
end
| uu____4604 -> begin
((FStar_Util.Inl (FStar_SMTEncoding_Term.Var (fvb.smt_id))), ([]), (fvb.smt_arity))
end)
end)
end)))


let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun env nm -> (FStar_Util.psmap_find_map env.fvar_bindings (fun uu____4630 fvb -> ((check_valid_fvb fvb);
(match ((Prims.op_Equality fvb.smt_id nm)) with
| true -> begin
fvb.smt_token
end
| uu____4638 -> begin
FStar_Pervasives_Native.None
end);
))))




