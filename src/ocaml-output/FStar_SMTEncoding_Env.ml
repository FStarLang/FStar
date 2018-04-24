
open Prims
open FStar_Pervasives
exception Inner_let_rec


let uu___is_Inner_let_rec : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Inner_let_rec -> begin
true
end
| uu____6 -> begin
false
end))


let add_fuel : 'Auu____13 . 'Auu____13  ->  'Auu____13 Prims.list  ->  'Auu____13 Prims.list = (fun x tl1 -> (

let uu____30 = (FStar_Options.unthrottle_inductives ())
in (match (uu____30) with
| true -> begin
tl1
end
| uu____33 -> begin
(x)::tl1
end)))


let withenv : 'Auu____44 'Auu____45 'Auu____46 . 'Auu____44  ->  ('Auu____45 * 'Auu____46)  ->  ('Auu____45 * 'Auu____46 * 'Auu____44) = (fun c uu____66 -> (match (uu____66) with
| (a, b) -> begin
((a), (b), (c))
end))


let vargs : 'Auu____81 'Auu____82 'Auu____83 . (('Auu____81, 'Auu____82) FStar_Util.either * 'Auu____83) Prims.list  ->  (('Auu____81, 'Auu____82) FStar_Util.either * 'Auu____83) Prims.list = (fun args -> (FStar_List.filter (fun uu___58_130 -> (match (uu___58_130) with
| (FStar_Util.Inl (uu____139), uu____140) -> begin
false
end
| uu____145 -> begin
true
end)) args))


let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s 39 (*'*) 95 (*_*)))


let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun lid a -> (

let a1 = (

let uu___60_172 = a
in (

let uu____173 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = uu____173; FStar_Syntax_Syntax.index = uu___60_172.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___60_172.FStar_Syntax_Syntax.sort}))
in (

let uu____174 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str a1.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (FStar_All.pipe_left escape uu____174))))


let primitive_projector_by_pos : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (

let fail1 = (fun uu____195 -> (

let uu____196 = (FStar_Util.format2 "Projector %s on data constructor %s not found" (Prims.string_of_int i) lid.FStar_Ident.str)
in (failwith uu____196)))
in (

let uu____197 = (FStar_TypeChecker_Env.lookup_datacon env lid)
in (match (uu____197) with
| (uu____202, t) -> begin
(

let uu____204 = (

let uu____205 = (FStar_Syntax_Subst.compress t)
in uu____205.FStar_Syntax_Syntax.n)
in (match (uu____204) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____226 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____226) with
| (binders, uu____232) -> begin
(match (((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders)))) with
| true -> begin
(fail1 ())
end
| uu____237 -> begin
(

let b = (FStar_List.nth binders i)
in (mk_term_projector_name lid (FStar_Pervasives_Native.fst b)))
end)
end))
end
| uu____247 -> begin
(fail1 ())
end))
end))))


let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (

let uu____258 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str (Prims.string_of_int i))
in (FStar_All.pipe_left escape uu____258)))


let mk_term_projector : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun lid a -> (

let uu____269 = (

let uu____274 = (mk_term_projector_name lid a)
in ((uu____274), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Util.mkFreeV uu____269)))


let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_SMTEncoding_Term.term = (fun lid i -> (

let uu____285 = (

let uu____290 = (mk_term_projector_name_by_pos lid i)
in ((uu____290), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Util.mkFreeV uu____285)))


let mk_data_tester : 'Auu____299 . 'Auu____299  ->  FStar_Ident.lident  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (fun env l x -> (FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x))

type varops_t =
{push : unit  ->  unit; pop : unit  ->  unit; new_var : FStar_Ident.ident  ->  Prims.int  ->  Prims.string; new_fvar : FStar_Ident.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_SMTEncoding_Term.term; next_id : unit  ->  Prims.int; mk_unique : Prims.string  ->  Prims.string}


let __proj__Mkvarops_t__item__push : varops_t  ->  unit  ->  unit = (fun projectee -> (match (projectee) with
| {push = __fname__push; pop = __fname__pop; new_var = __fname__new_var; new_fvar = __fname__new_fvar; fresh = __fname__fresh; string_const = __fname__string_const; next_id = __fname__next_id; mk_unique = __fname__mk_unique} -> begin
__fname__push
end))


let __proj__Mkvarops_t__item__pop : varops_t  ->  unit  ->  unit = (fun projectee -> (match (projectee) with
| {push = __fname__push; pop = __fname__pop; new_var = __fname__new_var; new_fvar = __fname__new_fvar; fresh = __fname__fresh; string_const = __fname__string_const; next_id = __fname__next_id; mk_unique = __fname__mk_unique} -> begin
__fname__pop
end))


let __proj__Mkvarops_t__item__new_var : varops_t  ->  FStar_Ident.ident  ->  Prims.int  ->  Prims.string = (fun projectee -> (match (projectee) with
| {push = __fname__push; pop = __fname__pop; new_var = __fname__new_var; new_fvar = __fname__new_fvar; fresh = __fname__fresh; string_const = __fname__string_const; next_id = __fname__next_id; mk_unique = __fname__mk_unique} -> begin
__fname__new_var
end))


let __proj__Mkvarops_t__item__new_fvar : varops_t  ->  FStar_Ident.lident  ->  Prims.string = (fun projectee -> (match (projectee) with
| {push = __fname__push; pop = __fname__pop; new_var = __fname__new_var; new_fvar = __fname__new_fvar; fresh = __fname__fresh; string_const = __fname__string_const; next_id = __fname__next_id; mk_unique = __fname__mk_unique} -> begin
__fname__new_fvar
end))


let __proj__Mkvarops_t__item__fresh : varops_t  ->  Prims.string  ->  Prims.string = (fun projectee -> (match (projectee) with
| {push = __fname__push; pop = __fname__pop; new_var = __fname__new_var; new_fvar = __fname__new_fvar; fresh = __fname__fresh; string_const = __fname__string_const; next_id = __fname__next_id; mk_unique = __fname__mk_unique} -> begin
__fname__fresh
end))


let __proj__Mkvarops_t__item__string_const : varops_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term = (fun projectee -> (match (projectee) with
| {push = __fname__push; pop = __fname__pop; new_var = __fname__new_var; new_fvar = __fname__new_fvar; fresh = __fname__fresh; string_const = __fname__string_const; next_id = __fname__next_id; mk_unique = __fname__mk_unique} -> begin
__fname__string_const
end))


let __proj__Mkvarops_t__item__next_id : varops_t  ->  unit  ->  Prims.int = (fun projectee -> (match (projectee) with
| {push = __fname__push; pop = __fname__pop; new_var = __fname__new_var; new_fvar = __fname__new_fvar; fresh = __fname__fresh; string_const = __fname__string_const; next_id = __fname__next_id; mk_unique = __fname__mk_unique} -> begin
__fname__next_id
end))


let __proj__Mkvarops_t__item__mk_unique : varops_t  ->  Prims.string  ->  Prims.string = (fun projectee -> (match (projectee) with
| {push = __fname__push; pop = __fname__pop; new_var = __fname__new_var; new_fvar = __fname__new_fvar; fresh = __fname__fresh; string_const = __fname__string_const; next_id = __fname__next_id; mk_unique = __fname__mk_unique} -> begin
__fname__mk_unique
end))


let varops : varops_t = (

let initial_ctr = (Prims.parse_int "100")
in (

let ctr = (FStar_Util.mk_ref initial_ctr)
in (

let new_scope = (fun uu____800 -> (

let uu____801 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (

let uu____804 = (FStar_Util.smap_create (Prims.parse_int "100"))
in ((uu____801), (uu____804)))))
in (

let scopes = (

let uu____824 = (

let uu____835 = (new_scope ())
in (uu____835)::[])
in (FStar_Util.mk_ref uu____824))
in (

let mk_unique = (fun y -> (

let y1 = (escape y)
in (

let y2 = (

let uu____878 = (

let uu____881 = (FStar_ST.op_Bang scopes)
in (FStar_Util.find_map uu____881 (fun uu____1022 -> (match (uu____1022) with
| (names1, uu____1034) -> begin
(FStar_Util.smap_try_find names1 y1)
end))))
in (match (uu____878) with
| FStar_Pervasives_Native.None -> begin
y1
end
| FStar_Pervasives_Native.Some (uu____1043) -> begin
((FStar_Util.incr ctr);
(

let uu____1150 = (

let uu____1151 = (

let uu____1152 = (FStar_ST.op_Bang ctr)
in (Prims.string_of_int uu____1152))
in (Prims.strcat "__" uu____1151))
in (Prims.strcat y1 uu____1150));
)
end))
in (

let top_scope = (

let uu____1255 = (

let uu____1264 = (FStar_ST.op_Bang scopes)
in (FStar_List.hd uu____1264))
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1255))
in ((FStar_Util.smap_add top_scope y2 true);
y2;
)))))
in (

let new_var = (fun pp rn -> (FStar_All.pipe_left mk_unique (Prims.strcat pp.FStar_Ident.idText (Prims.strcat "__" (Prims.string_of_int rn)))))
in (

let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (

let next_id1 = (fun uu____1439 -> ((FStar_Util.incr ctr);
(FStar_ST.op_Bang ctr);
))
in (

let fresh1 = (fun pfx -> (

let uu____1651 = (

let uu____1652 = (next_id1 ())
in (FStar_All.pipe_left Prims.string_of_int uu____1652))
in (FStar_Util.format2 "%s_%s" pfx uu____1651)))
in (

let string_const = (fun s -> (

let uu____1659 = (

let uu____1662 = (FStar_ST.op_Bang scopes)
in (FStar_Util.find_map uu____1662 (fun uu____1803 -> (match (uu____1803) with
| (uu____1814, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))
in (match (uu____1659) with
| FStar_Pervasives_Native.Some (f) -> begin
f
end
| FStar_Pervasives_Native.None -> begin
(

let id1 = (next_id1 ())
in (

let f = (

let uu____1827 = (FStar_SMTEncoding_Util.mk_String_const id1)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1827))
in (

let top_scope = (

let uu____1831 = (

let uu____1840 = (FStar_ST.op_Bang scopes)
in (FStar_List.hd uu____1840))
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1831))
in ((FStar_Util.smap_add top_scope s f);
f;
))))
end)))
in (

let push1 = (fun uu____1998 -> (

let uu____1999 = (

let uu____2010 = (new_scope ())
in (

let uu____2019 = (FStar_ST.op_Bang scopes)
in (uu____2010)::uu____2019))
in (FStar_ST.op_Colon_Equals scopes uu____1999)))
in (

let pop1 = (fun uu____2281 -> (

let uu____2282 = (

let uu____2293 = (FStar_ST.op_Bang scopes)
in (FStar_List.tl uu____2293))
in (FStar_ST.op_Colon_Equals scopes uu____2282)))
in {push = push1; pop = pop1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; string_const = string_const; next_id = next_id1; mk_unique = mk_unique}))))))))))))


let unmangle : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv = (fun x -> (

let uu___61_2555 = x
in (

let uu____2556 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = uu____2556; FStar_Syntax_Syntax.index = uu___61_2555.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___61_2555.FStar_Syntax_Syntax.sort})))

type fvar_binding =
{fvar_lid : FStar_Ident.lident; smt_arity : Prims.int; smt_id : Prims.string; smt_token : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option; smt_fuel_partial_app : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option}


let __proj__Mkfvar_binding__item__fvar_lid : fvar_binding  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {fvar_lid = __fname__fvar_lid; smt_arity = __fname__smt_arity; smt_id = __fname__smt_id; smt_token = __fname__smt_token; smt_fuel_partial_app = __fname__smt_fuel_partial_app} -> begin
__fname__fvar_lid
end))


let __proj__Mkfvar_binding__item__smt_arity : fvar_binding  ->  Prims.int = (fun projectee -> (match (projectee) with
| {fvar_lid = __fname__fvar_lid; smt_arity = __fname__smt_arity; smt_id = __fname__smt_id; smt_token = __fname__smt_token; smt_fuel_partial_app = __fname__smt_fuel_partial_app} -> begin
__fname__smt_arity
end))


let __proj__Mkfvar_binding__item__smt_id : fvar_binding  ->  Prims.string = (fun projectee -> (match (projectee) with
| {fvar_lid = __fname__fvar_lid; smt_arity = __fname__smt_arity; smt_id = __fname__smt_id; smt_token = __fname__smt_token; smt_fuel_partial_app = __fname__smt_fuel_partial_app} -> begin
__fname__smt_id
end))


let __proj__Mkfvar_binding__item__smt_token : fvar_binding  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {fvar_lid = __fname__fvar_lid; smt_arity = __fname__smt_arity; smt_id = __fname__smt_id; smt_token = __fname__smt_token; smt_fuel_partial_app = __fname__smt_fuel_partial_app} -> begin
__fname__smt_token
end))


let __proj__Mkfvar_binding__item__smt_fuel_partial_app : fvar_binding  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {fvar_lid = __fname__fvar_lid; smt_arity = __fname__smt_arity; smt_id = __fname__smt_id; smt_token = __fname__smt_token; smt_fuel_partial_app = __fname__smt_fuel_partial_app} -> begin
__fname__smt_fuel_partial_app
end))


let binder_of_eithervar : 'Auu____2670 'Auu____2671 . 'Auu____2670  ->  ('Auu____2670 * 'Auu____2671 FStar_Pervasives_Native.option) = (fun v1 -> ((v1), (FStar_Pervasives_Native.None)))

type cache_entry =
{cache_symbol_name : Prims.string; cache_symbol_arg_sorts : FStar_SMTEncoding_Term.sort Prims.list; cache_symbol_decls : FStar_SMTEncoding_Term.decl Prims.list; cache_symbol_assumption_names : Prims.string Prims.list}


let __proj__Mkcache_entry__item__cache_symbol_name : cache_entry  ->  Prims.string = (fun projectee -> (match (projectee) with
| {cache_symbol_name = __fname__cache_symbol_name; cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts; cache_symbol_decls = __fname__cache_symbol_decls; cache_symbol_assumption_names = __fname__cache_symbol_assumption_names} -> begin
__fname__cache_symbol_name
end))


let __proj__Mkcache_entry__item__cache_symbol_arg_sorts : cache_entry  ->  FStar_SMTEncoding_Term.sort Prims.list = (fun projectee -> (match (projectee) with
| {cache_symbol_name = __fname__cache_symbol_name; cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts; cache_symbol_decls = __fname__cache_symbol_decls; cache_symbol_assumption_names = __fname__cache_symbol_assumption_names} -> begin
__fname__cache_symbol_arg_sorts
end))


let __proj__Mkcache_entry__item__cache_symbol_decls : cache_entry  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun projectee -> (match (projectee) with
| {cache_symbol_name = __fname__cache_symbol_name; cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts; cache_symbol_decls = __fname__cache_symbol_decls; cache_symbol_assumption_names = __fname__cache_symbol_assumption_names} -> begin
__fname__cache_symbol_decls
end))


let __proj__Mkcache_entry__item__cache_symbol_assumption_names : cache_entry  ->  Prims.string Prims.list = (fun projectee -> (match (projectee) with
| {cache_symbol_name = __fname__cache_symbol_name; cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts; cache_symbol_decls = __fname__cache_symbol_decls; cache_symbol_assumption_names = __fname__cache_symbol_assumption_names} -> begin
__fname__cache_symbol_assumption_names
end))

type env_t =
{bvar_bindings : (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) FStar_Util.pimap FStar_Util.psmap; fvar_bindings : fvar_binding FStar_Util.psmap; depth : Prims.int; tcenv : FStar_TypeChecker_Env.env; warn : Prims.bool; cache : cache_entry FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool; current_module_name : Prims.string; encoding_quantifier : Prims.bool}


let __proj__Mkenv_t__item__bvar_bindings : env_t  ->  (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) FStar_Util.pimap FStar_Util.psmap = (fun projectee -> (match (projectee) with
| {bvar_bindings = __fname__bvar_bindings; fvar_bindings = __fname__fvar_bindings; depth = __fname__depth; tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache; nolabels = __fname__nolabels; use_zfuel_name = __fname__use_zfuel_name; encode_non_total_function_typ = __fname__encode_non_total_function_typ; current_module_name = __fname__current_module_name; encoding_quantifier = __fname__encoding_quantifier} -> begin
__fname__bvar_bindings
end))


let __proj__Mkenv_t__item__fvar_bindings : env_t  ->  fvar_binding FStar_Util.psmap = (fun projectee -> (match (projectee) with
| {bvar_bindings = __fname__bvar_bindings; fvar_bindings = __fname__fvar_bindings; depth = __fname__depth; tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache; nolabels = __fname__nolabels; use_zfuel_name = __fname__use_zfuel_name; encode_non_total_function_typ = __fname__encode_non_total_function_typ; current_module_name = __fname__current_module_name; encoding_quantifier = __fname__encoding_quantifier} -> begin
__fname__fvar_bindings
end))


let __proj__Mkenv_t__item__depth : env_t  ->  Prims.int = (fun projectee -> (match (projectee) with
| {bvar_bindings = __fname__bvar_bindings; fvar_bindings = __fname__fvar_bindings; depth = __fname__depth; tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache; nolabels = __fname__nolabels; use_zfuel_name = __fname__use_zfuel_name; encode_non_total_function_typ = __fname__encode_non_total_function_typ; current_module_name = __fname__current_module_name; encoding_quantifier = __fname__encoding_quantifier} -> begin
__fname__depth
end))


let __proj__Mkenv_t__item__tcenv : env_t  ->  FStar_TypeChecker_Env.env = (fun projectee -> (match (projectee) with
| {bvar_bindings = __fname__bvar_bindings; fvar_bindings = __fname__fvar_bindings; depth = __fname__depth; tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache; nolabels = __fname__nolabels; use_zfuel_name = __fname__use_zfuel_name; encode_non_total_function_typ = __fname__encode_non_total_function_typ; current_module_name = __fname__current_module_name; encoding_quantifier = __fname__encoding_quantifier} -> begin
__fname__tcenv
end))


let __proj__Mkenv_t__item__warn : env_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {bvar_bindings = __fname__bvar_bindings; fvar_bindings = __fname__fvar_bindings; depth = __fname__depth; tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache; nolabels = __fname__nolabels; use_zfuel_name = __fname__use_zfuel_name; encode_non_total_function_typ = __fname__encode_non_total_function_typ; current_module_name = __fname__current_module_name; encoding_quantifier = __fname__encoding_quantifier} -> begin
__fname__warn
end))


let __proj__Mkenv_t__item__cache : env_t  ->  cache_entry FStar_Util.smap = (fun projectee -> (match (projectee) with
| {bvar_bindings = __fname__bvar_bindings; fvar_bindings = __fname__fvar_bindings; depth = __fname__depth; tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache; nolabels = __fname__nolabels; use_zfuel_name = __fname__use_zfuel_name; encode_non_total_function_typ = __fname__encode_non_total_function_typ; current_module_name = __fname__current_module_name; encoding_quantifier = __fname__encoding_quantifier} -> begin
__fname__cache
end))


let __proj__Mkenv_t__item__nolabels : env_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {bvar_bindings = __fname__bvar_bindings; fvar_bindings = __fname__fvar_bindings; depth = __fname__depth; tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache; nolabels = __fname__nolabels; use_zfuel_name = __fname__use_zfuel_name; encode_non_total_function_typ = __fname__encode_non_total_function_typ; current_module_name = __fname__current_module_name; encoding_quantifier = __fname__encoding_quantifier} -> begin
__fname__nolabels
end))


let __proj__Mkenv_t__item__use_zfuel_name : env_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {bvar_bindings = __fname__bvar_bindings; fvar_bindings = __fname__fvar_bindings; depth = __fname__depth; tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache; nolabels = __fname__nolabels; use_zfuel_name = __fname__use_zfuel_name; encode_non_total_function_typ = __fname__encode_non_total_function_typ; current_module_name = __fname__current_module_name; encoding_quantifier = __fname__encoding_quantifier} -> begin
__fname__use_zfuel_name
end))


let __proj__Mkenv_t__item__encode_non_total_function_typ : env_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {bvar_bindings = __fname__bvar_bindings; fvar_bindings = __fname__fvar_bindings; depth = __fname__depth; tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache; nolabels = __fname__nolabels; use_zfuel_name = __fname__use_zfuel_name; encode_non_total_function_typ = __fname__encode_non_total_function_typ; current_module_name = __fname__current_module_name; encoding_quantifier = __fname__encoding_quantifier} -> begin
__fname__encode_non_total_function_typ
end))


let __proj__Mkenv_t__item__current_module_name : env_t  ->  Prims.string = (fun projectee -> (match (projectee) with
| {bvar_bindings = __fname__bvar_bindings; fvar_bindings = __fname__fvar_bindings; depth = __fname__depth; tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache; nolabels = __fname__nolabels; use_zfuel_name = __fname__use_zfuel_name; encode_non_total_function_typ = __fname__encode_non_total_function_typ; current_module_name = __fname__current_module_name; encoding_quantifier = __fname__encoding_quantifier} -> begin
__fname__current_module_name
end))


let __proj__Mkenv_t__item__encoding_quantifier : env_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {bvar_bindings = __fname__bvar_bindings; fvar_bindings = __fname__fvar_bindings; depth = __fname__depth; tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache; nolabels = __fname__nolabels; use_zfuel_name = __fname__use_zfuel_name; encode_non_total_function_typ = __fname__encode_non_total_function_typ; current_module_name = __fname__current_module_name; encoding_quantifier = __fname__encoding_quantifier} -> begin
__fname__encoding_quantifier
end))


let mk_cache_entry : 'Auu____3192 . 'Auu____3192  ->  Prims.string  ->  FStar_SMTEncoding_Term.sort Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  cache_entry = (fun env tsym cvar_sorts t_decls1 -> (

let names1 = (FStar_All.pipe_right t_decls1 (FStar_List.collect (fun uu___59_3230 -> (match (uu___59_3230) with
| FStar_SMTEncoding_Term.Assume (a) -> begin
(a.FStar_SMTEncoding_Term.assumption_name)::[]
end
| uu____3234 -> begin
[]
end))))
in {cache_symbol_name = tsym; cache_symbol_arg_sorts = cvar_sorts; cache_symbol_decls = t_decls1; cache_symbol_assumption_names = names1}))


let use_cache_entry : cache_entry  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun ce -> (FStar_SMTEncoding_Term.RetainAssumptions (ce.cache_symbol_assumption_names))::[])


let print_env : env_t  ->  Prims.string = (fun e -> (

let bvars = (FStar_Util.psmap_fold e.bvar_bindings (fun _k pi acc -> (FStar_Util.pimap_fold pi (fun _i uu____3285 acc1 -> (match (uu____3285) with
| (x, _term) -> begin
(

let uu____3297 = (FStar_Syntax_Print.bv_to_string x)
in (uu____3297)::acc1)
end)) acc)) [])
in (

let allvars = (FStar_Util.psmap_fold e.fvar_bindings (fun _k fvb acc -> (

let uu____3312 = (FStar_Syntax_Print.lid_to_string fvb.fvar_lid)
in (uu____3312)::acc)) bvars)
in (FStar_String.concat ", " allvars))))


let lookup_bvar_binding : env_t  ->  FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.option = (fun env bv -> (

let uu____3329 = (FStar_Util.psmap_try_find env.bvar_bindings bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (match (uu____3329) with
| FStar_Pervasives_Native.Some (bvs) -> begin
(FStar_Util.pimap_try_find bvs bv.FStar_Syntax_Syntax.index)
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)))


let lookup_fvar_binding : env_t  ->  FStar_Ident.lident  ->  fvar_binding FStar_Pervasives_Native.option = (fun env lid -> (FStar_Util.psmap_try_find env.fvar_bindings lid.FStar_Ident.str))


let add_bvar_binding : 'Auu____3395 . (FStar_Syntax_Syntax.bv * 'Auu____3395)  ->  (FStar_Syntax_Syntax.bv * 'Auu____3395) FStar_Util.pimap FStar_Util.psmap  ->  (FStar_Syntax_Syntax.bv * 'Auu____3395) FStar_Util.pimap FStar_Util.psmap = (fun bvb bvbs -> (FStar_Util.psmap_modify bvbs (FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.ppname.FStar_Ident.idText (fun pimap_opt -> (

let uu____3455 = (

let uu____3462 = (FStar_Util.pimap_empty ())
in (FStar_Util.dflt uu____3462 pimap_opt))
in (FStar_Util.pimap_add uu____3455 (FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.index bvb)))))


let add_fvar_binding : fvar_binding  ->  fvar_binding FStar_Util.psmap  ->  fvar_binding FStar_Util.psmap = (fun fvb fvbs -> (FStar_Util.psmap_add fvbs fvb.fvar_lid.FStar_Ident.str fvb))


let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (

let xsym = (varops.fresh x)
in (

let uu____3514 = (FStar_SMTEncoding_Util.mkFreeV ((xsym), (s)))
in ((xsym), (uu____3514)))))


let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (Prims.strcat "@x" (Prims.string_of_int env.depth))
in (

let y = (FStar_SMTEncoding_Util.mkFreeV ((ysym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____3533 = (

let uu___62_3534 = env
in (

let uu____3535 = (add_bvar_binding ((x), (y)) env.bvar_bindings)
in {bvar_bindings = uu____3535; fvar_bindings = uu___62_3534.fvar_bindings; depth = (env.depth + (Prims.parse_int "1")); tcenv = uu___62_3534.tcenv; warn = uu___62_3534.warn; cache = uu___62_3534.cache; nolabels = uu___62_3534.nolabels; use_zfuel_name = uu___62_3534.use_zfuel_name; encode_non_total_function_typ = uu___62_3534.encode_non_total_function_typ; current_module_name = uu___62_3534.current_module_name; encoding_quantifier = uu___62_3534.encoding_quantifier}))
in ((ysym), (y), (uu____3533))))))


let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in (

let uu____3564 = (

let uu___63_3565 = env
in (

let uu____3566 = (add_bvar_binding ((x), (y)) env.bvar_bindings)
in {bvar_bindings = uu____3566; fvar_bindings = uu___63_3565.fvar_bindings; depth = uu___63_3565.depth; tcenv = uu___63_3565.tcenv; warn = uu___63_3565.warn; cache = uu___63_3565.cache; nolabels = uu___63_3565.nolabels; use_zfuel_name = uu___63_3565.use_zfuel_name; encode_non_total_function_typ = uu___63_3565.encode_non_total_function_typ; current_module_name = uu___63_3565.current_module_name; encoding_quantifier = uu___63_3565.encoding_quantifier}))
in ((ysym), (y), (uu____3564))))))


let new_term_constant_from_string : env_t  ->  FStar_Syntax_Syntax.bv  ->  Prims.string  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x str -> (

let ysym = (varops.mk_unique str)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in (

let uu____3600 = (

let uu___64_3601 = env
in (

let uu____3602 = (add_bvar_binding ((x), (y)) env.bvar_bindings)
in {bvar_bindings = uu____3602; fvar_bindings = uu___64_3601.fvar_bindings; depth = uu___64_3601.depth; tcenv = uu___64_3601.tcenv; warn = uu___64_3601.warn; cache = uu___64_3601.cache; nolabels = uu___64_3601.nolabels; use_zfuel_name = uu___64_3601.use_zfuel_name; encode_non_total_function_typ = uu___64_3601.encode_non_total_function_typ; current_module_name = uu___64_3601.current_module_name; encoding_quantifier = uu___64_3601.encoding_quantifier}))
in ((ysym), (y), (uu____3600))))))


let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (

let uu___65_3626 = env
in (

let uu____3627 = (add_bvar_binding ((x), (t)) env.bvar_bindings)
in {bvar_bindings = uu____3627; fvar_bindings = uu___65_3626.fvar_bindings; depth = uu___65_3626.depth; tcenv = uu___65_3626.tcenv; warn = uu___65_3626.warn; cache = uu___65_3626.cache; nolabels = uu___65_3626.nolabels; use_zfuel_name = uu___65_3626.use_zfuel_name; encode_non_total_function_typ = uu___65_3626.encode_non_total_function_typ; current_module_name = uu___65_3626.current_module_name; encoding_quantifier = uu___65_3626.encoding_quantifier})))


let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let uu____3646 = (lookup_bvar_binding env a)
in (match (uu____3646) with
| FStar_Pervasives_Native.None -> begin
(

let a2 = (unmangle a)
in (

let uu____3658 = (lookup_bvar_binding env a2)
in (match (uu____3658) with
| FStar_Pervasives_Native.None -> begin
(

let uu____3669 = (

let uu____3670 = (FStar_Syntax_Print.bv_to_string a2)
in (

let uu____3671 = (print_env env)
in (FStar_Util.format2 "Bound term variable not found (after unmangling): %s in environment: %s" uu____3670 uu____3671)))
in (failwith uu____3669))
end
| FStar_Pervasives_Native.Some (b, t) -> begin
t
end)))
end
| FStar_Pervasives_Native.Some (b, t) -> begin
t
end)))


let mk_fvb : FStar_Ident.lident  ->  Prims.string  ->  Prims.int  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  fvar_binding = (fun lid fname arity ftok fuel_partial_app -> {fvar_lid = lid; smt_arity = arity; smt_id = fname; smt_token = ftok; smt_fuel_partial_app = fuel_partial_app})


let new_term_constant_and_tok_from_lid : env_t  ->  FStar_Ident.lident  ->  Prims.int  ->  (Prims.string * Prims.string * env_t) = (fun env x arity -> (

let fname = (varops.new_fvar x)
in (

let ftok_name = (Prims.strcat fname "@tok")
in (

let ftok = (FStar_SMTEncoding_Util.mkApp ((ftok_name), ([])))
in (

let fvb = (mk_fvb x fname arity (FStar_Pervasives_Native.Some (ftok)) FStar_Pervasives_Native.None)
in (

let uu____3744 = (

let uu___66_3745 = env
in (

let uu____3746 = (add_fvar_binding fvb env.fvar_bindings)
in {bvar_bindings = uu___66_3745.bvar_bindings; fvar_bindings = uu____3746; depth = uu___66_3745.depth; tcenv = uu___66_3745.tcenv; warn = uu___66_3745.warn; cache = uu___66_3745.cache; nolabels = uu___66_3745.nolabels; use_zfuel_name = uu___66_3745.use_zfuel_name; encode_non_total_function_typ = uu___66_3745.encode_non_total_function_typ; current_module_name = uu___66_3745.current_module_name; encoding_quantifier = uu___66_3745.encoding_quantifier}))
in ((fname), (ftok_name), (uu____3744))))))))


let lookup_lid : env_t  ->  FStar_Ident.lident  ->  fvar_binding = (fun env a -> (

let uu____3759 = (lookup_fvar_binding env a)
in (match (uu____3759) with
| FStar_Pervasives_Native.None -> begin
(

let uu____3762 = (

let uu____3763 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" uu____3763))
in (failwith uu____3762))
end
| FStar_Pervasives_Native.Some (s) -> begin
s
end)))


let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  env_t = (fun env x arity fname ftok -> (

let fvb = (mk_fvb x fname arity ftok FStar_Pervasives_Native.None)
in (

let uu___67_3795 = env
in (

let uu____3796 = (add_fvar_binding fvb env.fvar_bindings)
in {bvar_bindings = uu___67_3795.bvar_bindings; fvar_bindings = uu____3796; depth = uu___67_3795.depth; tcenv = uu___67_3795.tcenv; warn = uu___67_3795.warn; cache = uu___67_3795.cache; nolabels = uu___67_3795.nolabels; use_zfuel_name = uu___67_3795.use_zfuel_name; encode_non_total_function_typ = uu___67_3795.encode_non_total_function_typ; current_module_name = uu___67_3795.current_module_name; encoding_quantifier = uu___67_3795.encoding_quantifier}))))


let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (

let fvb = (lookup_lid env x)
in (

let t3 = (

let uu____3816 = (

let uu____3823 = (

let uu____3826 = (FStar_SMTEncoding_Util.mkApp (("ZFuel"), ([])))
in (uu____3826)::[])
in ((f), (uu____3823)))
in (FStar_SMTEncoding_Util.mkApp uu____3816))
in (

let fvb1 = (mk_fvb x fvb.smt_id fvb.smt_arity fvb.smt_token (FStar_Pervasives_Native.Some (t3)))
in (

let uu___68_3832 = env
in (

let uu____3833 = (add_fvar_binding fvb1 env.fvar_bindings)
in {bvar_bindings = uu___68_3832.bvar_bindings; fvar_bindings = uu____3833; depth = uu___68_3832.depth; tcenv = uu___68_3832.tcenv; warn = uu___68_3832.warn; cache = uu___68_3832.cache; nolabels = uu___68_3832.nolabels; use_zfuel_name = uu___68_3832.use_zfuel_name; encode_non_total_function_typ = uu___68_3832.encode_non_total_function_typ; current_module_name = uu___68_3832.current_module_name; encoding_quantifier = uu___68_3832.encoding_quantifier}))))))


let try_lookup_free_var : env_t  ->  FStar_Ident.lident  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun env l -> (

let uu____3848 = (lookup_fvar_binding env l)
in (match (uu____3848) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (fvb) -> begin
(match (fvb.smt_fuel_partial_app) with
| FStar_Pervasives_Native.Some (f) when env.use_zfuel_name -> begin
FStar_Pervasives_Native.Some (f)
end
| uu____3857 -> begin
(match (fvb.smt_token) with
| FStar_Pervasives_Native.Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (uu____3865, (fuel)::[]) -> begin
(

let uu____3869 = (

let uu____3870 = (

let uu____3871 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right uu____3871 FStar_Pervasives_Native.fst))
in (FStar_Util.starts_with uu____3870 "fuel"))
in (match (uu____3869) with
| true -> begin
(

let uu____3874 = (

let uu____3875 = (FStar_SMTEncoding_Util.mkFreeV ((fvb.smt_id), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_ApplyTF uu____3875 fuel))
in (FStar_All.pipe_left (fun _0_17 -> FStar_Pervasives_Native.Some (_0_17)) uu____3874))
end
| uu____3878 -> begin
FStar_Pervasives_Native.Some (t)
end))
end
| uu____3879 -> begin
FStar_Pervasives_Native.Some (t)
end)
end
| uu____3880 -> begin
FStar_Pervasives_Native.None
end)
end)
end)))


let lookup_free_var : env_t  ->  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let uu____3897 = (try_lookup_free_var env a.FStar_Syntax_Syntax.v)
in (match (uu____3897) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let uu____3901 = (

let uu____3902 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" uu____3902))
in (failwith uu____3901))
end)))


let lookup_free_var_name : env_t  ->  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t  ->  (Prims.string * Prims.int) = (fun env a -> (

let fvb = (lookup_lid env a.FStar_Syntax_Syntax.v)
in ((fvb.smt_id), (fvb.smt_arity))))


let lookup_free_var_sym : env_t  ->  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t  ->  (FStar_SMTEncoding_Term.op * FStar_SMTEncoding_Term.term Prims.list * Prims.int) = (fun env a -> (

let fvb = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (fvb.smt_fuel_partial_app) with
| FStar_Pervasives_Native.Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.freevars = uu____3955; FStar_SMTEncoding_Term.rng = uu____3956}) when env.use_zfuel_name -> begin
((g), (zf), ((fvb.smt_arity + (Prims.parse_int "1"))))
end
| uu____3971 -> begin
(match (fvb.smt_token) with
| FStar_Pervasives_Native.None -> begin
((FStar_SMTEncoding_Term.Var (fvb.smt_id)), ([]), (fvb.smt_arity))
end
| FStar_Pervasives_Native.Some (sym) -> begin
(match (sym.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, (fuel)::[]) -> begin
((g), ((fuel)::[]), ((fvb.smt_arity + (Prims.parse_int "1"))))
end
| uu____3999 -> begin
((FStar_SMTEncoding_Term.Var (fvb.smt_id)), ([]), (fvb.smt_arity))
end)
end)
end)))


let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun env nm -> (FStar_Util.psmap_find_map env.fvar_bindings (fun uu____4016 fvb -> (match ((Prims.op_Equality fvb.smt_id nm)) with
| true -> begin
fvb.smt_token
end
| uu____4020 -> begin
FStar_Pervasives_Native.None
end))))




