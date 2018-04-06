
open Prims
open FStar_Pervasives

let add_fuel : 'Auu____4 . 'Auu____4  ->  'Auu____4 Prims.list  ->  'Auu____4 Prims.list = (fun x tl1 -> (

let uu____19 = (FStar_Options.unthrottle_inductives ())
in (match (uu____19) with
| true -> begin
tl1
end
| uu____22 -> begin
(x)::tl1
end)))


let withenv : 'Auu____28 'Auu____29 'Auu____30 . 'Auu____28  ->  ('Auu____29 * 'Auu____30)  ->  ('Auu____29 * 'Auu____30 * 'Auu____28) = (fun c uu____48 -> (match (uu____48) with
| (a, b) -> begin
((a), (b), (c))
end))


let vargs : 'Auu____59 'Auu____60 'Auu____61 . (('Auu____59, 'Auu____60) FStar_Util.either * 'Auu____61) Prims.list  ->  (('Auu____59, 'Auu____60) FStar_Util.either * 'Auu____61) Prims.list = (fun args -> (FStar_List.filter (fun uu___82_107 -> (match (uu___82_107) with
| (FStar_Util.Inl (uu____116), uu____117) -> begin
false
end
| uu____122 -> begin
true
end)) args))


let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s 39 (*'*) 95 (*_*)))


let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun lid a -> (

let a1 = (

let uu___105_143 = a
in (

let uu____144 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = uu____144; FStar_Syntax_Syntax.index = uu___105_143.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___105_143.FStar_Syntax_Syntax.sort}))
in (

let uu____145 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str a1.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (FStar_All.pipe_left escape uu____145))))


let primitive_projector_by_pos : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (

let fail1 = (fun uu____158 -> (

let uu____159 = (FStar_Util.format2 "Projector %s on data constructor %s not found" (Prims.string_of_int i) lid.FStar_Ident.str)
in (failwith uu____159)))
in (

let uu____160 = (FStar_TypeChecker_Env.lookup_datacon env lid)
in (match (uu____160) with
| (uu____165, t) -> begin
(

let uu____167 = (

let uu____168 = (FStar_Syntax_Subst.compress t)
in uu____168.FStar_Syntax_Syntax.n)
in (match (uu____167) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____189 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____189) with
| (binders, uu____195) -> begin
(match (((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders)))) with
| true -> begin
(fail1 ())
end
| uu____200 -> begin
(

let b = (FStar_List.nth binders i)
in (mk_term_projector_name lid (FStar_Pervasives_Native.fst b)))
end)
end))
end
| uu____210 -> begin
(fail1 ())
end))
end))))


let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (

let uu____217 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str (Prims.string_of_int i))
in (FStar_All.pipe_left escape uu____217)))


let mk_term_projector : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun lid a -> (

let uu____224 = (

let uu____229 = (mk_term_projector_name lid a)
in ((uu____229), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Util.mkFreeV uu____224)))


let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_SMTEncoding_Term.term = (fun lid i -> (

let uu____236 = (

let uu____241 = (mk_term_projector_name_by_pos lid i)
in ((uu____241), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Util.mkFreeV uu____236)))


let mk_data_tester : 'Auu____246 . 'Auu____246  ->  FStar_Ident.lident  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (fun env l x -> (FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x))

type varops_t =
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; new_var : FStar_Ident.ident  ->  Prims.int  ->  Prims.string; new_fvar : FStar_Ident.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_SMTEncoding_Term.term; next_id : Prims.unit  ->  Prims.int; mk_unique : Prims.string  ->  Prims.string}


let __proj__Mkvarops_t__item__push : varops_t  ->  Prims.unit  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {push = __fname__push; pop = __fname__pop; new_var = __fname__new_var; new_fvar = __fname__new_fvar; fresh = __fname__fresh; string_const = __fname__string_const; next_id = __fname__next_id; mk_unique = __fname__mk_unique} -> begin
__fname__push
end))


let __proj__Mkvarops_t__item__pop : varops_t  ->  Prims.unit  ->  Prims.unit = (fun projectee -> (match (projectee) with
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


let __proj__Mkvarops_t__item__next_id : varops_t  ->  Prims.unit  ->  Prims.int = (fun projectee -> (match (projectee) with
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

let new_scope = (fun uu____610 -> (

let uu____611 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (

let uu____614 = (FStar_Util.smap_create (Prims.parse_int "100"))
in ((uu____611), (uu____614)))))
in (

let scopes = (

let uu____634 = (

let uu____645 = (new_scope ())
in (uu____645)::[])
in (FStar_Util.mk_ref uu____634))
in (

let mk_unique = (fun y -> (

let y1 = (escape y)
in (

let y2 = (

let uu____686 = (

let uu____689 = (FStar_ST.op_Bang scopes)
in (FStar_Util.find_map uu____689 (fun uu____826 -> (match (uu____826) with
| (names1, uu____838) -> begin
(FStar_Util.smap_try_find names1 y1)
end))))
in (match (uu____686) with
| FStar_Pervasives_Native.None -> begin
y1
end
| FStar_Pervasives_Native.Some (uu____847) -> begin
((FStar_Util.incr ctr);
(

let uu____954 = (

let uu____955 = (

let uu____956 = (FStar_ST.op_Bang ctr)
in (Prims.string_of_int uu____956))
in (Prims.strcat "__" uu____955))
in (Prims.strcat y1 uu____954));
)
end))
in (

let top_scope = (

let uu____1055 = (

let uu____1064 = (FStar_ST.op_Bang scopes)
in (FStar_List.hd uu____1064))
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1055))
in ((FStar_Util.smap_add top_scope y2 true);
y2;
)))))
in (

let new_var = (fun pp rn -> (FStar_All.pipe_left mk_unique (Prims.strcat pp.FStar_Ident.idText (Prims.strcat "__" (Prims.string_of_int rn)))))
in (

let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (

let next_id1 = (fun uu____1227 -> ((FStar_Util.incr ctr);
(FStar_ST.op_Bang ctr);
))
in (

let fresh1 = (fun pfx -> (

let uu____1433 = (

let uu____1434 = (next_id1 ())
in (FStar_All.pipe_left Prims.string_of_int uu____1434))
in (FStar_Util.format2 "%s_%s" pfx uu____1433)))
in (

let string_const = (fun s -> (

let uu____1439 = (

let uu____1442 = (FStar_ST.op_Bang scopes)
in (FStar_Util.find_map uu____1442 (fun uu____1579 -> (match (uu____1579) with
| (uu____1590, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))
in (match (uu____1439) with
| FStar_Pervasives_Native.Some (f) -> begin
f
end
| FStar_Pervasives_Native.None -> begin
(

let id1 = (next_id1 ())
in (

let f = (

let uu____1603 = (FStar_SMTEncoding_Util.mk_String_const id1)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1603))
in (

let top_scope = (

let uu____1607 = (

let uu____1616 = (FStar_ST.op_Bang scopes)
in (FStar_List.hd uu____1616))
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1607))
in ((FStar_Util.smap_add top_scope s f);
f;
))))
end)))
in (

let push1 = (fun uu____1768 -> (

let uu____1769 = (

let uu____1780 = (new_scope ())
in (

let uu____1789 = (FStar_ST.op_Bang scopes)
in (uu____1780)::uu____1789))
in (FStar_ST.op_Colon_Equals scopes uu____1769)))
in (

let pop1 = (fun uu____2041 -> (

let uu____2042 = (

let uu____2053 = (FStar_ST.op_Bang scopes)
in (FStar_List.tl uu____2053))
in (FStar_ST.op_Colon_Equals scopes uu____2042)))
in {push = push1; pop = pop1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; string_const = string_const; next_id = next_id1; mk_unique = mk_unique}))))))))))))


let unmangle : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv = (fun x -> (

let uu___106_2305 = x
in (

let uu____2306 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = uu____2306; FStar_Syntax_Syntax.index = uu___106_2305.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___106_2305.FStar_Syntax_Syntax.sort})))

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

type binding =
| Binding_var of (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term)
| Binding_fvar of fvar_binding


let uu___is_Binding_var : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Binding_var (_0) -> begin
true
end
| uu____2419 -> begin
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
| uu____2443 -> begin
false
end))


let __proj__Binding_fvar__item___0 : binding  ->  fvar_binding = (fun projectee -> (match (projectee) with
| Binding_fvar (_0) -> begin
_0
end))


let binder_of_eithervar : 'Auu____2454 'Auu____2455 . 'Auu____2454  ->  ('Auu____2454 * 'Auu____2455 FStar_Pervasives_Native.option) = (fun v1 -> ((v1), (FStar_Pervasives_Native.None)))

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
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_TypeChecker_Env.env; warn : Prims.bool; cache : cache_entry FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool; current_module_name : Prims.string}


let __proj__Mkenv_t__item__bindings : env_t  ->  binding Prims.list = (fun projectee -> (match (projectee) with
| {bindings = __fname__bindings; depth = __fname__depth; tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache; nolabels = __fname__nolabels; use_zfuel_name = __fname__use_zfuel_name; encode_non_total_function_typ = __fname__encode_non_total_function_typ; current_module_name = __fname__current_module_name} -> begin
__fname__bindings
end))


let __proj__Mkenv_t__item__depth : env_t  ->  Prims.int = (fun projectee -> (match (projectee) with
| {bindings = __fname__bindings; depth = __fname__depth; tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache; nolabels = __fname__nolabels; use_zfuel_name = __fname__use_zfuel_name; encode_non_total_function_typ = __fname__encode_non_total_function_typ; current_module_name = __fname__current_module_name} -> begin
__fname__depth
end))


let __proj__Mkenv_t__item__tcenv : env_t  ->  FStar_TypeChecker_Env.env = (fun projectee -> (match (projectee) with
| {bindings = __fname__bindings; depth = __fname__depth; tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache; nolabels = __fname__nolabels; use_zfuel_name = __fname__use_zfuel_name; encode_non_total_function_typ = __fname__encode_non_total_function_typ; current_module_name = __fname__current_module_name} -> begin
__fname__tcenv
end))


let __proj__Mkenv_t__item__warn : env_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {bindings = __fname__bindings; depth = __fname__depth; tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache; nolabels = __fname__nolabels; use_zfuel_name = __fname__use_zfuel_name; encode_non_total_function_typ = __fname__encode_non_total_function_typ; current_module_name = __fname__current_module_name} -> begin
__fname__warn
end))


let __proj__Mkenv_t__item__cache : env_t  ->  cache_entry FStar_Util.smap = (fun projectee -> (match (projectee) with
| {bindings = __fname__bindings; depth = __fname__depth; tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache; nolabels = __fname__nolabels; use_zfuel_name = __fname__use_zfuel_name; encode_non_total_function_typ = __fname__encode_non_total_function_typ; current_module_name = __fname__current_module_name} -> begin
__fname__cache
end))


let __proj__Mkenv_t__item__nolabels : env_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {bindings = __fname__bindings; depth = __fname__depth; tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache; nolabels = __fname__nolabels; use_zfuel_name = __fname__use_zfuel_name; encode_non_total_function_typ = __fname__encode_non_total_function_typ; current_module_name = __fname__current_module_name} -> begin
__fname__nolabels
end))


let __proj__Mkenv_t__item__use_zfuel_name : env_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {bindings = __fname__bindings; depth = __fname__depth; tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache; nolabels = __fname__nolabels; use_zfuel_name = __fname__use_zfuel_name; encode_non_total_function_typ = __fname__encode_non_total_function_typ; current_module_name = __fname__current_module_name} -> begin
__fname__use_zfuel_name
end))


let __proj__Mkenv_t__item__encode_non_total_function_typ : env_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {bindings = __fname__bindings; depth = __fname__depth; tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache; nolabels = __fname__nolabels; use_zfuel_name = __fname__use_zfuel_name; encode_non_total_function_typ = __fname__encode_non_total_function_typ; current_module_name = __fname__current_module_name} -> begin
__fname__encode_non_total_function_typ
end))


let __proj__Mkenv_t__item__current_module_name : env_t  ->  Prims.string = (fun projectee -> (match (projectee) with
| {bindings = __fname__bindings; depth = __fname__depth; tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache; nolabels = __fname__nolabels; use_zfuel_name = __fname__use_zfuel_name; encode_non_total_function_typ = __fname__encode_non_total_function_typ; current_module_name = __fname__current_module_name} -> begin
__fname__current_module_name
end))


let mk_cache_entry : 'Auu____2751 . 'Auu____2751  ->  Prims.string  ->  FStar_SMTEncoding_Term.sort Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  cache_entry = (fun env tsym cvar_sorts t_decls1 -> (

let names1 = (FStar_All.pipe_right t_decls1 (FStar_List.collect (fun uu___83_2785 -> (match (uu___83_2785) with
| FStar_SMTEncoding_Term.Assume (a) -> begin
(a.FStar_SMTEncoding_Term.assumption_name)::[]
end
| uu____2789 -> begin
[]
end))))
in {cache_symbol_name = tsym; cache_symbol_arg_sorts = cvar_sorts; cache_symbol_decls = t_decls1; cache_symbol_assumption_names = names1}))


let use_cache_entry : cache_entry  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun ce -> (FStar_SMTEncoding_Term.RetainAssumptions (ce.cache_symbol_assumption_names))::[])


let print_env : env_t  ->  Prims.string = (fun e -> (

let uu____2798 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun uu___84_2808 -> (match (uu___84_2808) with
| Binding_var (x, uu____2810) -> begin
(FStar_Syntax_Print.bv_to_string x)
end
| Binding_fvar (fvb) -> begin
(FStar_Syntax_Print.lid_to_string fvb.fvar_lid)
end))))
in (FStar_All.pipe_right uu____2798 (FStar_String.concat ", "))))


let lookup_binding : 'Auu____2817 . env_t  ->  (binding  ->  'Auu____2817 FStar_Pervasives_Native.option)  ->  'Auu____2817 FStar_Pervasives_Native.option = (fun env f -> (FStar_Util.find_map env.bindings f))


let caption_t : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.string FStar_Pervasives_Native.option = (fun env t -> (

let uu____2845 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____2845) with
| true -> begin
(

let uu____2848 = (FStar_Syntax_Print.term_to_string t)
in FStar_Pervasives_Native.Some (uu____2848))
end
| uu____2849 -> begin
FStar_Pervasives_Native.None
end)))


let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (

let xsym = (varops.fresh x)
in (

let uu____2861 = (FStar_SMTEncoding_Util.mkFreeV ((xsym), (s)))
in ((xsym), (uu____2861)))))


let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (Prims.strcat "@x" (Prims.string_of_int env.depth))
in (

let y = (FStar_SMTEncoding_Util.mkFreeV ((ysym), (FStar_SMTEncoding_Term.Term_sort)))
in ((ysym), (y), ((

let uu___107_2877 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = (env.depth + (Prims.parse_int "1")); tcenv = uu___107_2877.tcenv; warn = uu___107_2877.warn; cache = uu___107_2877.cache; nolabels = uu___107_2877.nolabels; use_zfuel_name = uu___107_2877.use_zfuel_name; encode_non_total_function_typ = uu___107_2877.encode_non_total_function_typ; current_module_name = uu___107_2877.current_module_name}))))))


let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let uu___108_2895 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = uu___108_2895.depth; tcenv = uu___108_2895.tcenv; warn = uu___108_2895.warn; cache = uu___108_2895.cache; nolabels = uu___108_2895.nolabels; use_zfuel_name = uu___108_2895.use_zfuel_name; encode_non_total_function_typ = uu___108_2895.encode_non_total_function_typ; current_module_name = uu___108_2895.current_module_name}))))))


let new_term_constant_from_string : env_t  ->  FStar_Syntax_Syntax.bv  ->  Prims.string  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x str -> (

let ysym = (varops.mk_unique str)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let uu___109_2916 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = uu___109_2916.depth; tcenv = uu___109_2916.tcenv; warn = uu___109_2916.warn; cache = uu___109_2916.cache; nolabels = uu___109_2916.nolabels; use_zfuel_name = uu___109_2916.use_zfuel_name; encode_non_total_function_typ = uu___109_2916.encode_non_total_function_typ; current_module_name = uu___109_2916.current_module_name}))))))


let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (

let uu___110_2926 = env
in {bindings = (Binding_var (((x), (t))))::env.bindings; depth = uu___110_2926.depth; tcenv = uu___110_2926.tcenv; warn = uu___110_2926.warn; cache = uu___110_2926.cache; nolabels = uu___110_2926.nolabels; use_zfuel_name = uu___110_2926.use_zfuel_name; encode_non_total_function_typ = uu___110_2926.encode_non_total_function_typ; current_module_name = uu___110_2926.current_module_name}))


let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let aux = (fun a' -> (lookup_binding env (fun uu___85_2950 -> (match (uu___85_2950) with
| Binding_var (b, t) when (FStar_Syntax_Syntax.bv_eq b a') -> begin
FStar_Pervasives_Native.Some (((b), (t)))
end
| uu____2963 -> begin
FStar_Pervasives_Native.None
end))))
in (

let uu____2968 = (aux a)
in (match (uu____2968) with
| FStar_Pervasives_Native.None -> begin
(

let a2 = (unmangle a)
in (

let uu____2980 = (aux a2)
in (match (uu____2980) with
| FStar_Pervasives_Native.None -> begin
(

let uu____2991 = (

let uu____2992 = (FStar_Syntax_Print.bv_to_string a2)
in (

let uu____2993 = (print_env env)
in (FStar_Util.format2 "Bound term variable not found (after unmangling): %s in environment: %s" uu____2992 uu____2993)))
in (failwith uu____2991))
end
| FStar_Pervasives_Native.Some (b, t) -> begin
t
end)))
end
| FStar_Pervasives_Native.Some (b, t) -> begin
t
end))))


let mk_fvb : FStar_Ident.lident  ->  Prims.string  ->  Prims.int  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  fvar_binding = (fun lid fname arity ftok fuel_partial_app -> {fvar_lid = lid; smt_arity = arity; smt_id = fname; smt_token = ftok; smt_fuel_partial_app = fuel_partial_app})


let new_term_constant_and_tok_from_lid : env_t  ->  FStar_Ident.lident  ->  Prims.int  ->  (Prims.string * Prims.string * env_t) = (fun env x arity -> (

let fname = (varops.new_fvar x)
in (

let ftok_name = (Prims.strcat fname "@tok")
in (

let ftok = (FStar_SMTEncoding_Util.mkApp ((ftok_name), ([])))
in (

let fvb = (mk_fvb x fname arity (FStar_Pervasives_Native.Some (ftok)) FStar_Pervasives_Native.None)
in ((fname), (ftok_name), ((

let uu___111_3051 = env
in {bindings = (Binding_fvar (fvb))::env.bindings; depth = uu___111_3051.depth; tcenv = uu___111_3051.tcenv; warn = uu___111_3051.warn; cache = uu___111_3051.cache; nolabels = uu___111_3051.nolabels; use_zfuel_name = uu___111_3051.use_zfuel_name; encode_non_total_function_typ = uu___111_3051.encode_non_total_function_typ; current_module_name = uu___111_3051.current_module_name}))))))))


let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  fvar_binding FStar_Pervasives_Native.option = (fun env a -> (lookup_binding env (fun uu___86_3062 -> (match (uu___86_3062) with
| Binding_fvar (fvb) when (FStar_Ident.lid_equals fvb.fvar_lid a) -> begin
FStar_Pervasives_Native.Some (fvb)
end
| uu____3066 -> begin
FStar_Pervasives_Native.None
end))))


let contains_name : env_t  ->  Prims.string  ->  Prims.bool = (fun env s -> (

let uu____3073 = (lookup_binding env (fun uu___87_3078 -> (match (uu___87_3078) with
| Binding_fvar (fvb) when (Prims.op_Equality fvb.fvar_lid.FStar_Ident.str s) -> begin
FStar_Pervasives_Native.Some (())
end
| uu____3082 -> begin
FStar_Pervasives_Native.None
end)))
in (FStar_All.pipe_right uu____3073 FStar_Option.isSome)))


let lookup_lid : env_t  ->  FStar_Ident.lident  ->  fvar_binding = (fun env a -> (

let uu____3091 = (try_lookup_lid env a)
in (match (uu____3091) with
| FStar_Pervasives_Native.None -> begin
(

let uu____3094 = (

let uu____3095 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" uu____3095))
in (failwith uu____3094))
end
| FStar_Pervasives_Native.Some (s) -> begin
s
end)))


let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  env_t = (fun env x arity fname ftok -> (

let fvb = (mk_fvb x fname arity ftok FStar_Pervasives_Native.None)
in (

let uu___112_3117 = env
in {bindings = (Binding_fvar (fvb))::env.bindings; depth = uu___112_3117.depth; tcenv = uu___112_3117.tcenv; warn = uu___112_3117.warn; cache = uu___112_3117.cache; nolabels = uu___112_3117.nolabels; use_zfuel_name = uu___112_3117.use_zfuel_name; encode_non_total_function_typ = uu___112_3117.encode_non_total_function_typ; current_module_name = uu___112_3117.current_module_name})))


let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (

let fvb = (lookup_lid env x)
in (

let t3 = (

let uu____3129 = (

let uu____3136 = (

let uu____3139 = (FStar_SMTEncoding_Util.mkApp (("ZFuel"), ([])))
in (uu____3139)::[])
in ((f), (uu____3136)))
in (FStar_SMTEncoding_Util.mkApp uu____3129))
in (

let fvb1 = (mk_fvb x fvb.smt_id fvb.smt_arity fvb.smt_token (FStar_Pervasives_Native.Some (t3)))
in (

let uu___113_3145 = env
in {bindings = (Binding_fvar (fvb1))::env.bindings; depth = uu___113_3145.depth; tcenv = uu___113_3145.tcenv; warn = uu___113_3145.warn; cache = uu___113_3145.cache; nolabels = uu___113_3145.nolabels; use_zfuel_name = uu___113_3145.use_zfuel_name; encode_non_total_function_typ = uu___113_3145.encode_non_total_function_typ; current_module_name = uu___113_3145.current_module_name})))))


let try_lookup_free_var : env_t  ->  FStar_Ident.lident  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun env l -> (

let uu____3154 = (try_lookup_lid env l)
in (match (uu____3154) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (fvb) -> begin
(match (fvb.smt_fuel_partial_app) with
| FStar_Pervasives_Native.Some (f) when env.use_zfuel_name -> begin
FStar_Pervasives_Native.Some (f)
end
| uu____3163 -> begin
(match (fvb.smt_token) with
| FStar_Pervasives_Native.Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (uu____3171, (fuel)::[]) -> begin
(

let uu____3175 = (

let uu____3176 = (

let uu____3177 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right uu____3177 FStar_Pervasives_Native.fst))
in (FStar_Util.starts_with uu____3176 "fuel"))
in (match (uu____3175) with
| true -> begin
(

let uu____3180 = (

let uu____3181 = (FStar_SMTEncoding_Util.mkFreeV ((fvb.smt_id), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_ApplyTF uu____3181 fuel))
in (FStar_All.pipe_left (fun _0_40 -> FStar_Pervasives_Native.Some (_0_40)) uu____3180))
end
| uu____3184 -> begin
FStar_Pervasives_Native.Some (t)
end))
end
| uu____3185 -> begin
FStar_Pervasives_Native.Some (t)
end)
end
| uu____3186 -> begin
FStar_Pervasives_Native.None
end)
end)
end)))


let lookup_free_var : env_t  ->  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let uu____3199 = (try_lookup_free_var env a.FStar_Syntax_Syntax.v)
in (match (uu____3199) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let uu____3203 = (

let uu____3204 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" uu____3204))
in (failwith uu____3203))
end)))


let lookup_free_var_name : env_t  ->  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t  ->  (Prims.string * Prims.int) = (fun env a -> (

let fvb = (lookup_lid env a.FStar_Syntax_Syntax.v)
in ((fvb.smt_id), (fvb.smt_arity))))


let lookup_free_var_sym : env_t  ->  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t  ->  (FStar_SMTEncoding_Term.op * FStar_SMTEncoding_Term.term Prims.list * Prims.int) = (fun env a -> (

let fvb = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (fvb.smt_fuel_partial_app) with
| FStar_Pervasives_Native.Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.freevars = uu____3249; FStar_SMTEncoding_Term.rng = uu____3250}) when env.use_zfuel_name -> begin
((g), (zf), ((fvb.smt_arity + (Prims.parse_int "1"))))
end
| uu____3265 -> begin
(match (fvb.smt_token) with
| FStar_Pervasives_Native.None -> begin
((FStar_SMTEncoding_Term.Var (fvb.smt_id)), ([]), (fvb.smt_arity))
end
| FStar_Pervasives_Native.Some (sym) -> begin
(match (sym.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, (fuel)::[]) -> begin
((g), ((fuel)::[]), ((fvb.smt_arity + (Prims.parse_int "1"))))
end
| uu____3293 -> begin
((FStar_SMTEncoding_Term.Var (fvb.smt_id)), ([]), (fvb.smt_arity))
end)
end)
end)))


let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun uu___88_3306 -> (match (uu___88_3306) with
| Binding_fvar (fvb) when (Prims.op_Equality fvb.smt_id nm) -> begin
fvb.smt_token
end
| uu____3310 -> begin
FStar_Pervasives_Native.None
end))))


let mkForall_fuel' : 'Auu____3314 . 'Auu____3314  ->  (FStar_SMTEncoding_Term.pat Prims.list Prims.list * FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (fun n1 uu____3332 -> (match (uu____3332) with
| (pats, vars, body) -> begin
(

let fallback = (fun uu____3357 -> (FStar_SMTEncoding_Util.mkForall ((pats), (vars), (body))))
in (

let uu____3362 = (FStar_Options.unthrottle_inductives ())
in (match (uu____3362) with
| true -> begin
(fallback ())
end
| uu____3363 -> begin
(

let uu____3364 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____3364) with
| (fsym, fterm) -> begin
(

let add_fuel1 = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Util.mkApp (("HasTypeFuel"), ((fterm)::args)))
end
| uu____3395 -> begin
p
end)))))
in (

let pats1 = (FStar_List.map add_fuel1 pats)
in (

let body1 = (match (body.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (guard)::(body')::[]) -> begin
(

let guard1 = (match (guard.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, guards) -> begin
(

let uu____3416 = (add_fuel1 guards)
in (FStar_SMTEncoding_Util.mk_and_l uu____3416))
end
| uu____3419 -> begin
(

let uu____3420 = (add_fuel1 ((guard)::[]))
in (FStar_All.pipe_right uu____3420 FStar_List.hd))
end)
in (FStar_SMTEncoding_Util.mkImp ((guard1), (body'))))
end
| uu____3425 -> begin
body
end)
in (

let vars1 = (((fsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars
in (FStar_SMTEncoding_Util.mkForall ((pats1), (vars1), (body1)))))))
end))
end)))
end))


let mkForall_fuel : (FStar_SMTEncoding_Term.pat Prims.list Prims.list * FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (mkForall_fuel' (Prims.parse_int "1"))


let head_normal : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let t1 = (FStar_Syntax_Util.unmeta t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____3466) -> begin
true
end
| FStar_Syntax_Syntax.Tm_refine (uu____3479) -> begin
true
end
| FStar_Syntax_Syntax.Tm_bvar (uu____3486) -> begin
true
end
| FStar_Syntax_Syntax.Tm_uvar (uu____3487) -> begin
true
end
| FStar_Syntax_Syntax.Tm_abs (uu____3504) -> begin
true
end
| FStar_Syntax_Syntax.Tm_constant (uu____3521) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____3523 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____3523 FStar_Option.isNone))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____3541; FStar_Syntax_Syntax.vars = uu____3542}, uu____3543) -> begin
(

let uu____3564 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____3564 FStar_Option.isNone))
end
| uu____3581 -> begin
false
end)))


let head_redex : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let uu____3588 = (

let uu____3589 = (FStar_Syntax_Util.un_uinst t)
in uu____3589.FStar_Syntax_Syntax.n)
in (match (uu____3588) with
| FStar_Syntax_Syntax.Tm_abs (uu____3592, uu____3593, FStar_Pervasives_Native.Some (rc)) -> begin
(((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_Tot_lid) || (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_GTot_lid)) || (FStar_List.existsb (fun uu___89_3614 -> (match (uu___89_3614) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____3615 -> begin
false
end)) rc.FStar_Syntax_Syntax.residual_flags))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____3617 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____3617 FStar_Option.isSome))
end
| uu____3634 -> begin
false
end)))


let whnf : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____3641 = (head_normal env t)
in (match (uu____3641) with
| true -> begin
t
end
| uu____3642 -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
end)))


let norm : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t))


let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____3652 = (

let uu____3653 = (FStar_Syntax_Syntax.null_binder t)
in (uu____3653)::[])
in (

let uu____3654 = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Util.abs uu____3652 uu____3654 FStar_Pervasives_Native.None))))


let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((FStar_Pervasives_Native.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(

let uu____3692 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out uu____3692))
end
| s -> begin
(

let uu____3703 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Util.mk_ApplyTT out uu____3703))
end)) e)))


let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)))


let raise_arity_mismatch : 'Auu____3721 . Prims.string  ->  Prims.int  ->  Prims.int  ->  FStar_Range.range  ->  'Auu____3721 = (fun head1 arity n_args rng -> (

let uu____3738 = (

let uu____3743 = (

let uu____3744 = (FStar_Util.string_of_int arity)
in (

let uu____3745 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format3 "Head symbol %s expects at least %s arguments; got only %s" head1 uu____3744 uu____3745)))
in ((FStar_Errors.Fatal_SMTEncodingArityMismatch), (uu____3743)))
in (FStar_Errors.raise_error uu____3738 rng)))


let maybe_curry_app : FStar_Range.range  ->  FStar_SMTEncoding_Term.op  ->  Prims.int  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun rng head1 arity args -> (

let n_args = (FStar_List.length args)
in (match ((Prims.op_Equality n_args arity)) with
| true -> begin
(FStar_SMTEncoding_Util.mkApp' ((head1), (args)))
end
| uu____3769 -> begin
(match ((n_args > arity)) with
| true -> begin
(

let uu____3776 = (FStar_Util.first_N arity args)
in (match (uu____3776) with
| (args1, rest) -> begin
(

let head2 = (FStar_SMTEncoding_Util.mkApp' ((head1), (args1)))
in (mk_Apply_args head2 rest))
end))
end
| uu____3798 -> begin
(

let uu____3799 = (FStar_SMTEncoding_Term.op_to_string head1)
in (raise_arity_mismatch uu____3799 arity n_args rng))
end)
end)))


let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun uu___90_3806 -> (match (uu___90_3806) with
| FStar_SMTEncoding_Term.Var ("ApplyTT") -> begin
true
end
| FStar_SMTEncoding_Term.Var ("ApplyTF") -> begin
true
end
| uu____3807 -> begin
false
end))


let is_an_eta_expansion : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun env vars body -> (

let rec check_partial_applications = (fun t xs -> (match (((t.FStar_SMTEncoding_Term.tm), (xs))) with
| (FStar_SMTEncoding_Term.App (app, (f)::({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.freevars = uu____3843; FStar_SMTEncoding_Term.rng = uu____3844})::[]), (x)::xs1) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(check_partial_applications f xs1)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), uu____3867) -> begin
(

let uu____3876 = ((Prims.op_Equality (FStar_List.length args) (FStar_List.length xs)) && (FStar_List.forall2 (fun a v1 -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v1)
end
| uu____3887 -> begin
false
end)) args (FStar_List.rev xs)))
in (match (uu____3876) with
| true -> begin
(tok_of_name env f)
end
| uu____3890 -> begin
FStar_Pervasives_Native.None
end))
end
| (uu____3891, []) -> begin
(

let fvs = (FStar_SMTEncoding_Term.free_variables t)
in (

let uu____3895 = (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (

let uu____3899 = (FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)
in (not (uu____3899))))))
in (match (uu____3895) with
| true -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____3902 -> begin
FStar_Pervasives_Native.None
end)))
end
| uu____3903 -> begin
FStar_Pervasives_Native.None
end))
in (check_partial_applications body (FStar_List.rev vars))))


type label =
(FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range)


type labels =
label Prims.list

type pattern =
{pat_vars : (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.fv) Prims.list; pat_term : Prims.unit  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t); guard : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term; projections : FStar_SMTEncoding_Term.term  ->  (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) Prims.list}


let __proj__Mkpattern__item__pat_vars : pattern  ->  (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.fv) Prims.list = (fun projectee -> (match (projectee) with
| {pat_vars = __fname__pat_vars; pat_term = __fname__pat_term; guard = __fname__guard; projections = __fname__projections} -> begin
__fname__pat_vars
end))


let __proj__Mkpattern__item__pat_term : pattern  ->  Prims.unit  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun projectee -> (match (projectee) with
| {pat_vars = __fname__pat_vars; pat_term = __fname__pat_term; guard = __fname__guard; projections = __fname__projections} -> begin
__fname__pat_term
end))


let __proj__Mkpattern__item__guard : pattern  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (fun projectee -> (match (projectee) with
| {pat_vars = __fname__pat_vars; pat_term = __fname__pat_term; guard = __fname__guard; projections = __fname__projections} -> begin
__fname__guard
end))


let __proj__Mkpattern__item__projections : pattern  ->  FStar_SMTEncoding_Term.term  ->  (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) Prims.list = (fun projectee -> (match (projectee) with
| {pat_vars = __fname__pat_vars; pat_term = __fname__pat_term; guard = __fname__guard; projections = __fname__projections} -> begin
__fname__projections
end))

exception Let_rec_unencodeable


let uu___is_Let_rec_unencodeable : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Let_rec_unencodeable -> begin
true
end
| uu____4125 -> begin
false
end))

exception Inner_let_rec


let uu___is_Inner_let_rec : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Inner_let_rec -> begin
true
end
| uu____4129 -> begin
false
end))


let as_function_typ : env_t  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (

let rec aux = (fun norm1 t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____4148) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_refine (uu____4161) -> begin
(

let uu____4168 = (FStar_Syntax_Util.unrefine t1)
in (aux true uu____4168))
end
| uu____4169 -> begin
(match (norm1) with
| true -> begin
(

let uu____4170 = (whnf env t1)
in (aux false uu____4170))
end
| uu____4171 -> begin
(

let uu____4172 = (

let uu____4173 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (

let uu____4174 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" uu____4173 uu____4174)))
in (failwith uu____4172))
end)
end)))
in (aux true t0)))


let rec curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun k -> (

let k1 = (FStar_Syntax_Subst.compress k)
in (match (k1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| FStar_Syntax_Syntax.Tm_refine (bv, uu____4206) -> begin
(curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort)
end
| uu____4211 -> begin
(

let uu____4212 = (FStar_Syntax_Syntax.mk_Total k1)
in (([]), (uu____4212)))
end)))


let is_arithmetic_primitive : 'Auu____4226 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  'Auu____4226 Prims.list  ->  Prims.bool = (fun head1 args -> (match (((head1.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____4246)::(uu____4247)::[]) -> begin
(((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Addition) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Subtraction)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Multiply)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Division)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Modulus))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____4251)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus)
end
| uu____4254 -> begin
false
end))


let isInteger : FStar_Syntax_Syntax.term'  ->  Prims.bool = (fun tm -> (match (tm) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (n1, FStar_Pervasives_Native.None)) -> begin
true
end
| uu____4275 -> begin
false
end))


let getInteger : FStar_Syntax_Syntax.term'  ->  Prims.int = (fun tm -> (match (tm) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (n1, FStar_Pervasives_Native.None)) -> begin
(FStar_Util.int_of_string n1)
end
| uu____4290 -> begin
(failwith "Expected an Integer term")
end))


let is_BitVector_primitive : 'Auu____4294 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____4294) Prims.list  ->  Prims.bool = (fun head1 args -> (match (((head1.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((sz_arg, uu____4333))::(uu____4334)::(uu____4335)::[]) -> begin
((((((((((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_and_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_xor_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_or_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_add_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_sub_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_shift_left_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_shift_right_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_udiv_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_mod_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_uext_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_mul_lid)) && (isInteger sz_arg.FStar_Syntax_Syntax.n))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((sz_arg, uu____4386))::(uu____4387)::[]) -> begin
(((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_to_nat_lid)) && (isInteger sz_arg.FStar_Syntax_Syntax.n))
end
| uu____4424 -> begin
false
end))


let rec encode_const : FStar_Const.sconst  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list) = (fun c env -> (match (c) with
| FStar_Const.Const_unit -> begin
((FStar_SMTEncoding_Term.mk_Term_unit), ([]))
end
| FStar_Const.Const_bool (true) -> begin
(

let uu____4643 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue)
in ((uu____4643), ([])))
end
| FStar_Const.Const_bool (false) -> begin
(

let uu____4646 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse)
in ((uu____4646), ([])))
end
| FStar_Const.Const_char (c1) -> begin
(

let uu____4650 = (

let uu____4651 = (

let uu____4658 = (

let uu____4661 = (

let uu____4662 = (FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c1))
in (FStar_SMTEncoding_Term.boxInt uu____4662))
in (uu____4661)::[])
in (("FStar.Char.__char_of_int"), (uu____4658)))
in (FStar_SMTEncoding_Util.mkApp uu____4651))
in ((uu____4650), ([])))
end
| FStar_Const.Const_int (i, FStar_Pervasives_Native.None) -> begin
(

let uu____4678 = (

let uu____4679 = (FStar_SMTEncoding_Util.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt uu____4679))
in ((uu____4678), ([])))
end
| FStar_Const.Const_int (repr, FStar_Pervasives_Native.Some (sw)) -> begin
(

let syntax_term = (FStar_ToSyntax_ToSyntax.desugar_machine_integer env.tcenv.FStar_TypeChecker_Env.dsenv repr sw FStar_Range.dummyRange)
in (encode_term syntax_term env))
end
| FStar_Const.Const_string (s, uu____4700) -> begin
(

let uu____4701 = (varops.string_const s)
in ((uu____4701), ([])))
end
| FStar_Const.Const_range (uu____4704) -> begin
(

let uu____4705 = (FStar_SMTEncoding_Term.mk_Range_const ())
in ((uu____4705), ([])))
end
| FStar_Const.Const_effect -> begin
((FStar_SMTEncoding_Term.mk_Term_type), ([]))
end
| c1 -> begin
(

let uu____4711 = (

let uu____4712 = (FStar_Syntax_Print.const_to_string c1)
in (FStar_Util.format1 "Unhandled constant: %s" uu____4712))
in (failwith uu____4711))
end))
and encode_binders : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> ((

let uu____4741 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____4741) with
| true -> begin
(

let uu____4742 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" uu____4742))
end
| uu____4743 -> begin
()
end));
(

let uu____4744 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____4828 b -> (match (uu____4828) with
| (vars, guards, env1, decls, names1) -> begin
(

let uu____4907 = (

let x = (unmangle (FStar_Pervasives_Native.fst b))
in (

let uu____4923 = (gen_term_var env1 x)
in (match (uu____4923) with
| (xxsym, xx, env') -> begin
(

let uu____4947 = (

let uu____4952 = (norm env1 x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt uu____4952 env1 xx))
in (match (uu____4947) with
| (guard_x_t, decls') -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (guard_x_t), (env'), (decls'), (x))
end))
end)))
in (match (uu____4907) with
| (v1, g, env2, decls', n1) -> begin
(((v1)::vars), ((g)::guards), (env2), ((FStar_List.append decls decls')), ((n1)::names1))
end))
end)) (([]), ([]), (env), ([]), ([]))))
in (match (uu____4744) with
| (vars, guards, env1, decls, names1) -> begin
(((FStar_List.rev vars)), ((FStar_List.rev guards)), (env1), (decls), ((FStar_List.rev names1)))
end));
))
and encode_term_pred : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let uu____5111 = (encode_term t env)
in (match (uu____5111) with
| (t1, decls) -> begin
(

let uu____5122 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1)
in ((uu____5122), (decls)))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let uu____5133 = (encode_term t env)
in (match (uu____5133) with
| (t1, decls) -> begin
(match (fuel_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5148 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t1)
in ((uu____5148), (decls)))
end
| FStar_Pervasives_Native.Some (f) -> begin
(

let uu____5150 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1)
in ((uu____5150), (decls)))
end)
end)))
and encode_arith_term : env_t  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.args  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun env head1 args_e -> (

let uu____5156 = (encode_args args_e env)
in (match (uu____5156) with
| (arg_tms, decls) -> begin
(

let head_fv = (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____5175 -> begin
(failwith "Impossible")
end)
in (

let unary = (fun arg_tms1 -> (

let uu____5184 = (FStar_List.hd arg_tms1)
in (FStar_SMTEncoding_Term.unboxInt uu____5184)))
in (

let binary = (fun arg_tms1 -> (

let uu____5197 = (

let uu____5198 = (FStar_List.hd arg_tms1)
in (FStar_SMTEncoding_Term.unboxInt uu____5198))
in (

let uu____5199 = (

let uu____5200 = (

let uu____5201 = (FStar_List.tl arg_tms1)
in (FStar_List.hd uu____5201))
in (FStar_SMTEncoding_Term.unboxInt uu____5200))
in ((uu____5197), (uu____5199)))))
in (

let mk_default = (fun uu____5207 -> (

let uu____5208 = (lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name)
in (match (uu____5208) with
| (fname, fuel_args, arity) -> begin
(

let args = (FStar_List.append fuel_args arg_tms)
in (maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity args))
end)))
in (

let mk_l = (fun a op mk_args ts -> (

let uu____5258 = (FStar_Options.smtencoding_l_arith_native ())
in (match (uu____5258) with
| true -> begin
(

let uu____5259 = (

let uu____5260 = (mk_args ts)
in (op uu____5260))
in (FStar_All.pipe_right uu____5259 FStar_SMTEncoding_Term.boxInt))
end
| uu____5261 -> begin
(mk_default ())
end)))
in (

let mk_nl = (fun nm op ts -> (

let uu____5289 = (FStar_Options.smtencoding_nl_arith_wrapped ())
in (match (uu____5289) with
| true -> begin
(

let uu____5290 = (binary ts)
in (match (uu____5290) with
| (t1, t2) -> begin
(

let uu____5297 = (FStar_SMTEncoding_Util.mkApp ((nm), ((t1)::(t2)::[])))
in (FStar_All.pipe_right uu____5297 FStar_SMTEncoding_Term.boxInt))
end))
end
| uu____5300 -> begin
(

let uu____5301 = (FStar_Options.smtencoding_nl_arith_native ())
in (match (uu____5301) with
| true -> begin
(

let uu____5302 = (op (binary ts))
in (FStar_All.pipe_right uu____5302 FStar_SMTEncoding_Term.boxInt))
end
| uu____5303 -> begin
(mk_default ())
end))
end)))
in (

let add1 = (mk_l () (fun a415 -> ((Obj.magic (FStar_SMTEncoding_Util.mkAdd)) a415)) (fun a416 -> ((Obj.magic (binary)) a416)))
in (

let sub1 = (mk_l () (fun a417 -> ((Obj.magic (FStar_SMTEncoding_Util.mkSub)) a417)) (fun a418 -> ((Obj.magic (binary)) a418)))
in (

let minus = (mk_l () (fun a419 -> ((Obj.magic (FStar_SMTEncoding_Util.mkMinus)) a419)) (fun a420 -> ((Obj.magic (unary)) a420)))
in (

let mul1 = (mk_nl "_mul" FStar_SMTEncoding_Util.mkMul)
in (

let div1 = (mk_nl "_div" FStar_SMTEncoding_Util.mkDiv)
in (

let modulus = (mk_nl "_mod" FStar_SMTEncoding_Util.mkMod)
in (

let ops = (((FStar_Parser_Const.op_Addition), (add1)))::(((FStar_Parser_Const.op_Subtraction), (sub1)))::(((FStar_Parser_Const.op_Multiply), (mul1)))::(((FStar_Parser_Const.op_Division), (div1)))::(((FStar_Parser_Const.op_Modulus), (modulus)))::(((FStar_Parser_Const.op_Minus), (minus)))::[]
in (

let uu____5425 = (

let uu____5434 = (FStar_List.tryFind (fun uu____5456 -> (match (uu____5456) with
| (l, uu____5466) -> begin
(FStar_Syntax_Syntax.fv_eq_lid head_fv l)
end)) ops)
in (FStar_All.pipe_right uu____5434 FStar_Util.must))
in (match (uu____5425) with
| (uu____5505, op) -> begin
(

let uu____5515 = (op arg_tms)
in ((uu____5515), (decls)))
end)))))))))))))))
end)))
and encode_BitVector_term : env_t  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.arg Prims.list  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list) = (fun env head1 args_e -> (

let uu____5523 = (FStar_List.hd args_e)
in (match (uu____5523) with
| (tm_sz, uu____5531) -> begin
(

let sz = (getInteger tm_sz.FStar_Syntax_Syntax.n)
in (

let sz_key = (FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz))
in (

let sz_decls = (

let uu____5541 = (FStar_Util.smap_try_find env.cache sz_key)
in (match (uu____5541) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
[]
end
| FStar_Pervasives_Native.None -> begin
(

let t_decls1 = (FStar_SMTEncoding_Term.mkBvConstructor sz)
in ((

let uu____5549 = (mk_cache_entry env "" [] [])
in (FStar_Util.smap_add env.cache sz_key uu____5549));
t_decls1;
))
end))
in (

let uu____5550 = (match (((head1.FStar_Syntax_Syntax.n), (args_e))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____5570)::((sz_arg, uu____5572))::(uu____5573)::[]) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_uext_lid) && (isInteger sz_arg.FStar_Syntax_Syntax.n)) -> begin
(

let uu____5622 = (

let uu____5625 = (FStar_List.tail args_e)
in (FStar_List.tail uu____5625))
in (

let uu____5628 = (

let uu____5631 = (getInteger sz_arg.FStar_Syntax_Syntax.n)
in FStar_Pervasives_Native.Some (uu____5631))
in ((uu____5622), (uu____5628))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____5637)::((sz_arg, uu____5639))::(uu____5640)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_uext_lid) -> begin
(

let uu____5689 = (

let uu____5690 = (FStar_Syntax_Print.term_to_string sz_arg)
in (FStar_Util.format1 "Not a constant bitvector extend size: %s" uu____5690))
in (failwith uu____5689))
end
| uu____5699 -> begin
(

let uu____5706 = (FStar_List.tail args_e)
in ((uu____5706), (FStar_Pervasives_Native.None)))
end)
in (match (uu____5550) with
| (arg_tms, ext_sz) -> begin
(

let uu____5729 = (encode_args arg_tms env)
in (match (uu____5729) with
| (arg_tms1, decls) -> begin
(

let head_fv = (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____5750 -> begin
(failwith "Impossible")
end)
in (

let unary = (fun arg_tms2 -> (

let uu____5759 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____5759)))
in (

let unary_arith = (fun arg_tms2 -> (

let uu____5768 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxInt uu____5768)))
in (

let binary = (fun arg_tms2 -> (

let uu____5781 = (

let uu____5782 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____5782))
in (

let uu____5783 = (

let uu____5784 = (

let uu____5785 = (FStar_List.tl arg_tms2)
in (FStar_List.hd uu____5785))
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____5784))
in ((uu____5781), (uu____5783)))))
in (

let binary_arith = (fun arg_tms2 -> (

let uu____5800 = (

let uu____5801 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____5801))
in (

let uu____5802 = (

let uu____5803 = (

let uu____5804 = (FStar_List.tl arg_tms2)
in (FStar_List.hd uu____5804))
in (FStar_SMTEncoding_Term.unboxInt uu____5803))
in ((uu____5800), (uu____5802)))))
in (

let mk_bv = (fun a op mk_args resBox ts -> (

let uu____5846 = (

let uu____5847 = (mk_args ts)
in (op uu____5847))
in (FStar_All.pipe_right uu____5846 resBox)))
in (

let bv_and = (mk_bv () (fun a421 -> ((Obj.magic (FStar_SMTEncoding_Util.mkBvAnd)) a421)) (fun a422 -> ((Obj.magic (binary)) a422)) (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_xor = (mk_bv () (fun a423 -> ((Obj.magic (FStar_SMTEncoding_Util.mkBvXor)) a423)) (fun a424 -> ((Obj.magic (binary)) a424)) (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_or = (mk_bv () (fun a425 -> ((Obj.magic (FStar_SMTEncoding_Util.mkBvOr)) a425)) (fun a426 -> ((Obj.magic (binary)) a426)) (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_add = (mk_bv () (fun a427 -> ((Obj.magic (FStar_SMTEncoding_Util.mkBvAdd)) a427)) (fun a428 -> ((Obj.magic (binary)) a428)) (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_sub = (mk_bv () (fun a429 -> ((Obj.magic (FStar_SMTEncoding_Util.mkBvSub)) a429)) (fun a430 -> ((Obj.magic (binary)) a430)) (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_shl = (mk_bv () (fun a431 -> ((Obj.magic ((FStar_SMTEncoding_Util.mkBvShl sz))) a431)) (fun a432 -> ((Obj.magic (binary_arith)) a432)) (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_shr = (mk_bv () (fun a433 -> ((Obj.magic ((FStar_SMTEncoding_Util.mkBvShr sz))) a433)) (fun a434 -> ((Obj.magic (binary_arith)) a434)) (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_udiv = (mk_bv () (fun a435 -> ((Obj.magic ((FStar_SMTEncoding_Util.mkBvUdiv sz))) a435)) (fun a436 -> ((Obj.magic (binary_arith)) a436)) (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_mod = (mk_bv () (fun a437 -> ((Obj.magic ((FStar_SMTEncoding_Util.mkBvMod sz))) a437)) (fun a438 -> ((Obj.magic (binary_arith)) a438)) (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_mul = (mk_bv () (fun a439 -> ((Obj.magic ((FStar_SMTEncoding_Util.mkBvMul sz))) a439)) (fun a440 -> ((Obj.magic (binary_arith)) a440)) (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_ult = (mk_bv () (fun a441 -> ((Obj.magic (FStar_SMTEncoding_Util.mkBvUlt)) a441)) (fun a442 -> ((Obj.magic (binary)) a442)) FStar_SMTEncoding_Term.boxBool)
in (

let bv_uext = (fun arg_tms2 -> (

let uu____5911 = (

let uu____5914 = (match (ext_sz) with
| FStar_Pervasives_Native.Some (x) -> begin
x
end
| FStar_Pervasives_Native.None -> begin
(failwith "impossible")
end)
in (FStar_SMTEncoding_Util.mkBvUext uu____5914))
in (

let uu____5916 = (

let uu____5919 = (

let uu____5920 = (match (ext_sz) with
| FStar_Pervasives_Native.Some (x) -> begin
x
end
| FStar_Pervasives_Native.None -> begin
(failwith "impossible")
end)
in (sz + uu____5920))
in (FStar_SMTEncoding_Term.boxBitVec uu____5919))
in (mk_bv () (fun a443 -> ((Obj.magic (uu____5911)) a443)) (fun a444 -> ((Obj.magic (unary)) a444)) uu____5916 arg_tms2))))
in (

let to_int1 = (mk_bv () (fun a445 -> ((Obj.magic (FStar_SMTEncoding_Util.mkBvToNat)) a445)) (fun a446 -> ((Obj.magic (unary)) a446)) FStar_SMTEncoding_Term.boxInt)
in (

let bv_to = (mk_bv () (fun a447 -> ((Obj.magic ((FStar_SMTEncoding_Util.mkNatToBv sz))) a447)) (fun a448 -> ((Obj.magic (unary_arith)) a448)) (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let ops = (((FStar_Parser_Const.bv_and_lid), (bv_and)))::(((FStar_Parser_Const.bv_xor_lid), (bv_xor)))::(((FStar_Parser_Const.bv_or_lid), (bv_or)))::(((FStar_Parser_Const.bv_add_lid), (bv_add)))::(((FStar_Parser_Const.bv_sub_lid), (bv_sub)))::(((FStar_Parser_Const.bv_shift_left_lid), (bv_shl)))::(((FStar_Parser_Const.bv_shift_right_lid), (bv_shr)))::(((FStar_Parser_Const.bv_udiv_lid), (bv_udiv)))::(((FStar_Parser_Const.bv_mod_lid), (bv_mod)))::(((FStar_Parser_Const.bv_mul_lid), (bv_mul)))::(((FStar_Parser_Const.bv_ult_lid), (bv_ult)))::(((FStar_Parser_Const.bv_uext_lid), (bv_uext)))::(((FStar_Parser_Const.bv_to_nat_lid), (to_int1)))::(((FStar_Parser_Const.nat_to_bv_lid), (bv_to)))::[]
in (

let uu____6119 = (

let uu____6128 = (FStar_List.tryFind (fun uu____6150 -> (match (uu____6150) with
| (l, uu____6160) -> begin
(FStar_Syntax_Syntax.fv_eq_lid head_fv l)
end)) ops)
in (FStar_All.pipe_right uu____6128 FStar_Util.must))
in (match (uu____6119) with
| (uu____6201, op) -> begin
(

let uu____6211 = (op arg_tms1)
in ((uu____6211), ((FStar_List.append sz_decls decls))))
end)))))))))))))))))))))))
end))
end)))))
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let t0 = (FStar_Syntax_Subst.compress t)
in ((

let uu____6222 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____6222) with
| true -> begin
(

let uu____6223 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____6224 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____6225 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" uu____6223 uu____6224 uu____6225))))
end
| uu____6226 -> begin
()
end));
(match (t0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____6231) -> begin
(

let uu____6256 = (

let uu____6257 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____6258 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____6259 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____6260 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6257 uu____6258 uu____6259 uu____6260)))))
in (failwith uu____6256))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____6265 = (

let uu____6266 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____6267 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____6268 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____6269 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6266 uu____6267 uu____6268 uu____6269)))))
in (failwith uu____6265))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____6275 = (FStar_Syntax_Util.unfold_lazy i)
in (encode_term uu____6275 env))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____6277 = (

let uu____6278 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" uu____6278))
in (failwith uu____6277))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, (k, uu____6285), uu____6286) -> begin
(

let uu____6335 = (match (k) with
| FStar_Util.Inl (t2) -> begin
(FStar_Syntax_Util.is_unit t2)
end
| uu____6343 -> begin
false
end)
in (match (uu____6335) with
| true -> begin
((FStar_SMTEncoding_Term.mk_Term_unit), ([]))
end
| uu____6358 -> begin
(encode_term t1 env)
end))
end
| FStar_Syntax_Syntax.Tm_quoted (qt, uu____6360) -> begin
(

let tv = (

let uu____6366 = (FStar_Reflection_Basic.inspect_ln qt)
in (FStar_Reflection_Embeddings.embed_term_view t.FStar_Syntax_Syntax.pos uu____6366))
in (

let t1 = (

let uu____6370 = (

let uu____6379 = (FStar_Syntax_Syntax.as_arg tv)
in (uu____6379)::[])
in (FStar_Syntax_Util.mk_app (FStar_Reflection_Data.refl_constant_term FStar_Reflection_Data.fstar_refl_pack_ln) uu____6370))
in (encode_term t1 env)))
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____6381) -> begin
(encode_term t1 env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t1 = (lookup_term_var env x)
in ((t1), ([])))
end
| FStar_Syntax_Syntax.Tm_fvar (v1) -> begin
(

let uu____6391 = (lookup_free_var env v1.FStar_Syntax_Syntax.fv_name)
in ((uu____6391), ([])))
end
| FStar_Syntax_Syntax.Tm_type (uu____6394) -> begin
((FStar_SMTEncoding_Term.mk_Term_type), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____6398) -> begin
(encode_term t1 env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(encode_const c env)
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let module_name = env.current_module_name
in (

let uu____6423 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____6423) with
| (binders1, res) -> begin
(

let uu____6434 = ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res))
in (match (uu____6434) with
| true -> begin
(

let uu____6439 = (encode_binders FStar_Pervasives_Native.None binders1 env)
in (match (uu____6439) with
| (vars, guards, env', decls, uu____6464) -> begin
(

let fsym = (

let uu____6482 = (varops.fresh "f")
in ((uu____6482), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV fsym)
in (

let app = (mk_Apply f vars)
in (

let uu____6485 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post (

let uu___114_6494 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___114_6494.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___114_6494.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___114_6494.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___114_6494.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___114_6494.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___114_6494.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___114_6494.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___114_6494.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___114_6494.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___114_6494.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___114_6494.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___114_6494.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___114_6494.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___114_6494.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___114_6494.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___114_6494.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___114_6494.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___114_6494.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___114_6494.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___114_6494.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___114_6494.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___114_6494.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___114_6494.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___114_6494.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___114_6494.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___114_6494.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___114_6494.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___114_6494.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___114_6494.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___114_6494.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___114_6494.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___114_6494.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___114_6494.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___114_6494.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___114_6494.FStar_TypeChecker_Env.dep_graph}) res)
in (match (uu____6485) with
| (pre_opt, res_t) -> begin
(

let uu____6505 = (encode_term_pred FStar_Pervasives_Native.None res_t env' app)
in (match (uu____6505) with
| (res_pred, decls') -> begin
(

let uu____6516 = (match (pre_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____6529 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____6529), ([])))
end
| FStar_Pervasives_Native.Some (pre) -> begin
(

let uu____6533 = (encode_formula pre env')
in (match (uu____6533) with
| (guard, decls0) -> begin
(

let uu____6546 = (FStar_SMTEncoding_Util.mk_and_l ((guard)::guards))
in ((uu____6546), (decls0)))
end))
end)
in (match (uu____6516) with
| (guards1, guard_decls) -> begin
(

let t_interp = (

let uu____6558 = (

let uu____6569 = (FStar_SMTEncoding_Util.mkImp ((guards1), (res_pred)))
in ((((app)::[])::[]), (vars), (uu____6569)))
in (FStar_SMTEncoding_Util.mkForall uu____6558))
in (

let cvars = (

let uu____6587 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right uu____6587 (FStar_List.filter (fun uu____6601 -> (match (uu____6601) with
| (x, uu____6607) -> begin
(Prims.op_disEquality x (FStar_Pervasives_Native.fst fsym))
end)))))
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), ((fsym)::cvars), (t_interp)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____6626 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____6626) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
(

let uu____6634 = (

let uu____6635 = (

let uu____6642 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((cache_entry.cache_symbol_name), (uu____6642)))
in (FStar_SMTEncoding_Util.mkApp uu____6635))
in ((uu____6634), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append guard_decls (use_cache_entry cache_entry)))))))
end
| FStar_Pervasives_Native.None -> begin
(

let tsym = (

let uu____6662 = (

let uu____6663 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_arrow_" uu____6663))
in (varops.mk_unique uu____6662))
in (

let cvar_sorts = (FStar_List.map FStar_Pervasives_Native.snd cvars)
in (

let caption = (

let uu____6674 = (FStar_Options.log_queries ())
in (match (uu____6674) with
| true -> begin
(

let uu____6677 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in FStar_Pervasives_Native.Some (uu____6677))
end
| uu____6678 -> begin
FStar_Pervasives_Native.None
end))
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (caption)))
in (

let t1 = (

let uu____6685 = (

let uu____6692 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((tsym), (uu____6692)))
in (FStar_SMTEncoding_Util.mkApp uu____6685))
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t1 FStar_SMTEncoding_Term.mk_Term_type)
in (

let k_assumption = (

let a_name = (Prims.strcat "kinding_" tsym)
in (

let uu____6704 = (

let uu____6711 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((uu____6711), (FStar_Pervasives_Native.Some (a_name)), (a_name)))
in (FStar_SMTEncoding_Util.mkAssume uu____6704)))
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t1)
in (

let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t1)
in (

let pre_typing = (

let a_name = (Prims.strcat "pre_typing_" tsym)
in (

let uu____6732 = (

let uu____6739 = (

let uu____6740 = (

let uu____6751 = (

let uu____6752 = (

let uu____6757 = (

let uu____6758 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____6758))
in ((f_has_t), (uu____6757)))
in (FStar_SMTEncoding_Util.mkImp uu____6752))
in ((((f_has_t)::[])::[]), ((fsym)::cvars), (uu____6751)))
in (mkForall_fuel uu____6740))
in ((uu____6739), (FStar_Pervasives_Native.Some ("pre-typing for functions")), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____6732)))
in (

let t_interp1 = (

let a_name = (Prims.strcat "interpretation_" tsym)
in (

let uu____6781 = (

let uu____6788 = (

let uu____6789 = (

let uu____6800 = (FStar_SMTEncoding_Util.mkIff ((f_has_t_z), (t_interp)))
in ((((f_has_t_z)::[])::[]), ((fsym)::cvars), (uu____6800)))
in (FStar_SMTEncoding_Util.mkForall uu____6789))
in ((uu____6788), (FStar_Pervasives_Native.Some (a_name)), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____6781)))
in (

let t_decls1 = (FStar_List.append ((tdecl)::decls) (FStar_List.append decls' (FStar_List.append guard_decls ((k_assumption)::(pre_typing)::(t_interp1)::[]))))
in ((

let uu____6825 = (mk_cache_entry env tsym cvar_sorts t_decls1)
in (FStar_Util.smap_add env.cache tkey_hash uu____6825));
((t1), (t_decls1));
)))))))))))))
end))))))
end))
end))
end)))))
end))
end
| uu____6828 -> begin
(

let tsym = (varops.fresh "Non_total_Tm_arrow")
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let t1 = (FStar_SMTEncoding_Util.mkApp ((tsym), ([])))
in (

let t_kinding = (

let a_name = (Prims.strcat "non_total_function_typing_" tsym)
in (

let uu____6840 = (

let uu____6847 = (FStar_SMTEncoding_Term.mk_HasType t1 FStar_SMTEncoding_Term.mk_Term_type)
in ((uu____6847), (FStar_Pervasives_Native.Some ("Typing for non-total arrows")), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____6840)))
in (

let fsym = (("f"), (FStar_SMTEncoding_Term.Term_sort))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV fsym)
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t1)
in (

let t_interp = (

let a_name = (Prims.strcat "pre_typing_" tsym)
in (

let uu____6859 = (

let uu____6866 = (

let uu____6867 = (

let uu____6878 = (

let uu____6879 = (

let uu____6884 = (

let uu____6885 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____6885))
in ((f_has_t), (uu____6884)))
in (FStar_SMTEncoding_Util.mkImp uu____6879))
in ((((f_has_t)::[])::[]), ((fsym)::[]), (uu____6878)))
in (mkForall_fuel uu____6867))
in ((uu____6866), (FStar_Pervasives_Native.Some (a_name)), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____6859)))
in ((t1), ((tdecl)::(t_kinding)::(t_interp)::[]))))))))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (uu____6912) -> begin
(

let uu____6919 = (

let uu____6924 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)
in (match (uu____6924) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.pos = uu____6931; FStar_Syntax_Syntax.vars = uu____6932} -> begin
(

let uu____6939 = (FStar_Syntax_Subst.open_term ((((x), (FStar_Pervasives_Native.None)))::[]) f)
in (match (uu____6939) with
| (b, f1) -> begin
(

let uu____6964 = (

let uu____6965 = (FStar_List.hd b)
in (FStar_Pervasives_Native.fst uu____6965))
in ((uu____6964), (f1)))
end))
end
| uu____6974 -> begin
(failwith "impossible")
end))
in (match (uu____6919) with
| (x, f) -> begin
(

let uu____6985 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (uu____6985) with
| (base_t, decls) -> begin
(

let uu____6996 = (gen_term_var env x)
in (match (uu____6996) with
| (x1, xtm, env') -> begin
(

let uu____7010 = (encode_formula f env')
in (match (uu____7010) with
| (refinement, decls') -> begin
(

let uu____7021 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____7021) with
| (fsym, fterm) -> begin
(

let tm_has_type_with_fuel = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (FStar_Pervasives_Native.Some (fterm)) xtm base_t)
in (

let encoding = (FStar_SMTEncoding_Util.mkAnd ((tm_has_type_with_fuel), (refinement)))
in (

let cvars = (

let uu____7037 = (

let uu____7040 = (FStar_SMTEncoding_Term.free_variables refinement)
in (

let uu____7047 = (FStar_SMTEncoding_Term.free_variables tm_has_type_with_fuel)
in (FStar_List.append uu____7040 uu____7047)))
in (FStar_Util.remove_dups FStar_SMTEncoding_Term.fv_eq uu____7037))
in (

let cvars1 = (FStar_All.pipe_right cvars (FStar_List.filter (fun uu____7080 -> (match (uu____7080) with
| (y, uu____7086) -> begin
((Prims.op_disEquality y x1) && (Prims.op_disEquality y fsym))
end))))
in (

let xfv = ((x1), (FStar_SMTEncoding_Term.Term_sort))
in (

let ffv = ((fsym), (FStar_SMTEncoding_Term.Fuel_sort))
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), ((ffv)::(xfv)::cvars1), (encoding)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____7119 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____7119) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
(

let uu____7127 = (

let uu____7128 = (

let uu____7135 = (FStar_All.pipe_right cvars1 (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((cache_entry.cache_symbol_name), (uu____7135)))
in (FStar_SMTEncoding_Util.mkApp uu____7128))
in ((uu____7127), ((FStar_List.append decls (FStar_List.append decls' (use_cache_entry cache_entry))))))
end
| FStar_Pervasives_Native.None -> begin
(

let module_name = env.current_module_name
in (

let tsym = (

let uu____7156 = (

let uu____7157 = (

let uu____7158 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "_Tm_refine_" uu____7158))
in (Prims.strcat module_name uu____7157))
in (varops.mk_unique uu____7156))
in (

let cvar_sorts = (FStar_List.map FStar_Pervasives_Native.snd cvars1)
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let t1 = (

let uu____7172 = (

let uu____7179 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars1)
in ((tsym), (uu____7179)))
in (FStar_SMTEncoding_Util.mkApp uu____7172))
in (

let x_has_base_t = (FStar_SMTEncoding_Term.mk_HasType xtm base_t)
in (

let x_has_t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (FStar_Pervasives_Native.Some (fterm)) xtm t1)
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t1 FStar_SMTEncoding_Term.mk_Term_type)
in (

let t_haseq_base = (FStar_SMTEncoding_Term.mk_haseq base_t)
in (

let t_haseq_ref = (FStar_SMTEncoding_Term.mk_haseq t1)
in (

let t_haseq1 = (

let uu____7194 = (

let uu____7201 = (

let uu____7202 = (

let uu____7213 = (FStar_SMTEncoding_Util.mkIff ((t_haseq_ref), (t_haseq_base)))
in ((((t_haseq_ref)::[])::[]), (cvars1), (uu____7213)))
in (FStar_SMTEncoding_Util.mkForall uu____7202))
in ((uu____7201), (FStar_Pervasives_Native.Some ((Prims.strcat "haseq for " tsym))), ((Prims.strcat "haseq" tsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____7194))
in (

let t_kinding = (

let uu____7231 = (

let uu____7238 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars1), (t_has_kind)))
in ((uu____7238), (FStar_Pervasives_Native.Some ("refinement kinding")), ((Prims.strcat "refinement_kinding_" tsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____7231))
in (

let t_interp = (

let uu____7256 = (

let uu____7263 = (

let uu____7264 = (

let uu____7275 = (FStar_SMTEncoding_Util.mkIff ((x_has_t), (encoding)))
in ((((x_has_t)::[])::[]), ((ffv)::(xfv)::cvars1), (uu____7275)))
in (FStar_SMTEncoding_Util.mkForall uu____7264))
in (

let uu____7298 = (

let uu____7301 = (FStar_Syntax_Print.term_to_string t0)
in FStar_Pervasives_Native.Some (uu____7301))
in ((uu____7263), (uu____7298), ((Prims.strcat "refinement_interpretation_" tsym)))))
in (FStar_SMTEncoding_Util.mkAssume uu____7256))
in (

let t_decls1 = (FStar_List.append decls (FStar_List.append decls' ((tdecl)::(t_kinding)::(t_interp)::(t_haseq1)::[])))
in ((

let uu____7308 = (mk_cache_entry env tsym cvar_sorts t_decls1)
in (FStar_Util.smap_add env.cache tkey_hash uu____7308));
((t1), (t_decls1));
)))))))))))))))
end))))))))))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
(

let ttm = (

let uu____7338 = (FStar_Syntax_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Util.mk_Term_uvar uu____7338))
in (

let uu____7339 = (encode_term_pred FStar_Pervasives_Native.None k env ttm)
in (match (uu____7339) with
| (t_has_k, decls) -> begin
(

let d = (

let uu____7351 = (

let uu____7358 = (

let uu____7359 = (

let uu____7360 = (

let uu____7361 = (FStar_Syntax_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____7361))
in (FStar_Util.format1 "uvar_typing_%s" uu____7360))
in (varops.mk_unique uu____7359))
in ((t_has_k), (FStar_Pervasives_Native.Some ("Uvar typing")), (uu____7358)))
in (FStar_SMTEncoding_Util.mkAssume uu____7351))
in ((ttm), ((FStar_List.append decls ((d)::[])))))
end)))
end
| FStar_Syntax_Syntax.Tm_app (uu____7366) -> begin
(

let uu____7381 = (FStar_Syntax_Util.head_and_args t0)
in (match (uu____7381) with
| (head1, args_e) -> begin
(

let uu____7422 = (

let uu____7435 = (

let uu____7436 = (FStar_Syntax_Subst.compress head1)
in uu____7436.FStar_Syntax_Syntax.n)
in ((uu____7435), (args_e)))
in (match (uu____7422) with
| uu____7451 when (head_redex env head1) -> begin
(

let uu____7464 = (whnf env t)
in (encode_term uu____7464 env))
end
| uu____7465 when (is_arithmetic_primitive head1 args_e) -> begin
(encode_arith_term env head1 args_e)
end
| uu____7484 when (is_BitVector_primitive head1 args_e) -> begin
(encode_BitVector_term env head1 args_e)
end
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____7498; FStar_Syntax_Syntax.vars = uu____7499}, uu____7500), (uu____7501)::((v1, uu____7503))::((v2, uu____7505))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.lexcons_lid) -> begin
(

let uu____7556 = (encode_term v1 env)
in (match (uu____7556) with
| (v11, decls1) -> begin
(

let uu____7567 = (encode_term v2 env)
in (match (uu____7567) with
| (v21, decls2) -> begin
(

let uu____7578 = (FStar_SMTEncoding_Util.mk_LexCons v11 v21)
in ((uu____7578), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____7582)::((v1, uu____7584))::((v2, uu____7586))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.lexcons_lid) -> begin
(

let uu____7633 = (encode_term v1 env)
in (match (uu____7633) with
| (v11, decls1) -> begin
(

let uu____7644 = (encode_term v2 env)
in (match (uu____7644) with
| (v21, decls2) -> begin
(

let uu____7655 = (FStar_SMTEncoding_Util.mk_LexCons v11 v21)
in ((uu____7655), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of), ((arg, uu____7659))::[]) -> begin
(encode_const (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos)) env)
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of), ((arg, uu____7685))::((rng, uu____7687))::[]) -> begin
(encode_term arg env)
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), uu____7722) -> begin
(

let e0 = (

let uu____7740 = (FStar_List.hd args_e)
in (FStar_TypeChecker_Util.reify_body_with_arg env.tcenv head1 uu____7740))
in ((

let uu____7748 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____7748) with
| true -> begin
(

let uu____7749 = (FStar_Syntax_Print.term_to_string e0)
in (FStar_Util.print1 "Result of normalization %s\n" uu____7749))
end
| uu____7750 -> begin
()
end));
(

let e = (

let uu____7754 = (

let uu____7755 = (FStar_TypeChecker_Util.remove_reify e0)
in (

let uu____7756 = (FStar_List.tl args_e)
in (FStar_Syntax_Syntax.mk_Tm_app uu____7755 uu____7756)))
in (uu____7754 FStar_Pervasives_Native.None t0.FStar_Syntax_Syntax.pos))
in (encode_term e env));
))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____7765)), ((arg, uu____7767))::[]) -> begin
(encode_term arg env)
end
| uu____7792 -> begin
(

let uu____7805 = (encode_args args_e env)
in (match (uu____7805) with
| (args, decls) -> begin
(

let encode_partial_app = (fun ht_opt -> (

let uu____7860 = (encode_term head1 env)
in (match (uu____7860) with
| (head2, decls') -> begin
(

let app_tm = (mk_Apply_args head2 args)
in (match (ht_opt) with
| FStar_Pervasives_Native.None -> begin
((app_tm), ((FStar_List.append decls decls')))
end
| FStar_Pervasives_Native.Some (formals, c) -> begin
(

let uu____7924 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (uu____7924) with
| (formals1, rest) -> begin
(

let subst1 = (FStar_List.map2 (fun uu____8002 uu____8003 -> (match (((uu____8002), (uu____8003))) with
| ((bv, uu____8025), (a, uu____8027)) -> begin
FStar_Syntax_Syntax.NT (((bv), (a)))
end)) formals1 args_e)
in (

let ty = (

let uu____8045 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right uu____8045 (FStar_Syntax_Subst.subst subst1)))
in (

let uu____8050 = (encode_term_pred FStar_Pervasives_Native.None ty env app_tm)
in (match (uu____8050) with
| (has_type, decls'') -> begin
(

let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (

let e_typing = (

let uu____8065 = (

let uu____8072 = (FStar_SMTEncoding_Util.mkForall ((((has_type)::[])::[]), (cvars), (has_type)))
in (

let uu____8081 = (

let uu____8082 = (

let uu____8083 = (

let uu____8084 = (FStar_SMTEncoding_Term.hash_of_term app_tm)
in (FStar_Util.digest_of_string uu____8084))
in (Prims.strcat "partial_app_typing_" uu____8083))
in (varops.mk_unique uu____8082))
in ((uu____8072), (FStar_Pervasives_Native.Some ("Partial app typing")), (uu____8081))))
in (FStar_SMTEncoding_Util.mkAssume uu____8065))
in ((app_tm), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' ((e_typing)::[]))))))))
end))))
end))
end))
end)))
in (

let encode_full_app = (fun fv -> (

let uu____8101 = (lookup_free_var_sym env fv)
in (match (uu____8101) with
| (fname, fuel_args, arity) -> begin
(

let tm = (maybe_curry_app t0.FStar_Syntax_Syntax.pos fname arity (FStar_List.append fuel_args args))
in ((tm), (decls)))
end)))
in (

let head2 = (FStar_Syntax_Subst.compress head1)
in (

let head_type = (match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (x); FStar_Syntax_Syntax.pos = uu____8133; FStar_Syntax_Syntax.vars = uu____8134}, uu____8135) -> begin
FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____8146; FStar_Syntax_Syntax.vars = uu____8147}, uu____8148) -> begin
(

let uu____8153 = (

let uu____8154 = (

let uu____8159 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____8159 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____8154 FStar_Pervasives_Native.snd))
in FStar_Pervasives_Native.Some (uu____8153))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____8189 = (

let uu____8190 = (

let uu____8195 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____8195 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____8190 FStar_Pervasives_Native.snd))
in FStar_Pervasives_Native.Some (uu____8189))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____8224, (FStar_Util.Inl (t1), uu____8226), uu____8227) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____8276, (FStar_Util.Inr (c), uu____8278), uu____8279) -> begin
FStar_Pervasives_Native.Some ((FStar_Syntax_Util.comp_result c))
end
| uu____8328 -> begin
FStar_Pervasives_Native.None
end)
in (match (head_type) with
| FStar_Pervasives_Native.None -> begin
(encode_partial_app FStar_Pervasives_Native.None)
end
| FStar_Pervasives_Native.Some (head_type1) -> begin
(

let head_type2 = (

let uu____8355 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type1)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine uu____8355))
in (

let uu____8356 = (curried_arrow_formals_comp head_type2)
in (match (uu____8356) with
| (formals, c) -> begin
(match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____8372; FStar_Syntax_Syntax.vars = uu____8373}, uu____8374) when (Prims.op_Equality (FStar_List.length formals) (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (Prims.op_Equality (FStar_List.length formals) (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| uu____8388 -> begin
(match (((FStar_List.length formals) > (FStar_List.length args))) with
| true -> begin
(encode_partial_app (FStar_Pervasives_Native.Some (((formals), (c)))))
end
| uu____8401 -> begin
(encode_partial_app FStar_Pervasives_Native.None)
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

let uu____8437 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____8437) with
| (bs1, body1, opening) -> begin
(

let fallback = (fun uu____8460 -> (

let f = (varops.fresh "Tm_abs")
in (

let decl = FStar_SMTEncoding_Term.DeclFun (((f), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Imprecise function encoding"))))
in (

let uu____8467 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in ((uu____8467), ((decl)::[]))))))
in (

let is_impure = (fun rc -> (

let uu____8474 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv rc.FStar_Syntax_Syntax.residual_effect)
in (FStar_All.pipe_right uu____8474 Prims.op_Negation)))
in (

let codomain_eff = (fun rc -> (

let res_typ = (match (rc.FStar_Syntax_Syntax.residual_typ) with
| FStar_Pervasives_Native.None -> begin
(

let uu____8484 = (FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange [] FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right uu____8484 FStar_Pervasives_Native.fst))
end
| FStar_Pervasives_Native.Some (t1) -> begin
t1
end)
in (match ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_Tot_lid)) with
| true -> begin
(

let uu____8504 = (FStar_Syntax_Syntax.mk_Total res_typ)
in FStar_Pervasives_Native.Some (uu____8504))
end
| uu____8505 -> begin
(match ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_GTot_lid)) with
| true -> begin
(

let uu____8508 = (FStar_Syntax_Syntax.mk_GTotal res_typ)
in FStar_Pervasives_Native.Some (uu____8508))
end
| uu____8509 -> begin
FStar_Pervasives_Native.None
end)
end)))
in (match (lopt) with
| FStar_Pervasives_Native.None -> begin
((

let uu____8515 = (

let uu____8520 = (

let uu____8521 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)" uu____8521))
in ((FStar_Errors.Warning_FunctionLiteralPrecisionLoss), (uu____8520)))
in (FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____8515));
(fallback ());
)
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____8523 = ((is_impure rc) && (

let uu____8525 = (FStar_TypeChecker_Env.is_reifiable env.tcenv rc)
in (not (uu____8525))))
in (match (uu____8523) with
| true -> begin
(fallback ())
end
| uu____8530 -> begin
(

let cache_size = (FStar_Util.smap_size env.cache)
in (

let uu____8532 = (encode_binders FStar_Pervasives_Native.None bs1 env)
in (match (uu____8532) with
| (vars, guards, envbody, decls, uu____8557) -> begin
(

let body2 = (

let uu____8571 = (FStar_TypeChecker_Env.is_reifiable env.tcenv rc)
in (match (uu____8571) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env.tcenv body1)
end
| uu____8572 -> begin
body1
end))
in (

let uu____8573 = (encode_term body2 envbody)
in (match (uu____8573) with
| (body3, decls') -> begin
(

let uu____8584 = (

let uu____8593 = (codomain_eff rc)
in (match (uu____8593) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), ([]))
end
| FStar_Pervasives_Native.Some (c) -> begin
(

let tfun = (FStar_Syntax_Util.arrow bs1 c)
in (

let uu____8612 = (encode_term tfun env)
in (match (uu____8612) with
| (t1, decls1) -> begin
((FStar_Pervasives_Native.Some (t1)), (decls1))
end)))
end))
in (match (uu____8584) with
| (arrow_t_opt, decls'') -> begin
(

let key_body = (

let uu____8644 = (

let uu____8655 = (

let uu____8656 = (

let uu____8661 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____8661), (body3)))
in (FStar_SMTEncoding_Util.mkImp uu____8656))
in (([]), (vars), (uu____8655)))
in (FStar_SMTEncoding_Util.mkForall uu____8644))
in (

let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (

let cvars1 = (match (arrow_t_opt) with
| FStar_Pervasives_Native.None -> begin
cvars
end
| FStar_Pervasives_Native.Some (t1) -> begin
(

let uu____8673 = (

let uu____8676 = (FStar_SMTEncoding_Term.free_variables t1)
in (FStar_List.append uu____8676 cvars))
in (FStar_Util.remove_dups FStar_SMTEncoding_Term.fv_eq uu____8673))
end)
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), (cvars1), (key_body)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____8695 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____8695) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
(

let uu____8703 = (

let uu____8704 = (

let uu____8711 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars1)
in ((cache_entry.cache_symbol_name), (uu____8711)))
in (FStar_SMTEncoding_Util.mkApp uu____8704))
in ((uu____8703), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' (use_cache_entry cache_entry)))))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____8722 = (is_an_eta_expansion env vars body3)
in (match (uu____8722) with
| FStar_Pervasives_Native.Some (t1) -> begin
(

let decls1 = (

let uu____8733 = (

let uu____8734 = (FStar_Util.smap_size env.cache)
in (Prims.op_Equality uu____8734 cache_size))
in (match (uu____8733) with
| true -> begin
[]
end
| uu____8737 -> begin
(FStar_List.append decls (FStar_List.append decls' decls''))
end))
in ((t1), (decls1)))
end
| FStar_Pervasives_Native.None -> begin
(

let cvar_sorts = (FStar_List.map FStar_Pervasives_Native.snd cvars1)
in (

let fsym = (

let module_name = env.current_module_name
in (

let fsym = (

let uu____8750 = (

let uu____8751 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_abs_" uu____8751))
in (varops.mk_unique uu____8750))
in (Prims.strcat module_name (Prims.strcat "_" fsym))))
in (

let fdecl = FStar_SMTEncoding_Term.DeclFun (((fsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let f = (

let uu____8758 = (

let uu____8765 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars1)
in ((fsym), (uu____8765)))
in (FStar_SMTEncoding_Util.mkApp uu____8758))
in (

let app = (mk_Apply f vars)
in (

let typing_f = (match (arrow_t_opt) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (t1) -> begin
(

let f_has_t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel FStar_Pervasives_Native.None f t1)
in (

let a_name = (Prims.strcat "typing_" fsym)
in (

let uu____8783 = (

let uu____8784 = (

let uu____8791 = (FStar_SMTEncoding_Util.mkForall ((((f)::[])::[]), (cvars1), (f_has_t)))
in ((uu____8791), (FStar_Pervasives_Native.Some (a_name)), (a_name)))
in (FStar_SMTEncoding_Util.mkAssume uu____8784))
in (uu____8783)::[])))
end)
in (

let interp_f = (

let a_name = (Prims.strcat "interpretation_" fsym)
in (

let uu____8804 = (

let uu____8811 = (

let uu____8812 = (

let uu____8823 = (FStar_SMTEncoding_Util.mkEq ((app), (body3)))
in ((((app)::[])::[]), ((FStar_List.append vars cvars1)), (uu____8823)))
in (FStar_SMTEncoding_Util.mkForall uu____8812))
in ((uu____8811), (FStar_Pervasives_Native.Some (a_name)), (a_name)))
in (FStar_SMTEncoding_Util.mkAssume uu____8804)))
in (

let f_decls = (FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' (FStar_List.append ((fdecl)::typing_f) ((interp_f)::[])))))
in ((

let uu____8840 = (mk_cache_entry env fsym cvar_sorts f_decls)
in (FStar_Util.smap_add env.cache tkey_hash uu____8840));
((f), (f_decls));
)))))))))
end))
end)))))))
end))
end)))
end)))
end))
end))))
end))
end
| FStar_Syntax_Syntax.Tm_let ((uu____8843, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____8844); FStar_Syntax_Syntax.lbunivs = uu____8845; FStar_Syntax_Syntax.lbtyp = uu____8846; FStar_Syntax_Syntax.lbeff = uu____8847; FStar_Syntax_Syntax.lbdef = uu____8848; FStar_Syntax_Syntax.lbattrs = uu____8849; FStar_Syntax_Syntax.lbpos = uu____8850})::uu____8851), uu____8852) -> begin
(failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____8882; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____8884; FStar_Syntax_Syntax.lbdef = e1; FStar_Syntax_Syntax.lbattrs = uu____8886; FStar_Syntax_Syntax.lbpos = uu____8887})::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (uu____8911) -> begin
((FStar_Errors.diag t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions, and their enclosings let bindings (including the top-level let) are not yet fully encoded to the SMT solver; you may not be able to prove some facts");
(FStar_Exn.raise Inner_let_rec);
)
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end);
)))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (

let uu____8981 = (

let uu____8986 = (FStar_Syntax_Util.ascribe e1 ((FStar_Util.Inl (t1)), (FStar_Pervasives_Native.None)))
in (encode_term uu____8986 env))
in (match (uu____8981) with
| (ee1, decls1) -> begin
(

let uu____9007 = (FStar_Syntax_Subst.open_term ((((x), (FStar_Pervasives_Native.None)))::[]) e2)
in (match (uu____9007) with
| (xs, e21) -> begin
(

let uu____9032 = (FStar_List.hd xs)
in (match (uu____9032) with
| (x1, uu____9046) -> begin
(

let env' = (push_term_var env x1 ee1)
in (

let uu____9048 = (encode_body e21 env')
in (match (uu____9048) with
| (ee2, decls2) -> begin
((ee2), ((FStar_List.append decls1 decls2)))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (

let uu____9080 = (

let uu____9087 = (

let uu____9088 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.null_bv uu____9088))
in (gen_term_var env uu____9087))
in (match (uu____9080) with
| (scrsym, scr', env1) -> begin
(

let uu____9096 = (encode_term e env1)
in (match (uu____9096) with
| (scr, decls) -> begin
(

let uu____9107 = (

let encode_branch = (fun b uu____9132 -> (match (uu____9132) with
| (else_case, decls1) -> begin
(

let uu____9151 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____9151) with
| (p, w, br) -> begin
(

let uu____9177 = (encode_pat env1 p)
in (match (uu____9177) with
| (env0, pattern) -> begin
(

let guard = (pattern.guard scr')
in (

let projections = (pattern.projections scr')
in (

let env2 = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env2 uu____9214 -> (match (uu____9214) with
| (x, t) -> begin
(push_term_var env2 x t)
end)) env1))
in (

let uu____9221 = (match (w) with
| FStar_Pervasives_Native.None -> begin
((guard), ([]))
end
| FStar_Pervasives_Native.Some (w1) -> begin
(

let uu____9243 = (encode_term w1 env2)
in (match (uu____9243) with
| (w2, decls2) -> begin
(

let uu____9256 = (

let uu____9257 = (

let uu____9262 = (

let uu____9263 = (

let uu____9268 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue)
in ((w2), (uu____9268)))
in (FStar_SMTEncoding_Util.mkEq uu____9263))
in ((guard), (uu____9262)))
in (FStar_SMTEncoding_Util.mkAnd uu____9257))
in ((uu____9256), (decls2)))
end))
end)
in (match (uu____9221) with
| (guard1, decls2) -> begin
(

let uu____9281 = (encode_br br env2)
in (match (uu____9281) with
| (br1, decls3) -> begin
(

let uu____9294 = (FStar_SMTEncoding_Util.mkITE ((guard1), (br1), (else_case)))
in ((uu____9294), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end)))))
end))
end))
end))
in (FStar_List.fold_right encode_branch pats ((default_case), (decls))))
in (match (uu____9107) with
| (match_tm, decls1) -> begin
(

let uu____9313 = (FStar_SMTEncoding_Term.mkLet' (((((((scrsym), (FStar_SMTEncoding_Term.Term_sort))), (scr)))::[]), (match_tm)) FStar_Range.dummyRange)
in ((uu____9313), (decls1)))
end))
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> ((

let uu____9353 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____9353) with
| true -> begin
(

let uu____9354 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" uu____9354))
end
| uu____9355 -> begin
()
end));
(

let uu____9356 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (uu____9356) with
| (vars, pat_term) -> begin
(

let uu____9373 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun uu____9426 v1 -> (match (uu____9426) with
| (env1, vars1) -> begin
(

let uu____9478 = (gen_term_var env1 v1)
in (match (uu____9478) with
| (xx, uu____9500, env2) -> begin
((env2), ((((v1), (((xx), (FStar_SMTEncoding_Term.Term_sort)))))::vars1))
end))
end)) ((env), ([]))))
in (match (uu____9373) with
| (env1, vars1) -> begin
(

let rec mk_guard = (fun pat1 scrutinee -> (match (pat1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_var (uu____9579) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_wild (uu____9580) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____9581) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____9589 = (encode_const c env1)
in (match (uu____9589) with
| (tm, decls) -> begin
((match (decls) with
| (uu____9603)::uu____9604 -> begin
(failwith "Unexpected encoding of constant pattern")
end
| uu____9607 -> begin
()
end);
(FStar_SMTEncoding_Util.mkEq ((scrutinee), (tm)));
)
end))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let is_f = (

let tc_name = (FStar_TypeChecker_Env.typ_of_datacon env1.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let uu____9630 = (FStar_TypeChecker_Env.datacons_of_typ env1.tcenv tc_name)
in (match (uu____9630) with
| (uu____9637, (uu____9638)::[]) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| uu____9641 -> begin
(mk_data_tester env1 f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
end)))
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____9674 -> (match (uu____9674) with
| (arg, uu____9682) -> begin
(

let proj = (primitive_projector_by_pos env1.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____9688 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_guard arg uu____9688)))
end))))
in (FStar_SMTEncoding_Util.mk_and_l ((is_f)::sub_term_guards))))
end))
in (

let rec mk_projections = (fun pat1 scrutinee -> (match (pat1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (x, uu____9715) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_constant (uu____9746) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let uu____9769 = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____9813 -> (match (uu____9813) with
| (arg, uu____9827) -> begin
(

let proj = (primitive_projector_by_pos env1.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____9833 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_projections arg uu____9833)))
end))))
in (FStar_All.pipe_right uu____9769 FStar_List.flatten))
end))
in (

let pat_term1 = (fun uu____9861 -> (encode_term pat_term env1))
in (

let pattern = {pat_vars = vars1; pat_term = pat_term1; guard = (mk_guard pat); projections = (mk_projections pat)}
in ((env1), (pattern))))))
end))
end));
))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (

let uu____9871 = (FStar_All.pipe_right l (FStar_List.fold_left (fun uu____9909 uu____9910 -> (match (((uu____9909), (uu____9910))) with
| ((tms, decls), (t, uu____9946)) -> begin
(

let uu____9967 = (encode_term t env)
in (match (uu____9967) with
| (t1, decls') -> begin
(((t1)::tms), ((FStar_List.append decls decls')))
end))
end)) (([]), ([]))))
in (match (uu____9871) with
| (l1, decls) -> begin
(((FStar_List.rev l1)), (decls))
end)))
and encode_function_type_as_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let list_elements1 = (fun e -> (

let uu____10024 = (FStar_Syntax_Util.list_elements e)
in (match (uu____10024) with
| FStar_Pervasives_Native.Some (l) -> begin
l
end
| FStar_Pervasives_Native.None -> begin
((FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos ((FStar_Errors.Warning_NonListLiteralSMTPattern), ("SMT pattern is not a list literal; ignoring the pattern")));
[];
)
end)))
in (

let one_pat = (fun p -> (

let uu____10045 = (

let uu____10060 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right uu____10060 FStar_Syntax_Util.head_and_args))
in (match (uu____10045) with
| (head1, args) -> begin
(

let uu____10099 = (

let uu____10112 = (

let uu____10113 = (FStar_Syntax_Util.un_uinst head1)
in uu____10113.FStar_Syntax_Syntax.n)
in ((uu____10112), (args)))
in (match (uu____10099) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((uu____10127, uu____10128))::((e, uu____10130))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpat_lid) -> begin
e
end
| uu____10165 -> begin
(failwith "Unexpected pattern term")
end))
end)))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements1 p)
in (

let smt_pat_or1 = (fun t1 -> (

let uu____10201 = (

let uu____10216 = (FStar_Syntax_Util.unmeta t1)
in (FStar_All.pipe_right uu____10216 FStar_Syntax_Util.head_and_args))
in (match (uu____10201) with
| (head1, args) -> begin
(

let uu____10257 = (

let uu____10270 = (

let uu____10271 = (FStar_Syntax_Util.un_uinst head1)
in uu____10271.FStar_Syntax_Syntax.n)
in ((uu____10270), (args)))
in (match (uu____10257) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, uu____10288))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpatOr_lid) -> begin
FStar_Pervasives_Native.Some (e)
end
| uu____10315 -> begin
FStar_Pervasives_Native.None
end))
end)))
in (match (elts) with
| (t1)::[] -> begin
(

let uu____10337 = (smt_pat_or1 t1)
in (match (uu____10337) with
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____10353 = (list_elements1 e)
in (FStar_All.pipe_right uu____10353 (FStar_List.map (fun branch1 -> (

let uu____10371 = (list_elements1 branch1)
in (FStar_All.pipe_right uu____10371 (FStar_List.map one_pat)))))))
end
| uu____10382 -> begin
(

let uu____10387 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____10387)::[])
end))
end
| uu____10408 -> begin
(

let uu____10411 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____10411)::[])
end))))
in (

let uu____10432 = (

let uu____10451 = (

let uu____10452 = (FStar_Syntax_Subst.compress t)
in uu____10452.FStar_Syntax_Syntax.n)
in (match (uu____10451) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____10491 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____10491) with
| (binders1, c1) -> begin
(match (c1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____10534; FStar_Syntax_Syntax.effect_name = uu____10535; FStar_Syntax_Syntax.result_typ = uu____10536; FStar_Syntax_Syntax.effect_args = ((pre, uu____10538))::((post, uu____10540))::((pats, uu____10542))::[]; FStar_Syntax_Syntax.flags = uu____10543}) -> begin
(

let uu____10584 = (lemma_pats pats)
in ((binders1), (pre), (post), (uu____10584)))
end
| uu____10601 -> begin
(failwith "impos")
end)
end))
end
| uu____10620 -> begin
(failwith "Impos")
end))
in (match (uu____10432) with
| (binders, pre, post, patterns) -> begin
(

let env1 = (

let uu___115_10668 = env
in {bindings = uu___115_10668.bindings; depth = uu___115_10668.depth; tcenv = uu___115_10668.tcenv; warn = uu___115_10668.warn; cache = uu___115_10668.cache; nolabels = uu___115_10668.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___115_10668.encode_non_total_function_typ; current_module_name = uu___115_10668.current_module_name})
in (

let uu____10669 = (encode_binders FStar_Pervasives_Native.None binders env1)
in (match (uu____10669) with
| (vars, guards, env2, decls, uu____10694) -> begin
(

let uu____10707 = (

let uu____10722 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch1 -> (

let uu____10776 = (

let uu____10787 = (FStar_All.pipe_right branch1 (FStar_List.map (fun t1 -> (encode_smt_pattern t1 env2))))
in (FStar_All.pipe_right uu____10787 FStar_List.unzip))
in (match (uu____10776) with
| (pats, decls1) -> begin
((pats), (decls1))
end)))))
in (FStar_All.pipe_right uu____10722 FStar_List.unzip))
in (match (uu____10707) with
| (pats, decls') -> begin
(

let decls'1 = (FStar_List.flatten decls')
in (

let post1 = (FStar_Syntax_Util.unthunk_lemma_post post)
in (

let env3 = (

let uu___116_10939 = env2
in {bindings = uu___116_10939.bindings; depth = uu___116_10939.depth; tcenv = uu___116_10939.tcenv; warn = uu___116_10939.warn; cache = uu___116_10939.cache; nolabels = true; use_zfuel_name = uu___116_10939.use_zfuel_name; encode_non_total_function_typ = uu___116_10939.encode_non_total_function_typ; current_module_name = uu___116_10939.current_module_name})
in (

let uu____10940 = (

let uu____10945 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula uu____10945 env3))
in (match (uu____10940) with
| (pre1, decls'') -> begin
(

let uu____10952 = (

let uu____10957 = (FStar_Syntax_Util.unmeta post1)
in (encode_formula uu____10957 env3))
in (match (uu____10952) with
| (post2, decls''') -> begin
(

let decls1 = (FStar_List.append decls (FStar_List.append (FStar_List.flatten decls'1) (FStar_List.append decls'' decls''')))
in (

let uu____10967 = (

let uu____10968 = (

let uu____10979 = (

let uu____10980 = (

let uu____10985 = (FStar_SMTEncoding_Util.mk_and_l ((pre1)::guards))
in ((uu____10985), (post2)))
in (FStar_SMTEncoding_Util.mkImp uu____10980))
in ((pats), (vars), (uu____10979)))
in (FStar_SMTEncoding_Util.mkForall uu____10968))
in ((uu____10967), (decls1))))
end))
end)))))
end))
end)))
end))))))
and encode_smt_pattern : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  env_t  ->  (FStar_SMTEncoding_Term.pat * FStar_SMTEncoding_Term.decl Prims.list) = (fun t env -> (

let uu____10998 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____10998) with
| (head1, args) -> begin
(

let head2 = (FStar_Syntax_Util.un_uinst head1)
in (match (((head2.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____11057)::((x, uu____11059))::((t1, uu____11061))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.has_type_lid) -> begin
(

let uu____11108 = (encode_term x env)
in (match (uu____11108) with
| (x1, decls) -> begin
(

let uu____11121 = (encode_term t1 env)
in (match (uu____11121) with
| (t2, decls') -> begin
(

let uu____11134 = (FStar_SMTEncoding_Term.mk_HasType x1 t2)
in ((uu____11134), ((FStar_List.append decls decls'))))
end))
end))
end
| uu____11137 -> begin
(encode_term t env)
end))
end)))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (

let debug1 = (fun phi1 -> (

let uu____11160 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____11160) with
| true -> begin
(

let uu____11161 = (FStar_Syntax_Print.tag_of_term phi1)
in (

let uu____11162 = (FStar_Syntax_Print.term_to_string phi1)
in (FStar_Util.print2 "Formula (%s)  %s\n" uu____11161 uu____11162)))
end
| uu____11163 -> begin
()
end)))
in (

let enc = (fun f r l -> (

let uu____11195 = (FStar_Util.fold_map (fun decls x -> (

let uu____11223 = (encode_term (FStar_Pervasives_Native.fst x) env)
in (match (uu____11223) with
| (t, decls') -> begin
(((FStar_List.append decls decls')), (t))
end))) [] l)
in (match (uu____11195) with
| (decls, args) -> begin
(

let uu____11252 = (

let uu___117_11253 = (f args)
in {FStar_SMTEncoding_Term.tm = uu___117_11253.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___117_11253.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____11252), (decls)))
end)))
in (

let const_op = (fun f r uu____11284 -> (

let uu____11297 = (f r)
in ((uu____11297), ([]))))
in (

let un_op = (fun f l -> (

let uu____11316 = (FStar_List.hd l)
in (FStar_All.pipe_left f uu____11316)))
in (

let bin_op = (fun f uu___91_11332 -> (match (uu___91_11332) with
| (t1)::(t2)::[] -> begin
(f ((t1), (t2)))
end
| uu____11343 -> begin
(failwith "Impossible")
end))
in (

let enc_prop_c = (fun f r l -> (

let uu____11377 = (FStar_Util.fold_map (fun decls uu____11400 -> (match (uu____11400) with
| (t, uu____11414) -> begin
(

let uu____11415 = (encode_formula t env)
in (match (uu____11415) with
| (phi1, decls') -> begin
(((FStar_List.append decls decls')), (phi1))
end))
end)) [] l)
in (match (uu____11377) with
| (decls, phis) -> begin
(

let uu____11444 = (

let uu___118_11445 = (f phis)
in {FStar_SMTEncoding_Term.tm = uu___118_11445.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___118_11445.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____11444), (decls)))
end)))
in (

let eq_op = (fun r args -> (

let rf = (FStar_List.filter (fun uu____11506 -> (match (uu____11506) with
| (a, q) -> begin
(match (q) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____11525)) -> begin
false
end
| uu____11526 -> begin
true
end)
end)) args)
in (match ((Prims.op_disEquality (FStar_List.length rf) (Prims.parse_int "2"))) with
| true -> begin
(

let uu____11541 = (FStar_Util.format1 "eq_op: got %s non-implicit arguments instead of 2?" (Prims.string_of_int (FStar_List.length rf)))
in (failwith uu____11541))
end
| uu____11554 -> begin
(

let uu____11555 = (enc (bin_op FStar_SMTEncoding_Util.mkEq))
in (uu____11555 r rf))
end)))
in (

let mk_imp1 = (fun r uu___92_11580 -> (match (uu___92_11580) with
| ((lhs, uu____11586))::((rhs, uu____11588))::[] -> begin
(

let uu____11615 = (encode_formula rhs env)
in (match (uu____11615) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____11630) -> begin
((l1), (decls1))
end
| uu____11635 -> begin
(

let uu____11636 = (encode_formula lhs env)
in (match (uu____11636) with
| (l2, decls2) -> begin
(

let uu____11647 = (FStar_SMTEncoding_Term.mkImp ((l2), (l1)) r)
in ((uu____11647), ((FStar_List.append decls1 decls2))))
end))
end)
end))
end
| uu____11650 -> begin
(failwith "impossible")
end))
in (

let mk_ite = (fun r uu___93_11671 -> (match (uu___93_11671) with
| ((guard, uu____11677))::((_then, uu____11679))::((_else, uu____11681))::[] -> begin
(

let uu____11718 = (encode_formula guard env)
in (match (uu____11718) with
| (g, decls1) -> begin
(

let uu____11729 = (encode_formula _then env)
in (match (uu____11729) with
| (t, decls2) -> begin
(

let uu____11740 = (encode_formula _else env)
in (match (uu____11740) with
| (e, decls3) -> begin
(

let res = (FStar_SMTEncoding_Term.mkITE ((g), (t), (e)) r)
in ((res), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end))
end))
end
| uu____11754 -> begin
(failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (

let uu____11779 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f uu____11779)))
in (

let connectives = (

let uu____11797 = (

let uu____11810 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd))
in ((FStar_Parser_Const.and_lid), (uu____11810)))
in (

let uu____11827 = (

let uu____11842 = (

let uu____11855 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr))
in ((FStar_Parser_Const.or_lid), (uu____11855)))
in (

let uu____11872 = (

let uu____11887 = (

let uu____11902 = (

let uu____11915 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff))
in ((FStar_Parser_Const.iff_lid), (uu____11915)))
in (

let uu____11932 = (

let uu____11947 = (

let uu____11962 = (

let uu____11975 = (enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot))
in ((FStar_Parser_Const.not_lid), (uu____11975)))
in (uu____11962)::(((FStar_Parser_Const.eq2_lid), (eq_op)))::(((FStar_Parser_Const.eq3_lid), (eq_op)))::(((FStar_Parser_Const.true_lid), ((const_op FStar_SMTEncoding_Term.mkTrue))))::(((FStar_Parser_Const.false_lid), ((const_op FStar_SMTEncoding_Term.mkFalse))))::[])
in (((FStar_Parser_Const.ite_lid), (mk_ite)))::uu____11947)
in (uu____11902)::uu____11932))
in (((FStar_Parser_Const.imp_lid), (mk_imp1)))::uu____11887)
in (uu____11842)::uu____11872))
in (uu____11797)::uu____11827))
in (

let rec fallback = (fun phi1 -> (match (phi1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(

let uu____12296 = (encode_formula phi' env)
in (match (uu____12296) with
| (phi2, decls) -> begin
(

let uu____12307 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled (((phi2), (msg), (r)))) r)
in ((uu____12307), (decls)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (uu____12308) -> begin
(

let uu____12315 = (FStar_Syntax_Util.unmeta phi1)
in (encode_formula uu____12315 env))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(

let uu____12354 = (encode_match e pats FStar_SMTEncoding_Util.mkFalse env encode_formula)
in (match (uu____12354) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____12366; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____12368; FStar_Syntax_Syntax.lbdef = e1; FStar_Syntax_Syntax.lbattrs = uu____12370; FStar_Syntax_Syntax.lbpos = uu____12371})::[]), e2) -> begin
(

let uu____12395 = (encode_let x t1 e1 e2 env encode_formula)
in (match (uu____12395) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let head2 = (FStar_Syntax_Util.un_uinst head1)
in (match (((head2.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____12442)::((x, uu____12444))::((t, uu____12446))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.has_type_lid) -> begin
(

let uu____12493 = (encode_term x env)
in (match (uu____12493) with
| (x1, decls) -> begin
(

let uu____12504 = (encode_term t env)
in (match (uu____12504) with
| (t1, decls') -> begin
(

let uu____12515 = (FStar_SMTEncoding_Term.mk_HasType x1 t1)
in ((uu____12515), ((FStar_List.append decls decls'))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((r, uu____12520))::((msg, uu____12522))::((phi2, uu____12524))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.labeled_lid) -> begin
(

let uu____12569 = (

let uu____12574 = (

let uu____12575 = (FStar_Syntax_Subst.compress r)
in uu____12575.FStar_Syntax_Syntax.n)
in (

let uu____12578 = (

let uu____12579 = (FStar_Syntax_Subst.compress msg)
in uu____12579.FStar_Syntax_Syntax.n)
in ((uu____12574), (uu____12578))))
in (match (uu____12569) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____12588))) -> begin
(

let phi3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((phi2), (FStar_Syntax_Syntax.Meta_labeled (((s), (r1), (false))))))) FStar_Pervasives_Native.None r1)
in (fallback phi3))
end
| uu____12594 -> begin
(fallback phi2)
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((t, uu____12601))::[]) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.auto_squash_lid)) -> begin
(encode_formula t env)
end
| uu____12626 when (head_redex env head2) -> begin
(

let uu____12639 = (whnf env phi1)
in (encode_formula uu____12639 env))
end
| uu____12640 -> begin
(

let uu____12653 = (encode_term phi1 env)
in (match (uu____12653) with
| (tt, decls) -> begin
(

let uu____12664 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___119_12667 = tt
in {FStar_SMTEncoding_Term.tm = uu___119_12667.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___119_12667.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi1.FStar_Syntax_Syntax.pos}))
in ((uu____12664), (decls)))
end))
end))
end
| uu____12668 -> begin
(

let uu____12669 = (encode_term phi1 env)
in (match (uu____12669) with
| (tt, decls) -> begin
(

let uu____12680 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___120_12683 = tt
in {FStar_SMTEncoding_Term.tm = uu___120_12683.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___120_12683.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi1.FStar_Syntax_Syntax.pos}))
in ((uu____12680), (decls)))
end))
end))
in (

let encode_q_body = (fun env1 bs ps body -> (

let uu____12719 = (encode_binders FStar_Pervasives_Native.None bs env1)
in (match (uu____12719) with
| (vars, guards, env2, decls, uu____12758) -> begin
(

let uu____12771 = (

let uu____12784 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let uu____12836 = (

let uu____12847 = (FStar_All.pipe_right p (FStar_List.map (fun uu____12887 -> (match (uu____12887) with
| (t, uu____12901) -> begin
(encode_smt_pattern t (

let uu___121_12907 = env2
in {bindings = uu___121_12907.bindings; depth = uu___121_12907.depth; tcenv = uu___121_12907.tcenv; warn = uu___121_12907.warn; cache = uu___121_12907.cache; nolabels = uu___121_12907.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___121_12907.encode_non_total_function_typ; current_module_name = uu___121_12907.current_module_name}))
end))))
in (FStar_All.pipe_right uu____12847 FStar_List.unzip))
in (match (uu____12836) with
| (p1, decls1) -> begin
((p1), ((FStar_List.flatten decls1)))
end)))))
in (FStar_All.pipe_right uu____12784 FStar_List.unzip))
in (match (uu____12771) with
| (pats, decls') -> begin
(

let uu____13016 = (encode_formula body env2)
in (match (uu____13016) with
| (body1, decls'') -> begin
(

let guards1 = (match (pats) with
| (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (gf), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____13048; FStar_SMTEncoding_Term.rng = uu____13049})::[])::[] when (Prims.op_Equality (FStar_Ident.text_of_lid FStar_Parser_Const.guard_free) gf) -> begin
[]
end
| uu____13064 -> begin
guards
end)
in (

let uu____13069 = (FStar_SMTEncoding_Util.mk_and_l guards1)
in ((vars), (pats), (uu____13069), (body1), ((FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') decls''))))))
end))
end))
end)))
in ((debug1 phi);
(

let phi1 = (FStar_Syntax_Util.unascribe phi)
in (

let check_pattern_vars = (fun vars pats -> (

let pats1 = (FStar_All.pipe_right pats (FStar_List.map (fun uu____13129 -> (match (uu____13129) with
| (x, uu____13135) -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x)
end))))
in (match (pats1) with
| [] -> begin
()
end
| (hd1)::tl1 -> begin
(

let pat_vars = (

let uu____13143 = (FStar_Syntax_Free.names hd1)
in (FStar_List.fold_left (fun out x -> (

let uu____13155 = (FStar_Syntax_Free.names x)
in (FStar_Util.set_union out uu____13155))) uu____13143 tl1))
in (

let uu____13158 = (FStar_All.pipe_right vars (FStar_Util.find_opt (fun uu____13185 -> (match (uu____13185) with
| (b, uu____13191) -> begin
(

let uu____13192 = (FStar_Util.set_mem b pat_vars)
in (not (uu____13192)))
end))))
in (match (uu____13158) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (x, uu____13198) -> begin
(

let pos = (FStar_List.fold_left (fun out t -> (FStar_Range.union_ranges out t.FStar_Syntax_Syntax.pos)) hd1.FStar_Syntax_Syntax.pos tl1)
in (

let uu____13212 = (

let uu____13217 = (

let uu____13218 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "SMT pattern misses at least one bound variable: %s" uu____13218))
in ((FStar_Errors.Warning_SMTPatternMissingBoundVar), (uu____13217)))
in (FStar_Errors.log_issue pos uu____13212)))
end)))
end)))
in (

let uu____13219 = (FStar_Syntax_Util.destruct_typ_as_formula phi1)
in (match (uu____13219) with
| FStar_Pervasives_Native.None -> begin
(fallback phi1)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(

let uu____13228 = (FStar_All.pipe_right connectives (FStar_List.tryFind (fun uu____13286 -> (match (uu____13286) with
| (l, uu____13300) -> begin
(FStar_Ident.lid_equals op l)
end))))
in (match (uu____13228) with
| FStar_Pervasives_Native.None -> begin
(fallback phi1)
end
| FStar_Pervasives_Native.Some (uu____13333, f) -> begin
(f phi1.FStar_Syntax_Syntax.pos arms)
end))
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____13373 = (encode_q_body env vars pats body)
in (match (uu____13373) with
| (vars1, pats1, guard, body1, decls) -> begin
(

let tm = (

let uu____13418 = (

let uu____13429 = (FStar_SMTEncoding_Util.mkImp ((guard), (body1)))
in ((pats1), (vars1), (uu____13429)))
in (FStar_SMTEncoding_Term.mkForall uu____13418 phi1.FStar_Syntax_Syntax.pos))
in ((tm), (decls)))
end));
)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____13448 = (encode_q_body env vars pats body)
in (match (uu____13448) with
| (vars1, pats1, guard, body1, decls) -> begin
(

let uu____13492 = (

let uu____13493 = (

let uu____13504 = (FStar_SMTEncoding_Util.mkAnd ((guard), (body1)))
in ((pats1), (vars1), (uu____13504)))
in (FStar_SMTEncoding_Term.mkExists uu____13493 phi1.FStar_Syntax_Syntax.pos))
in ((uu____13492), (decls)))
end));
)
end))));
)))))))))))))))

type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  (FStar_SMTEncoding_Term.term * Prims.int * FStar_SMTEncoding_Term.decl Prims.list); is : FStar_Ident.lident  ->  Prims.bool}


let __proj__Mkprims_t__item__mk : prims_t  ->  FStar_Ident.lident  ->  Prims.string  ->  (FStar_SMTEncoding_Term.term * Prims.int * FStar_SMTEncoding_Term.decl Prims.list) = (fun projectee -> (match (projectee) with
| {mk = __fname__mk; is = __fname__is} -> begin
__fname__mk
end))


let __proj__Mkprims_t__item__is : prims_t  ->  FStar_Ident.lident  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {mk = __fname__mk; is = __fname__is} -> begin
__fname__is
end))


let prims : prims_t = (

let uu____13607 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____13607) with
| (asym, a) -> begin
(

let uu____13614 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____13614) with
| (xsym, x) -> begin
(

let uu____13621 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____13621) with
| (ysym, y) -> begin
(

let quant = (fun vars body x1 -> (

let xname_decl = (

let uu____13669 = (

let uu____13680 = (FStar_All.pipe_right vars (FStar_List.map FStar_Pervasives_Native.snd))
in ((x1), (uu____13680), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____13669))
in (

let xtok = (Prims.strcat x1 "@tok")
in (

let xtok_decl = FStar_SMTEncoding_Term.DeclFun (((xtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let xapp = (

let uu____13706 = (

let uu____13713 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((x1), (uu____13713)))
in (FStar_SMTEncoding_Util.mkApp uu____13706))
in (

let xtok1 = (FStar_SMTEncoding_Util.mkApp ((xtok), ([])))
in (

let xtok_app = (mk_Apply xtok1 vars)
in (

let uu____13726 = (

let uu____13729 = (

let uu____13732 = (

let uu____13735 = (

let uu____13736 = (

let uu____13743 = (

let uu____13744 = (

let uu____13755 = (FStar_SMTEncoding_Util.mkEq ((xapp), (body)))
in ((((xapp)::[])::[]), (vars), (uu____13755)))
in (FStar_SMTEncoding_Util.mkForall uu____13744))
in ((uu____13743), (FStar_Pervasives_Native.None), ((Prims.strcat "primitive_" x1))))
in (FStar_SMTEncoding_Util.mkAssume uu____13736))
in (

let uu____13772 = (

let uu____13775 = (

let uu____13776 = (

let uu____13783 = (

let uu____13784 = (

let uu____13795 = (FStar_SMTEncoding_Util.mkEq ((xtok_app), (xapp)))
in ((((xtok_app)::[])::[]), (vars), (uu____13795)))
in (FStar_SMTEncoding_Util.mkForall uu____13784))
in ((uu____13783), (FStar_Pervasives_Native.Some ("Name-token correspondence")), ((Prims.strcat "token_correspondence_" x1))))
in (FStar_SMTEncoding_Util.mkAssume uu____13776))
in (uu____13775)::[])
in (uu____13735)::uu____13772))
in (xtok_decl)::uu____13732)
in (xname_decl)::uu____13729)
in ((xtok1), ((FStar_List.length vars)), (uu____13726))))))))))
in (

let axy = (((asym), (FStar_SMTEncoding_Term.Term_sort)))::(((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let xy = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let qx = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let prims1 = (

let uu____13892 = (

let uu____13907 = (

let uu____13918 = (

let uu____13919 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13919))
in (quant axy uu____13918))
in ((FStar_Parser_Const.op_Eq), (uu____13907)))
in (

let uu____13930 = (

let uu____13947 = (

let uu____13962 = (

let uu____13973 = (

let uu____13974 = (

let uu____13975 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_SMTEncoding_Util.mkNot uu____13975))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13974))
in (quant axy uu____13973))
in ((FStar_Parser_Const.op_notEq), (uu____13962)))
in (

let uu____13986 = (

let uu____14003 = (

let uu____14018 = (

let uu____14029 = (

let uu____14030 = (

let uu____14031 = (

let uu____14036 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____14037 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____14036), (uu____14037))))
in (FStar_SMTEncoding_Util.mkLT uu____14031))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____14030))
in (quant xy uu____14029))
in ((FStar_Parser_Const.op_LT), (uu____14018)))
in (

let uu____14048 = (

let uu____14065 = (

let uu____14080 = (

let uu____14091 = (

let uu____14092 = (

let uu____14093 = (

let uu____14098 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____14099 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____14098), (uu____14099))))
in (FStar_SMTEncoding_Util.mkLTE uu____14093))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____14092))
in (quant xy uu____14091))
in ((FStar_Parser_Const.op_LTE), (uu____14080)))
in (

let uu____14110 = (

let uu____14127 = (

let uu____14142 = (

let uu____14153 = (

let uu____14154 = (

let uu____14155 = (

let uu____14160 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____14161 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____14160), (uu____14161))))
in (FStar_SMTEncoding_Util.mkGT uu____14155))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____14154))
in (quant xy uu____14153))
in ((FStar_Parser_Const.op_GT), (uu____14142)))
in (

let uu____14172 = (

let uu____14189 = (

let uu____14204 = (

let uu____14215 = (

let uu____14216 = (

let uu____14217 = (

let uu____14222 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____14223 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____14222), (uu____14223))))
in (FStar_SMTEncoding_Util.mkGTE uu____14217))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____14216))
in (quant xy uu____14215))
in ((FStar_Parser_Const.op_GTE), (uu____14204)))
in (

let uu____14234 = (

let uu____14251 = (

let uu____14266 = (

let uu____14277 = (

let uu____14278 = (

let uu____14279 = (

let uu____14284 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____14285 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____14284), (uu____14285))))
in (FStar_SMTEncoding_Util.mkSub uu____14279))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____14278))
in (quant xy uu____14277))
in ((FStar_Parser_Const.op_Subtraction), (uu____14266)))
in (

let uu____14296 = (

let uu____14313 = (

let uu____14328 = (

let uu____14339 = (

let uu____14340 = (

let uu____14341 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Util.mkMinus uu____14341))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____14340))
in (quant qx uu____14339))
in ((FStar_Parser_Const.op_Minus), (uu____14328)))
in (

let uu____14352 = (

let uu____14369 = (

let uu____14384 = (

let uu____14395 = (

let uu____14396 = (

let uu____14397 = (

let uu____14402 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____14403 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____14402), (uu____14403))))
in (FStar_SMTEncoding_Util.mkAdd uu____14397))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____14396))
in (quant xy uu____14395))
in ((FStar_Parser_Const.op_Addition), (uu____14384)))
in (

let uu____14414 = (

let uu____14431 = (

let uu____14446 = (

let uu____14457 = (

let uu____14458 = (

let uu____14459 = (

let uu____14464 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____14465 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____14464), (uu____14465))))
in (FStar_SMTEncoding_Util.mkMul uu____14459))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____14458))
in (quant xy uu____14457))
in ((FStar_Parser_Const.op_Multiply), (uu____14446)))
in (

let uu____14476 = (

let uu____14493 = (

let uu____14508 = (

let uu____14519 = (

let uu____14520 = (

let uu____14521 = (

let uu____14526 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____14527 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____14526), (uu____14527))))
in (FStar_SMTEncoding_Util.mkDiv uu____14521))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____14520))
in (quant xy uu____14519))
in ((FStar_Parser_Const.op_Division), (uu____14508)))
in (

let uu____14538 = (

let uu____14555 = (

let uu____14570 = (

let uu____14581 = (

let uu____14582 = (

let uu____14583 = (

let uu____14588 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____14589 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____14588), (uu____14589))))
in (FStar_SMTEncoding_Util.mkMod uu____14583))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____14582))
in (quant xy uu____14581))
in ((FStar_Parser_Const.op_Modulus), (uu____14570)))
in (

let uu____14600 = (

let uu____14617 = (

let uu____14632 = (

let uu____14643 = (

let uu____14644 = (

let uu____14645 = (

let uu____14650 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____14651 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____14650), (uu____14651))))
in (FStar_SMTEncoding_Util.mkAnd uu____14645))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____14644))
in (quant xy uu____14643))
in ((FStar_Parser_Const.op_And), (uu____14632)))
in (

let uu____14662 = (

let uu____14679 = (

let uu____14694 = (

let uu____14705 = (

let uu____14706 = (

let uu____14707 = (

let uu____14712 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____14713 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____14712), (uu____14713))))
in (FStar_SMTEncoding_Util.mkOr uu____14707))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____14706))
in (quant xy uu____14705))
in ((FStar_Parser_Const.op_Or), (uu____14694)))
in (

let uu____14724 = (

let uu____14741 = (

let uu____14756 = (

let uu____14767 = (

let uu____14768 = (

let uu____14769 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Util.mkNot uu____14769))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____14768))
in (quant qx uu____14767))
in ((FStar_Parser_Const.op_Negation), (uu____14756)))
in (uu____14741)::[])
in (uu____14679)::uu____14724))
in (uu____14617)::uu____14662))
in (uu____14555)::uu____14600))
in (uu____14493)::uu____14538))
in (uu____14431)::uu____14476))
in (uu____14369)::uu____14414))
in (uu____14313)::uu____14352))
in (uu____14251)::uu____14296))
in (uu____14189)::uu____14234))
in (uu____14127)::uu____14172))
in (uu____14065)::uu____14110))
in (uu____14003)::uu____14048))
in (uu____13947)::uu____13986))
in (uu____13892)::uu____13930))
in (

let mk1 = (fun l v1 -> (

let uu____15019 = (

let uu____15030 = (FStar_All.pipe_right prims1 (FStar_List.find (fun uu____15096 -> (match (uu____15096) with
| (l', uu____15112) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right uu____15030 (FStar_Option.map (fun uu____15184 -> (match (uu____15184) with
| (uu____15207, b) -> begin
(b v1)
end)))))
in (FStar_All.pipe_right uu____15019 FStar_Option.get)))
in (

let is = (fun l -> (FStar_All.pipe_right prims1 (FStar_Util.for_some (fun uu____15292 -> (match (uu____15292) with
| (l', uu____15308) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk1; is = is})))))))
end))
end))
end))


let pretype_axiom : env_t  ->  FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun env tapp vars -> (

let uu____15350 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____15350) with
| (xxsym, xx) -> begin
(

let uu____15357 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____15357) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let tapp_hash = (FStar_SMTEncoding_Term.hash_of_term tapp)
in (

let module_name = env.current_module_name
in (

let uu____15367 = (

let uu____15374 = (

let uu____15375 = (

let uu____15386 = (

let uu____15387 = (

let uu____15392 = (

let uu____15393 = (

let uu____15398 = (FStar_SMTEncoding_Util.mkApp (("PreType"), ((xx)::[])))
in ((tapp), (uu____15398)))
in (FStar_SMTEncoding_Util.mkEq uu____15393))
in ((xx_has_type), (uu____15392)))
in (FStar_SMTEncoding_Util.mkImp uu____15387))
in ((((xx_has_type)::[])::[]), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars), (uu____15386)))
in (FStar_SMTEncoding_Util.mkForall uu____15375))
in (

let uu____15423 = (

let uu____15424 = (

let uu____15425 = (

let uu____15426 = (FStar_Util.digest_of_string tapp_hash)
in (Prims.strcat "_pretyping_" uu____15426))
in (Prims.strcat module_name uu____15425))
in (varops.mk_unique uu____15424))
in ((uu____15374), (FStar_Pervasives_Native.Some ("pretyping")), (uu____15423))))
in (FStar_SMTEncoding_Util.mkAssume uu____15367)))))
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
in (

let uu____15462 = (

let uu____15463 = (

let uu____15470 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in ((uu____15470), (FStar_Pervasives_Native.Some ("unit typing")), ("unit_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____15463))
in (

let uu____15473 = (

let uu____15476 = (

let uu____15477 = (

let uu____15484 = (

let uu____15485 = (

let uu____15496 = (

let uu____15497 = (

let uu____15502 = (FStar_SMTEncoding_Util.mkEq ((x), (FStar_SMTEncoding_Term.mk_Term_unit)))
in ((typing_pred), (uu____15502)))
in (FStar_SMTEncoding_Util.mkImp uu____15497))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____15496)))
in (mkForall_fuel uu____15485))
in ((uu____15484), (FStar_Pervasives_Native.Some ("unit inversion")), ("unit_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____15477))
in (uu____15476)::[])
in (uu____15462)::uu____15473))))
in (

let mk_bool = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Bool_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____15544 = (

let uu____15545 = (

let uu____15552 = (

let uu____15553 = (

let uu____15564 = (

let uu____15569 = (

let uu____15572 = (FStar_SMTEncoding_Term.boxBool b)
in (uu____15572)::[])
in (uu____15569)::[])
in (

let uu____15577 = (

let uu____15578 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType uu____15578 tt))
in ((uu____15564), ((bb)::[]), (uu____15577))))
in (FStar_SMTEncoding_Util.mkForall uu____15553))
in ((uu____15552), (FStar_Pervasives_Native.Some ("bool typing")), ("bool_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____15545))
in (

let uu____15599 = (

let uu____15602 = (

let uu____15603 = (

let uu____15610 = (

let uu____15611 = (

let uu____15622 = (

let uu____15623 = (

let uu____15628 = (FStar_SMTEncoding_Term.mk_tester (FStar_Pervasives_Native.fst FStar_SMTEncoding_Term.boxBoolFun) x)
in ((typing_pred), (uu____15628)))
in (FStar_SMTEncoding_Util.mkImp uu____15623))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____15622)))
in (mkForall_fuel uu____15611))
in ((uu____15610), (FStar_Pervasives_Native.Some ("bool inversion")), ("bool_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____15603))
in (uu____15602)::[])
in (uu____15544)::uu____15599))))))
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

let precedes = (

let uu____15678 = (

let uu____15679 = (

let uu____15686 = (

let uu____15689 = (

let uu____15692 = (

let uu____15695 = (FStar_SMTEncoding_Term.boxInt a)
in (

let uu____15696 = (

let uu____15699 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____15699)::[])
in (uu____15695)::uu____15696))
in (tt)::uu____15692)
in (tt)::uu____15689)
in (("Prims.Precedes"), (uu____15686)))
in (FStar_SMTEncoding_Util.mkApp uu____15679))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15678))
in (

let precedes_y_x = (

let uu____15703 = (FStar_SMTEncoding_Util.mkApp (("Precedes"), ((y)::(x)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15703))
in (

let uu____15706 = (

let uu____15707 = (

let uu____15714 = (

let uu____15715 = (

let uu____15726 = (

let uu____15731 = (

let uu____15734 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____15734)::[])
in (uu____15731)::[])
in (

let uu____15739 = (

let uu____15740 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType uu____15740 tt))
in ((uu____15726), ((bb)::[]), (uu____15739))))
in (FStar_SMTEncoding_Util.mkForall uu____15715))
in ((uu____15714), (FStar_Pervasives_Native.Some ("int typing")), ("int_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____15707))
in (

let uu____15761 = (

let uu____15764 = (

let uu____15765 = (

let uu____15772 = (

let uu____15773 = (

let uu____15784 = (

let uu____15785 = (

let uu____15790 = (FStar_SMTEncoding_Term.mk_tester (FStar_Pervasives_Native.fst FStar_SMTEncoding_Term.boxIntFun) x)
in ((typing_pred), (uu____15790)))
in (FStar_SMTEncoding_Util.mkImp uu____15785))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____15784)))
in (mkForall_fuel uu____15773))
in ((uu____15772), (FStar_Pervasives_Native.Some ("int inversion")), ("int_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____15765))
in (

let uu____15815 = (

let uu____15818 = (

let uu____15819 = (

let uu____15826 = (

let uu____15827 = (

let uu____15838 = (

let uu____15839 = (

let uu____15844 = (

let uu____15845 = (

let uu____15848 = (

let uu____15851 = (

let uu____15854 = (

let uu____15855 = (

let uu____15860 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____15861 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____15860), (uu____15861))))
in (FStar_SMTEncoding_Util.mkGT uu____15855))
in (

let uu____15862 = (

let uu____15865 = (

let uu____15866 = (

let uu____15871 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____15872 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____15871), (uu____15872))))
in (FStar_SMTEncoding_Util.mkGTE uu____15866))
in (

let uu____15873 = (

let uu____15876 = (

let uu____15877 = (

let uu____15882 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____15883 = (FStar_SMTEncoding_Term.unboxInt x)
in ((uu____15882), (uu____15883))))
in (FStar_SMTEncoding_Util.mkLT uu____15877))
in (uu____15876)::[])
in (uu____15865)::uu____15873))
in (uu____15854)::uu____15862))
in (typing_pred_y)::uu____15851)
in (typing_pred)::uu____15848)
in (FStar_SMTEncoding_Util.mk_and_l uu____15845))
in ((uu____15844), (precedes_y_x)))
in (FStar_SMTEncoding_Util.mkImp uu____15839))
in ((((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[]), ((xx)::(yy)::[]), (uu____15838)))
in (mkForall_fuel uu____15827))
in ((uu____15826), (FStar_Pervasives_Native.Some ("well-founded ordering on nat (alt)")), ("well-founded-ordering-on-nat")))
in (FStar_SMTEncoding_Util.mkAssume uu____15819))
in (uu____15818)::[])
in (uu____15764)::uu____15815))
in (uu____15706)::uu____15761)))))))))))
in (

let mk_str = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.String_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____15929 = (

let uu____15930 = (

let uu____15937 = (

let uu____15938 = (

let uu____15949 = (

let uu____15954 = (

let uu____15957 = (FStar_SMTEncoding_Term.boxString b)
in (uu____15957)::[])
in (uu____15954)::[])
in (

let uu____15962 = (

let uu____15963 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType uu____15963 tt))
in ((uu____15949), ((bb)::[]), (uu____15962))))
in (FStar_SMTEncoding_Util.mkForall uu____15938))
in ((uu____15937), (FStar_Pervasives_Native.Some ("string typing")), ("string_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____15930))
in (

let uu____15984 = (

let uu____15987 = (

let uu____15988 = (

let uu____15995 = (

let uu____15996 = (

let uu____16007 = (

let uu____16008 = (

let uu____16013 = (FStar_SMTEncoding_Term.mk_tester (FStar_Pervasives_Native.fst FStar_SMTEncoding_Term.boxStringFun) x)
in ((typing_pred), (uu____16013)))
in (FStar_SMTEncoding_Util.mkImp uu____16008))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____16007)))
in (mkForall_fuel uu____15996))
in ((uu____15995), (FStar_Pervasives_Native.Some ("string inversion")), ("string_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____15988))
in (uu____15987)::[])
in (uu____15929)::uu____15984))))))
in (

let mk_true_interp = (fun env nm true_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((true_tm)::[])))
in ((FStar_SMTEncoding_Util.mkAssume ((valid), (FStar_Pervasives_Native.Some ("True interpretation")), ("true_interp"))))::[]))
in (

let mk_false_interp = (fun env nm false_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((false_tm)::[])))
in (

let uu____16066 = (

let uu____16067 = (

let uu____16074 = (FStar_SMTEncoding_Util.mkIff ((FStar_SMTEncoding_Util.mkFalse), (valid)))
in ((uu____16074), (FStar_Pervasives_Native.Some ("False interpretation")), ("false_interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16067))
in (uu____16066)::[])))
in (

let mk_and_interp = (fun env conj uu____16086 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let l_and_a_b = (FStar_SMTEncoding_Util.mkApp ((conj), ((a)::(b)::[])))
in (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((l_and_a_b)::[])))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____16111 = (

let uu____16112 = (

let uu____16119 = (

let uu____16120 = (

let uu____16131 = (

let uu____16132 = (

let uu____16137 = (FStar_SMTEncoding_Util.mkAnd ((valid_a), (valid_b)))
in ((uu____16137), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____16132))
in ((((l_and_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____16131)))
in (FStar_SMTEncoding_Util.mkForall uu____16120))
in ((uu____16119), (FStar_Pervasives_Native.Some ("/\\ interpretation")), ("l_and-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16112))
in (uu____16111)::[]))))))))))
in (

let mk_or_interp = (fun env disj uu____16175 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let l_or_a_b = (FStar_SMTEncoding_Util.mkApp ((disj), ((a)::(b)::[])))
in (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((l_or_a_b)::[])))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____16200 = (

let uu____16201 = (

let uu____16208 = (

let uu____16209 = (

let uu____16220 = (

let uu____16221 = (

let uu____16226 = (FStar_SMTEncoding_Util.mkOr ((valid_a), (valid_b)))
in ((uu____16226), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____16221))
in ((((l_or_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____16220)))
in (FStar_SMTEncoding_Util.mkForall uu____16209))
in ((uu____16208), (FStar_Pervasives_Native.Some ("\\/ interpretation")), ("l_or-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16201))
in (uu____16200)::[]))))))))))
in (

let mk_eq2_interp = (fun env eq2 tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let xx1 = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let yy1 = (("y"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let x1 = (FStar_SMTEncoding_Util.mkFreeV xx1)
in (

let y1 = (FStar_SMTEncoding_Util.mkFreeV yy1)
in (

let eq2_x_y = (FStar_SMTEncoding_Util.mkApp ((eq2), ((a)::(x1)::(y1)::[])))
in (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((eq2_x_y)::[])))
in (

let uu____16289 = (

let uu____16290 = (

let uu____16297 = (

let uu____16298 = (

let uu____16309 = (

let uu____16310 = (

let uu____16315 = (FStar_SMTEncoding_Util.mkEq ((x1), (y1)))
in ((uu____16315), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____16310))
in ((((eq2_x_y)::[])::[]), ((aa)::(xx1)::(yy1)::[]), (uu____16309)))
in (FStar_SMTEncoding_Util.mkForall uu____16298))
in ((uu____16297), (FStar_Pervasives_Native.Some ("Eq2 interpretation")), ("eq2-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16290))
in (uu____16289)::[]))))))))))
in (

let mk_eq3_interp = (fun env eq3 tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let xx1 = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let yy1 = (("y"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let x1 = (FStar_SMTEncoding_Util.mkFreeV xx1)
in (

let y1 = (FStar_SMTEncoding_Util.mkFreeV yy1)
in (

let eq3_x_y = (FStar_SMTEncoding_Util.mkApp ((eq3), ((a)::(b)::(x1)::(y1)::[])))
in (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((eq3_x_y)::[])))
in (

let uu____16388 = (

let uu____16389 = (

let uu____16396 = (

let uu____16397 = (

let uu____16408 = (

let uu____16409 = (

let uu____16414 = (FStar_SMTEncoding_Util.mkEq ((x1), (y1)))
in ((uu____16414), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____16409))
in ((((eq3_x_y)::[])::[]), ((aa)::(bb)::(xx1)::(yy1)::[]), (uu____16408)))
in (FStar_SMTEncoding_Util.mkForall uu____16397))
in ((uu____16396), (FStar_Pervasives_Native.Some ("Eq3 interpretation")), ("eq3-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16389))
in (uu____16388)::[]))))))))))))
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

let l_imp_a_b = (FStar_SMTEncoding_Util.mkApp ((imp), ((a)::(b)::[])))
in (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((l_imp_a_b)::[])))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____16485 = (

let uu____16486 = (

let uu____16493 = (

let uu____16494 = (

let uu____16505 = (

let uu____16506 = (

let uu____16511 = (FStar_SMTEncoding_Util.mkImp ((valid_a), (valid_b)))
in ((uu____16511), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____16506))
in ((((l_imp_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____16505)))
in (FStar_SMTEncoding_Util.mkForall uu____16494))
in ((uu____16493), (FStar_Pervasives_Native.Some ("==> interpretation")), ("l_imp-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16486))
in (uu____16485)::[]))))))))))
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

let l_iff_a_b = (FStar_SMTEncoding_Util.mkApp ((iff), ((a)::(b)::[])))
in (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((l_iff_a_b)::[])))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____16574 = (

let uu____16575 = (

let uu____16582 = (

let uu____16583 = (

let uu____16594 = (

let uu____16595 = (

let uu____16600 = (FStar_SMTEncoding_Util.mkIff ((valid_a), (valid_b)))
in ((uu____16600), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____16595))
in ((((l_iff_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____16594)))
in (FStar_SMTEncoding_Util.mkForall uu____16583))
in ((uu____16582), (FStar_Pervasives_Native.Some ("<==> interpretation")), ("l_iff-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16575))
in (uu____16574)::[]))))))))))
in (

let mk_not_interp = (fun env l_not tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let l_not_a = (FStar_SMTEncoding_Util.mkApp ((l_not), ((a)::[])))
in (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((l_not_a)::[])))
in (

let not_valid_a = (

let uu____16652 = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____16652))
in (

let uu____16655 = (

let uu____16656 = (

let uu____16663 = (

let uu____16664 = (

let uu____16675 = (FStar_SMTEncoding_Util.mkIff ((not_valid_a), (valid)))
in ((((l_not_a)::[])::[]), ((aa)::[]), (uu____16675)))
in (FStar_SMTEncoding_Util.mkForall uu____16664))
in ((uu____16663), (FStar_Pervasives_Native.Some ("not interpretation")), ("l_not-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16656))
in (uu____16655)::[])))))))
in (

let mk_forall_interp = (fun env for_all1 tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let xx1 = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let x1 = (FStar_SMTEncoding_Util.mkFreeV xx1)
in (

let l_forall_a_b = (FStar_SMTEncoding_Util.mkApp ((for_all1), ((a)::(b)::[])))
in (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((l_forall_a_b)::[])))
in (

let valid_b_x = (

let uu____16735 = (

let uu____16742 = (

let uu____16745 = (FStar_SMTEncoding_Util.mk_ApplyTT b x1)
in (uu____16745)::[])
in (("Valid"), (uu____16742)))
in (FStar_SMTEncoding_Util.mkApp uu____16735))
in (

let uu____16748 = (

let uu____16749 = (

let uu____16756 = (

let uu____16757 = (

let uu____16768 = (

let uu____16769 = (

let uu____16774 = (

let uu____16775 = (

let uu____16786 = (

let uu____16791 = (

let uu____16794 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in (uu____16794)::[])
in (uu____16791)::[])
in (

let uu____16799 = (

let uu____16800 = (

let uu____16805 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in ((uu____16805), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp uu____16800))
in ((uu____16786), ((xx1)::[]), (uu____16799))))
in (FStar_SMTEncoding_Util.mkForall uu____16775))
in ((uu____16774), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____16769))
in ((((l_forall_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____16768)))
in (FStar_SMTEncoding_Util.mkForall uu____16757))
in ((uu____16756), (FStar_Pervasives_Native.Some ("forall interpretation")), ("forall-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16749))
in (uu____16748)::[])))))))))))
in (

let mk_exists_interp = (fun env for_some1 tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let xx1 = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let x1 = (FStar_SMTEncoding_Util.mkFreeV xx1)
in (

let l_exists_a_b = (FStar_SMTEncoding_Util.mkApp ((for_some1), ((a)::(b)::[])))
in (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((l_exists_a_b)::[])))
in (

let valid_b_x = (

let uu____16887 = (

let uu____16894 = (

let uu____16897 = (FStar_SMTEncoding_Util.mk_ApplyTT b x1)
in (uu____16897)::[])
in (("Valid"), (uu____16894)))
in (FStar_SMTEncoding_Util.mkApp uu____16887))
in (

let uu____16900 = (

let uu____16901 = (

let uu____16908 = (

let uu____16909 = (

let uu____16920 = (

let uu____16921 = (

let uu____16926 = (

let uu____16927 = (

let uu____16938 = (

let uu____16943 = (

let uu____16946 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in (uu____16946)::[])
in (uu____16943)::[])
in (

let uu____16951 = (

let uu____16952 = (

let uu____16957 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in ((uu____16957), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp uu____16952))
in ((uu____16938), ((xx1)::[]), (uu____16951))))
in (FStar_SMTEncoding_Util.mkExists uu____16927))
in ((uu____16926), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____16921))
in ((((l_exists_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____16920)))
in (FStar_SMTEncoding_Util.mkForall uu____16909))
in ((uu____16908), (FStar_Pervasives_Native.Some ("exists interpretation")), ("exists-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16901))
in (uu____16900)::[])))))))))))
in (

let mk_range_interp = (fun env range tt -> (

let range_ty = (FStar_SMTEncoding_Util.mkApp ((range), ([])))
in (

let uu____17017 = (

let uu____17018 = (

let uu____17025 = (

let uu____17026 = (FStar_SMTEncoding_Term.mk_Range_const ())
in (FStar_SMTEncoding_Term.mk_HasTypeZ uu____17026 range_ty))
in (

let uu____17027 = (varops.mk_unique "typing_range_const")
in ((uu____17025), (FStar_Pervasives_Native.Some ("Range_const typing")), (uu____17027))))
in (FStar_SMTEncoding_Util.mkAssume uu____17018))
in (uu____17017)::[])))
in (

let mk_inversion_axiom = (fun env inversion tt -> (

let tt1 = (("t"), (FStar_SMTEncoding_Term.Term_sort))
in (

let t = (FStar_SMTEncoding_Util.mkFreeV tt1)
in (

let xx1 = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let x1 = (FStar_SMTEncoding_Util.mkFreeV xx1)
in (

let inversion_t = (FStar_SMTEncoding_Util.mkApp ((inversion), ((t)::[])))
in (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((inversion_t)::[])))
in (

let body = (

let hastypeZ = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 t)
in (

let hastypeS = (

let uu____17061 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1"))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel uu____17061 x1 t))
in (

let uu____17062 = (

let uu____17073 = (FStar_SMTEncoding_Util.mkImp ((hastypeZ), (hastypeS)))
in ((((hastypeZ)::[])::[]), ((xx1)::[]), (uu____17073)))
in (FStar_SMTEncoding_Util.mkForall uu____17062))))
in (

let uu____17096 = (

let uu____17097 = (

let uu____17104 = (

let uu____17105 = (

let uu____17116 = (FStar_SMTEncoding_Util.mkImp ((valid), (body)))
in ((((inversion_t)::[])::[]), ((tt1)::[]), (uu____17116)))
in (FStar_SMTEncoding_Util.mkForall uu____17105))
in ((uu____17104), (FStar_Pervasives_Native.Some ("inversion interpretation")), ("inversion-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____17097))
in (uu____17096)::[])))))))))
in (

let mk_with_type_axiom = (fun env with_type1 tt -> (

let tt1 = (("t"), (FStar_SMTEncoding_Term.Term_sort))
in (

let t = (FStar_SMTEncoding_Util.mkFreeV tt1)
in (

let ee = (("e"), (FStar_SMTEncoding_Term.Term_sort))
in (

let e = (FStar_SMTEncoding_Util.mkFreeV ee)
in (

let with_type_t_e = (FStar_SMTEncoding_Util.mkApp ((with_type1), ((t)::(e)::[])))
in (

let uu____17166 = (

let uu____17167 = (

let uu____17174 = (

let uu____17175 = (

let uu____17190 = (

let uu____17191 = (

let uu____17196 = (FStar_SMTEncoding_Util.mkEq ((with_type_t_e), (e)))
in (

let uu____17197 = (FStar_SMTEncoding_Term.mk_HasType with_type_t_e t)
in ((uu____17196), (uu____17197))))
in (FStar_SMTEncoding_Util.mkAnd uu____17191))
in ((((with_type_t_e)::[])::[]), (FStar_Pervasives_Native.Some ((Prims.parse_int "0"))), ((tt1)::(ee)::[]), (uu____17190)))
in (FStar_SMTEncoding_Util.mkForall' uu____17175))
in ((uu____17174), (FStar_Pervasives_Native.Some ("with_type primitive axiom")), ("@with_type_primitive_axiom")))
in (FStar_SMTEncoding_Util.mkAssume uu____17167))
in (uu____17166)::[])))))))
in (

let prims1 = (((FStar_Parser_Const.unit_lid), (mk_unit)))::(((FStar_Parser_Const.bool_lid), (mk_bool)))::(((FStar_Parser_Const.int_lid), (mk_int)))::(((FStar_Parser_Const.string_lid), (mk_str)))::(((FStar_Parser_Const.true_lid), (mk_true_interp)))::(((FStar_Parser_Const.false_lid), (mk_false_interp)))::(((FStar_Parser_Const.and_lid), (mk_and_interp)))::(((FStar_Parser_Const.or_lid), (mk_or_interp)))::(((FStar_Parser_Const.eq2_lid), (mk_eq2_interp)))::(((FStar_Parser_Const.t_eq2_lid), (mk_eq2_interp)))::(((FStar_Parser_Const.eq3_lid), (mk_eq3_interp)))::(((FStar_Parser_Const.imp_lid), (mk_imp_interp)))::(((FStar_Parser_Const.iff_lid), (mk_iff_interp)))::(((FStar_Parser_Const.not_lid), (mk_not_interp)))::(((FStar_Parser_Const.forall_lid), (mk_forall_interp)))::(((FStar_Parser_Const.t_forall_lid), (mk_forall_interp)))::(((FStar_Parser_Const.exists_lid), (mk_exists_interp)))::(((FStar_Parser_Const.range_lid), (mk_range_interp)))::(((FStar_Parser_Const.inversion_lid), (mk_inversion_axiom)))::(((FStar_Parser_Const.with_type_lid), (mk_with_type_axiom)))::[]
in (fun env t s tt -> (

let uu____17575 = (FStar_Util.find_opt (fun uu____17601 -> (match (uu____17601) with
| (l, uu____17613) -> begin
(FStar_Ident.lid_equals l t)
end)) prims1)
in (match (uu____17575) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (uu____17638, f) -> begin
(f env s tt)
end))))))))))))))))))))))))))


let encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____17674 = (encode_function_type_as_formula t env)
in (match (uu____17674) with
| (form, decls) -> begin
(FStar_List.append decls (((FStar_SMTEncoding_Util.mkAssume ((form), (FStar_Pervasives_Native.Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str))), ((Prims.strcat "lemma_" lid.FStar_Ident.str)))))::[]))
end))))


let encode_free_var : Prims.bool  ->  env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun uninterpreted env fv tt t_norm quals -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____17714 = (((

let uu____17717 = ((FStar_Syntax_Util.is_pure_or_ghost_function t_norm) || (FStar_TypeChecker_Env.is_reifiable_function env.tcenv t_norm))
in (FStar_All.pipe_left Prims.op_Negation uu____17717)) || (FStar_Syntax_Util.is_lemma t_norm)) || uninterpreted)
in (match (uu____17714) with
| true -> begin
(

let arg_sorts = (

let uu____17727 = (

let uu____17728 = (FStar_Syntax_Subst.compress t_norm)
in uu____17728.FStar_Syntax_Syntax.n)
in (match (uu____17727) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____17734) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun uu____17764 -> FStar_SMTEncoding_Term.Term_sort)))
end
| uu____17769 -> begin
[]
end))
in (

let arity = (FStar_List.length arg_sorts)
in (

let uu____17771 = (new_term_constant_and_tok_from_lid env lid arity)
in (match (uu____17771) with
| (vname, vtok, env1) -> begin
(

let d = FStar_SMTEncoding_Term.DeclFun (((vname), (arg_sorts), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Uninterpreted function symbol for impure function"))))
in (

let dd = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Uninterpreted name for impure function"))))
in (((d)::(dd)::[]), (env1))))
end))))
end
| uu____17803 -> begin
(

let uu____17804 = (prims.is lid)
in (match (uu____17804) with
| true -> begin
(

let vname = (varops.new_fvar lid)
in (

let uu____17812 = (prims.mk lid vname)
in (match (uu____17812) with
| (tok, arity, definition) -> begin
(

let env1 = (push_free_var env lid arity vname (FStar_Pervasives_Native.Some (tok)))
in ((definition), (env1)))
end)))
end
| uu____17837 -> begin
(

let encode_non_total_function_typ = (Prims.op_disEquality lid.FStar_Ident.nsstr "Prims")
in (

let uu____17839 = (

let uu____17850 = (curried_arrow_formals_comp t_norm)
in (match (uu____17850) with
| (args, comp) -> begin
(

let comp1 = (

let uu____17868 = (FStar_TypeChecker_Env.is_reifiable_comp env.tcenv comp)
in (match (uu____17868) with
| true -> begin
(

let uu____17869 = (FStar_TypeChecker_Env.reify_comp (

let uu___122_17872 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___122_17872.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___122_17872.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___122_17872.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___122_17872.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___122_17872.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___122_17872.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___122_17872.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___122_17872.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___122_17872.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___122_17872.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___122_17872.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___122_17872.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___122_17872.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___122_17872.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___122_17872.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___122_17872.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___122_17872.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___122_17872.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___122_17872.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___122_17872.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___122_17872.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___122_17872.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___122_17872.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___122_17872.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___122_17872.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___122_17872.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___122_17872.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___122_17872.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___122_17872.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___122_17872.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___122_17872.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___122_17872.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___122_17872.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___122_17872.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___122_17872.FStar_TypeChecker_Env.dep_graph}) comp FStar_Syntax_Syntax.U_unknown)
in (FStar_Syntax_Syntax.mk_Total uu____17869))
end
| uu____17873 -> begin
comp
end))
in (match (encode_non_total_function_typ) with
| true -> begin
(

let uu____17884 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp1)
in ((args), (uu____17884)))
end
| uu____17897 -> begin
((args), (((FStar_Pervasives_Native.None), ((FStar_Syntax_Util.comp_result comp1)))))
end))
end))
in (match (uu____17839) with
| (formals, (pre_opt, res_t)) -> begin
(

let arity = (FStar_List.length formals)
in (

let uu____17934 = (new_term_constant_and_tok_from_lid env lid arity)
in (match (uu____17934) with
| (vname, vtok, env1) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
end
| uu____17959 -> begin
(FStar_SMTEncoding_Util.mkApp ((vtok), ([])))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun uu___94_18001 -> (match (uu___94_18001) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(

let uu____18005 = (FStar_Util.prefix vars)
in (match (uu____18005) with
| (uu____18026, (xxsym, uu____18028)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____18046 = (

let uu____18047 = (

let uu____18054 = (

let uu____18055 = (

let uu____18066 = (

let uu____18067 = (

let uu____18072 = (

let uu____18073 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____18073))
in ((vapp), (uu____18072)))
in (FStar_SMTEncoding_Util.mkEq uu____18067))
in ((((vapp)::[])::[]), (vars), (uu____18066)))
in (FStar_SMTEncoding_Util.mkForall uu____18055))
in ((uu____18054), (FStar_Pervasives_Native.Some ("Discriminator equation")), ((Prims.strcat "disc_equation_" (escape d.FStar_Ident.str)))))
in (FStar_SMTEncoding_Util.mkAssume uu____18047))
in (uu____18046)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(

let uu____18092 = (FStar_Util.prefix vars)
in (match (uu____18092) with
| (uu____18113, (xxsym, uu____18115)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f1 = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (

let tp_name = (mk_term_projector_name d f1)
in (

let prim_app = (FStar_SMTEncoding_Util.mkApp ((tp_name), ((xx)::[])))
in (

let uu____18138 = (

let uu____18139 = (

let uu____18146 = (

let uu____18147 = (

let uu____18158 = (FStar_SMTEncoding_Util.mkEq ((vapp), (prim_app)))
in ((((vapp)::[])::[]), (vars), (uu____18158)))
in (FStar_SMTEncoding_Util.mkForall uu____18147))
in ((uu____18146), (FStar_Pervasives_Native.Some ("Projector equation")), ((Prims.strcat "proj_equation_" tp_name))))
in (FStar_SMTEncoding_Util.mkAssume uu____18139))
in (uu____18138)::[])))))
end))
end
| uu____18175 -> begin
[]
end)))))
in (

let uu____18176 = (encode_binders FStar_Pervasives_Native.None formals env1)
in (match (uu____18176) with
| (vars, guards, env', decls1, uu____18203) -> begin
(

let uu____18216 = (match (pre_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____18225 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____18225), (decls1)))
end
| FStar_Pervasives_Native.Some (p) -> begin
(

let uu____18227 = (encode_formula p env')
in (match (uu____18227) with
| (g, ds) -> begin
(

let uu____18238 = (FStar_SMTEncoding_Util.mk_and_l ((g)::guards))
in ((uu____18238), ((FStar_List.append decls1 ds))))
end))
end)
in (match (uu____18216) with
| (guard, decls11) -> begin
(

let vtok_app = (mk_Apply vtok_tm vars)
in (

let vapp = (

let uu____18251 = (

let uu____18258 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((vname), (uu____18258)))
in (FStar_SMTEncoding_Util.mkApp uu____18251))
in (

let uu____18267 = (

let vname_decl = (

let uu____18275 = (

let uu____18286 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____18296 -> FStar_SMTEncoding_Term.Term_sort)))
in ((vname), (uu____18286), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____18275))
in (

let uu____18305 = (

let env2 = (

let uu___123_18311 = env1
in {bindings = uu___123_18311.bindings; depth = uu___123_18311.depth; tcenv = uu___123_18311.tcenv; warn = uu___123_18311.warn; cache = uu___123_18311.cache; nolabels = uu___123_18311.nolabels; use_zfuel_name = uu___123_18311.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = uu___123_18311.current_module_name})
in (

let uu____18312 = (

let uu____18313 = (head_normal env2 tt)
in (not (uu____18313)))
in (match (uu____18312) with
| true -> begin
(encode_term_pred FStar_Pervasives_Native.None tt env2 vtok_tm)
end
| uu____18318 -> begin
(encode_term_pred FStar_Pervasives_Native.None t_norm env2 vtok_tm)
end)))
in (match (uu____18305) with
| (tok_typing, decls2) -> begin
(

let tok_typing1 = (match (formals) with
| (uu____18328)::uu____18329 -> begin
(

let ff = (("ty"), (FStar_SMTEncoding_Term.Term_sort))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV ff)
in (

let vtok_app_l = (mk_Apply vtok_tm ((ff)::[]))
in (

let vtok_app_r = (mk_Apply f ((((vtok), (FStar_SMTEncoding_Term.Term_sort)))::[]))
in (

let guarded_tok_typing = (

let uu____18369 = (

let uu____18380 = (FStar_SMTEncoding_Term.mk_NoHoist f tok_typing)
in ((((vtok_app_l)::[])::((vtok_app_r)::[])::[]), ((ff)::[]), (uu____18380)))
in (FStar_SMTEncoding_Util.mkForall uu____18369))
in (FStar_SMTEncoding_Util.mkAssume ((guarded_tok_typing), (FStar_Pervasives_Native.Some ("function token typing")), ((Prims.strcat "function_token_typing_" vname)))))))))
end
| uu____18407 -> begin
(FStar_SMTEncoding_Util.mkAssume ((tok_typing), (FStar_Pervasives_Native.Some ("function token typing")), ((Prims.strcat "function_token_typing_" vname))))
end)
in (

let uu____18410 = (match (formals) with
| [] -> begin
(

let uu____18427 = (

let uu____18428 = (

let uu____18431 = (FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left (fun _0_41 -> FStar_Pervasives_Native.Some (_0_41)) uu____18431))
in (push_free_var env1 lid arity vname uu____18428))
in (((FStar_List.append decls2 ((tok_typing1)::[]))), (uu____18427)))
end
| uu____18440 -> begin
(

let vtok_decl = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let name_tok_corr = (

let uu____18447 = (

let uu____18454 = (

let uu____18455 = (

let uu____18466 = (FStar_SMTEncoding_Util.mkEq ((vtok_app), (vapp)))
in ((((vtok_app)::[])::((vapp)::[])::[]), (vars), (uu____18466)))
in (FStar_SMTEncoding_Util.mkForall uu____18455))
in ((uu____18454), (FStar_Pervasives_Native.Some ("Name-token correspondence")), ((Prims.strcat "token_correspondence_" vname))))
in (FStar_SMTEncoding_Util.mkAssume uu____18447))
in (((FStar_List.append decls2 ((vtok_decl)::(name_tok_corr)::(tok_typing1)::[]))), (env1))))
end)
in (match (uu____18410) with
| (tok_decl, env2) -> begin
(((vname_decl)::tok_decl), (env2))
end)))
end)))
in (match (uu____18267) with
| (decls2, env2) -> begin
(

let uu____18509 = (

let res_t1 = (FStar_Syntax_Subst.compress res_t)
in (

let uu____18517 = (encode_term res_t1 env')
in (match (uu____18517) with
| (encoded_res_t, decls) -> begin
(

let uu____18530 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in ((encoded_res_t), (uu____18530), (decls)))
end)))
in (match (uu____18509) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (

let uu____18541 = (

let uu____18548 = (

let uu____18549 = (

let uu____18560 = (FStar_SMTEncoding_Util.mkImp ((guard), (ty_pred)))
in ((((vapp)::[])::[]), (vars), (uu____18560)))
in (FStar_SMTEncoding_Util.mkForall uu____18549))
in ((uu____18548), (FStar_Pervasives_Native.Some ("free var typing")), ((Prims.strcat "typing_" vname))))
in (FStar_SMTEncoding_Util.mkAssume uu____18541))
in (

let freshness = (

let uu____18576 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New))
in (match (uu____18576) with
| true -> begin
(

let uu____18581 = (

let uu____18582 = (

let uu____18593 = (FStar_All.pipe_right vars (FStar_List.map FStar_Pervasives_Native.snd))
in (

let uu____18604 = (varops.next_id ())
in ((vname), (uu____18593), (FStar_SMTEncoding_Term.Term_sort), (uu____18604))))
in (FStar_SMTEncoding_Term.fresh_constructor uu____18582))
in (

let uu____18607 = (

let uu____18610 = (pretype_axiom env2 vapp vars)
in (uu____18610)::[])
in (uu____18581)::uu____18607))
end
| uu____18611 -> begin
[]
end))
in (

let g = (

let uu____18615 = (

let uu____18618 = (

let uu____18621 = (

let uu____18624 = (

let uu____18627 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::uu____18627)
in (FStar_List.append freshness uu____18624))
in (FStar_List.append decls3 uu____18621))
in (FStar_List.append decls2 uu____18618))
in (FStar_List.append decls11 uu____18615))
in ((g), (env2)))))
end))
end))))
end))
end))))
end)))
end)))
end))
end))))


let declare_top_level_let : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (fvar_binding * FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env x t t_norm -> (

let uu____18652 = (try_lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____18652) with
| FStar_Pervasives_Native.None -> begin
(

let uu____18663 = (encode_free_var false env x t t_norm [])
in (match (uu____18663) with
| (decls, env1) -> begin
(

let fvb = (lookup_lid env1 x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in ((fvb), (decls), (env1)))
end))
end
| FStar_Pervasives_Native.Some (fvb) -> begin
((fvb), ([]), (env))
end)))


let encode_top_level_val : Prims.bool  ->  env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun uninterpreted env lid t quals -> (

let tt = (norm env t)
in (

let uu____18716 = (encode_free_var uninterpreted env lid t tt quals)
in (match (uu____18716) with
| (decls, env1) -> begin
(

let uu____18735 = (FStar_Syntax_Util.is_smt_lemma t)
in (match (uu____18735) with
| true -> begin
(

let uu____18742 = (

let uu____18745 = (encode_smt_lemma env1 lid tt)
in (FStar_List.append decls uu____18745))
in ((uu____18742), (env1)))
end
| uu____18750 -> begin
((decls), (env1))
end))
end))))


let encode_top_level_vals : env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____18797 lb -> (match (uu____18797) with
| (decls, env1) -> begin
(

let uu____18817 = (

let uu____18824 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val false env1 uu____18824 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (uu____18817) with
| (decls', env2) -> begin
(((FStar_List.append decls decls')), (env2))
end))
end)) (([]), (env)))))


let is_tactic : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let fstar_tactics_tactic_lid = (FStar_Parser_Const.p2l (("FStar")::("Tactics")::("tactic")::[]))
in (

let uu____18845 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____18845) with
| (hd1, args) -> begin
(

let uu____18882 = (

let uu____18883 = (FStar_Syntax_Util.un_uinst hd1)
in uu____18883.FStar_Syntax_Syntax.n)
in (match (uu____18882) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____18887, c) -> begin
(

let effect_name = (FStar_Syntax_Util.comp_effect_name c)
in (FStar_Util.starts_with "FStar.Tactics" effect_name.FStar_Ident.str))
end
| uu____18906 -> begin
false
end))
end))))


let encode_top_level_let : env_t  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env uu____18928 quals -> (match (uu____18928) with
| (is_rec, bindings) -> begin
(

let eta_expand1 = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let uu____19004 = (FStar_Util.first_N nbinders formals)
in (match (uu____19004) with
| (formals1, extra_formals) -> begin
(

let subst1 = (FStar_List.map2 (fun uu____19085 uu____19086 -> (match (((uu____19085), (uu____19086))) with
| ((formal, uu____19104), (binder, uu____19106)) -> begin
(

let uu____19115 = (

let uu____19122 = (FStar_Syntax_Syntax.bv_to_name binder)
in ((formal), (uu____19122)))
in FStar_Syntax_Syntax.NT (uu____19115))
end)) formals1 binders)
in (

let extra_formals1 = (

let uu____19130 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun uu____19161 -> (match (uu____19161) with
| (x, i) -> begin
(

let uu____19172 = (

let uu___124_19173 = x
in (

let uu____19174 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___124_19173.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___124_19173.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____19174}))
in ((uu____19172), (i)))
end))))
in (FStar_All.pipe_right uu____19130 FStar_Syntax_Util.name_binders))
in (

let body1 = (

let uu____19192 = (

let uu____19193 = (FStar_Syntax_Subst.compress body)
in (

let uu____19194 = (

let uu____19195 = (FStar_Syntax_Util.args_of_binders extra_formals1)
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____19195))
in (FStar_Syntax_Syntax.extend_app_n uu____19193 uu____19194)))
in (uu____19192 FStar_Pervasives_Native.None body.FStar_Syntax_Syntax.pos))
in (((FStar_List.append binders extra_formals1)), (body1)))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (

let get_result_type = (fun c -> (

let uu____19256 = (FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c)
in (match (uu____19256) with
| true -> begin
(FStar_TypeChecker_Env.reify_comp (

let uu___125_19259 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___125_19259.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___125_19259.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___125_19259.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___125_19259.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___125_19259.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___125_19259.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___125_19259.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___125_19259.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___125_19259.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___125_19259.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___125_19259.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___125_19259.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___125_19259.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___125_19259.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___125_19259.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___125_19259.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___125_19259.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___125_19259.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___125_19259.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___125_19259.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___125_19259.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___125_19259.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___125_19259.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___125_19259.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___125_19259.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___125_19259.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___125_19259.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___125_19259.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___125_19259.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___125_19259.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___125_19259.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___125_19259.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___125_19259.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___125_19259.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___125_19259.FStar_TypeChecker_Env.dep_graph}) c FStar_Syntax_Syntax.U_unknown)
end
| uu____19260 -> begin
(FStar_Syntax_Util.comp_result c)
end)))
in (

let rec aux = (fun norm1 t_norm1 -> (

let uu____19292 = (FStar_Syntax_Util.abs_formals e)
in (match (uu____19292) with
| (binders, body, lopt) -> begin
(match (binders) with
| (uu____19356)::uu____19357 -> begin
(

let uu____19372 = (

let uu____19373 = (

let uu____19376 = (FStar_Syntax_Subst.compress t_norm1)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____19376))
in uu____19373.FStar_Syntax_Syntax.n)
in (match (uu____19372) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____19419 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____19419) with
| (formals1, c1) -> begin
(

let nformals = (FStar_List.length formals1)
in (

let nbinders = (FStar_List.length binders)
in (

let tres = (get_result_type c1)
in (

let uu____19461 = ((nformals < nbinders) && (FStar_Syntax_Util.is_total_comp c1))
in (match (uu____19461) with
| true -> begin
(

let uu____19496 = (FStar_Util.first_N nformals binders)
in (match (uu____19496) with
| (bs0, rest) -> begin
(

let c2 = (

let subst1 = (FStar_List.map2 (fun uu____19590 uu____19591 -> (match (((uu____19590), (uu____19591))) with
| ((x, uu____19609), (b, uu____19611)) -> begin
(

let uu____19620 = (

let uu____19627 = (FStar_Syntax_Syntax.bv_to_name b)
in ((x), (uu____19627)))
in FStar_Syntax_Syntax.NT (uu____19620))
end)) formals1 bs0)
in (FStar_Syntax_Subst.subst_comp subst1 c1))
in (

let body1 = (FStar_Syntax_Util.abs rest body lopt)
in (

let uu____19629 = (

let uu____19650 = (get_result_type c2)
in ((bs0), (body1), (bs0), (uu____19650)))
in ((uu____19629), (false)))))
end))
end
| uu____19683 -> begin
(match ((nformals > nbinders)) with
| true -> begin
(

let uu____19718 = (eta_expand1 binders formals1 body tres)
in (match (uu____19718) with
| (binders1, body1) -> begin
((((binders1), (body1), (formals1), (tres))), (false))
end))
end
| uu____19797 -> begin
((((binders), (body), (formals1), (tres))), (false))
end)
end)))))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____19807) -> begin
(

let uu____19812 = (

let uu____19833 = (aux norm1 x.FStar_Syntax_Syntax.sort)
in (FStar_Pervasives_Native.fst uu____19833))
in ((uu____19812), (true)))
end
| uu____19898 when (not (norm1)) -> begin
(

let t_norm2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm1)
in (aux true t_norm2))
end
| uu____19900 -> begin
(

let uu____19901 = (

let uu____19902 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____19903 = (FStar_Syntax_Print.term_to_string t_norm1)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str uu____19902 uu____19903)))
in (failwith uu____19901))
end))
end
| uu____19928 -> begin
(

let rec aux' = (fun t_norm2 -> (

let uu____19953 = (

let uu____19954 = (FStar_Syntax_Subst.compress t_norm2)
in uu____19954.FStar_Syntax_Syntax.n)
in (match (uu____19953) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____19995 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____19995) with
| (formals1, c1) -> begin
(

let tres = (get_result_type c1)
in (

let uu____20023 = (eta_expand1 [] formals1 e tres)
in (match (uu____20023) with
| (binders1, body1) -> begin
((((binders1), (body1), (formals1), (tres))), (false))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (bv, uu____20103) -> begin
(aux' bv.FStar_Syntax_Syntax.sort)
end
| uu____20108 -> begin
(((([]), (e), ([]), (t_norm2))), (false))
end)))
in (aux' t_norm1))
end)
end)))
in (aux false t_norm))))
in (FStar_All.try_with (fun uu___127_20157 -> (match (()) with
| () -> begin
(

let uu____20164 = (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> ((FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))))
in (match (uu____20164) with
| true -> begin
(encode_top_level_vals env bindings quals)
end
| uu____20175 -> begin
(

let uu____20176 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____20239 lb -> (match (uu____20239) with
| (toks, typs, decls, env1) -> begin
((

let uu____20294 = (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp)
in (match (uu____20294) with
| true -> begin
(FStar_Exn.raise Let_rec_unencodeable)
end
| uu____20295 -> begin
()
end));
(

let t_norm = (whnf env1 lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____20297 = (

let uu____20306 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env1 uu____20306 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (uu____20297) with
| (tok, decl, env2) -> begin
(((tok)::toks), ((t_norm)::typs), ((decl)::decls), (env2))
end)));
)
end)) (([]), ([]), ([]), (env))))
in (match (uu____20176) with
| (toks, typs, decls, env1) -> begin
(

let toks_fvbs = (FStar_List.rev toks)
in (

let decls1 = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (

let typs1 = (FStar_List.rev typs)
in (

let mk_app1 = (fun rng curry fvb vars -> (

let mk_fv = (fun uu____20421 -> (match ((Prims.op_Equality fvb.smt_arity (Prims.parse_int "0"))) with
| true -> begin
(FStar_SMTEncoding_Util.mkFreeV ((fvb.smt_id), (FStar_SMTEncoding_Term.Term_sort)))
end
| uu____20422 -> begin
(raise_arity_mismatch fvb.smt_id fvb.smt_arity (Prims.parse_int "0") rng)
end))
in (match (vars) with
| [] -> begin
(mk_fv ())
end
| uu____20427 -> begin
(match (curry) with
| true -> begin
(match (fvb.smt_token) with
| FStar_Pervasives_Native.Some (ftok) -> begin
(mk_Apply ftok vars)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____20435 = (mk_fv ())
in (mk_Apply uu____20435 vars))
end)
end
| uu____20436 -> begin
(

let uu____20437 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (maybe_curry_app rng (FStar_SMTEncoding_Term.Var (fvb.smt_id)) fvb.smt_arity uu____20437))
end)
end)))
in (

let encode_non_rec_lbdef = (fun bindings1 typs2 toks1 env2 -> (match (((bindings1), (typs2), (toks1))) with
| (({FStar_Syntax_Syntax.lbname = lbn; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____20489; FStar_Syntax_Syntax.lbeff = uu____20490; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = uu____20492; FStar_Syntax_Syntax.lbpos = uu____20493})::[], (t_norm)::[], (fvb)::[]) -> begin
(

let flid = fvb.fvar_lid
in (

let uu____20517 = (

let uu____20524 = (FStar_TypeChecker_Env.open_universes_in env2.tcenv uvs ((e)::(t_norm)::[]))
in (match (uu____20524) with
| (tcenv', uu____20542, e_t) -> begin
(

let uu____20548 = (match (e_t) with
| (e1)::(t_norm1)::[] -> begin
((e1), (t_norm1))
end
| uu____20559 -> begin
(failwith "Impossible")
end)
in (match (uu____20548) with
| (e1, t_norm1) -> begin
(((

let uu___128_20575 = env2
in {bindings = uu___128_20575.bindings; depth = uu___128_20575.depth; tcenv = tcenv'; warn = uu___128_20575.warn; cache = uu___128_20575.cache; nolabels = uu___128_20575.nolabels; use_zfuel_name = uu___128_20575.use_zfuel_name; encode_non_total_function_typ = uu___128_20575.encode_non_total_function_typ; current_module_name = uu___128_20575.current_module_name})), (e1), (t_norm1))
end))
end))
in (match (uu____20517) with
| (env', e1, t_norm1) -> begin
(

let uu____20585 = (destruct_bound_function flid t_norm1 e1)
in (match (uu____20585) with
| ((binders, body, uu____20606, t_body), curry) -> begin
((

let uu____20618 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____20618) with
| true -> begin
(

let uu____20619 = (FStar_Syntax_Print.binders_to_string ", " binders)
in (

let uu____20620 = (FStar_Syntax_Print.term_to_string body)
in (FStar_Util.print2 "Encoding let : binders=[%s], body=%s\n" uu____20619 uu____20620)))
end
| uu____20621 -> begin
()
end));
(

let uu____20622 = (encode_binders FStar_Pervasives_Native.None binders env')
in (match (uu____20622) with
| (vars, guards, env'1, binder_decls, uu____20649) -> begin
(

let body1 = (

let uu____20663 = (FStar_TypeChecker_Env.is_reifiable_function env'1.tcenv t_norm1)
in (match (uu____20663) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env'1.tcenv body)
end
| uu____20664 -> begin
(FStar_Syntax_Util.ascribe body ((FStar_Util.Inl (t_body)), (FStar_Pervasives_Native.None)))
end))
in (

let app = (

let uu____20680 = (FStar_Syntax_Util.range_of_lbname lbn)
in (mk_app1 uu____20680 curry fvb vars))
in (

let uu____20681 = (

let uu____20690 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic))
in (match (uu____20690) with
| true -> begin
(

let uu____20701 = (FStar_SMTEncoding_Term.mk_Valid app)
in (

let uu____20702 = (encode_formula body1 env'1)
in ((uu____20701), (uu____20702))))
end
| uu____20711 -> begin
(

let uu____20712 = (encode_term body1 env'1)
in ((app), (uu____20712)))
end))
in (match (uu____20681) with
| (app1, (body2, decls2)) -> begin
(

let eqn = (

let uu____20735 = (

let uu____20742 = (

let uu____20743 = (

let uu____20754 = (FStar_SMTEncoding_Util.mkEq ((app1), (body2)))
in ((((app1)::[])::[]), (vars), (uu____20754)))
in (FStar_SMTEncoding_Util.mkForall uu____20743))
in (

let uu____20765 = (

let uu____20768 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in FStar_Pervasives_Native.Some (uu____20768))
in ((uu____20742), (uu____20765), ((Prims.strcat "equation_" fvb.smt_id)))))
in (FStar_SMTEncoding_Util.mkAssume uu____20735))
in (

let uu____20771 = (

let uu____20774 = (

let uu____20777 = (

let uu____20780 = (

let uu____20783 = (primitive_type_axioms env2.tcenv flid fvb.smt_id app1)
in (FStar_List.append ((eqn)::[]) uu____20783))
in (FStar_List.append decls2 uu____20780))
in (FStar_List.append binder_decls uu____20777))
in (FStar_List.append decls1 uu____20774))
in ((uu____20771), (env2))))
end))))
end));
)
end))
end)))
end
| uu____20788 -> begin
(failwith "Impossible")
end))
in (

let encode_rec_lbdefs = (fun bindings1 typs2 toks1 env2 -> (

let fuel = (

let uu____20843 = (varops.fresh "fuel")
in ((uu____20843), (FStar_SMTEncoding_Term.Fuel_sort)))
in (

let fuel_tm = (FStar_SMTEncoding_Util.mkFreeV fuel)
in (

let env0 = env2
in (

let uu____20846 = (FStar_All.pipe_right toks1 (FStar_List.fold_left (fun uu____20893 fvb -> (match (uu____20893) with
| (gtoks, env3) -> begin
(

let flid = fvb.fvar_lid
in (

let g = (

let uu____20939 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented")
in (varops.new_fvar uu____20939))
in (

let gtok = (

let uu____20941 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented_token")
in (varops.new_fvar uu____20941))
in (

let env4 = (

let uu____20943 = (

let uu____20946 = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::[])))
in (FStar_All.pipe_left (fun _0_42 -> FStar_Pervasives_Native.Some (_0_42)) uu____20946))
in (push_free_var env3 flid fvb.smt_arity gtok uu____20943))
in (((((fvb), (g), (gtok)))::gtoks), (env4))))))
end)) (([]), (env2))))
in (match (uu____20846) with
| (gtoks, env3) -> begin
(

let gtoks1 = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env01 uu____21046 t_norm uu____21048 -> (match (((uu____21046), (uu____21048))) with
| ((fvb, g, gtok), {FStar_Syntax_Syntax.lbname = lbn; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____21078; FStar_Syntax_Syntax.lbeff = uu____21079; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = uu____21081; FStar_Syntax_Syntax.lbpos = uu____21082}) -> begin
(

let uu____21103 = (

let uu____21110 = (FStar_TypeChecker_Env.open_universes_in env3.tcenv uvs ((e)::(t_norm)::[]))
in (match (uu____21110) with
| (tcenv', uu____21132, e_t) -> begin
(

let uu____21138 = (match (e_t) with
| (e1)::(t_norm1)::[] -> begin
((e1), (t_norm1))
end
| uu____21149 -> begin
(failwith "Impossible")
end)
in (match (uu____21138) with
| (e1, t_norm1) -> begin
(((

let uu___129_21165 = env3
in {bindings = uu___129_21165.bindings; depth = uu___129_21165.depth; tcenv = tcenv'; warn = uu___129_21165.warn; cache = uu___129_21165.cache; nolabels = uu___129_21165.nolabels; use_zfuel_name = uu___129_21165.use_zfuel_name; encode_non_total_function_typ = uu___129_21165.encode_non_total_function_typ; current_module_name = uu___129_21165.current_module_name})), (e1), (t_norm1))
end))
end))
in (match (uu____21103) with
| (env', e1, t_norm1) -> begin
((

let uu____21180 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env01.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____21180) with
| true -> begin
(

let uu____21181 = (FStar_Syntax_Print.lbname_to_string lbn)
in (

let uu____21182 = (FStar_Syntax_Print.term_to_string t_norm1)
in (

let uu____21183 = (FStar_Syntax_Print.term_to_string e1)
in (FStar_Util.print3 "Encoding let rec %s : %s = %s\n" uu____21181 uu____21182 uu____21183))))
end
| uu____21184 -> begin
()
end));
(

let uu____21185 = (destruct_bound_function fvb.fvar_lid t_norm1 e1)
in (match (uu____21185) with
| ((binders, body, formals, tres), curry) -> begin
((

let uu____21222 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env01.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____21222) with
| true -> begin
(

let uu____21223 = (FStar_Syntax_Print.binders_to_string ", " binders)
in (

let uu____21224 = (FStar_Syntax_Print.term_to_string body)
in (

let uu____21225 = (FStar_Syntax_Print.binders_to_string ", " formals)
in (

let uu____21226 = (FStar_Syntax_Print.term_to_string tres)
in (FStar_Util.print4 "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n" uu____21223 uu____21224 uu____21225 uu____21226)))))
end
| uu____21227 -> begin
()
end));
(match (curry) with
| true -> begin
(failwith "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type")
end
| uu____21229 -> begin
()
end);
(

let uu____21230 = (encode_binders FStar_Pervasives_Native.None binders env')
in (match (uu____21230) with
| (vars, guards, env'1, binder_decls, uu____21261) -> begin
(

let decl_g = (

let uu____21275 = (

let uu____21286 = (

let uu____21289 = (FStar_List.map FStar_Pervasives_Native.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::uu____21289)
in ((g), (uu____21286), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Fuel-instrumented function name"))))
in FStar_SMTEncoding_Term.DeclFun (uu____21275))
in (

let env02 = (push_zfuel_name env01 fvb.fvar_lid g)
in (

let decl_g_tok = FStar_SMTEncoding_Term.DeclFun (((gtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Token for fuel-instrumented partial applications"))))
in (

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let app = (

let uu____21314 = (

let uu____21321 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((fvb.smt_id), (uu____21321)))
in (FStar_SMTEncoding_Util.mkApp uu____21314))
in (

let gsapp = (

let uu____21331 = (

let uu____21338 = (

let uu____21341 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (uu____21341)::vars_tm)
in ((g), (uu____21338)))
in (FStar_SMTEncoding_Util.mkApp uu____21331))
in (

let gmax = (

let uu____21347 = (

let uu____21354 = (

let uu____21357 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (uu____21357)::vars_tm)
in ((g), (uu____21354)))
in (FStar_SMTEncoding_Util.mkApp uu____21347))
in (

let body1 = (

let uu____21363 = (FStar_TypeChecker_Env.is_reifiable_function env'1.tcenv t_norm1)
in (match (uu____21363) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env'1.tcenv body)
end
| uu____21364 -> begin
body
end))
in (

let uu____21365 = (encode_term body1 env'1)
in (match (uu____21365) with
| (body_tm, decls2) -> begin
(

let eqn_g = (

let uu____21383 = (

let uu____21390 = (

let uu____21391 = (

let uu____21406 = (FStar_SMTEncoding_Util.mkEq ((gsapp), (body_tm)))
in ((((gsapp)::[])::[]), (FStar_Pervasives_Native.Some ((Prims.parse_int "0"))), ((fuel)::vars), (uu____21406)))
in (FStar_SMTEncoding_Util.mkForall' uu____21391))
in (

let uu____21427 = (

let uu____21430 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" fvb.fvar_lid.FStar_Ident.str)
in FStar_Pervasives_Native.Some (uu____21430))
in ((uu____21390), (uu____21427), ((Prims.strcat "equation_with_fuel_" g)))))
in (FStar_SMTEncoding_Util.mkAssume uu____21383))
in (

let eqn_f = (

let uu____21434 = (

let uu____21441 = (

let uu____21442 = (

let uu____21453 = (FStar_SMTEncoding_Util.mkEq ((app), (gmax)))
in ((((app)::[])::[]), (vars), (uu____21453)))
in (FStar_SMTEncoding_Util.mkForall uu____21442))
in ((uu____21441), (FStar_Pervasives_Native.Some ("Correspondence of recursive function to instrumented version")), ((Prims.strcat "@fuel_correspondence_" g))))
in (FStar_SMTEncoding_Util.mkAssume uu____21434))
in (

let eqn_g' = (

let uu____21467 = (

let uu____21474 = (

let uu____21475 = (

let uu____21486 = (

let uu____21487 = (

let uu____21492 = (

let uu____21493 = (

let uu____21500 = (

let uu____21503 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "0"))
in (uu____21503)::vars_tm)
in ((g), (uu____21500)))
in (FStar_SMTEncoding_Util.mkApp uu____21493))
in ((gsapp), (uu____21492)))
in (FStar_SMTEncoding_Util.mkEq uu____21487))
in ((((gsapp)::[])::[]), ((fuel)::vars), (uu____21486)))
in (FStar_SMTEncoding_Util.mkForall uu____21475))
in ((uu____21474), (FStar_Pervasives_Native.Some ("Fuel irrelevance")), ((Prims.strcat "@fuel_irrelevance_" g))))
in (FStar_SMTEncoding_Util.mkAssume uu____21467))
in (

let uu____21526 = (

let uu____21535 = (encode_binders FStar_Pervasives_Native.None formals env02)
in (match (uu____21535) with
| (vars1, v_guards, env4, binder_decls1, uu____21564) -> begin
(

let vars_tm1 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars1)
in (

let gapp = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::vars_tm1)))
in (

let tok_corr = (

let tok_app = (

let uu____21589 = (FStar_SMTEncoding_Util.mkFreeV ((gtok), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply uu____21589 ((fuel)::vars1)))
in (

let uu____21594 = (

let uu____21601 = (

let uu____21602 = (

let uu____21613 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (gapp)))
in ((((tok_app)::[])::[]), ((fuel)::vars1), (uu____21613)))
in (FStar_SMTEncoding_Util.mkForall uu____21602))
in ((uu____21601), (FStar_Pervasives_Native.Some ("Fuel token correspondence")), ((Prims.strcat "fuel_token_correspondence_" gtok))))
in (FStar_SMTEncoding_Util.mkAssume uu____21594)))
in (

let uu____21634 = (

let uu____21641 = (encode_term_pred FStar_Pervasives_Native.None tres env4 gapp)
in (match (uu____21641) with
| (g_typing, d3) -> begin
(

let uu____21654 = (

let uu____21657 = (

let uu____21658 = (

let uu____21665 = (

let uu____21666 = (

let uu____21677 = (

let uu____21678 = (

let uu____21683 = (FStar_SMTEncoding_Util.mk_and_l v_guards)
in ((uu____21683), (g_typing)))
in (FStar_SMTEncoding_Util.mkImp uu____21678))
in ((((gapp)::[])::[]), ((fuel)::vars1), (uu____21677)))
in (FStar_SMTEncoding_Util.mkForall uu____21666))
in ((uu____21665), (FStar_Pervasives_Native.Some ("Typing correspondence of token to term")), ((Prims.strcat "token_correspondence_" g))))
in (FStar_SMTEncoding_Util.mkAssume uu____21658))
in (uu____21657)::[])
in ((d3), (uu____21654)))
end))
in (match (uu____21634) with
| (aux_decls, typing_corr) -> begin
(((FStar_List.append binder_decls1 aux_decls)), ((FStar_List.append typing_corr ((tok_corr)::[]))))
end)))))
end))
in (match (uu____21526) with
| (aux_decls, g_typing) -> begin
(((FStar_List.append binder_decls (FStar_List.append decls2 (FStar_List.append aux_decls ((decl_g)::(decl_g_tok)::[]))))), ((FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing)), (env02))
end)))))
end))))))))))
end));
)
end));
)
end))
end))
in (

let uu____21748 = (

let uu____21761 = (FStar_List.zip3 gtoks1 typs2 bindings1)
in (FStar_List.fold_left (fun uu____21822 uu____21823 -> (match (((uu____21822), (uu____21823))) with
| ((decls2, eqns, env01), (gtok, ty, lb)) -> begin
(

let uu____21948 = (encode_one_binding env01 gtok ty lb)
in (match (uu____21948) with
| (decls', eqns', env02) -> begin
(((decls')::decls2), ((FStar_List.append eqns' eqns)), (env02))
end))
end)) (((decls1)::[]), ([]), (env0)) uu____21761))
in (match (uu____21748) with
| (decls2, eqns, env01) -> begin
(

let uu____22021 = (

let isDeclFun = (fun uu___95_22033 -> (match (uu___95_22033) with
| FStar_SMTEncoding_Term.DeclFun (uu____22034) -> begin
true
end
| uu____22045 -> begin
false
end))
in (

let uu____22046 = (FStar_All.pipe_right decls2 FStar_List.flatten)
in (FStar_All.pipe_right uu____22046 (FStar_List.partition isDeclFun))))
in (match (uu____22021) with
| (prefix_decls, rest) -> begin
(

let eqns1 = (FStar_List.rev eqns)
in (((FStar_List.append prefix_decls (FStar_List.append rest eqns1))), (env01)))
end))
end))))
end))))))
in (

let uu____22086 = ((FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___96_22090 -> (match (uu___96_22090) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| uu____22091 -> begin
false
end)))) || (FStar_All.pipe_right typs1 (FStar_Util.for_some (fun t -> (

let uu____22097 = ((FStar_Syntax_Util.is_pure_or_ghost_function t) || (FStar_TypeChecker_Env.is_reifiable_function env1.tcenv t))
in (FStar_All.pipe_left Prims.op_Negation uu____22097))))))
in (match (uu____22086) with
| true -> begin
((decls1), (env1))
end
| uu____22106 -> begin
(FStar_All.try_with (fun uu___131_22114 -> (match (()) with
| () -> begin
(match ((not (is_rec))) with
| true -> begin
(encode_non_rec_lbdef bindings typs1 toks_fvbs env1)
end
| uu____22127 -> begin
(encode_rec_lbdefs bindings typs1 toks_fvbs env1)
end)
end)) (fun uu___130_22129 -> (match (uu___130_22129) with
| Inner_let_rec -> begin
((decls1), (env1))
end)))
end))))))))
end))
end))
end)) (fun uu___126_22141 -> (match (uu___126_22141) with
| Let_rec_unencodeable -> begin
(

let msg = (

let uu____22149 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right uu____22149 (FStar_String.concat " and ")))
in (

let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in (((decl)::[]), (env))))
end)))))
end))


let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let nm = (

let uu____22198 = (FStar_Syntax_Util.lid_of_sigelt se)
in (match (uu____22198) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (l) -> begin
l.FStar_Ident.str
end))
in (

let uu____22202 = (encode_sigelt' env se)
in (match (uu____22202) with
| (g, env1) -> begin
(

let g1 = (match (g) with
| [] -> begin
(

let uu____22218 = (

let uu____22219 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (uu____22219))
in (uu____22218)::[])
end
| uu____22220 -> begin
(

let uu____22221 = (

let uu____22224 = (

let uu____22225 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____22225))
in (uu____22224)::g)
in (

let uu____22226 = (

let uu____22229 = (

let uu____22230 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____22230))
in (uu____22229)::[])
in (FStar_List.append uu____22221 uu____22226)))
end)
in ((g1), (env1)))
end))))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let is_opaque_to_smt = (fun t -> (

let uu____22243 = (

let uu____22244 = (FStar_Syntax_Subst.compress t)
in uu____22244.FStar_Syntax_Syntax.n)
in (match (uu____22243) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____22248)) -> begin
(Prims.op_Equality s "opaque_to_smt")
end
| uu____22249 -> begin
false
end)))
in (

let is_uninterpreted_by_smt = (fun t -> (

let uu____22254 = (

let uu____22255 = (FStar_Syntax_Subst.compress t)
in uu____22255.FStar_Syntax_Syntax.n)
in (match (uu____22254) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____22259)) -> begin
(Prims.op_Equality s "uninterpreted_by_smt")
end
| uu____22260 -> begin
false
end)))
in (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____22265) -> begin
(failwith "impossible -- new_effect_for_free should have been removed by Tc.fs")
end
| FStar_Syntax_Syntax.Sig_splice (uu____22270) -> begin
(failwith "impossible -- splice should have been removed by Tc.fs")
end
| FStar_Syntax_Syntax.Sig_pragma (uu____22275) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_main (uu____22278) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____22281) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____22296) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(

let uu____22300 = (

let uu____22301 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right uu____22301 Prims.op_Negation))
in (match (uu____22300) with
| true -> begin
(([]), (env))
end
| uu____22310 -> begin
(

let close_effect_params = (fun tm -> (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
tm
end
| uu____22327 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((ed.FStar_Syntax_Syntax.binders), (tm), (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[]))))))) FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)
end))
in (

let encode_action = (fun env1 a -> (

let uu____22347 = (FStar_Syntax_Util.arrow_formals_comp a.FStar_Syntax_Syntax.action_typ)
in (match (uu____22347) with
| (formals, uu____22365) -> begin
(

let arity = (FStar_List.length formals)
in (

let uu____22383 = (new_term_constant_and_tok_from_lid env1 a.FStar_Syntax_Syntax.action_name arity)
in (match (uu____22383) with
| (aname, atok, env2) -> begin
(

let uu____22403 = (

let uu____22408 = (close_effect_params a.FStar_Syntax_Syntax.action_defn)
in (encode_term uu____22408 env2))
in (match (uu____22403) with
| (tm, decls) -> begin
(

let a_decls = (

let uu____22420 = (

let uu____22421 = (

let uu____22432 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____22448 -> FStar_SMTEncoding_Term.Term_sort)))
in ((aname), (uu____22432), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Action"))))
in FStar_SMTEncoding_Term.DeclFun (uu____22421))
in (uu____22420)::(FStar_SMTEncoding_Term.DeclFun (((atok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Action token")))))::[])
in (

let uu____22461 = (

let aux = (fun uu____22513 uu____22514 -> (match (((uu____22513), (uu____22514))) with
| ((bv, uu____22566), (env3, acc_sorts, acc)) -> begin
(

let uu____22604 = (gen_term_var env3 bv)
in (match (uu____22604) with
| (xxsym, xx, env4) -> begin
((env4), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::acc_sorts), ((xx)::acc))
end))
end))
in (FStar_List.fold_right aux formals ((env2), ([]), ([]))))
in (match (uu____22461) with
| (uu____22676, xs_sorts, xs) -> begin
(

let app = (FStar_SMTEncoding_Util.mkApp ((aname), (xs)))
in (

let a_eq = (

let uu____22699 = (

let uu____22706 = (

let uu____22707 = (

let uu____22718 = (

let uu____22719 = (

let uu____22724 = (mk_Apply tm xs_sorts)
in ((app), (uu____22724)))
in (FStar_SMTEncoding_Util.mkEq uu____22719))
in ((((app)::[])::[]), (xs_sorts), (uu____22718)))
in (FStar_SMTEncoding_Util.mkForall uu____22707))
in ((uu____22706), (FStar_Pervasives_Native.Some ("Action equality")), ((Prims.strcat aname "_equality"))))
in (FStar_SMTEncoding_Util.mkAssume uu____22699))
in (

let tok_correspondence = (

let tok_term = (FStar_SMTEncoding_Util.mkFreeV ((atok), (FStar_SMTEncoding_Term.Term_sort)))
in (

let tok_app = (mk_Apply tok_term xs_sorts)
in (

let uu____22744 = (

let uu____22751 = (

let uu____22752 = (

let uu____22763 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (app)))
in ((((tok_app)::[])::[]), (xs_sorts), (uu____22763)))
in (FStar_SMTEncoding_Util.mkForall uu____22752))
in ((uu____22751), (FStar_Pervasives_Native.Some ("Action token correspondence")), ((Prims.strcat aname "_token_correspondence"))))
in (FStar_SMTEncoding_Util.mkAssume uu____22744))))
in ((env2), ((FStar_List.append decls (FStar_List.append a_decls ((a_eq)::(tok_correspondence)::[]))))))))
end)))
end))
end)))
end)))
in (

let uu____22782 = (FStar_Util.fold_map encode_action env ed.FStar_Syntax_Syntax.actions)
in (match (uu____22782) with
| (env1, decls2) -> begin
(((FStar_List.flatten decls2)), (env1))
end))))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____22810, uu____22811) when (FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid) -> begin
(

let uu____22812 = (new_term_constant_and_tok_from_lid env lid (Prims.parse_int "4"))
in (match (uu____22812) with
| (tname, ttok, env1) -> begin
(([]), (env1))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____22829, t) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let will_encode_definition = (

let uu____22835 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___97_22839 -> (match (uu___97_22839) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.Projector (uu____22840) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____22845) -> begin
true
end
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| uu____22846 -> begin
false
end))))
in (not (uu____22835)))
in (match (will_encode_definition) with
| true -> begin
(([]), (env))
end
| uu____22853 -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____22855 = (

let uu____22862 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs (FStar_Util.for_some is_uninterpreted_by_smt))
in (encode_top_level_val uu____22862 env fv t quals))
in (match (uu____22855) with
| (decls, env1) -> begin
(

let tname = lid.FStar_Ident.str
in (

let tsym = (FStar_SMTEncoding_Util.mkFreeV ((tname), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____22877 = (

let uu____22880 = (primitive_type_axioms env1.tcenv lid tname tsym)
in (FStar_List.append decls uu____22880))
in ((uu____22877), (env1)))))
end)))
end)))
end
| FStar_Syntax_Syntax.Sig_assume (l, us, f) -> begin
(

let uu____22888 = (FStar_Syntax_Subst.open_univ_vars us f)
in (match (uu____22888) with
| (uu____22897, f1) -> begin
(

let uu____22899 = (encode_formula f1 env)
in (match (uu____22899) with
| (f2, decls) -> begin
(

let g = (

let uu____22913 = (

let uu____22914 = (

let uu____22921 = (

let uu____22924 = (

let uu____22925 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" uu____22925))
in FStar_Pervasives_Native.Some (uu____22924))
in (

let uu____22926 = (varops.mk_unique (Prims.strcat "assumption_" l.FStar_Ident.str))
in ((f2), (uu____22921), (uu____22926))))
in (FStar_SMTEncoding_Util.mkAssume uu____22914))
in (uu____22913)::[])
in (((FStar_List.append decls g)), (env)))
end))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____22932) when ((FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) || (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs (FStar_Util.for_some is_opaque_to_smt))) -> begin
(

let attrs = se.FStar_Syntax_Syntax.sigattrs
in (

let uu____22944 = (FStar_Util.fold_map (fun env1 lb -> (

let lid = (

let uu____22962 = (

let uu____22965 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____22965.FStar_Syntax_Syntax.fv_name)
in uu____22962.FStar_Syntax_Syntax.v)
in (

let uu____22966 = (

let uu____22967 = (FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone uu____22967))
in (match (uu____22966) with
| true -> begin
(

let val_decl = (

let uu___132_22995 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = uu___132_22995.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Irreducible)::se.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___132_22995.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___132_22995.FStar_Syntax_Syntax.sigattrs})
in (

let uu____23000 = (encode_sigelt' env1 val_decl)
in (match (uu____23000) with
| (decls, env2) -> begin
((env2), (decls))
end)))
end
| uu____23011 -> begin
((env1), ([]))
end)))) env (FStar_Pervasives_Native.snd lbs))
in (match (uu____22944) with
| (env1, decls) -> begin
(((FStar_List.flatten decls)), (env1))
end)))
end
| FStar_Syntax_Syntax.Sig_let ((uu____23028, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2p1); FStar_Syntax_Syntax.lbunivs = uu____23030; FStar_Syntax_Syntax.lbtyp = uu____23031; FStar_Syntax_Syntax.lbeff = uu____23032; FStar_Syntax_Syntax.lbdef = uu____23033; FStar_Syntax_Syntax.lbattrs = uu____23034; FStar_Syntax_Syntax.lbpos = uu____23035})::[]), uu____23036) when (FStar_Syntax_Syntax.fv_eq_lid b2p1 FStar_Parser_Const.b2p_lid) -> begin
(

let uu____23059 = (new_term_constant_and_tok_from_lid env b2p1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v (Prims.parse_int "1"))
in (match (uu____23059) with
| (tname, ttok, env1) -> begin
(

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let b2p_x = (FStar_SMTEncoding_Util.mkApp (("Prims.b2p"), ((x)::[])))
in (

let valid_b2p_x = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b2p_x)::[])))
in (

let decls = (

let uu____23088 = (

let uu____23091 = (

let uu____23092 = (

let uu____23099 = (

let uu____23100 = (

let uu____23111 = (

let uu____23112 = (

let uu____23117 = (FStar_SMTEncoding_Util.mkApp (((FStar_Pervasives_Native.snd FStar_SMTEncoding_Term.boxBoolFun)), ((x)::[])))
in ((valid_b2p_x), (uu____23117)))
in (FStar_SMTEncoding_Util.mkEq uu____23112))
in ((((b2p_x)::[])::[]), ((xx)::[]), (uu____23111)))
in (FStar_SMTEncoding_Util.mkForall uu____23100))
in ((uu____23099), (FStar_Pervasives_Native.Some ("b2p def")), ("b2p_def")))
in (FStar_SMTEncoding_Util.mkAssume uu____23092))
in (uu____23091)::[])
in (FStar_SMTEncoding_Term.DeclFun (((tname), ((FStar_SMTEncoding_Term.Term_sort)::[]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None))))::uu____23088)
in ((decls), (env1)))))))
end))
end
| FStar_Syntax_Syntax.Sig_let (uu____23150, uu____23151) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___98_23160 -> (match (uu___98_23160) with
| FStar_Syntax_Syntax.Discriminator (uu____23161) -> begin
true
end
| uu____23162 -> begin
false
end)))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let (uu____23165, lids) when ((FStar_All.pipe_right lids (FStar_Util.for_some (fun l -> (

let uu____23176 = (

let uu____23177 = (FStar_List.hd l.FStar_Ident.ns)
in uu____23177.FStar_Ident.idText)
in (Prims.op_Equality uu____23176 "Prims"))))) && (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___99_23181 -> (match (uu___99_23181) with
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
true
end
| uu____23182 -> begin
false
end))))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____23186) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___100_23203 -> (match (uu___100_23203) with
| FStar_Syntax_Syntax.Projector (uu____23204) -> begin
true
end
| uu____23209 -> begin
false
end)))) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____23212 = (try_lookup_free_var env l)
in (match (uu____23212) with
| FStar_Pervasives_Native.Some (uu____23219) -> begin
(([]), (env))
end
| FStar_Pervasives_Native.None -> begin
(

let se1 = (

let uu___133_23223 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l); FStar_Syntax_Syntax.sigquals = uu___133_23223.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___133_23223.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___133_23223.FStar_Syntax_Syntax.sigattrs})
in (encode_sigelt env se1))
end))))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), uu____23230) -> begin
(encode_top_level_let env ((is_rec), (bindings)) se.FStar_Syntax_Syntax.sigquals)
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____23248) -> begin
(

let uu____23257 = (encode_sigelts env ses)
in (match (uu____23257) with
| (g, env1) -> begin
(

let uu____23274 = (FStar_All.pipe_right g (FStar_List.partition (fun uu___101_23297 -> (match (uu___101_23297) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.assumption_term = uu____23298; FStar_SMTEncoding_Term.assumption_caption = FStar_Pervasives_Native.Some ("inversion axiom"); FStar_SMTEncoding_Term.assumption_name = uu____23299; FStar_SMTEncoding_Term.assumption_fact_ids = uu____23300}) -> begin
false
end
| uu____23303 -> begin
true
end))))
in (match (uu____23274) with
| (g', inversions) -> begin
(

let uu____23318 = (FStar_All.pipe_right g' (FStar_List.partition (fun uu___102_23339 -> (match (uu___102_23339) with
| FStar_SMTEncoding_Term.DeclFun (uu____23340) -> begin
true
end
| uu____23351 -> begin
false
end))))
in (match (uu____23318) with
| (decls, rest) -> begin
(((FStar_List.append decls (FStar_List.append rest inversions))), (env1))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, uu____23369, tps, k, uu____23372, datas) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___103_23389 -> (match (uu___103_23389) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____23390 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> (match (is_logical) with
| true -> begin
(

let uu____23399 = c
in (match (uu____23399) with
| (name, args, uu____23404, uu____23405, uu____23406) -> begin
(

let uu____23411 = (

let uu____23412 = (

let uu____23423 = (FStar_All.pipe_right args (FStar_List.map (fun uu____23440 -> (match (uu____23440) with
| (uu____23447, sort, uu____23449) -> begin
sort
end))))
in ((name), (uu____23423), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____23412))
in (uu____23411)::[])
end))
end
| uu____23454 -> begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end))
in (

let inversion_axioms = (fun tapp vars -> (

let uu____23476 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (

let uu____23482 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right uu____23482 FStar_Option.isNone)))))
in (match (uu____23476) with
| true -> begin
[]
end
| uu____23513 -> begin
(

let uu____23514 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____23514) with
| (xxsym, xx) -> begin
(

let uu____23523 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun uu____23562 l -> (match (uu____23562) with
| (out, decls) -> begin
(

let uu____23582 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (uu____23582) with
| (uu____23593, data_t) -> begin
(

let uu____23595 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (uu____23595) with
| (args, res) -> begin
(

let indices = (

let uu____23641 = (

let uu____23642 = (FStar_Syntax_Subst.compress res)
in uu____23642.FStar_Syntax_Syntax.n)
in (match (uu____23641) with
| FStar_Syntax_Syntax.Tm_app (uu____23653, indices) -> begin
indices
end
| uu____23675 -> begin
[]
end))
in (

let env1 = (FStar_All.pipe_right args (FStar_List.fold_left (fun env1 uu____23699 -> (match (uu____23699) with
| (x, uu____23705) -> begin
(

let uu____23706 = (

let uu____23707 = (

let uu____23714 = (mk_term_projector_name l x)
in ((uu____23714), ((xx)::[])))
in (FStar_SMTEncoding_Util.mkApp uu____23707))
in (push_term_var env1 x uu____23706))
end)) env))
in (

let uu____23717 = (encode_args indices env1)
in (match (uu____23717) with
| (indices1, decls') -> begin
((match ((Prims.op_disEquality (FStar_List.length indices1) (FStar_List.length vars))) with
| true -> begin
(failwith "Impossible")
end
| uu____23741 -> begin
()
end);
(

let eqs = (

let uu____23743 = (FStar_List.map2 (fun v1 a -> (

let uu____23759 = (

let uu____23764 = (FStar_SMTEncoding_Util.mkFreeV v1)
in ((uu____23764), (a)))
in (FStar_SMTEncoding_Util.mkEq uu____23759))) vars indices1)
in (FStar_All.pipe_right uu____23743 FStar_SMTEncoding_Util.mk_and_l))
in (

let uu____23767 = (

let uu____23768 = (

let uu____23773 = (

let uu____23774 = (

let uu____23779 = (mk_data_tester env1 l xx)
in ((uu____23779), (eqs)))
in (FStar_SMTEncoding_Util.mkAnd uu____23774))
in ((out), (uu____23773)))
in (FStar_SMTEncoding_Util.mkOr uu____23768))
in ((uu____23767), ((FStar_List.append decls decls')))));
)
end))))
end))
end))
end)) ((FStar_SMTEncoding_Util.mkFalse), ([]))))
in (match (uu____23523) with
| (data_ax, decls) -> begin
(

let uu____23792 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____23792) with
| (ffsym, ff) -> begin
(

let fuel_guarded_inversion = (

let xx_has_type_sfuel = (match (((FStar_List.length datas) > (Prims.parse_int "1"))) with
| true -> begin
(

let uu____23803 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((ff)::[])))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel uu____23803 xx tapp))
end
| uu____23806 -> begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end)
in (

let uu____23807 = (

let uu____23814 = (

let uu____23815 = (

let uu____23826 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (

let uu____23841 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_sfuel), (data_ax)))
in ((((xx_has_type_sfuel)::[])::[]), (uu____23826), (uu____23841))))
in (FStar_SMTEncoding_Util.mkForall uu____23815))
in (

let uu____23856 = (varops.mk_unique (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str))
in ((uu____23814), (FStar_Pervasives_Native.Some ("inversion axiom")), (uu____23856))))
in (FStar_SMTEncoding_Util.mkAssume uu____23807)))
in (FStar_List.append decls ((fuel_guarded_inversion)::[])))
end))
end))
end))
end)))
in (

let uu____23859 = (

let uu____23872 = (

let uu____23873 = (FStar_Syntax_Subst.compress k)
in uu____23873.FStar_Syntax_Syntax.n)
in (match (uu____23872) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
(((FStar_List.append tps formals)), ((FStar_Syntax_Util.comp_result kres)))
end
| uu____23918 -> begin
((tps), (k))
end))
in (match (uu____23859) with
| (formals, res) -> begin
(

let uu____23941 = (FStar_Syntax_Subst.open_term formals res)
in (match (uu____23941) with
| (formals1, res1) -> begin
(

let uu____23952 = (encode_binders FStar_Pervasives_Native.None formals1 env)
in (match (uu____23952) with
| (vars, guards, env', binder_decls, uu____23977) -> begin
(

let arity = (FStar_List.length vars)
in (

let uu____23991 = (new_term_constant_and_tok_from_lid env t arity)
in (match (uu____23991) with
| (tname, ttok, env1) -> begin
(

let ttok_tm = (FStar_SMTEncoding_Util.mkApp ((ttok), ([])))
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let tapp = (

let uu____24014 = (

let uu____24021 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((tname), (uu____24021)))
in (FStar_SMTEncoding_Util.mkApp uu____24014))
in (

let uu____24030 = (

let tname_decl = (

let uu____24040 = (

let uu____24041 = (FStar_All.pipe_right vars (FStar_List.map (fun uu____24073 -> (match (uu____24073) with
| (n1, s) -> begin
(((Prims.strcat tname n1)), (s), (false))
end))))
in (

let uu____24086 = (varops.next_id ())
in ((tname), (uu____24041), (FStar_SMTEncoding_Term.Term_sort), (uu____24086), (false))))
in (constructor_or_logic_type_decl uu____24040))
in (

let uu____24095 = (match (vars) with
| [] -> begin
(

let uu____24108 = (

let uu____24109 = (

let uu____24112 = (FStar_SMTEncoding_Util.mkApp ((tname), ([])))
in (FStar_All.pipe_left (fun _0_43 -> FStar_Pervasives_Native.Some (_0_43)) uu____24112))
in (push_free_var env1 t arity tname uu____24109))
in (([]), (uu____24108)))
end
| uu____24123 -> begin
(

let ttok_decl = FStar_SMTEncoding_Term.DeclFun (((ttok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("token"))))
in (

let ttok_fresh = (

let uu____24132 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ttok), (FStar_SMTEncoding_Term.Term_sort)) uu____24132))
in (

let ttok_app = (mk_Apply ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (

let uu____24146 = (

let uu____24153 = (

let uu____24154 = (

let uu____24169 = (FStar_SMTEncoding_Util.mkEq ((ttok_app), (tapp)))
in ((pats), (FStar_Pervasives_Native.None), (vars), (uu____24169)))
in (FStar_SMTEncoding_Util.mkForall' uu____24154))
in ((uu____24153), (FStar_Pervasives_Native.Some ("name-token correspondence")), ((Prims.strcat "token_correspondence_" ttok))))
in (FStar_SMTEncoding_Util.mkAssume uu____24146))
in (((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[]), (env1)))))))
end)
in (match (uu____24095) with
| (tok_decls, env2) -> begin
(((FStar_List.append tname_decl tok_decls)), (env2))
end)))
in (match (uu____24030) with
| (decls, env2) -> begin
(

let kindingAx = (

let uu____24209 = (encode_term_pred FStar_Pervasives_Native.None res1 env' tapp)
in (match (uu____24209) with
| (k1, decls1) -> begin
(

let karr = (match (((FStar_List.length formals1) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____24227 = (

let uu____24228 = (

let uu____24235 = (

let uu____24236 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____24236))
in ((uu____24235), (FStar_Pervasives_Native.Some ("kinding")), ((Prims.strcat "pre_kinding_" ttok))))
in (FStar_SMTEncoding_Util.mkAssume uu____24228))
in (uu____24227)::[])
end
| uu____24239 -> begin
[]
end)
in (

let uu____24240 = (

let uu____24243 = (

let uu____24246 = (

let uu____24247 = (

let uu____24254 = (

let uu____24255 = (

let uu____24266 = (FStar_SMTEncoding_Util.mkImp ((guard), (k1)))
in ((((tapp)::[])::[]), (vars), (uu____24266)))
in (FStar_SMTEncoding_Util.mkForall uu____24255))
in ((uu____24254), (FStar_Pervasives_Native.None), ((Prims.strcat "kinding_" ttok))))
in (FStar_SMTEncoding_Util.mkAssume uu____24247))
in (uu____24246)::[])
in (FStar_List.append karr uu____24243))
in (FStar_List.append decls1 uu____24240)))
end))
in (

let aux = (

let uu____24282 = (

let uu____24285 = (inversion_axioms tapp vars)
in (

let uu____24288 = (

let uu____24291 = (pretype_axiom env2 tapp vars)
in (uu____24291)::[])
in (FStar_List.append uu____24285 uu____24288)))
in (FStar_List.append kindingAx uu____24282))
in (

let g = (FStar_List.append decls (FStar_List.append binder_decls aux))
in ((g), (env2)))))
end)))))
end)))
end))
end))
end))))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____24298, uu____24299, uu____24300, uu____24301, uu____24302) when (FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____24310, t, uu____24312, n_tps, uu____24314) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____24322 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____24322) with
| (formals, t_res) -> begin
(

let arity = (FStar_List.length formals)
in (

let uu____24362 = (new_term_constant_and_tok_from_lid env d arity)
in (match (uu____24362) with
| (ddconstrsym, ddtok, env1) -> begin
(

let ddtok_tm = (FStar_SMTEncoding_Util.mkApp ((ddtok), ([])))
in (

let uu____24383 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____24383) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (

let uu____24397 = (encode_binders (FStar_Pervasives_Native.Some (fuel_tm)) formals env1)
in (match (uu____24397) with
| (vars, guards, env', binder_decls, names1) -> begin
(

let fields = (FStar_All.pipe_right names1 (FStar_List.mapi (fun n1 x -> (

let projectible = true
in (

let uu____24467 = (mk_term_projector_name d x)
in ((uu____24467), (FStar_SMTEncoding_Term.Term_sort), (projectible)))))))
in (

let datacons = (

let uu____24469 = (

let uu____24488 = (varops.next_id ())
in ((ddconstrsym), (fields), (FStar_SMTEncoding_Term.Term_sort), (uu____24488), (true)))
in (FStar_All.pipe_right uu____24469 FStar_SMTEncoding_Term.constructor_to_decl))
in (

let app = (mk_Apply ddtok_tm vars)
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (

let uu____24527 = (encode_term_pred FStar_Pervasives_Native.None t env1 ddtok_tm)
in (match (uu____24527) with
| (tok_typing, decls3) -> begin
(

let tok_typing1 = (match (fields) with
| (uu____24539)::uu____24540 -> begin
(

let ff = (("ty"), (FStar_SMTEncoding_Term.Term_sort))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV ff)
in (

let vtok_app_l = (mk_Apply ddtok_tm ((ff)::[]))
in (

let vtok_app_r = (mk_Apply f ((((ddtok), (FStar_SMTEncoding_Term.Term_sort)))::[]))
in (

let uu____24585 = (

let uu____24596 = (FStar_SMTEncoding_Term.mk_NoHoist f tok_typing)
in ((((vtok_app_l)::[])::((vtok_app_r)::[])::[]), ((ff)::[]), (uu____24596)))
in (FStar_SMTEncoding_Util.mkForall uu____24585))))))
end
| uu____24621 -> begin
tok_typing
end)
in (

let uu____24630 = (encode_binders (FStar_Pervasives_Native.Some (fuel_tm)) formals env1)
in (match (uu____24630) with
| (vars', guards', env'', decls_formals, uu____24655) -> begin
(

let uu____24668 = (

let xvars1 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars')
in (

let dapp1 = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars1)))
in (encode_term_pred (FStar_Pervasives_Native.Some (fuel_tm)) t_res env'' dapp1)))
in (match (uu____24668) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_SMTEncoding_Util.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| uu____24699 -> begin
(

let uu____24706 = (

let uu____24707 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ddtok), (FStar_SMTEncoding_Term.Term_sort)) uu____24707))
in (uu____24706)::[])
end)
in (

let encode_elim = (fun uu____24717 -> (

let uu____24718 = (FStar_Syntax_Util.head_and_args t_res)
in (match (uu____24718) with
| (head1, args) -> begin
(

let uu____24761 = (

let uu____24762 = (FStar_Syntax_Subst.compress head1)
in uu____24762.FStar_Syntax_Syntax.n)
in (match (uu____24761) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____24772; FStar_Syntax_Syntax.vars = uu____24773}, uu____24774) -> begin
(

let uu____24779 = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (match (uu____24779) with
| (encoded_head, encoded_head_arity) -> begin
(

let uu____24792 = (encode_args args env')
in (match (uu____24792) with
| (encoded_args, arg_decls) -> begin
(

let guards_for_parameter = (fun orig_arg arg xv -> (

let fv1 = (match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv1) -> begin
fv1
end
| uu____24835 -> begin
(

let uu____24836 = (

let uu____24841 = (

let uu____24842 = (FStar_Syntax_Print.term_to_string orig_arg)
in (FStar_Util.format1 "Inductive type parameter %s must be a variable ; You may want to change it to an index." uu____24842))
in ((FStar_Errors.Fatal_NonVariableInductiveTypeParameter), (uu____24841)))
in (FStar_Errors.raise_error uu____24836 orig_arg.FStar_Syntax_Syntax.pos))
end)
in (

let guards1 = (FStar_All.pipe_right guards (FStar_List.collect (fun g -> (

let uu____24858 = (

let uu____24859 = (FStar_SMTEncoding_Term.free_variables g)
in (FStar_List.contains fv1 uu____24859))
in (match (uu____24858) with
| true -> begin
(

let uu____24872 = (FStar_SMTEncoding_Term.subst g fv1 xv)
in (uu____24872)::[])
end
| uu____24873 -> begin
[]
end)))))
in (FStar_SMTEncoding_Util.mk_and_l guards1))))
in (

let uu____24874 = (

let uu____24887 = (FStar_List.zip args encoded_args)
in (FStar_List.fold_left (fun uu____24937 uu____24938 -> (match (((uu____24937), (uu____24938))) with
| ((env2, arg_vars, eqns_or_guards, i), (orig_arg, arg)) -> begin
(

let uu____25033 = (

let uu____25040 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (gen_term_var env2 uu____25040))
in (match (uu____25033) with
| (uu____25053, xv, env3) -> begin
(

let eqns = (match ((i < n_tps)) with
| true -> begin
(

let uu____25061 = (guards_for_parameter (FStar_Pervasives_Native.fst orig_arg) arg xv)
in (uu____25061)::eqns_or_guards)
end
| uu____25062 -> begin
(

let uu____25063 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (uu____25063)::eqns_or_guards)
end)
in ((env3), ((xv)::arg_vars), (eqns), ((i + (Prims.parse_int "1")))))
end))
end)) ((env'), ([]), ([]), ((Prims.parse_int "0"))) uu____24887))
in (match (uu____24874) with
| (uu____25078, arg_vars, elim_eqns_or_guards, uu____25081) -> begin
(

let arg_vars1 = (FStar_List.rev arg_vars)
in (

let ty = (maybe_curry_app fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.p (FStar_SMTEncoding_Term.Var (encoded_head)) encoded_head_arity arg_vars1)
in (

let xvars1 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp1 = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars1)))
in (

let ty_pred = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (FStar_Pervasives_Native.Some (s_fuel_tm)) dapp1 ty)
in (

let arg_binders = (FStar_List.map FStar_SMTEncoding_Term.fv_of_term arg_vars1)
in (

let typing_inversion = (

let uu____25109 = (

let uu____25116 = (

let uu____25117 = (

let uu____25128 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____25139 = (

let uu____25140 = (

let uu____25145 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append elim_eqns_or_guards guards))
in ((ty_pred), (uu____25145)))
in (FStar_SMTEncoding_Util.mkImp uu____25140))
in ((((ty_pred)::[])::[]), (uu____25128), (uu____25139))))
in (FStar_SMTEncoding_Util.mkForall uu____25117))
in ((uu____25116), (FStar_Pervasives_Native.Some ("data constructor typing elim")), ((Prims.strcat "data_elim_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____25109))
in (

let subterm_ordering = (match ((FStar_Ident.lid_equals d FStar_Parser_Const.lextop_lid)) with
| true -> begin
(

let x = (

let uu____25168 = (varops.fresh "x")
in ((uu____25168), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (

let uu____25170 = (

let uu____25177 = (

let uu____25178 = (

let uu____25189 = (

let uu____25194 = (

let uu____25197 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in (uu____25197)::[])
in (uu____25194)::[])
in (

let uu____25202 = (

let uu____25203 = (

let uu____25208 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (

let uu____25209 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in ((uu____25208), (uu____25209))))
in (FStar_SMTEncoding_Util.mkImp uu____25203))
in ((uu____25189), ((x)::[]), (uu____25202))))
in (FStar_SMTEncoding_Util.mkForall uu____25178))
in (

let uu____25228 = (varops.mk_unique "lextop")
in ((uu____25177), (FStar_Pervasives_Native.Some ("lextop is top")), (uu____25228))))
in (FStar_SMTEncoding_Util.mkAssume uu____25170))))
end
| uu____25231 -> begin
(

let prec = (

let uu____25235 = (FStar_All.pipe_right vars (FStar_List.mapi (fun i v1 -> (match ((i < n_tps)) with
| true -> begin
[]
end
| uu____25262 -> begin
(

let uu____25263 = (

let uu____25264 = (FStar_SMTEncoding_Util.mkFreeV v1)
in (FStar_SMTEncoding_Util.mk_Precedes uu____25264 dapp1))
in (uu____25263)::[])
end))))
in (FStar_All.pipe_right uu____25235 FStar_List.flatten))
in (

let uu____25271 = (

let uu____25278 = (

let uu____25279 = (

let uu____25290 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____25301 = (

let uu____25302 = (

let uu____25307 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (uu____25307)))
in (FStar_SMTEncoding_Util.mkImp uu____25302))
in ((((ty_pred)::[])::[]), (uu____25290), (uu____25301))))
in (FStar_SMTEncoding_Util.mkForall uu____25279))
in ((uu____25278), (FStar_Pervasives_Native.Some ("subterm ordering")), ((Prims.strcat "subterm_ordering_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____25271)))
end)
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____25327 = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (match (uu____25327) with
| (encoded_head, encoded_head_arity) -> begin
(

let uu____25340 = (encode_args args env')
in (match (uu____25340) with
| (encoded_args, arg_decls) -> begin
(

let guards_for_parameter = (fun orig_arg arg xv -> (

let fv1 = (match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv1) -> begin
fv1
end
| uu____25383 -> begin
(

let uu____25384 = (

let uu____25389 = (

let uu____25390 = (FStar_Syntax_Print.term_to_string orig_arg)
in (FStar_Util.format1 "Inductive type parameter %s must be a variable ; You may want to change it to an index." uu____25390))
in ((FStar_Errors.Fatal_NonVariableInductiveTypeParameter), (uu____25389)))
in (FStar_Errors.raise_error uu____25384 orig_arg.FStar_Syntax_Syntax.pos))
end)
in (

let guards1 = (FStar_All.pipe_right guards (FStar_List.collect (fun g -> (

let uu____25406 = (

let uu____25407 = (FStar_SMTEncoding_Term.free_variables g)
in (FStar_List.contains fv1 uu____25407))
in (match (uu____25406) with
| true -> begin
(

let uu____25420 = (FStar_SMTEncoding_Term.subst g fv1 xv)
in (uu____25420)::[])
end
| uu____25421 -> begin
[]
end)))))
in (FStar_SMTEncoding_Util.mk_and_l guards1))))
in (

let uu____25422 = (

let uu____25435 = (FStar_List.zip args encoded_args)
in (FStar_List.fold_left (fun uu____25485 uu____25486 -> (match (((uu____25485), (uu____25486))) with
| ((env2, arg_vars, eqns_or_guards, i), (orig_arg, arg)) -> begin
(

let uu____25581 = (

let uu____25588 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (gen_term_var env2 uu____25588))
in (match (uu____25581) with
| (uu____25601, xv, env3) -> begin
(

let eqns = (match ((i < n_tps)) with
| true -> begin
(

let uu____25609 = (guards_for_parameter (FStar_Pervasives_Native.fst orig_arg) arg xv)
in (uu____25609)::eqns_or_guards)
end
| uu____25610 -> begin
(

let uu____25611 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (uu____25611)::eqns_or_guards)
end)
in ((env3), ((xv)::arg_vars), (eqns), ((i + (Prims.parse_int "1")))))
end))
end)) ((env'), ([]), ([]), ((Prims.parse_int "0"))) uu____25435))
in (match (uu____25422) with
| (uu____25626, arg_vars, elim_eqns_or_guards, uu____25629) -> begin
(

let arg_vars1 = (FStar_List.rev arg_vars)
in (

let ty = (maybe_curry_app fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.p (FStar_SMTEncoding_Term.Var (encoded_head)) encoded_head_arity arg_vars1)
in (

let xvars1 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp1 = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars1)))
in (

let ty_pred = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (FStar_Pervasives_Native.Some (s_fuel_tm)) dapp1 ty)
in (

let arg_binders = (FStar_List.map FStar_SMTEncoding_Term.fv_of_term arg_vars1)
in (

let typing_inversion = (

let uu____25657 = (

let uu____25664 = (

let uu____25665 = (

let uu____25676 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____25687 = (

let uu____25688 = (

let uu____25693 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append elim_eqns_or_guards guards))
in ((ty_pred), (uu____25693)))
in (FStar_SMTEncoding_Util.mkImp uu____25688))
in ((((ty_pred)::[])::[]), (uu____25676), (uu____25687))))
in (FStar_SMTEncoding_Util.mkForall uu____25665))
in ((uu____25664), (FStar_Pervasives_Native.Some ("data constructor typing elim")), ((Prims.strcat "data_elim_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____25657))
in (

let subterm_ordering = (match ((FStar_Ident.lid_equals d FStar_Parser_Const.lextop_lid)) with
| true -> begin
(

let x = (

let uu____25716 = (varops.fresh "x")
in ((uu____25716), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (

let uu____25718 = (

let uu____25725 = (

let uu____25726 = (

let uu____25737 = (

let uu____25742 = (

let uu____25745 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in (uu____25745)::[])
in (uu____25742)::[])
in (

let uu____25750 = (

let uu____25751 = (

let uu____25756 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (

let uu____25757 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in ((uu____25756), (uu____25757))))
in (FStar_SMTEncoding_Util.mkImp uu____25751))
in ((uu____25737), ((x)::[]), (uu____25750))))
in (FStar_SMTEncoding_Util.mkForall uu____25726))
in (

let uu____25776 = (varops.mk_unique "lextop")
in ((uu____25725), (FStar_Pervasives_Native.Some ("lextop is top")), (uu____25776))))
in (FStar_SMTEncoding_Util.mkAssume uu____25718))))
end
| uu____25779 -> begin
(

let prec = (

let uu____25783 = (FStar_All.pipe_right vars (FStar_List.mapi (fun i v1 -> (match ((i < n_tps)) with
| true -> begin
[]
end
| uu____25810 -> begin
(

let uu____25811 = (

let uu____25812 = (FStar_SMTEncoding_Util.mkFreeV v1)
in (FStar_SMTEncoding_Util.mk_Precedes uu____25812 dapp1))
in (uu____25811)::[])
end))))
in (FStar_All.pipe_right uu____25783 FStar_List.flatten))
in (

let uu____25819 = (

let uu____25826 = (

let uu____25827 = (

let uu____25838 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____25849 = (

let uu____25850 = (

let uu____25855 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (uu____25855)))
in (FStar_SMTEncoding_Util.mkImp uu____25850))
in ((((ty_pred)::[])::[]), (uu____25838), (uu____25849))))
in (FStar_SMTEncoding_Util.mkForall uu____25827))
in ((uu____25826), (FStar_Pervasives_Native.Some ("subterm ordering")), ((Prims.strcat "subterm_ordering_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____25819)))
end)
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end)))
end))
end))
end
| uu____25874 -> begin
((

let uu____25876 = (

let uu____25881 = (

let uu____25882 = (FStar_Syntax_Print.lid_to_string d)
in (

let uu____25883 = (FStar_Syntax_Print.term_to_string head1)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" uu____25882 uu____25883)))
in ((FStar_Errors.Warning_ConstructorBuildsUnexpectedType), (uu____25881)))
in (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng uu____25876));
(([]), ([]));
)
end))
end)))
in (

let uu____25888 = (encode_elim ())
in (match (uu____25888) with
| (decls2, elim) -> begin
(

let g = (

let uu____25908 = (

let uu____25911 = (

let uu____25914 = (

let uu____25917 = (

let uu____25920 = (

let uu____25921 = (

let uu____25932 = (

let uu____25935 = (

let uu____25936 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" uu____25936))
in FStar_Pervasives_Native.Some (uu____25935))
in ((ddtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (uu____25932)))
in FStar_SMTEncoding_Term.DeclFun (uu____25921))
in (uu____25920)::[])
in (

let uu____25941 = (

let uu____25944 = (

let uu____25947 = (

let uu____25950 = (

let uu____25953 = (

let uu____25956 = (

let uu____25959 = (

let uu____25960 = (

let uu____25967 = (

let uu____25968 = (

let uu____25979 = (FStar_SMTEncoding_Util.mkEq ((app), (dapp)))
in ((((app)::[])::[]), (vars), (uu____25979)))
in (FStar_SMTEncoding_Util.mkForall uu____25968))
in ((uu____25967), (FStar_Pervasives_Native.Some ("equality for proxy")), ((Prims.strcat "equality_tok_" ddtok))))
in (FStar_SMTEncoding_Util.mkAssume uu____25960))
in (

let uu____25992 = (

let uu____25995 = (

let uu____25996 = (

let uu____26003 = (

let uu____26004 = (

let uu____26015 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) vars')
in (

let uu____26026 = (FStar_SMTEncoding_Util.mkImp ((guard'), (ty_pred')))
in ((((ty_pred')::[])::[]), (uu____26015), (uu____26026))))
in (FStar_SMTEncoding_Util.mkForall uu____26004))
in ((uu____26003), (FStar_Pervasives_Native.Some ("data constructor typing intro")), ((Prims.strcat "data_typing_intro_" ddtok))))
in (FStar_SMTEncoding_Util.mkAssume uu____25996))
in (uu____25995)::[])
in (uu____25959)::uu____25992))
in ((FStar_SMTEncoding_Util.mkAssume ((tok_typing1), (FStar_Pervasives_Native.Some ("typing for data constructor proxy")), ((Prims.strcat "typing_tok_" ddtok)))))::uu____25956)
in (FStar_List.append uu____25953 elim))
in (FStar_List.append decls_pred uu____25950))
in (FStar_List.append decls_formals uu____25947))
in (FStar_List.append proxy_fresh uu____25944))
in (FStar_List.append uu____25917 uu____25941)))
in (FStar_List.append decls3 uu____25914))
in (FStar_List.append decls2 uu____25911))
in (FStar_List.append binder_decls uu____25908))
in (((FStar_List.append datacons g)), (env1)))
end)))))
end))
end)))
end))))))))
end)))
end)))
end)))
end)))
end))))
and encode_sigelts : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun uu____26072 se -> (match (uu____26072) with
| (g, env1) -> begin
(

let uu____26092 = (encode_sigelt env1 se)
in (match (uu____26092) with
| (g', env2) -> begin
(((FStar_List.append g g')), (env2))
end))
end)) (([]), (env)))))


let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env bindings -> (

let encode_binding = (fun b uu____26149 -> (match (uu____26149) with
| (i, decls, env1) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (uu____26181) -> begin
(((i + (Prims.parse_int "1"))), ([]), (env1))
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env1.tcenv x.FStar_Syntax_Syntax.sort)
in ((

let uu____26187 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____26187) with
| true -> begin
(

let uu____26188 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____26189 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____26190 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" uu____26188 uu____26189 uu____26190))))
end
| uu____26191 -> begin
()
end));
(

let uu____26192 = (encode_term t1 env1)
in (match (uu____26192) with
| (t, decls') -> begin
(

let t_hash = (FStar_SMTEncoding_Term.hash_of_term t)
in (

let uu____26208 = (

let uu____26215 = (

let uu____26216 = (

let uu____26217 = (FStar_Util.digest_of_string t_hash)
in (Prims.strcat uu____26217 (Prims.strcat "_" (Prims.string_of_int i))))
in (Prims.strcat "x_" uu____26216))
in (new_term_constant_from_string env1 x uu____26215))
in (match (uu____26208) with
| (xxsym, xx, env') -> begin
(

let t2 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel FStar_Pervasives_Native.None xx t)
in (

let caption = (

let uu____26233 = (FStar_Options.log_queries ())
in (match (uu____26233) with
| true -> begin
(

let uu____26236 = (

let uu____26237 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____26238 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____26239 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" uu____26237 uu____26238 uu____26239))))
in FStar_Pervasives_Native.Some (uu____26236))
end
| uu____26240 -> begin
FStar_Pervasives_Native.None
end))
in (

let ax = (

let a_name = (Prims.strcat "binder_" xxsym)
in (FStar_SMTEncoding_Util.mkAssume ((t2), (FStar_Pervasives_Native.Some (a_name)), (a_name))))
in (

let g = (FStar_List.append ((FStar_SMTEncoding_Term.DeclFun (((xxsym), ([]), (FStar_SMTEncoding_Term.Term_sort), (caption))))::[]) (FStar_List.append decls' ((ax)::[])))
in (((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))))))
end)))
end));
))
end
| FStar_TypeChecker_Env.Binding_lid (x, (uu____26255, t)) -> begin
(

let t_norm = (whnf env1 t)
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____26269 = (encode_free_var false env1 fv t t_norm [])
in (match (uu____26269) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))))
end
| FStar_TypeChecker_Env.Binding_sig_inst (uu____26292, se, uu____26294) -> begin
(

let uu____26299 = (encode_sigelt env1 se)
in (match (uu____26299) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))
end
| FStar_TypeChecker_Env.Binding_sig (uu____26316, se) -> begin
(

let uu____26322 = (encode_sigelt env1 se)
in (match (uu____26322) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))
end)
end))
in (

let uu____26339 = (FStar_List.fold_right encode_binding bindings (((Prims.parse_int "0")), ([]), (env)))
in (match (uu____26339) with
| (uu____26362, decls, env1) -> begin
((decls), (env1))
end))))


let encode_labels : 'Auu____26374 'Auu____26375 . ((Prims.string * FStar_SMTEncoding_Term.sort) * 'Auu____26374 * 'Auu____26375) Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl Prims.list) = (fun labs -> (

let prefix1 = (FStar_All.pipe_right labs (FStar_List.map (fun uu____26443 -> (match (uu____26443) with
| (l, uu____26455, uu____26456) -> begin
FStar_SMTEncoding_Term.DeclFun ((((FStar_Pervasives_Native.fst l)), ([]), (FStar_SMTEncoding_Term.Bool_sort), (FStar_Pervasives_Native.None)))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun uu____26502 -> (match (uu____26502) with
| (l, uu____26516, uu____26517) -> begin
(

let uu____26526 = (FStar_All.pipe_left (fun _0_44 -> FStar_SMTEncoding_Term.Echo (_0_44)) (FStar_Pervasives_Native.fst l))
in (

let uu____26527 = (

let uu____26530 = (

let uu____26531 = (FStar_SMTEncoding_Util.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (uu____26531))
in (uu____26530)::[])
in (uu____26526)::uu____26527))
end))))
in ((prefix1), (suffix)))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (

let uu____26580 = (

let uu____26583 = (

let uu____26584 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (

let uu____26587 = (

let uu____26588 = (FStar_TypeChecker_Env.current_module tcenv)
in (FStar_All.pipe_right uu____26588 FStar_Ident.string_of_lid))
in {bindings = []; depth = (Prims.parse_int "0"); tcenv = tcenv; warn = true; cache = uu____26584; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true; current_module_name = uu____26587}))
in (uu____26583)::[])
in (FStar_ST.op_Colon_Equals last_env uu____26580)))


let get_env : FStar_Ident.lident  ->  FStar_TypeChecker_Env.env  ->  env_t = (fun cmn tcenv -> (

let uu____26624 = (FStar_ST.op_Bang last_env)
in (match (uu____26624) with
| [] -> begin
(failwith "No env; call init first!")
end
| (e)::uu____26657 -> begin
(

let uu___134_26660 = e
in (

let uu____26661 = (FStar_Ident.string_of_lid cmn)
in {bindings = uu___134_26660.bindings; depth = uu___134_26660.depth; tcenv = tcenv; warn = uu___134_26660.warn; cache = uu___134_26660.cache; nolabels = uu___134_26660.nolabels; use_zfuel_name = uu___134_26660.use_zfuel_name; encode_non_total_function_typ = uu___134_26660.encode_non_total_function_typ; current_module_name = uu____26661}))
end)))


let set_env : env_t  ->  Prims.unit = (fun env -> (

let uu____26665 = (FStar_ST.op_Bang last_env)
in (match (uu____26665) with
| [] -> begin
(failwith "Empty env stack")
end
| (uu____26697)::tl1 -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl1))
end)))


let push_env : Prims.unit  ->  Prims.unit = (fun uu____26732 -> (

let uu____26733 = (FStar_ST.op_Bang last_env)
in (match (uu____26733) with
| [] -> begin
(failwith "Empty env stack")
end
| (hd1)::tl1 -> begin
(

let refs = (FStar_Util.smap_copy hd1.cache)
in (

let top = (

let uu___135_26773 = hd1
in {bindings = uu___135_26773.bindings; depth = uu___135_26773.depth; tcenv = uu___135_26773.tcenv; warn = uu___135_26773.warn; cache = refs; nolabels = uu___135_26773.nolabels; use_zfuel_name = uu___135_26773.use_zfuel_name; encode_non_total_function_typ = uu___135_26773.encode_non_total_function_typ; current_module_name = uu___135_26773.current_module_name})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd1)::tl1))))
end)))


let pop_env : Prims.unit  ->  Prims.unit = (fun uu____26805 -> (

let uu____26806 = (FStar_ST.op_Bang last_env)
in (match (uu____26806) with
| [] -> begin
(failwith "Popping an empty stack")
end
| (uu____26838)::tl1 -> begin
(FStar_ST.op_Colon_Equals last_env tl1)
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


let open_fact_db_tags : env_t  ->  FStar_SMTEncoding_Term.fact_db_id Prims.list = (fun env -> [])


let place_decl_in_fact_dbs : env_t  ->  FStar_SMTEncoding_Term.fact_db_id Prims.list  ->  FStar_SMTEncoding_Term.decl  ->  FStar_SMTEncoding_Term.decl = (fun env fact_db_ids d -> (match (((fact_db_ids), (d))) with
| ((uu____26908)::uu____26909, FStar_SMTEncoding_Term.Assume (a)) -> begin
FStar_SMTEncoding_Term.Assume ((

let uu___136_26917 = a
in {FStar_SMTEncoding_Term.assumption_term = uu___136_26917.FStar_SMTEncoding_Term.assumption_term; FStar_SMTEncoding_Term.assumption_caption = uu___136_26917.FStar_SMTEncoding_Term.assumption_caption; FStar_SMTEncoding_Term.assumption_name = uu___136_26917.FStar_SMTEncoding_Term.assumption_name; FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids}))
end
| uu____26918 -> begin
d
end))


let fact_dbs_for_lid : env_t  ->  FStar_Ident.lid  ->  FStar_SMTEncoding_Term.fact_db_id Prims.list = (fun env lid -> (

let uu____26933 = (

let uu____26936 = (

let uu____26937 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in FStar_SMTEncoding_Term.Namespace (uu____26937))
in (

let uu____26938 = (open_fact_db_tags env)
in (uu____26936)::uu____26938))
in (FStar_SMTEncoding_Term.Name (lid))::uu____26933))


let encode_top_level_facts : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env se -> (

let fact_db_ids = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.collect (fact_dbs_for_lid env)))
in (

let uu____26960 = (encode_sigelt env se)
in (match (uu____26960) with
| (g, env1) -> begin
(

let g1 = (FStar_All.pipe_right g (FStar_List.map (place_decl_in_fact_dbs env1 fact_db_ids)))
in ((g1), (env1)))
end))))


let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (

let caption = (fun decls -> (

let uu____26996 = (FStar_Options.log_queries ())
in (match (uu____26996) with
| true -> begin
(

let uu____26999 = (

let uu____27000 = (

let uu____27001 = (

let uu____27002 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.map FStar_Syntax_Print.lid_to_string))
in (FStar_All.pipe_right uu____27002 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " uu____27001))
in FStar_SMTEncoding_Term.Caption (uu____27000))
in (uu____26999)::decls)
end
| uu____27011 -> begin
decls
end)))
in ((

let uu____27013 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____27013) with
| true -> begin
(

let uu____27014 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____27014))
end
| uu____27015 -> begin
()
end));
(

let env = (

let uu____27017 = (FStar_TypeChecker_Env.current_module tcenv)
in (get_env uu____27017 tcenv))
in (

let uu____27018 = (encode_top_level_facts env se)
in (match (uu____27018) with
| (decls, env1) -> begin
((set_env env1);
(

let uu____27032 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 uu____27032));
)
end)));
)))


let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____27042 -> begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in ((

let uu____27044 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____27044) with
| true -> begin
(

let uu____27045 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) Prims.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name uu____27045))
end
| uu____27046 -> begin
()
end));
(

let env = (get_env modul.FStar_Syntax_Syntax.name tcenv)
in (

let encode_signature = (fun env1 ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun uu____27080 se -> (match (uu____27080) with
| (g, env2) -> begin
(

let uu____27100 = (encode_top_level_facts env2 se)
in (match (uu____27100) with
| (g', env3) -> begin
(((FStar_List.append g g')), (env3))
end))
end)) (([]), (env1)))))
in (

let uu____27123 = (encode_signature (

let uu___137_27132 = env
in {bindings = uu___137_27132.bindings; depth = uu___137_27132.depth; tcenv = uu___137_27132.tcenv; warn = false; cache = uu___137_27132.cache; nolabels = uu___137_27132.nolabels; use_zfuel_name = uu___137_27132.use_zfuel_name; encode_non_total_function_typ = uu___137_27132.encode_non_total_function_typ; current_module_name = uu___137_27132.current_module_name}) modul.FStar_Syntax_Syntax.exports)
in (match (uu____27123) with
| (decls, env1) -> begin
(

let caption = (fun decls1 -> (

let uu____27149 = (FStar_Options.log_queries ())
in (match (uu____27149) with
| true -> begin
(

let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::decls1) ((FStar_SMTEncoding_Term.Caption ((Prims.strcat "End " msg)))::[])))
end
| uu____27153 -> begin
decls1
end)))
in ((set_env (

let uu___138_27157 = env1
in {bindings = uu___138_27157.bindings; depth = uu___138_27157.depth; tcenv = uu___138_27157.tcenv; warn = true; cache = uu___138_27157.cache; nolabels = uu___138_27157.nolabels; use_zfuel_name = uu___138_27157.use_zfuel_name; encode_non_total_function_typ = uu___138_27157.encode_non_total_function_typ; current_module_name = uu___138_27157.current_module_name}));
(

let uu____27159 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____27159) with
| true -> begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end
| uu____27160 -> begin
()
end));
(

let decls1 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls1));
))
end))));
)))


let encode_query : (Prims.unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_ErrorReporting.label Prims.list * FStar_SMTEncoding_Term.decl * FStar_SMTEncoding_Term.decl Prims.list) = (fun use_env_msg tcenv q -> ((

let uu____27211 = (

let uu____27212 = (FStar_TypeChecker_Env.current_module tcenv)
in uu____27212.FStar_Ident.str)
in (FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name uu____27211));
(

let env = (

let uu____27214 = (FStar_TypeChecker_Env.current_module tcenv)
in (get_env uu____27214 tcenv))
in (

let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (

let uu____27226 = (

let rec aux = (fun bindings1 -> (match (bindings1) with
| (FStar_TypeChecker_Env.Binding_var (x))::rest -> begin
(

let uu____27261 = (aux rest)
in (match (uu____27261) with
| (out, rest1) -> begin
(

let t = (

let uu____27291 = (FStar_Syntax_Util.destruct_typ_as_formula x.FStar_Syntax_Syntax.sort)
in (match (uu____27291) with
| FStar_Pervasives_Native.Some (uu____27296) -> begin
(

let uu____27297 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.t_unit)
in (FStar_Syntax_Util.refine uu____27297 x.FStar_Syntax_Syntax.sort))
end
| uu____27298 -> begin
x.FStar_Syntax_Syntax.sort
end))
in (

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
in (

let uu____27302 = (

let uu____27305 = (FStar_Syntax_Syntax.mk_binder (

let uu___139_27308 = x
in {FStar_Syntax_Syntax.ppname = uu___139_27308.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___139_27308.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in (uu____27305)::out)
in ((uu____27302), (rest1)))))
end))
end
| uu____27313 -> begin
(([]), (bindings1))
end))
in (

let uu____27320 = (aux bindings)
in (match (uu____27320) with
| (closing, bindings1) -> begin
(

let uu____27345 = (FStar_Syntax_Util.close_forall_no_univs (FStar_List.rev closing) q)
in ((uu____27345), (bindings1)))
end)))
in (match (uu____27226) with
| (q1, bindings1) -> begin
(

let uu____27368 = (

let uu____27373 = (FStar_List.filter (fun uu___104_27378 -> (match (uu___104_27378) with
| FStar_TypeChecker_Env.Binding_sig (uu____27379) -> begin
false
end
| uu____27386 -> begin
true
end)) bindings1)
in (encode_env_bindings env uu____27373))
in (match (uu____27368) with
| (env_decls, env1) -> begin
((

let uu____27404 = (((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTQuery"))))
in (match (uu____27404) with
| true -> begin
(

let uu____27405 = (FStar_Syntax_Print.term_to_string q1)
in (FStar_Util.print1 "Encoding query formula: %s\n" uu____27405))
end
| uu____27406 -> begin
()
end));
(

let uu____27407 = (encode_formula q1 env1)
in (match (uu____27407) with
| (phi, qdecls) -> begin
(

let uu____27428 = (

let uu____27433 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg uu____27433 phi))
in (match (uu____27428) with
| (labels, phi1) -> begin
(

let uu____27450 = (encode_labels labels)
in (match (uu____27450) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append env_decls (FStar_List.append label_prefix qdecls))
in (

let qry = (

let uu____27487 = (

let uu____27494 = (FStar_SMTEncoding_Util.mkNot phi1)
in (

let uu____27495 = (varops.mk_unique "@query")
in ((uu____27494), (FStar_Pervasives_Native.Some ("query")), (uu____27495))))
in (FStar_SMTEncoding_Util.mkAssume uu____27487))
in (

let suffix = (FStar_List.append ((FStar_SMTEncoding_Term.Echo ("<labels>"))::[]) (FStar_List.append label_suffix ((FStar_SMTEncoding_Term.Echo ("</labels>"))::(FStar_SMTEncoding_Term.Echo ("Done!"))::[])))
in ((query_prelude), (labels), (qry), (suffix)))))
end))
end))
end));
)
end))
end))));
))




