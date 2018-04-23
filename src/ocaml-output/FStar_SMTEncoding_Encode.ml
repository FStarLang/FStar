
open Prims
open FStar_Pervasives

let add_fuel : 'Auu____7 . 'Auu____7  ->  'Auu____7 Prims.list  ->  'Auu____7 Prims.list = (fun x tl1 -> (

let uu____24 = (FStar_Options.unthrottle_inductives ())
in (match (uu____24) with
| true -> begin
tl1
end
| uu____27 -> begin
(x)::tl1
end)))


let withenv : 'Auu____38 'Auu____39 'Auu____40 . 'Auu____38  ->  ('Auu____39 * 'Auu____40)  ->  ('Auu____39 * 'Auu____40 * 'Auu____38) = (fun c uu____60 -> (match (uu____60) with
| (a, b) -> begin
((a), (b), (c))
end))


let vargs : 'Auu____75 'Auu____76 'Auu____77 . (('Auu____75, 'Auu____76) FStar_Util.either * 'Auu____77) Prims.list  ->  (('Auu____75, 'Auu____76) FStar_Util.either * 'Auu____77) Prims.list = (fun args -> (FStar_List.filter (fun uu___83_124 -> (match (uu___83_124) with
| (FStar_Util.Inl (uu____133), uu____134) -> begin
false
end
| uu____139 -> begin
true
end)) args))


let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s 39 (*'*) 95 (*_*)))


let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun lid a -> (

let a1 = (

let uu___106_166 = a
in (

let uu____167 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = uu____167; FStar_Syntax_Syntax.index = uu___106_166.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___106_166.FStar_Syntax_Syntax.sort}))
in (

let uu____168 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str a1.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (FStar_All.pipe_left escape uu____168))))


let primitive_projector_by_pos : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (

let fail1 = (fun uu____189 -> (

let uu____190 = (FStar_Util.format2 "Projector %s on data constructor %s not found" (Prims.string_of_int i) lid.FStar_Ident.str)
in (failwith uu____190)))
in (

let uu____191 = (FStar_TypeChecker_Env.lookup_datacon env lid)
in (match (uu____191) with
| (uu____196, t) -> begin
(

let uu____198 = (

let uu____199 = (FStar_Syntax_Subst.compress t)
in uu____199.FStar_Syntax_Syntax.n)
in (match (uu____198) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____220 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____220) with
| (binders, uu____226) -> begin
(match (((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders)))) with
| true -> begin
(fail1 ())
end
| uu____231 -> begin
(

let b = (FStar_List.nth binders i)
in (mk_term_projector_name lid (FStar_Pervasives_Native.fst b)))
end)
end))
end
| uu____241 -> begin
(fail1 ())
end))
end))))


let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (

let uu____252 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str (Prims.string_of_int i))
in (FStar_All.pipe_left escape uu____252)))


let mk_term_projector : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun lid a -> (

let uu____263 = (

let uu____268 = (mk_term_projector_name lid a)
in ((uu____268), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Util.mkFreeV uu____263)))


let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_SMTEncoding_Term.term = (fun lid i -> (

let uu____279 = (

let uu____284 = (mk_term_projector_name_by_pos lid i)
in ((uu____284), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Util.mkFreeV uu____279)))


let mk_data_tester : 'Auu____293 . 'Auu____293  ->  FStar_Ident.lident  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (fun env l x -> (FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x))

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

let new_scope = (fun uu____794 -> (

let uu____795 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (

let uu____798 = (FStar_Util.smap_create (Prims.parse_int "100"))
in ((uu____795), (uu____798)))))
in (

let scopes = (

let uu____818 = (

let uu____829 = (new_scope ())
in (uu____829)::[])
in (FStar_Util.mk_ref uu____818))
in (

let mk_unique = (fun y -> (

let y1 = (escape y)
in (

let y2 = (

let uu____872 = (

let uu____875 = (FStar_ST.op_Bang scopes)
in (FStar_Util.find_map uu____875 (fun uu____962 -> (match (uu____962) with
| (names1, uu____974) -> begin
(FStar_Util.smap_try_find names1 y1)
end))))
in (match (uu____872) with
| FStar_Pervasives_Native.None -> begin
y1
end
| FStar_Pervasives_Native.Some (uu____983) -> begin
((FStar_Util.incr ctr);
(

let uu____1018 = (

let uu____1019 = (

let uu____1020 = (FStar_ST.op_Bang ctr)
in (Prims.string_of_int uu____1020))
in (Prims.strcat "__" uu____1019))
in (Prims.strcat y1 uu____1018));
)
end))
in (

let top_scope = (

let uu____1069 = (

let uu____1078 = (FStar_ST.op_Bang scopes)
in (FStar_List.hd uu____1078))
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1069))
in ((FStar_Util.smap_add top_scope y2 true);
y2;
)))))
in (

let new_var = (fun pp rn -> (FStar_All.pipe_left mk_unique (Prims.strcat pp.FStar_Ident.idText (Prims.strcat "__" (Prims.string_of_int rn)))))
in (

let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (

let next_id1 = (fun uu____1199 -> ((FStar_Util.incr ctr);
(FStar_ST.op_Bang ctr);
))
in (

let fresh1 = (fun pfx -> (

let uu____1285 = (

let uu____1286 = (next_id1 ())
in (FStar_All.pipe_left Prims.string_of_int uu____1286))
in (FStar_Util.format2 "%s_%s" pfx uu____1285)))
in (

let string_const = (fun s -> (

let uu____1293 = (

let uu____1296 = (FStar_ST.op_Bang scopes)
in (FStar_Util.find_map uu____1296 (fun uu____1383 -> (match (uu____1383) with
| (uu____1394, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))
in (match (uu____1293) with
| FStar_Pervasives_Native.Some (f) -> begin
f
end
| FStar_Pervasives_Native.None -> begin
(

let id1 = (next_id1 ())
in (

let f = (

let uu____1407 = (FStar_SMTEncoding_Util.mk_String_const id1)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1407))
in (

let top_scope = (

let uu____1411 = (

let uu____1420 = (FStar_ST.op_Bang scopes)
in (FStar_List.hd uu____1420))
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1411))
in ((FStar_Util.smap_add top_scope s f);
f;
))))
end)))
in (

let push1 = (fun uu____1524 -> (

let uu____1525 = (

let uu____1536 = (new_scope ())
in (

let uu____1545 = (FStar_ST.op_Bang scopes)
in (uu____1536)::uu____1545))
in (FStar_ST.op_Colon_Equals scopes uu____1525)))
in (

let pop1 = (fun uu____1699 -> (

let uu____1700 = (

let uu____1711 = (FStar_ST.op_Bang scopes)
in (FStar_List.tl uu____1711))
in (FStar_ST.op_Colon_Equals scopes uu____1700)))
in {push = push1; pop = pop1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; string_const = string_const; next_id = next_id1; mk_unique = mk_unique}))))))))))))


let unmangle : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv = (fun x -> (

let uu___107_1865 = x
in (

let uu____1866 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = uu____1866; FStar_Syntax_Syntax.index = uu___107_1865.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___107_1865.FStar_Syntax_Syntax.sort})))

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
| uu____1998 -> begin
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
| uu____2024 -> begin
false
end))


let __proj__Binding_fvar__item___0 : binding  ->  fvar_binding = (fun projectee -> (match (projectee) with
| Binding_fvar (_0) -> begin
_0
end))


let binder_of_eithervar : 'Auu____2038 'Auu____2039 . 'Auu____2038  ->  ('Auu____2038 * 'Auu____2039 FStar_Pervasives_Native.option) = (fun v1 -> ((v1), (FStar_Pervasives_Native.None)))

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


let mk_cache_entry : 'Auu____2380 . 'Auu____2380  ->  Prims.string  ->  FStar_SMTEncoding_Term.sort Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  cache_entry = (fun env tsym cvar_sorts t_decls1 -> (

let names1 = (FStar_All.pipe_right t_decls1 (FStar_List.collect (fun uu___84_2418 -> (match (uu___84_2418) with
| FStar_SMTEncoding_Term.Assume (a) -> begin
(a.FStar_SMTEncoding_Term.assumption_name)::[]
end
| uu____2422 -> begin
[]
end))))
in {cache_symbol_name = tsym; cache_symbol_arg_sorts = cvar_sorts; cache_symbol_decls = t_decls1; cache_symbol_assumption_names = names1}))


let use_cache_entry : cache_entry  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun ce -> (FStar_SMTEncoding_Term.RetainAssumptions (ce.cache_symbol_assumption_names))::[])


let print_env : env_t  ->  Prims.string = (fun e -> (

let vars = (

let uu____2438 = (FStar_Util.prefix_until (fun uu___85_2453 -> (match (uu___85_2453) with
| Binding_fvar (uu____2454) -> begin
true
end
| uu____2455 -> begin
false
end)) e.bindings)
in (match (uu____2438) with
| FStar_Pervasives_Native.None -> begin
e.bindings
end
| FStar_Pervasives_Native.Some (vars, fv, uu____2470) -> begin
(FStar_List.append vars ((fv)::[]))
end))
in (

let uu____2489 = (FStar_All.pipe_right vars (FStar_List.map (fun uu___86_2499 -> (match (uu___86_2499) with
| Binding_var (x, uu____2501) -> begin
(FStar_Syntax_Print.bv_to_string x)
end
| Binding_fvar (fvb) -> begin
(FStar_Syntax_Print.lid_to_string fvb.fvar_lid)
end))))
in (FStar_All.pipe_right uu____2489 (FStar_String.concat ", ")))))


let lookup_binding : 'Auu____2511 . env_t  ->  (binding  ->  'Auu____2511 FStar_Pervasives_Native.option)  ->  'Auu____2511 FStar_Pervasives_Native.option = (fun env f -> (FStar_Util.find_map env.bindings f))


let caption_t : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.string FStar_Pervasives_Native.option = (fun env t -> (

let uu____2545 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____2545) with
| true -> begin
(

let uu____2548 = (FStar_Syntax_Print.term_to_string t)
in FStar_Pervasives_Native.Some (uu____2548))
end
| uu____2549 -> begin
FStar_Pervasives_Native.None
end)))


let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (

let xsym = (varops.fresh x)
in (

let uu____2565 = (FStar_SMTEncoding_Util.mkFreeV ((xsym), (s)))
in ((xsym), (uu____2565)))))


let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (Prims.strcat "@x" (Prims.string_of_int env.depth))
in (

let y = (FStar_SMTEncoding_Util.mkFreeV ((ysym), (FStar_SMTEncoding_Term.Term_sort)))
in ((ysym), (y), ((

let uu___108_2585 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = (env.depth + (Prims.parse_int "1")); tcenv = uu___108_2585.tcenv; warn = uu___108_2585.warn; cache = uu___108_2585.cache; nolabels = uu___108_2585.nolabels; use_zfuel_name = uu___108_2585.use_zfuel_name; encode_non_total_function_typ = uu___108_2585.encode_non_total_function_typ; current_module_name = uu___108_2585.current_module_name}))))))


let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let uu___109_2607 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = uu___109_2607.depth; tcenv = uu___109_2607.tcenv; warn = uu___109_2607.warn; cache = uu___109_2607.cache; nolabels = uu___109_2607.nolabels; use_zfuel_name = uu___109_2607.use_zfuel_name; encode_non_total_function_typ = uu___109_2607.encode_non_total_function_typ; current_module_name = uu___109_2607.current_module_name}))))))


let new_term_constant_from_string : env_t  ->  FStar_Syntax_Syntax.bv  ->  Prims.string  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x str -> (

let ysym = (varops.mk_unique str)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let uu___110_2634 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = uu___110_2634.depth; tcenv = uu___110_2634.tcenv; warn = uu___110_2634.warn; cache = uu___110_2634.cache; nolabels = uu___110_2634.nolabels; use_zfuel_name = uu___110_2634.use_zfuel_name; encode_non_total_function_typ = uu___110_2634.encode_non_total_function_typ; current_module_name = uu___110_2634.current_module_name}))))))


let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (

let uu___111_2650 = env
in {bindings = (Binding_var (((x), (t))))::env.bindings; depth = uu___111_2650.depth; tcenv = uu___111_2650.tcenv; warn = uu___111_2650.warn; cache = uu___111_2650.cache; nolabels = uu___111_2650.nolabels; use_zfuel_name = uu___111_2650.use_zfuel_name; encode_non_total_function_typ = uu___111_2650.encode_non_total_function_typ; current_module_name = uu___111_2650.current_module_name}))


let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let aux = (fun a' -> (lookup_binding env (fun uu___87_2680 -> (match (uu___87_2680) with
| Binding_var (b, t) when (FStar_Syntax_Syntax.bv_eq b a') -> begin
FStar_Pervasives_Native.Some (((b), (t)))
end
| uu____2693 -> begin
FStar_Pervasives_Native.None
end))))
in (

let uu____2698 = (aux a)
in (match (uu____2698) with
| FStar_Pervasives_Native.None -> begin
(

let a2 = (unmangle a)
in (

let uu____2710 = (aux a2)
in (match (uu____2710) with
| FStar_Pervasives_Native.None -> begin
(

let uu____2721 = (

let uu____2722 = (FStar_Syntax_Print.bv_to_string a2)
in (

let uu____2723 = (print_env env)
in (FStar_Util.format2 "Bound term variable not found (after unmangling): %s in environment: %s" uu____2722 uu____2723)))
in (failwith uu____2721))
end
| FStar_Pervasives_Native.Some (b, t) -> begin
t
end)))
end
| FStar_Pervasives_Native.Some (b, t) -> begin
t
end))))


let mk_fvb : FStar_Ident.lident  ->  Prims.string  ->  Prims.int  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  fvar_binding = (fun lid fname arity ftok fuel_partial_app -> {fvar_lid = lid; smt_arity = arity; smt_id = fname; smt_token = ftok; smt_fuel_partial_app = fuel_partial_app})


let aux_check_push_fvar : env_t  ->  fvar_binding  ->  env_t = (fun env fvb -> (

let uu___112_2779 = env
in {bindings = (Binding_fvar (fvb))::env.bindings; depth = uu___112_2779.depth; tcenv = uu___112_2779.tcenv; warn = uu___112_2779.warn; cache = uu___112_2779.cache; nolabels = uu___112_2779.nolabels; use_zfuel_name = uu___112_2779.use_zfuel_name; encode_non_total_function_typ = uu___112_2779.encode_non_total_function_typ; current_module_name = uu___112_2779.current_module_name}))


let new_term_constant_and_tok_from_lid : env_t  ->  FStar_Ident.lident  ->  Prims.int  ->  (Prims.string * Prims.string * env_t) = (fun env x arity -> (

let fname = (varops.new_fvar x)
in (

let ftok_name = (Prims.strcat fname "@tok")
in (

let ftok = (FStar_SMTEncoding_Util.mkApp ((ftok_name), ([])))
in (

let fvb = (mk_fvb x fname arity (FStar_Pervasives_Native.Some (ftok)) FStar_Pervasives_Native.None)
in ((fname), (ftok_name), ((aux_check_push_fvar env fvb))))))))


let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  fvar_binding FStar_Pervasives_Native.option = (fun env a -> (lookup_binding env (fun uu___88_2821 -> (match (uu___88_2821) with
| Binding_fvar (fvb) when (FStar_Ident.lid_equals fvb.fvar_lid a) -> begin
FStar_Pervasives_Native.Some (fvb)
end
| uu____2825 -> begin
FStar_Pervasives_Native.None
end))))


let contains_name : env_t  ->  Prims.string  ->  Prims.bool = (fun env s -> (

let uu____2836 = (lookup_binding env (fun uu___89_2841 -> (match (uu___89_2841) with
| Binding_fvar (fvb) when (Prims.op_Equality fvb.fvar_lid.FStar_Ident.str s) -> begin
FStar_Pervasives_Native.Some (())
end
| uu____2845 -> begin
FStar_Pervasives_Native.None
end)))
in (FStar_All.pipe_right uu____2836 FStar_Option.isSome)))


let lookup_lid : env_t  ->  FStar_Ident.lid  ->  fvar_binding = (fun env a -> (

let uu____2858 = (try_lookup_lid env a)
in (match (uu____2858) with
| FStar_Pervasives_Native.None -> begin
(

let uu____2861 = (

let uu____2862 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" uu____2862))
in (failwith uu____2861))
end
| FStar_Pervasives_Native.Some (s) -> begin
s
end)))


let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  env_t = (fun env x arity fname ftok -> (

let fvb = (mk_fvb x fname arity ftok FStar_Pervasives_Native.None)
in (aux_check_push_fvar env fvb)))


let replace_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  env_t = (fun env x arity fname ftok -> (

let fvb = (mk_fvb x fname arity ftok FStar_Pervasives_Native.None)
in (

let env1 = (match (env.bindings) with
| (Binding_fvar (fvb1))::bs when (FStar_Ident.lid_equals fvb1.fvar_lid x) -> begin
(

let uu___113_2929 = env
in {bindings = bs; depth = uu___113_2929.depth; tcenv = uu___113_2929.tcenv; warn = uu___113_2929.warn; cache = uu___113_2929.cache; nolabels = uu___113_2929.nolabels; use_zfuel_name = uu___113_2929.use_zfuel_name; encode_non_total_function_typ = uu___113_2929.encode_non_total_function_typ; current_module_name = uu___113_2929.current_module_name})
end
| uu____2930 -> begin
(failwith "replace_free_var: unexpected binding at the head")
end)
in (aux_check_push_fvar env1 fvb))))


let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (

let fvb = (lookup_lid env x)
in (

let t3 = (

let uu____2950 = (

let uu____2957 = (

let uu____2960 = (FStar_SMTEncoding_Util.mkApp (("ZFuel"), ([])))
in (uu____2960)::[])
in ((f), (uu____2957)))
in (FStar_SMTEncoding_Util.mkApp uu____2950))
in (

let fvb1 = (mk_fvb x fvb.smt_id fvb.smt_arity fvb.smt_token (FStar_Pervasives_Native.Some (t3)))
in (aux_check_push_fvar env fvb1)))))


let try_lookup_free_var : env_t  ->  FStar_Ident.lident  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun env l -> (

let uu____2978 = (try_lookup_lid env l)
in (match (uu____2978) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (fvb) -> begin
(match (fvb.smt_fuel_partial_app) with
| FStar_Pervasives_Native.Some (f) when env.use_zfuel_name -> begin
FStar_Pervasives_Native.Some (f)
end
| uu____2987 -> begin
(match (fvb.smt_token) with
| FStar_Pervasives_Native.Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (uu____2995, (fuel)::[]) -> begin
(

let uu____2999 = (

let uu____3000 = (

let uu____3001 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right uu____3001 FStar_Pervasives_Native.fst))
in (FStar_Util.starts_with uu____3000 "fuel"))
in (match (uu____2999) with
| true -> begin
(

let uu____3004 = (

let uu____3005 = (FStar_SMTEncoding_Util.mkFreeV ((fvb.smt_id), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_ApplyTF uu____3005 fuel))
in (FStar_All.pipe_left (fun _0_17 -> FStar_Pervasives_Native.Some (_0_17)) uu____3004))
end
| uu____3008 -> begin
FStar_Pervasives_Native.Some (t)
end))
end
| uu____3009 -> begin
FStar_Pervasives_Native.Some (t)
end)
end
| uu____3010 -> begin
FStar_Pervasives_Native.None
end)
end)
end)))


let lookup_free_var : env_t  ->  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let uu____3027 = (try_lookup_free_var env a.FStar_Syntax_Syntax.v)
in (match (uu____3027) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let uu____3031 = (

let uu____3032 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" uu____3032))
in (failwith uu____3031))
end)))


let lookup_free_var_name : env_t  ->  FStar_Ident.lid FStar_Syntax_Syntax.withinfo_t  ->  (Prims.string * Prims.int) = (fun env a -> (

let fvb = (lookup_lid env a.FStar_Syntax_Syntax.v)
in ((fvb.smt_id), (fvb.smt_arity))))


let lookup_free_var_sym : env_t  ->  FStar_Ident.lid FStar_Syntax_Syntax.withinfo_t  ->  (FStar_SMTEncoding_Term.op * FStar_SMTEncoding_Term.term Prims.list * Prims.int) = (fun env a -> (

let fvb = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (fvb.smt_fuel_partial_app) with
| FStar_Pervasives_Native.Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.freevars = uu____3085; FStar_SMTEncoding_Term.rng = uu____3086}) when env.use_zfuel_name -> begin
((g), (zf), ((fvb.smt_arity + (Prims.parse_int "1"))))
end
| uu____3101 -> begin
(match (fvb.smt_token) with
| FStar_Pervasives_Native.None -> begin
((FStar_SMTEncoding_Term.Var (fvb.smt_id)), ([]), (fvb.smt_arity))
end
| FStar_Pervasives_Native.Some (sym) -> begin
(match (sym.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, (fuel)::[]) -> begin
((g), ((fuel)::[]), ((fvb.smt_arity + (Prims.parse_int "1"))))
end
| uu____3129 -> begin
((FStar_SMTEncoding_Term.Var (fvb.smt_id)), ([]), (fvb.smt_arity))
end)
end)
end)))


let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun uu___90_3146 -> (match (uu___90_3146) with
| Binding_fvar (fvb) when (Prims.op_Equality fvb.smt_id nm) -> begin
fvb.smt_token
end
| uu____3150 -> begin
FStar_Pervasives_Native.None
end))))


let mkForall_fuel' : 'Auu____3157 . 'Auu____3157  ->  (FStar_SMTEncoding_Term.pat Prims.list Prims.list * FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (fun n1 uu____3177 -> (match (uu____3177) with
| (pats, vars, body) -> begin
(

let fallback = (fun uu____3204 -> (FStar_SMTEncoding_Util.mkForall ((pats), (vars), (body))))
in (

let uu____3209 = (FStar_Options.unthrottle_inductives ())
in (match (uu____3209) with
| true -> begin
(fallback ())
end
| uu____3210 -> begin
(

let uu____3211 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____3211) with
| (fsym, fterm) -> begin
(

let add_fuel1 = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Util.mkApp (("HasTypeFuel"), ((fterm)::args)))
end
| uu____3244 -> begin
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

let uu____3265 = (add_fuel1 guards)
in (FStar_SMTEncoding_Util.mk_and_l uu____3265))
end
| uu____3268 -> begin
(

let uu____3269 = (add_fuel1 ((guard)::[]))
in (FStar_All.pipe_right uu____3269 FStar_List.hd))
end)
in (FStar_SMTEncoding_Util.mkImp ((guard1), (body'))))
end
| uu____3274 -> begin
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
| FStar_Syntax_Syntax.Tm_arrow (uu____3315) -> begin
true
end
| FStar_Syntax_Syntax.Tm_refine (uu____3328) -> begin
true
end
| FStar_Syntax_Syntax.Tm_bvar (uu____3335) -> begin
true
end
| FStar_Syntax_Syntax.Tm_uvar (uu____3336) -> begin
true
end
| FStar_Syntax_Syntax.Tm_abs (uu____3337) -> begin
true
end
| FStar_Syntax_Syntax.Tm_constant (uu____3354) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____3356 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____3356 FStar_Option.isNone))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____3374; FStar_Syntax_Syntax.vars = uu____3375}, uu____3376) -> begin
(

let uu____3397 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____3397 FStar_Option.isNone))
end
| uu____3414 -> begin
false
end)))


let head_redex : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let uu____3425 = (

let uu____3426 = (FStar_Syntax_Util.un_uinst t)
in uu____3426.FStar_Syntax_Syntax.n)
in (match (uu____3425) with
| FStar_Syntax_Syntax.Tm_abs (uu____3429, uu____3430, FStar_Pervasives_Native.Some (rc)) -> begin
(((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_Tot_lid) || (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_GTot_lid)) || (FStar_List.existsb (fun uu___91_3451 -> (match (uu___91_3451) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____3452 -> begin
false
end)) rc.FStar_Syntax_Syntax.residual_flags))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____3454 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____3454 FStar_Option.isSome))
end
| uu____3471 -> begin
false
end)))


let whnf : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____3482 = (head_normal env t)
in (match (uu____3482) with
| true -> begin
t
end
| uu____3483 -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
end)))


let norm : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t))


let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____3499 = (

let uu____3500 = (FStar_Syntax_Syntax.null_binder t)
in (uu____3500)::[])
in (

let uu____3513 = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Util.abs uu____3499 uu____3513 FStar_Pervasives_Native.None))))


let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((FStar_Pervasives_Native.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(

let uu____3557 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out uu____3557))
end
| s -> begin
(

let uu____3560 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Util.mk_ApplyTT out uu____3560))
end)) e)))


let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)))


let raise_arity_mismatch : 'Auu____3587 . Prims.string  ->  Prims.int  ->  Prims.int  ->  FStar_Range.range  ->  'Auu____3587 = (fun head1 arity n_args rng -> (

let uu____3608 = (

let uu____3613 = (

let uu____3614 = (FStar_Util.string_of_int arity)
in (

let uu____3615 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format3 "Head symbol %s expects at least %s arguments; got only %s" head1 uu____3614 uu____3615)))
in ((FStar_Errors.Fatal_SMTEncodingArityMismatch), (uu____3613)))
in (FStar_Errors.raise_error uu____3608 rng)))


let maybe_curry_app : FStar_Range.range  ->  FStar_SMTEncoding_Term.op  ->  Prims.int  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun rng head1 arity args -> (

let n_args = (FStar_List.length args)
in (match ((Prims.op_Equality n_args arity)) with
| true -> begin
(FStar_SMTEncoding_Util.mkApp' ((head1), (args)))
end
| uu____3647 -> begin
(match ((n_args > arity)) with
| true -> begin
(

let uu____3654 = (FStar_Util.first_N arity args)
in (match (uu____3654) with
| (args1, rest) -> begin
(

let head2 = (FStar_SMTEncoding_Util.mkApp' ((head1), (args1)))
in (mk_Apply_args head2 rest))
end))
end
| uu____3676 -> begin
(

let uu____3677 = (FStar_SMTEncoding_Term.op_to_string head1)
in (raise_arity_mismatch uu____3677 arity n_args rng))
end)
end)))


let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun uu___92_3686 -> (match (uu___92_3686) with
| FStar_SMTEncoding_Term.Var ("ApplyTT") -> begin
true
end
| FStar_SMTEncoding_Term.Var ("ApplyTF") -> begin
true
end
| uu____3687 -> begin
false
end))


let is_an_eta_expansion : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun env vars body -> (

let rec check_partial_applications = (fun t xs -> (match (((t.FStar_SMTEncoding_Term.tm), (xs))) with
| (FStar_SMTEncoding_Term.App (app, (f)::({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.freevars = uu____3733; FStar_SMTEncoding_Term.rng = uu____3734})::[]), (x)::xs1) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(check_partial_applications f xs1)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), uu____3757) -> begin
(

let uu____3766 = ((Prims.op_Equality (FStar_List.length args) (FStar_List.length xs)) && (FStar_List.forall2 (fun a v1 -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v1)
end
| uu____3777 -> begin
false
end)) args (FStar_List.rev xs)))
in (match (uu____3766) with
| true -> begin
(tok_of_name env f)
end
| uu____3780 -> begin
FStar_Pervasives_Native.None
end))
end
| (uu____3781, []) -> begin
(

let fvs = (FStar_SMTEncoding_Term.free_variables t)
in (

let uu____3785 = (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (

let uu____3789 = (FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)
in (not (uu____3789))))))
in (match (uu____3785) with
| true -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____3792 -> begin
FStar_Pervasives_Native.None
end)))
end
| uu____3793 -> begin
FStar_Pervasives_Native.None
end))
in (check_partial_applications body (FStar_List.rev vars))))


type label =
(FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range)


type labels =
label Prims.list

type pattern =
{pat_vars : (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.fv) Prims.list; pat_term : unit  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t); guard : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term; projections : FStar_SMTEncoding_Term.term  ->  (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) Prims.list}


let __proj__Mkpattern__item__pat_vars : pattern  ->  (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.fv) Prims.list = (fun projectee -> (match (projectee) with
| {pat_vars = __fname__pat_vars; pat_term = __fname__pat_term; guard = __fname__guard; projections = __fname__projections} -> begin
__fname__pat_vars
end))


let __proj__Mkpattern__item__pat_term : pattern  ->  unit  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun projectee -> (match (projectee) with
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
| uu____4053 -> begin
false
end))

exception Inner_let_rec


let uu___is_Inner_let_rec : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Inner_let_rec -> begin
true
end
| uu____4059 -> begin
false
end))


let as_function_typ : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (

let rec aux = (fun norm1 t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____4082) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_refine (uu____4095) -> begin
(

let uu____4102 = (FStar_Syntax_Util.unrefine t1)
in (aux true uu____4102))
end
| uu____4103 -> begin
(match (norm1) with
| true -> begin
(

let uu____4104 = (whnf env t1)
in (aux false uu____4104))
end
| uu____4105 -> begin
(

let uu____4106 = (

let uu____4107 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (

let uu____4108 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" uu____4107 uu____4108)))
in (failwith uu____4106))
end)
end)))
in (aux true t0)))


let rec curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.comp) = (fun k -> (

let k1 = (FStar_Syntax_Subst.compress k)
in (match (k1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| FStar_Syntax_Syntax.Tm_refine (bv, uu____4154) -> begin
(curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort)
end
| uu____4159 -> begin
(

let uu____4160 = (FStar_Syntax_Syntax.mk_Total k1)
in (([]), (uu____4160)))
end)))


let is_arithmetic_primitive : 'Auu____4177 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  'Auu____4177 Prims.list  ->  Prims.bool = (fun head1 args -> (match (((head1.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____4199)::(uu____4200)::[]) -> begin
(((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Addition) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Subtraction)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Multiply)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Division)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Modulus))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____4204)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus)
end
| uu____4207 -> begin
false
end))


let isInteger : FStar_Syntax_Syntax.term'  ->  Prims.bool = (fun tm -> (match (tm) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (n1, FStar_Pervasives_Native.None)) -> begin
true
end
| uu____4230 -> begin
false
end))


let getInteger : FStar_Syntax_Syntax.term'  ->  Prims.int = (fun tm -> (match (tm) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (n1, FStar_Pervasives_Native.None)) -> begin
(FStar_Util.int_of_string n1)
end
| uu____4247 -> begin
(failwith "Expected an Integer term")
end))


let is_BitVector_primitive : 'Auu____4254 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____4254) Prims.list  ->  Prims.bool = (fun head1 args -> (match (((head1.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((sz_arg, uu____4295))::(uu____4296)::(uu____4297)::[]) -> begin
((((((((((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_and_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_xor_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_or_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_add_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_sub_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_shift_left_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_shift_right_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_udiv_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_mod_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_uext_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_mul_lid)) && (isInteger sz_arg.FStar_Syntax_Syntax.n))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((sz_arg, uu____4348))::(uu____4349)::[]) -> begin
(((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_to_nat_lid)) && (isInteger sz_arg.FStar_Syntax_Syntax.n))
end
| uu____4386 -> begin
false
end))


let rec encode_const : FStar_Const.sconst  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list) = (fun c env -> (match (c) with
| FStar_Const.Const_unit -> begin
((FStar_SMTEncoding_Term.mk_Term_unit), ([]))
end
| FStar_Const.Const_bool (true) -> begin
(

let uu____4695 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue)
in ((uu____4695), ([])))
end
| FStar_Const.Const_bool (false) -> begin
(

let uu____4698 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse)
in ((uu____4698), ([])))
end
| FStar_Const.Const_char (c1) -> begin
(

let uu____4702 = (

let uu____4703 = (

let uu____4710 = (

let uu____4713 = (

let uu____4714 = (FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c1))
in (FStar_SMTEncoding_Term.boxInt uu____4714))
in (uu____4713)::[])
in (("FStar.Char.__char_of_int"), (uu____4710)))
in (FStar_SMTEncoding_Util.mkApp uu____4703))
in ((uu____4702), ([])))
end
| FStar_Const.Const_int (i, FStar_Pervasives_Native.None) -> begin
(

let uu____4730 = (

let uu____4731 = (FStar_SMTEncoding_Util.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt uu____4731))
in ((uu____4730), ([])))
end
| FStar_Const.Const_int (repr, FStar_Pervasives_Native.Some (sw)) -> begin
(

let syntax_term = (FStar_ToSyntax_ToSyntax.desugar_machine_integer env.tcenv.FStar_TypeChecker_Env.dsenv repr sw FStar_Range.dummyRange)
in (encode_term syntax_term env))
end
| FStar_Const.Const_string (s, uu____4752) -> begin
(

let uu____4753 = (varops.string_const s)
in ((uu____4753), ([])))
end
| FStar_Const.Const_range (uu____4756) -> begin
(

let uu____4757 = (FStar_SMTEncoding_Term.mk_Range_const ())
in ((uu____4757), ([])))
end
| FStar_Const.Const_effect -> begin
((FStar_SMTEncoding_Term.mk_Term_type), ([]))
end
| c1 -> begin
(

let uu____4763 = (

let uu____4764 = (FStar_Syntax_Print.const_to_string c1)
in (FStar_Util.format1 "Unhandled constant: %s" uu____4764))
in (failwith uu____4763))
end))
and encode_binders : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> ((

let uu____4793 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____4793) with
| true -> begin
(

let uu____4794 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" uu____4794))
end
| uu____4795 -> begin
()
end));
(

let uu____4796 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____4886 b -> (match (uu____4886) with
| (vars, guards, env1, decls, names1) -> begin
(

let uu____4965 = (

let x = (unmangle (FStar_Pervasives_Native.fst b))
in (

let uu____4981 = (gen_term_var env1 x)
in (match (uu____4981) with
| (xxsym, xx, env') -> begin
(

let uu____5005 = (

let uu____5010 = (norm env1 x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt uu____5010 env1 xx))
in (match (uu____5005) with
| (guard_x_t, decls') -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (guard_x_t), (env'), (decls'), (x))
end))
end)))
in (match (uu____4965) with
| (v1, g, env2, decls', n1) -> begin
(((v1)::vars), ((g)::guards), (env2), ((FStar_List.append decls decls')), ((n1)::names1))
end))
end)) (([]), ([]), (env), ([]), ([]))))
in (match (uu____4796) with
| (vars, guards, env1, decls, names1) -> begin
(((FStar_List.rev vars)), ((FStar_List.rev guards)), (env1), (decls), ((FStar_List.rev names1)))
end));
))
and encode_term_pred : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let uu____5159 = (encode_term t env)
in (match (uu____5159) with
| (t1, decls) -> begin
(

let uu____5170 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1)
in ((uu____5170), (decls)))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let uu____5181 = (encode_term t env)
in (match (uu____5181) with
| (t1, decls) -> begin
(match (fuel_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5196 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t1)
in ((uu____5196), (decls)))
end
| FStar_Pervasives_Native.Some (f) -> begin
(

let uu____5198 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1)
in ((uu____5198), (decls)))
end)
end)))
and encode_arith_term : env_t  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.args  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun env head1 args_e -> (

let uu____5204 = (encode_args args_e env)
in (match (uu____5204) with
| (arg_tms, decls) -> begin
(

let head_fv = (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____5223 -> begin
(failwith "Impossible")
end)
in (

let unary = (fun arg_tms1 -> (

let uu____5234 = (FStar_List.hd arg_tms1)
in (FStar_SMTEncoding_Term.unboxInt uu____5234)))
in (

let binary = (fun arg_tms1 -> (

let uu____5249 = (

let uu____5250 = (FStar_List.hd arg_tms1)
in (FStar_SMTEncoding_Term.unboxInt uu____5250))
in (

let uu____5251 = (

let uu____5252 = (

let uu____5253 = (FStar_List.tl arg_tms1)
in (FStar_List.hd uu____5253))
in (FStar_SMTEncoding_Term.unboxInt uu____5252))
in ((uu____5249), (uu____5251)))))
in (

let mk_default = (fun uu____5261 -> (

let uu____5262 = (lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name)
in (match (uu____5262) with
| (fname, fuel_args, arity) -> begin
(

let args = (FStar_List.append fuel_args arg_tms)
in (maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity args))
end)))
in (

let mk_l = (fun op mk_args ts -> (

let uu____5324 = (FStar_Options.smtencoding_l_arith_native ())
in (match (uu____5324) with
| true -> begin
(

let uu____5325 = (

let uu____5326 = (mk_args ts)
in (op uu____5326))
in (FStar_All.pipe_right uu____5325 FStar_SMTEncoding_Term.boxInt))
end
| uu____5327 -> begin
(mk_default ())
end)))
in (

let mk_nl = (fun nm op ts -> (

let uu____5361 = (FStar_Options.smtencoding_nl_arith_wrapped ())
in (match (uu____5361) with
| true -> begin
(

let uu____5362 = (binary ts)
in (match (uu____5362) with
| (t1, t2) -> begin
(

let uu____5369 = (FStar_SMTEncoding_Util.mkApp ((nm), ((t1)::(t2)::[])))
in (FStar_All.pipe_right uu____5369 FStar_SMTEncoding_Term.boxInt))
end))
end
| uu____5372 -> begin
(

let uu____5373 = (FStar_Options.smtencoding_nl_arith_native ())
in (match (uu____5373) with
| true -> begin
(

let uu____5374 = (

let uu____5375 = (binary ts)
in (op uu____5375))
in (FStar_All.pipe_right uu____5374 FStar_SMTEncoding_Term.boxInt))
end
| uu____5380 -> begin
(mk_default ())
end))
end)))
in (

let add1 = (mk_l FStar_SMTEncoding_Util.mkAdd binary)
in (

let sub1 = (mk_l FStar_SMTEncoding_Util.mkSub binary)
in (

let minus = (mk_l FStar_SMTEncoding_Util.mkMinus unary)
in (

let mul1 = (mk_nl "_mul" FStar_SMTEncoding_Util.mkMul)
in (

let div1 = (mk_nl "_div" FStar_SMTEncoding_Util.mkDiv)
in (

let modulus = (mk_nl "_mod" FStar_SMTEncoding_Util.mkMod)
in (

let ops = (((FStar_Parser_Const.op_Addition), (add1)))::(((FStar_Parser_Const.op_Subtraction), (sub1)))::(((FStar_Parser_Const.op_Multiply), (mul1)))::(((FStar_Parser_Const.op_Division), (div1)))::(((FStar_Parser_Const.op_Modulus), (modulus)))::(((FStar_Parser_Const.op_Minus), (minus)))::[]
in (

let uu____5536 = (

let uu____5546 = (FStar_List.tryFind (fun uu____5570 -> (match (uu____5570) with
| (l, uu____5580) -> begin
(FStar_Syntax_Syntax.fv_eq_lid head_fv l)
end)) ops)
in (FStar_All.pipe_right uu____5546 FStar_Util.must))
in (match (uu____5536) with
| (uu____5624, op) -> begin
(

let uu____5636 = (op arg_tms)
in ((uu____5636), (decls)))
end)))))))))))))))
end)))
and encode_BitVector_term : env_t  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list) = (fun env head1 args_e -> (

let uu____5650 = (FStar_List.hd args_e)
in (match (uu____5650) with
| (tm_sz, uu____5664) -> begin
(

let sz = (getInteger tm_sz.FStar_Syntax_Syntax.n)
in (

let sz_key = (FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz))
in (

let sz_decls = (

let uu____5672 = (FStar_Util.smap_try_find env.cache sz_key)
in (match (uu____5672) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
[]
end
| FStar_Pervasives_Native.None -> begin
(

let t_decls1 = (FStar_SMTEncoding_Term.mkBvConstructor sz)
in ((

let uu____5678 = (mk_cache_entry env "" [] [])
in (FStar_Util.smap_add env.cache sz_key uu____5678));
t_decls1;
))
end))
in (

let uu____5679 = (match (((head1.FStar_Syntax_Syntax.n), (args_e))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____5701)::((sz_arg, uu____5703))::(uu____5704)::[]) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_uext_lid) && (isInteger sz_arg.FStar_Syntax_Syntax.n)) -> begin
(

let uu____5753 = (

let uu____5762 = (FStar_List.tail args_e)
in (FStar_List.tail uu____5762))
in (

let uu____5783 = (

let uu____5786 = (getInteger sz_arg.FStar_Syntax_Syntax.n)
in FStar_Pervasives_Native.Some (uu____5786))
in ((uu____5753), (uu____5783))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____5798)::((sz_arg, uu____5800))::(uu____5801)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_uext_lid) -> begin
(

let uu____5850 = (

let uu____5851 = (FStar_Syntax_Print.term_to_string sz_arg)
in (FStar_Util.format1 "Not a constant bitvector extend size: %s" uu____5851))
in (failwith uu____5850))
end
| uu____5858 -> begin
(

let uu____5871 = (FStar_List.tail args_e)
in ((uu____5871), (FStar_Pervasives_Native.None)))
end)
in (match (uu____5679) with
| (arg_tms, ext_sz) -> begin
(

let uu____5908 = (encode_args arg_tms env)
in (match (uu____5908) with
| (arg_tms1, decls) -> begin
(

let head_fv = (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____5929 -> begin
(failwith "Impossible")
end)
in (

let unary = (fun arg_tms2 -> (

let uu____5940 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____5940)))
in (

let unary_arith = (fun arg_tms2 -> (

let uu____5951 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxInt uu____5951)))
in (

let binary = (fun arg_tms2 -> (

let uu____5966 = (

let uu____5967 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____5967))
in (

let uu____5968 = (

let uu____5969 = (

let uu____5970 = (FStar_List.tl arg_tms2)
in (FStar_List.hd uu____5970))
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____5969))
in ((uu____5966), (uu____5968)))))
in (

let binary_arith = (fun arg_tms2 -> (

let uu____5987 = (

let uu____5988 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____5988))
in (

let uu____5989 = (

let uu____5990 = (

let uu____5991 = (FStar_List.tl arg_tms2)
in (FStar_List.hd uu____5991))
in (FStar_SMTEncoding_Term.unboxInt uu____5990))
in ((uu____5987), (uu____5989)))))
in (

let mk_bv = (fun op mk_args resBox ts -> (

let uu____6049 = (

let uu____6050 = (mk_args ts)
in (op uu____6050))
in (FStar_All.pipe_right uu____6049 resBox)))
in (

let bv_and = (mk_bv FStar_SMTEncoding_Util.mkBvAnd binary (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_xor = (mk_bv FStar_SMTEncoding_Util.mkBvXor binary (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_or = (mk_bv FStar_SMTEncoding_Util.mkBvOr binary (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_add = (mk_bv FStar_SMTEncoding_Util.mkBvAdd binary (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_sub = (mk_bv FStar_SMTEncoding_Util.mkBvSub binary (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_shl = (mk_bv (FStar_SMTEncoding_Util.mkBvShl sz) binary_arith (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_shr = (mk_bv (FStar_SMTEncoding_Util.mkBvShr sz) binary_arith (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_udiv = (mk_bv (FStar_SMTEncoding_Util.mkBvUdiv sz) binary_arith (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_mod = (mk_bv (FStar_SMTEncoding_Util.mkBvMod sz) binary_arith (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_mul = (mk_bv (FStar_SMTEncoding_Util.mkBvMul sz) binary_arith (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_ult = (mk_bv FStar_SMTEncoding_Util.mkBvUlt binary FStar_SMTEncoding_Term.boxBool)
in (

let bv_uext = (fun arg_tms2 -> (

let uu____6182 = (

let uu____6187 = (match (ext_sz) with
| FStar_Pervasives_Native.Some (x) -> begin
x
end
| FStar_Pervasives_Native.None -> begin
(failwith "impossible")
end)
in (FStar_SMTEncoding_Util.mkBvUext uu____6187))
in (

let uu____6189 = (

let uu____6194 = (

let uu____6195 = (match (ext_sz) with
| FStar_Pervasives_Native.Some (x) -> begin
x
end
| FStar_Pervasives_Native.None -> begin
(failwith "impossible")
end)
in (sz + uu____6195))
in (FStar_SMTEncoding_Term.boxBitVec uu____6194))
in (mk_bv uu____6182 unary uu____6189 arg_tms2))))
in (

let to_int1 = (mk_bv FStar_SMTEncoding_Util.mkBvToNat unary FStar_SMTEncoding_Term.boxInt)
in (

let bv_to = (mk_bv (FStar_SMTEncoding_Util.mkNatToBv sz) unary_arith (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let ops = (((FStar_Parser_Const.bv_and_lid), (bv_and)))::(((FStar_Parser_Const.bv_xor_lid), (bv_xor)))::(((FStar_Parser_Const.bv_or_lid), (bv_or)))::(((FStar_Parser_Const.bv_add_lid), (bv_add)))::(((FStar_Parser_Const.bv_sub_lid), (bv_sub)))::(((FStar_Parser_Const.bv_shift_left_lid), (bv_shl)))::(((FStar_Parser_Const.bv_shift_right_lid), (bv_shr)))::(((FStar_Parser_Const.bv_udiv_lid), (bv_udiv)))::(((FStar_Parser_Const.bv_mod_lid), (bv_mod)))::(((FStar_Parser_Const.bv_mul_lid), (bv_mul)))::(((FStar_Parser_Const.bv_ult_lid), (bv_ult)))::(((FStar_Parser_Const.bv_uext_lid), (bv_uext)))::(((FStar_Parser_Const.bv_to_nat_lid), (to_int1)))::(((FStar_Parser_Const.nat_to_bv_lid), (bv_to)))::[]
in (

let uu____6428 = (

let uu____6438 = (FStar_List.tryFind (fun uu____6462 -> (match (uu____6462) with
| (l, uu____6472) -> begin
(FStar_Syntax_Syntax.fv_eq_lid head_fv l)
end)) ops)
in (FStar_All.pipe_right uu____6438 FStar_Util.must))
in (match (uu____6428) with
| (uu____6518, op) -> begin
(

let uu____6530 = (op arg_tms1)
in ((uu____6530), ((FStar_List.append sz_decls decls))))
end)))))))))))))))))))))))
end))
end)))))
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let t0 = (FStar_Syntax_Subst.compress t)
in ((

let uu____6541 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____6541) with
| true -> begin
(

let uu____6542 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____6543 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____6544 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" uu____6542 uu____6543 uu____6544))))
end
| uu____6545 -> begin
()
end));
(match (t0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____6550) -> begin
(

let uu____6575 = (

let uu____6576 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____6577 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____6578 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____6579 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6576 uu____6577 uu____6578 uu____6579)))))
in (failwith uu____6575))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____6584 = (

let uu____6585 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____6586 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____6587 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____6588 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6585 uu____6586 uu____6587 uu____6588)))))
in (failwith uu____6584))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____6594 = (FStar_Syntax_Util.unfold_lazy i)
in (encode_term uu____6594 env))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____6596 = (

let uu____6597 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" uu____6597))
in (failwith uu____6596))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, (k, uu____6604), uu____6605) -> begin
(

let uu____6654 = (match (k) with
| FStar_Util.Inl (t2) -> begin
(FStar_Syntax_Util.is_unit t2)
end
| uu____6662 -> begin
false
end)
in (match (uu____6654) with
| true -> begin
((FStar_SMTEncoding_Term.mk_Term_unit), ([]))
end
| uu____6675 -> begin
(encode_term t1 env)
end))
end
| FStar_Syntax_Syntax.Tm_quoted (qt, uu____6677) -> begin
(

let tv = (

let uu____6683 = (FStar_Reflection_Basic.inspect_ln qt)
in (FStar_Syntax_Embeddings.embed FStar_Reflection_Embeddings.e_term_view t.FStar_Syntax_Syntax.pos uu____6683))
in (

let t1 = (

let uu____6687 = (

let uu____6696 = (FStar_Syntax_Syntax.as_arg tv)
in (uu____6696)::[])
in (FStar_Syntax_Util.mk_app (FStar_Reflection_Data.refl_constant_term FStar_Reflection_Data.fstar_refl_pack_ln) uu____6687))
in (encode_term t1 env)))
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____6716) -> begin
(encode_term t1 env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t1 = (lookup_term_var env x)
in ((t1), ([])))
end
| FStar_Syntax_Syntax.Tm_fvar (v1) -> begin
(

let uu____6724 = (lookup_free_var env v1.FStar_Syntax_Syntax.fv_name)
in ((uu____6724), ([])))
end
| FStar_Syntax_Syntax.Tm_type (uu____6725) -> begin
((FStar_SMTEncoding_Term.mk_Term_type), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____6727) -> begin
(encode_term t1 env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(encode_const c env)
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let module_name = env.current_module_name
in (

let uu____6752 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____6752) with
| (binders1, res) -> begin
(

let uu____6763 = ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res))
in (match (uu____6763) with
| true -> begin
(

let uu____6768 = (encode_binders FStar_Pervasives_Native.None binders1 env)
in (match (uu____6768) with
| (vars, guards, env', decls, uu____6793) -> begin
(

let fsym = (

let uu____6811 = (varops.fresh "f")
in ((uu____6811), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV fsym)
in (

let app = (mk_Apply f vars)
in (

let uu____6814 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post (

let uu___114_6823 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___114_6823.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___114_6823.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___114_6823.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___114_6823.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___114_6823.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___114_6823.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___114_6823.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___114_6823.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___114_6823.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___114_6823.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___114_6823.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___114_6823.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___114_6823.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___114_6823.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___114_6823.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___114_6823.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___114_6823.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___114_6823.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___114_6823.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___114_6823.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___114_6823.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___114_6823.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___114_6823.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___114_6823.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___114_6823.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___114_6823.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___114_6823.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___114_6823.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___114_6823.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___114_6823.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___114_6823.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___114_6823.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___114_6823.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___114_6823.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___114_6823.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___114_6823.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___114_6823.FStar_TypeChecker_Env.dep_graph}) res)
in (match (uu____6814) with
| (pre_opt, res_t) -> begin
(

let uu____6834 = (encode_term_pred FStar_Pervasives_Native.None res_t env' app)
in (match (uu____6834) with
| (res_pred, decls') -> begin
(

let uu____6845 = (match (pre_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____6858 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____6858), ([])))
end
| FStar_Pervasives_Native.Some (pre) -> begin
(

let uu____6862 = (encode_formula pre env')
in (match (uu____6862) with
| (guard, decls0) -> begin
(

let uu____6875 = (FStar_SMTEncoding_Util.mk_and_l ((guard)::guards))
in ((uu____6875), (decls0)))
end))
end)
in (match (uu____6845) with
| (guards1, guard_decls) -> begin
(

let t_interp = (

let uu____6887 = (

let uu____6898 = (FStar_SMTEncoding_Util.mkImp ((guards1), (res_pred)))
in ((((app)::[])::[]), (vars), (uu____6898)))
in (FStar_SMTEncoding_Util.mkForall uu____6887))
in (

let cvars = (

let uu____6914 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right uu____6914 (FStar_List.filter (fun uu____6928 -> (match (uu____6928) with
| (x, uu____6934) -> begin
(Prims.op_disEquality x (FStar_Pervasives_Native.fst fsym))
end)))))
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), ((fsym)::cvars), (t_interp)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____6947 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____6947) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
(

let uu____6955 = (

let uu____6956 = (

let uu____6963 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((cache_entry.cache_symbol_name), (uu____6963)))
in (FStar_SMTEncoding_Util.mkApp uu____6956))
in ((uu____6955), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append guard_decls (use_cache_entry cache_entry)))))))
end
| FStar_Pervasives_Native.None -> begin
(

let tsym = (

let uu____6981 = (

let uu____6982 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_arrow_" uu____6982))
in (varops.mk_unique uu____6981))
in (

let cvar_sorts = (FStar_List.map FStar_Pervasives_Native.snd cvars)
in (

let caption = (

let uu____6993 = (FStar_Options.log_queries ())
in (match (uu____6993) with
| true -> begin
(

let uu____6996 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in FStar_Pervasives_Native.Some (uu____6996))
end
| uu____6997 -> begin
FStar_Pervasives_Native.None
end))
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (caption)))
in (

let t1 = (

let uu____7002 = (

let uu____7009 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((tsym), (uu____7009)))
in (FStar_SMTEncoding_Util.mkApp uu____7002))
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t1 FStar_SMTEncoding_Term.mk_Term_type)
in (

let k_assumption = (

let a_name = (Prims.strcat "kinding_" tsym)
in (

let uu____7021 = (

let uu____7028 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((uu____7028), (FStar_Pervasives_Native.Some (a_name)), (a_name)))
in (FStar_SMTEncoding_Util.mkAssume uu____7021)))
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t1)
in (

let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t1)
in (

let pre_typing = (

let a_name = (Prims.strcat "pre_typing_" tsym)
in (

let uu____7041 = (

let uu____7048 = (

let uu____7049 = (

let uu____7060 = (

let uu____7061 = (

let uu____7066 = (

let uu____7067 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____7067))
in ((f_has_t), (uu____7066)))
in (FStar_SMTEncoding_Util.mkImp uu____7061))
in ((((f_has_t)::[])::[]), ((fsym)::cvars), (uu____7060)))
in (mkForall_fuel uu____7049))
in ((uu____7048), (FStar_Pervasives_Native.Some ("pre-typing for functions")), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____7041)))
in (

let t_interp1 = (

let a_name = (Prims.strcat "interpretation_" tsym)
in (

let uu____7082 = (

let uu____7089 = (

let uu____7090 = (

let uu____7101 = (FStar_SMTEncoding_Util.mkIff ((f_has_t_z), (t_interp)))
in ((((f_has_t_z)::[])::[]), ((fsym)::cvars), (uu____7101)))
in (FStar_SMTEncoding_Util.mkForall uu____7090))
in ((uu____7089), (FStar_Pervasives_Native.Some (a_name)), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____7082)))
in (

let t_decls1 = (FStar_List.append ((tdecl)::decls) (FStar_List.append decls' (FStar_List.append guard_decls ((k_assumption)::(pre_typing)::(t_interp1)::[]))))
in ((

let uu____7118 = (mk_cache_entry env tsym cvar_sorts t_decls1)
in (FStar_Util.smap_add env.cache tkey_hash uu____7118));
((t1), (t_decls1));
)))))))))))))
end))))))
end))
end))
end)))))
end))
end
| uu____7119 -> begin
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

let uu____7129 = (

let uu____7136 = (FStar_SMTEncoding_Term.mk_HasType t1 FStar_SMTEncoding_Term.mk_Term_type)
in ((uu____7136), (FStar_Pervasives_Native.Some ("Typing for non-total arrows")), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____7129)))
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

let uu____7146 = (

let uu____7153 = (

let uu____7154 = (

let uu____7165 = (

let uu____7166 = (

let uu____7171 = (

let uu____7172 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____7172))
in ((f_has_t), (uu____7171)))
in (FStar_SMTEncoding_Util.mkImp uu____7166))
in ((((f_has_t)::[])::[]), ((fsym)::[]), (uu____7165)))
in (mkForall_fuel uu____7154))
in ((uu____7153), (FStar_Pervasives_Native.Some (a_name)), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____7146)))
in ((t1), ((tdecl)::(t_kinding)::(t_interp)::[]))))))))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (uu____7189) -> begin
(

let uu____7196 = (

let uu____7201 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)
in (match (uu____7201) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.pos = uu____7208; FStar_Syntax_Syntax.vars = uu____7209} -> begin
(

let uu____7216 = (FStar_Syntax_Subst.open_term ((((x), (FStar_Pervasives_Native.None)))::[]) f)
in (match (uu____7216) with
| (b, f1) -> begin
(

let uu____7237 = (

let uu____7238 = (FStar_List.hd b)
in (FStar_Pervasives_Native.fst uu____7238))
in ((uu____7237), (f1)))
end))
end
| uu____7247 -> begin
(failwith "impossible")
end))
in (match (uu____7196) with
| (x, f) -> begin
(

let uu____7258 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (uu____7258) with
| (base_t, decls) -> begin
(

let uu____7269 = (gen_term_var env x)
in (match (uu____7269) with
| (x1, xtm, env') -> begin
(

let uu____7283 = (encode_formula f env')
in (match (uu____7283) with
| (refinement, decls') -> begin
(

let uu____7294 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____7294) with
| (fsym, fterm) -> begin
(

let tm_has_type_with_fuel = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (FStar_Pervasives_Native.Some (fterm)) xtm base_t)
in (

let encoding = (FStar_SMTEncoding_Util.mkAnd ((tm_has_type_with_fuel), (refinement)))
in (

let cvars = (

let uu____7314 = (

let uu____7321 = (FStar_SMTEncoding_Term.free_variables refinement)
in (

let uu____7328 = (FStar_SMTEncoding_Term.free_variables tm_has_type_with_fuel)
in (FStar_List.append uu____7321 uu____7328)))
in (FStar_Util.remove_dups FStar_SMTEncoding_Term.fv_eq uu____7314))
in (

let cvars1 = (FStar_All.pipe_right cvars (FStar_List.filter (fun uu____7369 -> (match (uu____7369) with
| (y, uu____7375) -> begin
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

let uu____7402 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____7402) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
(

let uu____7410 = (

let uu____7411 = (

let uu____7418 = (FStar_All.pipe_right cvars1 (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((cache_entry.cache_symbol_name), (uu____7418)))
in (FStar_SMTEncoding_Util.mkApp uu____7411))
in ((uu____7410), ((FStar_List.append decls (FStar_List.append decls' (use_cache_entry cache_entry))))))
end
| FStar_Pervasives_Native.None -> begin
(

let module_name = env.current_module_name
in (

let tsym = (

let uu____7437 = (

let uu____7438 = (

let uu____7439 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "_Tm_refine_" uu____7439))
in (Prims.strcat module_name uu____7438))
in (varops.mk_unique uu____7437))
in (

let cvar_sorts = (FStar_List.map FStar_Pervasives_Native.snd cvars1)
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let t1 = (

let uu____7451 = (

let uu____7458 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars1)
in ((tsym), (uu____7458)))
in (FStar_SMTEncoding_Util.mkApp uu____7451))
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

let uu____7473 = (

let uu____7480 = (

let uu____7481 = (

let uu____7492 = (FStar_SMTEncoding_Util.mkIff ((t_haseq_ref), (t_haseq_base)))
in ((((t_haseq_ref)::[])::[]), (cvars1), (uu____7492)))
in (FStar_SMTEncoding_Util.mkForall uu____7481))
in ((uu____7480), (FStar_Pervasives_Native.Some ((Prims.strcat "haseq for " tsym))), ((Prims.strcat "haseq" tsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____7473))
in (

let t_kinding = (

let uu____7502 = (

let uu____7509 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars1), (t_has_kind)))
in ((uu____7509), (FStar_Pervasives_Native.Some ("refinement kinding")), ((Prims.strcat "refinement_kinding_" tsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____7502))
in (

let t_interp = (

let uu____7519 = (

let uu____7526 = (

let uu____7527 = (

let uu____7538 = (FStar_SMTEncoding_Util.mkIff ((x_has_t), (encoding)))
in ((((x_has_t)::[])::[]), ((ffv)::(xfv)::cvars1), (uu____7538)))
in (FStar_SMTEncoding_Util.mkForall uu____7527))
in (

let uu____7555 = (

let uu____7556 = (FStar_Syntax_Print.term_to_string t0)
in FStar_Pervasives_Native.Some (uu____7556))
in ((uu____7526), (uu____7555), ((Prims.strcat "refinement_interpretation_" tsym)))))
in (FStar_SMTEncoding_Util.mkAssume uu____7519))
in (

let t_decls1 = (FStar_List.append decls (FStar_List.append decls' ((tdecl)::(t_kinding)::(t_interp)::(t_haseq1)::[])))
in ((

let uu____7561 = (mk_cache_entry env tsym cvar_sorts t_decls1)
in (FStar_Util.smap_add env.cache tkey_hash uu____7561));
((t1), (t_decls1));
)))))))))))))))
end))))))))))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_uvar (uv) -> begin
(

let ttm = (

let uu____7564 = (FStar_Syntax_Unionfind.uvar_id uv.FStar_Syntax_Syntax.ctx_uvar_head)
in (FStar_SMTEncoding_Util.mk_Term_uvar uu____7564))
in (

let uu____7565 = (encode_term_pred FStar_Pervasives_Native.None uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm)
in (match (uu____7565) with
| (t_has_k, decls) -> begin
(

let d = (

let uu____7577 = (

let uu____7584 = (

let uu____7585 = (

let uu____7586 = (

let uu____7587 = (FStar_Syntax_Unionfind.uvar_id uv.FStar_Syntax_Syntax.ctx_uvar_head)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____7587))
in (FStar_Util.format1 "uvar_typing_%s" uu____7586))
in (varops.mk_unique uu____7585))
in ((t_has_k), (FStar_Pervasives_Native.Some ("Uvar typing")), (uu____7584)))
in (FStar_SMTEncoding_Util.mkAssume uu____7577))
in ((ttm), ((FStar_List.append decls ((d)::[])))))
end)))
end
| FStar_Syntax_Syntax.Tm_app (uu____7588) -> begin
(

let uu____7603 = (FStar_Syntax_Util.head_and_args t0)
in (match (uu____7603) with
| (head1, args_e) -> begin
(

let uu____7644 = (

let uu____7655 = (

let uu____7656 = (FStar_Syntax_Subst.compress head1)
in uu____7656.FStar_Syntax_Syntax.n)
in ((uu____7655), (args_e)))
in (match (uu____7644) with
| uu____7669 when (head_redex env head1) -> begin
(

let uu____7680 = (whnf env t)
in (encode_term uu____7680 env))
end
| uu____7681 when (is_arithmetic_primitive head1 args_e) -> begin
(encode_arith_term env head1 args_e)
end
| uu____7698 when (is_BitVector_primitive head1 args_e) -> begin
(encode_BitVector_term env head1 args_e)
end
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____7710; FStar_Syntax_Syntax.vars = uu____7711}, uu____7712), (uu____7713)::((v1, uu____7715))::((v2, uu____7717))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.lexcons_lid) -> begin
(

let uu____7748 = (encode_term v1 env)
in (match (uu____7748) with
| (v11, decls1) -> begin
(

let uu____7759 = (encode_term v2 env)
in (match (uu____7759) with
| (v21, decls2) -> begin
(

let uu____7770 = (FStar_SMTEncoding_Util.mk_LexCons v11 v21)
in ((uu____7770), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____7772)::((v1, uu____7774))::((v2, uu____7776))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.lexcons_lid) -> begin
(

let uu____7803 = (encode_term v1 env)
in (match (uu____7803) with
| (v11, decls1) -> begin
(

let uu____7814 = (encode_term v2 env)
in (match (uu____7814) with
| (v21, decls2) -> begin
(

let uu____7825 = (FStar_SMTEncoding_Util.mk_LexCons v11 v21)
in ((uu____7825), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of), ((arg, uu____7827))::[]) -> begin
(encode_const (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos)) env)
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of), ((arg, uu____7843))::((rng, uu____7845))::[]) -> begin
(encode_term arg env)
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), uu____7864) -> begin
(

let e0 = (

let uu____7878 = (FStar_List.hd args_e)
in (FStar_TypeChecker_Util.reify_body_with_arg env.tcenv head1 uu____7878))
in ((

let uu____7886 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____7886) with
| true -> begin
(

let uu____7887 = (FStar_Syntax_Print.term_to_string e0)
in (FStar_Util.print1 "Result of normalization %s\n" uu____7887))
end
| uu____7888 -> begin
()
end));
(

let e = (

let uu____7892 = (

let uu____7897 = (FStar_TypeChecker_Util.remove_reify e0)
in (

let uu____7898 = (FStar_List.tl args_e)
in (FStar_Syntax_Syntax.mk_Tm_app uu____7897 uu____7898)))
in (uu____7892 FStar_Pervasives_Native.None t0.FStar_Syntax_Syntax.pos))
in (encode_term e env));
))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____7907)), ((arg, uu____7909))::[]) -> begin
(encode_term arg env)
end
| uu____7924 -> begin
(

let uu____7935 = (encode_args args_e env)
in (match (uu____7935) with
| (args, decls) -> begin
(

let encode_partial_app = (fun ht_opt -> (

let uu____7992 = (encode_term head1 env)
in (match (uu____7992) with
| (head2, decls') -> begin
(

let app_tm = (mk_Apply_args head2 args)
in (match (ht_opt) with
| FStar_Pervasives_Native.None -> begin
((app_tm), ((FStar_List.append decls decls')))
end
| FStar_Pervasives_Native.Some (formals, c) -> begin
(

let uu____8056 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (uu____8056) with
| (formals1, rest) -> begin
(

let subst1 = (FStar_List.map2 (fun uu____8134 uu____8135 -> (match (((uu____8134), (uu____8135))) with
| ((bv, uu____8157), (a, uu____8159)) -> begin
FStar_Syntax_Syntax.NT (((bv), (a)))
end)) formals1 args_e)
in (

let ty = (

let uu____8177 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right uu____8177 (FStar_Syntax_Subst.subst subst1)))
in (

let uu____8182 = (encode_term_pred FStar_Pervasives_Native.None ty env app_tm)
in (match (uu____8182) with
| (has_type, decls'') -> begin
(

let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (

let e_typing = (

let uu____8197 = (

let uu____8204 = (FStar_SMTEncoding_Util.mkForall ((((has_type)::[])::[]), (cvars), (has_type)))
in (

let uu____8213 = (

let uu____8214 = (

let uu____8215 = (

let uu____8216 = (FStar_SMTEncoding_Term.hash_of_term app_tm)
in (FStar_Util.digest_of_string uu____8216))
in (Prims.strcat "partial_app_typing_" uu____8215))
in (varops.mk_unique uu____8214))
in ((uu____8204), (FStar_Pervasives_Native.Some ("Partial app typing")), (uu____8213))))
in (FStar_SMTEncoding_Util.mkAssume uu____8197))
in ((app_tm), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' ((e_typing)::[]))))))))
end))))
end))
end))
end)))
in (

let encode_full_app = (fun fv -> (

let uu____8233 = (lookup_free_var_sym env fv)
in (match (uu____8233) with
| (fname, fuel_args, arity) -> begin
(

let tm = (maybe_curry_app t0.FStar_Syntax_Syntax.pos fname arity (FStar_List.append fuel_args args))
in ((tm), (decls)))
end)))
in (

let head2 = (FStar_Syntax_Subst.compress head1)
in (

let head_type = (match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (x); FStar_Syntax_Syntax.pos = uu____8265; FStar_Syntax_Syntax.vars = uu____8266}, uu____8267) -> begin
FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____8278; FStar_Syntax_Syntax.vars = uu____8279}, uu____8280) -> begin
(

let uu____8285 = (

let uu____8288 = (

let uu____8293 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____8293 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____8288 FStar_Pervasives_Native.snd))
in FStar_Pervasives_Native.Some (uu____8285))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____8325 = (

let uu____8328 = (

let uu____8333 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____8333 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____8328 FStar_Pervasives_Native.snd))
in FStar_Pervasives_Native.Some (uu____8325))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____8364, (FStar_Util.Inl (t1), uu____8366), uu____8367) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____8416, (FStar_Util.Inr (c), uu____8418), uu____8419) -> begin
FStar_Pervasives_Native.Some ((FStar_Syntax_Util.comp_result c))
end
| uu____8468 -> begin
FStar_Pervasives_Native.None
end)
in (match (head_type) with
| FStar_Pervasives_Native.None -> begin
(encode_partial_app FStar_Pervasives_Native.None)
end
| FStar_Pervasives_Native.Some (head_type1) -> begin
(

let head_type2 = (

let uu____8495 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type1)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine uu____8495))
in (

let uu____8496 = (curried_arrow_formals_comp head_type2)
in (match (uu____8496) with
| (formals, c) -> begin
(match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____8530; FStar_Syntax_Syntax.vars = uu____8531}, uu____8532) when (Prims.op_Equality (FStar_List.length formals) (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (Prims.op_Equality (FStar_List.length formals) (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| uu____8546 -> begin
(match (((FStar_List.length formals) > (FStar_List.length args))) with
| true -> begin
(encode_partial_app (FStar_Pervasives_Native.Some (((formals), (c)))))
end
| uu____8575 -> begin
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

let uu____8611 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____8611) with
| (bs1, body1, opening) -> begin
(

let fallback = (fun uu____8636 -> (

let f = (varops.fresh "Tm_abs")
in (

let decl = FStar_SMTEncoding_Term.DeclFun (((f), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Imprecise function encoding"))))
in (

let uu____8641 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in ((uu____8641), ((decl)::[]))))))
in (

let is_impure = (fun rc -> (

let uu____8650 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv rc.FStar_Syntax_Syntax.residual_effect)
in (FStar_All.pipe_right uu____8650 Prims.op_Negation)))
in (

let codomain_eff = (fun rc -> (

let res_typ = (match (rc.FStar_Syntax_Syntax.residual_typ) with
| FStar_Pervasives_Native.None -> begin
(

let uu____8662 = (

let uu____8675 = (FStar_TypeChecker_Env.get_range env.tcenv)
in (FStar_TypeChecker_Util.new_implicit_var "SMTEncoding codomain" uu____8675 env.tcenv FStar_Syntax_Util.ktype0))
in (match (uu____8662) with
| (t1, uu____8677, uu____8678) -> begin
t1
end))
end
| FStar_Pervasives_Native.Some (t1) -> begin
t1
end)
in (

let uu____8696 = (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_Tot_lid)
in (match (uu____8696) with
| true -> begin
(

let uu____8699 = (FStar_Syntax_Syntax.mk_Total res_typ)
in FStar_Pervasives_Native.Some (uu____8699))
end
| uu____8700 -> begin
(

let uu____8701 = (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_GTot_lid)
in (match (uu____8701) with
| true -> begin
(

let uu____8704 = (FStar_Syntax_Syntax.mk_GTotal res_typ)
in FStar_Pervasives_Native.Some (uu____8704))
end
| uu____8705 -> begin
FStar_Pervasives_Native.None
end))
end))))
in (match (lopt) with
| FStar_Pervasives_Native.None -> begin
((

let uu____8711 = (

let uu____8716 = (

let uu____8717 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)" uu____8717))
in ((FStar_Errors.Warning_FunctionLiteralPrecisionLoss), (uu____8716)))
in (FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____8711));
(fallback ());
)
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____8719 = ((is_impure rc) && (

let uu____8721 = (FStar_TypeChecker_Env.is_reifiable env.tcenv rc)
in (not (uu____8721))))
in (match (uu____8719) with
| true -> begin
(fallback ())
end
| uu____8726 -> begin
(

let cache_size = (FStar_Util.smap_size env.cache)
in (

let uu____8728 = (encode_binders FStar_Pervasives_Native.None bs1 env)
in (match (uu____8728) with
| (vars, guards, envbody, decls, uu____8753) -> begin
(

let body2 = (

let uu____8767 = (FStar_TypeChecker_Env.is_reifiable env.tcenv rc)
in (match (uu____8767) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env.tcenv body1)
end
| uu____8768 -> begin
body1
end))
in (

let uu____8769 = (encode_term body2 envbody)
in (match (uu____8769) with
| (body3, decls') -> begin
(

let uu____8780 = (

let uu____8789 = (codomain_eff rc)
in (match (uu____8789) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), ([]))
end
| FStar_Pervasives_Native.Some (c) -> begin
(

let tfun = (FStar_Syntax_Util.arrow bs1 c)
in (

let uu____8808 = (encode_term tfun env)
in (match (uu____8808) with
| (t1, decls1) -> begin
((FStar_Pervasives_Native.Some (t1)), (decls1))
end)))
end))
in (match (uu____8780) with
| (arrow_t_opt, decls'') -> begin
(

let key_body = (

let uu____8840 = (

let uu____8851 = (

let uu____8852 = (

let uu____8857 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____8857), (body3)))
in (FStar_SMTEncoding_Util.mkImp uu____8852))
in (([]), (vars), (uu____8851)))
in (FStar_SMTEncoding_Util.mkForall uu____8840))
in (

let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (

let cvars1 = (match (arrow_t_opt) with
| FStar_Pervasives_Native.None -> begin
cvars
end
| FStar_Pervasives_Native.Some (t1) -> begin
(

let uu____8867 = (

let uu____8874 = (FStar_SMTEncoding_Term.free_variables t1)
in (FStar_List.append uu____8874 cvars))
in (FStar_Util.remove_dups FStar_SMTEncoding_Term.fv_eq uu____8867))
end)
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), (cvars1), (key_body)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____8897 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____8897) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
(

let uu____8905 = (

let uu____8906 = (

let uu____8913 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars1)
in ((cache_entry.cache_symbol_name), (uu____8913)))
in (FStar_SMTEncoding_Util.mkApp uu____8906))
in ((uu____8905), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' (use_cache_entry cache_entry)))))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____8922 = (is_an_eta_expansion env vars body3)
in (match (uu____8922) with
| FStar_Pervasives_Native.Some (t1) -> begin
(

let decls1 = (

let uu____8933 = (

let uu____8934 = (FStar_Util.smap_size env.cache)
in (Prims.op_Equality uu____8934 cache_size))
in (match (uu____8933) with
| true -> begin
[]
end
| uu____8937 -> begin
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

let uu____8948 = (

let uu____8949 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_abs_" uu____8949))
in (varops.mk_unique uu____8948))
in (Prims.strcat module_name (Prims.strcat "_" fsym))))
in (

let fdecl = FStar_SMTEncoding_Term.DeclFun (((fsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let f = (

let uu____8954 = (

let uu____8961 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars1)
in ((fsym), (uu____8961)))
in (FStar_SMTEncoding_Util.mkApp uu____8954))
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

let uu____8979 = (

let uu____8980 = (

let uu____8987 = (FStar_SMTEncoding_Util.mkForall ((((f)::[])::[]), (cvars1), (f_has_t)))
in ((uu____8987), (FStar_Pervasives_Native.Some (a_name)), (a_name)))
in (FStar_SMTEncoding_Util.mkAssume uu____8980))
in (uu____8979)::[])))
end)
in (

let interp_f = (

let a_name = (Prims.strcat "interpretation_" fsym)
in (

let uu____8998 = (

let uu____9005 = (

let uu____9006 = (

let uu____9017 = (FStar_SMTEncoding_Util.mkEq ((app), (body3)))
in ((((app)::[])::[]), ((FStar_List.append vars cvars1)), (uu____9017)))
in (FStar_SMTEncoding_Util.mkForall uu____9006))
in ((uu____9005), (FStar_Pervasives_Native.Some (a_name)), (a_name)))
in (FStar_SMTEncoding_Util.mkAssume uu____8998)))
in (

let f_decls = (FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' (FStar_List.append ((fdecl)::typing_f) ((interp_f)::[])))))
in ((

let uu____9030 = (mk_cache_entry env fsym cvar_sorts f_decls)
in (FStar_Util.smap_add env.cache tkey_hash uu____9030));
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
| FStar_Syntax_Syntax.Tm_let ((uu____9031, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____9032); FStar_Syntax_Syntax.lbunivs = uu____9033; FStar_Syntax_Syntax.lbtyp = uu____9034; FStar_Syntax_Syntax.lbeff = uu____9035; FStar_Syntax_Syntax.lbdef = uu____9036; FStar_Syntax_Syntax.lbattrs = uu____9037; FStar_Syntax_Syntax.lbpos = uu____9038})::uu____9039), uu____9040) -> begin
(failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____9070; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____9072; FStar_Syntax_Syntax.lbdef = e1; FStar_Syntax_Syntax.lbattrs = uu____9074; FStar_Syntax_Syntax.lbpos = uu____9075})::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (uu____9099) -> begin
((FStar_Errors.diag t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions, and their enclosings let bindings (including the top-level let) are not yet fully encoded to the SMT solver; you may not be able to prove some facts");
(FStar_Exn.raise Inner_let_rec);
)
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end);
)))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (

let uu____9169 = (

let uu____9174 = (FStar_Syntax_Util.ascribe e1 ((FStar_Util.Inl (t1)), (FStar_Pervasives_Native.None)))
in (encode_term uu____9174 env))
in (match (uu____9169) with
| (ee1, decls1) -> begin
(

let uu____9199 = (FStar_Syntax_Subst.open_term ((((x), (FStar_Pervasives_Native.None)))::[]) e2)
in (match (uu____9199) with
| (xs, e21) -> begin
(

let uu____9220 = (FStar_List.hd xs)
in (match (uu____9220) with
| (x1, uu____9234) -> begin
(

let env' = (push_term_var env x1 ee1)
in (

let uu____9236 = (encode_body e21 env')
in (match (uu____9236) with
| (ee2, decls2) -> begin
((ee2), ((FStar_List.append decls1 decls2)))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (

let uu____9266 = (

let uu____9273 = (

let uu____9274 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.null_bv uu____9274))
in (gen_term_var env uu____9273))
in (match (uu____9266) with
| (scrsym, scr', env1) -> begin
(

let uu____9282 = (encode_term e env1)
in (match (uu____9282) with
| (scr, decls) -> begin
(

let uu____9293 = (

let encode_branch = (fun b uu____9322 -> (match (uu____9322) with
| (else_case, decls1) -> begin
(

let uu____9341 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____9341) with
| (p, w, br) -> begin
(

let uu____9367 = (encode_pat env1 p)
in (match (uu____9367) with
| (env0, pattern) -> begin
(

let guard = (pattern.guard scr')
in (

let projections = (pattern.projections scr')
in (

let env2 = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env2 uu____9404 -> (match (uu____9404) with
| (x, t) -> begin
(push_term_var env2 x t)
end)) env1))
in (

let uu____9411 = (match (w) with
| FStar_Pervasives_Native.None -> begin
((guard), ([]))
end
| FStar_Pervasives_Native.Some (w1) -> begin
(

let uu____9433 = (encode_term w1 env2)
in (match (uu____9433) with
| (w2, decls2) -> begin
(

let uu____9446 = (

let uu____9447 = (

let uu____9452 = (

let uu____9453 = (

let uu____9458 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue)
in ((w2), (uu____9458)))
in (FStar_SMTEncoding_Util.mkEq uu____9453))
in ((guard), (uu____9452)))
in (FStar_SMTEncoding_Util.mkAnd uu____9447))
in ((uu____9446), (decls2)))
end))
end)
in (match (uu____9411) with
| (guard1, decls2) -> begin
(

let uu____9471 = (encode_br br env2)
in (match (uu____9471) with
| (br1, decls3) -> begin
(

let uu____9484 = (FStar_SMTEncoding_Util.mkITE ((guard1), (br1), (else_case)))
in ((uu____9484), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end)))))
end))
end))
end))
in (FStar_List.fold_right encode_branch pats ((default_case), (decls))))
in (match (uu____9293) with
| (match_tm, decls1) -> begin
(

let uu____9503 = (FStar_SMTEncoding_Term.mkLet' (((((((scrsym), (FStar_SMTEncoding_Term.Term_sort))), (scr)))::[]), (match_tm)) FStar_Range.dummyRange)
in ((uu____9503), (decls1)))
end))
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> ((

let uu____9537 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____9537) with
| true -> begin
(

let uu____9538 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" uu____9538))
end
| uu____9539 -> begin
()
end));
(

let uu____9540 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (uu____9540) with
| (vars, pat_term) -> begin
(

let uu____9557 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun uu____9610 v1 -> (match (uu____9610) with
| (env1, vars1) -> begin
(

let uu____9662 = (gen_term_var env1 v1)
in (match (uu____9662) with
| (xx, uu____9684, env2) -> begin
((env2), ((((v1), (((xx), (FStar_SMTEncoding_Term.Term_sort)))))::vars1))
end))
end)) ((env), ([]))))
in (match (uu____9557) with
| (env1, vars1) -> begin
(

let rec mk_guard = (fun pat1 scrutinee -> (match (pat1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_var (uu____9767) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_wild (uu____9768) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____9769) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____9777 = (encode_const c env1)
in (match (uu____9777) with
| (tm, decls) -> begin
((match (decls) with
| (uu____9791)::uu____9792 -> begin
(failwith "Unexpected encoding of constant pattern")
end
| uu____9795 -> begin
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

let uu____9818 = (FStar_TypeChecker_Env.datacons_of_typ env1.tcenv tc_name)
in (match (uu____9818) with
| (uu____9825, (uu____9826)::[]) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| uu____9829 -> begin
(mk_data_tester env1 f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
end)))
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____9862 -> (match (uu____9862) with
| (arg, uu____9870) -> begin
(

let proj = (primitive_projector_by_pos env1.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____9876 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_guard arg uu____9876)))
end))))
in (FStar_SMTEncoding_Util.mk_and_l ((is_f)::sub_term_guards))))
end))
in (

let rec mk_projections = (fun pat1 scrutinee -> (match (pat1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (x, uu____9907) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_constant (uu____9938) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let uu____9961 = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____10005 -> (match (uu____10005) with
| (arg, uu____10019) -> begin
(

let proj = (primitive_projector_by_pos env1.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____10025 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_projections arg uu____10025)))
end))))
in (FStar_All.pipe_right uu____9961 FStar_List.flatten))
end))
in (

let pat_term1 = (fun uu____10055 -> (encode_term pat_term env1))
in (

let pattern = {pat_vars = vars1; pat_term = pat_term1; guard = (mk_guard pat); projections = (mk_projections pat)}
in ((env1), (pattern))))))
end))
end));
))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (

let uu____10065 = (FStar_All.pipe_right l (FStar_List.fold_left (fun uu____10109 uu____10110 -> (match (((uu____10109), (uu____10110))) with
| ((tms, decls), (t, uu____10146)) -> begin
(

let uu____10167 = (encode_term t env)
in (match (uu____10167) with
| (t1, decls') -> begin
(((t1)::tms), ((FStar_List.append decls decls')))
end))
end)) (([]), ([]))))
in (match (uu____10065) with
| (l1, decls) -> begin
(((FStar_List.rev l1)), (decls))
end)))
and encode_function_type_as_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let list_elements1 = (fun e -> (

let uu____10224 = (FStar_Syntax_Util.list_elements e)
in (match (uu____10224) with
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

let uu____10247 = (

let uu____10262 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right uu____10262 FStar_Syntax_Util.head_and_args))
in (match (uu____10247) with
| (head1, args) -> begin
(

let uu____10301 = (

let uu____10314 = (

let uu____10315 = (FStar_Syntax_Util.un_uinst head1)
in uu____10315.FStar_Syntax_Syntax.n)
in ((uu____10314), (args)))
in (match (uu____10301) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((uu____10329, uu____10330))::((e, uu____10332))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpat_lid) -> begin
e
end
| uu____10367 -> begin
(failwith "Unexpected pattern term")
end))
end)))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements1 p)
in (

let smt_pat_or = (fun t1 -> (

let uu____10407 = (

let uu____10422 = (FStar_Syntax_Util.unmeta t1)
in (FStar_All.pipe_right uu____10422 FStar_Syntax_Util.head_and_args))
in (match (uu____10407) with
| (head1, args) -> begin
(

let uu____10463 = (

let uu____10476 = (

let uu____10477 = (FStar_Syntax_Util.un_uinst head1)
in uu____10477.FStar_Syntax_Syntax.n)
in ((uu____10476), (args)))
in (match (uu____10463) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, uu____10494))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpatOr_lid) -> begin
FStar_Pervasives_Native.Some (e)
end
| uu____10521 -> begin
FStar_Pervasives_Native.None
end))
end)))
in (match (elts) with
| (t1)::[] -> begin
(

let uu____10543 = (smt_pat_or t1)
in (match (uu____10543) with
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____10559 = (list_elements1 e)
in (FStar_All.pipe_right uu____10559 (FStar_List.map (fun branch1 -> (

let uu____10577 = (list_elements1 branch1)
in (FStar_All.pipe_right uu____10577 (FStar_List.map one_pat)))))))
end
| uu____10588 -> begin
(

let uu____10593 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____10593)::[])
end))
end
| uu____10614 -> begin
(

let uu____10617 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____10617)::[])
end))))
in (

let uu____10638 = (

let uu____10657 = (

let uu____10658 = (FStar_Syntax_Subst.compress t)
in uu____10658.FStar_Syntax_Syntax.n)
in (match (uu____10657) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____10697 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____10697) with
| (binders1, c1) -> begin
(match (c1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____10740; FStar_Syntax_Syntax.effect_name = uu____10741; FStar_Syntax_Syntax.result_typ = uu____10742; FStar_Syntax_Syntax.effect_args = ((pre, uu____10744))::((post, uu____10746))::((pats, uu____10748))::[]; FStar_Syntax_Syntax.flags = uu____10749}) -> begin
(

let uu____10790 = (lemma_pats pats)
in ((binders1), (pre), (post), (uu____10790)))
end
| uu____10807 -> begin
(failwith "impos")
end)
end))
end
| uu____10826 -> begin
(failwith "Impos")
end))
in (match (uu____10638) with
| (binders, pre, post, patterns) -> begin
(

let env1 = (

let uu___115_10874 = env
in {bindings = uu___115_10874.bindings; depth = uu___115_10874.depth; tcenv = uu___115_10874.tcenv; warn = uu___115_10874.warn; cache = uu___115_10874.cache; nolabels = uu___115_10874.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___115_10874.encode_non_total_function_typ; current_module_name = uu___115_10874.current_module_name})
in (

let uu____10875 = (encode_binders FStar_Pervasives_Native.None binders env1)
in (match (uu____10875) with
| (vars, guards, env2, decls, uu____10900) -> begin
(

let uu____10913 = (

let uu____10928 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch1 -> (

let uu____10982 = (

let uu____10993 = (FStar_All.pipe_right branch1 (FStar_List.map (fun t1 -> (encode_smt_pattern t1 env2))))
in (FStar_All.pipe_right uu____10993 FStar_List.unzip))
in (match (uu____10982) with
| (pats, decls1) -> begin
((pats), (decls1))
end)))))
in (FStar_All.pipe_right uu____10928 FStar_List.unzip))
in (match (uu____10913) with
| (pats, decls') -> begin
(

let decls'1 = (FStar_List.flatten decls')
in (

let post1 = (FStar_Syntax_Util.unthunk_lemma_post post)
in (

let env3 = (

let uu___116_11145 = env2
in {bindings = uu___116_11145.bindings; depth = uu___116_11145.depth; tcenv = uu___116_11145.tcenv; warn = uu___116_11145.warn; cache = uu___116_11145.cache; nolabels = true; use_zfuel_name = uu___116_11145.use_zfuel_name; encode_non_total_function_typ = uu___116_11145.encode_non_total_function_typ; current_module_name = uu___116_11145.current_module_name})
in (

let uu____11146 = (

let uu____11151 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula uu____11151 env3))
in (match (uu____11146) with
| (pre1, decls'') -> begin
(

let uu____11158 = (

let uu____11163 = (FStar_Syntax_Util.unmeta post1)
in (encode_formula uu____11163 env3))
in (match (uu____11158) with
| (post2, decls''') -> begin
(

let decls1 = (FStar_List.append decls (FStar_List.append (FStar_List.flatten decls'1) (FStar_List.append decls'' decls''')))
in (

let uu____11173 = (

let uu____11174 = (

let uu____11185 = (

let uu____11186 = (

let uu____11191 = (FStar_SMTEncoding_Util.mk_and_l ((pre1)::guards))
in ((uu____11191), (post2)))
in (FStar_SMTEncoding_Util.mkImp uu____11186))
in ((pats), (vars), (uu____11185)))
in (FStar_SMTEncoding_Util.mkForall uu____11174))
in ((uu____11173), (decls1))))
end))
end)))))
end))
end)))
end))))))
and encode_smt_pattern : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  env_t  ->  (FStar_SMTEncoding_Term.pat * FStar_SMTEncoding_Term.decl Prims.list) = (fun t env -> (

let uu____11200 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____11200) with
| (head1, args) -> begin
(

let head2 = (FStar_Syntax_Util.un_uinst head1)
in (match (((head2.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____11257)::((x, uu____11259))::((t1, uu____11261))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.has_type_lid) -> begin
(

let uu____11288 = (encode_term x env)
in (match (uu____11288) with
| (x1, decls) -> begin
(

let uu____11301 = (encode_term t1 env)
in (match (uu____11301) with
| (t2, decls') -> begin
(

let uu____11314 = (FStar_SMTEncoding_Term.mk_HasType x1 t2)
in ((uu____11314), ((FStar_List.append decls decls'))))
end))
end))
end
| uu____11317 -> begin
(encode_term t env)
end))
end)))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (

let debug1 = (fun phi1 -> (

let uu____11340 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____11340) with
| true -> begin
(

let uu____11341 = (FStar_Syntax_Print.tag_of_term phi1)
in (

let uu____11342 = (FStar_Syntax_Print.term_to_string phi1)
in (FStar_Util.print2 "Formula (%s)  %s\n" uu____11341 uu____11342)))
end
| uu____11343 -> begin
()
end)))
in (

let enc = (fun f r l -> (

let uu____11381 = (FStar_Util.fold_map (fun decls x -> (

let uu____11409 = (encode_term (FStar_Pervasives_Native.fst x) env)
in (match (uu____11409) with
| (t, decls') -> begin
(((FStar_List.append decls decls')), (t))
end))) [] l)
in (match (uu____11381) with
| (decls, args) -> begin
(

let uu____11438 = (

let uu___117_11439 = (f args)
in {FStar_SMTEncoding_Term.tm = uu___117_11439.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___117_11439.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____11438), (decls)))
end)))
in (

let const_op = (fun f r uu____11464 -> (

let uu____11467 = (f r)
in ((uu____11467), ([]))))
in (

let un_op = (fun f l -> (

let uu____11490 = (FStar_List.hd l)
in (FStar_All.pipe_left f uu____11490)))
in (

let bin_op = (fun f uu___93_11510 -> (match (uu___93_11510) with
| (t1)::(t2)::[] -> begin
(f ((t1), (t2)))
end
| uu____11521 -> begin
(failwith "Impossible")
end))
in (

let enc_prop_c = (fun f r l -> (

let uu____11561 = (FStar_Util.fold_map (fun decls uu____11584 -> (match (uu____11584) with
| (t, uu____11598) -> begin
(

let uu____11599 = (encode_formula t env)
in (match (uu____11599) with
| (phi1, decls') -> begin
(((FStar_List.append decls decls')), (phi1))
end))
end)) [] l)
in (match (uu____11561) with
| (decls, phis) -> begin
(

let uu____11628 = (

let uu___118_11629 = (f phis)
in {FStar_SMTEncoding_Term.tm = uu___118_11629.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___118_11629.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____11628), (decls)))
end)))
in (

let eq_op = (fun r args -> (

let rf = (FStar_List.filter (fun uu____11692 -> (match (uu____11692) with
| (a, q) -> begin
(match (q) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____11711)) -> begin
false
end
| uu____11712 -> begin
true
end)
end)) args)
in (match ((Prims.op_disEquality (FStar_List.length rf) (Prims.parse_int "2"))) with
| true -> begin
(

let uu____11727 = (FStar_Util.format1 "eq_op: got %s non-implicit arguments instead of 2?" (Prims.string_of_int (FStar_List.length rf)))
in (failwith uu____11727))
end
| uu____11740 -> begin
(

let uu____11741 = (enc (bin_op FStar_SMTEncoding_Util.mkEq))
in (uu____11741 r rf))
end)))
in (

let mk_imp1 = (fun r uu___94_11776 -> (match (uu___94_11776) with
| ((lhs, uu____11782))::((rhs, uu____11784))::[] -> begin
(

let uu____11811 = (encode_formula rhs env)
in (match (uu____11811) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____11826) -> begin
((l1), (decls1))
end
| uu____11831 -> begin
(

let uu____11832 = (encode_formula lhs env)
in (match (uu____11832) with
| (l2, decls2) -> begin
(

let uu____11843 = (FStar_SMTEncoding_Term.mkImp ((l2), (l1)) r)
in ((uu____11843), ((FStar_List.append decls1 decls2))))
end))
end)
end))
end
| uu____11844 -> begin
(failwith "impossible")
end))
in (

let mk_ite = (fun r uu___95_11871 -> (match (uu___95_11871) with
| ((guard, uu____11877))::((_then, uu____11879))::((_else, uu____11881))::[] -> begin
(

let uu____11918 = (encode_formula guard env)
in (match (uu____11918) with
| (g, decls1) -> begin
(

let uu____11929 = (encode_formula _then env)
in (match (uu____11929) with
| (t, decls2) -> begin
(

let uu____11940 = (encode_formula _else env)
in (match (uu____11940) with
| (e, decls3) -> begin
(

let res = (FStar_SMTEncoding_Term.mkITE ((g), (t), (e)) r)
in ((res), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end))
end))
end
| uu____11952 -> begin
(failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (

let uu____11981 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f uu____11981)))
in (

let connectives = (

let uu____12001 = (

let uu____12016 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd))
in ((FStar_Parser_Const.and_lid), (uu____12016)))
in (

let uu____12039 = (

let uu____12056 = (

let uu____12071 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr))
in ((FStar_Parser_Const.or_lid), (uu____12071)))
in (

let uu____12094 = (

let uu____12111 = (

let uu____12128 = (

let uu____12143 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff))
in ((FStar_Parser_Const.iff_lid), (uu____12143)))
in (

let uu____12166 = (

let uu____12183 = (

let uu____12200 = (

let uu____12215 = (enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot))
in ((FStar_Parser_Const.not_lid), (uu____12215)))
in (uu____12200)::(((FStar_Parser_Const.eq2_lid), (eq_op)))::(((FStar_Parser_Const.eq3_lid), (eq_op)))::(((FStar_Parser_Const.true_lid), ((const_op FStar_SMTEncoding_Term.mkTrue))))::(((FStar_Parser_Const.false_lid), ((const_op FStar_SMTEncoding_Term.mkFalse))))::[])
in (((FStar_Parser_Const.ite_lid), (mk_ite)))::uu____12183)
in (uu____12128)::uu____12166))
in (((FStar_Parser_Const.imp_lid), (mk_imp1)))::uu____12111)
in (uu____12056)::uu____12094))
in (uu____12001)::uu____12039))
in (

let rec fallback = (fun phi1 -> (match (phi1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(

let uu____12504 = (encode_formula phi' env)
in (match (uu____12504) with
| (phi2, decls) -> begin
(

let uu____12515 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled (((phi2), (msg), (r)))) r)
in ((uu____12515), (decls)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (uu____12516) -> begin
(

let uu____12523 = (FStar_Syntax_Util.unmeta phi1)
in (encode_formula uu____12523 env))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(

let uu____12562 = (encode_match e pats FStar_SMTEncoding_Util.mkFalse env encode_formula)
in (match (uu____12562) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____12574; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____12576; FStar_Syntax_Syntax.lbdef = e1; FStar_Syntax_Syntax.lbattrs = uu____12578; FStar_Syntax_Syntax.lbpos = uu____12579})::[]), e2) -> begin
(

let uu____12603 = (encode_let x t1 e1 e2 env encode_formula)
in (match (uu____12603) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let head2 = (FStar_Syntax_Util.un_uinst head1)
in (match (((head2.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____12648)::((x, uu____12650))::((t, uu____12652))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.has_type_lid) -> begin
(

let uu____12679 = (encode_term x env)
in (match (uu____12679) with
| (x1, decls) -> begin
(

let uu____12690 = (encode_term t env)
in (match (uu____12690) with
| (t1, decls') -> begin
(

let uu____12701 = (FStar_SMTEncoding_Term.mk_HasType x1 t1)
in ((uu____12701), ((FStar_List.append decls decls'))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((r, uu____12706))::((msg, uu____12708))::((phi2, uu____12710))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.labeled_lid) -> begin
(

let uu____12733 = (

let uu____12738 = (

let uu____12739 = (FStar_Syntax_Subst.compress r)
in uu____12739.FStar_Syntax_Syntax.n)
in (

let uu____12742 = (

let uu____12743 = (FStar_Syntax_Subst.compress msg)
in uu____12743.FStar_Syntax_Syntax.n)
in ((uu____12738), (uu____12742))))
in (match (uu____12733) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____12752))) -> begin
(

let phi3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((phi2), (FStar_Syntax_Syntax.Meta_labeled (((s), (r1), (false))))))) FStar_Pervasives_Native.None r1)
in (fallback phi3))
end
| uu____12758 -> begin
(fallback phi2)
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((t, uu____12765))::[]) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.auto_squash_lid)) -> begin
(encode_formula t env)
end
| uu____12780 when (head_redex env head2) -> begin
(

let uu____12791 = (whnf env phi1)
in (encode_formula uu____12791 env))
end
| uu____12792 -> begin
(

let uu____12803 = (encode_term phi1 env)
in (match (uu____12803) with
| (tt, decls) -> begin
(

let uu____12814 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___119_12817 = tt
in {FStar_SMTEncoding_Term.tm = uu___119_12817.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___119_12817.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi1.FStar_Syntax_Syntax.pos}))
in ((uu____12814), (decls)))
end))
end))
end
| uu____12818 -> begin
(

let uu____12819 = (encode_term phi1 env)
in (match (uu____12819) with
| (tt, decls) -> begin
(

let uu____12830 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___120_12833 = tt
in {FStar_SMTEncoding_Term.tm = uu___120_12833.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___120_12833.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi1.FStar_Syntax_Syntax.pos}))
in ((uu____12830), (decls)))
end))
end))
in (

let encode_q_body = (fun env1 bs ps body -> (

let uu____12877 = (encode_binders FStar_Pervasives_Native.None bs env1)
in (match (uu____12877) with
| (vars, guards, env2, decls, uu____12916) -> begin
(

let uu____12929 = (

let uu____12942 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let uu____12994 = (

let uu____13005 = (FStar_All.pipe_right p (FStar_List.map (fun uu____13045 -> (match (uu____13045) with
| (t, uu____13059) -> begin
(encode_smt_pattern t (

let uu___121_13065 = env2
in {bindings = uu___121_13065.bindings; depth = uu___121_13065.depth; tcenv = uu___121_13065.tcenv; warn = uu___121_13065.warn; cache = uu___121_13065.cache; nolabels = uu___121_13065.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___121_13065.encode_non_total_function_typ; current_module_name = uu___121_13065.current_module_name}))
end))))
in (FStar_All.pipe_right uu____13005 FStar_List.unzip))
in (match (uu____12994) with
| (p1, decls1) -> begin
((p1), ((FStar_List.flatten decls1)))
end)))))
in (FStar_All.pipe_right uu____12942 FStar_List.unzip))
in (match (uu____12929) with
| (pats, decls') -> begin
(

let uu____13174 = (encode_formula body env2)
in (match (uu____13174) with
| (body1, decls'') -> begin
(

let guards1 = (match (pats) with
| (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (gf), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____13206; FStar_SMTEncoding_Term.rng = uu____13207})::[])::[] when (

let uu____13222 = (FStar_Ident.text_of_lid FStar_Parser_Const.guard_free)
in (Prims.op_Equality uu____13222 gf)) -> begin
[]
end
| uu____13223 -> begin
guards
end)
in (

let uu____13228 = (FStar_SMTEncoding_Util.mk_and_l guards1)
in ((vars), (pats), (uu____13228), (body1), ((FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') decls''))))))
end))
end))
end)))
in ((debug1 phi);
(

let phi1 = (FStar_Syntax_Util.unascribe phi)
in (

let check_pattern_vars = (fun vars pats -> (

let pats1 = (FStar_All.pipe_right pats (FStar_List.map (fun uu____13292 -> (match (uu____13292) with
| (x, uu____13298) -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x)
end))))
in (match (pats1) with
| [] -> begin
()
end
| (hd1)::tl1 -> begin
(

let pat_vars = (

let uu____13306 = (FStar_Syntax_Free.names hd1)
in (FStar_List.fold_left (fun out x -> (

let uu____13318 = (FStar_Syntax_Free.names x)
in (FStar_Util.set_union out uu____13318))) uu____13306 tl1))
in (

let uu____13321 = (FStar_All.pipe_right vars (FStar_Util.find_opt (fun uu____13348 -> (match (uu____13348) with
| (b, uu____13354) -> begin
(

let uu____13355 = (FStar_Util.set_mem b pat_vars)
in (not (uu____13355)))
end))))
in (match (uu____13321) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (x, uu____13361) -> begin
(

let pos = (FStar_List.fold_left (fun out t -> (FStar_Range.union_ranges out t.FStar_Syntax_Syntax.pos)) hd1.FStar_Syntax_Syntax.pos tl1)
in (

let uu____13375 = (

let uu____13380 = (

let uu____13381 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "SMT pattern misses at least one bound variable: %s" uu____13381))
in ((FStar_Errors.Warning_SMTPatternMissingBoundVar), (uu____13380)))
in (FStar_Errors.log_issue pos uu____13375)))
end)))
end)))
in (

let uu____13382 = (FStar_Syntax_Util.destruct_typ_as_formula phi1)
in (match (uu____13382) with
| FStar_Pervasives_Native.None -> begin
(fallback phi1)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(

let uu____13391 = (FStar_All.pipe_right connectives (FStar_List.tryFind (fun uu____13457 -> (match (uu____13457) with
| (l, uu____13471) -> begin
(FStar_Ident.lid_equals op l)
end))))
in (match (uu____13391) with
| FStar_Pervasives_Native.None -> begin
(fallback phi1)
end
| FStar_Pervasives_Native.Some (uu____13510, f) -> begin
(f phi1.FStar_Syntax_Syntax.pos arms)
end))
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____13556 = (encode_q_body env vars pats body)
in (match (uu____13556) with
| (vars1, pats1, guard, body1, decls) -> begin
(

let tm = (

let uu____13601 = (

let uu____13612 = (FStar_SMTEncoding_Util.mkImp ((guard), (body1)))
in ((pats1), (vars1), (uu____13612)))
in (FStar_SMTEncoding_Term.mkForall uu____13601 phi1.FStar_Syntax_Syntax.pos))
in ((tm), (decls)))
end));
)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____13627 = (encode_q_body env vars pats body)
in (match (uu____13627) with
| (vars1, pats1, guard, body1, decls) -> begin
(

let uu____13671 = (

let uu____13672 = (

let uu____13683 = (FStar_SMTEncoding_Util.mkAnd ((guard), (body1)))
in ((pats1), (vars1), (uu____13683)))
in (FStar_SMTEncoding_Term.mkExists uu____13672 phi1.FStar_Syntax_Syntax.pos))
in ((uu____13671), (decls)))
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

let uu____13806 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____13806) with
| (asym, a) -> begin
(

let uu____13813 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____13813) with
| (xsym, x) -> begin
(

let uu____13820 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____13820) with
| (ysym, y) -> begin
(

let quant = (fun vars body x1 -> (

let xname_decl = (

let uu____13874 = (

let uu____13885 = (FStar_All.pipe_right vars (FStar_List.map FStar_Pervasives_Native.snd))
in ((x1), (uu____13885), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____13874))
in (

let xtok = (Prims.strcat x1 "@tok")
in (

let xtok_decl = FStar_SMTEncoding_Term.DeclFun (((xtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let xapp = (

let uu____13907 = (

let uu____13914 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((x1), (uu____13914)))
in (FStar_SMTEncoding_Util.mkApp uu____13907))
in (

let xtok1 = (FStar_SMTEncoding_Util.mkApp ((xtok), ([])))
in (

let xtok_app = (mk_Apply xtok1 vars)
in (

let uu____13927 = (

let uu____13930 = (

let uu____13933 = (

let uu____13936 = (

let uu____13937 = (

let uu____13944 = (

let uu____13945 = (

let uu____13956 = (FStar_SMTEncoding_Util.mkEq ((xapp), (body)))
in ((((xapp)::[])::[]), (vars), (uu____13956)))
in (FStar_SMTEncoding_Util.mkForall uu____13945))
in ((uu____13944), (FStar_Pervasives_Native.None), ((Prims.strcat "primitive_" x1))))
in (FStar_SMTEncoding_Util.mkAssume uu____13937))
in (

let uu____13965 = (

let uu____13968 = (

let uu____13969 = (

let uu____13976 = (

let uu____13977 = (

let uu____13988 = (FStar_SMTEncoding_Util.mkEq ((xtok_app), (xapp)))
in ((((xtok_app)::[])::[]), (vars), (uu____13988)))
in (FStar_SMTEncoding_Util.mkForall uu____13977))
in ((uu____13976), (FStar_Pervasives_Native.Some ("Name-token correspondence")), ((Prims.strcat "token_correspondence_" x1))))
in (FStar_SMTEncoding_Util.mkAssume uu____13969))
in (uu____13968)::[])
in (uu____13936)::uu____13965))
in (xtok_decl)::uu____13933)
in (xname_decl)::uu____13930)
in ((xtok1), ((FStar_List.length vars)), (uu____13927))))))))))
in (

let axy = (((asym), (FStar_SMTEncoding_Term.Term_sort)))::(((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let xy = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let qx = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let prims1 = (

let uu____14078 = (

let uu____14094 = (

let uu____14107 = (

let uu____14108 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____14108))
in (quant axy uu____14107))
in ((FStar_Parser_Const.op_Eq), (uu____14094)))
in (

let uu____14120 = (

let uu____14138 = (

let uu____14154 = (

let uu____14167 = (

let uu____14168 = (

let uu____14169 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_SMTEncoding_Util.mkNot uu____14169))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____14168))
in (quant axy uu____14167))
in ((FStar_Parser_Const.op_notEq), (uu____14154)))
in (

let uu____14181 = (

let uu____14199 = (

let uu____14215 = (

let uu____14228 = (

let uu____14229 = (

let uu____14230 = (

let uu____14235 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____14236 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____14235), (uu____14236))))
in (FStar_SMTEncoding_Util.mkLT uu____14230))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____14229))
in (quant xy uu____14228))
in ((FStar_Parser_Const.op_LT), (uu____14215)))
in (

let uu____14248 = (

let uu____14266 = (

let uu____14282 = (

let uu____14295 = (

let uu____14296 = (

let uu____14297 = (

let uu____14302 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____14303 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____14302), (uu____14303))))
in (FStar_SMTEncoding_Util.mkLTE uu____14297))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____14296))
in (quant xy uu____14295))
in ((FStar_Parser_Const.op_LTE), (uu____14282)))
in (

let uu____14315 = (

let uu____14333 = (

let uu____14349 = (

let uu____14362 = (

let uu____14363 = (

let uu____14364 = (

let uu____14369 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____14370 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____14369), (uu____14370))))
in (FStar_SMTEncoding_Util.mkGT uu____14364))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____14363))
in (quant xy uu____14362))
in ((FStar_Parser_Const.op_GT), (uu____14349)))
in (

let uu____14382 = (

let uu____14400 = (

let uu____14416 = (

let uu____14429 = (

let uu____14430 = (

let uu____14431 = (

let uu____14436 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____14437 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____14436), (uu____14437))))
in (FStar_SMTEncoding_Util.mkGTE uu____14431))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____14430))
in (quant xy uu____14429))
in ((FStar_Parser_Const.op_GTE), (uu____14416)))
in (

let uu____14449 = (

let uu____14467 = (

let uu____14483 = (

let uu____14496 = (

let uu____14497 = (

let uu____14498 = (

let uu____14503 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____14504 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____14503), (uu____14504))))
in (FStar_SMTEncoding_Util.mkSub uu____14498))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____14497))
in (quant xy uu____14496))
in ((FStar_Parser_Const.op_Subtraction), (uu____14483)))
in (

let uu____14516 = (

let uu____14534 = (

let uu____14550 = (

let uu____14563 = (

let uu____14564 = (

let uu____14565 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Util.mkMinus uu____14565))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____14564))
in (quant qx uu____14563))
in ((FStar_Parser_Const.op_Minus), (uu____14550)))
in (

let uu____14577 = (

let uu____14595 = (

let uu____14611 = (

let uu____14624 = (

let uu____14625 = (

let uu____14626 = (

let uu____14631 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____14632 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____14631), (uu____14632))))
in (FStar_SMTEncoding_Util.mkAdd uu____14626))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____14625))
in (quant xy uu____14624))
in ((FStar_Parser_Const.op_Addition), (uu____14611)))
in (

let uu____14644 = (

let uu____14662 = (

let uu____14678 = (

let uu____14691 = (

let uu____14692 = (

let uu____14693 = (

let uu____14698 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____14699 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____14698), (uu____14699))))
in (FStar_SMTEncoding_Util.mkMul uu____14693))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____14692))
in (quant xy uu____14691))
in ((FStar_Parser_Const.op_Multiply), (uu____14678)))
in (

let uu____14711 = (

let uu____14729 = (

let uu____14745 = (

let uu____14758 = (

let uu____14759 = (

let uu____14760 = (

let uu____14765 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____14766 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____14765), (uu____14766))))
in (FStar_SMTEncoding_Util.mkDiv uu____14760))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____14759))
in (quant xy uu____14758))
in ((FStar_Parser_Const.op_Division), (uu____14745)))
in (

let uu____14778 = (

let uu____14796 = (

let uu____14812 = (

let uu____14825 = (

let uu____14826 = (

let uu____14827 = (

let uu____14832 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____14833 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____14832), (uu____14833))))
in (FStar_SMTEncoding_Util.mkMod uu____14827))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____14826))
in (quant xy uu____14825))
in ((FStar_Parser_Const.op_Modulus), (uu____14812)))
in (

let uu____14845 = (

let uu____14863 = (

let uu____14879 = (

let uu____14892 = (

let uu____14893 = (

let uu____14894 = (

let uu____14899 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____14900 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____14899), (uu____14900))))
in (FStar_SMTEncoding_Util.mkAnd uu____14894))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____14893))
in (quant xy uu____14892))
in ((FStar_Parser_Const.op_And), (uu____14879)))
in (

let uu____14912 = (

let uu____14930 = (

let uu____14946 = (

let uu____14959 = (

let uu____14960 = (

let uu____14961 = (

let uu____14966 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____14967 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____14966), (uu____14967))))
in (FStar_SMTEncoding_Util.mkOr uu____14961))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____14960))
in (quant xy uu____14959))
in ((FStar_Parser_Const.op_Or), (uu____14946)))
in (

let uu____14979 = (

let uu____14997 = (

let uu____15013 = (

let uu____15026 = (

let uu____15027 = (

let uu____15028 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Util.mkNot uu____15028))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____15027))
in (quant qx uu____15026))
in ((FStar_Parser_Const.op_Negation), (uu____15013)))
in (uu____14997)::[])
in (uu____14930)::uu____14979))
in (uu____14863)::uu____14912))
in (uu____14796)::uu____14845))
in (uu____14729)::uu____14778))
in (uu____14662)::uu____14711))
in (uu____14595)::uu____14644))
in (uu____14534)::uu____14577))
in (uu____14467)::uu____14516))
in (uu____14400)::uu____14449))
in (uu____14333)::uu____14382))
in (uu____14266)::uu____14315))
in (uu____14199)::uu____14248))
in (uu____14138)::uu____14181))
in (uu____14078)::uu____14120))
in (

let mk1 = (fun l v1 -> (

let uu____15299 = (

let uu____15310 = (FStar_All.pipe_right prims1 (FStar_List.find (fun uu____15380 -> (match (uu____15380) with
| (l', uu____15396) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right uu____15310 (FStar_Option.map (fun uu____15472 -> (match (uu____15472) with
| (uu____15495, b) -> begin
(b v1)
end)))))
in (FStar_All.pipe_right uu____15299 FStar_Option.get)))
in (

let is = (fun l -> (FStar_All.pipe_right prims1 (FStar_Util.for_some (fun uu____15586 -> (match (uu____15586) with
| (l', uu____15602) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk1; is = is})))))))
end))
end))
end))


let pretype_axiom : env_t  ->  FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun env tapp vars -> (

let uu____15652 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____15652) with
| (xxsym, xx) -> begin
(

let uu____15659 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____15659) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let tapp_hash = (FStar_SMTEncoding_Term.hash_of_term tapp)
in (

let module_name = env.current_module_name
in (

let uu____15669 = (

let uu____15676 = (

let uu____15677 = (

let uu____15688 = (

let uu____15689 = (

let uu____15694 = (

let uu____15695 = (

let uu____15700 = (FStar_SMTEncoding_Util.mkApp (("PreType"), ((xx)::[])))
in ((tapp), (uu____15700)))
in (FStar_SMTEncoding_Util.mkEq uu____15695))
in ((xx_has_type), (uu____15694)))
in (FStar_SMTEncoding_Util.mkImp uu____15689))
in ((((xx_has_type)::[])::[]), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars), (uu____15688)))
in (FStar_SMTEncoding_Util.mkForall uu____15677))
in (

let uu____15719 = (

let uu____15720 = (

let uu____15721 = (

let uu____15722 = (FStar_Util.digest_of_string tapp_hash)
in (Prims.strcat "_pretyping_" uu____15722))
in (Prims.strcat module_name uu____15721))
in (varops.mk_unique uu____15720))
in ((uu____15676), (FStar_Pervasives_Native.Some ("pretyping")), (uu____15719))))
in (FStar_SMTEncoding_Util.mkAssume uu____15669)))))
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

let uu____15770 = (

let uu____15771 = (

let uu____15778 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in ((uu____15778), (FStar_Pervasives_Native.Some ("unit typing")), ("unit_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____15771))
in (

let uu____15779 = (

let uu____15782 = (

let uu____15783 = (

let uu____15790 = (

let uu____15791 = (

let uu____15802 = (

let uu____15803 = (

let uu____15808 = (FStar_SMTEncoding_Util.mkEq ((x), (FStar_SMTEncoding_Term.mk_Term_unit)))
in ((typing_pred), (uu____15808)))
in (FStar_SMTEncoding_Util.mkImp uu____15803))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____15802)))
in (mkForall_fuel uu____15791))
in ((uu____15790), (FStar_Pervasives_Native.Some ("unit inversion")), ("unit_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____15783))
in (uu____15782)::[])
in (uu____15770)::uu____15779))))
in (

let mk_bool = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Bool_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____15848 = (

let uu____15849 = (

let uu____15856 = (

let uu____15857 = (

let uu____15868 = (

let uu____15873 = (

let uu____15876 = (FStar_SMTEncoding_Term.boxBool b)
in (uu____15876)::[])
in (uu____15873)::[])
in (

let uu____15881 = (

let uu____15882 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType uu____15882 tt))
in ((uu____15868), ((bb)::[]), (uu____15881))))
in (FStar_SMTEncoding_Util.mkForall uu____15857))
in ((uu____15856), (FStar_Pervasives_Native.Some ("bool typing")), ("bool_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____15849))
in (

let uu____15895 = (

let uu____15898 = (

let uu____15899 = (

let uu____15906 = (

let uu____15907 = (

let uu____15918 = (

let uu____15919 = (

let uu____15924 = (FStar_SMTEncoding_Term.mk_tester (FStar_Pervasives_Native.fst FStar_SMTEncoding_Term.boxBoolFun) x)
in ((typing_pred), (uu____15924)))
in (FStar_SMTEncoding_Util.mkImp uu____15919))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____15918)))
in (mkForall_fuel uu____15907))
in ((uu____15906), (FStar_Pervasives_Native.Some ("bool inversion")), ("bool_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____15899))
in (uu____15898)::[])
in (uu____15848)::uu____15895))))))
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

let uu____15972 = (

let uu____15973 = (

let uu____15980 = (

let uu____15983 = (

let uu____15986 = (

let uu____15989 = (FStar_SMTEncoding_Term.boxInt a)
in (

let uu____15990 = (

let uu____15993 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____15993)::[])
in (uu____15989)::uu____15990))
in (tt)::uu____15986)
in (tt)::uu____15983)
in (("Prims.Precedes"), (uu____15980)))
in (FStar_SMTEncoding_Util.mkApp uu____15973))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15972))
in (

let precedes_y_x = (

let uu____15997 = (FStar_SMTEncoding_Util.mkApp (("Precedes"), ((y)::(x)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15997))
in (

let uu____16000 = (

let uu____16001 = (

let uu____16008 = (

let uu____16009 = (

let uu____16020 = (

let uu____16025 = (

let uu____16028 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____16028)::[])
in (uu____16025)::[])
in (

let uu____16033 = (

let uu____16034 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType uu____16034 tt))
in ((uu____16020), ((bb)::[]), (uu____16033))))
in (FStar_SMTEncoding_Util.mkForall uu____16009))
in ((uu____16008), (FStar_Pervasives_Native.Some ("int typing")), ("int_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____16001))
in (

let uu____16047 = (

let uu____16050 = (

let uu____16051 = (

let uu____16058 = (

let uu____16059 = (

let uu____16070 = (

let uu____16071 = (

let uu____16076 = (FStar_SMTEncoding_Term.mk_tester (FStar_Pervasives_Native.fst FStar_SMTEncoding_Term.boxIntFun) x)
in ((typing_pred), (uu____16076)))
in (FStar_SMTEncoding_Util.mkImp uu____16071))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____16070)))
in (mkForall_fuel uu____16059))
in ((uu____16058), (FStar_Pervasives_Native.Some ("int inversion")), ("int_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____16051))
in (

let uu____16093 = (

let uu____16096 = (

let uu____16097 = (

let uu____16104 = (

let uu____16105 = (

let uu____16116 = (

let uu____16117 = (

let uu____16122 = (

let uu____16123 = (

let uu____16126 = (

let uu____16129 = (

let uu____16132 = (

let uu____16133 = (

let uu____16138 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____16139 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____16138), (uu____16139))))
in (FStar_SMTEncoding_Util.mkGT uu____16133))
in (

let uu____16140 = (

let uu____16143 = (

let uu____16144 = (

let uu____16149 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____16150 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____16149), (uu____16150))))
in (FStar_SMTEncoding_Util.mkGTE uu____16144))
in (

let uu____16151 = (

let uu____16154 = (

let uu____16155 = (

let uu____16160 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____16161 = (FStar_SMTEncoding_Term.unboxInt x)
in ((uu____16160), (uu____16161))))
in (FStar_SMTEncoding_Util.mkLT uu____16155))
in (uu____16154)::[])
in (uu____16143)::uu____16151))
in (uu____16132)::uu____16140))
in (typing_pred_y)::uu____16129)
in (typing_pred)::uu____16126)
in (FStar_SMTEncoding_Util.mk_and_l uu____16123))
in ((uu____16122), (precedes_y_x)))
in (FStar_SMTEncoding_Util.mkImp uu____16117))
in ((((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[]), ((xx)::(yy)::[]), (uu____16116)))
in (mkForall_fuel uu____16105))
in ((uu____16104), (FStar_Pervasives_Native.Some ("well-founded ordering on nat (alt)")), ("well-founded-ordering-on-nat")))
in (FStar_SMTEncoding_Util.mkAssume uu____16097))
in (uu____16096)::[])
in (uu____16050)::uu____16093))
in (uu____16000)::uu____16047)))))))))))
in (

let mk_str = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.String_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____16205 = (

let uu____16206 = (

let uu____16213 = (

let uu____16214 = (

let uu____16225 = (

let uu____16230 = (

let uu____16233 = (FStar_SMTEncoding_Term.boxString b)
in (uu____16233)::[])
in (uu____16230)::[])
in (

let uu____16238 = (

let uu____16239 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType uu____16239 tt))
in ((uu____16225), ((bb)::[]), (uu____16238))))
in (FStar_SMTEncoding_Util.mkForall uu____16214))
in ((uu____16213), (FStar_Pervasives_Native.Some ("string typing")), ("string_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____16206))
in (

let uu____16252 = (

let uu____16255 = (

let uu____16256 = (

let uu____16263 = (

let uu____16264 = (

let uu____16275 = (

let uu____16276 = (

let uu____16281 = (FStar_SMTEncoding_Term.mk_tester (FStar_Pervasives_Native.fst FStar_SMTEncoding_Term.boxStringFun) x)
in ((typing_pred), (uu____16281)))
in (FStar_SMTEncoding_Util.mkImp uu____16276))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____16275)))
in (mkForall_fuel uu____16264))
in ((uu____16263), (FStar_Pervasives_Native.Some ("string inversion")), ("string_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____16256))
in (uu____16255)::[])
in (uu____16205)::uu____16252))))))
in (

let mk_true_interp = (fun env nm true_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((true_tm)::[])))
in ((FStar_SMTEncoding_Util.mkAssume ((valid), (FStar_Pervasives_Native.Some ("True interpretation")), ("true_interp"))))::[]))
in (

let mk_false_interp = (fun env nm false_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((false_tm)::[])))
in (

let uu____16336 = (

let uu____16337 = (

let uu____16344 = (FStar_SMTEncoding_Util.mkIff ((FStar_SMTEncoding_Util.mkFalse), (valid)))
in ((uu____16344), (FStar_Pervasives_Native.Some ("False interpretation")), ("false_interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16337))
in (uu____16336)::[])))
in (

let mk_and_interp = (fun env conj uu____16360 -> (

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

let uu____16385 = (

let uu____16386 = (

let uu____16393 = (

let uu____16394 = (

let uu____16405 = (

let uu____16406 = (

let uu____16411 = (FStar_SMTEncoding_Util.mkAnd ((valid_a), (valid_b)))
in ((uu____16411), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____16406))
in ((((l_and_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____16405)))
in (FStar_SMTEncoding_Util.mkForall uu____16394))
in ((uu____16393), (FStar_Pervasives_Native.Some ("/\\ interpretation")), ("l_and-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16386))
in (uu____16385)::[]))))))))))
in (

let mk_or_interp = (fun env disj uu____16447 -> (

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

let uu____16472 = (

let uu____16473 = (

let uu____16480 = (

let uu____16481 = (

let uu____16492 = (

let uu____16493 = (

let uu____16498 = (FStar_SMTEncoding_Util.mkOr ((valid_a), (valid_b)))
in ((uu____16498), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____16493))
in ((((l_or_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____16492)))
in (FStar_SMTEncoding_Util.mkForall uu____16481))
in ((uu____16480), (FStar_Pervasives_Native.Some ("\\/ interpretation")), ("l_or-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16473))
in (uu____16472)::[]))))))))))
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

let uu____16559 = (

let uu____16560 = (

let uu____16567 = (

let uu____16568 = (

let uu____16579 = (

let uu____16580 = (

let uu____16585 = (FStar_SMTEncoding_Util.mkEq ((x1), (y1)))
in ((uu____16585), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____16580))
in ((((eq2_x_y)::[])::[]), ((aa)::(xx1)::(yy1)::[]), (uu____16579)))
in (FStar_SMTEncoding_Util.mkForall uu____16568))
in ((uu____16567), (FStar_Pervasives_Native.Some ("Eq2 interpretation")), ("eq2-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16560))
in (uu____16559)::[]))))))))))
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

let uu____16656 = (

let uu____16657 = (

let uu____16664 = (

let uu____16665 = (

let uu____16676 = (

let uu____16677 = (

let uu____16682 = (FStar_SMTEncoding_Util.mkEq ((x1), (y1)))
in ((uu____16682), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____16677))
in ((((eq3_x_y)::[])::[]), ((aa)::(bb)::(xx1)::(yy1)::[]), (uu____16676)))
in (FStar_SMTEncoding_Util.mkForall uu____16665))
in ((uu____16664), (FStar_Pervasives_Native.Some ("Eq3 interpretation")), ("eq3-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16657))
in (uu____16656)::[]))))))))))))
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

let uu____16751 = (

let uu____16752 = (

let uu____16759 = (

let uu____16760 = (

let uu____16771 = (

let uu____16772 = (

let uu____16777 = (FStar_SMTEncoding_Util.mkImp ((valid_a), (valid_b)))
in ((uu____16777), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____16772))
in ((((l_imp_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____16771)))
in (FStar_SMTEncoding_Util.mkForall uu____16760))
in ((uu____16759), (FStar_Pervasives_Native.Some ("==> interpretation")), ("l_imp-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16752))
in (uu____16751)::[]))))))))))
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

let uu____16838 = (

let uu____16839 = (

let uu____16846 = (

let uu____16847 = (

let uu____16858 = (

let uu____16859 = (

let uu____16864 = (FStar_SMTEncoding_Util.mkIff ((valid_a), (valid_b)))
in ((uu____16864), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____16859))
in ((((l_iff_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____16858)))
in (FStar_SMTEncoding_Util.mkForall uu____16847))
in ((uu____16846), (FStar_Pervasives_Native.Some ("<==> interpretation")), ("l_iff-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16839))
in (uu____16838)::[]))))))))))
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

let uu____16914 = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____16914))
in (

let uu____16917 = (

let uu____16918 = (

let uu____16925 = (

let uu____16926 = (

let uu____16937 = (FStar_SMTEncoding_Util.mkIff ((not_valid_a), (valid)))
in ((((l_not_a)::[])::[]), ((aa)::[]), (uu____16937)))
in (FStar_SMTEncoding_Util.mkForall uu____16926))
in ((uu____16925), (FStar_Pervasives_Native.Some ("not interpretation")), ("l_not-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16918))
in (uu____16917)::[])))))))
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

let uu____16995 = (

let uu____17002 = (

let uu____17005 = (FStar_SMTEncoding_Util.mk_ApplyTT b x1)
in (uu____17005)::[])
in (("Valid"), (uu____17002)))
in (FStar_SMTEncoding_Util.mkApp uu____16995))
in (

let uu____17008 = (

let uu____17009 = (

let uu____17016 = (

let uu____17017 = (

let uu____17028 = (

let uu____17029 = (

let uu____17034 = (

let uu____17035 = (

let uu____17046 = (

let uu____17051 = (

let uu____17054 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in (uu____17054)::[])
in (uu____17051)::[])
in (

let uu____17059 = (

let uu____17060 = (

let uu____17065 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in ((uu____17065), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp uu____17060))
in ((uu____17046), ((xx1)::[]), (uu____17059))))
in (FStar_SMTEncoding_Util.mkForall uu____17035))
in ((uu____17034), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____17029))
in ((((l_forall_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____17028)))
in (FStar_SMTEncoding_Util.mkForall uu____17017))
in ((uu____17016), (FStar_Pervasives_Native.Some ("forall interpretation")), ("forall-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____17009))
in (uu____17008)::[])))))))))))
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

let uu____17139 = (

let uu____17146 = (

let uu____17149 = (FStar_SMTEncoding_Util.mk_ApplyTT b x1)
in (uu____17149)::[])
in (("Valid"), (uu____17146)))
in (FStar_SMTEncoding_Util.mkApp uu____17139))
in (

let uu____17152 = (

let uu____17153 = (

let uu____17160 = (

let uu____17161 = (

let uu____17172 = (

let uu____17173 = (

let uu____17178 = (

let uu____17179 = (

let uu____17190 = (

let uu____17195 = (

let uu____17198 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in (uu____17198)::[])
in (uu____17195)::[])
in (

let uu____17203 = (

let uu____17204 = (

let uu____17209 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in ((uu____17209), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp uu____17204))
in ((uu____17190), ((xx1)::[]), (uu____17203))))
in (FStar_SMTEncoding_Util.mkExists uu____17179))
in ((uu____17178), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____17173))
in ((((l_exists_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____17172)))
in (FStar_SMTEncoding_Util.mkForall uu____17161))
in ((uu____17160), (FStar_Pervasives_Native.Some ("exists interpretation")), ("exists-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____17153))
in (uu____17152)::[])))))))))))
in (

let mk_range_interp = (fun env range tt -> (

let range_ty = (FStar_SMTEncoding_Util.mkApp ((range), ([])))
in (

let uu____17261 = (

let uu____17262 = (

let uu____17269 = (

let uu____17270 = (FStar_SMTEncoding_Term.mk_Range_const ())
in (FStar_SMTEncoding_Term.mk_HasTypeZ uu____17270 range_ty))
in (

let uu____17271 = (varops.mk_unique "typing_range_const")
in ((uu____17269), (FStar_Pervasives_Native.Some ("Range_const typing")), (uu____17271))))
in (FStar_SMTEncoding_Util.mkAssume uu____17262))
in (uu____17261)::[])))
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

let uu____17309 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1"))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel uu____17309 x1 t))
in (

let uu____17310 = (

let uu____17321 = (FStar_SMTEncoding_Util.mkImp ((hastypeZ), (hastypeS)))
in ((((hastypeZ)::[])::[]), ((xx1)::[]), (uu____17321)))
in (FStar_SMTEncoding_Util.mkForall uu____17310))))
in (

let uu____17338 = (

let uu____17339 = (

let uu____17346 = (

let uu____17347 = (

let uu____17358 = (FStar_SMTEncoding_Util.mkImp ((valid), (body)))
in ((((inversion_t)::[])::[]), ((tt1)::[]), (uu____17358)))
in (FStar_SMTEncoding_Util.mkForall uu____17347))
in ((uu____17346), (FStar_Pervasives_Native.Some ("inversion interpretation")), ("inversion-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____17339))
in (uu____17338)::[])))))))))
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

let uu____17406 = (

let uu____17407 = (

let uu____17414 = (

let uu____17415 = (

let uu____17430 = (

let uu____17431 = (

let uu____17436 = (FStar_SMTEncoding_Util.mkEq ((with_type_t_e), (e)))
in (

let uu____17437 = (FStar_SMTEncoding_Term.mk_HasType with_type_t_e t)
in ((uu____17436), (uu____17437))))
in (FStar_SMTEncoding_Util.mkAnd uu____17431))
in ((((with_type_t_e)::[])::[]), (FStar_Pervasives_Native.Some ((Prims.parse_int "0"))), ((tt1)::(ee)::[]), (uu____17430)))
in (FStar_SMTEncoding_Util.mkForall' uu____17415))
in ((uu____17414), (FStar_Pervasives_Native.Some ("with_type primitive axiom")), ("@with_type_primitive_axiom")))
in (FStar_SMTEncoding_Util.mkAssume uu____17407))
in (uu____17406)::[])))))))
in (

let prims1 = (((FStar_Parser_Const.unit_lid), (mk_unit)))::(((FStar_Parser_Const.bool_lid), (mk_bool)))::(((FStar_Parser_Const.int_lid), (mk_int)))::(((FStar_Parser_Const.string_lid), (mk_str)))::(((FStar_Parser_Const.true_lid), (mk_true_interp)))::(((FStar_Parser_Const.false_lid), (mk_false_interp)))::(((FStar_Parser_Const.and_lid), (mk_and_interp)))::(((FStar_Parser_Const.or_lid), (mk_or_interp)))::(((FStar_Parser_Const.eq2_lid), (mk_eq2_interp)))::(((FStar_Parser_Const.eq3_lid), (mk_eq3_interp)))::(((FStar_Parser_Const.imp_lid), (mk_imp_interp)))::(((FStar_Parser_Const.iff_lid), (mk_iff_interp)))::(((FStar_Parser_Const.not_lid), (mk_not_interp)))::(((FStar_Parser_Const.forall_lid), (mk_forall_interp)))::(((FStar_Parser_Const.exists_lid), (mk_exists_interp)))::(((FStar_Parser_Const.range_lid), (mk_range_interp)))::(((FStar_Parser_Const.inversion_lid), (mk_inversion_axiom)))::(((FStar_Parser_Const.with_type_lid), (mk_with_type_axiom)))::[]
in (fun env t s tt -> (

let uu____17929 = (FStar_Util.find_opt (fun uu____17965 -> (match (uu____17965) with
| (l, uu____17979) -> begin
(FStar_Ident.lid_equals l t)
end)) prims1)
in (match (uu____17929) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (uu____18019, f) -> begin
(f env s tt)
end))))))))))))))))))))))))))


let encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____18076 = (encode_function_type_as_formula t env)
in (match (uu____18076) with
| (form, decls) -> begin
(FStar_List.append decls (((FStar_SMTEncoding_Util.mkAssume ((form), (FStar_Pervasives_Native.Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str))), ((Prims.strcat "lemma_" lid.FStar_Ident.str)))))::[]))
end))))


let encode_free_var : Prims.bool  ->  env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun uninterpreted env fv tt t_norm quals -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____18126 = (((

let uu____18129 = ((FStar_Syntax_Util.is_pure_or_ghost_function t_norm) || (FStar_TypeChecker_Env.is_reifiable_function env.tcenv t_norm))
in (FStar_All.pipe_left Prims.op_Negation uu____18129)) || (FStar_Syntax_Util.is_lemma t_norm)) || uninterpreted)
in (match (uu____18126) with
| true -> begin
(

let arg_sorts = (

let uu____18139 = (

let uu____18140 = (FStar_Syntax_Subst.compress t_norm)
in uu____18140.FStar_Syntax_Syntax.n)
in (match (uu____18139) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____18146) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun uu____18176 -> FStar_SMTEncoding_Term.Term_sort)))
end
| uu____18181 -> begin
[]
end))
in (

let arity = (FStar_List.length arg_sorts)
in (

let uu____18183 = (new_term_constant_and_tok_from_lid env lid arity)
in (match (uu____18183) with
| (vname, vtok, env1) -> begin
(

let d = FStar_SMTEncoding_Term.DeclFun (((vname), (arg_sorts), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Uninterpreted function symbol for impure function"))))
in (

let dd = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Uninterpreted name for impure function"))))
in (((d)::(dd)::[]), (env1))))
end))))
end
| uu____18211 -> begin
(

let uu____18212 = (prims.is lid)
in (match (uu____18212) with
| true -> begin
(

let vname = (varops.new_fvar lid)
in (

let uu____18220 = (prims.mk lid vname)
in (match (uu____18220) with
| (tok, arity, definition) -> begin
(

let env1 = (push_free_var env lid arity vname (FStar_Pervasives_Native.Some (tok)))
in ((definition), (env1)))
end)))
end
| uu____18245 -> begin
(

let encode_non_total_function_typ = (Prims.op_disEquality lid.FStar_Ident.nsstr "Prims")
in (

let uu____18247 = (

let uu____18264 = (curried_arrow_formals_comp t_norm)
in (match (uu____18264) with
| (args, comp) -> begin
(

let comp1 = (

let uu____18306 = (FStar_TypeChecker_Env.is_reifiable_comp env.tcenv comp)
in (match (uu____18306) with
| true -> begin
(

let uu____18307 = (FStar_TypeChecker_Env.reify_comp (

let uu___122_18310 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___122_18310.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___122_18310.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___122_18310.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___122_18310.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___122_18310.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___122_18310.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___122_18310.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___122_18310.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___122_18310.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___122_18310.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___122_18310.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___122_18310.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___122_18310.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___122_18310.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___122_18310.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___122_18310.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___122_18310.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___122_18310.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___122_18310.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___122_18310.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___122_18310.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___122_18310.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___122_18310.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___122_18310.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___122_18310.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___122_18310.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___122_18310.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___122_18310.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___122_18310.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___122_18310.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___122_18310.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___122_18310.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___122_18310.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___122_18310.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___122_18310.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___122_18310.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___122_18310.FStar_TypeChecker_Env.dep_graph}) comp FStar_Syntax_Syntax.U_unknown)
in (FStar_Syntax_Syntax.mk_Total uu____18307))
end
| uu____18311 -> begin
comp
end))
in (match (encode_non_total_function_typ) with
| true -> begin
(

let uu____18328 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp1)
in ((args), (uu____18328)))
end
| uu____18347 -> begin
((args), (((FStar_Pervasives_Native.None), ((FStar_Syntax_Util.comp_result comp1)))))
end))
end))
in (match (uu____18247) with
| (formals, (pre_opt, res_t)) -> begin
(

let arity = (FStar_List.length formals)
in (

let uu____18402 = (new_term_constant_and_tok_from_lid env lid arity)
in (match (uu____18402) with
| (vname, vtok, env1) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
end
| uu____18427 -> begin
(FStar_SMTEncoding_Util.mkApp ((vtok), ([])))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun uu___96_18483 -> (match (uu___96_18483) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(

let uu____18487 = (FStar_Util.prefix vars)
in (match (uu____18487) with
| (uu____18508, (xxsym, uu____18510)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____18528 = (

let uu____18529 = (

let uu____18536 = (

let uu____18537 = (

let uu____18548 = (

let uu____18549 = (

let uu____18554 = (

let uu____18555 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____18555))
in ((vapp), (uu____18554)))
in (FStar_SMTEncoding_Util.mkEq uu____18549))
in ((((vapp)::[])::[]), (vars), (uu____18548)))
in (FStar_SMTEncoding_Util.mkForall uu____18537))
in ((uu____18536), (FStar_Pervasives_Native.Some ("Discriminator equation")), ((Prims.strcat "disc_equation_" (escape d.FStar_Ident.str)))))
in (FStar_SMTEncoding_Util.mkAssume uu____18529))
in (uu____18528)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(

let uu____18566 = (FStar_Util.prefix vars)
in (match (uu____18566) with
| (uu____18587, (xxsym, uu____18589)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f1 = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (

let tp_name = (mk_term_projector_name d f1)
in (

let prim_app = (FStar_SMTEncoding_Util.mkApp ((tp_name), ((xx)::[])))
in (

let uu____18612 = (

let uu____18613 = (

let uu____18620 = (

let uu____18621 = (

let uu____18632 = (FStar_SMTEncoding_Util.mkEq ((vapp), (prim_app)))
in ((((vapp)::[])::[]), (vars), (uu____18632)))
in (FStar_SMTEncoding_Util.mkForall uu____18621))
in ((uu____18620), (FStar_Pervasives_Native.Some ("Projector equation")), ((Prims.strcat "proj_equation_" tp_name))))
in (FStar_SMTEncoding_Util.mkAssume uu____18613))
in (uu____18612)::[])))))
end))
end
| uu____18641 -> begin
[]
end)))))
in (

let uu____18642 = (encode_binders FStar_Pervasives_Native.None formals env1)
in (match (uu____18642) with
| (vars, guards, env', decls1, uu____18669) -> begin
(

let uu____18682 = (match (pre_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____18691 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____18691), (decls1)))
end
| FStar_Pervasives_Native.Some (p) -> begin
(

let uu____18693 = (encode_formula p env')
in (match (uu____18693) with
| (g, ds) -> begin
(

let uu____18704 = (FStar_SMTEncoding_Util.mk_and_l ((g)::guards))
in ((uu____18704), ((FStar_List.append decls1 ds))))
end))
end)
in (match (uu____18682) with
| (guard, decls11) -> begin
(

let vtok_app = (mk_Apply vtok_tm vars)
in (

let vapp = (

let uu____18717 = (

let uu____18724 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((vname), (uu____18724)))
in (FStar_SMTEncoding_Util.mkApp uu____18717))
in (

let uu____18729 = (

let vname_decl = (

let uu____18737 = (

let uu____18748 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____18764 -> FStar_SMTEncoding_Term.Term_sort)))
in ((vname), (uu____18748), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____18737))
in (

let uu____18771 = (

let env2 = (

let uu___123_18777 = env1
in {bindings = uu___123_18777.bindings; depth = uu___123_18777.depth; tcenv = uu___123_18777.tcenv; warn = uu___123_18777.warn; cache = uu___123_18777.cache; nolabels = uu___123_18777.nolabels; use_zfuel_name = uu___123_18777.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = uu___123_18777.current_module_name})
in (

let uu____18778 = (

let uu____18779 = (head_normal env2 tt)
in (not (uu____18779)))
in (match (uu____18778) with
| true -> begin
(encode_term_pred FStar_Pervasives_Native.None tt env2 vtok_tm)
end
| uu____18784 -> begin
(encode_term_pred FStar_Pervasives_Native.None t_norm env2 vtok_tm)
end)))
in (match (uu____18771) with
| (tok_typing, decls2) -> begin
(

let tok_typing1 = (match (formals) with
| (uu____18794)::uu____18795 -> begin
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

let uu____18835 = (

let uu____18846 = (FStar_SMTEncoding_Term.mk_NoHoist f tok_typing)
in ((((vtok_app_l)::[])::((vtok_app_r)::[])::[]), ((ff)::[]), (uu____18846)))
in (FStar_SMTEncoding_Util.mkForall uu____18835))
in (FStar_SMTEncoding_Util.mkAssume ((guarded_tok_typing), (FStar_Pervasives_Native.Some ("function token typing")), ((Prims.strcat "function_token_typing_" vname)))))))))
end
| uu____18865 -> begin
(FStar_SMTEncoding_Util.mkAssume ((tok_typing), (FStar_Pervasives_Native.Some ("function token typing")), ((Prims.strcat "function_token_typing_" vname))))
end)
in (

let uu____18872 = (match (formals) with
| [] -> begin
(

let uu____18889 = (

let uu____18890 = (

let uu____18893 = (FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left (fun _0_18 -> FStar_Pervasives_Native.Some (_0_18)) uu____18893))
in (replace_free_var env1 lid arity vname uu____18890))
in (((FStar_List.append decls2 ((tok_typing1)::[]))), (uu____18889)))
end
| uu____18902 -> begin
(

let vtok_decl = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let name_tok_corr = (

let uu____18913 = (

let uu____18920 = (

let uu____18921 = (

let uu____18932 = (FStar_SMTEncoding_Util.mkEq ((vtok_app), (vapp)))
in ((((vtok_app)::[])::((vapp)::[])::[]), (vars), (uu____18932)))
in (FStar_SMTEncoding_Util.mkForall uu____18921))
in ((uu____18920), (FStar_Pervasives_Native.Some ("Name-token correspondence")), ((Prims.strcat "token_correspondence_" vname))))
in (FStar_SMTEncoding_Util.mkAssume uu____18913))
in (((FStar_List.append decls2 ((vtok_decl)::(name_tok_corr)::(tok_typing1)::[]))), (env1))))
end)
in (match (uu____18872) with
| (tok_decl, env2) -> begin
(((vname_decl)::tok_decl), (env2))
end)))
end)))
in (match (uu____18729) with
| (decls2, env2) -> begin
(

let uu____18971 = (

let res_t1 = (FStar_Syntax_Subst.compress res_t)
in (

let uu____18979 = (encode_term res_t1 env')
in (match (uu____18979) with
| (encoded_res_t, decls) -> begin
(

let uu____18992 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in ((encoded_res_t), (uu____18992), (decls)))
end)))
in (match (uu____18971) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (

let uu____19003 = (

let uu____19010 = (

let uu____19011 = (

let uu____19022 = (FStar_SMTEncoding_Util.mkImp ((guard), (ty_pred)))
in ((((vapp)::[])::[]), (vars), (uu____19022)))
in (FStar_SMTEncoding_Util.mkForall uu____19011))
in ((uu____19010), (FStar_Pervasives_Native.Some ("free var typing")), ((Prims.strcat "typing_" vname))))
in (FStar_SMTEncoding_Util.mkAssume uu____19003))
in (

let freshness = (

let uu____19034 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New))
in (match (uu____19034) with
| true -> begin
(

let uu____19039 = (

let uu____19040 = (

let uu____19051 = (FStar_All.pipe_right vars (FStar_List.map FStar_Pervasives_Native.snd))
in (

let uu____19062 = (varops.next_id ())
in ((vname), (uu____19051), (FStar_SMTEncoding_Term.Term_sort), (uu____19062))))
in (FStar_SMTEncoding_Term.fresh_constructor uu____19040))
in (

let uu____19065 = (

let uu____19068 = (pretype_axiom env2 vapp vars)
in (uu____19068)::[])
in (uu____19039)::uu____19065))
end
| uu____19069 -> begin
[]
end))
in (

let g = (

let uu____19073 = (

let uu____19076 = (

let uu____19079 = (

let uu____19082 = (

let uu____19085 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::uu____19085)
in (FStar_List.append freshness uu____19082))
in (FStar_List.append decls3 uu____19079))
in (FStar_List.append decls2 uu____19076))
in (FStar_List.append decls11 uu____19073))
in ((g), (env2)))))
end))
end))))
end))
end))))
end)))
end)))
end))
end))))


let declare_top_level_let : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  (fvar_binding * FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env x t t_norm -> (

let uu____19118 = (try_lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____19118) with
| FStar_Pervasives_Native.None -> begin
(

let uu____19129 = (encode_free_var false env x t t_norm [])
in (match (uu____19129) with
| (decls, env1) -> begin
(

let fvb = (lookup_lid env1 x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in ((fvb), (decls), (env1)))
end))
end
| FStar_Pervasives_Native.Some (fvb) -> begin
((fvb), ([]), (env))
end)))


let encode_top_level_val : Prims.bool  ->  env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun uninterpreted env lid t quals -> (

let tt = (norm env t)
in (

let uu____19192 = (encode_free_var uninterpreted env lid t tt quals)
in (match (uu____19192) with
| (decls, env1) -> begin
(

let uu____19211 = (FStar_Syntax_Util.is_smt_lemma t)
in (match (uu____19211) with
| true -> begin
(

let uu____19218 = (

let uu____19221 = (encode_smt_lemma env1 lid tt)
in (FStar_List.append decls uu____19221))
in ((uu____19218), (env1)))
end
| uu____19226 -> begin
((decls), (env1))
end))
end))))


let encode_top_level_vals : env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____19279 lb -> (match (uu____19279) with
| (decls, env1) -> begin
(

let uu____19299 = (

let uu____19306 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val false env1 uu____19306 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (uu____19299) with
| (decls', env2) -> begin
(((FStar_List.append decls decls')), (env2))
end))
end)) (([]), (env)))))


let is_tactic : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let fstar_tactics_tactic_lid = (FStar_Parser_Const.p2l (("FStar")::("Tactics")::("tactic")::[]))
in (

let uu____19329 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____19329) with
| (hd1, args) -> begin
(

let uu____19366 = (

let uu____19367 = (FStar_Syntax_Util.un_uinst hd1)
in uu____19367.FStar_Syntax_Syntax.n)
in (match (uu____19366) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____19371, c) -> begin
(

let effect_name = (FStar_Syntax_Util.comp_effect_name c)
in (FStar_Util.starts_with "FStar.Tactics" effect_name.FStar_Ident.str))
end
| uu____19390 -> begin
false
end))
end))))


let encode_top_level_let : env_t  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env uu____19418 quals -> (match (uu____19418) with
| (is_rec, bindings) -> begin
(

let eta_expand1 = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let uu____19506 = (FStar_Util.first_N nbinders formals)
in (match (uu____19506) with
| (formals1, extra_formals) -> begin
(

let subst1 = (FStar_List.map2 (fun uu____19587 uu____19588 -> (match (((uu____19587), (uu____19588))) with
| ((formal, uu____19606), (binder, uu____19608)) -> begin
(

let uu____19617 = (

let uu____19624 = (FStar_Syntax_Syntax.bv_to_name binder)
in ((formal), (uu____19624)))
in FStar_Syntax_Syntax.NT (uu____19617))
end)) formals1 binders)
in (

let extra_formals1 = (

let uu____19636 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun uu____19667 -> (match (uu____19667) with
| (x, i) -> begin
(

let uu____19678 = (

let uu___124_19679 = x
in (

let uu____19680 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___124_19679.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___124_19679.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____19680}))
in ((uu____19678), (i)))
end))))
in (FStar_All.pipe_right uu____19636 FStar_Syntax_Util.name_binders))
in (

let body1 = (

let uu____19698 = (

let uu____19703 = (FStar_Syntax_Subst.compress body)
in (

let uu____19704 = (

let uu____19705 = (FStar_Syntax_Util.args_of_binders extra_formals1)
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____19705))
in (FStar_Syntax_Syntax.extend_app_n uu____19703 uu____19704)))
in (uu____19698 FStar_Pervasives_Native.None body.FStar_Syntax_Syntax.pos))
in (((FStar_List.append binders extra_formals1)), (body1)))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (

let get_result_type = (fun c -> (

let uu____19776 = (FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c)
in (match (uu____19776) with
| true -> begin
(FStar_TypeChecker_Env.reify_comp (

let uu___125_19781 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___125_19781.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___125_19781.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___125_19781.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___125_19781.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___125_19781.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___125_19781.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___125_19781.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___125_19781.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___125_19781.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___125_19781.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___125_19781.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___125_19781.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___125_19781.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___125_19781.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___125_19781.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___125_19781.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___125_19781.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___125_19781.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___125_19781.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___125_19781.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___125_19781.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___125_19781.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___125_19781.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___125_19781.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___125_19781.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___125_19781.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___125_19781.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___125_19781.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___125_19781.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___125_19781.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___125_19781.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___125_19781.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___125_19781.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___125_19781.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___125_19781.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___125_19781.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___125_19781.FStar_TypeChecker_Env.dep_graph}) c FStar_Syntax_Syntax.U_unknown)
end
| uu____19782 -> begin
(FStar_Syntax_Util.comp_result c)
end)))
in (

let rec aux = (fun norm1 t_norm1 -> (

let uu____19808 = (FStar_Syntax_Util.abs_formals e)
in (match (uu____19808) with
| (binders, body, lopt) -> begin
(match (binders) with
| (uu____19852)::uu____19853 -> begin
(

let uu____19868 = (

let uu____19869 = (

let uu____19872 = (FStar_Syntax_Subst.compress t_norm1)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____19872))
in uu____19869.FStar_Syntax_Syntax.n)
in (match (uu____19868) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____19905 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____19905) with
| (formals1, c1) -> begin
(

let nformals = (FStar_List.length formals1)
in (

let nbinders = (FStar_List.length binders)
in (

let tres = (get_result_type c1)
in (

let uu____19939 = ((nformals < nbinders) && (FStar_Syntax_Util.is_total_comp c1))
in (match (uu____19939) with
| true -> begin
(

let uu____19964 = (FStar_Util.first_N nformals binders)
in (match (uu____19964) with
| (bs0, rest) -> begin
(

let c2 = (

let subst1 = (FStar_List.map2 (fun uu____20048 uu____20049 -> (match (((uu____20048), (uu____20049))) with
| ((x, uu____20067), (b, uu____20069)) -> begin
(

let uu____20078 = (

let uu____20085 = (FStar_Syntax_Syntax.bv_to_name b)
in ((x), (uu____20085)))
in FStar_Syntax_Syntax.NT (uu____20078))
end)) formals1 bs0)
in (FStar_Syntax_Subst.subst_comp subst1 c1))
in (

let body1 = (FStar_Syntax_Util.abs rest body lopt)
in (

let uu____20093 = (

let uu____20118 = (get_result_type c2)
in ((bs0), (body1), (bs0), (uu____20118)))
in ((uu____20093), (false)))))
end))
end
| uu____20161 -> begin
(match ((nformals > nbinders)) with
| true -> begin
(

let uu____20186 = (eta_expand1 binders formals1 body tres)
in (match (uu____20186) with
| (binders1, body1) -> begin
((((binders1), (body1), (formals1), (tres))), (false))
end))
end
| uu____20259 -> begin
((((binders), (body), (formals1), (tres))), (false))
end)
end)))))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____20273) -> begin
(

let uu____20278 = (

let uu____20289 = (aux norm1 x.FStar_Syntax_Syntax.sort)
in (FStar_Pervasives_Native.fst uu____20289))
in ((uu____20278), (true)))
end
| uu____20324 when (not (norm1)) -> begin
(

let t_norm2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm1)
in (aux true t_norm2))
end
| uu____20326 -> begin
(

let uu____20327 = (

let uu____20328 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____20329 = (FStar_Syntax_Print.term_to_string t_norm1)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str uu____20328 uu____20329)))
in (failwith uu____20327))
end))
end
| uu____20344 -> begin
(

let rec aux' = (fun t_norm2 -> (

let uu____20377 = (

let uu____20378 = (FStar_Syntax_Subst.compress t_norm2)
in uu____20378.FStar_Syntax_Syntax.n)
in (match (uu____20377) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____20425 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____20425) with
| (formals1, c1) -> begin
(

let tres = (get_result_type c1)
in (

let uu____20461 = (eta_expand1 [] formals1 e tres)
in (match (uu____20461) with
| (binders1, body1) -> begin
((((binders1), (body1), (formals1), (tres))), (false))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (bv, uu____20551) -> begin
(aux' bv.FStar_Syntax_Syntax.sort)
end
| uu____20556 -> begin
(((([]), (e), ([]), (t_norm2))), (false))
end)))
in (aux' t_norm1))
end)
end)))
in (aux false t_norm))))
in (FStar_All.try_with (fun uu___127_20609 -> (match (()) with
| () -> begin
(

let uu____20616 = (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> ((FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))))
in (match (uu____20616) with
| true -> begin
(encode_top_level_vals env bindings quals)
end
| uu____20627 -> begin
(

let uu____20628 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____20691 lb -> (match (uu____20691) with
| (toks, typs, decls, env1) -> begin
((

let uu____20746 = (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp)
in (match (uu____20746) with
| true -> begin
(FStar_Exn.raise Let_rec_unencodeable)
end
| uu____20747 -> begin
()
end));
(

let t_norm = (whnf env1 lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____20749 = (

let uu____20758 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env1 uu____20758 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (uu____20749) with
| (tok, decl, env2) -> begin
(((tok)::toks), ((t_norm)::typs), ((decl)::decls), (env2))
end)));
)
end)) (([]), ([]), ([]), (env))))
in (match (uu____20628) with
| (toks, typs, decls, env1) -> begin
(

let toks_fvbs = (FStar_List.rev toks)
in (

let decls1 = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (

let typs1 = (FStar_List.rev typs)
in (

let mk_app1 = (fun rng curry fvb vars -> (

let mk_fv = (fun uu____20883 -> (match ((Prims.op_Equality fvb.smt_arity (Prims.parse_int "0"))) with
| true -> begin
(FStar_SMTEncoding_Util.mkFreeV ((fvb.smt_id), (FStar_SMTEncoding_Term.Term_sort)))
end
| uu____20884 -> begin
(raise_arity_mismatch fvb.smt_id fvb.smt_arity (Prims.parse_int "0") rng)
end))
in (match (vars) with
| [] -> begin
(mk_fv ())
end
| uu____20889 -> begin
(match (curry) with
| true -> begin
(match (fvb.smt_token) with
| FStar_Pervasives_Native.Some (ftok) -> begin
(mk_Apply ftok vars)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____20897 = (mk_fv ())
in (mk_Apply uu____20897 vars))
end)
end
| uu____20898 -> begin
(

let uu____20899 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (maybe_curry_app rng (FStar_SMTEncoding_Term.Var (fvb.smt_id)) fvb.smt_arity uu____20899))
end)
end)))
in (

let encode_non_rec_lbdef = (fun bindings1 typs2 toks1 env2 -> (match (((bindings1), (typs2), (toks1))) with
| (({FStar_Syntax_Syntax.lbname = lbn; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____20959; FStar_Syntax_Syntax.lbeff = uu____20960; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = uu____20962; FStar_Syntax_Syntax.lbpos = uu____20963})::[], (t_norm)::[], (fvb)::[]) -> begin
(

let flid = fvb.fvar_lid
in (

let uu____20987 = (

let uu____20994 = (FStar_TypeChecker_Env.open_universes_in env2.tcenv uvs ((e)::(t_norm)::[]))
in (match (uu____20994) with
| (tcenv', uu____21010, e_t) -> begin
(

let uu____21016 = (match (e_t) with
| (e1)::(t_norm1)::[] -> begin
((e1), (t_norm1))
end
| uu____21027 -> begin
(failwith "Impossible")
end)
in (match (uu____21016) with
| (e1, t_norm1) -> begin
(((

let uu___128_21043 = env2
in {bindings = uu___128_21043.bindings; depth = uu___128_21043.depth; tcenv = tcenv'; warn = uu___128_21043.warn; cache = uu___128_21043.cache; nolabels = uu___128_21043.nolabels; use_zfuel_name = uu___128_21043.use_zfuel_name; encode_non_total_function_typ = uu___128_21043.encode_non_total_function_typ; current_module_name = uu___128_21043.current_module_name})), (e1), (t_norm1))
end))
end))
in (match (uu____20987) with
| (env', e1, t_norm1) -> begin
(

let uu____21053 = (destruct_bound_function flid t_norm1 e1)
in (match (uu____21053) with
| ((binders, body, uu____21074, t_body), curry) -> begin
((

let uu____21086 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____21086) with
| true -> begin
(

let uu____21087 = (FStar_Syntax_Print.binders_to_string ", " binders)
in (

let uu____21088 = (FStar_Syntax_Print.term_to_string body)
in (FStar_Util.print2 "Encoding let : binders=[%s], body=%s\n" uu____21087 uu____21088)))
end
| uu____21089 -> begin
()
end));
(

let uu____21090 = (encode_binders FStar_Pervasives_Native.None binders env')
in (match (uu____21090) with
| (vars, guards, env'1, binder_decls, uu____21117) -> begin
(

let body1 = (

let uu____21131 = (FStar_TypeChecker_Env.is_reifiable_function env'1.tcenv t_norm1)
in (match (uu____21131) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env'1.tcenv body)
end
| uu____21132 -> begin
(FStar_Syntax_Util.ascribe body ((FStar_Util.Inl (t_body)), (FStar_Pervasives_Native.None)))
end))
in (

let app = (

let uu____21150 = (FStar_Syntax_Util.range_of_lbname lbn)
in (mk_app1 uu____21150 curry fvb vars))
in (

let uu____21151 = (

let uu____21160 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic))
in (match (uu____21160) with
| true -> begin
(

let uu____21171 = (FStar_SMTEncoding_Term.mk_Valid app)
in (

let uu____21172 = (encode_formula body1 env'1)
in ((uu____21171), (uu____21172))))
end
| uu____21181 -> begin
(

let uu____21182 = (encode_term body1 env'1)
in ((app), (uu____21182)))
end))
in (match (uu____21151) with
| (app1, (body2, decls2)) -> begin
(

let eqn = (

let uu____21205 = (

let uu____21212 = (

let uu____21213 = (

let uu____21224 = (FStar_SMTEncoding_Util.mkEq ((app1), (body2)))
in ((((app1)::[])::[]), (vars), (uu____21224)))
in (FStar_SMTEncoding_Util.mkForall uu____21213))
in (

let uu____21233 = (

let uu____21234 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in FStar_Pervasives_Native.Some (uu____21234))
in ((uu____21212), (uu____21233), ((Prims.strcat "equation_" fvb.smt_id)))))
in (FStar_SMTEncoding_Util.mkAssume uu____21205))
in (

let uu____21235 = (

let uu____21238 = (

let uu____21241 = (

let uu____21244 = (

let uu____21247 = (primitive_type_axioms env2.tcenv flid fvb.smt_id app1)
in (FStar_List.append ((eqn)::[]) uu____21247))
in (FStar_List.append decls2 uu____21244))
in (FStar_List.append binder_decls uu____21241))
in (FStar_List.append decls1 uu____21238))
in ((uu____21235), (env2))))
end))))
end));
)
end))
end)))
end
| uu____21252 -> begin
(failwith "Impossible")
end))
in (

let encode_rec_lbdefs = (fun bindings1 typs2 toks1 env2 -> (

let fuel = (

let uu____21315 = (varops.fresh "fuel")
in ((uu____21315), (FStar_SMTEncoding_Term.Fuel_sort)))
in (

let fuel_tm = (FStar_SMTEncoding_Util.mkFreeV fuel)
in (

let env0 = env2
in (

let uu____21318 = (FStar_All.pipe_right toks1 (FStar_List.fold_left (fun uu____21365 fvb -> (match (uu____21365) with
| (gtoks, env3) -> begin
(

let flid = fvb.fvar_lid
in (

let g = (

let uu____21411 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented")
in (varops.new_fvar uu____21411))
in (

let gtok = (

let uu____21413 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented_token")
in (varops.new_fvar uu____21413))
in (

let env4 = (

let uu____21415 = (

let uu____21418 = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::[])))
in (FStar_All.pipe_left (fun _0_19 -> FStar_Pervasives_Native.Some (_0_19)) uu____21418))
in (push_free_var env3 flid fvb.smt_arity gtok uu____21415))
in (((((fvb), (g), (gtok)))::gtoks), (env4))))))
end)) (([]), (env2))))
in (match (uu____21318) with
| (gtoks, env3) -> begin
(

let gtoks1 = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env01 uu____21524 t_norm uu____21526 -> (match (((uu____21524), (uu____21526))) with
| ((fvb, g, gtok), {FStar_Syntax_Syntax.lbname = lbn; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____21554; FStar_Syntax_Syntax.lbeff = uu____21555; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = uu____21557; FStar_Syntax_Syntax.lbpos = uu____21558}) -> begin
(

let uu____21579 = (

let uu____21586 = (FStar_TypeChecker_Env.open_universes_in env3.tcenv uvs ((e)::(t_norm)::[]))
in (match (uu____21586) with
| (tcenv', uu____21602, e_t) -> begin
(

let uu____21608 = (match (e_t) with
| (e1)::(t_norm1)::[] -> begin
((e1), (t_norm1))
end
| uu____21619 -> begin
(failwith "Impossible")
end)
in (match (uu____21608) with
| (e1, t_norm1) -> begin
(((

let uu___129_21635 = env3
in {bindings = uu___129_21635.bindings; depth = uu___129_21635.depth; tcenv = tcenv'; warn = uu___129_21635.warn; cache = uu___129_21635.cache; nolabels = uu___129_21635.nolabels; use_zfuel_name = uu___129_21635.use_zfuel_name; encode_non_total_function_typ = uu___129_21635.encode_non_total_function_typ; current_module_name = uu___129_21635.current_module_name})), (e1), (t_norm1))
end))
end))
in (match (uu____21579) with
| (env', e1, t_norm1) -> begin
((

let uu____21650 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env01.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____21650) with
| true -> begin
(

let uu____21651 = (FStar_Syntax_Print.lbname_to_string lbn)
in (

let uu____21652 = (FStar_Syntax_Print.term_to_string t_norm1)
in (

let uu____21653 = (FStar_Syntax_Print.term_to_string e1)
in (FStar_Util.print3 "Encoding let rec %s : %s = %s\n" uu____21651 uu____21652 uu____21653))))
end
| uu____21654 -> begin
()
end));
(

let uu____21655 = (destruct_bound_function fvb.fvar_lid t_norm1 e1)
in (match (uu____21655) with
| ((binders, body, formals, tres), curry) -> begin
((

let uu____21692 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env01.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____21692) with
| true -> begin
(

let uu____21693 = (FStar_Syntax_Print.binders_to_string ", " binders)
in (

let uu____21694 = (FStar_Syntax_Print.term_to_string body)
in (

let uu____21695 = (FStar_Syntax_Print.binders_to_string ", " formals)
in (

let uu____21696 = (FStar_Syntax_Print.term_to_string tres)
in (FStar_Util.print4 "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n" uu____21693 uu____21694 uu____21695 uu____21696)))))
end
| uu____21697 -> begin
()
end));
(match (curry) with
| true -> begin
(failwith "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type")
end
| uu____21699 -> begin
()
end);
(

let uu____21700 = (encode_binders FStar_Pervasives_Native.None binders env')
in (match (uu____21700) with
| (vars, guards, env'1, binder_decls, uu____21731) -> begin
(

let decl_g = (

let uu____21745 = (

let uu____21756 = (

let uu____21759 = (FStar_List.map FStar_Pervasives_Native.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::uu____21759)
in ((g), (uu____21756), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Fuel-instrumented function name"))))
in FStar_SMTEncoding_Term.DeclFun (uu____21745))
in (

let env02 = (push_zfuel_name env01 fvb.fvar_lid g)
in (

let decl_g_tok = FStar_SMTEncoding_Term.DeclFun (((gtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Token for fuel-instrumented partial applications"))))
in (

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let app = (

let uu____21772 = (

let uu____21779 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((fvb.smt_id), (uu____21779)))
in (FStar_SMTEncoding_Util.mkApp uu____21772))
in (

let gsapp = (

let uu____21785 = (

let uu____21792 = (

let uu____21795 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (uu____21795)::vars_tm)
in ((g), (uu____21792)))
in (FStar_SMTEncoding_Util.mkApp uu____21785))
in (

let gmax = (

let uu____21801 = (

let uu____21808 = (

let uu____21811 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (uu____21811)::vars_tm)
in ((g), (uu____21808)))
in (FStar_SMTEncoding_Util.mkApp uu____21801))
in (

let body1 = (

let uu____21817 = (FStar_TypeChecker_Env.is_reifiable_function env'1.tcenv t_norm1)
in (match (uu____21817) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env'1.tcenv body)
end
| uu____21818 -> begin
body
end))
in (

let uu____21819 = (encode_term body1 env'1)
in (match (uu____21819) with
| (body_tm, decls2) -> begin
(

let eqn_g = (

let uu____21837 = (

let uu____21844 = (

let uu____21845 = (

let uu____21860 = (FStar_SMTEncoding_Util.mkEq ((gsapp), (body_tm)))
in ((((gsapp)::[])::[]), (FStar_Pervasives_Native.Some ((Prims.parse_int "0"))), ((fuel)::vars), (uu____21860)))
in (FStar_SMTEncoding_Util.mkForall' uu____21845))
in (

let uu____21871 = (

let uu____21872 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" fvb.fvar_lid.FStar_Ident.str)
in FStar_Pervasives_Native.Some (uu____21872))
in ((uu____21844), (uu____21871), ((Prims.strcat "equation_with_fuel_" g)))))
in (FStar_SMTEncoding_Util.mkAssume uu____21837))
in (

let eqn_f = (

let uu____21874 = (

let uu____21881 = (

let uu____21882 = (

let uu____21893 = (FStar_SMTEncoding_Util.mkEq ((app), (gmax)))
in ((((app)::[])::[]), (vars), (uu____21893)))
in (FStar_SMTEncoding_Util.mkForall uu____21882))
in ((uu____21881), (FStar_Pervasives_Native.Some ("Correspondence of recursive function to instrumented version")), ((Prims.strcat "@fuel_correspondence_" g))))
in (FStar_SMTEncoding_Util.mkAssume uu____21874))
in (

let eqn_g' = (

let uu____21903 = (

let uu____21910 = (

let uu____21911 = (

let uu____21922 = (

let uu____21923 = (

let uu____21928 = (

let uu____21929 = (

let uu____21936 = (

let uu____21939 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "0"))
in (uu____21939)::vars_tm)
in ((g), (uu____21936)))
in (FStar_SMTEncoding_Util.mkApp uu____21929))
in ((gsapp), (uu____21928)))
in (FStar_SMTEncoding_Util.mkEq uu____21923))
in ((((gsapp)::[])::[]), ((fuel)::vars), (uu____21922)))
in (FStar_SMTEncoding_Util.mkForall uu____21911))
in ((uu____21910), (FStar_Pervasives_Native.Some ("Fuel irrelevance")), ((Prims.strcat "@fuel_irrelevance_" g))))
in (FStar_SMTEncoding_Util.mkAssume uu____21903))
in (

let uu____21950 = (

let uu____21959 = (encode_binders FStar_Pervasives_Native.None formals env02)
in (match (uu____21959) with
| (vars1, v_guards, env4, binder_decls1, uu____21988) -> begin
(

let vars_tm1 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars1)
in (

let gapp = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::vars_tm1)))
in (

let tok_corr = (

let tok_app = (

let uu____22009 = (FStar_SMTEncoding_Util.mkFreeV ((gtok), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply uu____22009 ((fuel)::vars1)))
in (

let uu____22010 = (

let uu____22017 = (

let uu____22018 = (

let uu____22029 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (gapp)))
in ((((tok_app)::[])::[]), ((fuel)::vars1), (uu____22029)))
in (FStar_SMTEncoding_Util.mkForall uu____22018))
in ((uu____22017), (FStar_Pervasives_Native.Some ("Fuel token correspondence")), ((Prims.strcat "fuel_token_correspondence_" gtok))))
in (FStar_SMTEncoding_Util.mkAssume uu____22010)))
in (

let uu____22038 = (

let uu____22045 = (encode_term_pred FStar_Pervasives_Native.None tres env4 gapp)
in (match (uu____22045) with
| (g_typing, d3) -> begin
(

let uu____22058 = (

let uu____22061 = (

let uu____22062 = (

let uu____22069 = (

let uu____22070 = (

let uu____22081 = (

let uu____22082 = (

let uu____22087 = (FStar_SMTEncoding_Util.mk_and_l v_guards)
in ((uu____22087), (g_typing)))
in (FStar_SMTEncoding_Util.mkImp uu____22082))
in ((((gapp)::[])::[]), ((fuel)::vars1), (uu____22081)))
in (FStar_SMTEncoding_Util.mkForall uu____22070))
in ((uu____22069), (FStar_Pervasives_Native.Some ("Typing correspondence of token to term")), ((Prims.strcat "token_correspondence_" g))))
in (FStar_SMTEncoding_Util.mkAssume uu____22062))
in (uu____22061)::[])
in ((d3), (uu____22058)))
end))
in (match (uu____22038) with
| (aux_decls, typing_corr) -> begin
(((FStar_List.append binder_decls1 aux_decls)), ((FStar_List.append typing_corr ((tok_corr)::[]))))
end)))))
end))
in (match (uu____21950) with
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

let uu____22140 = (

let uu____22153 = (FStar_List.zip3 gtoks1 typs2 bindings1)
in (FStar_List.fold_left (fun uu____22210 uu____22211 -> (match (((uu____22210), (uu____22211))) with
| ((decls2, eqns, env01), (gtok, ty, lb)) -> begin
(

let uu____22326 = (encode_one_binding env01 gtok ty lb)
in (match (uu____22326) with
| (decls', eqns', env02) -> begin
(((decls')::decls2), ((FStar_List.append eqns' eqns)), (env02))
end))
end)) (((decls1)::[]), ([]), (env0)) uu____22153))
in (match (uu____22140) with
| (decls2, eqns, env01) -> begin
(

let uu____22399 = (

let isDeclFun = (fun uu___97_22413 -> (match (uu___97_22413) with
| FStar_SMTEncoding_Term.DeclFun (uu____22414) -> begin
true
end
| uu____22425 -> begin
false
end))
in (

let uu____22426 = (FStar_All.pipe_right decls2 FStar_List.flatten)
in (FStar_All.pipe_right uu____22426 (FStar_List.partition isDeclFun))))
in (match (uu____22399) with
| (prefix_decls, rest) -> begin
(

let eqns1 = (FStar_List.rev eqns)
in (((FStar_List.append prefix_decls (FStar_List.append rest eqns1))), (env01)))
end))
end))))
end))))))
in (

let uu____22466 = ((FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___98_22470 -> (match (uu___98_22470) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| uu____22471 -> begin
false
end)))) || (FStar_All.pipe_right typs1 (FStar_Util.for_some (fun t -> (

let uu____22477 = ((FStar_Syntax_Util.is_pure_or_ghost_function t) || (FStar_TypeChecker_Env.is_reifiable_function env1.tcenv t))
in (FStar_All.pipe_left Prims.op_Negation uu____22477))))))
in (match (uu____22466) with
| true -> begin
((decls1), (env1))
end
| uu____22486 -> begin
(FStar_All.try_with (fun uu___131_22494 -> (match (()) with
| () -> begin
(match ((not (is_rec))) with
| true -> begin
(encode_non_rec_lbdef bindings typs1 toks_fvbs env1)
end
| uu____22507 -> begin
(encode_rec_lbdefs bindings typs1 toks_fvbs env1)
end)
end)) (fun uu___130_22509 -> (match (uu___130_22509) with
| Inner_let_rec -> begin
((decls1), (env1))
end)))
end))))))))
end))
end))
end)) (fun uu___126_22521 -> (match (uu___126_22521) with
| Let_rec_unencodeable -> begin
(

let msg = (

let uu____22529 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right uu____22529 (FStar_String.concat " and ")))
in (

let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in (((decl)::[]), (env))))
end)))))
end))


let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let nm = (

let uu____22590 = (FStar_Syntax_Util.lid_of_sigelt se)
in (match (uu____22590) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (l) -> begin
l.FStar_Ident.str
end))
in (

let uu____22594 = (encode_sigelt' env se)
in (match (uu____22594) with
| (g, env1) -> begin
(

let g1 = (match (g) with
| [] -> begin
(

let uu____22610 = (

let uu____22611 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (uu____22611))
in (uu____22610)::[])
end
| uu____22612 -> begin
(

let uu____22613 = (

let uu____22616 = (

let uu____22617 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____22617))
in (uu____22616)::g)
in (

let uu____22618 = (

let uu____22621 = (

let uu____22622 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____22622))
in (uu____22621)::[])
in (FStar_List.append uu____22613 uu____22618)))
end)
in ((g1), (env1)))
end))))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let is_opaque_to_smt = (fun t -> (

let uu____22635 = (

let uu____22636 = (FStar_Syntax_Subst.compress t)
in uu____22636.FStar_Syntax_Syntax.n)
in (match (uu____22635) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____22640)) -> begin
(Prims.op_Equality s "opaque_to_smt")
end
| uu____22641 -> begin
false
end)))
in (

let is_uninterpreted_by_smt = (fun t -> (

let uu____22648 = (

let uu____22649 = (FStar_Syntax_Subst.compress t)
in uu____22649.FStar_Syntax_Syntax.n)
in (match (uu____22648) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____22653)) -> begin
(Prims.op_Equality s "uninterpreted_by_smt")
end
| uu____22654 -> begin
false
end)))
in (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____22659) -> begin
(failwith "impossible -- new_effect_for_free should have been removed by Tc.fs")
end
| FStar_Syntax_Syntax.Sig_splice (uu____22664) -> begin
(failwith "impossible -- splice should have been removed by Tc.fs")
end
| FStar_Syntax_Syntax.Sig_pragma (uu____22675) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_main (uu____22676) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____22677) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____22690) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(

let uu____22692 = (

let uu____22693 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right uu____22693 Prims.op_Negation))
in (match (uu____22692) with
| true -> begin
(([]), (env))
end
| uu____22700 -> begin
(

let close_effect_params = (fun tm -> (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
tm
end
| uu____22719 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((ed.FStar_Syntax_Syntax.binders), (tm), (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[]))))))) FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)
end))
in (

let encode_action = (fun env1 a -> (

let uu____22749 = (FStar_Syntax_Util.arrow_formals_comp a.FStar_Syntax_Syntax.action_typ)
in (match (uu____22749) with
| (formals, uu____22767) -> begin
(

let arity = (FStar_List.length formals)
in (

let uu____22785 = (new_term_constant_and_tok_from_lid env1 a.FStar_Syntax_Syntax.action_name arity)
in (match (uu____22785) with
| (aname, atok, env2) -> begin
(

let uu____22805 = (

let uu____22810 = (close_effect_params a.FStar_Syntax_Syntax.action_defn)
in (encode_term uu____22810 env2))
in (match (uu____22805) with
| (tm, decls) -> begin
(

let a_decls = (

let uu____22822 = (

let uu____22823 = (

let uu____22834 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____22850 -> FStar_SMTEncoding_Term.Term_sort)))
in ((aname), (uu____22834), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Action"))))
in FStar_SMTEncoding_Term.DeclFun (uu____22823))
in (uu____22822)::(FStar_SMTEncoding_Term.DeclFun (((atok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Action token")))))::[])
in (

let uu____22859 = (

let aux = (fun uu____22915 uu____22916 -> (match (((uu____22915), (uu____22916))) with
| ((bv, uu____22968), (env3, acc_sorts, acc)) -> begin
(

let uu____23006 = (gen_term_var env3 bv)
in (match (uu____23006) with
| (xxsym, xx, env4) -> begin
((env4), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::acc_sorts), ((xx)::acc))
end))
end))
in (FStar_List.fold_right aux formals ((env2), ([]), ([]))))
in (match (uu____22859) with
| (uu____23078, xs_sorts, xs) -> begin
(

let app = (FStar_SMTEncoding_Util.mkApp ((aname), (xs)))
in (

let a_eq = (

let uu____23101 = (

let uu____23108 = (

let uu____23109 = (

let uu____23120 = (

let uu____23121 = (

let uu____23126 = (mk_Apply tm xs_sorts)
in ((app), (uu____23126)))
in (FStar_SMTEncoding_Util.mkEq uu____23121))
in ((((app)::[])::[]), (xs_sorts), (uu____23120)))
in (FStar_SMTEncoding_Util.mkForall uu____23109))
in ((uu____23108), (FStar_Pervasives_Native.Some ("Action equality")), ((Prims.strcat aname "_equality"))))
in (FStar_SMTEncoding_Util.mkAssume uu____23101))
in (

let tok_correspondence = (

let tok_term = (FStar_SMTEncoding_Util.mkFreeV ((atok), (FStar_SMTEncoding_Term.Term_sort)))
in (

let tok_app = (mk_Apply tok_term xs_sorts)
in (

let uu____23138 = (

let uu____23145 = (

let uu____23146 = (

let uu____23157 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (app)))
in ((((tok_app)::[])::[]), (xs_sorts), (uu____23157)))
in (FStar_SMTEncoding_Util.mkForall uu____23146))
in ((uu____23145), (FStar_Pervasives_Native.Some ("Action token correspondence")), ((Prims.strcat aname "_token_correspondence"))))
in (FStar_SMTEncoding_Util.mkAssume uu____23138))))
in ((env2), ((FStar_List.append decls (FStar_List.append a_decls ((a_eq)::(tok_correspondence)::[]))))))))
end)))
end))
end)))
end)))
in (

let uu____23168 = (FStar_Util.fold_map encode_action env ed.FStar_Syntax_Syntax.actions)
in (match (uu____23168) with
| (env1, decls2) -> begin
(((FStar_List.flatten decls2)), (env1))
end))))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____23194, uu____23195) when (FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid) -> begin
(

let uu____23196 = (new_term_constant_and_tok_from_lid env lid (Prims.parse_int "4"))
in (match (uu____23196) with
| (tname, ttok, env1) -> begin
(([]), (env1))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____23211, t) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let will_encode_definition = (

let uu____23217 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___99_23221 -> (match (uu___99_23221) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.Projector (uu____23222) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____23227) -> begin
true
end
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| uu____23228 -> begin
false
end))))
in (not (uu____23217)))
in (match (will_encode_definition) with
| true -> begin
(([]), (env))
end
| uu____23233 -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____23235 = (

let uu____23242 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs (FStar_Util.for_some is_uninterpreted_by_smt))
in (encode_top_level_val uu____23242 env fv t quals))
in (match (uu____23235) with
| (decls, env1) -> begin
(

let tname = lid.FStar_Ident.str
in (

let tsym = (FStar_SMTEncoding_Util.mkFreeV ((tname), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____23257 = (

let uu____23258 = (primitive_type_axioms env1.tcenv lid tname tsym)
in (FStar_List.append decls uu____23258))
in ((uu____23257), (env1)))))
end)))
end)))
end
| FStar_Syntax_Syntax.Sig_assume (l, us, f) -> begin
(

let uu____23264 = (FStar_Syntax_Subst.open_univ_vars us f)
in (match (uu____23264) with
| (uu____23273, f1) -> begin
(

let uu____23275 = (encode_formula f1 env)
in (match (uu____23275) with
| (f2, decls) -> begin
(

let g = (

let uu____23289 = (

let uu____23290 = (

let uu____23297 = (

let uu____23298 = (

let uu____23299 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" uu____23299))
in FStar_Pervasives_Native.Some (uu____23298))
in (

let uu____23300 = (varops.mk_unique (Prims.strcat "assumption_" l.FStar_Ident.str))
in ((f2), (uu____23297), (uu____23300))))
in (FStar_SMTEncoding_Util.mkAssume uu____23290))
in (uu____23289)::[])
in (((FStar_List.append decls g)), (env)))
end))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____23302) when ((FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) || (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs (FStar_Util.for_some is_opaque_to_smt))) -> begin
(

let attrs = se.FStar_Syntax_Syntax.sigattrs
in (

let uu____23314 = (FStar_Util.fold_map (fun env1 lb -> (

let lid = (

let uu____23332 = (

let uu____23335 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____23335.FStar_Syntax_Syntax.fv_name)
in uu____23332.FStar_Syntax_Syntax.v)
in (

let uu____23336 = (

let uu____23337 = (FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone uu____23337))
in (match (uu____23336) with
| true -> begin
(

let val_decl = (

let uu___132_23365 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = uu___132_23365.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Irreducible)::se.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___132_23365.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___132_23365.FStar_Syntax_Syntax.sigattrs})
in (

let uu____23366 = (encode_sigelt' env1 val_decl)
in (match (uu____23366) with
| (decls, env2) -> begin
((env2), (decls))
end)))
end
| uu____23377 -> begin
((env1), ([]))
end)))) env (FStar_Pervasives_Native.snd lbs))
in (match (uu____23314) with
| (env1, decls) -> begin
(((FStar_List.flatten decls)), (env1))
end)))
end
| FStar_Syntax_Syntax.Sig_let ((uu____23390, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t1); FStar_Syntax_Syntax.lbunivs = uu____23392; FStar_Syntax_Syntax.lbtyp = uu____23393; FStar_Syntax_Syntax.lbeff = uu____23394; FStar_Syntax_Syntax.lbdef = uu____23395; FStar_Syntax_Syntax.lbattrs = uu____23396; FStar_Syntax_Syntax.lbpos = uu____23397})::[]), uu____23398) when (FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid) -> begin
(

let uu____23415 = (new_term_constant_and_tok_from_lid env b2t1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v (Prims.parse_int "1"))
in (match (uu____23415) with
| (tname, ttok, env1) -> begin
(

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let b2t_x = (FStar_SMTEncoding_Util.mkApp (("Prims.b2t"), ((x)::[])))
in (

let valid_b2t_x = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b2t_x)::[])))
in (

let decls = (

let uu____23444 = (

let uu____23447 = (

let uu____23448 = (

let uu____23455 = (

let uu____23456 = (

let uu____23467 = (

let uu____23468 = (

let uu____23473 = (FStar_SMTEncoding_Util.mkApp (((FStar_Pervasives_Native.snd FStar_SMTEncoding_Term.boxBoolFun)), ((x)::[])))
in ((valid_b2t_x), (uu____23473)))
in (FStar_SMTEncoding_Util.mkEq uu____23468))
in ((((b2t_x)::[])::[]), ((xx)::[]), (uu____23467)))
in (FStar_SMTEncoding_Util.mkForall uu____23456))
in ((uu____23455), (FStar_Pervasives_Native.Some ("b2t def")), ("b2t_def")))
in (FStar_SMTEncoding_Util.mkAssume uu____23448))
in (uu____23447)::[])
in (FStar_SMTEncoding_Term.DeclFun (((tname), ((FStar_SMTEncoding_Term.Term_sort)::[]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None))))::uu____23444)
in ((decls), (env1)))))))
end))
end
| FStar_Syntax_Syntax.Sig_let (uu____23494, uu____23495) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___100_23504 -> (match (uu___100_23504) with
| FStar_Syntax_Syntax.Discriminator (uu____23505) -> begin
true
end
| uu____23506 -> begin
false
end)))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let (uu____23507, lids) when ((FStar_All.pipe_right lids (FStar_Util.for_some (fun l -> (

let uu____23518 = (

let uu____23519 = (FStar_List.hd l.FStar_Ident.ns)
in uu____23519.FStar_Ident.idText)
in (Prims.op_Equality uu____23518 "Prims"))))) && (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___101_23523 -> (match (uu___101_23523) with
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
true
end
| uu____23524 -> begin
false
end))))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____23526) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___102_23537 -> (match (uu___102_23537) with
| FStar_Syntax_Syntax.Projector (uu____23538) -> begin
true
end
| uu____23543 -> begin
false
end)))) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____23546 = (try_lookup_free_var env l)
in (match (uu____23546) with
| FStar_Pervasives_Native.Some (uu____23553) -> begin
(([]), (env))
end
| FStar_Pervasives_Native.None -> begin
(

let se1 = (

let uu___133_23555 = se
in (

let uu____23556 = (FStar_Ident.range_of_lid l)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = uu____23556; FStar_Syntax_Syntax.sigquals = uu___133_23555.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___133_23555.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___133_23555.FStar_Syntax_Syntax.sigattrs}))
in (encode_sigelt env se1))
end))))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), uu____23559) -> begin
(encode_top_level_let env ((is_rec), (bindings)) se.FStar_Syntax_Syntax.sigquals)
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____23571) -> begin
(

let uu____23580 = (encode_sigelts env ses)
in (match (uu____23580) with
| (g, env1) -> begin
(

let uu____23597 = (FStar_All.pipe_right g (FStar_List.partition (fun uu___103_23620 -> (match (uu___103_23620) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.assumption_term = uu____23621; FStar_SMTEncoding_Term.assumption_caption = FStar_Pervasives_Native.Some ("inversion axiom"); FStar_SMTEncoding_Term.assumption_name = uu____23622; FStar_SMTEncoding_Term.assumption_fact_ids = uu____23623}) -> begin
false
end
| uu____23626 -> begin
true
end))))
in (match (uu____23597) with
| (g', inversions) -> begin
(

let uu____23641 = (FStar_All.pipe_right g' (FStar_List.partition (fun uu___104_23662 -> (match (uu___104_23662) with
| FStar_SMTEncoding_Term.DeclFun (uu____23663) -> begin
true
end
| uu____23674 -> begin
false
end))))
in (match (uu____23641) with
| (decls, rest) -> begin
(((FStar_List.append decls (FStar_List.append rest inversions))), (env1))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, uu____23690, tps, k, uu____23693, datas) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___105_23710 -> (match (uu___105_23710) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____23711 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> (match (is_logical) with
| true -> begin
(

let uu____23718 = c
in (match (uu____23718) with
| (name, args, uu____23721, uu____23722, uu____23723) -> begin
(

let uu____23728 = (

let uu____23729 = (

let uu____23740 = (FStar_All.pipe_right args (FStar_List.map (fun uu____23757 -> (match (uu____23757) with
| (uu____23764, sort, uu____23766) -> begin
sort
end))))
in ((name), (uu____23740), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____23729))
in (uu____23728)::[])
end))
end
| uu____23769 -> begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end))
in (

let inversion_axioms = (fun tapp vars -> (

let uu____23795 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (

let uu____23801 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right uu____23801 FStar_Option.isNone)))))
in (match (uu____23795) with
| true -> begin
[]
end
| uu____23832 -> begin
(

let uu____23833 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____23833) with
| (xxsym, xx) -> begin
(

let uu____23842 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun uu____23881 l -> (match (uu____23881) with
| (out, decls) -> begin
(

let uu____23901 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (uu____23901) with
| (uu____23912, data_t) -> begin
(

let uu____23914 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (uu____23914) with
| (args, res) -> begin
(

let indices = (

let uu____23960 = (

let uu____23961 = (FStar_Syntax_Subst.compress res)
in uu____23961.FStar_Syntax_Syntax.n)
in (match (uu____23960) with
| FStar_Syntax_Syntax.Tm_app (uu____23972, indices) -> begin
indices
end
| uu____23994 -> begin
[]
end))
in (

let env1 = (FStar_All.pipe_right args (FStar_List.fold_left (fun env1 uu____24018 -> (match (uu____24018) with
| (x, uu____24024) -> begin
(

let uu____24025 = (

let uu____24026 = (

let uu____24033 = (mk_term_projector_name l x)
in ((uu____24033), ((xx)::[])))
in (FStar_SMTEncoding_Util.mkApp uu____24026))
in (push_term_var env1 x uu____24025))
end)) env))
in (

let uu____24036 = (encode_args indices env1)
in (match (uu____24036) with
| (indices1, decls') -> begin
((match ((Prims.op_disEquality (FStar_List.length indices1) (FStar_List.length vars))) with
| true -> begin
(failwith "Impossible")
end
| uu____24060 -> begin
()
end);
(

let eqs = (

let uu____24062 = (FStar_List.map2 (fun v1 a -> (

let uu____24078 = (

let uu____24083 = (FStar_SMTEncoding_Util.mkFreeV v1)
in ((uu____24083), (a)))
in (FStar_SMTEncoding_Util.mkEq uu____24078))) vars indices1)
in (FStar_All.pipe_right uu____24062 FStar_SMTEncoding_Util.mk_and_l))
in (

let uu____24086 = (

let uu____24087 = (

let uu____24092 = (

let uu____24093 = (

let uu____24098 = (mk_data_tester env1 l xx)
in ((uu____24098), (eqs)))
in (FStar_SMTEncoding_Util.mkAnd uu____24093))
in ((out), (uu____24092)))
in (FStar_SMTEncoding_Util.mkOr uu____24087))
in ((uu____24086), ((FStar_List.append decls decls')))));
)
end))))
end))
end))
end)) ((FStar_SMTEncoding_Util.mkFalse), ([]))))
in (match (uu____23842) with
| (data_ax, decls) -> begin
(

let uu____24111 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____24111) with
| (ffsym, ff) -> begin
(

let fuel_guarded_inversion = (

let xx_has_type_sfuel = (match (((FStar_List.length datas) > (Prims.parse_int "1"))) with
| true -> begin
(

let uu____24122 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((ff)::[])))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel uu____24122 xx tapp))
end
| uu____24125 -> begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end)
in (

let uu____24126 = (

let uu____24133 = (

let uu____24134 = (

let uu____24145 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (

let uu____24154 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_sfuel), (data_ax)))
in ((((xx_has_type_sfuel)::[])::[]), (uu____24145), (uu____24154))))
in (FStar_SMTEncoding_Util.mkForall uu____24134))
in (

let uu____24163 = (varops.mk_unique (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str))
in ((uu____24133), (FStar_Pervasives_Native.Some ("inversion axiom")), (uu____24163))))
in (FStar_SMTEncoding_Util.mkAssume uu____24126)))
in (FStar_List.append decls ((fuel_guarded_inversion)::[])))
end))
end))
end))
end)))
in (

let uu____24164 = (

let uu____24177 = (

let uu____24178 = (FStar_Syntax_Subst.compress k)
in uu____24178.FStar_Syntax_Syntax.n)
in (match (uu____24177) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
(((FStar_List.append tps formals)), ((FStar_Syntax_Util.comp_result kres)))
end
| uu____24223 -> begin
((tps), (k))
end))
in (match (uu____24164) with
| (formals, res) -> begin
(

let uu____24246 = (FStar_Syntax_Subst.open_term formals res)
in (match (uu____24246) with
| (formals1, res1) -> begin
(

let uu____24257 = (encode_binders FStar_Pervasives_Native.None formals1 env)
in (match (uu____24257) with
| (vars, guards, env', binder_decls, uu____24282) -> begin
(

let arity = (FStar_List.length vars)
in (

let uu____24296 = (new_term_constant_and_tok_from_lid env t arity)
in (match (uu____24296) with
| (tname, ttok, env1) -> begin
(

let ttok_tm = (FStar_SMTEncoding_Util.mkApp ((ttok), ([])))
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let tapp = (

let uu____24319 = (

let uu____24326 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((tname), (uu____24326)))
in (FStar_SMTEncoding_Util.mkApp uu____24319))
in (

let uu____24331 = (

let tname_decl = (

let uu____24339 = (

let uu____24340 = (FStar_All.pipe_right vars (FStar_List.map (fun uu____24366 -> (match (uu____24366) with
| (n1, s) -> begin
(((Prims.strcat tname n1)), (s), (false))
end))))
in (

let uu____24379 = (varops.next_id ())
in ((tname), (uu____24340), (FStar_SMTEncoding_Term.Term_sort), (uu____24379), (false))))
in (constructor_or_logic_type_decl uu____24339))
in (

let uu____24382 = (match (vars) with
| [] -> begin
(

let uu____24395 = (

let uu____24396 = (

let uu____24399 = (FStar_SMTEncoding_Util.mkApp ((tname), ([])))
in (FStar_All.pipe_left (fun _0_20 -> FStar_Pervasives_Native.Some (_0_20)) uu____24399))
in (replace_free_var env1 t arity tname uu____24396))
in (([]), (uu____24395)))
end
| uu____24410 -> begin
(

let ttok_decl = FStar_SMTEncoding_Term.DeclFun (((ttok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("token"))))
in (

let ttok_fresh = (

let uu____24417 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ttok), (FStar_SMTEncoding_Term.Term_sort)) uu____24417))
in (

let ttok_app = (mk_Apply ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (

let uu____24431 = (

let uu____24438 = (

let uu____24439 = (

let uu____24454 = (FStar_SMTEncoding_Util.mkEq ((ttok_app), (tapp)))
in ((pats), (FStar_Pervasives_Native.None), (vars), (uu____24454)))
in (FStar_SMTEncoding_Util.mkForall' uu____24439))
in ((uu____24438), (FStar_Pervasives_Native.Some ("name-token correspondence")), ((Prims.strcat "token_correspondence_" ttok))))
in (FStar_SMTEncoding_Util.mkAssume uu____24431))
in (((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[]), (env1)))))))
end)
in (match (uu____24382) with
| (tok_decls, env2) -> begin
(((FStar_List.append tname_decl tok_decls)), (env2))
end)))
in (match (uu____24331) with
| (decls, env2) -> begin
(

let kindingAx = (

let uu____24490 = (encode_term_pred FStar_Pervasives_Native.None res1 env' tapp)
in (match (uu____24490) with
| (k1, decls1) -> begin
(

let karr = (match (((FStar_List.length formals1) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____24508 = (

let uu____24509 = (

let uu____24516 = (

let uu____24517 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____24517))
in ((uu____24516), (FStar_Pervasives_Native.Some ("kinding")), ((Prims.strcat "pre_kinding_" ttok))))
in (FStar_SMTEncoding_Util.mkAssume uu____24509))
in (uu____24508)::[])
end
| uu____24518 -> begin
[]
end)
in (

let uu____24519 = (

let uu____24522 = (

let uu____24525 = (

let uu____24526 = (

let uu____24533 = (

let uu____24534 = (

let uu____24545 = (FStar_SMTEncoding_Util.mkImp ((guard), (k1)))
in ((((tapp)::[])::[]), (vars), (uu____24545)))
in (FStar_SMTEncoding_Util.mkForall uu____24534))
in ((uu____24533), (FStar_Pervasives_Native.None), ((Prims.strcat "kinding_" ttok))))
in (FStar_SMTEncoding_Util.mkAssume uu____24526))
in (uu____24525)::[])
in (FStar_List.append karr uu____24522))
in (FStar_List.append decls1 uu____24519)))
end))
in (

let aux = (

let uu____24557 = (

let uu____24560 = (inversion_axioms tapp vars)
in (

let uu____24563 = (

let uu____24566 = (pretype_axiom env2 tapp vars)
in (uu____24566)::[])
in (FStar_List.append uu____24560 uu____24563)))
in (FStar_List.append kindingAx uu____24557))
in (

let g = (FStar_List.append decls (FStar_List.append binder_decls aux))
in ((g), (env2)))))
end)))))
end)))
end))
end))
end))))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____24571, uu____24572, uu____24573, uu____24574, uu____24575) when (FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____24581, t, uu____24583, n_tps, uu____24585) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____24593 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____24593) with
| (formals, t_res) -> begin
(

let arity = (FStar_List.length formals)
in (

let uu____24633 = (new_term_constant_and_tok_from_lid env d arity)
in (match (uu____24633) with
| (ddconstrsym, ddtok, env1) -> begin
(

let ddtok_tm = (FStar_SMTEncoding_Util.mkApp ((ddtok), ([])))
in (

let uu____24654 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____24654) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (

let uu____24668 = (encode_binders (FStar_Pervasives_Native.Some (fuel_tm)) formals env1)
in (match (uu____24668) with
| (vars, guards, env', binder_decls, names1) -> begin
(

let fields = (FStar_All.pipe_right names1 (FStar_List.mapi (fun n1 x -> (

let projectible = true
in (

let uu____24726 = (mk_term_projector_name d x)
in ((uu____24726), (FStar_SMTEncoding_Term.Term_sort), (projectible)))))))
in (

let datacons = (

let uu____24728 = (

let uu____24741 = (varops.next_id ())
in ((ddconstrsym), (fields), (FStar_SMTEncoding_Term.Term_sort), (uu____24741), (true)))
in (FStar_All.pipe_right uu____24728 FStar_SMTEncoding_Term.constructor_to_decl))
in (

let app = (mk_Apply ddtok_tm vars)
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (

let uu____24764 = (encode_term_pred FStar_Pervasives_Native.None t env1 ddtok_tm)
in (match (uu____24764) with
| (tok_typing, decls3) -> begin
(

let tok_typing1 = (match (fields) with
| (uu____24776)::uu____24777 -> begin
(

let ff = (("ty"), (FStar_SMTEncoding_Term.Term_sort))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV ff)
in (

let vtok_app_l = (mk_Apply ddtok_tm ((ff)::[]))
in (

let vtok_app_r = (mk_Apply f ((((ddtok), (FStar_SMTEncoding_Term.Term_sort)))::[]))
in (

let uu____24804 = (

let uu____24815 = (FStar_SMTEncoding_Term.mk_NoHoist f tok_typing)
in ((((vtok_app_l)::[])::((vtok_app_r)::[])::[]), ((ff)::[]), (uu____24815)))
in (FStar_SMTEncoding_Util.mkForall uu____24804))))))
end
| uu____24834 -> begin
tok_typing
end)
in (

let uu____24837 = (encode_binders (FStar_Pervasives_Native.Some (fuel_tm)) formals env1)
in (match (uu____24837) with
| (vars', guards', env'', decls_formals, uu____24862) -> begin
(

let uu____24875 = (

let xvars1 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars')
in (

let dapp1 = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars1)))
in (encode_term_pred (FStar_Pervasives_Native.Some (fuel_tm)) t_res env'' dapp1)))
in (match (uu____24875) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_SMTEncoding_Util.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| uu____24902 -> begin
(

let uu____24909 = (

let uu____24910 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ddtok), (FStar_SMTEncoding_Term.Term_sort)) uu____24910))
in (uu____24909)::[])
end)
in (

let encode_elim = (fun uu____24922 -> (

let uu____24923 = (FStar_Syntax_Util.head_and_args t_res)
in (match (uu____24923) with
| (head1, args) -> begin
(

let uu____24966 = (

let uu____24967 = (FStar_Syntax_Subst.compress head1)
in uu____24967.FStar_Syntax_Syntax.n)
in (match (uu____24966) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____24977; FStar_Syntax_Syntax.vars = uu____24978}, uu____24979) -> begin
(

let uu____24984 = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (match (uu____24984) with
| (encoded_head, encoded_head_arity) -> begin
(

let uu____24997 = (encode_args args env')
in (match (uu____24997) with
| (encoded_args, arg_decls) -> begin
(

let guards_for_parameter = (fun orig_arg arg xv -> (

let fv1 = (match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv1) -> begin
fv1
end
| uu____25046 -> begin
(

let uu____25047 = (

let uu____25052 = (

let uu____25053 = (FStar_Syntax_Print.term_to_string orig_arg)
in (FStar_Util.format1 "Inductive type parameter %s must be a variable ; You may want to change it to an index." uu____25053))
in ((FStar_Errors.Fatal_NonVariableInductiveTypeParameter), (uu____25052)))
in (FStar_Errors.raise_error uu____25047 orig_arg.FStar_Syntax_Syntax.pos))
end)
in (

let guards1 = (FStar_All.pipe_right guards (FStar_List.collect (fun g -> (

let uu____25069 = (

let uu____25070 = (FStar_SMTEncoding_Term.free_variables g)
in (FStar_List.contains fv1 uu____25070))
in (match (uu____25069) with
| true -> begin
(

let uu____25083 = (FStar_SMTEncoding_Term.subst g fv1 xv)
in (uu____25083)::[])
end
| uu____25084 -> begin
[]
end)))))
in (FStar_SMTEncoding_Util.mk_and_l guards1))))
in (

let uu____25085 = (

let uu____25098 = (FStar_List.zip args encoded_args)
in (FStar_List.fold_left (fun uu____25148 uu____25149 -> (match (((uu____25148), (uu____25149))) with
| ((env2, arg_vars, eqns_or_guards, i), (orig_arg, arg)) -> begin
(

let uu____25244 = (

let uu____25251 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (gen_term_var env2 uu____25251))
in (match (uu____25244) with
| (uu____25264, xv, env3) -> begin
(

let eqns = (match ((i < n_tps)) with
| true -> begin
(

let uu____25272 = (guards_for_parameter (FStar_Pervasives_Native.fst orig_arg) arg xv)
in (uu____25272)::eqns_or_guards)
end
| uu____25273 -> begin
(

let uu____25274 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (uu____25274)::eqns_or_guards)
end)
in ((env3), ((xv)::arg_vars), (eqns), ((i + (Prims.parse_int "1")))))
end))
end)) ((env'), ([]), ([]), ((Prims.parse_int "0"))) uu____25098))
in (match (uu____25085) with
| (uu____25289, arg_vars, elim_eqns_or_guards, uu____25292) -> begin
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

let uu____25316 = (

let uu____25323 = (

let uu____25324 = (

let uu____25335 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____25336 = (

let uu____25337 = (

let uu____25342 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append elim_eqns_or_guards guards))
in ((ty_pred), (uu____25342)))
in (FStar_SMTEncoding_Util.mkImp uu____25337))
in ((((ty_pred)::[])::[]), (uu____25335), (uu____25336))))
in (FStar_SMTEncoding_Util.mkForall uu____25324))
in ((uu____25323), (FStar_Pervasives_Native.Some ("data constructor typing elim")), ((Prims.strcat "data_elim_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____25316))
in (

let subterm_ordering = (

let uu____25352 = (FStar_Ident.lid_equals d FStar_Parser_Const.lextop_lid)
in (match (uu____25352) with
| true -> begin
(

let x = (

let uu____25358 = (varops.fresh "x")
in ((uu____25358), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (

let uu____25360 = (

let uu____25367 = (

let uu____25368 = (

let uu____25379 = (

let uu____25384 = (

let uu____25387 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in (uu____25387)::[])
in (uu____25384)::[])
in (

let uu____25392 = (

let uu____25393 = (

let uu____25398 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (

let uu____25399 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in ((uu____25398), (uu____25399))))
in (FStar_SMTEncoding_Util.mkImp uu____25393))
in ((uu____25379), ((x)::[]), (uu____25392))))
in (FStar_SMTEncoding_Util.mkForall uu____25368))
in (

let uu____25412 = (varops.mk_unique "lextop")
in ((uu____25367), (FStar_Pervasives_Native.Some ("lextop is top")), (uu____25412))))
in (FStar_SMTEncoding_Util.mkAssume uu____25360))))
end
| uu____25413 -> begin
(

let prec = (

let uu____25417 = (FStar_All.pipe_right vars (FStar_List.mapi (fun i v1 -> (match ((i < n_tps)) with
| true -> begin
[]
end
| uu____25444 -> begin
(

let uu____25445 = (

let uu____25446 = (FStar_SMTEncoding_Util.mkFreeV v1)
in (FStar_SMTEncoding_Util.mk_Precedes uu____25446 dapp1))
in (uu____25445)::[])
end))))
in (FStar_All.pipe_right uu____25417 FStar_List.flatten))
in (

let uu____25453 = (

let uu____25460 = (

let uu____25461 = (

let uu____25472 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____25473 = (

let uu____25474 = (

let uu____25479 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (uu____25479)))
in (FStar_SMTEncoding_Util.mkImp uu____25474))
in ((((ty_pred)::[])::[]), (uu____25472), (uu____25473))))
in (FStar_SMTEncoding_Util.mkForall uu____25461))
in ((uu____25460), (FStar_Pervasives_Native.Some ("subterm ordering")), ((Prims.strcat "subterm_ordering_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____25453)))
end))
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____25491 = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (match (uu____25491) with
| (encoded_head, encoded_head_arity) -> begin
(

let uu____25504 = (encode_args args env')
in (match (uu____25504) with
| (encoded_args, arg_decls) -> begin
(

let guards_for_parameter = (fun orig_arg arg xv -> (

let fv1 = (match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv1) -> begin
fv1
end
| uu____25553 -> begin
(

let uu____25554 = (

let uu____25559 = (

let uu____25560 = (FStar_Syntax_Print.term_to_string orig_arg)
in (FStar_Util.format1 "Inductive type parameter %s must be a variable ; You may want to change it to an index." uu____25560))
in ((FStar_Errors.Fatal_NonVariableInductiveTypeParameter), (uu____25559)))
in (FStar_Errors.raise_error uu____25554 orig_arg.FStar_Syntax_Syntax.pos))
end)
in (

let guards1 = (FStar_All.pipe_right guards (FStar_List.collect (fun g -> (

let uu____25576 = (

let uu____25577 = (FStar_SMTEncoding_Term.free_variables g)
in (FStar_List.contains fv1 uu____25577))
in (match (uu____25576) with
| true -> begin
(

let uu____25590 = (FStar_SMTEncoding_Term.subst g fv1 xv)
in (uu____25590)::[])
end
| uu____25591 -> begin
[]
end)))))
in (FStar_SMTEncoding_Util.mk_and_l guards1))))
in (

let uu____25592 = (

let uu____25605 = (FStar_List.zip args encoded_args)
in (FStar_List.fold_left (fun uu____25655 uu____25656 -> (match (((uu____25655), (uu____25656))) with
| ((env2, arg_vars, eqns_or_guards, i), (orig_arg, arg)) -> begin
(

let uu____25751 = (

let uu____25758 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (gen_term_var env2 uu____25758))
in (match (uu____25751) with
| (uu____25771, xv, env3) -> begin
(

let eqns = (match ((i < n_tps)) with
| true -> begin
(

let uu____25779 = (guards_for_parameter (FStar_Pervasives_Native.fst orig_arg) arg xv)
in (uu____25779)::eqns_or_guards)
end
| uu____25780 -> begin
(

let uu____25781 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (uu____25781)::eqns_or_guards)
end)
in ((env3), ((xv)::arg_vars), (eqns), ((i + (Prims.parse_int "1")))))
end))
end)) ((env'), ([]), ([]), ((Prims.parse_int "0"))) uu____25605))
in (match (uu____25592) with
| (uu____25796, arg_vars, elim_eqns_or_guards, uu____25799) -> begin
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

let uu____25823 = (

let uu____25830 = (

let uu____25831 = (

let uu____25842 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____25843 = (

let uu____25844 = (

let uu____25849 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append elim_eqns_or_guards guards))
in ((ty_pred), (uu____25849)))
in (FStar_SMTEncoding_Util.mkImp uu____25844))
in ((((ty_pred)::[])::[]), (uu____25842), (uu____25843))))
in (FStar_SMTEncoding_Util.mkForall uu____25831))
in ((uu____25830), (FStar_Pervasives_Native.Some ("data constructor typing elim")), ((Prims.strcat "data_elim_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____25823))
in (

let subterm_ordering = (

let uu____25859 = (FStar_Ident.lid_equals d FStar_Parser_Const.lextop_lid)
in (match (uu____25859) with
| true -> begin
(

let x = (

let uu____25865 = (varops.fresh "x")
in ((uu____25865), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (

let uu____25867 = (

let uu____25874 = (

let uu____25875 = (

let uu____25886 = (

let uu____25891 = (

let uu____25894 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in (uu____25894)::[])
in (uu____25891)::[])
in (

let uu____25899 = (

let uu____25900 = (

let uu____25905 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (

let uu____25906 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in ((uu____25905), (uu____25906))))
in (FStar_SMTEncoding_Util.mkImp uu____25900))
in ((uu____25886), ((x)::[]), (uu____25899))))
in (FStar_SMTEncoding_Util.mkForall uu____25875))
in (

let uu____25919 = (varops.mk_unique "lextop")
in ((uu____25874), (FStar_Pervasives_Native.Some ("lextop is top")), (uu____25919))))
in (FStar_SMTEncoding_Util.mkAssume uu____25867))))
end
| uu____25920 -> begin
(

let prec = (

let uu____25924 = (FStar_All.pipe_right vars (FStar_List.mapi (fun i v1 -> (match ((i < n_tps)) with
| true -> begin
[]
end
| uu____25951 -> begin
(

let uu____25952 = (

let uu____25953 = (FStar_SMTEncoding_Util.mkFreeV v1)
in (FStar_SMTEncoding_Util.mk_Precedes uu____25953 dapp1))
in (uu____25952)::[])
end))))
in (FStar_All.pipe_right uu____25924 FStar_List.flatten))
in (

let uu____25960 = (

let uu____25967 = (

let uu____25968 = (

let uu____25979 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____25980 = (

let uu____25981 = (

let uu____25986 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (uu____25986)))
in (FStar_SMTEncoding_Util.mkImp uu____25981))
in ((((ty_pred)::[])::[]), (uu____25979), (uu____25980))))
in (FStar_SMTEncoding_Util.mkForall uu____25968))
in ((uu____25967), (FStar_Pervasives_Native.Some ("subterm ordering")), ((Prims.strcat "subterm_ordering_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____25960)))
end))
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end)))
end))
end))
end
| uu____25997 -> begin
((

let uu____25999 = (

let uu____26004 = (

let uu____26005 = (FStar_Syntax_Print.lid_to_string d)
in (

let uu____26006 = (FStar_Syntax_Print.term_to_string head1)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" uu____26005 uu____26006)))
in ((FStar_Errors.Warning_ConstructorBuildsUnexpectedType), (uu____26004)))
in (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng uu____25999));
(([]), ([]));
)
end))
end)))
in (

let uu____26011 = (encode_elim ())
in (match (uu____26011) with
| (decls2, elim) -> begin
(

let g = (

let uu____26031 = (

let uu____26034 = (

let uu____26037 = (

let uu____26040 = (

let uu____26043 = (

let uu____26044 = (

let uu____26055 = (

let uu____26056 = (

let uu____26057 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" uu____26057))
in FStar_Pervasives_Native.Some (uu____26056))
in ((ddtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (uu____26055)))
in FStar_SMTEncoding_Term.DeclFun (uu____26044))
in (uu____26043)::[])
in (

let uu____26060 = (

let uu____26063 = (

let uu____26066 = (

let uu____26069 = (

let uu____26072 = (

let uu____26075 = (

let uu____26078 = (

let uu____26079 = (

let uu____26086 = (

let uu____26087 = (

let uu____26098 = (FStar_SMTEncoding_Util.mkEq ((app), (dapp)))
in ((((app)::[])::[]), (vars), (uu____26098)))
in (FStar_SMTEncoding_Util.mkForall uu____26087))
in ((uu____26086), (FStar_Pervasives_Native.Some ("equality for proxy")), ((Prims.strcat "equality_tok_" ddtok))))
in (FStar_SMTEncoding_Util.mkAssume uu____26079))
in (

let uu____26107 = (

let uu____26110 = (

let uu____26111 = (

let uu____26118 = (

let uu____26119 = (

let uu____26130 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) vars')
in (

let uu____26131 = (FStar_SMTEncoding_Util.mkImp ((guard'), (ty_pred')))
in ((((ty_pred')::[])::[]), (uu____26130), (uu____26131))))
in (FStar_SMTEncoding_Util.mkForall uu____26119))
in ((uu____26118), (FStar_Pervasives_Native.Some ("data constructor typing intro")), ((Prims.strcat "data_typing_intro_" ddtok))))
in (FStar_SMTEncoding_Util.mkAssume uu____26111))
in (uu____26110)::[])
in (uu____26078)::uu____26107))
in ((FStar_SMTEncoding_Util.mkAssume ((tok_typing1), (FStar_Pervasives_Native.Some ("typing for data constructor proxy")), ((Prims.strcat "typing_tok_" ddtok)))))::uu____26075)
in (FStar_List.append uu____26072 elim))
in (FStar_List.append decls_pred uu____26069))
in (FStar_List.append decls_formals uu____26066))
in (FStar_List.append proxy_fresh uu____26063))
in (FStar_List.append uu____26040 uu____26060)))
in (FStar_List.append decls3 uu____26037))
in (FStar_List.append decls2 uu____26034))
in (FStar_List.append binder_decls uu____26031))
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
and encode_sigelts : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun uu____26165 se -> (match (uu____26165) with
| (g, env1) -> begin
(

let uu____26185 = (encode_sigelt env1 se)
in (match (uu____26185) with
| (g', env2) -> begin
(((FStar_List.append g g')), (env2))
end))
end)) (([]), (env)))))


let encode_env_bindings : env_t  ->  FStar_Syntax_Syntax.binding Prims.list  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env bindings -> (

let encode_binding = (fun b uu____26250 -> (match (uu____26250) with
| (i, decls, env1) -> begin
(match (b) with
| FStar_Syntax_Syntax.Binding_univ (uu____26282) -> begin
(((i + (Prims.parse_int "1"))), (decls), (env1))
end
| FStar_Syntax_Syntax.Binding_var (x) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env1.tcenv x.FStar_Syntax_Syntax.sort)
in ((

let uu____26288 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____26288) with
| true -> begin
(

let uu____26289 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____26290 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____26291 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" uu____26289 uu____26290 uu____26291))))
end
| uu____26292 -> begin
()
end));
(

let uu____26293 = (encode_term t1 env1)
in (match (uu____26293) with
| (t, decls') -> begin
(

let t_hash = (FStar_SMTEncoding_Term.hash_of_term t)
in (

let uu____26309 = (

let uu____26316 = (

let uu____26317 = (

let uu____26318 = (FStar_Util.digest_of_string t_hash)
in (Prims.strcat uu____26318 (Prims.strcat "_" (Prims.string_of_int i))))
in (Prims.strcat "x_" uu____26317))
in (new_term_constant_from_string env1 x uu____26316))
in (match (uu____26309) with
| (xxsym, xx, env') -> begin
(

let t2 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel FStar_Pervasives_Native.None xx t)
in (

let caption = (

let uu____26334 = (FStar_Options.log_queries ())
in (match (uu____26334) with
| true -> begin
(

let uu____26337 = (

let uu____26338 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____26339 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____26340 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" uu____26338 uu____26339 uu____26340))))
in FStar_Pervasives_Native.Some (uu____26337))
end
| uu____26341 -> begin
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
| FStar_Syntax_Syntax.Binding_lid (x, (uu____26352, t)) -> begin
(

let t_norm = (whnf env1 t)
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____26372 = (encode_free_var false env1 fv t t_norm [])
in (match (uu____26372) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))))
end)
end))
in (

let uu____26395 = (FStar_List.fold_right encode_binding bindings (((Prims.parse_int "0")), ([]), (env)))
in (match (uu____26395) with
| (uu____26418, decls, env1) -> begin
((decls), (env1))
end))))


let encode_labels : 'Auu____26431 'Auu____26432 . ((Prims.string * FStar_SMTEncoding_Term.sort) * 'Auu____26431 * 'Auu____26432) Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl Prims.list) = (fun labs -> (

let prefix1 = (FStar_All.pipe_right labs (FStar_List.map (fun uu____26501 -> (match (uu____26501) with
| (l, uu____26513, uu____26514) -> begin
FStar_SMTEncoding_Term.DeclFun ((((FStar_Pervasives_Native.fst l)), ([]), (FStar_SMTEncoding_Term.Bool_sort), (FStar_Pervasives_Native.None)))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun uu____26558 -> (match (uu____26558) with
| (l, uu____26572, uu____26573) -> begin
(

let uu____26582 = (FStar_All.pipe_left (fun _0_21 -> FStar_SMTEncoding_Term.Echo (_0_21)) (FStar_Pervasives_Native.fst l))
in (

let uu____26583 = (

let uu____26586 = (

let uu____26587 = (FStar_SMTEncoding_Util.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (uu____26587))
in (uu____26586)::[])
in (uu____26582)::uu____26583))
end))))
in ((prefix1), (suffix)))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_TypeChecker_Env.env  ->  unit = (fun tcenv -> (

let uu____26614 = (

let uu____26617 = (

let uu____26618 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (

let uu____26621 = (

let uu____26622 = (FStar_TypeChecker_Env.current_module tcenv)
in (FStar_All.pipe_right uu____26622 FStar_Ident.string_of_lid))
in {bindings = []; depth = (Prims.parse_int "0"); tcenv = tcenv; warn = true; cache = uu____26618; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true; current_module_name = uu____26621}))
in (uu____26617)::[])
in (FStar_ST.op_Colon_Equals last_env uu____26614)))


let get_env : FStar_Ident.lident  ->  FStar_TypeChecker_Env.env  ->  env_t = (fun cmn tcenv -> (

let uu____26660 = (FStar_ST.op_Bang last_env)
in (match (uu____26660) with
| [] -> begin
(failwith "No env; call init first!")
end
| (e)::uu____26691 -> begin
(

let uu___134_26694 = e
in (

let uu____26695 = (FStar_Ident.string_of_lid cmn)
in {bindings = uu___134_26694.bindings; depth = uu___134_26694.depth; tcenv = tcenv; warn = uu___134_26694.warn; cache = uu___134_26694.cache; nolabels = uu___134_26694.nolabels; use_zfuel_name = uu___134_26694.use_zfuel_name; encode_non_total_function_typ = uu___134_26694.encode_non_total_function_typ; current_module_name = uu____26695}))
end)))


let set_env : env_t  ->  unit = (fun env -> (

let uu____26701 = (FStar_ST.op_Bang last_env)
in (match (uu____26701) with
| [] -> begin
(failwith "Empty env stack")
end
| (uu____26731)::tl1 -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl1))
end)))


let push_env : unit  ->  unit = (fun uu____26766 -> (

let uu____26767 = (FStar_ST.op_Bang last_env)
in (match (uu____26767) with
| [] -> begin
(failwith "Empty env stack")
end
| (hd1)::tl1 -> begin
(

let refs = (FStar_Util.smap_copy hd1.cache)
in (

let top = (

let uu___135_26805 = hd1
in {bindings = uu___135_26805.bindings; depth = uu___135_26805.depth; tcenv = uu___135_26805.tcenv; warn = uu___135_26805.warn; cache = refs; nolabels = uu___135_26805.nolabels; use_zfuel_name = uu___135_26805.use_zfuel_name; encode_non_total_function_typ = uu___135_26805.encode_non_total_function_typ; current_module_name = uu___135_26805.current_module_name})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd1)::tl1))))
end)))


let pop_env : unit  ->  unit = (fun uu____26837 -> (

let uu____26838 = (FStar_ST.op_Bang last_env)
in (match (uu____26838) with
| [] -> begin
(failwith "Popping an empty stack")
end
| (uu____26868)::tl1 -> begin
(FStar_ST.op_Colon_Equals last_env tl1)
end)))


let init : FStar_TypeChecker_Env.env  ->  unit = (fun tcenv -> ((init_env tcenv);
(FStar_SMTEncoding_Z3.init ());
(FStar_SMTEncoding_Z3.giveZ3 ((FStar_SMTEncoding_Term.DefPrelude)::[]));
))


let push : Prims.string  ->  unit = (fun msg -> ((push_env ());
(varops.push ());
(FStar_SMTEncoding_Z3.push msg);
))


let pop : Prims.string  ->  unit = (fun msg -> ((pop_env ());
(varops.pop ());
(FStar_SMTEncoding_Z3.pop msg);
))


let open_fact_db_tags : env_t  ->  FStar_SMTEncoding_Term.fact_db_id Prims.list = (fun env -> [])


let place_decl_in_fact_dbs : env_t  ->  FStar_SMTEncoding_Term.fact_db_id Prims.list  ->  FStar_SMTEncoding_Term.decl  ->  FStar_SMTEncoding_Term.decl = (fun env fact_db_ids d -> (match (((fact_db_ids), (d))) with
| ((uu____26950)::uu____26951, FStar_SMTEncoding_Term.Assume (a)) -> begin
FStar_SMTEncoding_Term.Assume ((

let uu___136_26959 = a
in {FStar_SMTEncoding_Term.assumption_term = uu___136_26959.FStar_SMTEncoding_Term.assumption_term; FStar_SMTEncoding_Term.assumption_caption = uu___136_26959.FStar_SMTEncoding_Term.assumption_caption; FStar_SMTEncoding_Term.assumption_name = uu___136_26959.FStar_SMTEncoding_Term.assumption_name; FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids}))
end
| uu____26960 -> begin
d
end))


let fact_dbs_for_lid : env_t  ->  FStar_Ident.lid  ->  FStar_SMTEncoding_Term.fact_db_id Prims.list = (fun env lid -> (

let uu____26979 = (

let uu____26982 = (

let uu____26983 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in FStar_SMTEncoding_Term.Namespace (uu____26983))
in (

let uu____26984 = (open_fact_db_tags env)
in (uu____26982)::uu____26984))
in (FStar_SMTEncoding_Term.Name (lid))::uu____26979))


let encode_top_level_facts : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env se -> (

let fact_db_ids = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.collect (fact_dbs_for_lid env)))
in (

let uu____27010 = (encode_sigelt env se)
in (match (uu____27010) with
| (g, env1) -> begin
(

let g1 = (FStar_All.pipe_right g (FStar_List.map (place_decl_in_fact_dbs env1 fact_db_ids)))
in ((g1), (env1)))
end))))


let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  unit = (fun tcenv se -> (

let caption = (fun decls -> (

let uu____27052 = (FStar_Options.log_queries ())
in (match (uu____27052) with
| true -> begin
(

let uu____27055 = (

let uu____27056 = (

let uu____27057 = (

let uu____27058 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.map FStar_Syntax_Print.lid_to_string))
in (FStar_All.pipe_right uu____27058 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " uu____27057))
in FStar_SMTEncoding_Term.Caption (uu____27056))
in (uu____27055)::decls)
end
| uu____27067 -> begin
decls
end)))
in ((

let uu____27069 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____27069) with
| true -> begin
(

let uu____27070 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____27070))
end
| uu____27071 -> begin
()
end));
(

let env = (

let uu____27073 = (FStar_TypeChecker_Env.current_module tcenv)
in (get_env uu____27073 tcenv))
in (

let uu____27074 = (encode_top_level_facts env se)
in (match (uu____27074) with
| (decls, env1) -> begin
((set_env env1);
(

let uu____27088 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 uu____27088));
)
end)));
)))


let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____27102 -> begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in ((

let uu____27104 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____27104) with
| true -> begin
(

let uu____27105 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) Prims.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name uu____27105))
end
| uu____27106 -> begin
()
end));
(

let env = (get_env modul.FStar_Syntax_Syntax.name tcenv)
in (

let encode_signature = (fun env1 ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun uu____27146 se -> (match (uu____27146) with
| (g, env2) -> begin
(

let uu____27166 = (encode_top_level_facts env2 se)
in (match (uu____27166) with
| (g', env3) -> begin
(((FStar_List.append g g')), (env3))
end))
end)) (([]), (env1)))))
in (

let uu____27189 = (encode_signature (

let uu___137_27198 = env
in {bindings = uu___137_27198.bindings; depth = uu___137_27198.depth; tcenv = uu___137_27198.tcenv; warn = false; cache = uu___137_27198.cache; nolabels = uu___137_27198.nolabels; use_zfuel_name = uu___137_27198.use_zfuel_name; encode_non_total_function_typ = uu___137_27198.encode_non_total_function_typ; current_module_name = uu___137_27198.current_module_name}) modul.FStar_Syntax_Syntax.exports)
in (match (uu____27189) with
| (decls, env1) -> begin
(

let caption = (fun decls1 -> (

let uu____27217 = (FStar_Options.log_queries ())
in (match (uu____27217) with
| true -> begin
(

let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::decls1) ((FStar_SMTEncoding_Term.Caption ((Prims.strcat "End " msg)))::[])))
end
| uu____27221 -> begin
decls1
end)))
in ((set_env (

let uu___138_27225 = env1
in {bindings = uu___138_27225.bindings; depth = uu___138_27225.depth; tcenv = uu___138_27225.tcenv; warn = true; cache = uu___138_27225.cache; nolabels = uu___138_27225.nolabels; use_zfuel_name = uu___138_27225.use_zfuel_name; encode_non_total_function_typ = uu___138_27225.encode_non_total_function_typ; current_module_name = uu___138_27225.current_module_name}));
(

let uu____27227 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____27227) with
| true -> begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end
| uu____27228 -> begin
()
end));
(

let decls1 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls1));
))
end))));
)))


let encode_query : (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_ErrorReporting.label Prims.list * FStar_SMTEncoding_Term.decl * FStar_SMTEncoding_Term.decl Prims.list) = (fun use_env_msg tcenv q -> ((

let uu____27285 = (

let uu____27286 = (FStar_TypeChecker_Env.current_module tcenv)
in uu____27286.FStar_Ident.str)
in (FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name uu____27285));
(

let env = (

let uu____27288 = (FStar_TypeChecker_Env.current_module tcenv)
in (get_env uu____27288 tcenv))
in (

let uu____27289 = (

let rec aux = (fun bindings -> (match (bindings) with
| (FStar_Syntax_Syntax.Binding_var (x))::rest -> begin
(

let uu____27326 = (aux rest)
in (match (uu____27326) with
| (out, rest1) -> begin
(

let t = (

let uu____27356 = (FStar_Syntax_Util.destruct_typ_as_formula x.FStar_Syntax_Syntax.sort)
in (match (uu____27356) with
| FStar_Pervasives_Native.Some (uu____27361) -> begin
(

let uu____27362 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.t_unit)
in (FStar_Syntax_Util.refine uu____27362 x.FStar_Syntax_Syntax.sort))
end
| uu____27363 -> begin
x.FStar_Syntax_Syntax.sort
end))
in (

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
in (

let uu____27367 = (

let uu____27370 = (FStar_Syntax_Syntax.mk_binder (

let uu___139_27373 = x
in {FStar_Syntax_Syntax.ppname = uu___139_27373.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___139_27373.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in (uu____27370)::out)
in ((uu____27367), (rest1)))))
end))
end
| uu____27378 -> begin
(([]), (bindings))
end))
in (

let uu____27385 = (aux tcenv.FStar_TypeChecker_Env.gamma)
in (match (uu____27385) with
| (closing, bindings) -> begin
(

let uu____27410 = (FStar_Syntax_Util.close_forall_no_univs (FStar_List.rev closing) q)
in ((uu____27410), (bindings)))
end)))
in (match (uu____27289) with
| (q1, bindings) -> begin
(

let uu____27433 = (encode_env_bindings env bindings)
in (match (uu____27433) with
| (env_decls, env1) -> begin
((

let uu____27455 = (((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTQuery"))))
in (match (uu____27455) with
| true -> begin
(

let uu____27456 = (FStar_Syntax_Print.term_to_string q1)
in (FStar_Util.print1 "Encoding query formula: %s\n" uu____27456))
end
| uu____27457 -> begin
()
end));
(

let uu____27458 = (encode_formula q1 env1)
in (match (uu____27458) with
| (phi, qdecls) -> begin
(

let uu____27479 = (

let uu____27484 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg uu____27484 phi))
in (match (uu____27479) with
| (labels, phi1) -> begin
(

let uu____27501 = (encode_labels labels)
in (match (uu____27501) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append env_decls (FStar_List.append label_prefix qdecls))
in (

let qry = (

let uu____27538 = (

let uu____27545 = (FStar_SMTEncoding_Util.mkNot phi1)
in (

let uu____27546 = (varops.mk_unique "@query")
in ((uu____27545), (FStar_Pervasives_Native.Some ("query")), (uu____27546))))
in (FStar_SMTEncoding_Util.mkAssume uu____27538))
in (

let suffix = (FStar_List.append ((FStar_SMTEncoding_Term.Echo ("<labels>"))::[]) (FStar_List.append label_suffix ((FStar_SMTEncoding_Term.Echo ("</labels>"))::(FStar_SMTEncoding_Term.Echo ("Done!"))::[])))
in ((query_prelude), (labels), (qry), (suffix)))))
end))
end))
end));
)
end))
end)));
))




