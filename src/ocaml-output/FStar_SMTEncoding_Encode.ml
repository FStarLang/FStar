
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


let lookup_lid : env_t  ->  FStar_Ident.lident  ->  fvar_binding = (fun env a -> (

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

let uu____3012 = (

let uu____3013 = (FStar_SMTEncoding_Util.mkFreeV ((fvb.smt_id), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_ApplyTF uu____3013 fuel))
in (FStar_All.pipe_left (fun _0_17 -> FStar_Pervasives_Native.Some (_0_17)) uu____3012))
end
| uu____3016 -> begin
FStar_Pervasives_Native.Some (t)
end))
end
| uu____3017 -> begin
FStar_Pervasives_Native.Some (t)
end)
end
| uu____3018 -> begin
FStar_Pervasives_Native.None
end)
end)
end)))


let lookup_free_var : env_t  ->  FStar_Ident.lid FStar_Syntax_Syntax.withinfo_t  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let uu____3035 = (try_lookup_free_var env a.FStar_Syntax_Syntax.v)
in (match (uu____3035) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let uu____3039 = (

let uu____3040 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" uu____3040))
in (failwith uu____3039))
end)))


let lookup_free_var_name : env_t  ->  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t  ->  (Prims.string * Prims.int) = (fun env a -> (

let fvb = (lookup_lid env a.FStar_Syntax_Syntax.v)
in ((fvb.smt_id), (fvb.smt_arity))))


let lookup_free_var_sym : env_t  ->  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t  ->  (FStar_SMTEncoding_Term.op * FStar_SMTEncoding_Term.term Prims.list * Prims.int) = (fun env a -> (

let fvb = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (fvb.smt_fuel_partial_app) with
| FStar_Pervasives_Native.Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.freevars = uu____3093; FStar_SMTEncoding_Term.rng = uu____3094}) when env.use_zfuel_name -> begin
((g), (zf), ((fvb.smt_arity + (Prims.parse_int "1"))))
end
| uu____3109 -> begin
(match (fvb.smt_token) with
| FStar_Pervasives_Native.None -> begin
((FStar_SMTEncoding_Term.Var (fvb.smt_id)), ([]), (fvb.smt_arity))
end
| FStar_Pervasives_Native.Some (sym) -> begin
(match (sym.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, (fuel)::[]) -> begin
((g), ((fuel)::[]), ((fvb.smt_arity + (Prims.parse_int "1"))))
end
| uu____3137 -> begin
((FStar_SMTEncoding_Term.Var (fvb.smt_id)), ([]), (fvb.smt_arity))
end)
end)
end)))


let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun uu___90_3154 -> (match (uu___90_3154) with
| Binding_fvar (fvb) when (Prims.op_Equality fvb.smt_id nm) -> begin
fvb.smt_token
end
| uu____3158 -> begin
FStar_Pervasives_Native.None
end))))


let mkForall_fuel' : 'Auu____3165 . 'Auu____3165  ->  (FStar_SMTEncoding_Term.pat Prims.list Prims.list * FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (fun n1 uu____3185 -> (match (uu____3185) with
| (pats, vars, body) -> begin
(

let fallback = (fun uu____3212 -> (FStar_SMTEncoding_Util.mkForall ((pats), (vars), (body))))
in (

let uu____3217 = (FStar_Options.unthrottle_inductives ())
in (match (uu____3217) with
| true -> begin
(fallback ())
end
| uu____3218 -> begin
(

let uu____3219 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____3219) with
| (fsym, fterm) -> begin
(

let add_fuel1 = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Util.mkApp (("HasTypeFuel"), ((fterm)::args)))
end
| uu____3252 -> begin
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

let uu____3273 = (add_fuel1 guards)
in (FStar_SMTEncoding_Util.mk_and_l uu____3273))
end
| uu____3276 -> begin
(

let uu____3277 = (add_fuel1 ((guard)::[]))
in (FStar_All.pipe_right uu____3277 FStar_List.hd))
end)
in (FStar_SMTEncoding_Util.mkImp ((guard1), (body'))))
end
| uu____3282 -> begin
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
| FStar_Syntax_Syntax.Tm_arrow (uu____3323) -> begin
true
end
| FStar_Syntax_Syntax.Tm_refine (uu____3336) -> begin
true
end
| FStar_Syntax_Syntax.Tm_bvar (uu____3343) -> begin
true
end
| FStar_Syntax_Syntax.Tm_uvar (uu____3344) -> begin
true
end
| FStar_Syntax_Syntax.Tm_abs (uu____3345) -> begin
true
end
| FStar_Syntax_Syntax.Tm_constant (uu____3362) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____3364 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____3364 FStar_Option.isNone))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____3382; FStar_Syntax_Syntax.vars = uu____3383}, uu____3384) -> begin
(

let uu____3405 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____3405 FStar_Option.isNone))
end
| uu____3422 -> begin
false
end)))


let head_redex : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let uu____3433 = (

let uu____3434 = (FStar_Syntax_Util.un_uinst t)
in uu____3434.FStar_Syntax_Syntax.n)
in (match (uu____3433) with
| FStar_Syntax_Syntax.Tm_abs (uu____3437, uu____3438, FStar_Pervasives_Native.Some (rc)) -> begin
(((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_Tot_lid) || (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_GTot_lid)) || (FStar_List.existsb (fun uu___91_3459 -> (match (uu___91_3459) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____3460 -> begin
false
end)) rc.FStar_Syntax_Syntax.residual_flags))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____3462 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____3462 FStar_Option.isSome))
end
| uu____3479 -> begin
false
end)))


let whnf : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____3490 = (head_normal env t)
in (match (uu____3490) with
| true -> begin
t
end
| uu____3491 -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
end)))


let norm : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t))


let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____3507 = (

let uu____3508 = (FStar_Syntax_Syntax.null_binder t)
in (uu____3508)::[])
in (

let uu____3521 = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Util.abs uu____3507 uu____3521 FStar_Pervasives_Native.None))))


let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((FStar_Pervasives_Native.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(

let uu____3565 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out uu____3565))
end
| s -> begin
(

let uu____3568 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Util.mk_ApplyTT out uu____3568))
end)) e)))


let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)))


let raise_arity_mismatch : 'Auu____3595 . Prims.string  ->  Prims.int  ->  Prims.int  ->  FStar_Range.range  ->  'Auu____3595 = (fun head1 arity n_args rng -> (

let uu____3616 = (

let uu____3621 = (

let uu____3622 = (FStar_Util.string_of_int arity)
in (

let uu____3623 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format3 "Head symbol %s expects at least %s arguments; got only %s" head1 uu____3622 uu____3623)))
in ((FStar_Errors.Fatal_SMTEncodingArityMismatch), (uu____3621)))
in (FStar_Errors.raise_error uu____3616 rng)))


let maybe_curry_app : FStar_Range.range  ->  FStar_SMTEncoding_Term.op  ->  Prims.int  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun rng head1 arity args -> (

let n_args = (FStar_List.length args)
in (match ((Prims.op_Equality n_args arity)) with
| true -> begin
(FStar_SMTEncoding_Util.mkApp' ((head1), (args)))
end
| uu____3656 -> begin
(match ((n_args > arity)) with
| true -> begin
(

let uu____3663 = (FStar_Util.first_N arity args)
in (match (uu____3663) with
| (args1, rest) -> begin
(

let head2 = (FStar_SMTEncoding_Util.mkApp' ((head1), (args1)))
in (mk_Apply_args head2 rest))
end))
end
| uu____3685 -> begin
(

let uu____3686 = (FStar_SMTEncoding_Term.op_to_string head1)
in (raise_arity_mismatch uu____3686 arity n_args rng))
end)
end)))


let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun uu___92_3695 -> (match (uu___92_3695) with
| FStar_SMTEncoding_Term.Var ("ApplyTT") -> begin
true
end
| FStar_SMTEncoding_Term.Var ("ApplyTF") -> begin
true
end
| uu____3696 -> begin
false
end))


let is_an_eta_expansion : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun env vars body -> (

let rec check_partial_applications = (fun t xs -> (match (((t.FStar_SMTEncoding_Term.tm), (xs))) with
| (FStar_SMTEncoding_Term.App (app, (f)::({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.freevars = uu____3742; FStar_SMTEncoding_Term.rng = uu____3743})::[]), (x)::xs1) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(check_partial_applications f xs1)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), uu____3766) -> begin
(

let uu____3775 = ((Prims.op_Equality (FStar_List.length args) (FStar_List.length xs)) && (FStar_List.forall2 (fun a v1 -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v1)
end
| uu____3786 -> begin
false
end)) args (FStar_List.rev xs)))
in (match (uu____3775) with
| true -> begin
(tok_of_name env f)
end
| uu____3789 -> begin
FStar_Pervasives_Native.None
end))
end
| (uu____3790, []) -> begin
(

let fvs = (FStar_SMTEncoding_Term.free_variables t)
in (

let uu____3794 = (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (

let uu____3800 = (FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)
in (not (uu____3800))))))
in (match (uu____3794) with
| true -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____3803 -> begin
FStar_Pervasives_Native.None
end)))
end
| uu____3804 -> begin
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
| uu____4064 -> begin
false
end))

exception Inner_let_rec


let uu___is_Inner_let_rec : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Inner_let_rec -> begin
true
end
| uu____4070 -> begin
false
end))


let as_function_typ : env_t  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (

let rec aux = (fun norm1 t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____4097) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_refine (uu____4110) -> begin
(

let uu____4117 = (FStar_Syntax_Util.unrefine t1)
in (aux true uu____4117))
end
| uu____4118 -> begin
(match (norm1) with
| true -> begin
(

let uu____4119 = (whnf env t1)
in (aux false uu____4119))
end
| uu____4120 -> begin
(

let uu____4121 = (

let uu____4122 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (

let uu____4123 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" uu____4122 uu____4123)))
in (failwith uu____4121))
end)
end)))
in (aux true t0)))


let rec curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.comp) = (fun k -> (

let k1 = (FStar_Syntax_Subst.compress k)
in (match (k1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| FStar_Syntax_Syntax.Tm_refine (bv, uu____4169) -> begin
(curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort)
end
| uu____4174 -> begin
(

let uu____4175 = (FStar_Syntax_Syntax.mk_Total k1)
in (([]), (uu____4175)))
end)))


let is_arithmetic_primitive : 'Auu____4192 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  'Auu____4192 Prims.list  ->  Prims.bool = (fun head1 args -> (match (((head1.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____4214)::(uu____4215)::[]) -> begin
(((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Addition) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Subtraction)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Multiply)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Division)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Modulus))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____4219)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus)
end
| uu____4222 -> begin
false
end))


let isInteger : FStar_Syntax_Syntax.term'  ->  Prims.bool = (fun tm -> (match (tm) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (n1, FStar_Pervasives_Native.None)) -> begin
true
end
| uu____4245 -> begin
false
end))


let getInteger : FStar_Syntax_Syntax.term'  ->  Prims.int = (fun tm -> (match (tm) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (n1, FStar_Pervasives_Native.None)) -> begin
(FStar_Util.int_of_string n1)
end
| uu____4262 -> begin
(failwith "Expected an Integer term")
end))


let is_BitVector_primitive : 'Auu____4269 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____4269) Prims.list  ->  Prims.bool = (fun head1 args -> (match (((head1.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((sz_arg, uu____4310))::(uu____4311)::(uu____4312)::[]) -> begin
((((((((((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_and_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_xor_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_or_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_add_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_sub_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_shift_left_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_shift_right_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_udiv_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_mod_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_uext_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_mul_lid)) && (isInteger sz_arg.FStar_Syntax_Syntax.n))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((sz_arg, uu____4363))::(uu____4364)::[]) -> begin
(((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_to_nat_lid)) && (isInteger sz_arg.FStar_Syntax_Syntax.n))
end
| uu____4401 -> begin
false
end))


let rec encode_const : FStar_Const.sconst  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list) = (fun c env -> (match (c) with
| FStar_Const.Const_unit -> begin
((FStar_SMTEncoding_Term.mk_Term_unit), ([]))
end
| FStar_Const.Const_bool (true) -> begin
(

let uu____4710 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue)
in ((uu____4710), ([])))
end
| FStar_Const.Const_bool (false) -> begin
(

let uu____4713 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse)
in ((uu____4713), ([])))
end
| FStar_Const.Const_char (c1) -> begin
(

let uu____4717 = (

let uu____4718 = (

let uu____4725 = (

let uu____4728 = (

let uu____4729 = (FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c1))
in (FStar_SMTEncoding_Term.boxInt uu____4729))
in (uu____4728)::[])
in (("FStar.Char.__char_of_int"), (uu____4725)))
in (FStar_SMTEncoding_Util.mkApp uu____4718))
in ((uu____4717), ([])))
end
| FStar_Const.Const_int (i, FStar_Pervasives_Native.None) -> begin
(

let uu____4745 = (

let uu____4746 = (FStar_SMTEncoding_Util.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt uu____4746))
in ((uu____4745), ([])))
end
| FStar_Const.Const_int (repr, FStar_Pervasives_Native.Some (sw)) -> begin
(

let syntax_term = (FStar_ToSyntax_ToSyntax.desugar_machine_integer env.tcenv.FStar_TypeChecker_Env.dsenv repr sw FStar_Range.dummyRange)
in (encode_term syntax_term env))
end
| FStar_Const.Const_string (s, uu____4767) -> begin
(

let uu____4768 = (varops.string_const s)
in ((uu____4768), ([])))
end
| FStar_Const.Const_range (uu____4771) -> begin
(

let uu____4772 = (FStar_SMTEncoding_Term.mk_Range_const ())
in ((uu____4772), ([])))
end
| FStar_Const.Const_effect -> begin
((FStar_SMTEncoding_Term.mk_Term_type), ([]))
end
| c1 -> begin
(

let uu____4778 = (

let uu____4779 = (FStar_Syntax_Print.const_to_string c1)
in (FStar_Util.format1 "Unhandled constant: %s" uu____4779))
in (failwith uu____4778))
end))
and encode_binders : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> ((

let uu____4808 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____4808) with
| true -> begin
(

let uu____4809 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" uu____4809))
end
| uu____4810 -> begin
()
end));
(

let uu____4811 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____4901 b -> (match (uu____4901) with
| (vars, guards, env1, decls, names1) -> begin
(

let uu____4980 = (

let x = (unmangle (FStar_Pervasives_Native.fst b))
in (

let uu____4996 = (gen_term_var env1 x)
in (match (uu____4996) with
| (xxsym, xx, env') -> begin
(

let uu____5020 = (

let uu____5025 = (norm env1 x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt uu____5025 env1 xx))
in (match (uu____5020) with
| (guard_x_t, decls') -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (guard_x_t), (env'), (decls'), (x))
end))
end)))
in (match (uu____4980) with
| (v1, g, env2, decls', n1) -> begin
(((v1)::vars), ((g)::guards), (env2), ((FStar_List.append decls decls')), ((n1)::names1))
end))
end)) (([]), ([]), (env), ([]), ([]))))
in (match (uu____4811) with
| (vars, guards, env1, decls, names1) -> begin
(((FStar_List.rev vars)), ((FStar_List.rev guards)), (env1), (decls), ((FStar_List.rev names1)))
end));
))
and encode_term_pred : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let uu____5174 = (encode_term t env)
in (match (uu____5174) with
| (t1, decls) -> begin
(

let uu____5185 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1)
in ((uu____5185), (decls)))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let uu____5196 = (encode_term t env)
in (match (uu____5196) with
| (t1, decls) -> begin
(match (fuel_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5211 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t1)
in ((uu____5211), (decls)))
end
| FStar_Pervasives_Native.Some (f) -> begin
(

let uu____5213 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1)
in ((uu____5213), (decls)))
end)
end)))
and encode_arith_term : env_t  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.args  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun env head1 args_e -> (

let uu____5219 = (encode_args args_e env)
in (match (uu____5219) with
| (arg_tms, decls) -> begin
(

let head_fv = (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____5238 -> begin
(failwith "Impossible")
end)
in (

let unary = (fun arg_tms1 -> (

let uu____5249 = (FStar_List.hd arg_tms1)
in (FStar_SMTEncoding_Term.unboxInt uu____5249)))
in (

let binary = (fun arg_tms1 -> (

let uu____5264 = (

let uu____5265 = (FStar_List.hd arg_tms1)
in (FStar_SMTEncoding_Term.unboxInt uu____5265))
in (

let uu____5266 = (

let uu____5267 = (

let uu____5268 = (FStar_List.tl arg_tms1)
in (FStar_List.hd uu____5268))
in (FStar_SMTEncoding_Term.unboxInt uu____5267))
in ((uu____5264), (uu____5266)))))
in (

let mk_default = (fun uu____5276 -> (

let uu____5277 = (lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name)
in (match (uu____5277) with
| (fname, fuel_args, arity) -> begin
(

let args = (FStar_List.append fuel_args arg_tms)
in (maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity args))
end)))
in (

let mk_l = (fun op mk_args ts -> (

let uu____5339 = (FStar_Options.smtencoding_l_arith_native ())
in (match (uu____5339) with
| true -> begin
(

let uu____5340 = (

let uu____5341 = (mk_args ts)
in (op uu____5341))
in (FStar_All.pipe_right uu____5340 FStar_SMTEncoding_Term.boxInt))
end
| uu____5342 -> begin
(mk_default ())
end)))
in (

let mk_nl = (fun nm op ts -> (

let uu____5376 = (FStar_Options.smtencoding_nl_arith_wrapped ())
in (match (uu____5376) with
| true -> begin
(

let uu____5377 = (binary ts)
in (match (uu____5377) with
| (t1, t2) -> begin
(

let uu____5384 = (FStar_SMTEncoding_Util.mkApp ((nm), ((t1)::(t2)::[])))
in (FStar_All.pipe_right uu____5384 FStar_SMTEncoding_Term.boxInt))
end))
end
| uu____5387 -> begin
(

let uu____5388 = (FStar_Options.smtencoding_nl_arith_native ())
in (match (uu____5388) with
| true -> begin
(

let uu____5389 = (

let uu____5390 = (binary ts)
in (op uu____5390))
in (FStar_All.pipe_right uu____5389 FStar_SMTEncoding_Term.boxInt))
end
| uu____5395 -> begin
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

let uu____5551 = (

let uu____5561 = (FStar_List.tryFind (fun uu____5585 -> (match (uu____5585) with
| (l, uu____5595) -> begin
(FStar_Syntax_Syntax.fv_eq_lid head_fv l)
end)) ops)
in (FStar_All.pipe_right uu____5561 FStar_Util.must))
in (match (uu____5551) with
| (uu____5639, op) -> begin
(

let uu____5651 = (op arg_tms)
in ((uu____5651), (decls)))
end)))))))))))))))
end)))
and encode_BitVector_term : env_t  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list) = (fun env head1 args_e -> (

let uu____5665 = (FStar_List.hd args_e)
in (match (uu____5665) with
| (tm_sz, uu____5679) -> begin
(

let sz = (getInteger tm_sz.FStar_Syntax_Syntax.n)
in (

let sz_key = (FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz))
in (

let sz_decls = (

let uu____5689 = (FStar_Util.smap_try_find env.cache sz_key)
in (match (uu____5689) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
[]
end
| FStar_Pervasives_Native.None -> begin
(

let t_decls1 = (FStar_SMTEncoding_Term.mkBvConstructor sz)
in ((

let uu____5697 = (mk_cache_entry env "" [] [])
in (FStar_Util.smap_add env.cache sz_key uu____5697));
t_decls1;
))
end))
in (

let uu____5698 = (match (((head1.FStar_Syntax_Syntax.n), (args_e))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____5736)::((sz_arg, uu____5738))::(uu____5739)::[]) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_uext_lid) && (isInteger sz_arg.FStar_Syntax_Syntax.n)) -> begin
(

let uu____5788 = (

let uu____5797 = (FStar_List.tail args_e)
in (FStar_List.tail uu____5797))
in (

let uu____5818 = (

let uu____5821 = (getInteger sz_arg.FStar_Syntax_Syntax.n)
in FStar_Pervasives_Native.Some (uu____5821))
in ((uu____5788), (uu____5818))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____5833)::((sz_arg, uu____5835))::(uu____5836)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_uext_lid) -> begin
(

let uu____5885 = (

let uu____5886 = (FStar_Syntax_Print.term_to_string sz_arg)
in (FStar_Util.format1 "Not a constant bitvector extend size: %s" uu____5886))
in (failwith uu____5885))
end
| uu____5901 -> begin
(

let uu____5914 = (FStar_List.tail args_e)
in ((uu____5914), (FStar_Pervasives_Native.None)))
end)
in (match (uu____5698) with
| (arg_tms, ext_sz) -> begin
(

let uu____5967 = (encode_args arg_tms env)
in (match (uu____5967) with
| (arg_tms1, decls) -> begin
(

let head_fv = (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____5988 -> begin
(failwith "Impossible")
end)
in (

let unary = (fun arg_tms2 -> (

let uu____5999 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____5999)))
in (

let unary_arith = (fun arg_tms2 -> (

let uu____6010 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxInt uu____6010)))
in (

let binary = (fun arg_tms2 -> (

let uu____6025 = (

let uu____6026 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____6026))
in (

let uu____6027 = (

let uu____6028 = (

let uu____6029 = (FStar_List.tl arg_tms2)
in (FStar_List.hd uu____6029))
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____6028))
in ((uu____6025), (uu____6027)))))
in (

let binary_arith = (fun arg_tms2 -> (

let uu____6046 = (

let uu____6047 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____6047))
in (

let uu____6048 = (

let uu____6049 = (

let uu____6050 = (FStar_List.tl arg_tms2)
in (FStar_List.hd uu____6050))
in (FStar_SMTEncoding_Term.unboxInt uu____6049))
in ((uu____6046), (uu____6048)))))
in (

let mk_bv = (fun op mk_args resBox ts -> (

let uu____6108 = (

let uu____6109 = (mk_args ts)
in (op uu____6109))
in (FStar_All.pipe_right uu____6108 resBox)))
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

let uu____6241 = (

let uu____6246 = (match (ext_sz) with
| FStar_Pervasives_Native.Some (x) -> begin
x
end
| FStar_Pervasives_Native.None -> begin
(failwith "impossible")
end)
in (FStar_SMTEncoding_Util.mkBvUext uu____6246))
in (

let uu____6248 = (

let uu____6253 = (

let uu____6254 = (match (ext_sz) with
| FStar_Pervasives_Native.Some (x) -> begin
x
end
| FStar_Pervasives_Native.None -> begin
(failwith "impossible")
end)
in (sz + uu____6254))
in (FStar_SMTEncoding_Term.boxBitVec uu____6253))
in (mk_bv uu____6241 unary uu____6248 arg_tms2))))
in (

let to_int1 = (mk_bv FStar_SMTEncoding_Util.mkBvToNat unary FStar_SMTEncoding_Term.boxInt)
in (

let bv_to = (mk_bv (FStar_SMTEncoding_Util.mkNatToBv sz) unary_arith (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let ops = (((FStar_Parser_Const.bv_and_lid), (bv_and)))::(((FStar_Parser_Const.bv_xor_lid), (bv_xor)))::(((FStar_Parser_Const.bv_or_lid), (bv_or)))::(((FStar_Parser_Const.bv_add_lid), (bv_add)))::(((FStar_Parser_Const.bv_sub_lid), (bv_sub)))::(((FStar_Parser_Const.bv_shift_left_lid), (bv_shl)))::(((FStar_Parser_Const.bv_shift_right_lid), (bv_shr)))::(((FStar_Parser_Const.bv_udiv_lid), (bv_udiv)))::(((FStar_Parser_Const.bv_mod_lid), (bv_mod)))::(((FStar_Parser_Const.bv_mul_lid), (bv_mul)))::(((FStar_Parser_Const.bv_ult_lid), (bv_ult)))::(((FStar_Parser_Const.bv_uext_lid), (bv_uext)))::(((FStar_Parser_Const.bv_to_nat_lid), (to_int1)))::(((FStar_Parser_Const.nat_to_bv_lid), (bv_to)))::[]
in (

let uu____6487 = (

let uu____6497 = (FStar_List.tryFind (fun uu____6521 -> (match (uu____6521) with
| (l, uu____6531) -> begin
(FStar_Syntax_Syntax.fv_eq_lid head_fv l)
end)) ops)
in (FStar_All.pipe_right uu____6497 FStar_Util.must))
in (match (uu____6487) with
| (uu____6577, op) -> begin
(

let uu____6589 = (op arg_tms1)
in ((uu____6589), ((FStar_List.append sz_decls decls))))
end)))))))))))))))))))))))
end))
end)))))
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let t0 = (FStar_Syntax_Subst.compress t)
in ((

let uu____6600 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____6600) with
| true -> begin
(

let uu____6601 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____6602 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____6603 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" uu____6601 uu____6602 uu____6603))))
end
| uu____6604 -> begin
()
end));
(match (t0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____6609) -> begin
(

let uu____6634 = (

let uu____6635 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____6636 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____6637 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____6638 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6635 uu____6636 uu____6637 uu____6638)))))
in (failwith uu____6634))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____6643 = (

let uu____6644 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____6645 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____6646 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____6647 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6644 uu____6645 uu____6646 uu____6647)))))
in (failwith uu____6643))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____6653 = (FStar_Syntax_Util.unfold_lazy i)
in (encode_term uu____6653 env))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____6655 = (

let uu____6656 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" uu____6656))
in (failwith uu____6655))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, (k, uu____6663), uu____6664) -> begin
(

let uu____6713 = (match (k) with
| FStar_Util.Inl (t2) -> begin
(FStar_Syntax_Util.is_unit t2)
end
| uu____6721 -> begin
false
end)
in (match (uu____6713) with
| true -> begin
((FStar_SMTEncoding_Term.mk_Term_unit), ([]))
end
| uu____6734 -> begin
(encode_term t1 env)
end))
end
| FStar_Syntax_Syntax.Tm_quoted (qt, uu____6736) -> begin
(

let tv = (

let uu____6742 = (FStar_Reflection_Basic.inspect_ln qt)
in (FStar_Syntax_Embeddings.embed FStar_Reflection_Embeddings.e_term_view t.FStar_Syntax_Syntax.pos uu____6742))
in (

let t1 = (

let uu____6746 = (

let uu____6755 = (FStar_Syntax_Syntax.as_arg tv)
in (uu____6755)::[])
in (FStar_Syntax_Util.mk_app (FStar_Reflection_Data.refl_constant_term FStar_Reflection_Data.fstar_refl_pack_ln) uu____6746))
in (encode_term t1 env)))
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____6775) -> begin
(encode_term t1 env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t1 = (lookup_term_var env x)
in ((t1), ([])))
end
| FStar_Syntax_Syntax.Tm_fvar (v1) -> begin
(

let uu____6783 = (lookup_free_var env v1.FStar_Syntax_Syntax.fv_name)
in ((uu____6783), ([])))
end
| FStar_Syntax_Syntax.Tm_type (uu____6784) -> begin
((FStar_SMTEncoding_Term.mk_Term_type), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____6786) -> begin
(encode_term t1 env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(encode_const c env)
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let module_name = env.current_module_name
in (

let uu____6811 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____6811) with
| (binders1, res) -> begin
(

let uu____6822 = ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res))
in (match (uu____6822) with
| true -> begin
(

let uu____6827 = (encode_binders FStar_Pervasives_Native.None binders1 env)
in (match (uu____6827) with
| (vars, guards, env', decls, uu____6852) -> begin
(

let fsym = (

let uu____6870 = (varops.fresh "f")
in ((uu____6870), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV fsym)
in (

let app = (mk_Apply f vars)
in (

let uu____6873 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post (

let uu___114_6882 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___114_6882.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___114_6882.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___114_6882.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___114_6882.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___114_6882.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___114_6882.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___114_6882.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___114_6882.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___114_6882.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___114_6882.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___114_6882.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___114_6882.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___114_6882.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___114_6882.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___114_6882.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___114_6882.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___114_6882.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___114_6882.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___114_6882.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___114_6882.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___114_6882.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___114_6882.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___114_6882.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___114_6882.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___114_6882.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___114_6882.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___114_6882.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___114_6882.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___114_6882.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___114_6882.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___114_6882.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___114_6882.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___114_6882.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___114_6882.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___114_6882.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___114_6882.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___114_6882.FStar_TypeChecker_Env.dep_graph}) res)
in (match (uu____6873) with
| (pre_opt, res_t) -> begin
(

let uu____6893 = (encode_term_pred FStar_Pervasives_Native.None res_t env' app)
in (match (uu____6893) with
| (res_pred, decls') -> begin
(

let uu____6904 = (match (pre_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____6913 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____6913), ([])))
end
| FStar_Pervasives_Native.Some (pre) -> begin
(

let uu____6915 = (encode_formula pre env')
in (match (uu____6915) with
| (guard, decls0) -> begin
(

let uu____6926 = (FStar_SMTEncoding_Util.mk_and_l ((guard)::guards))
in ((uu____6926), (decls0)))
end))
end)
in (match (uu____6904) with
| (guards1, guard_decls) -> begin
(

let t_interp = (

let uu____6934 = (

let uu____6945 = (FStar_SMTEncoding_Util.mkImp ((guards1), (res_pred)))
in ((((app)::[])::[]), (vars), (uu____6945)))
in (FStar_SMTEncoding_Util.mkForall uu____6934))
in (

let cvars = (

let uu____6961 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right uu____6961 (FStar_List.filter (fun uu____6987 -> (match (uu____6987) with
| (x, uu____6993) -> begin
(Prims.op_disEquality x (FStar_Pervasives_Native.fst fsym))
end)))))
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), ((fsym)::cvars), (t_interp)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____7006 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____7006) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
(

let uu____7014 = (

let uu____7015 = (

let uu____7022 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((cache_entry.cache_symbol_name), (uu____7022)))
in (FStar_SMTEncoding_Util.mkApp uu____7015))
in ((uu____7014), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append guard_decls (use_cache_entry cache_entry)))))))
end
| FStar_Pervasives_Native.None -> begin
(

let tsym = (

let uu____7040 = (

let uu____7041 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_arrow_" uu____7041))
in (varops.mk_unique uu____7040))
in (

let cvar_sorts = (FStar_List.map FStar_Pervasives_Native.snd cvars)
in (

let caption = (

let uu____7050 = (FStar_Options.log_queries ())
in (match (uu____7050) with
| true -> begin
(

let uu____7051 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in FStar_Pervasives_Native.Some (uu____7051))
end
| uu____7052 -> begin
FStar_Pervasives_Native.None
end))
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (caption)))
in (

let t1 = (

let uu____7057 = (

let uu____7064 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((tsym), (uu____7064)))
in (FStar_SMTEncoding_Util.mkApp uu____7057))
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t1 FStar_SMTEncoding_Term.mk_Term_type)
in (

let k_assumption = (

let a_name = (Prims.strcat "kinding_" tsym)
in (

let uu____7076 = (

let uu____7083 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((uu____7083), (FStar_Pervasives_Native.Some (a_name)), (a_name)))
in (FStar_SMTEncoding_Util.mkAssume uu____7076)))
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t1)
in (

let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t1)
in (

let pre_typing = (

let a_name = (Prims.strcat "pre_typing_" tsym)
in (

let uu____7096 = (

let uu____7103 = (

let uu____7104 = (

let uu____7115 = (

let uu____7116 = (

let uu____7121 = (

let uu____7122 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____7122))
in ((f_has_t), (uu____7121)))
in (FStar_SMTEncoding_Util.mkImp uu____7116))
in ((((f_has_t)::[])::[]), ((fsym)::cvars), (uu____7115)))
in (mkForall_fuel uu____7104))
in ((uu____7103), (FStar_Pervasives_Native.Some ("pre-typing for functions")), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____7096)))
in (

let t_interp1 = (

let a_name = (Prims.strcat "interpretation_" tsym)
in (

let uu____7137 = (

let uu____7144 = (

let uu____7145 = (

let uu____7156 = (FStar_SMTEncoding_Util.mkIff ((f_has_t_z), (t_interp)))
in ((((f_has_t_z)::[])::[]), ((fsym)::cvars), (uu____7156)))
in (FStar_SMTEncoding_Util.mkForall uu____7145))
in ((uu____7144), (FStar_Pervasives_Native.Some (a_name)), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____7137)))
in (

let t_decls1 = (FStar_List.append ((tdecl)::decls) (FStar_List.append decls' (FStar_List.append guard_decls ((k_assumption)::(pre_typing)::(t_interp1)::[]))))
in ((

let uu____7173 = (mk_cache_entry env tsym cvar_sorts t_decls1)
in (FStar_Util.smap_add env.cache tkey_hash uu____7173));
((t1), (t_decls1));
)))))))))))))
end))))))
end))
end))
end)))))
end))
end
| uu____7174 -> begin
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

let uu____7184 = (

let uu____7191 = (FStar_SMTEncoding_Term.mk_HasType t1 FStar_SMTEncoding_Term.mk_Term_type)
in ((uu____7191), (FStar_Pervasives_Native.Some ("Typing for non-total arrows")), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____7184)))
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

let uu____7201 = (

let uu____7208 = (

let uu____7209 = (

let uu____7220 = (

let uu____7221 = (

let uu____7226 = (

let uu____7227 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____7227))
in ((f_has_t), (uu____7226)))
in (FStar_SMTEncoding_Util.mkImp uu____7221))
in ((((f_has_t)::[])::[]), ((fsym)::[]), (uu____7220)))
in (mkForall_fuel uu____7209))
in ((uu____7208), (FStar_Pervasives_Native.Some (a_name)), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____7201)))
in ((t1), ((tdecl)::(t_kinding)::(t_interp)::[]))))))))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (uu____7244) -> begin
(

let uu____7251 = (

let uu____7256 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)
in (match (uu____7256) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.pos = uu____7263; FStar_Syntax_Syntax.vars = uu____7264} -> begin
(

let uu____7271 = (FStar_Syntax_Subst.open_term ((((x), (FStar_Pervasives_Native.None)))::[]) f)
in (match (uu____7271) with
| (b, f1) -> begin
(

let uu____7290 = (

let uu____7291 = (FStar_List.hd b)
in (FStar_Pervasives_Native.fst uu____7291))
in ((uu____7290), (f1)))
end))
end
| uu____7300 -> begin
(failwith "impossible")
end))
in (match (uu____7251) with
| (x, f) -> begin
(

let uu____7311 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (uu____7311) with
| (base_t, decls) -> begin
(

let uu____7322 = (gen_term_var env x)
in (match (uu____7322) with
| (x1, xtm, env') -> begin
(

let uu____7336 = (encode_formula f env')
in (match (uu____7336) with
| (refinement, decls') -> begin
(

let uu____7347 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____7347) with
| (fsym, fterm) -> begin
(

let tm_has_type_with_fuel = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (FStar_Pervasives_Native.Some (fterm)) xtm base_t)
in (

let encoding = (FStar_SMTEncoding_Util.mkAnd ((tm_has_type_with_fuel), (refinement)))
in (

let cvars = (

let uu____7367 = (

let uu____7374 = (FStar_SMTEncoding_Term.free_variables refinement)
in (

let uu____7381 = (FStar_SMTEncoding_Term.free_variables tm_has_type_with_fuel)
in (FStar_List.append uu____7374 uu____7381)))
in (FStar_Util.remove_dups FStar_SMTEncoding_Term.fv_eq uu____7367))
in (

let cvars1 = (FStar_All.pipe_right cvars (FStar_List.filter (fun uu____7422 -> (match (uu____7422) with
| (y, uu____7428) -> begin
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

let uu____7455 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____7455) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
(

let uu____7463 = (

let uu____7464 = (

let uu____7471 = (FStar_All.pipe_right cvars1 (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((cache_entry.cache_symbol_name), (uu____7471)))
in (FStar_SMTEncoding_Util.mkApp uu____7464))
in ((uu____7463), ((FStar_List.append decls (FStar_List.append decls' (use_cache_entry cache_entry))))))
end
| FStar_Pervasives_Native.None -> begin
(

let module_name = env.current_module_name
in (

let tsym = (

let uu____7490 = (

let uu____7491 = (

let uu____7492 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "_Tm_refine_" uu____7492))
in (Prims.strcat module_name uu____7491))
in (varops.mk_unique uu____7490))
in (

let cvar_sorts = (FStar_List.map FStar_Pervasives_Native.snd cvars1)
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let t1 = (

let uu____7504 = (

let uu____7511 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars1)
in ((tsym), (uu____7511)))
in (FStar_SMTEncoding_Util.mkApp uu____7504))
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

let uu____7526 = (

let uu____7533 = (

let uu____7534 = (

let uu____7545 = (FStar_SMTEncoding_Util.mkIff ((t_haseq_ref), (t_haseq_base)))
in ((((t_haseq_ref)::[])::[]), (cvars1), (uu____7545)))
in (FStar_SMTEncoding_Util.mkForall uu____7534))
in ((uu____7533), (FStar_Pervasives_Native.Some ((Prims.strcat "haseq for " tsym))), ((Prims.strcat "haseq" tsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____7526))
in (

let t_kinding = (

let uu____7555 = (

let uu____7562 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars1), (t_has_kind)))
in ((uu____7562), (FStar_Pervasives_Native.Some ("refinement kinding")), ((Prims.strcat "refinement_kinding_" tsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____7555))
in (

let t_interp = (

let uu____7572 = (

let uu____7579 = (

let uu____7580 = (

let uu____7591 = (FStar_SMTEncoding_Util.mkIff ((x_has_t), (encoding)))
in ((((x_has_t)::[])::[]), ((ffv)::(xfv)::cvars1), (uu____7591)))
in (FStar_SMTEncoding_Util.mkForall uu____7580))
in (

let uu____7608 = (

let uu____7609 = (FStar_Syntax_Print.term_to_string t0)
in FStar_Pervasives_Native.Some (uu____7609))
in ((uu____7579), (uu____7608), ((Prims.strcat "refinement_interpretation_" tsym)))))
in (FStar_SMTEncoding_Util.mkAssume uu____7572))
in (

let t_decls1 = (FStar_List.append decls (FStar_List.append decls' ((tdecl)::(t_kinding)::(t_interp)::(t_haseq1)::[])))
in ((

let uu____7614 = (mk_cache_entry env tsym cvar_sorts t_decls1)
in (FStar_Util.smap_add env.cache tkey_hash uu____7614));
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

let uu____7617 = (FStar_Syntax_Unionfind.uvar_id uv.FStar_Syntax_Syntax.ctx_uvar_head)
in (FStar_SMTEncoding_Util.mk_Term_uvar uu____7617))
in (

let uu____7618 = (encode_term_pred FStar_Pervasives_Native.None uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm)
in (match (uu____7618) with
| (t_has_k, decls) -> begin
(

let d = (

let uu____7630 = (

let uu____7637 = (

let uu____7638 = (

let uu____7639 = (

let uu____7640 = (FStar_Syntax_Unionfind.uvar_id uv.FStar_Syntax_Syntax.ctx_uvar_head)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____7640))
in (FStar_Util.format1 "uvar_typing_%s" uu____7639))
in (varops.mk_unique uu____7638))
in ((t_has_k), (FStar_Pervasives_Native.Some ("Uvar typing")), (uu____7637)))
in (FStar_SMTEncoding_Util.mkAssume uu____7630))
in ((ttm), ((FStar_List.append decls ((d)::[])))))
end)))
end
| FStar_Syntax_Syntax.Tm_app (uu____7641) -> begin
(

let uu____7656 = (FStar_Syntax_Util.head_and_args t0)
in (match (uu____7656) with
| (head1, args_e) -> begin
(

let uu____7697 = (

let uu____7710 = (

let uu____7711 = (FStar_Syntax_Subst.compress head1)
in uu____7711.FStar_Syntax_Syntax.n)
in ((uu____7710), (args_e)))
in (match (uu____7697) with
| uu____7726 when (head_redex env head1) -> begin
(

let uu____7739 = (whnf env t)
in (encode_term uu____7739 env))
end
| uu____7740 when (is_arithmetic_primitive head1 args_e) -> begin
(encode_arith_term env head1 args_e)
end
| uu____7759 when (is_BitVector_primitive head1 args_e) -> begin
(encode_BitVector_term env head1 args_e)
end
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____7773; FStar_Syntax_Syntax.vars = uu____7774}, uu____7775), (uu____7776)::((v1, uu____7778))::((v2, uu____7780))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.lexcons_lid) -> begin
(

let uu____7831 = (encode_term v1 env)
in (match (uu____7831) with
| (v11, decls1) -> begin
(

let uu____7842 = (encode_term v2 env)
in (match (uu____7842) with
| (v21, decls2) -> begin
(

let uu____7853 = (FStar_SMTEncoding_Util.mk_LexCons v11 v21)
in ((uu____7853), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____7855)::((v1, uu____7857))::((v2, uu____7859))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.lexcons_lid) -> begin
(

let uu____7906 = (encode_term v1 env)
in (match (uu____7906) with
| (v11, decls1) -> begin
(

let uu____7917 = (encode_term v2 env)
in (match (uu____7917) with
| (v21, decls2) -> begin
(

let uu____7928 = (FStar_SMTEncoding_Util.mk_LexCons v11 v21)
in ((uu____7928), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of), ((arg, uu____7930))::[]) -> begin
(encode_const (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos)) env)
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of), ((arg, uu____7956))::((rng, uu____7958))::[]) -> begin
(encode_term arg env)
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), uu____7993) -> begin
(

let e0 = (

let uu____8011 = (FStar_List.hd args_e)
in (FStar_TypeChecker_Util.reify_body_with_arg env.tcenv head1 uu____8011))
in ((

let uu____8019 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____8019) with
| true -> begin
(

let uu____8020 = (FStar_Syntax_Print.term_to_string e0)
in (FStar_Util.print1 "Result of normalization %s\n" uu____8020))
end
| uu____8021 -> begin
()
end));
(

let e = (

let uu____8025 = (

let uu____8030 = (FStar_TypeChecker_Util.remove_reify e0)
in (

let uu____8031 = (FStar_List.tl args_e)
in (FStar_Syntax_Syntax.mk_Tm_app uu____8030 uu____8031)))
in (uu____8025 FStar_Pervasives_Native.None t0.FStar_Syntax_Syntax.pos))
in (encode_term e env));
))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____8040)), ((arg, uu____8042))::[]) -> begin
(encode_term arg env)
end
| uu____8067 -> begin
(

let uu____8080 = (encode_args args_e env)
in (match (uu____8080) with
| (args, decls) -> begin
(

let encode_partial_app = (fun ht_opt -> (

let uu____8137 = (encode_term head1 env)
in (match (uu____8137) with
| (head2, decls') -> begin
(

let app_tm = (mk_Apply_args head2 args)
in (match (ht_opt) with
| FStar_Pervasives_Native.None -> begin
((app_tm), ((FStar_List.append decls decls')))
end
| FStar_Pervasives_Native.Some (formals, c) -> begin
(

let uu____8201 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (uu____8201) with
| (formals1, rest) -> begin
(

let subst1 = (FStar_List.map2 (fun uu____8279 uu____8280 -> (match (((uu____8279), (uu____8280))) with
| ((bv, uu____8302), (a, uu____8304)) -> begin
FStar_Syntax_Syntax.NT (((bv), (a)))
end)) formals1 args_e)
in (

let ty = (

let uu____8322 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right uu____8322 (FStar_Syntax_Subst.subst subst1)))
in (

let uu____8323 = (encode_term_pred FStar_Pervasives_Native.None ty env app_tm)
in (match (uu____8323) with
| (has_type, decls'') -> begin
(

let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (

let e_typing = (

let uu____8338 = (

let uu____8345 = (FStar_SMTEncoding_Util.mkForall ((((has_type)::[])::[]), (cvars), (has_type)))
in (

let uu____8354 = (

let uu____8355 = (

let uu____8356 = (

let uu____8357 = (FStar_SMTEncoding_Term.hash_of_term app_tm)
in (FStar_Util.digest_of_string uu____8357))
in (Prims.strcat "partial_app_typing_" uu____8356))
in (varops.mk_unique uu____8355))
in ((uu____8345), (FStar_Pervasives_Native.Some ("Partial app typing")), (uu____8354))))
in (FStar_SMTEncoding_Util.mkAssume uu____8338))
in ((app_tm), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' ((e_typing)::[]))))))))
end))))
end))
end))
end)))
in (

let encode_full_app = (fun fv -> (

let uu____8374 = (lookup_free_var_sym env fv)
in (match (uu____8374) with
| (fname, fuel_args, arity) -> begin
(

let tm = (maybe_curry_app t0.FStar_Syntax_Syntax.pos fname arity (FStar_List.append fuel_args args))
in ((tm), (decls)))
end)))
in (

let head2 = (FStar_Syntax_Subst.compress head1)
in (

let head_type = (match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (x); FStar_Syntax_Syntax.pos = uu____8406; FStar_Syntax_Syntax.vars = uu____8407}, uu____8408) -> begin
FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____8419; FStar_Syntax_Syntax.vars = uu____8420}, uu____8421) -> begin
(

let uu____8426 = (

let uu____8427 = (

let uu____8432 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____8432 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____8427 FStar_Pervasives_Native.snd))
in FStar_Pervasives_Native.Some (uu____8426))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____8462 = (

let uu____8463 = (

let uu____8468 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____8468 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____8463 FStar_Pervasives_Native.snd))
in FStar_Pervasives_Native.Some (uu____8462))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____8497, (FStar_Util.Inl (t1), uu____8499), uu____8500) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____8549, (FStar_Util.Inr (c), uu____8551), uu____8552) -> begin
FStar_Pervasives_Native.Some ((FStar_Syntax_Util.comp_result c))
end
| uu____8601 -> begin
FStar_Pervasives_Native.None
end)
in (match (head_type) with
| FStar_Pervasives_Native.None -> begin
(encode_partial_app FStar_Pervasives_Native.None)
end
| FStar_Pervasives_Native.Some (head_type1) -> begin
(

let head_type2 = (

let uu____8628 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type1)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine uu____8628))
in (

let uu____8629 = (curried_arrow_formals_comp head_type2)
in (match (uu____8629) with
| (formals, c) -> begin
(match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____8663; FStar_Syntax_Syntax.vars = uu____8664}, uu____8665) when (Prims.op_Equality (FStar_List.length formals) (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (Prims.op_Equality (FStar_List.length formals) (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| uu____8679 -> begin
(match (((FStar_List.length formals) > (FStar_List.length args))) with
| true -> begin
(encode_partial_app (FStar_Pervasives_Native.Some (((formals), (c)))))
end
| uu____8708 -> begin
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

let uu____8744 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____8744) with
| (bs1, body1, opening) -> begin
(

let fallback = (fun uu____8769 -> (

let f = (varops.fresh "Tm_abs")
in (

let decl = FStar_SMTEncoding_Term.DeclFun (((f), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Imprecise function encoding"))))
in (

let uu____8774 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in ((uu____8774), ((decl)::[]))))))
in (

let is_impure = (fun rc -> (

let uu____8783 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv rc.FStar_Syntax_Syntax.residual_effect)
in (FStar_All.pipe_right uu____8783 Prims.op_Negation)))
in (

let codomain_eff = (fun rc -> (

let res_typ = (match (rc.FStar_Syntax_Syntax.residual_typ) with
| FStar_Pervasives_Native.None -> begin
(

let uu____8795 = (

let uu____8808 = (FStar_TypeChecker_Env.get_range env.tcenv)
in (FStar_TypeChecker_Util.new_implicit_var "SMTEncoding codomain" uu____8808 env.tcenv FStar_Syntax_Util.ktype0))
in (match (uu____8795) with
| (t1, uu____8810, uu____8811) -> begin
t1
end))
end
| FStar_Pervasives_Native.Some (t1) -> begin
t1
end)
in (

let uu____8829 = (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_Tot_lid)
in (match (uu____8829) with
| true -> begin
(

let uu____8832 = (FStar_Syntax_Syntax.mk_Total res_typ)
in FStar_Pervasives_Native.Some (uu____8832))
end
| uu____8833 -> begin
(

let uu____8834 = (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_GTot_lid)
in (match (uu____8834) with
| true -> begin
(

let uu____8837 = (FStar_Syntax_Syntax.mk_GTotal res_typ)
in FStar_Pervasives_Native.Some (uu____8837))
end
| uu____8838 -> begin
FStar_Pervasives_Native.None
end))
end))))
in (match (lopt) with
| FStar_Pervasives_Native.None -> begin
((

let uu____8844 = (

let uu____8849 = (

let uu____8850 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)" uu____8850))
in ((FStar_Errors.Warning_FunctionLiteralPrecisionLoss), (uu____8849)))
in (FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____8844));
(fallback ());
)
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____8852 = ((is_impure rc) && (

let uu____8854 = (FStar_TypeChecker_Env.is_reifiable env.tcenv rc)
in (not (uu____8854))))
in (match (uu____8852) with
| true -> begin
(fallback ())
end
| uu____8859 -> begin
(

let cache_size = (FStar_Util.smap_size env.cache)
in (

let uu____8861 = (encode_binders FStar_Pervasives_Native.None bs1 env)
in (match (uu____8861) with
| (vars, guards, envbody, decls, uu____8886) -> begin
(

let body2 = (

let uu____8900 = (FStar_TypeChecker_Env.is_reifiable env.tcenv rc)
in (match (uu____8900) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env.tcenv body1)
end
| uu____8901 -> begin
body1
end))
in (

let uu____8902 = (encode_term body2 envbody)
in (match (uu____8902) with
| (body3, decls') -> begin
(

let uu____8913 = (

let uu____8920 = (codomain_eff rc)
in (match (uu____8920) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), ([]))
end
| FStar_Pervasives_Native.Some (c) -> begin
(

let tfun = (FStar_Syntax_Util.arrow bs1 c)
in (

let uu____8935 = (encode_term tfun env)
in (match (uu____8935) with
| (t1, decls1) -> begin
((FStar_Pervasives_Native.Some (t1)), (decls1))
end)))
end))
in (match (uu____8913) with
| (arrow_t_opt, decls'') -> begin
(

let key_body = (

let uu____8961 = (

let uu____8972 = (

let uu____8973 = (

let uu____8978 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____8978), (body3)))
in (FStar_SMTEncoding_Util.mkImp uu____8973))
in (([]), (vars), (uu____8972)))
in (FStar_SMTEncoding_Util.mkForall uu____8961))
in (

let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (

let cvars1 = (match (arrow_t_opt) with
| FStar_Pervasives_Native.None -> begin
cvars
end
| FStar_Pervasives_Native.Some (t1) -> begin
(

let uu____9000 = (

let uu____9007 = (FStar_SMTEncoding_Term.free_variables t1)
in (FStar_List.append uu____9007 cvars))
in (FStar_Util.remove_dups FStar_SMTEncoding_Term.fv_eq uu____9000))
end)
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), (cvars1), (key_body)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____9030 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____9030) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
(

let uu____9038 = (

let uu____9039 = (

let uu____9046 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars1)
in ((cache_entry.cache_symbol_name), (uu____9046)))
in (FStar_SMTEncoding_Util.mkApp uu____9039))
in ((uu____9038), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' (use_cache_entry cache_entry)))))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____9055 = (is_an_eta_expansion env vars body3)
in (match (uu____9055) with
| FStar_Pervasives_Native.Some (t1) -> begin
(

let decls1 = (

let uu____9064 = (

let uu____9065 = (FStar_Util.smap_size env.cache)
in (Prims.op_Equality uu____9065 cache_size))
in (match (uu____9064) with
| true -> begin
[]
end
| uu____9066 -> begin
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

let uu____9077 = (

let uu____9078 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_abs_" uu____9078))
in (varops.mk_unique uu____9077))
in (Prims.strcat module_name (Prims.strcat "_" fsym))))
in (

let fdecl = FStar_SMTEncoding_Term.DeclFun (((fsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let f = (

let uu____9083 = (

let uu____9090 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars1)
in ((fsym), (uu____9090)))
in (FStar_SMTEncoding_Util.mkApp uu____9083))
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

let uu____9108 = (

let uu____9109 = (

let uu____9116 = (FStar_SMTEncoding_Util.mkForall ((((f)::[])::[]), (cvars1), (f_has_t)))
in ((uu____9116), (FStar_Pervasives_Native.Some (a_name)), (a_name)))
in (FStar_SMTEncoding_Util.mkAssume uu____9109))
in (uu____9108)::[])))
end)
in (

let interp_f = (

let a_name = (Prims.strcat "interpretation_" fsym)
in (

let uu____9127 = (

let uu____9134 = (

let uu____9135 = (

let uu____9146 = (FStar_SMTEncoding_Util.mkEq ((app), (body3)))
in ((((app)::[])::[]), ((FStar_List.append vars cvars1)), (uu____9146)))
in (FStar_SMTEncoding_Util.mkForall uu____9135))
in ((uu____9134), (FStar_Pervasives_Native.Some (a_name)), (a_name)))
in (FStar_SMTEncoding_Util.mkAssume uu____9127)))
in (

let f_decls = (FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' (FStar_List.append ((fdecl)::typing_f) ((interp_f)::[])))))
in ((

let uu____9159 = (mk_cache_entry env fsym cvar_sorts f_decls)
in (FStar_Util.smap_add env.cache tkey_hash uu____9159));
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
| FStar_Syntax_Syntax.Tm_let ((uu____9160, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____9161); FStar_Syntax_Syntax.lbunivs = uu____9162; FStar_Syntax_Syntax.lbtyp = uu____9163; FStar_Syntax_Syntax.lbeff = uu____9164; FStar_Syntax_Syntax.lbdef = uu____9165; FStar_Syntax_Syntax.lbattrs = uu____9166; FStar_Syntax_Syntax.lbpos = uu____9167})::uu____9168), uu____9169) -> begin
(failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____9199; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____9201; FStar_Syntax_Syntax.lbdef = e1; FStar_Syntax_Syntax.lbattrs = uu____9203; FStar_Syntax_Syntax.lbpos = uu____9204})::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (uu____9228) -> begin
((FStar_Errors.diag t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions, and their enclosings let bindings (including the top-level let) are not yet fully encoded to the SMT solver; you may not be able to prove some facts");
(FStar_Exn.raise Inner_let_rec);
)
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end);
)))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (

let uu____9298 = (

let uu____9303 = (FStar_Syntax_Util.ascribe e1 ((FStar_Util.Inl (t1)), (FStar_Pervasives_Native.None)))
in (encode_term uu____9303 env))
in (match (uu____9298) with
| (ee1, decls1) -> begin
(

let uu____9328 = (FStar_Syntax_Subst.open_term ((((x), (FStar_Pervasives_Native.None)))::[]) e2)
in (match (uu____9328) with
| (xs, e21) -> begin
(

let uu____9347 = (FStar_List.hd xs)
in (match (uu____9347) with
| (x1, uu____9361) -> begin
(

let env' = (push_term_var env x1 ee1)
in (

let uu____9363 = (encode_body e21 env')
in (match (uu____9363) with
| (ee2, decls2) -> begin
((ee2), ((FStar_List.append decls1 decls2)))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (

let uu____9393 = (

let uu____9400 = (

let uu____9401 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.null_bv uu____9401))
in (gen_term_var env uu____9400))
in (match (uu____9393) with
| (scrsym, scr', env1) -> begin
(

let uu____9409 = (encode_term e env1)
in (match (uu____9409) with
| (scr, decls) -> begin
(

let uu____9420 = (

let encode_branch = (fun b uu____9449 -> (match (uu____9449) with
| (else_case, decls1) -> begin
(

let uu____9468 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____9468) with
| (p, w, br) -> begin
(

let uu____9494 = (encode_pat env1 p)
in (match (uu____9494) with
| (env0, pattern) -> begin
(

let guard = (pattern.guard scr')
in (

let projections = (pattern.projections scr')
in (

let env2 = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env2 uu____9531 -> (match (uu____9531) with
| (x, t) -> begin
(push_term_var env2 x t)
end)) env1))
in (

let uu____9538 = (match (w) with
| FStar_Pervasives_Native.None -> begin
((guard), ([]))
end
| FStar_Pervasives_Native.Some (w1) -> begin
(

let uu____9554 = (encode_term w1 env2)
in (match (uu____9554) with
| (w2, decls2) -> begin
(

let uu____9565 = (

let uu____9566 = (

let uu____9571 = (

let uu____9572 = (

let uu____9577 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue)
in ((w2), (uu____9577)))
in (FStar_SMTEncoding_Util.mkEq uu____9572))
in ((guard), (uu____9571)))
in (FStar_SMTEncoding_Util.mkAnd uu____9566))
in ((uu____9565), (decls2)))
end))
end)
in (match (uu____9538) with
| (guard1, decls2) -> begin
(

let uu____9586 = (encode_br br env2)
in (match (uu____9586) with
| (br1, decls3) -> begin
(

let uu____9599 = (FStar_SMTEncoding_Util.mkITE ((guard1), (br1), (else_case)))
in ((uu____9599), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end)))))
end))
end))
end))
in (FStar_List.fold_right encode_branch pats ((default_case), (decls))))
in (match (uu____9420) with
| (match_tm, decls1) -> begin
(

let uu____9620 = (FStar_SMTEncoding_Term.mkLet' (((((((scrsym), (FStar_SMTEncoding_Term.Term_sort))), (scr)))::[]), (match_tm)) FStar_Range.dummyRange)
in ((uu____9620), (decls1)))
end))
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> ((

let uu____9642 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____9642) with
| true -> begin
(

let uu____9643 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" uu____9643))
end
| uu____9644 -> begin
()
end));
(

let uu____9645 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (uu____9645) with
| (vars, pat_term) -> begin
(

let uu____9662 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun uu____9715 v1 -> (match (uu____9715) with
| (env1, vars1) -> begin
(

let uu____9767 = (gen_term_var env1 v1)
in (match (uu____9767) with
| (xx, uu____9789, env2) -> begin
((env2), ((((v1), (((xx), (FStar_SMTEncoding_Term.Term_sort)))))::vars1))
end))
end)) ((env), ([]))))
in (match (uu____9662) with
| (env1, vars1) -> begin
(

let rec mk_guard = (fun pat1 scrutinee -> (match (pat1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_var (uu____9872) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_wild (uu____9873) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____9874) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____9882 = (encode_const c env1)
in (match (uu____9882) with
| (tm, decls) -> begin
((match (decls) with
| (uu____9896)::uu____9897 -> begin
(failwith "Unexpected encoding of constant pattern")
end
| uu____9900 -> begin
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

let uu____9923 = (FStar_TypeChecker_Env.datacons_of_typ env1.tcenv tc_name)
in (match (uu____9923) with
| (uu____9930, (uu____9931)::[]) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| uu____9934 -> begin
(mk_data_tester env1 f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
end)))
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____9967 -> (match (uu____9967) with
| (arg, uu____9975) -> begin
(

let proj = (primitive_projector_by_pos env1.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____9981 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_guard arg uu____9981)))
end))))
in (FStar_SMTEncoding_Util.mk_and_l ((is_f)::sub_term_guards))))
end))
in (

let rec mk_projections = (fun pat1 scrutinee -> (match (pat1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (x, uu____10012) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_constant (uu____10043) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let uu____10066 = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____10110 -> (match (uu____10110) with
| (arg, uu____10124) -> begin
(

let proj = (primitive_projector_by_pos env1.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____10130 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_projections arg uu____10130)))
end))))
in (FStar_All.pipe_right uu____10066 FStar_List.flatten))
end))
in (

let pat_term1 = (fun uu____10160 -> (encode_term pat_term env1))
in (

let pattern = {pat_vars = vars1; pat_term = pat_term1; guard = (mk_guard pat); projections = (mk_projections pat)}
in ((env1), (pattern))))))
end))
end));
))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (

let uu____10170 = (FStar_All.pipe_right l (FStar_List.fold_left (fun uu____10214 uu____10215 -> (match (((uu____10214), (uu____10215))) with
| ((tms, decls), (t, uu____10251)) -> begin
(

let uu____10272 = (encode_term t env)
in (match (uu____10272) with
| (t1, decls') -> begin
(((t1)::tms), ((FStar_List.append decls decls')))
end))
end)) (([]), ([]))))
in (match (uu____10170) with
| (l1, decls) -> begin
(((FStar_List.rev l1)), (decls))
end)))
and encode_function_type_as_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let list_elements1 = (fun e -> (

let uu____10329 = (FStar_Syntax_Util.list_elements e)
in (match (uu____10329) with
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

let uu____10352 = (

let uu____10367 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right uu____10367 FStar_Syntax_Util.head_and_args))
in (match (uu____10352) with
| (head1, args) -> begin
(

let uu____10406 = (

let uu____10419 = (

let uu____10420 = (FStar_Syntax_Util.un_uinst head1)
in uu____10420.FStar_Syntax_Syntax.n)
in ((uu____10419), (args)))
in (match (uu____10406) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((uu____10434, uu____10435))::((e, uu____10437))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpat_lid) -> begin
e
end
| uu____10472 -> begin
(failwith "Unexpected pattern term")
end))
end)))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements1 p)
in (

let smt_pat_or = (fun t1 -> (

let uu____10512 = (

let uu____10527 = (FStar_Syntax_Util.unmeta t1)
in (FStar_All.pipe_right uu____10527 FStar_Syntax_Util.head_and_args))
in (match (uu____10512) with
| (head1, args) -> begin
(

let uu____10568 = (

let uu____10581 = (

let uu____10582 = (FStar_Syntax_Util.un_uinst head1)
in uu____10582.FStar_Syntax_Syntax.n)
in ((uu____10581), (args)))
in (match (uu____10568) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, uu____10599))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpatOr_lid) -> begin
FStar_Pervasives_Native.Some (e)
end
| uu____10626 -> begin
FStar_Pervasives_Native.None
end))
end)))
in (match (elts) with
| (t1)::[] -> begin
(

let uu____10648 = (smt_pat_or t1)
in (match (uu____10648) with
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____10664 = (list_elements1 e)
in (FStar_All.pipe_right uu____10664 (FStar_List.map (fun branch1 -> (

let uu____10682 = (list_elements1 branch1)
in (FStar_All.pipe_right uu____10682 (FStar_List.map one_pat)))))))
end
| uu____10693 -> begin
(

let uu____10698 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____10698)::[])
end))
end
| uu____10719 -> begin
(

let uu____10722 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____10722)::[])
end))))
in (

let uu____10743 = (

let uu____10762 = (

let uu____10763 = (FStar_Syntax_Subst.compress t)
in uu____10763.FStar_Syntax_Syntax.n)
in (match (uu____10762) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____10802 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____10802) with
| (binders1, c1) -> begin
(match (c1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____10845; FStar_Syntax_Syntax.effect_name = uu____10846; FStar_Syntax_Syntax.result_typ = uu____10847; FStar_Syntax_Syntax.effect_args = ((pre, uu____10849))::((post, uu____10851))::((pats, uu____10853))::[]; FStar_Syntax_Syntax.flags = uu____10854}) -> begin
(

let uu____10895 = (lemma_pats pats)
in ((binders1), (pre), (post), (uu____10895)))
end
| uu____10912 -> begin
(failwith "impos")
end)
end))
end
| uu____10931 -> begin
(failwith "Impos")
end))
in (match (uu____10743) with
| (binders, pre, post, patterns) -> begin
(

let env1 = (

let uu___115_10979 = env
in {bindings = uu___115_10979.bindings; depth = uu___115_10979.depth; tcenv = uu___115_10979.tcenv; warn = uu___115_10979.warn; cache = uu___115_10979.cache; nolabels = uu___115_10979.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___115_10979.encode_non_total_function_typ; current_module_name = uu___115_10979.current_module_name})
in (

let uu____10980 = (encode_binders FStar_Pervasives_Native.None binders env1)
in (match (uu____10980) with
| (vars, guards, env2, decls, uu____11005) -> begin
(

let uu____11018 = (

let uu____11033 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch1 -> (

let uu____11087 = (

let uu____11098 = (FStar_All.pipe_right branch1 (FStar_List.map (fun t1 -> (encode_smt_pattern t1 env2))))
in (FStar_All.pipe_right uu____11098 FStar_List.unzip))
in (match (uu____11087) with
| (pats, decls1) -> begin
((pats), (decls1))
end)))))
in (FStar_All.pipe_right uu____11033 FStar_List.unzip))
in (match (uu____11018) with
| (pats, decls') -> begin
(

let decls'1 = (FStar_List.flatten decls')
in (

let post1 = (FStar_Syntax_Util.unthunk_lemma_post post)
in (

let env3 = (

let uu___116_11250 = env2
in {bindings = uu___116_11250.bindings; depth = uu___116_11250.depth; tcenv = uu___116_11250.tcenv; warn = uu___116_11250.warn; cache = uu___116_11250.cache; nolabels = true; use_zfuel_name = uu___116_11250.use_zfuel_name; encode_non_total_function_typ = uu___116_11250.encode_non_total_function_typ; current_module_name = uu___116_11250.current_module_name})
in (

let uu____11251 = (

let uu____11256 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula uu____11256 env3))
in (match (uu____11251) with
| (pre1, decls'') -> begin
(

let uu____11263 = (

let uu____11268 = (FStar_Syntax_Util.unmeta post1)
in (encode_formula uu____11268 env3))
in (match (uu____11263) with
| (post2, decls''') -> begin
(

let decls1 = (FStar_List.append decls (FStar_List.append (FStar_List.flatten decls'1) (FStar_List.append decls'' decls''')))
in (

let uu____11278 = (

let uu____11279 = (

let uu____11290 = (

let uu____11291 = (

let uu____11296 = (FStar_SMTEncoding_Util.mk_and_l ((pre1)::guards))
in ((uu____11296), (post2)))
in (FStar_SMTEncoding_Util.mkImp uu____11291))
in ((pats), (vars), (uu____11290)))
in (FStar_SMTEncoding_Util.mkForall uu____11279))
in ((uu____11278), (decls1))))
end))
end)))))
end))
end)))
end))))))
and encode_smt_pattern : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  env_t  ->  (FStar_SMTEncoding_Term.pat * FStar_SMTEncoding_Term.decl Prims.list) = (fun t env -> (

let uu____11305 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____11305) with
| (head1, args) -> begin
(

let head2 = (FStar_Syntax_Util.un_uinst head1)
in (match (((head2.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____11364)::((x, uu____11366))::((t1, uu____11368))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.has_type_lid) -> begin
(

let uu____11415 = (encode_term x env)
in (match (uu____11415) with
| (x1, decls) -> begin
(

let uu____11428 = (encode_term t1 env)
in (match (uu____11428) with
| (t2, decls') -> begin
(

let uu____11441 = (FStar_SMTEncoding_Term.mk_HasType x1 t2)
in ((uu____11441), ((FStar_List.append decls decls'))))
end))
end))
end
| uu____11444 -> begin
(encode_term t env)
end))
end)))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (

let debug1 = (fun phi1 -> (

let uu____11469 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____11469) with
| true -> begin
(

let uu____11470 = (FStar_Syntax_Print.tag_of_term phi1)
in (

let uu____11471 = (FStar_Syntax_Print.term_to_string phi1)
in (FStar_Util.print2 "Formula (%s)  %s\n" uu____11470 uu____11471)))
end
| uu____11472 -> begin
()
end)))
in (

let enc = (fun f r l -> (

let uu____11510 = (FStar_Util.fold_map (fun decls x -> (

let uu____11538 = (encode_term (FStar_Pervasives_Native.fst x) env)
in (match (uu____11538) with
| (t, decls') -> begin
(((FStar_List.append decls decls')), (t))
end))) [] l)
in (match (uu____11510) with
| (decls, args) -> begin
(

let uu____11567 = (

let uu___117_11568 = (f args)
in {FStar_SMTEncoding_Term.tm = uu___117_11568.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___117_11568.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____11567), (decls)))
end)))
in (

let const_op = (fun f r uu____11593 -> (

let uu____11596 = (f r)
in ((uu____11596), ([]))))
in (

let un_op = (fun f l -> (

let uu____11619 = (FStar_List.hd l)
in (FStar_All.pipe_left f uu____11619)))
in (

let bin_op = (fun f uu___93_11639 -> (match (uu___93_11639) with
| (t1)::(t2)::[] -> begin
(f ((t1), (t2)))
end
| uu____11650 -> begin
(failwith "Impossible")
end))
in (

let enc_prop_c = (fun f r l -> (

let uu____11690 = (FStar_Util.fold_map (fun decls uu____11713 -> (match (uu____11713) with
| (t, uu____11727) -> begin
(

let uu____11728 = (encode_formula t env)
in (match (uu____11728) with
| (phi1, decls') -> begin
(((FStar_List.append decls decls')), (phi1))
end))
end)) [] l)
in (match (uu____11690) with
| (decls, phis) -> begin
(

let uu____11757 = (

let uu___118_11758 = (f phis)
in {FStar_SMTEncoding_Term.tm = uu___118_11758.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___118_11758.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____11757), (decls)))
end)))
in (

let eq_op = (fun r args -> (

let rf = (FStar_List.filter (fun uu____11821 -> (match (uu____11821) with
| (a, q) -> begin
(match (q) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____11840)) -> begin
false
end
| uu____11841 -> begin
true
end)
end)) args)
in (match ((Prims.op_disEquality (FStar_List.length rf) (Prims.parse_int "2"))) with
| true -> begin
(

let uu____11857 = (FStar_Util.format1 "eq_op: got %s non-implicit arguments instead of 2?" (Prims.string_of_int (FStar_List.length rf)))
in (failwith uu____11857))
end
| uu____11870 -> begin
(

let uu____11871 = (enc (bin_op FStar_SMTEncoding_Util.mkEq))
in (uu____11871 r rf))
end)))
in (

let mk_imp1 = (fun r uu___94_11906 -> (match (uu___94_11906) with
| ((lhs, uu____11912))::((rhs, uu____11914))::[] -> begin
(

let uu____11941 = (encode_formula rhs env)
in (match (uu____11941) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____11956) -> begin
((l1), (decls1))
end
| uu____11961 -> begin
(

let uu____11962 = (encode_formula lhs env)
in (match (uu____11962) with
| (l2, decls2) -> begin
(

let uu____11973 = (FStar_SMTEncoding_Term.mkImp ((l2), (l1)) r)
in ((uu____11973), ((FStar_List.append decls1 decls2))))
end))
end)
end))
end
| uu____11974 -> begin
(failwith "impossible")
end))
in (

let mk_ite = (fun r uu___95_12001 -> (match (uu___95_12001) with
| ((guard, uu____12007))::((_then, uu____12009))::((_else, uu____12011))::[] -> begin
(

let uu____12048 = (encode_formula guard env)
in (match (uu____12048) with
| (g, decls1) -> begin
(

let uu____12059 = (encode_formula _then env)
in (match (uu____12059) with
| (t, decls2) -> begin
(

let uu____12070 = (encode_formula _else env)
in (match (uu____12070) with
| (e, decls3) -> begin
(

let res = (FStar_SMTEncoding_Term.mkITE ((g), (t), (e)) r)
in ((res), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end))
end))
end
| uu____12082 -> begin
(failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (

let uu____12111 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f uu____12111)))
in (

let connectives = (

let uu____12131 = (

let uu____12146 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd))
in ((FStar_Parser_Const.and_lid), (uu____12146)))
in (

let uu____12169 = (

let uu____12186 = (

let uu____12201 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr))
in ((FStar_Parser_Const.or_lid), (uu____12201)))
in (

let uu____12224 = (

let uu____12241 = (

let uu____12258 = (

let uu____12273 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff))
in ((FStar_Parser_Const.iff_lid), (uu____12273)))
in (

let uu____12296 = (

let uu____12313 = (

let uu____12330 = (

let uu____12345 = (enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot))
in ((FStar_Parser_Const.not_lid), (uu____12345)))
in (uu____12330)::(((FStar_Parser_Const.eq2_lid), (eq_op)))::(((FStar_Parser_Const.eq3_lid), (eq_op)))::(((FStar_Parser_Const.true_lid), ((const_op FStar_SMTEncoding_Term.mkTrue))))::(((FStar_Parser_Const.false_lid), ((const_op FStar_SMTEncoding_Term.mkFalse))))::[])
in (((FStar_Parser_Const.ite_lid), (mk_ite)))::uu____12313)
in (uu____12258)::uu____12296))
in (((FStar_Parser_Const.imp_lid), (mk_imp1)))::uu____12241)
in (uu____12186)::uu____12224))
in (uu____12131)::uu____12169))
in (

let rec fallback = (fun phi1 -> (match (phi1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(

let uu____12608 = (encode_formula phi' env)
in (match (uu____12608) with
| (phi2, decls) -> begin
(

let uu____12619 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled (((phi2), (msg), (r)))) r)
in ((uu____12619), (decls)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (uu____12620) -> begin
(

let uu____12627 = (FStar_Syntax_Util.unmeta phi1)
in (encode_formula uu____12627 env))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(

let uu____12666 = (encode_match e pats FStar_SMTEncoding_Util.mkFalse env encode_formula)
in (match (uu____12666) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____12678; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____12680; FStar_Syntax_Syntax.lbdef = e1; FStar_Syntax_Syntax.lbattrs = uu____12682; FStar_Syntax_Syntax.lbpos = uu____12683})::[]), e2) -> begin
(

let uu____12707 = (encode_let x t1 e1 e2 env encode_formula)
in (match (uu____12707) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let head2 = (FStar_Syntax_Util.un_uinst head1)
in (match (((head2.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____12754)::((x, uu____12756))::((t, uu____12758))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.has_type_lid) -> begin
(

let uu____12805 = (encode_term x env)
in (match (uu____12805) with
| (x1, decls) -> begin
(

let uu____12816 = (encode_term t env)
in (match (uu____12816) with
| (t1, decls') -> begin
(

let uu____12827 = (FStar_SMTEncoding_Term.mk_HasType x1 t1)
in ((uu____12827), ((FStar_List.append decls decls'))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((r, uu____12832))::((msg, uu____12834))::((phi2, uu____12836))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.labeled_lid) -> begin
(

let uu____12881 = (

let uu____12886 = (

let uu____12887 = (FStar_Syntax_Subst.compress r)
in uu____12887.FStar_Syntax_Syntax.n)
in (

let uu____12890 = (

let uu____12891 = (FStar_Syntax_Subst.compress msg)
in uu____12891.FStar_Syntax_Syntax.n)
in ((uu____12886), (uu____12890))))
in (match (uu____12881) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____12900))) -> begin
(

let phi3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((phi2), (FStar_Syntax_Syntax.Meta_labeled (((s), (r1), (false))))))) FStar_Pervasives_Native.None r1)
in (fallback phi3))
end
| uu____12906 -> begin
(fallback phi2)
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((t, uu____12913))::[]) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.auto_squash_lid)) -> begin
(encode_formula t env)
end
| uu____12938 when (head_redex env head2) -> begin
(

let uu____12951 = (whnf env phi1)
in (encode_formula uu____12951 env))
end
| uu____12952 -> begin
(

let uu____12965 = (encode_term phi1 env)
in (match (uu____12965) with
| (tt, decls) -> begin
(

let uu____12976 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___119_12979 = tt
in {FStar_SMTEncoding_Term.tm = uu___119_12979.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___119_12979.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi1.FStar_Syntax_Syntax.pos}))
in ((uu____12976), (decls)))
end))
end))
end
| uu____12980 -> begin
(

let uu____12981 = (encode_term phi1 env)
in (match (uu____12981) with
| (tt, decls) -> begin
(

let uu____12992 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___120_12995 = tt
in {FStar_SMTEncoding_Term.tm = uu___120_12995.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___120_12995.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi1.FStar_Syntax_Syntax.pos}))
in ((uu____12992), (decls)))
end))
end))
in (

let encode_q_body = (fun env1 bs ps body -> (

let uu____13039 = (encode_binders FStar_Pervasives_Native.None bs env1)
in (match (uu____13039) with
| (vars, guards, env2, decls, uu____13078) -> begin
(

let uu____13091 = (

let uu____13104 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let uu____13164 = (

let uu____13175 = (FStar_All.pipe_right p (FStar_List.map (fun uu____13215 -> (match (uu____13215) with
| (t, uu____13229) -> begin
(encode_smt_pattern t (

let uu___121_13235 = env2
in {bindings = uu___121_13235.bindings; depth = uu___121_13235.depth; tcenv = uu___121_13235.tcenv; warn = uu___121_13235.warn; cache = uu___121_13235.cache; nolabels = uu___121_13235.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___121_13235.encode_non_total_function_typ; current_module_name = uu___121_13235.current_module_name}))
end))))
in (FStar_All.pipe_right uu____13175 FStar_List.unzip))
in (match (uu____13164) with
| (p1, decls1) -> begin
((p1), ((FStar_List.flatten decls1)))
end)))))
in (FStar_All.pipe_right uu____13104 FStar_List.unzip))
in (match (uu____13091) with
| (pats, decls') -> begin
(

let uu____13344 = (encode_formula body env2)
in (match (uu____13344) with
| (body1, decls'') -> begin
(

let guards1 = (match (pats) with
| (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (gf), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____13376; FStar_SMTEncoding_Term.rng = uu____13377})::[])::[] when (

let uu____13392 = (FStar_Ident.text_of_lid FStar_Parser_Const.guard_free)
in (Prims.op_Equality uu____13392 gf)) -> begin
[]
end
| uu____13393 -> begin
guards
end)
in (

let uu____13398 = (FStar_SMTEncoding_Util.mk_and_l guards1)
in ((vars), (pats), (uu____13398), (body1), ((FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') decls''))))))
end))
end))
end)))
in ((debug1 phi);
(

let phi1 = (FStar_Syntax_Util.unascribe phi)
in (

let check_pattern_vars = (fun vars pats -> (

let pats1 = (FStar_All.pipe_right pats (FStar_List.map (fun uu____13462 -> (match (uu____13462) with
| (x, uu____13468) -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x)
end))))
in (match (pats1) with
| [] -> begin
()
end
| (hd1)::tl1 -> begin
(

let pat_vars = (

let uu____13476 = (FStar_Syntax_Free.names hd1)
in (FStar_List.fold_left (fun out x -> (

let uu____13488 = (FStar_Syntax_Free.names x)
in (FStar_Util.set_union out uu____13488))) uu____13476 tl1))
in (

let uu____13491 = (FStar_All.pipe_right vars (FStar_Util.find_opt (fun uu____13518 -> (match (uu____13518) with
| (b, uu____13524) -> begin
(

let uu____13525 = (FStar_Util.set_mem b pat_vars)
in (not (uu____13525)))
end))))
in (match (uu____13491) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (x, uu____13531) -> begin
(

let pos = (FStar_List.fold_left (fun out t -> (FStar_Range.union_ranges out t.FStar_Syntax_Syntax.pos)) hd1.FStar_Syntax_Syntax.pos tl1)
in (

let uu____13545 = (

let uu____13550 = (

let uu____13551 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "SMT pattern misses at least one bound variable: %s" uu____13551))
in ((FStar_Errors.Warning_SMTPatternMissingBoundVar), (uu____13550)))
in (FStar_Errors.log_issue pos uu____13545)))
end)))
end)))
in (

let uu____13552 = (FStar_Syntax_Util.destruct_typ_as_formula phi1)
in (match (uu____13552) with
| FStar_Pervasives_Native.None -> begin
(fallback phi1)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(

let uu____13561 = (FStar_All.pipe_right connectives (FStar_List.tryFind (fun uu____13627 -> (match (uu____13627) with
| (l, uu____13641) -> begin
(FStar_Ident.lid_equals op l)
end))))
in (match (uu____13561) with
| FStar_Pervasives_Native.None -> begin
(fallback phi1)
end
| FStar_Pervasives_Native.Some (uu____13680, f) -> begin
(f phi1.FStar_Syntax_Syntax.pos arms)
end))
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____13734 = (encode_q_body env vars pats body)
in (match (uu____13734) with
| (vars1, pats1, guard, body1, decls) -> begin
(

let tm = (

let uu____13779 = (

let uu____13790 = (FStar_SMTEncoding_Util.mkImp ((guard), (body1)))
in ((pats1), (vars1), (uu____13790)))
in (FStar_SMTEncoding_Term.mkForall uu____13779 phi1.FStar_Syntax_Syntax.pos))
in ((tm), (decls)))
end));
)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____13813 = (encode_q_body env vars pats body)
in (match (uu____13813) with
| (vars1, pats1, guard, body1, decls) -> begin
(

let uu____13857 = (

let uu____13858 = (

let uu____13869 = (FStar_SMTEncoding_Util.mkAnd ((guard), (body1)))
in ((pats1), (vars1), (uu____13869)))
in (FStar_SMTEncoding_Term.mkExists uu____13858 phi1.FStar_Syntax_Syntax.pos))
in ((uu____13857), (decls)))
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

let uu____13992 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____13992) with
| (asym, a) -> begin
(

let uu____13999 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____13999) with
| (xsym, x) -> begin
(

let uu____14006 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____14006) with
| (ysym, y) -> begin
(

let quant = (fun vars body x1 -> (

let xname_decl = (

let uu____14060 = (

let uu____14071 = (FStar_All.pipe_right vars (FStar_List.map FStar_Pervasives_Native.snd))
in ((x1), (uu____14071), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____14060))
in (

let xtok = (Prims.strcat x1 "@tok")
in (

let xtok_decl = FStar_SMTEncoding_Term.DeclFun (((xtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let xapp = (

let uu____14093 = (

let uu____14100 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((x1), (uu____14100)))
in (FStar_SMTEncoding_Util.mkApp uu____14093))
in (

let xtok1 = (FStar_SMTEncoding_Util.mkApp ((xtok), ([])))
in (

let xtok_app = (mk_Apply xtok1 vars)
in (

let uu____14113 = (

let uu____14116 = (

let uu____14119 = (

let uu____14122 = (

let uu____14123 = (

let uu____14130 = (

let uu____14131 = (

let uu____14142 = (FStar_SMTEncoding_Util.mkEq ((xapp), (body)))
in ((((xapp)::[])::[]), (vars), (uu____14142)))
in (FStar_SMTEncoding_Util.mkForall uu____14131))
in ((uu____14130), (FStar_Pervasives_Native.None), ((Prims.strcat "primitive_" x1))))
in (FStar_SMTEncoding_Util.mkAssume uu____14123))
in (

let uu____14151 = (

let uu____14154 = (

let uu____14155 = (

let uu____14162 = (

let uu____14163 = (

let uu____14174 = (FStar_SMTEncoding_Util.mkEq ((xtok_app), (xapp)))
in ((((xtok_app)::[])::[]), (vars), (uu____14174)))
in (FStar_SMTEncoding_Util.mkForall uu____14163))
in ((uu____14162), (FStar_Pervasives_Native.Some ("Name-token correspondence")), ((Prims.strcat "token_correspondence_" x1))))
in (FStar_SMTEncoding_Util.mkAssume uu____14155))
in (uu____14154)::[])
in (uu____14122)::uu____14151))
in (xtok_decl)::uu____14119)
in (xname_decl)::uu____14116)
in ((xtok1), ((FStar_List.length vars)), (uu____14113))))))))))
in (

let axy = (((asym), (FStar_SMTEncoding_Term.Term_sort)))::(((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let xy = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let qx = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let prims1 = (

let uu____14264 = (

let uu____14280 = (

let uu____14293 = (

let uu____14294 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____14294))
in (quant axy uu____14293))
in ((FStar_Parser_Const.op_Eq), (uu____14280)))
in (

let uu____14306 = (

let uu____14324 = (

let uu____14340 = (

let uu____14353 = (

let uu____14354 = (

let uu____14355 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_SMTEncoding_Util.mkNot uu____14355))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____14354))
in (quant axy uu____14353))
in ((FStar_Parser_Const.op_notEq), (uu____14340)))
in (

let uu____14367 = (

let uu____14385 = (

let uu____14401 = (

let uu____14414 = (

let uu____14415 = (

let uu____14416 = (

let uu____14421 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____14422 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____14421), (uu____14422))))
in (FStar_SMTEncoding_Util.mkLT uu____14416))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____14415))
in (quant xy uu____14414))
in ((FStar_Parser_Const.op_LT), (uu____14401)))
in (

let uu____14434 = (

let uu____14452 = (

let uu____14468 = (

let uu____14481 = (

let uu____14482 = (

let uu____14483 = (

let uu____14488 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____14489 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____14488), (uu____14489))))
in (FStar_SMTEncoding_Util.mkLTE uu____14483))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____14482))
in (quant xy uu____14481))
in ((FStar_Parser_Const.op_LTE), (uu____14468)))
in (

let uu____14501 = (

let uu____14519 = (

let uu____14535 = (

let uu____14548 = (

let uu____14549 = (

let uu____14550 = (

let uu____14555 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____14556 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____14555), (uu____14556))))
in (FStar_SMTEncoding_Util.mkGT uu____14550))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____14549))
in (quant xy uu____14548))
in ((FStar_Parser_Const.op_GT), (uu____14535)))
in (

let uu____14568 = (

let uu____14586 = (

let uu____14602 = (

let uu____14615 = (

let uu____14616 = (

let uu____14617 = (

let uu____14622 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____14623 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____14622), (uu____14623))))
in (FStar_SMTEncoding_Util.mkGTE uu____14617))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____14616))
in (quant xy uu____14615))
in ((FStar_Parser_Const.op_GTE), (uu____14602)))
in (

let uu____14635 = (

let uu____14653 = (

let uu____14669 = (

let uu____14682 = (

let uu____14683 = (

let uu____14684 = (

let uu____14689 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____14690 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____14689), (uu____14690))))
in (FStar_SMTEncoding_Util.mkSub uu____14684))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____14683))
in (quant xy uu____14682))
in ((FStar_Parser_Const.op_Subtraction), (uu____14669)))
in (

let uu____14702 = (

let uu____14720 = (

let uu____14736 = (

let uu____14749 = (

let uu____14750 = (

let uu____14751 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Util.mkMinus uu____14751))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____14750))
in (quant qx uu____14749))
in ((FStar_Parser_Const.op_Minus), (uu____14736)))
in (

let uu____14763 = (

let uu____14781 = (

let uu____14797 = (

let uu____14810 = (

let uu____14811 = (

let uu____14812 = (

let uu____14817 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____14818 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____14817), (uu____14818))))
in (FStar_SMTEncoding_Util.mkAdd uu____14812))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____14811))
in (quant xy uu____14810))
in ((FStar_Parser_Const.op_Addition), (uu____14797)))
in (

let uu____14830 = (

let uu____14848 = (

let uu____14864 = (

let uu____14877 = (

let uu____14878 = (

let uu____14879 = (

let uu____14884 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____14885 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____14884), (uu____14885))))
in (FStar_SMTEncoding_Util.mkMul uu____14879))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____14878))
in (quant xy uu____14877))
in ((FStar_Parser_Const.op_Multiply), (uu____14864)))
in (

let uu____14897 = (

let uu____14915 = (

let uu____14931 = (

let uu____14944 = (

let uu____14945 = (

let uu____14946 = (

let uu____14951 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____14952 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____14951), (uu____14952))))
in (FStar_SMTEncoding_Util.mkDiv uu____14946))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____14945))
in (quant xy uu____14944))
in ((FStar_Parser_Const.op_Division), (uu____14931)))
in (

let uu____14964 = (

let uu____14982 = (

let uu____14998 = (

let uu____15011 = (

let uu____15012 = (

let uu____15013 = (

let uu____15018 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____15019 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____15018), (uu____15019))))
in (FStar_SMTEncoding_Util.mkMod uu____15013))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____15012))
in (quant xy uu____15011))
in ((FStar_Parser_Const.op_Modulus), (uu____14998)))
in (

let uu____15031 = (

let uu____15049 = (

let uu____15065 = (

let uu____15078 = (

let uu____15079 = (

let uu____15080 = (

let uu____15085 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____15086 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____15085), (uu____15086))))
in (FStar_SMTEncoding_Util.mkAnd uu____15080))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____15079))
in (quant xy uu____15078))
in ((FStar_Parser_Const.op_And), (uu____15065)))
in (

let uu____15098 = (

let uu____15116 = (

let uu____15132 = (

let uu____15145 = (

let uu____15146 = (

let uu____15147 = (

let uu____15152 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____15153 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____15152), (uu____15153))))
in (FStar_SMTEncoding_Util.mkOr uu____15147))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____15146))
in (quant xy uu____15145))
in ((FStar_Parser_Const.op_Or), (uu____15132)))
in (

let uu____15165 = (

let uu____15183 = (

let uu____15199 = (

let uu____15212 = (

let uu____15213 = (

let uu____15214 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Util.mkNot uu____15214))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____15213))
in (quant qx uu____15212))
in ((FStar_Parser_Const.op_Negation), (uu____15199)))
in (uu____15183)::[])
in (uu____15116)::uu____15165))
in (uu____15049)::uu____15098))
in (uu____14982)::uu____15031))
in (uu____14915)::uu____14964))
in (uu____14848)::uu____14897))
in (uu____14781)::uu____14830))
in (uu____14720)::uu____14763))
in (uu____14653)::uu____14702))
in (uu____14586)::uu____14635))
in (uu____14519)::uu____14568))
in (uu____14452)::uu____14501))
in (uu____14385)::uu____14434))
in (uu____14324)::uu____14367))
in (uu____14264)::uu____14306))
in (

let mk1 = (fun l v1 -> (

let uu____15485 = (

let uu____15496 = (FStar_All.pipe_right prims1 (FStar_List.find (fun uu____15566 -> (match (uu____15566) with
| (l', uu____15582) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right uu____15496 (FStar_Option.map (fun uu____15658 -> (match (uu____15658) with
| (uu____15681, b) -> begin
(b v1)
end)))))
in (FStar_All.pipe_right uu____15485 FStar_Option.get)))
in (

let is = (fun l -> (FStar_All.pipe_right prims1 (FStar_Util.for_some (fun uu____15772 -> (match (uu____15772) with
| (l', uu____15788) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk1; is = is})))))))
end))
end))
end))


let pretype_axiom : env_t  ->  FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun env tapp vars -> (

let uu____15838 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____15838) with
| (xxsym, xx) -> begin
(

let uu____15845 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____15845) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let tapp_hash = (FStar_SMTEncoding_Term.hash_of_term tapp)
in (

let module_name = env.current_module_name
in (

let uu____15855 = (

let uu____15862 = (

let uu____15863 = (

let uu____15874 = (

let uu____15875 = (

let uu____15880 = (

let uu____15881 = (

let uu____15886 = (FStar_SMTEncoding_Util.mkApp (("PreType"), ((xx)::[])))
in ((tapp), (uu____15886)))
in (FStar_SMTEncoding_Util.mkEq uu____15881))
in ((xx_has_type), (uu____15880)))
in (FStar_SMTEncoding_Util.mkImp uu____15875))
in ((((xx_has_type)::[])::[]), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars), (uu____15874)))
in (FStar_SMTEncoding_Util.mkForall uu____15863))
in (

let uu____15905 = (

let uu____15906 = (

let uu____15907 = (

let uu____15908 = (FStar_Util.digest_of_string tapp_hash)
in (Prims.strcat "_pretyping_" uu____15908))
in (Prims.strcat module_name uu____15907))
in (varops.mk_unique uu____15906))
in ((uu____15862), (FStar_Pervasives_Native.Some ("pretyping")), (uu____15905))))
in (FStar_SMTEncoding_Util.mkAssume uu____15855)))))
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

let uu____15956 = (

let uu____15957 = (

let uu____15964 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in ((uu____15964), (FStar_Pervasives_Native.Some ("unit typing")), ("unit_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____15957))
in (

let uu____15965 = (

let uu____15968 = (

let uu____15969 = (

let uu____15976 = (

let uu____15977 = (

let uu____15988 = (

let uu____15989 = (

let uu____15994 = (FStar_SMTEncoding_Util.mkEq ((x), (FStar_SMTEncoding_Term.mk_Term_unit)))
in ((typing_pred), (uu____15994)))
in (FStar_SMTEncoding_Util.mkImp uu____15989))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____15988)))
in (mkForall_fuel uu____15977))
in ((uu____15976), (FStar_Pervasives_Native.Some ("unit inversion")), ("unit_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____15969))
in (uu____15968)::[])
in (uu____15956)::uu____15965))))
in (

let mk_bool = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Bool_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____16034 = (

let uu____16035 = (

let uu____16042 = (

let uu____16043 = (

let uu____16054 = (

let uu____16059 = (

let uu____16062 = (FStar_SMTEncoding_Term.boxBool b)
in (uu____16062)::[])
in (uu____16059)::[])
in (

let uu____16067 = (

let uu____16068 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType uu____16068 tt))
in ((uu____16054), ((bb)::[]), (uu____16067))))
in (FStar_SMTEncoding_Util.mkForall uu____16043))
in ((uu____16042), (FStar_Pervasives_Native.Some ("bool typing")), ("bool_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____16035))
in (

let uu____16081 = (

let uu____16084 = (

let uu____16085 = (

let uu____16092 = (

let uu____16093 = (

let uu____16104 = (

let uu____16105 = (

let uu____16110 = (FStar_SMTEncoding_Term.mk_tester (FStar_Pervasives_Native.fst FStar_SMTEncoding_Term.boxBoolFun) x)
in ((typing_pred), (uu____16110)))
in (FStar_SMTEncoding_Util.mkImp uu____16105))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____16104)))
in (mkForall_fuel uu____16093))
in ((uu____16092), (FStar_Pervasives_Native.Some ("bool inversion")), ("bool_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____16085))
in (uu____16084)::[])
in (uu____16034)::uu____16081))))))
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

let uu____16158 = (

let uu____16159 = (

let uu____16166 = (

let uu____16169 = (

let uu____16172 = (

let uu____16175 = (FStar_SMTEncoding_Term.boxInt a)
in (

let uu____16176 = (

let uu____16179 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____16179)::[])
in (uu____16175)::uu____16176))
in (tt)::uu____16172)
in (tt)::uu____16169)
in (("Prims.Precedes"), (uu____16166)))
in (FStar_SMTEncoding_Util.mkApp uu____16159))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____16158))
in (

let precedes_y_x = (

let uu____16183 = (FStar_SMTEncoding_Util.mkApp (("Precedes"), ((y)::(x)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____16183))
in (

let uu____16186 = (

let uu____16187 = (

let uu____16194 = (

let uu____16195 = (

let uu____16206 = (

let uu____16211 = (

let uu____16214 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____16214)::[])
in (uu____16211)::[])
in (

let uu____16219 = (

let uu____16220 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType uu____16220 tt))
in ((uu____16206), ((bb)::[]), (uu____16219))))
in (FStar_SMTEncoding_Util.mkForall uu____16195))
in ((uu____16194), (FStar_Pervasives_Native.Some ("int typing")), ("int_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____16187))
in (

let uu____16233 = (

let uu____16236 = (

let uu____16237 = (

let uu____16244 = (

let uu____16245 = (

let uu____16256 = (

let uu____16257 = (

let uu____16262 = (FStar_SMTEncoding_Term.mk_tester (FStar_Pervasives_Native.fst FStar_SMTEncoding_Term.boxIntFun) x)
in ((typing_pred), (uu____16262)))
in (FStar_SMTEncoding_Util.mkImp uu____16257))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____16256)))
in (mkForall_fuel uu____16245))
in ((uu____16244), (FStar_Pervasives_Native.Some ("int inversion")), ("int_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____16237))
in (

let uu____16279 = (

let uu____16282 = (

let uu____16283 = (

let uu____16290 = (

let uu____16291 = (

let uu____16302 = (

let uu____16303 = (

let uu____16308 = (

let uu____16309 = (

let uu____16312 = (

let uu____16315 = (

let uu____16318 = (

let uu____16319 = (

let uu____16324 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____16325 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____16324), (uu____16325))))
in (FStar_SMTEncoding_Util.mkGT uu____16319))
in (

let uu____16326 = (

let uu____16329 = (

let uu____16330 = (

let uu____16335 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____16336 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____16335), (uu____16336))))
in (FStar_SMTEncoding_Util.mkGTE uu____16330))
in (

let uu____16337 = (

let uu____16340 = (

let uu____16341 = (

let uu____16346 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____16347 = (FStar_SMTEncoding_Term.unboxInt x)
in ((uu____16346), (uu____16347))))
in (FStar_SMTEncoding_Util.mkLT uu____16341))
in (uu____16340)::[])
in (uu____16329)::uu____16337))
in (uu____16318)::uu____16326))
in (typing_pred_y)::uu____16315)
in (typing_pred)::uu____16312)
in (FStar_SMTEncoding_Util.mk_and_l uu____16309))
in ((uu____16308), (precedes_y_x)))
in (FStar_SMTEncoding_Util.mkImp uu____16303))
in ((((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[]), ((xx)::(yy)::[]), (uu____16302)))
in (mkForall_fuel uu____16291))
in ((uu____16290), (FStar_Pervasives_Native.Some ("well-founded ordering on nat (alt)")), ("well-founded-ordering-on-nat")))
in (FStar_SMTEncoding_Util.mkAssume uu____16283))
in (uu____16282)::[])
in (uu____16236)::uu____16279))
in (uu____16186)::uu____16233)))))))))))
in (

let mk_str = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.String_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____16391 = (

let uu____16392 = (

let uu____16399 = (

let uu____16400 = (

let uu____16411 = (

let uu____16416 = (

let uu____16419 = (FStar_SMTEncoding_Term.boxString b)
in (uu____16419)::[])
in (uu____16416)::[])
in (

let uu____16424 = (

let uu____16425 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType uu____16425 tt))
in ((uu____16411), ((bb)::[]), (uu____16424))))
in (FStar_SMTEncoding_Util.mkForall uu____16400))
in ((uu____16399), (FStar_Pervasives_Native.Some ("string typing")), ("string_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____16392))
in (

let uu____16438 = (

let uu____16441 = (

let uu____16442 = (

let uu____16449 = (

let uu____16450 = (

let uu____16461 = (

let uu____16462 = (

let uu____16467 = (FStar_SMTEncoding_Term.mk_tester (FStar_Pervasives_Native.fst FStar_SMTEncoding_Term.boxStringFun) x)
in ((typing_pred), (uu____16467)))
in (FStar_SMTEncoding_Util.mkImp uu____16462))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____16461)))
in (mkForall_fuel uu____16450))
in ((uu____16449), (FStar_Pervasives_Native.Some ("string inversion")), ("string_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____16442))
in (uu____16441)::[])
in (uu____16391)::uu____16438))))))
in (

let mk_true_interp = (fun env nm true_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((true_tm)::[])))
in ((FStar_SMTEncoding_Util.mkAssume ((valid), (FStar_Pervasives_Native.Some ("True interpretation")), ("true_interp"))))::[]))
in (

let mk_false_interp = (fun env nm false_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((false_tm)::[])))
in (

let uu____16522 = (

let uu____16523 = (

let uu____16530 = (FStar_SMTEncoding_Util.mkIff ((FStar_SMTEncoding_Util.mkFalse), (valid)))
in ((uu____16530), (FStar_Pervasives_Native.Some ("False interpretation")), ("false_interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16523))
in (uu____16522)::[])))
in (

let mk_and_interp = (fun env conj uu____16546 -> (

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

let uu____16571 = (

let uu____16572 = (

let uu____16579 = (

let uu____16580 = (

let uu____16591 = (

let uu____16592 = (

let uu____16597 = (FStar_SMTEncoding_Util.mkAnd ((valid_a), (valid_b)))
in ((uu____16597), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____16592))
in ((((l_and_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____16591)))
in (FStar_SMTEncoding_Util.mkForall uu____16580))
in ((uu____16579), (FStar_Pervasives_Native.Some ("/\\ interpretation")), ("l_and-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16572))
in (uu____16571)::[]))))))))))
in (

let mk_or_interp = (fun env disj uu____16633 -> (

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

let uu____16658 = (

let uu____16659 = (

let uu____16666 = (

let uu____16667 = (

let uu____16678 = (

let uu____16679 = (

let uu____16684 = (FStar_SMTEncoding_Util.mkOr ((valid_a), (valid_b)))
in ((uu____16684), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____16679))
in ((((l_or_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____16678)))
in (FStar_SMTEncoding_Util.mkForall uu____16667))
in ((uu____16666), (FStar_Pervasives_Native.Some ("\\/ interpretation")), ("l_or-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16659))
in (uu____16658)::[]))))))))))
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

let uu____16745 = (

let uu____16746 = (

let uu____16753 = (

let uu____16754 = (

let uu____16765 = (

let uu____16766 = (

let uu____16771 = (FStar_SMTEncoding_Util.mkEq ((x1), (y1)))
in ((uu____16771), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____16766))
in ((((eq2_x_y)::[])::[]), ((aa)::(xx1)::(yy1)::[]), (uu____16765)))
in (FStar_SMTEncoding_Util.mkForall uu____16754))
in ((uu____16753), (FStar_Pervasives_Native.Some ("Eq2 interpretation")), ("eq2-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16746))
in (uu____16745)::[]))))))))))
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

let uu____16842 = (

let uu____16843 = (

let uu____16850 = (

let uu____16851 = (

let uu____16862 = (

let uu____16863 = (

let uu____16868 = (FStar_SMTEncoding_Util.mkEq ((x1), (y1)))
in ((uu____16868), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____16863))
in ((((eq3_x_y)::[])::[]), ((aa)::(bb)::(xx1)::(yy1)::[]), (uu____16862)))
in (FStar_SMTEncoding_Util.mkForall uu____16851))
in ((uu____16850), (FStar_Pervasives_Native.Some ("Eq3 interpretation")), ("eq3-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16843))
in (uu____16842)::[]))))))))))))
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

let uu____16937 = (

let uu____16938 = (

let uu____16945 = (

let uu____16946 = (

let uu____16957 = (

let uu____16958 = (

let uu____16963 = (FStar_SMTEncoding_Util.mkImp ((valid_a), (valid_b)))
in ((uu____16963), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____16958))
in ((((l_imp_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____16957)))
in (FStar_SMTEncoding_Util.mkForall uu____16946))
in ((uu____16945), (FStar_Pervasives_Native.Some ("==> interpretation")), ("l_imp-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16938))
in (uu____16937)::[]))))))))))
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

let uu____17024 = (

let uu____17025 = (

let uu____17032 = (

let uu____17033 = (

let uu____17044 = (

let uu____17045 = (

let uu____17050 = (FStar_SMTEncoding_Util.mkIff ((valid_a), (valid_b)))
in ((uu____17050), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____17045))
in ((((l_iff_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____17044)))
in (FStar_SMTEncoding_Util.mkForall uu____17033))
in ((uu____17032), (FStar_Pervasives_Native.Some ("<==> interpretation")), ("l_iff-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____17025))
in (uu____17024)::[]))))))))))
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

let uu____17100 = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____17100))
in (

let uu____17103 = (

let uu____17104 = (

let uu____17111 = (

let uu____17112 = (

let uu____17123 = (FStar_SMTEncoding_Util.mkIff ((not_valid_a), (valid)))
in ((((l_not_a)::[])::[]), ((aa)::[]), (uu____17123)))
in (FStar_SMTEncoding_Util.mkForall uu____17112))
in ((uu____17111), (FStar_Pervasives_Native.Some ("not interpretation")), ("l_not-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____17104))
in (uu____17103)::[])))))))
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

let uu____17181 = (

let uu____17188 = (

let uu____17191 = (FStar_SMTEncoding_Util.mk_ApplyTT b x1)
in (uu____17191)::[])
in (("Valid"), (uu____17188)))
in (FStar_SMTEncoding_Util.mkApp uu____17181))
in (

let uu____17194 = (

let uu____17195 = (

let uu____17202 = (

let uu____17203 = (

let uu____17214 = (

let uu____17215 = (

let uu____17220 = (

let uu____17221 = (

let uu____17232 = (

let uu____17237 = (

let uu____17240 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in (uu____17240)::[])
in (uu____17237)::[])
in (

let uu____17245 = (

let uu____17246 = (

let uu____17251 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in ((uu____17251), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp uu____17246))
in ((uu____17232), ((xx1)::[]), (uu____17245))))
in (FStar_SMTEncoding_Util.mkForall uu____17221))
in ((uu____17220), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____17215))
in ((((l_forall_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____17214)))
in (FStar_SMTEncoding_Util.mkForall uu____17203))
in ((uu____17202), (FStar_Pervasives_Native.Some ("forall interpretation")), ("forall-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____17195))
in (uu____17194)::[])))))))))))
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

let uu____17325 = (

let uu____17332 = (

let uu____17335 = (FStar_SMTEncoding_Util.mk_ApplyTT b x1)
in (uu____17335)::[])
in (("Valid"), (uu____17332)))
in (FStar_SMTEncoding_Util.mkApp uu____17325))
in (

let uu____17338 = (

let uu____17339 = (

let uu____17346 = (

let uu____17347 = (

let uu____17358 = (

let uu____17359 = (

let uu____17364 = (

let uu____17365 = (

let uu____17376 = (

let uu____17381 = (

let uu____17384 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in (uu____17384)::[])
in (uu____17381)::[])
in (

let uu____17389 = (

let uu____17390 = (

let uu____17395 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in ((uu____17395), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp uu____17390))
in ((uu____17376), ((xx1)::[]), (uu____17389))))
in (FStar_SMTEncoding_Util.mkExists uu____17365))
in ((uu____17364), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____17359))
in ((((l_exists_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____17358)))
in (FStar_SMTEncoding_Util.mkForall uu____17347))
in ((uu____17346), (FStar_Pervasives_Native.Some ("exists interpretation")), ("exists-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____17339))
in (uu____17338)::[])))))))))))
in (

let mk_range_interp = (fun env range tt -> (

let range_ty = (FStar_SMTEncoding_Util.mkApp ((range), ([])))
in (

let uu____17447 = (

let uu____17448 = (

let uu____17455 = (

let uu____17456 = (FStar_SMTEncoding_Term.mk_Range_const ())
in (FStar_SMTEncoding_Term.mk_HasTypeZ uu____17456 range_ty))
in (

let uu____17457 = (varops.mk_unique "typing_range_const")
in ((uu____17455), (FStar_Pervasives_Native.Some ("Range_const typing")), (uu____17457))))
in (FStar_SMTEncoding_Util.mkAssume uu____17448))
in (uu____17447)::[])))
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

let uu____17495 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1"))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel uu____17495 x1 t))
in (

let uu____17496 = (

let uu____17507 = (FStar_SMTEncoding_Util.mkImp ((hastypeZ), (hastypeS)))
in ((((hastypeZ)::[])::[]), ((xx1)::[]), (uu____17507)))
in (FStar_SMTEncoding_Util.mkForall uu____17496))))
in (

let uu____17524 = (

let uu____17525 = (

let uu____17532 = (

let uu____17533 = (

let uu____17544 = (FStar_SMTEncoding_Util.mkImp ((valid), (body)))
in ((((inversion_t)::[])::[]), ((tt1)::[]), (uu____17544)))
in (FStar_SMTEncoding_Util.mkForall uu____17533))
in ((uu____17532), (FStar_Pervasives_Native.Some ("inversion interpretation")), ("inversion-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____17525))
in (uu____17524)::[])))))))))
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

let uu____17592 = (

let uu____17593 = (

let uu____17600 = (

let uu____17601 = (

let uu____17616 = (

let uu____17617 = (

let uu____17622 = (FStar_SMTEncoding_Util.mkEq ((with_type_t_e), (e)))
in (

let uu____17623 = (FStar_SMTEncoding_Term.mk_HasType with_type_t_e t)
in ((uu____17622), (uu____17623))))
in (FStar_SMTEncoding_Util.mkAnd uu____17617))
in ((((with_type_t_e)::[])::[]), (FStar_Pervasives_Native.Some ((Prims.parse_int "0"))), ((tt1)::(ee)::[]), (uu____17616)))
in (FStar_SMTEncoding_Util.mkForall' uu____17601))
in ((uu____17600), (FStar_Pervasives_Native.Some ("with_type primitive axiom")), ("@with_type_primitive_axiom")))
in (FStar_SMTEncoding_Util.mkAssume uu____17593))
in (uu____17592)::[])))))))
in (

let prims1 = (((FStar_Parser_Const.unit_lid), (mk_unit)))::(((FStar_Parser_Const.bool_lid), (mk_bool)))::(((FStar_Parser_Const.int_lid), (mk_int)))::(((FStar_Parser_Const.string_lid), (mk_str)))::(((FStar_Parser_Const.true_lid), (mk_true_interp)))::(((FStar_Parser_Const.false_lid), (mk_false_interp)))::(((FStar_Parser_Const.and_lid), (mk_and_interp)))::(((FStar_Parser_Const.or_lid), (mk_or_interp)))::(((FStar_Parser_Const.eq2_lid), (mk_eq2_interp)))::(((FStar_Parser_Const.eq3_lid), (mk_eq3_interp)))::(((FStar_Parser_Const.imp_lid), (mk_imp_interp)))::(((FStar_Parser_Const.iff_lid), (mk_iff_interp)))::(((FStar_Parser_Const.not_lid), (mk_not_interp)))::(((FStar_Parser_Const.forall_lid), (mk_forall_interp)))::(((FStar_Parser_Const.exists_lid), (mk_exists_interp)))::(((FStar_Parser_Const.range_lid), (mk_range_interp)))::(((FStar_Parser_Const.inversion_lid), (mk_inversion_axiom)))::(((FStar_Parser_Const.with_type_lid), (mk_with_type_axiom)))::[]
in (fun env t s tt -> (

let uu____18151 = (FStar_Util.find_opt (fun uu____18187 -> (match (uu____18187) with
| (l, uu____18201) -> begin
(FStar_Ident.lid_equals l t)
end)) prims1)
in (match (uu____18151) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (uu____18241, f) -> begin
(f env s tt)
end))))))))))))))))))))))))))


let encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____18298 = (encode_function_type_as_formula t env)
in (match (uu____18298) with
| (form, decls) -> begin
(FStar_List.append decls (((FStar_SMTEncoding_Util.mkAssume ((form), (FStar_Pervasives_Native.Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str))), ((Prims.strcat "lemma_" lid.FStar_Ident.str)))))::[]))
end))))


let encode_free_var : Prims.bool  ->  env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun uninterpreted env fv tt t_norm quals -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____18356 = (((

let uu____18359 = ((FStar_Syntax_Util.is_pure_or_ghost_function t_norm) || (FStar_TypeChecker_Env.is_reifiable_function env.tcenv t_norm))
in (FStar_All.pipe_left Prims.op_Negation uu____18359)) || (FStar_Syntax_Util.is_lemma t_norm)) || uninterpreted)
in (match (uu____18356) with
| true -> begin
(

let arg_sorts = (

let uu____18369 = (

let uu____18370 = (FStar_Syntax_Subst.compress t_norm)
in uu____18370.FStar_Syntax_Syntax.n)
in (match (uu____18369) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____18376) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun uu____18406 -> FStar_SMTEncoding_Term.Term_sort)))
end
| uu____18411 -> begin
[]
end))
in (

let arity = (FStar_List.length arg_sorts)
in (

let uu____18413 = (new_term_constant_and_tok_from_lid env lid arity)
in (match (uu____18413) with
| (vname, vtok, env1) -> begin
(

let d = FStar_SMTEncoding_Term.DeclFun (((vname), (arg_sorts), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Uninterpreted function symbol for impure function"))))
in (

let dd = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Uninterpreted name for impure function"))))
in (((d)::(dd)::[]), (env1))))
end))))
end
| uu____18441 -> begin
(

let uu____18442 = (prims.is lid)
in (match (uu____18442) with
| true -> begin
(

let vname = (varops.new_fvar lid)
in (

let uu____18450 = (prims.mk lid vname)
in (match (uu____18450) with
| (tok, arity, definition) -> begin
(

let env1 = (push_free_var env lid arity vname (FStar_Pervasives_Native.Some (tok)))
in ((definition), (env1)))
end)))
end
| uu____18475 -> begin
(

let encode_non_total_function_typ = (Prims.op_disEquality lid.FStar_Ident.nsstr "Prims")
in (

let uu____18477 = (

let uu____18494 = (curried_arrow_formals_comp t_norm)
in (match (uu____18494) with
| (args, comp) -> begin
(

let comp1 = (

let uu____18538 = (FStar_TypeChecker_Env.is_reifiable_comp env.tcenv comp)
in (match (uu____18538) with
| true -> begin
(

let uu____18541 = (FStar_TypeChecker_Env.reify_comp (

let uu___122_18544 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___122_18544.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___122_18544.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___122_18544.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___122_18544.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___122_18544.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___122_18544.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___122_18544.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___122_18544.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___122_18544.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___122_18544.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___122_18544.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___122_18544.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___122_18544.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___122_18544.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___122_18544.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___122_18544.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___122_18544.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___122_18544.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___122_18544.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___122_18544.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___122_18544.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___122_18544.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___122_18544.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___122_18544.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___122_18544.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___122_18544.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___122_18544.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___122_18544.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___122_18544.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___122_18544.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___122_18544.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___122_18544.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___122_18544.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___122_18544.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___122_18544.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___122_18544.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___122_18544.FStar_TypeChecker_Env.dep_graph}) comp FStar_Syntax_Syntax.U_unknown)
in (FStar_Syntax_Syntax.mk_Total uu____18541))
end
| uu____18545 -> begin
comp
end))
in (match (encode_non_total_function_typ) with
| true -> begin
(

let uu____18562 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp1)
in ((args), (uu____18562)))
end
| uu____18581 -> begin
((args), (((FStar_Pervasives_Native.None), ((FStar_Syntax_Util.comp_result comp1)))))
end))
end))
in (match (uu____18477) with
| (formals, (pre_opt, res_t)) -> begin
(

let arity = (FStar_List.length formals)
in (

let uu____18636 = (new_term_constant_and_tok_from_lid env lid arity)
in (match (uu____18636) with
| (vname, vtok, env1) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
end
| uu____18661 -> begin
(FStar_SMTEncoding_Util.mkApp ((vtok), ([])))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun uu___96_18717 -> (match (uu___96_18717) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(

let uu____18721 = (FStar_Util.prefix vars)
in (match (uu____18721) with
| (uu____18742, (xxsym, uu____18744)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____18762 = (

let uu____18763 = (

let uu____18770 = (

let uu____18771 = (

let uu____18782 = (

let uu____18783 = (

let uu____18788 = (

let uu____18789 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____18789))
in ((vapp), (uu____18788)))
in (FStar_SMTEncoding_Util.mkEq uu____18783))
in ((((vapp)::[])::[]), (vars), (uu____18782)))
in (FStar_SMTEncoding_Util.mkForall uu____18771))
in ((uu____18770), (FStar_Pervasives_Native.Some ("Discriminator equation")), ((Prims.strcat "disc_equation_" (escape d.FStar_Ident.str)))))
in (FStar_SMTEncoding_Util.mkAssume uu____18763))
in (uu____18762)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(

let uu____18800 = (FStar_Util.prefix vars)
in (match (uu____18800) with
| (uu____18821, (xxsym, uu____18823)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f1 = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (

let tp_name = (mk_term_projector_name d f1)
in (

let prim_app = (FStar_SMTEncoding_Util.mkApp ((tp_name), ((xx)::[])))
in (

let uu____18846 = (

let uu____18847 = (

let uu____18854 = (

let uu____18855 = (

let uu____18866 = (FStar_SMTEncoding_Util.mkEq ((vapp), (prim_app)))
in ((((vapp)::[])::[]), (vars), (uu____18866)))
in (FStar_SMTEncoding_Util.mkForall uu____18855))
in ((uu____18854), (FStar_Pervasives_Native.Some ("Projector equation")), ((Prims.strcat "proj_equation_" tp_name))))
in (FStar_SMTEncoding_Util.mkAssume uu____18847))
in (uu____18846)::[])))))
end))
end
| uu____18875 -> begin
[]
end)))))
in (

let uu____18876 = (encode_binders FStar_Pervasives_Native.None formals env1)
in (match (uu____18876) with
| (vars, guards, env', decls1, uu____18903) -> begin
(

let uu____18916 = (match (pre_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____18929 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____18929), (decls1)))
end
| FStar_Pervasives_Native.Some (p) -> begin
(

let uu____18933 = (encode_formula p env')
in (match (uu____18933) with
| (g, ds) -> begin
(

let uu____18946 = (FStar_SMTEncoding_Util.mk_and_l ((g)::guards))
in ((uu____18946), ((FStar_List.append decls1 ds))))
end))
end)
in (match (uu____18916) with
| (guard, decls11) -> begin
(

let vtok_app = (mk_Apply vtok_tm vars)
in (

let vapp = (

let uu____18963 = (

let uu____18970 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((vname), (uu____18970)))
in (FStar_SMTEncoding_Util.mkApp uu____18963))
in (

let uu____18975 = (

let vname_decl = (

let uu____18983 = (

let uu____18994 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____19010 -> FStar_SMTEncoding_Term.Term_sort)))
in ((vname), (uu____18994), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____18983))
in (

let uu____19017 = (

let env2 = (

let uu___123_19023 = env1
in {bindings = uu___123_19023.bindings; depth = uu___123_19023.depth; tcenv = uu___123_19023.tcenv; warn = uu___123_19023.warn; cache = uu___123_19023.cache; nolabels = uu___123_19023.nolabels; use_zfuel_name = uu___123_19023.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = uu___123_19023.current_module_name})
in (

let uu____19024 = (

let uu____19025 = (head_normal env2 tt)
in (not (uu____19025)))
in (match (uu____19024) with
| true -> begin
(encode_term_pred FStar_Pervasives_Native.None tt env2 vtok_tm)
end
| uu____19030 -> begin
(encode_term_pred FStar_Pervasives_Native.None t_norm env2 vtok_tm)
end)))
in (match (uu____19017) with
| (tok_typing, decls2) -> begin
(

let tok_typing1 = (match (formals) with
| (uu____19040)::uu____19041 -> begin
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

let uu____19081 = (

let uu____19092 = (FStar_SMTEncoding_Term.mk_NoHoist f tok_typing)
in ((((vtok_app_l)::[])::((vtok_app_r)::[])::[]), ((ff)::[]), (uu____19092)))
in (FStar_SMTEncoding_Util.mkForall uu____19081))
in (FStar_SMTEncoding_Util.mkAssume ((guarded_tok_typing), (FStar_Pervasives_Native.Some ("function token typing")), ((Prims.strcat "function_token_typing_" vname)))))))))
end
| uu____19111 -> begin
(FStar_SMTEncoding_Util.mkAssume ((tok_typing), (FStar_Pervasives_Native.Some ("function token typing")), ((Prims.strcat "function_token_typing_" vname))))
end)
in (

let uu____19118 = (match (formals) with
| [] -> begin
(

let uu____19135 = (

let uu____19136 = (

let uu____19139 = (FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left (fun _0_18 -> FStar_Pervasives_Native.Some (_0_18)) uu____19139))
in (replace_free_var env1 lid arity vname uu____19136))
in (((FStar_List.append decls2 ((tok_typing1)::[]))), (uu____19135)))
end
| uu____19148 -> begin
(

let vtok_decl = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let name_tok_corr = (

let uu____19159 = (

let uu____19166 = (

let uu____19167 = (

let uu____19178 = (FStar_SMTEncoding_Util.mkEq ((vtok_app), (vapp)))
in ((((vtok_app)::[])::((vapp)::[])::[]), (vars), (uu____19178)))
in (FStar_SMTEncoding_Util.mkForall uu____19167))
in ((uu____19166), (FStar_Pervasives_Native.Some ("Name-token correspondence")), ((Prims.strcat "token_correspondence_" vname))))
in (FStar_SMTEncoding_Util.mkAssume uu____19159))
in (((FStar_List.append decls2 ((vtok_decl)::(name_tok_corr)::(tok_typing1)::[]))), (env1))))
end)
in (match (uu____19118) with
| (tok_decl, env2) -> begin
(((vname_decl)::tok_decl), (env2))
end)))
end)))
in (match (uu____18975) with
| (decls2, env2) -> begin
(

let uu____19217 = (

let res_t1 = (FStar_Syntax_Subst.compress res_t)
in (

let uu____19225 = (encode_term res_t1 env')
in (match (uu____19225) with
| (encoded_res_t, decls) -> begin
(

let uu____19238 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in ((encoded_res_t), (uu____19238), (decls)))
end)))
in (match (uu____19217) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (

let uu____19249 = (

let uu____19256 = (

let uu____19257 = (

let uu____19268 = (FStar_SMTEncoding_Util.mkImp ((guard), (ty_pred)))
in ((((vapp)::[])::[]), (vars), (uu____19268)))
in (FStar_SMTEncoding_Util.mkForall uu____19257))
in ((uu____19256), (FStar_Pervasives_Native.Some ("free var typing")), ((Prims.strcat "typing_" vname))))
in (FStar_SMTEncoding_Util.mkAssume uu____19249))
in (

let freshness = (

let uu____19280 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New))
in (match (uu____19280) with
| true -> begin
(

let uu____19285 = (

let uu____19286 = (

let uu____19297 = (FStar_All.pipe_right vars (FStar_List.map FStar_Pervasives_Native.snd))
in (

let uu____19312 = (varops.next_id ())
in ((vname), (uu____19297), (FStar_SMTEncoding_Term.Term_sort), (uu____19312))))
in (FStar_SMTEncoding_Term.fresh_constructor uu____19286))
in (

let uu____19315 = (

let uu____19318 = (pretype_axiom env2 vapp vars)
in (uu____19318)::[])
in (uu____19285)::uu____19315))
end
| uu____19319 -> begin
[]
end))
in (

let g = (

let uu____19323 = (

let uu____19326 = (

let uu____19329 = (

let uu____19332 = (

let uu____19335 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::uu____19335)
in (FStar_List.append freshness uu____19332))
in (FStar_List.append decls3 uu____19329))
in (FStar_List.append decls2 uu____19326))
in (FStar_List.append decls11 uu____19323))
in ((g), (env2)))))
end))
end))))
end))
end))))
end)))
end)))
end))
end))))


let declare_top_level_let : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (fvar_binding * FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env x t t_norm -> (

let uu____19376 = (try_lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____19376) with
| FStar_Pervasives_Native.None -> begin
(

let uu____19387 = (encode_free_var false env x t t_norm [])
in (match (uu____19387) with
| (decls, env1) -> begin
(

let fvb = (lookup_lid env1 x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in ((fvb), (decls), (env1)))
end))
end
| FStar_Pervasives_Native.Some (fvb) -> begin
((fvb), ([]), (env))
end)))


let encode_top_level_val : Prims.bool  ->  env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun uninterpreted env lid t quals -> (

let tt = (norm env t)
in (

let uu____19454 = (encode_free_var uninterpreted env lid t tt quals)
in (match (uu____19454) with
| (decls, env1) -> begin
(

let uu____19473 = (FStar_Syntax_Util.is_smt_lemma t)
in (match (uu____19473) with
| true -> begin
(

let uu____19480 = (

let uu____19483 = (encode_smt_lemma env1 lid tt)
in (FStar_List.append decls uu____19483))
in ((uu____19480), (env1)))
end
| uu____19488 -> begin
((decls), (env1))
end))
end))))


let encode_top_level_vals : env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____19541 lb -> (match (uu____19541) with
| (decls, env1) -> begin
(

let uu____19561 = (

let uu____19568 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val false env1 uu____19568 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (uu____19561) with
| (decls', env2) -> begin
(((FStar_List.append decls decls')), (env2))
end))
end)) (([]), (env)))))


let is_tactic : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let fstar_tactics_tactic_lid = (FStar_Parser_Const.p2l (("FStar")::("Tactics")::("tactic")::[]))
in (

let uu____19591 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____19591) with
| (hd1, args) -> begin
(

let uu____19628 = (

let uu____19629 = (FStar_Syntax_Util.un_uinst hd1)
in uu____19629.FStar_Syntax_Syntax.n)
in (match (uu____19628) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____19633, c) -> begin
(

let effect_name = (FStar_Syntax_Util.comp_effect_name c)
in (FStar_Util.starts_with "FStar.Tactics" effect_name.FStar_Ident.str))
end
| uu____19652 -> begin
false
end))
end))))


let encode_top_level_let : env_t  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env uu____19680 quals -> (match (uu____19680) with
| (is_rec, bindings) -> begin
(

let eta_expand1 = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let uu____19772 = (FStar_Util.first_N nbinders formals)
in (match (uu____19772) with
| (formals1, extra_formals) -> begin
(

let subst1 = (FStar_List.map2 (fun uu____19853 uu____19854 -> (match (((uu____19853), (uu____19854))) with
| ((formal, uu____19872), (binder, uu____19874)) -> begin
(

let uu____19883 = (

let uu____19890 = (FStar_Syntax_Syntax.bv_to_name binder)
in ((formal), (uu____19890)))
in FStar_Syntax_Syntax.NT (uu____19883))
end)) formals1 binders)
in (

let extra_formals1 = (

let uu____19902 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun uu____19933 -> (match (uu____19933) with
| (x, i) -> begin
(

let uu____19944 = (

let uu___124_19945 = x
in (

let uu____19946 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___124_19945.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___124_19945.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____19946}))
in ((uu____19944), (i)))
end))))
in (FStar_All.pipe_right uu____19902 FStar_Syntax_Util.name_binders))
in (

let body1 = (

let uu____19964 = (

let uu____19969 = (FStar_Syntax_Subst.compress body)
in (

let uu____19970 = (

let uu____19971 = (FStar_Syntax_Util.args_of_binders extra_formals1)
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____19971))
in (FStar_Syntax_Syntax.extend_app_n uu____19969 uu____19970)))
in (uu____19964 FStar_Pervasives_Native.None body.FStar_Syntax_Syntax.pos))
in (((FStar_List.append binders extra_formals1)), (body1)))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (

let get_result_type = (fun c -> (

let uu____20050 = (FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c)
in (match (uu____20050) with
| true -> begin
(FStar_TypeChecker_Env.reify_comp (

let uu___125_20055 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___125_20055.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___125_20055.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___125_20055.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___125_20055.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___125_20055.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___125_20055.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___125_20055.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___125_20055.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___125_20055.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___125_20055.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___125_20055.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___125_20055.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___125_20055.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___125_20055.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___125_20055.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___125_20055.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___125_20055.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___125_20055.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___125_20055.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___125_20055.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___125_20055.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___125_20055.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___125_20055.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___125_20055.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___125_20055.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___125_20055.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___125_20055.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___125_20055.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___125_20055.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___125_20055.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___125_20055.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___125_20055.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___125_20055.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___125_20055.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___125_20055.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___125_20055.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___125_20055.FStar_TypeChecker_Env.dep_graph}) c FStar_Syntax_Syntax.U_unknown)
end
| uu____20056 -> begin
(FStar_Syntax_Util.comp_result c)
end)))
in (

let rec aux = (fun norm1 t_norm1 -> (

let uu____20096 = (FStar_Syntax_Util.abs_formals e)
in (match (uu____20096) with
| (binders, body, lopt) -> begin
(match (binders) with
| (uu____20168)::uu____20169 -> begin
(

let uu____20184 = (

let uu____20185 = (

let uu____20188 = (FStar_Syntax_Subst.compress t_norm1)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____20188))
in uu____20185.FStar_Syntax_Syntax.n)
in (match (uu____20184) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____20237 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____20237) with
| (formals1, c1) -> begin
(

let nformals = (FStar_List.length formals1)
in (

let nbinders = (FStar_List.length binders)
in (

let tres = (get_result_type c1)
in (

let uu____20285 = ((nformals < nbinders) && (FStar_Syntax_Util.is_total_comp c1))
in (match (uu____20285) with
| true -> begin
(

let uu____20324 = (FStar_Util.first_N nformals binders)
in (match (uu____20324) with
| (bs0, rest) -> begin
(

let c2 = (

let subst1 = (FStar_List.map2 (fun uu____20422 uu____20423 -> (match (((uu____20422), (uu____20423))) with
| ((x, uu____20441), (b, uu____20443)) -> begin
(

let uu____20452 = (

let uu____20459 = (FStar_Syntax_Syntax.bv_to_name b)
in ((x), (uu____20459)))
in FStar_Syntax_Syntax.NT (uu____20452))
end)) formals1 bs0)
in (FStar_Syntax_Subst.subst_comp subst1 c1))
in (

let body1 = (FStar_Syntax_Util.abs rest body lopt)
in (

let uu____20467 = (

let uu____20492 = (get_result_type c2)
in ((bs0), (body1), (bs0), (uu____20492)))
in ((uu____20467), (false)))))
end))
end
| uu____20535 -> begin
(match ((nformals > nbinders)) with
| true -> begin
(

let uu____20574 = (eta_expand1 binders formals1 body tres)
in (match (uu____20574) with
| (binders1, body1) -> begin
((((binders1), (body1), (formals1), (tres))), (false))
end))
end
| uu____20661 -> begin
((((binders), (body), (formals1), (tres))), (false))
end)
end)))))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____20675) -> begin
(

let uu____20680 = (

let uu____20705 = (aux norm1 x.FStar_Syntax_Syntax.sort)
in (FStar_Pervasives_Native.fst uu____20705))
in ((uu____20680), (true)))
end
| uu____20782 when (not (norm1)) -> begin
(

let t_norm2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm1)
in (aux true t_norm2))
end
| uu____20784 -> begin
(

let uu____20785 = (

let uu____20786 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____20787 = (FStar_Syntax_Print.term_to_string t_norm1)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str uu____20786 uu____20787)))
in (failwith uu____20785))
end))
end
| uu____20816 -> begin
(

let rec aux' = (fun t_norm2 -> (

let uu____20849 = (

let uu____20850 = (FStar_Syntax_Subst.compress t_norm2)
in uu____20850.FStar_Syntax_Syntax.n)
in (match (uu____20849) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____20897 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____20897) with
| (formals1, c1) -> begin
(

let tres = (get_result_type c1)
in (

let uu____20933 = (eta_expand1 [] formals1 e tres)
in (match (uu____20933) with
| (binders1, body1) -> begin
((((binders1), (body1), (formals1), (tres))), (false))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (bv, uu____21023) -> begin
(aux' bv.FStar_Syntax_Syntax.sort)
end
| uu____21028 -> begin
(((([]), (e), ([]), (t_norm2))), (false))
end)))
in (aux' t_norm1))
end)
end)))
in (aux false t_norm))))
in (FStar_All.try_with (fun uu___127_21081 -> (match (()) with
| () -> begin
(

let uu____21088 = (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> ((FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))))
in (match (uu____21088) with
| true -> begin
(encode_top_level_vals env bindings quals)
end
| uu____21099 -> begin
(

let uu____21100 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____21163 lb -> (match (uu____21163) with
| (toks, typs, decls, env1) -> begin
((

let uu____21218 = (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp)
in (match (uu____21218) with
| true -> begin
(FStar_Exn.raise Let_rec_unencodeable)
end
| uu____21219 -> begin
()
end));
(

let t_norm = (whnf env1 lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____21221 = (

let uu____21230 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env1 uu____21230 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (uu____21221) with
| (tok, decl, env2) -> begin
(((tok)::toks), ((t_norm)::typs), ((decl)::decls), (env2))
end)));
)
end)) (([]), ([]), ([]), (env))))
in (match (uu____21100) with
| (toks, typs, decls, env1) -> begin
(

let toks_fvbs = (FStar_List.rev toks)
in (

let decls1 = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (

let typs1 = (FStar_List.rev typs)
in (

let mk_app1 = (fun rng curry fvb vars -> (

let mk_fv = (fun uu____21355 -> (match ((Prims.op_Equality fvb.smt_arity (Prims.parse_int "0"))) with
| true -> begin
(FStar_SMTEncoding_Util.mkFreeV ((fvb.smt_id), (FStar_SMTEncoding_Term.Term_sort)))
end
| uu____21356 -> begin
(raise_arity_mismatch fvb.smt_id fvb.smt_arity (Prims.parse_int "0") rng)
end))
in (match (vars) with
| [] -> begin
(mk_fv ())
end
| uu____21361 -> begin
(match (curry) with
| true -> begin
(match (fvb.smt_token) with
| FStar_Pervasives_Native.Some (ftok) -> begin
(mk_Apply ftok vars)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____21369 = (mk_fv ())
in (mk_Apply uu____21369 vars))
end)
end
| uu____21370 -> begin
(

let uu____21371 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (maybe_curry_app rng (FStar_SMTEncoding_Term.Var (fvb.smt_id)) fvb.smt_arity uu____21371))
end)
end)))
in (

let encode_non_rec_lbdef = (fun bindings1 typs2 toks1 env2 -> (match (((bindings1), (typs2), (toks1))) with
| (({FStar_Syntax_Syntax.lbname = lbn; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____21431; FStar_Syntax_Syntax.lbeff = uu____21432; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = uu____21434; FStar_Syntax_Syntax.lbpos = uu____21435})::[], (t_norm)::[], (fvb)::[]) -> begin
(

let flid = fvb.fvar_lid
in (

let uu____21459 = (

let uu____21466 = (FStar_TypeChecker_Env.open_universes_in env2.tcenv uvs ((e)::(t_norm)::[]))
in (match (uu____21466) with
| (tcenv', uu____21482, e_t) -> begin
(

let uu____21488 = (match (e_t) with
| (e1)::(t_norm1)::[] -> begin
((e1), (t_norm1))
end
| uu____21499 -> begin
(failwith "Impossible")
end)
in (match (uu____21488) with
| (e1, t_norm1) -> begin
(((

let uu___128_21515 = env2
in {bindings = uu___128_21515.bindings; depth = uu___128_21515.depth; tcenv = tcenv'; warn = uu___128_21515.warn; cache = uu___128_21515.cache; nolabels = uu___128_21515.nolabels; use_zfuel_name = uu___128_21515.use_zfuel_name; encode_non_total_function_typ = uu___128_21515.encode_non_total_function_typ; current_module_name = uu___128_21515.current_module_name})), (e1), (t_norm1))
end))
end))
in (match (uu____21459) with
| (env', e1, t_norm1) -> begin
(

let uu____21525 = (destruct_bound_function flid t_norm1 e1)
in (match (uu____21525) with
| ((binders, body, uu____21546, t_body), curry) -> begin
((

let uu____21558 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____21558) with
| true -> begin
(

let uu____21559 = (FStar_Syntax_Print.binders_to_string ", " binders)
in (

let uu____21560 = (FStar_Syntax_Print.term_to_string body)
in (FStar_Util.print2 "Encoding let : binders=[%s], body=%s\n" uu____21559 uu____21560)))
end
| uu____21561 -> begin
()
end));
(

let uu____21562 = (encode_binders FStar_Pervasives_Native.None binders env')
in (match (uu____21562) with
| (vars, guards, env'1, binder_decls, uu____21589) -> begin
(

let body1 = (

let uu____21603 = (FStar_TypeChecker_Env.is_reifiable_function env'1.tcenv t_norm1)
in (match (uu____21603) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env'1.tcenv body)
end
| uu____21604 -> begin
(FStar_Syntax_Util.ascribe body ((FStar_Util.Inl (t_body)), (FStar_Pervasives_Native.None)))
end))
in (

let app = (

let uu____21624 = (FStar_Syntax_Util.range_of_lbname lbn)
in (mk_app1 uu____21624 curry fvb vars))
in (

let uu____21625 = (

let uu____21634 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic))
in (match (uu____21634) with
| true -> begin
(

let uu____21645 = (FStar_SMTEncoding_Term.mk_Valid app)
in (

let uu____21646 = (encode_formula body1 env'1)
in ((uu____21645), (uu____21646))))
end
| uu____21655 -> begin
(

let uu____21656 = (encode_term body1 env'1)
in ((app), (uu____21656)))
end))
in (match (uu____21625) with
| (app1, (body2, decls2)) -> begin
(

let eqn = (

let uu____21679 = (

let uu____21686 = (

let uu____21687 = (

let uu____21698 = (FStar_SMTEncoding_Util.mkEq ((app1), (body2)))
in ((((app1)::[])::[]), (vars), (uu____21698)))
in (FStar_SMTEncoding_Util.mkForall uu____21687))
in (

let uu____21707 = (

let uu____21708 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in FStar_Pervasives_Native.Some (uu____21708))
in ((uu____21686), (uu____21707), ((Prims.strcat "equation_" fvb.smt_id)))))
in (FStar_SMTEncoding_Util.mkAssume uu____21679))
in (

let uu____21709 = (

let uu____21712 = (

let uu____21715 = (

let uu____21718 = (

let uu____21721 = (primitive_type_axioms env2.tcenv flid fvb.smt_id app1)
in (FStar_List.append ((eqn)::[]) uu____21721))
in (FStar_List.append decls2 uu____21718))
in (FStar_List.append binder_decls uu____21715))
in (FStar_List.append decls1 uu____21712))
in ((uu____21709), (env2))))
end))))
end));
)
end))
end)))
end
| uu____21726 -> begin
(failwith "Impossible")
end))
in (

let encode_rec_lbdefs = (fun bindings1 typs2 toks1 env2 -> (

let fuel = (

let uu____21789 = (varops.fresh "fuel")
in ((uu____21789), (FStar_SMTEncoding_Term.Fuel_sort)))
in (

let fuel_tm = (FStar_SMTEncoding_Util.mkFreeV fuel)
in (

let env0 = env2
in (

let uu____21792 = (FStar_All.pipe_right toks1 (FStar_List.fold_left (fun uu____21839 fvb -> (match (uu____21839) with
| (gtoks, env3) -> begin
(

let flid = fvb.fvar_lid
in (

let g = (

let uu____21885 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented")
in (varops.new_fvar uu____21885))
in (

let gtok = (

let uu____21887 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented_token")
in (varops.new_fvar uu____21887))
in (

let env4 = (

let uu____21889 = (

let uu____21892 = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::[])))
in (FStar_All.pipe_left (fun _0_19 -> FStar_Pervasives_Native.Some (_0_19)) uu____21892))
in (push_free_var env3 flid fvb.smt_arity gtok uu____21889))
in (((((fvb), (g), (gtok)))::gtoks), (env4))))))
end)) (([]), (env2))))
in (match (uu____21792) with
| (gtoks, env3) -> begin
(

let gtoks1 = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env01 uu____21998 t_norm uu____22000 -> (match (((uu____21998), (uu____22000))) with
| ((fvb, g, gtok), {FStar_Syntax_Syntax.lbname = lbn; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____22028; FStar_Syntax_Syntax.lbeff = uu____22029; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = uu____22031; FStar_Syntax_Syntax.lbpos = uu____22032}) -> begin
(

let uu____22053 = (

let uu____22060 = (FStar_TypeChecker_Env.open_universes_in env3.tcenv uvs ((e)::(t_norm)::[]))
in (match (uu____22060) with
| (tcenv', uu____22076, e_t) -> begin
(

let uu____22082 = (match (e_t) with
| (e1)::(t_norm1)::[] -> begin
((e1), (t_norm1))
end
| uu____22093 -> begin
(failwith "Impossible")
end)
in (match (uu____22082) with
| (e1, t_norm1) -> begin
(((

let uu___129_22109 = env3
in {bindings = uu___129_22109.bindings; depth = uu___129_22109.depth; tcenv = tcenv'; warn = uu___129_22109.warn; cache = uu___129_22109.cache; nolabels = uu___129_22109.nolabels; use_zfuel_name = uu___129_22109.use_zfuel_name; encode_non_total_function_typ = uu___129_22109.encode_non_total_function_typ; current_module_name = uu___129_22109.current_module_name})), (e1), (t_norm1))
end))
end))
in (match (uu____22053) with
| (env', e1, t_norm1) -> begin
((

let uu____22124 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env01.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____22124) with
| true -> begin
(

let uu____22125 = (FStar_Syntax_Print.lbname_to_string lbn)
in (

let uu____22126 = (FStar_Syntax_Print.term_to_string t_norm1)
in (

let uu____22127 = (FStar_Syntax_Print.term_to_string e1)
in (FStar_Util.print3 "Encoding let rec %s : %s = %s\n" uu____22125 uu____22126 uu____22127))))
end
| uu____22128 -> begin
()
end));
(

let uu____22129 = (destruct_bound_function fvb.fvar_lid t_norm1 e1)
in (match (uu____22129) with
| ((binders, body, formals, tres), curry) -> begin
((

let uu____22166 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env01.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____22166) with
| true -> begin
(

let uu____22167 = (FStar_Syntax_Print.binders_to_string ", " binders)
in (

let uu____22168 = (FStar_Syntax_Print.term_to_string body)
in (

let uu____22169 = (FStar_Syntax_Print.binders_to_string ", " formals)
in (

let uu____22170 = (FStar_Syntax_Print.term_to_string tres)
in (FStar_Util.print4 "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n" uu____22167 uu____22168 uu____22169 uu____22170)))))
end
| uu____22171 -> begin
()
end));
(match (curry) with
| true -> begin
(failwith "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type")
end
| uu____22173 -> begin
()
end);
(

let uu____22174 = (encode_binders FStar_Pervasives_Native.None binders env')
in (match (uu____22174) with
| (vars, guards, env'1, binder_decls, uu____22205) -> begin
(

let decl_g = (

let uu____22219 = (

let uu____22230 = (

let uu____22233 = (FStar_List.map FStar_Pervasives_Native.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::uu____22233)
in ((g), (uu____22230), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Fuel-instrumented function name"))))
in FStar_SMTEncoding_Term.DeclFun (uu____22219))
in (

let env02 = (push_zfuel_name env01 fvb.fvar_lid g)
in (

let decl_g_tok = FStar_SMTEncoding_Term.DeclFun (((gtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Token for fuel-instrumented partial applications"))))
in (

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let app = (

let uu____22246 = (

let uu____22253 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((fvb.smt_id), (uu____22253)))
in (FStar_SMTEncoding_Util.mkApp uu____22246))
in (

let gsapp = (

let uu____22259 = (

let uu____22266 = (

let uu____22269 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (uu____22269)::vars_tm)
in ((g), (uu____22266)))
in (FStar_SMTEncoding_Util.mkApp uu____22259))
in (

let gmax = (

let uu____22275 = (

let uu____22282 = (

let uu____22285 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (uu____22285)::vars_tm)
in ((g), (uu____22282)))
in (FStar_SMTEncoding_Util.mkApp uu____22275))
in (

let body1 = (

let uu____22291 = (FStar_TypeChecker_Env.is_reifiable_function env'1.tcenv t_norm1)
in (match (uu____22291) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env'1.tcenv body)
end
| uu____22292 -> begin
body
end))
in (

let uu____22293 = (encode_term body1 env'1)
in (match (uu____22293) with
| (body_tm, decls2) -> begin
(

let eqn_g = (

let uu____22311 = (

let uu____22318 = (

let uu____22319 = (

let uu____22334 = (FStar_SMTEncoding_Util.mkEq ((gsapp), (body_tm)))
in ((((gsapp)::[])::[]), (FStar_Pervasives_Native.Some ((Prims.parse_int "0"))), ((fuel)::vars), (uu____22334)))
in (FStar_SMTEncoding_Util.mkForall' uu____22319))
in (

let uu____22345 = (

let uu____22346 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" fvb.fvar_lid.FStar_Ident.str)
in FStar_Pervasives_Native.Some (uu____22346))
in ((uu____22318), (uu____22345), ((Prims.strcat "equation_with_fuel_" g)))))
in (FStar_SMTEncoding_Util.mkAssume uu____22311))
in (

let eqn_f = (

let uu____22348 = (

let uu____22355 = (

let uu____22356 = (

let uu____22367 = (FStar_SMTEncoding_Util.mkEq ((app), (gmax)))
in ((((app)::[])::[]), (vars), (uu____22367)))
in (FStar_SMTEncoding_Util.mkForall uu____22356))
in ((uu____22355), (FStar_Pervasives_Native.Some ("Correspondence of recursive function to instrumented version")), ((Prims.strcat "@fuel_correspondence_" g))))
in (FStar_SMTEncoding_Util.mkAssume uu____22348))
in (

let eqn_g' = (

let uu____22377 = (

let uu____22384 = (

let uu____22385 = (

let uu____22396 = (

let uu____22397 = (

let uu____22402 = (

let uu____22403 = (

let uu____22410 = (

let uu____22413 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "0"))
in (uu____22413)::vars_tm)
in ((g), (uu____22410)))
in (FStar_SMTEncoding_Util.mkApp uu____22403))
in ((gsapp), (uu____22402)))
in (FStar_SMTEncoding_Util.mkEq uu____22397))
in ((((gsapp)::[])::[]), ((fuel)::vars), (uu____22396)))
in (FStar_SMTEncoding_Util.mkForall uu____22385))
in ((uu____22384), (FStar_Pervasives_Native.Some ("Fuel irrelevance")), ((Prims.strcat "@fuel_irrelevance_" g))))
in (FStar_SMTEncoding_Util.mkAssume uu____22377))
in (

let uu____22424 = (

let uu____22433 = (encode_binders FStar_Pervasives_Native.None formals env02)
in (match (uu____22433) with
| (vars1, v_guards, env4, binder_decls1, uu____22462) -> begin
(

let vars_tm1 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars1)
in (

let gapp = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::vars_tm1)))
in (

let tok_corr = (

let tok_app = (

let uu____22483 = (FStar_SMTEncoding_Util.mkFreeV ((gtok), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply uu____22483 ((fuel)::vars1)))
in (

let uu____22484 = (

let uu____22491 = (

let uu____22492 = (

let uu____22503 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (gapp)))
in ((((tok_app)::[])::[]), ((fuel)::vars1), (uu____22503)))
in (FStar_SMTEncoding_Util.mkForall uu____22492))
in ((uu____22491), (FStar_Pervasives_Native.Some ("Fuel token correspondence")), ((Prims.strcat "fuel_token_correspondence_" gtok))))
in (FStar_SMTEncoding_Util.mkAssume uu____22484)))
in (

let uu____22512 = (

let uu____22519 = (encode_term_pred FStar_Pervasives_Native.None tres env4 gapp)
in (match (uu____22519) with
| (g_typing, d3) -> begin
(

let uu____22532 = (

let uu____22535 = (

let uu____22536 = (

let uu____22543 = (

let uu____22544 = (

let uu____22555 = (

let uu____22556 = (

let uu____22561 = (FStar_SMTEncoding_Util.mk_and_l v_guards)
in ((uu____22561), (g_typing)))
in (FStar_SMTEncoding_Util.mkImp uu____22556))
in ((((gapp)::[])::[]), ((fuel)::vars1), (uu____22555)))
in (FStar_SMTEncoding_Util.mkForall uu____22544))
in ((uu____22543), (FStar_Pervasives_Native.Some ("Typing correspondence of token to term")), ((Prims.strcat "token_correspondence_" g))))
in (FStar_SMTEncoding_Util.mkAssume uu____22536))
in (uu____22535)::[])
in ((d3), (uu____22532)))
end))
in (match (uu____22512) with
| (aux_decls, typing_corr) -> begin
(((FStar_List.append binder_decls1 aux_decls)), ((FStar_List.append typing_corr ((tok_corr)::[]))))
end)))))
end))
in (match (uu____22424) with
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

let uu____22614 = (

let uu____22627 = (FStar_List.zip3 gtoks1 typs2 bindings1)
in (FStar_List.fold_left (fun uu____22684 uu____22685 -> (match (((uu____22684), (uu____22685))) with
| ((decls2, eqns, env01), (gtok, ty, lb)) -> begin
(

let uu____22800 = (encode_one_binding env01 gtok ty lb)
in (match (uu____22800) with
| (decls', eqns', env02) -> begin
(((decls')::decls2), ((FStar_List.append eqns' eqns)), (env02))
end))
end)) (((decls1)::[]), ([]), (env0)) uu____22627))
in (match (uu____22614) with
| (decls2, eqns, env01) -> begin
(

let uu____22873 = (

let isDeclFun = (fun uu___97_22887 -> (match (uu___97_22887) with
| FStar_SMTEncoding_Term.DeclFun (uu____22888) -> begin
true
end
| uu____22899 -> begin
false
end))
in (

let uu____22900 = (FStar_All.pipe_right decls2 FStar_List.flatten)
in (FStar_All.pipe_right uu____22900 (FStar_List.partition isDeclFun))))
in (match (uu____22873) with
| (prefix_decls, rest) -> begin
(

let eqns1 = (FStar_List.rev eqns)
in (((FStar_List.append prefix_decls (FStar_List.append rest eqns1))), (env01)))
end))
end))))
end))))))
in (

let uu____22940 = ((FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___98_22944 -> (match (uu___98_22944) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| uu____22945 -> begin
false
end)))) || (FStar_All.pipe_right typs1 (FStar_Util.for_some (fun t -> (

let uu____22951 = ((FStar_Syntax_Util.is_pure_or_ghost_function t) || (FStar_TypeChecker_Env.is_reifiable_function env1.tcenv t))
in (FStar_All.pipe_left Prims.op_Negation uu____22951))))))
in (match (uu____22940) with
| true -> begin
((decls1), (env1))
end
| uu____22960 -> begin
(FStar_All.try_with (fun uu___131_22968 -> (match (()) with
| () -> begin
(match ((not (is_rec))) with
| true -> begin
(encode_non_rec_lbdef bindings typs1 toks_fvbs env1)
end
| uu____22981 -> begin
(encode_rec_lbdefs bindings typs1 toks_fvbs env1)
end)
end)) (fun uu___130_22983 -> (match (uu___130_22983) with
| Inner_let_rec -> begin
((decls1), (env1))
end)))
end))))))))
end))
end))
end)) (fun uu___126_22995 -> (match (uu___126_22995) with
| Let_rec_unencodeable -> begin
(

let msg = (

let uu____23003 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right uu____23003 (FStar_String.concat " and ")))
in (

let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in (((decl)::[]), (env))))
end)))))
end))


let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let nm = (

let uu____23064 = (FStar_Syntax_Util.lid_of_sigelt se)
in (match (uu____23064) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (l) -> begin
l.FStar_Ident.str
end))
in (

let uu____23068 = (encode_sigelt' env se)
in (match (uu____23068) with
| (g, env1) -> begin
(

let g1 = (match (g) with
| [] -> begin
(

let uu____23080 = (

let uu____23081 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (uu____23081))
in (uu____23080)::[])
end
| uu____23082 -> begin
(

let uu____23083 = (

let uu____23086 = (

let uu____23087 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____23087))
in (uu____23086)::g)
in (

let uu____23088 = (

let uu____23091 = (

let uu____23092 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____23092))
in (uu____23091)::[])
in (FStar_List.append uu____23083 uu____23088)))
end)
in ((g1), (env1)))
end))))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let is_opaque_to_smt = (fun t -> (

let uu____23105 = (

let uu____23106 = (FStar_Syntax_Subst.compress t)
in uu____23106.FStar_Syntax_Syntax.n)
in (match (uu____23105) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____23110)) -> begin
(Prims.op_Equality s "opaque_to_smt")
end
| uu____23111 -> begin
false
end)))
in (

let is_uninterpreted_by_smt = (fun t -> (

let uu____23118 = (

let uu____23119 = (FStar_Syntax_Subst.compress t)
in uu____23119.FStar_Syntax_Syntax.n)
in (match (uu____23118) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____23123)) -> begin
(Prims.op_Equality s "uninterpreted_by_smt")
end
| uu____23124 -> begin
false
end)))
in (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____23129) -> begin
(failwith "impossible -- new_effect_for_free should have been removed by Tc.fs")
end
| FStar_Syntax_Syntax.Sig_splice (uu____23134) -> begin
(failwith "impossible -- splice should have been removed by Tc.fs")
end
| FStar_Syntax_Syntax.Sig_pragma (uu____23145) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_main (uu____23146) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____23147) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____23160) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(

let uu____23162 = (

let uu____23163 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right uu____23163 Prims.op_Negation))
in (match (uu____23162) with
| true -> begin
(([]), (env))
end
| uu____23170 -> begin
(

let close_effect_params = (fun tm -> (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
tm
end
| uu____23189 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((ed.FStar_Syntax_Syntax.binders), (tm), (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[]))))))) FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)
end))
in (

let encode_action = (fun env1 a -> (

let uu____23219 = (FStar_Syntax_Util.arrow_formals_comp a.FStar_Syntax_Syntax.action_typ)
in (match (uu____23219) with
| (formals, uu____23237) -> begin
(

let arity = (FStar_List.length formals)
in (

let uu____23255 = (new_term_constant_and_tok_from_lid env1 a.FStar_Syntax_Syntax.action_name arity)
in (match (uu____23255) with
| (aname, atok, env2) -> begin
(

let uu____23275 = (

let uu____23280 = (close_effect_params a.FStar_Syntax_Syntax.action_defn)
in (encode_term uu____23280 env2))
in (match (uu____23275) with
| (tm, decls) -> begin
(

let a_decls = (

let uu____23292 = (

let uu____23293 = (

let uu____23304 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____23320 -> FStar_SMTEncoding_Term.Term_sort)))
in ((aname), (uu____23304), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Action"))))
in FStar_SMTEncoding_Term.DeclFun (uu____23293))
in (uu____23292)::(FStar_SMTEncoding_Term.DeclFun (((atok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Action token")))))::[])
in (

let uu____23329 = (

let aux = (fun uu____23385 uu____23386 -> (match (((uu____23385), (uu____23386))) with
| ((bv, uu____23438), (env3, acc_sorts, acc)) -> begin
(

let uu____23476 = (gen_term_var env3 bv)
in (match (uu____23476) with
| (xxsym, xx, env4) -> begin
((env4), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::acc_sorts), ((xx)::acc))
end))
end))
in (FStar_List.fold_right aux formals ((env2), ([]), ([]))))
in (match (uu____23329) with
| (uu____23548, xs_sorts, xs) -> begin
(

let app = (FStar_SMTEncoding_Util.mkApp ((aname), (xs)))
in (

let a_eq = (

let uu____23571 = (

let uu____23578 = (

let uu____23579 = (

let uu____23590 = (

let uu____23591 = (

let uu____23596 = (mk_Apply tm xs_sorts)
in ((app), (uu____23596)))
in (FStar_SMTEncoding_Util.mkEq uu____23591))
in ((((app)::[])::[]), (xs_sorts), (uu____23590)))
in (FStar_SMTEncoding_Util.mkForall uu____23579))
in ((uu____23578), (FStar_Pervasives_Native.Some ("Action equality")), ((Prims.strcat aname "_equality"))))
in (FStar_SMTEncoding_Util.mkAssume uu____23571))
in (

let tok_correspondence = (

let tok_term = (FStar_SMTEncoding_Util.mkFreeV ((atok), (FStar_SMTEncoding_Term.Term_sort)))
in (

let tok_app = (mk_Apply tok_term xs_sorts)
in (

let uu____23608 = (

let uu____23615 = (

let uu____23616 = (

let uu____23627 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (app)))
in ((((tok_app)::[])::[]), (xs_sorts), (uu____23627)))
in (FStar_SMTEncoding_Util.mkForall uu____23616))
in ((uu____23615), (FStar_Pervasives_Native.Some ("Action token correspondence")), ((Prims.strcat aname "_token_correspondence"))))
in (FStar_SMTEncoding_Util.mkAssume uu____23608))))
in ((env2), ((FStar_List.append decls (FStar_List.append a_decls ((a_eq)::(tok_correspondence)::[]))))))))
end)))
end))
end)))
end)))
in (

let uu____23638 = (FStar_Util.fold_map encode_action env ed.FStar_Syntax_Syntax.actions)
in (match (uu____23638) with
| (env1, decls2) -> begin
(((FStar_List.flatten decls2)), (env1))
end))))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____23664, uu____23665) when (FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid) -> begin
(

let uu____23666 = (new_term_constant_and_tok_from_lid env lid (Prims.parse_int "4"))
in (match (uu____23666) with
| (tname, ttok, env1) -> begin
(([]), (env1))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____23681, t) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let will_encode_definition = (

let uu____23687 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___99_23691 -> (match (uu___99_23691) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.Projector (uu____23692) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____23697) -> begin
true
end
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| uu____23698 -> begin
false
end))))
in (not (uu____23687)))
in (match (will_encode_definition) with
| true -> begin
(([]), (env))
end
| uu____23703 -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____23705 = (

let uu____23712 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs (FStar_Util.for_some is_uninterpreted_by_smt))
in (encode_top_level_val uu____23712 env fv t quals))
in (match (uu____23705) with
| (decls, env1) -> begin
(

let tname = lid.FStar_Ident.str
in (

let tsym = (FStar_SMTEncoding_Util.mkFreeV ((tname), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____23727 = (

let uu____23728 = (primitive_type_axioms env1.tcenv lid tname tsym)
in (FStar_List.append decls uu____23728))
in ((uu____23727), (env1)))))
end)))
end)))
end
| FStar_Syntax_Syntax.Sig_assume (l, us, f) -> begin
(

let uu____23734 = (FStar_Syntax_Subst.open_univ_vars us f)
in (match (uu____23734) with
| (uu____23743, f1) -> begin
(

let uu____23745 = (encode_formula f1 env)
in (match (uu____23745) with
| (f2, decls) -> begin
(

let g = (

let uu____23759 = (

let uu____23760 = (

let uu____23767 = (

let uu____23768 = (

let uu____23769 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" uu____23769))
in FStar_Pervasives_Native.Some (uu____23768))
in (

let uu____23770 = (varops.mk_unique (Prims.strcat "assumption_" l.FStar_Ident.str))
in ((f2), (uu____23767), (uu____23770))))
in (FStar_SMTEncoding_Util.mkAssume uu____23760))
in (uu____23759)::[])
in (((FStar_List.append decls g)), (env)))
end))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____23772) when ((FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) || (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs (FStar_Util.for_some is_opaque_to_smt))) -> begin
(

let attrs = se.FStar_Syntax_Syntax.sigattrs
in (

let uu____23784 = (FStar_Util.fold_map (fun env1 lb -> (

let lid = (

let uu____23806 = (

let uu____23809 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____23809.FStar_Syntax_Syntax.fv_name)
in uu____23806.FStar_Syntax_Syntax.v)
in (

let uu____23810 = (

let uu____23811 = (FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone uu____23811))
in (match (uu____23810) with
| true -> begin
(

let val_decl = (

let uu___132_23841 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = uu___132_23841.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Irreducible)::se.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___132_23841.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___132_23841.FStar_Syntax_Syntax.sigattrs})
in (

let uu____23842 = (encode_sigelt' env1 val_decl)
in (match (uu____23842) with
| (decls, env2) -> begin
((env2), (decls))
end)))
end
| uu____23857 -> begin
((env1), ([]))
end)))) env (FStar_Pervasives_Native.snd lbs))
in (match (uu____23784) with
| (env1, decls) -> begin
(((FStar_List.flatten decls)), (env1))
end)))
end
| FStar_Syntax_Syntax.Sig_let ((uu____23876, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t1); FStar_Syntax_Syntax.lbunivs = uu____23878; FStar_Syntax_Syntax.lbtyp = uu____23879; FStar_Syntax_Syntax.lbeff = uu____23880; FStar_Syntax_Syntax.lbdef = uu____23881; FStar_Syntax_Syntax.lbattrs = uu____23882; FStar_Syntax_Syntax.lbpos = uu____23883})::[]), uu____23884) when (FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid) -> begin
(

let uu____23901 = (new_term_constant_and_tok_from_lid env b2t1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v (Prims.parse_int "1"))
in (match (uu____23901) with
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

let uu____23930 = (

let uu____23933 = (

let uu____23934 = (

let uu____23941 = (

let uu____23942 = (

let uu____23953 = (

let uu____23954 = (

let uu____23959 = (FStar_SMTEncoding_Util.mkApp (((FStar_Pervasives_Native.snd FStar_SMTEncoding_Term.boxBoolFun)), ((x)::[])))
in ((valid_b2t_x), (uu____23959)))
in (FStar_SMTEncoding_Util.mkEq uu____23954))
in ((((b2t_x)::[])::[]), ((xx)::[]), (uu____23953)))
in (FStar_SMTEncoding_Util.mkForall uu____23942))
in ((uu____23941), (FStar_Pervasives_Native.Some ("b2t def")), ("b2t_def")))
in (FStar_SMTEncoding_Util.mkAssume uu____23934))
in (uu____23933)::[])
in (FStar_SMTEncoding_Term.DeclFun (((tname), ((FStar_SMTEncoding_Term.Term_sort)::[]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None))))::uu____23930)
in ((decls), (env1)))))))
end))
end
| FStar_Syntax_Syntax.Sig_let (uu____23980, uu____23981) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___100_23990 -> (match (uu___100_23990) with
| FStar_Syntax_Syntax.Discriminator (uu____23991) -> begin
true
end
| uu____23992 -> begin
false
end)))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let (uu____23993, lids) when ((FStar_All.pipe_right lids (FStar_Util.for_some (fun l -> (

let uu____24004 = (

let uu____24005 = (FStar_List.hd l.FStar_Ident.ns)
in uu____24005.FStar_Ident.idText)
in (Prims.op_Equality uu____24004 "Prims"))))) && (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___101_24009 -> (match (uu___101_24009) with
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
true
end
| uu____24010 -> begin
false
end))))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____24012) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___102_24023 -> (match (uu___102_24023) with
| FStar_Syntax_Syntax.Projector (uu____24024) -> begin
true
end
| uu____24029 -> begin
false
end)))) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____24032 = (try_lookup_free_var env l)
in (match (uu____24032) with
| FStar_Pervasives_Native.Some (uu____24039) -> begin
(([]), (env))
end
| FStar_Pervasives_Native.None -> begin
(

let se1 = (

let uu___133_24041 = se
in (

let uu____24042 = (FStar_Ident.range_of_lid l)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = uu____24042; FStar_Syntax_Syntax.sigquals = uu___133_24041.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___133_24041.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___133_24041.FStar_Syntax_Syntax.sigattrs}))
in (encode_sigelt env se1))
end))))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), uu____24045) -> begin
(encode_top_level_let env ((is_rec), (bindings)) se.FStar_Syntax_Syntax.sigquals)
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____24057) -> begin
(

let uu____24066 = (encode_sigelts env ses)
in (match (uu____24066) with
| (g, env1) -> begin
(

let uu____24083 = (FStar_All.pipe_right g (FStar_List.partition (fun uu___103_24106 -> (match (uu___103_24106) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.assumption_term = uu____24107; FStar_SMTEncoding_Term.assumption_caption = FStar_Pervasives_Native.Some ("inversion axiom"); FStar_SMTEncoding_Term.assumption_name = uu____24108; FStar_SMTEncoding_Term.assumption_fact_ids = uu____24109}) -> begin
false
end
| uu____24112 -> begin
true
end))))
in (match (uu____24083) with
| (g', inversions) -> begin
(

let uu____24127 = (FStar_All.pipe_right g' (FStar_List.partition (fun uu___104_24148 -> (match (uu___104_24148) with
| FStar_SMTEncoding_Term.DeclFun (uu____24149) -> begin
true
end
| uu____24160 -> begin
false
end))))
in (match (uu____24127) with
| (decls, rest) -> begin
(((FStar_List.append decls (FStar_List.append rest inversions))), (env1))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, uu____24176, tps, k, uu____24179, datas) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___105_24196 -> (match (uu___105_24196) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____24197 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> (match (is_logical) with
| true -> begin
(

let uu____24208 = c
in (match (uu____24208) with
| (name, args, uu____24213, uu____24214, uu____24215) -> begin
(

let uu____24220 = (

let uu____24221 = (

let uu____24232 = (FStar_All.pipe_right args (FStar_List.map (fun uu____24255 -> (match (uu____24255) with
| (uu____24262, sort, uu____24264) -> begin
sort
end))))
in ((name), (uu____24232), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____24221))
in (uu____24220)::[])
end))
end
| uu____24267 -> begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end))
in (

let inversion_axioms = (fun tapp vars -> (

let uu____24293 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (

let uu____24299 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right uu____24299 FStar_Option.isNone)))))
in (match (uu____24293) with
| true -> begin
[]
end
| uu____24330 -> begin
(

let uu____24331 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____24331) with
| (xxsym, xx) -> begin
(

let uu____24340 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun uu____24379 l -> (match (uu____24379) with
| (out, decls) -> begin
(

let uu____24399 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (uu____24399) with
| (uu____24410, data_t) -> begin
(

let uu____24412 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (uu____24412) with
| (args, res) -> begin
(

let indices = (

let uu____24450 = (

let uu____24451 = (FStar_Syntax_Subst.compress res)
in uu____24451.FStar_Syntax_Syntax.n)
in (match (uu____24450) with
| FStar_Syntax_Syntax.Tm_app (uu____24454, indices) -> begin
indices
end
| uu____24476 -> begin
[]
end))
in (

let env1 = (FStar_All.pipe_right args (FStar_List.fold_left (fun env1 uu____24500 -> (match (uu____24500) with
| (x, uu____24506) -> begin
(

let uu____24507 = (

let uu____24508 = (

let uu____24515 = (mk_term_projector_name l x)
in ((uu____24515), ((xx)::[])))
in (FStar_SMTEncoding_Util.mkApp uu____24508))
in (push_term_var env1 x uu____24507))
end)) env))
in (

let uu____24518 = (encode_args indices env1)
in (match (uu____24518) with
| (indices1, decls') -> begin
((match ((Prims.op_disEquality (FStar_List.length indices1) (FStar_List.length vars))) with
| true -> begin
(failwith "Impossible")
end
| uu____24542 -> begin
()
end);
(

let eqs = (

let uu____24544 = (FStar_List.map2 (fun v1 a -> (

let uu____24560 = (

let uu____24565 = (FStar_SMTEncoding_Util.mkFreeV v1)
in ((uu____24565), (a)))
in (FStar_SMTEncoding_Util.mkEq uu____24560))) vars indices1)
in (FStar_All.pipe_right uu____24544 FStar_SMTEncoding_Util.mk_and_l))
in (

let uu____24568 = (

let uu____24569 = (

let uu____24574 = (

let uu____24575 = (

let uu____24580 = (mk_data_tester env1 l xx)
in ((uu____24580), (eqs)))
in (FStar_SMTEncoding_Util.mkAnd uu____24575))
in ((out), (uu____24574)))
in (FStar_SMTEncoding_Util.mkOr uu____24569))
in ((uu____24568), ((FStar_List.append decls decls')))));
)
end))))
end))
end))
end)) ((FStar_SMTEncoding_Util.mkFalse), ([]))))
in (match (uu____24340) with
| (data_ax, decls) -> begin
(

let uu____24593 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____24593) with
| (ffsym, ff) -> begin
(

let fuel_guarded_inversion = (

let xx_has_type_sfuel = (match (((FStar_List.length datas) > (Prims.parse_int "1"))) with
| true -> begin
(

let uu____24604 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((ff)::[])))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel uu____24604 xx tapp))
end
| uu____24607 -> begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end)
in (

let uu____24608 = (

let uu____24615 = (

let uu____24616 = (

let uu____24627 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (

let uu____24636 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_sfuel), (data_ax)))
in ((((xx_has_type_sfuel)::[])::[]), (uu____24627), (uu____24636))))
in (FStar_SMTEncoding_Util.mkForall uu____24616))
in (

let uu____24645 = (varops.mk_unique (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str))
in ((uu____24615), (FStar_Pervasives_Native.Some ("inversion axiom")), (uu____24645))))
in (FStar_SMTEncoding_Util.mkAssume uu____24608)))
in (FStar_List.append decls ((fuel_guarded_inversion)::[])))
end))
end))
end))
end)))
in (

let uu____24646 = (

let uu____24659 = (

let uu____24660 = (FStar_Syntax_Subst.compress k)
in uu____24660.FStar_Syntax_Syntax.n)
in (match (uu____24659) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
(((FStar_List.append tps formals)), ((FStar_Syntax_Util.comp_result kres)))
end
| uu____24705 -> begin
((tps), (k))
end))
in (match (uu____24646) with
| (formals, res) -> begin
(

let uu____24728 = (FStar_Syntax_Subst.open_term formals res)
in (match (uu____24728) with
| (formals1, res1) -> begin
(

let uu____24739 = (encode_binders FStar_Pervasives_Native.None formals1 env)
in (match (uu____24739) with
| (vars, guards, env', binder_decls, uu____24764) -> begin
(

let arity = (FStar_List.length vars)
in (

let uu____24778 = (new_term_constant_and_tok_from_lid env t arity)
in (match (uu____24778) with
| (tname, ttok, env1) -> begin
(

let ttok_tm = (FStar_SMTEncoding_Util.mkApp ((ttok), ([])))
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let tapp = (

let uu____24801 = (

let uu____24808 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((tname), (uu____24808)))
in (FStar_SMTEncoding_Util.mkApp uu____24801))
in (

let uu____24813 = (

let tname_decl = (

let uu____24823 = (

let uu____24824 = (FStar_All.pipe_right vars (FStar_List.map (fun uu____24848 -> (match (uu____24848) with
| (n1, s) -> begin
(((Prims.strcat tname n1)), (s), (false))
end))))
in (

let uu____24861 = (varops.next_id ())
in ((tname), (uu____24824), (FStar_SMTEncoding_Term.Term_sort), (uu____24861), (false))))
in (constructor_or_logic_type_decl uu____24823))
in (

let uu____24864 = (match (vars) with
| [] -> begin
(

let uu____24877 = (

let uu____24878 = (

let uu____24881 = (FStar_SMTEncoding_Util.mkApp ((tname), ([])))
in (FStar_All.pipe_left (fun _0_20 -> FStar_Pervasives_Native.Some (_0_20)) uu____24881))
in (replace_free_var env1 t arity tname uu____24878))
in (([]), (uu____24877)))
end
| uu____24892 -> begin
(

let ttok_decl = FStar_SMTEncoding_Term.DeclFun (((ttok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("token"))))
in (

let ttok_fresh = (

let uu____24899 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ttok), (FStar_SMTEncoding_Term.Term_sort)) uu____24899))
in (

let ttok_app = (mk_Apply ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (

let uu____24913 = (

let uu____24920 = (

let uu____24921 = (

let uu____24936 = (FStar_SMTEncoding_Util.mkEq ((ttok_app), (tapp)))
in ((pats), (FStar_Pervasives_Native.None), (vars), (uu____24936)))
in (FStar_SMTEncoding_Util.mkForall' uu____24921))
in ((uu____24920), (FStar_Pervasives_Native.Some ("name-token correspondence")), ((Prims.strcat "token_correspondence_" ttok))))
in (FStar_SMTEncoding_Util.mkAssume uu____24913))
in (((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[]), (env1)))))))
end)
in (match (uu____24864) with
| (tok_decls, env2) -> begin
(((FStar_List.append tname_decl tok_decls)), (env2))
end)))
in (match (uu____24813) with
| (decls, env2) -> begin
(

let kindingAx = (

let uu____24972 = (encode_term_pred FStar_Pervasives_Native.None res1 env' tapp)
in (match (uu____24972) with
| (k1, decls1) -> begin
(

let karr = (match (((FStar_List.length formals1) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____24990 = (

let uu____24991 = (

let uu____24998 = (

let uu____24999 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____24999))
in ((uu____24998), (FStar_Pervasives_Native.Some ("kinding")), ((Prims.strcat "pre_kinding_" ttok))))
in (FStar_SMTEncoding_Util.mkAssume uu____24991))
in (uu____24990)::[])
end
| uu____25000 -> begin
[]
end)
in (

let uu____25001 = (

let uu____25004 = (

let uu____25007 = (

let uu____25008 = (

let uu____25015 = (

let uu____25016 = (

let uu____25027 = (FStar_SMTEncoding_Util.mkImp ((guard), (k1)))
in ((((tapp)::[])::[]), (vars), (uu____25027)))
in (FStar_SMTEncoding_Util.mkForall uu____25016))
in ((uu____25015), (FStar_Pervasives_Native.None), ((Prims.strcat "kinding_" ttok))))
in (FStar_SMTEncoding_Util.mkAssume uu____25008))
in (uu____25007)::[])
in (FStar_List.append karr uu____25004))
in (FStar_List.append decls1 uu____25001)))
end))
in (

let aux = (

let uu____25039 = (

let uu____25042 = (inversion_axioms tapp vars)
in (

let uu____25045 = (

let uu____25048 = (pretype_axiom env2 tapp vars)
in (uu____25048)::[])
in (FStar_List.append uu____25042 uu____25045)))
in (FStar_List.append kindingAx uu____25039))
in (

let g = (FStar_List.append decls (FStar_List.append binder_decls aux))
in ((g), (env2)))))
end)))))
end)))
end))
end))
end))))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____25053, uu____25054, uu____25055, uu____25056, uu____25057) when (FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____25063, t, uu____25065, n_tps, uu____25067) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____25075 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____25075) with
| (formals, t_res) -> begin
(

let arity = (FStar_List.length formals)
in (

let uu____25115 = (new_term_constant_and_tok_from_lid env d arity)
in (match (uu____25115) with
| (ddconstrsym, ddtok, env1) -> begin
(

let ddtok_tm = (FStar_SMTEncoding_Util.mkApp ((ddtok), ([])))
in (

let uu____25136 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____25136) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (

let uu____25150 = (encode_binders (FStar_Pervasives_Native.Some (fuel_tm)) formals env1)
in (match (uu____25150) with
| (vars, guards, env', binder_decls, names1) -> begin
(

let fields = (FStar_All.pipe_right names1 (FStar_List.mapi (fun n1 x -> (

let projectible = true
in (

let uu____25208 = (mk_term_projector_name d x)
in ((uu____25208), (FStar_SMTEncoding_Term.Term_sort), (projectible)))))))
in (

let datacons = (

let uu____25212 = (

let uu____25213 = (varops.next_id ())
in ((ddconstrsym), (fields), (FStar_SMTEncoding_Term.Term_sort), (uu____25213), (true)))
in (FStar_All.pipe_right uu____25212 FStar_SMTEncoding_Term.constructor_to_decl))
in (

let app = (mk_Apply ddtok_tm vars)
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (

let uu____25226 = (encode_term_pred FStar_Pervasives_Native.None t env1 ddtok_tm)
in (match (uu____25226) with
| (tok_typing, decls3) -> begin
(

let tok_typing1 = (match (fields) with
| (uu____25238)::uu____25239 -> begin
(

let ff = (("ty"), (FStar_SMTEncoding_Term.Term_sort))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV ff)
in (

let vtok_app_l = (mk_Apply ddtok_tm ((ff)::[]))
in (

let vtok_app_r = (mk_Apply f ((((ddtok), (FStar_SMTEncoding_Term.Term_sort)))::[]))
in (

let uu____25266 = (

let uu____25277 = (FStar_SMTEncoding_Term.mk_NoHoist f tok_typing)
in ((((vtok_app_l)::[])::((vtok_app_r)::[])::[]), ((ff)::[]), (uu____25277)))
in (FStar_SMTEncoding_Util.mkForall uu____25266))))))
end
| uu____25296 -> begin
tok_typing
end)
in (

let uu____25299 = (encode_binders (FStar_Pervasives_Native.Some (fuel_tm)) formals env1)
in (match (uu____25299) with
| (vars', guards', env'', decls_formals, uu____25324) -> begin
(

let uu____25337 = (

let xvars1 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars')
in (

let dapp1 = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars1)))
in (encode_term_pred (FStar_Pervasives_Native.Some (fuel_tm)) t_res env'' dapp1)))
in (match (uu____25337) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_SMTEncoding_Util.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| uu____25364 -> begin
(

let uu____25371 = (

let uu____25372 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ddtok), (FStar_SMTEncoding_Term.Term_sort)) uu____25372))
in (uu____25371)::[])
end)
in (

let encode_elim = (fun uu____25384 -> (

let uu____25385 = (FStar_Syntax_Util.head_and_args t_res)
in (match (uu____25385) with
| (head1, args) -> begin
(

let uu____25428 = (

let uu____25429 = (FStar_Syntax_Subst.compress head1)
in uu____25429.FStar_Syntax_Syntax.n)
in (match (uu____25428) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____25439; FStar_Syntax_Syntax.vars = uu____25440}, uu____25441) -> begin
(

let uu____25446 = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (match (uu____25446) with
| (encoded_head, encoded_head_arity) -> begin
(

let uu____25459 = (encode_args args env')
in (match (uu____25459) with
| (encoded_args, arg_decls) -> begin
(

let guards_for_parameter = (fun orig_arg arg xv -> (

let fv1 = (match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv1) -> begin
fv1
end
| uu____25508 -> begin
(

let uu____25509 = (

let uu____25514 = (

let uu____25515 = (FStar_Syntax_Print.term_to_string orig_arg)
in (FStar_Util.format1 "Inductive type parameter %s must be a variable ; You may want to change it to an index." uu____25515))
in ((FStar_Errors.Fatal_NonVariableInductiveTypeParameter), (uu____25514)))
in (FStar_Errors.raise_error uu____25509 orig_arg.FStar_Syntax_Syntax.pos))
end)
in (

let guards1 = (FStar_All.pipe_right guards (FStar_List.collect (fun g -> (

let uu____25531 = (

let uu____25532 = (FStar_SMTEncoding_Term.free_variables g)
in (FStar_List.contains fv1 uu____25532))
in (match (uu____25531) with
| true -> begin
(

let uu____25545 = (FStar_SMTEncoding_Term.subst g fv1 xv)
in (uu____25545)::[])
end
| uu____25546 -> begin
[]
end)))))
in (FStar_SMTEncoding_Util.mk_and_l guards1))))
in (

let uu____25547 = (

let uu____25560 = (FStar_List.zip args encoded_args)
in (FStar_List.fold_left (fun uu____25610 uu____25611 -> (match (((uu____25610), (uu____25611))) with
| ((env2, arg_vars, eqns_or_guards, i), (orig_arg, arg)) -> begin
(

let uu____25706 = (

let uu____25713 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (gen_term_var env2 uu____25713))
in (match (uu____25706) with
| (uu____25726, xv, env3) -> begin
(

let eqns = (match ((i < n_tps)) with
| true -> begin
(

let uu____25734 = (guards_for_parameter (FStar_Pervasives_Native.fst orig_arg) arg xv)
in (uu____25734)::eqns_or_guards)
end
| uu____25735 -> begin
(

let uu____25736 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (uu____25736)::eqns_or_guards)
end)
in ((env3), ((xv)::arg_vars), (eqns), ((i + (Prims.parse_int "1")))))
end))
end)) ((env'), ([]), ([]), ((Prims.parse_int "0"))) uu____25560))
in (match (uu____25547) with
| (uu____25751, arg_vars, elim_eqns_or_guards, uu____25754) -> begin
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

let uu____25778 = (

let uu____25785 = (

let uu____25786 = (

let uu____25797 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____25798 = (

let uu____25799 = (

let uu____25804 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append elim_eqns_or_guards guards))
in ((ty_pred), (uu____25804)))
in (FStar_SMTEncoding_Util.mkImp uu____25799))
in ((((ty_pred)::[])::[]), (uu____25797), (uu____25798))))
in (FStar_SMTEncoding_Util.mkForall uu____25786))
in ((uu____25785), (FStar_Pervasives_Native.Some ("data constructor typing elim")), ((Prims.strcat "data_elim_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____25778))
in (

let subterm_ordering = (

let uu____25814 = (FStar_Ident.lid_equals d FStar_Parser_Const.lextop_lid)
in (match (uu____25814) with
| true -> begin
(

let x = (

let uu____25820 = (varops.fresh "x")
in ((uu____25820), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (

let uu____25822 = (

let uu____25829 = (

let uu____25830 = (

let uu____25841 = (

let uu____25846 = (

let uu____25849 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in (uu____25849)::[])
in (uu____25846)::[])
in (

let uu____25854 = (

let uu____25855 = (

let uu____25860 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (

let uu____25861 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in ((uu____25860), (uu____25861))))
in (FStar_SMTEncoding_Util.mkImp uu____25855))
in ((uu____25841), ((x)::[]), (uu____25854))))
in (FStar_SMTEncoding_Util.mkForall uu____25830))
in (

let uu____25874 = (varops.mk_unique "lextop")
in ((uu____25829), (FStar_Pervasives_Native.Some ("lextop is top")), (uu____25874))))
in (FStar_SMTEncoding_Util.mkAssume uu____25822))))
end
| uu____25875 -> begin
(

let prec = (

let uu____25879 = (FStar_All.pipe_right vars (FStar_List.mapi (fun i v1 -> (match ((i < n_tps)) with
| true -> begin
[]
end
| uu____25910 -> begin
(

let uu____25911 = (

let uu____25912 = (FStar_SMTEncoding_Util.mkFreeV v1)
in (FStar_SMTEncoding_Util.mk_Precedes uu____25912 dapp1))
in (uu____25911)::[])
end))))
in (FStar_All.pipe_right uu____25879 FStar_List.flatten))
in (

let uu____25919 = (

let uu____25926 = (

let uu____25927 = (

let uu____25938 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____25939 = (

let uu____25940 = (

let uu____25945 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (uu____25945)))
in (FStar_SMTEncoding_Util.mkImp uu____25940))
in ((((ty_pred)::[])::[]), (uu____25938), (uu____25939))))
in (FStar_SMTEncoding_Util.mkForall uu____25927))
in ((uu____25926), (FStar_Pervasives_Native.Some ("subterm ordering")), ((Prims.strcat "subterm_ordering_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____25919)))
end))
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____25957 = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (match (uu____25957) with
| (encoded_head, encoded_head_arity) -> begin
(

let uu____25970 = (encode_args args env')
in (match (uu____25970) with
| (encoded_args, arg_decls) -> begin
(

let guards_for_parameter = (fun orig_arg arg xv -> (

let fv1 = (match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv1) -> begin
fv1
end
| uu____26019 -> begin
(

let uu____26020 = (

let uu____26025 = (

let uu____26026 = (FStar_Syntax_Print.term_to_string orig_arg)
in (FStar_Util.format1 "Inductive type parameter %s must be a variable ; You may want to change it to an index." uu____26026))
in ((FStar_Errors.Fatal_NonVariableInductiveTypeParameter), (uu____26025)))
in (FStar_Errors.raise_error uu____26020 orig_arg.FStar_Syntax_Syntax.pos))
end)
in (

let guards1 = (FStar_All.pipe_right guards (FStar_List.collect (fun g -> (

let uu____26042 = (

let uu____26043 = (FStar_SMTEncoding_Term.free_variables g)
in (FStar_List.contains fv1 uu____26043))
in (match (uu____26042) with
| true -> begin
(

let uu____26056 = (FStar_SMTEncoding_Term.subst g fv1 xv)
in (uu____26056)::[])
end
| uu____26057 -> begin
[]
end)))))
in (FStar_SMTEncoding_Util.mk_and_l guards1))))
in (

let uu____26058 = (

let uu____26071 = (FStar_List.zip args encoded_args)
in (FStar_List.fold_left (fun uu____26121 uu____26122 -> (match (((uu____26121), (uu____26122))) with
| ((env2, arg_vars, eqns_or_guards, i), (orig_arg, arg)) -> begin
(

let uu____26217 = (

let uu____26224 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (gen_term_var env2 uu____26224))
in (match (uu____26217) with
| (uu____26237, xv, env3) -> begin
(

let eqns = (match ((i < n_tps)) with
| true -> begin
(

let uu____26245 = (guards_for_parameter (FStar_Pervasives_Native.fst orig_arg) arg xv)
in (uu____26245)::eqns_or_guards)
end
| uu____26246 -> begin
(

let uu____26247 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (uu____26247)::eqns_or_guards)
end)
in ((env3), ((xv)::arg_vars), (eqns), ((i + (Prims.parse_int "1")))))
end))
end)) ((env'), ([]), ([]), ((Prims.parse_int "0"))) uu____26071))
in (match (uu____26058) with
| (uu____26262, arg_vars, elim_eqns_or_guards, uu____26265) -> begin
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

let uu____26289 = (

let uu____26296 = (

let uu____26297 = (

let uu____26308 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____26309 = (

let uu____26310 = (

let uu____26315 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append elim_eqns_or_guards guards))
in ((ty_pred), (uu____26315)))
in (FStar_SMTEncoding_Util.mkImp uu____26310))
in ((((ty_pred)::[])::[]), (uu____26308), (uu____26309))))
in (FStar_SMTEncoding_Util.mkForall uu____26297))
in ((uu____26296), (FStar_Pervasives_Native.Some ("data constructor typing elim")), ((Prims.strcat "data_elim_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____26289))
in (

let subterm_ordering = (

let uu____26325 = (FStar_Ident.lid_equals d FStar_Parser_Const.lextop_lid)
in (match (uu____26325) with
| true -> begin
(

let x = (

let uu____26331 = (varops.fresh "x")
in ((uu____26331), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (

let uu____26333 = (

let uu____26340 = (

let uu____26341 = (

let uu____26352 = (

let uu____26357 = (

let uu____26360 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in (uu____26360)::[])
in (uu____26357)::[])
in (

let uu____26365 = (

let uu____26366 = (

let uu____26371 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (

let uu____26372 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in ((uu____26371), (uu____26372))))
in (FStar_SMTEncoding_Util.mkImp uu____26366))
in ((uu____26352), ((x)::[]), (uu____26365))))
in (FStar_SMTEncoding_Util.mkForall uu____26341))
in (

let uu____26385 = (varops.mk_unique "lextop")
in ((uu____26340), (FStar_Pervasives_Native.Some ("lextop is top")), (uu____26385))))
in (FStar_SMTEncoding_Util.mkAssume uu____26333))))
end
| uu____26386 -> begin
(

let prec = (

let uu____26390 = (FStar_All.pipe_right vars (FStar_List.mapi (fun i v1 -> (match ((i < n_tps)) with
| true -> begin
[]
end
| uu____26421 -> begin
(

let uu____26422 = (

let uu____26423 = (FStar_SMTEncoding_Util.mkFreeV v1)
in (FStar_SMTEncoding_Util.mk_Precedes uu____26423 dapp1))
in (uu____26422)::[])
end))))
in (FStar_All.pipe_right uu____26390 FStar_List.flatten))
in (

let uu____26430 = (

let uu____26437 = (

let uu____26438 = (

let uu____26449 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____26450 = (

let uu____26451 = (

let uu____26456 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (uu____26456)))
in (FStar_SMTEncoding_Util.mkImp uu____26451))
in ((((ty_pred)::[])::[]), (uu____26449), (uu____26450))))
in (FStar_SMTEncoding_Util.mkForall uu____26438))
in ((uu____26437), (FStar_Pervasives_Native.Some ("subterm ordering")), ((Prims.strcat "subterm_ordering_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____26430)))
end))
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end)))
end))
end))
end
| uu____26467 -> begin
((

let uu____26469 = (

let uu____26474 = (

let uu____26475 = (FStar_Syntax_Print.lid_to_string d)
in (

let uu____26476 = (FStar_Syntax_Print.term_to_string head1)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" uu____26475 uu____26476)))
in ((FStar_Errors.Warning_ConstructorBuildsUnexpectedType), (uu____26474)))
in (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng uu____26469));
(([]), ([]));
)
end))
end)))
in (

let uu____26481 = (encode_elim ())
in (match (uu____26481) with
| (decls2, elim) -> begin
(

let g = (

let uu____26501 = (

let uu____26504 = (

let uu____26507 = (

let uu____26510 = (

let uu____26513 = (

let uu____26514 = (

let uu____26525 = (

let uu____26526 = (

let uu____26527 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" uu____26527))
in FStar_Pervasives_Native.Some (uu____26526))
in ((ddtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (uu____26525)))
in FStar_SMTEncoding_Term.DeclFun (uu____26514))
in (uu____26513)::[])
in (

let uu____26530 = (

let uu____26533 = (

let uu____26536 = (

let uu____26539 = (

let uu____26542 = (

let uu____26545 = (

let uu____26548 = (

let uu____26549 = (

let uu____26556 = (

let uu____26557 = (

let uu____26568 = (FStar_SMTEncoding_Util.mkEq ((app), (dapp)))
in ((((app)::[])::[]), (vars), (uu____26568)))
in (FStar_SMTEncoding_Util.mkForall uu____26557))
in ((uu____26556), (FStar_Pervasives_Native.Some ("equality for proxy")), ((Prims.strcat "equality_tok_" ddtok))))
in (FStar_SMTEncoding_Util.mkAssume uu____26549))
in (

let uu____26577 = (

let uu____26580 = (

let uu____26581 = (

let uu____26588 = (

let uu____26589 = (

let uu____26600 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) vars')
in (

let uu____26601 = (FStar_SMTEncoding_Util.mkImp ((guard'), (ty_pred')))
in ((((ty_pred')::[])::[]), (uu____26600), (uu____26601))))
in (FStar_SMTEncoding_Util.mkForall uu____26589))
in ((uu____26588), (FStar_Pervasives_Native.Some ("data constructor typing intro")), ((Prims.strcat "data_typing_intro_" ddtok))))
in (FStar_SMTEncoding_Util.mkAssume uu____26581))
in (uu____26580)::[])
in (uu____26548)::uu____26577))
in ((FStar_SMTEncoding_Util.mkAssume ((tok_typing1), (FStar_Pervasives_Native.Some ("typing for data constructor proxy")), ((Prims.strcat "typing_tok_" ddtok)))))::uu____26545)
in (FStar_List.append uu____26542 elim))
in (FStar_List.append decls_pred uu____26539))
in (FStar_List.append decls_formals uu____26536))
in (FStar_List.append proxy_fresh uu____26533))
in (FStar_List.append uu____26510 uu____26530)))
in (FStar_List.append decls3 uu____26507))
in (FStar_List.append decls2 uu____26504))
in (FStar_List.append binder_decls uu____26501))
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
and encode_sigelts : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun uu____26635 se -> (match (uu____26635) with
| (g, env1) -> begin
(

let uu____26655 = (encode_sigelt env1 se)
in (match (uu____26655) with
| (g', env2) -> begin
(((FStar_List.append g g')), (env2))
end))
end)) (([]), (env)))))


let encode_env_bindings : env_t  ->  FStar_Syntax_Syntax.binding Prims.list  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env bindings -> (

let encode_binding = (fun b uu____26720 -> (match (uu____26720) with
| (i, decls, env1) -> begin
(match (b) with
| FStar_Syntax_Syntax.Binding_univ (uu____26752) -> begin
(((i + (Prims.parse_int "1"))), (decls), (env1))
end
| FStar_Syntax_Syntax.Binding_var (x) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env1.tcenv x.FStar_Syntax_Syntax.sort)
in ((

let uu____26758 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____26758) with
| true -> begin
(

let uu____26759 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____26760 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____26761 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" uu____26759 uu____26760 uu____26761))))
end
| uu____26762 -> begin
()
end));
(

let uu____26763 = (encode_term t1 env1)
in (match (uu____26763) with
| (t, decls') -> begin
(

let t_hash = (FStar_SMTEncoding_Term.hash_of_term t)
in (

let uu____26779 = (

let uu____26786 = (

let uu____26787 = (

let uu____26788 = (FStar_Util.digest_of_string t_hash)
in (Prims.strcat uu____26788 (Prims.strcat "_" (Prims.string_of_int i))))
in (Prims.strcat "x_" uu____26787))
in (new_term_constant_from_string env1 x uu____26786))
in (match (uu____26779) with
| (xxsym, xx, env') -> begin
(

let t2 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel FStar_Pervasives_Native.None xx t)
in (

let caption = (

let uu____26802 = (FStar_Options.log_queries ())
in (match (uu____26802) with
| true -> begin
(

let uu____26803 = (

let uu____26804 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____26805 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____26806 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" uu____26804 uu____26805 uu____26806))))
in FStar_Pervasives_Native.Some (uu____26803))
end
| uu____26807 -> begin
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
| FStar_Syntax_Syntax.Binding_lid (x, (uu____26818, t)) -> begin
(

let t_norm = (whnf env1 t)
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____26838 = (encode_free_var false env1 fv t t_norm [])
in (match (uu____26838) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))))
end)
end))
in (

let uu____26861 = (FStar_List.fold_right encode_binding bindings (((Prims.parse_int "0")), ([]), (env)))
in (match (uu____26861) with
| (uu____26884, decls, env1) -> begin
((decls), (env1))
end))))


let encode_labels : 'Auu____26897 'Auu____26898 . ((Prims.string * FStar_SMTEncoding_Term.sort) * 'Auu____26897 * 'Auu____26898) Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl Prims.list) = (fun labs -> (

let prefix1 = (FStar_All.pipe_right labs (FStar_List.map (fun uu____26967 -> (match (uu____26967) with
| (l, uu____26979, uu____26980) -> begin
FStar_SMTEncoding_Term.DeclFun ((((FStar_Pervasives_Native.fst l)), ([]), (FStar_SMTEncoding_Term.Bool_sort), (FStar_Pervasives_Native.None)))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun uu____27024 -> (match (uu____27024) with
| (l, uu____27038, uu____27039) -> begin
(

let uu____27048 = (FStar_All.pipe_left (fun _0_21 -> FStar_SMTEncoding_Term.Echo (_0_21)) (FStar_Pervasives_Native.fst l))
in (

let uu____27049 = (

let uu____27052 = (

let uu____27053 = (FStar_SMTEncoding_Util.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (uu____27053))
in (uu____27052)::[])
in (uu____27048)::uu____27049))
end))))
in ((prefix1), (suffix)))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_TypeChecker_Env.env  ->  unit = (fun tcenv -> (

let uu____27080 = (

let uu____27083 = (

let uu____27084 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (

let uu____27087 = (

let uu____27088 = (FStar_TypeChecker_Env.current_module tcenv)
in (FStar_All.pipe_right uu____27088 FStar_Ident.string_of_lid))
in {bindings = []; depth = (Prims.parse_int "0"); tcenv = tcenv; warn = true; cache = uu____27084; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true; current_module_name = uu____27087}))
in (uu____27083)::[])
in (FStar_ST.op_Colon_Equals last_env uu____27080)))


let get_env : FStar_Ident.lident  ->  FStar_TypeChecker_Env.env  ->  env_t = (fun cmn tcenv -> (

let uu____27126 = (FStar_ST.op_Bang last_env)
in (match (uu____27126) with
| [] -> begin
(failwith "No env; call init first!")
end
| (e)::uu____27157 -> begin
(

let uu___134_27160 = e
in (

let uu____27161 = (FStar_Ident.string_of_lid cmn)
in {bindings = uu___134_27160.bindings; depth = uu___134_27160.depth; tcenv = tcenv; warn = uu___134_27160.warn; cache = uu___134_27160.cache; nolabels = uu___134_27160.nolabels; use_zfuel_name = uu___134_27160.use_zfuel_name; encode_non_total_function_typ = uu___134_27160.encode_non_total_function_typ; current_module_name = uu____27161}))
end)))


let set_env : env_t  ->  unit = (fun env -> (

let uu____27167 = (FStar_ST.op_Bang last_env)
in (match (uu____27167) with
| [] -> begin
(failwith "Empty env stack")
end
| (uu____27197)::tl1 -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl1))
end)))


let push_env : unit  ->  unit = (fun uu____27232 -> (

let uu____27233 = (FStar_ST.op_Bang last_env)
in (match (uu____27233) with
| [] -> begin
(failwith "Empty env stack")
end
| (hd1)::tl1 -> begin
(

let refs = (FStar_Util.smap_copy hd1.cache)
in (

let top = (

let uu___135_27271 = hd1
in {bindings = uu___135_27271.bindings; depth = uu___135_27271.depth; tcenv = uu___135_27271.tcenv; warn = uu___135_27271.warn; cache = refs; nolabels = uu___135_27271.nolabels; use_zfuel_name = uu___135_27271.use_zfuel_name; encode_non_total_function_typ = uu___135_27271.encode_non_total_function_typ; current_module_name = uu___135_27271.current_module_name})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd1)::tl1))))
end)))


let pop_env : unit  ->  unit = (fun uu____27303 -> (

let uu____27304 = (FStar_ST.op_Bang last_env)
in (match (uu____27304) with
| [] -> begin
(failwith "Popping an empty stack")
end
| (uu____27334)::tl1 -> begin
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
| ((uu____27416)::uu____27417, FStar_SMTEncoding_Term.Assume (a)) -> begin
FStar_SMTEncoding_Term.Assume ((

let uu___136_27425 = a
in {FStar_SMTEncoding_Term.assumption_term = uu___136_27425.FStar_SMTEncoding_Term.assumption_term; FStar_SMTEncoding_Term.assumption_caption = uu___136_27425.FStar_SMTEncoding_Term.assumption_caption; FStar_SMTEncoding_Term.assumption_name = uu___136_27425.FStar_SMTEncoding_Term.assumption_name; FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids}))
end
| uu____27426 -> begin
d
end))


let fact_dbs_for_lid : env_t  ->  FStar_Ident.lid  ->  FStar_SMTEncoding_Term.fact_db_id Prims.list = (fun env lid -> (

let uu____27445 = (

let uu____27448 = (

let uu____27449 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in FStar_SMTEncoding_Term.Namespace (uu____27449))
in (

let uu____27450 = (open_fact_db_tags env)
in (uu____27448)::uu____27450))
in (FStar_SMTEncoding_Term.Name (lid))::uu____27445))


let encode_top_level_facts : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env se -> (

let fact_db_ids = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.collect (fact_dbs_for_lid env)))
in (

let uu____27476 = (encode_sigelt env se)
in (match (uu____27476) with
| (g, env1) -> begin
(

let g1 = (FStar_All.pipe_right g (FStar_List.map (place_decl_in_fact_dbs env1 fact_db_ids)))
in ((g1), (env1)))
end))))


let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  unit = (fun tcenv se -> (

let caption = (fun decls -> (

let uu____27520 = (FStar_Options.log_queries ())
in (match (uu____27520) with
| true -> begin
(

let uu____27523 = (

let uu____27524 = (

let uu____27525 = (

let uu____27526 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.map FStar_Syntax_Print.lid_to_string))
in (FStar_All.pipe_right uu____27526 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " uu____27525))
in FStar_SMTEncoding_Term.Caption (uu____27524))
in (uu____27523)::decls)
end
| uu____27535 -> begin
decls
end)))
in ((

let uu____27537 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____27537) with
| true -> begin
(

let uu____27538 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____27538))
end
| uu____27539 -> begin
()
end));
(

let env = (

let uu____27541 = (FStar_TypeChecker_Env.current_module tcenv)
in (get_env uu____27541 tcenv))
in (

let uu____27542 = (encode_top_level_facts env se)
in (match (uu____27542) with
| (decls, env1) -> begin
((set_env env1);
(

let uu____27556 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 uu____27556));
)
end)));
)))


let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____27570 -> begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in ((

let uu____27572 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____27572) with
| true -> begin
(

let uu____27573 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) Prims.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name uu____27573))
end
| uu____27574 -> begin
()
end));
(

let env = (get_env modul.FStar_Syntax_Syntax.name tcenv)
in (

let encode_signature = (fun env1 ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun uu____27614 se -> (match (uu____27614) with
| (g, env2) -> begin
(

let uu____27634 = (encode_top_level_facts env2 se)
in (match (uu____27634) with
| (g', env3) -> begin
(((FStar_List.append g g')), (env3))
end))
end)) (([]), (env1)))))
in (

let uu____27657 = (encode_signature (

let uu___137_27666 = env
in {bindings = uu___137_27666.bindings; depth = uu___137_27666.depth; tcenv = uu___137_27666.tcenv; warn = false; cache = uu___137_27666.cache; nolabels = uu___137_27666.nolabels; use_zfuel_name = uu___137_27666.use_zfuel_name; encode_non_total_function_typ = uu___137_27666.encode_non_total_function_typ; current_module_name = uu___137_27666.current_module_name}) modul.FStar_Syntax_Syntax.exports)
in (match (uu____27657) with
| (decls, env1) -> begin
(

let caption = (fun decls1 -> (

let uu____27685 = (FStar_Options.log_queries ())
in (match (uu____27685) with
| true -> begin
(

let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::decls1) ((FStar_SMTEncoding_Term.Caption ((Prims.strcat "End " msg)))::[])))
end
| uu____27689 -> begin
decls1
end)))
in ((set_env (

let uu___138_27693 = env1
in {bindings = uu___138_27693.bindings; depth = uu___138_27693.depth; tcenv = uu___138_27693.tcenv; warn = true; cache = uu___138_27693.cache; nolabels = uu___138_27693.nolabels; use_zfuel_name = uu___138_27693.use_zfuel_name; encode_non_total_function_typ = uu___138_27693.encode_non_total_function_typ; current_module_name = uu___138_27693.current_module_name}));
(

let uu____27695 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____27695) with
| true -> begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end
| uu____27696 -> begin
()
end));
(

let decls1 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls1));
))
end))));
)))


let encode_query : (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_ErrorReporting.label Prims.list * FStar_SMTEncoding_Term.decl * FStar_SMTEncoding_Term.decl Prims.list) = (fun use_env_msg tcenv q -> ((

let uu____27753 = (

let uu____27754 = (FStar_TypeChecker_Env.current_module tcenv)
in uu____27754.FStar_Ident.str)
in (FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name uu____27753));
(

let env = (

let uu____27756 = (FStar_TypeChecker_Env.current_module tcenv)
in (get_env uu____27756 tcenv))
in (

let uu____27757 = (

let rec aux = (fun bindings -> (match (bindings) with
| (FStar_Syntax_Syntax.Binding_var (x))::rest -> begin
(

let uu____27794 = (aux rest)
in (match (uu____27794) with
| (out, rest1) -> begin
(

let t = (

let uu____27822 = (FStar_Syntax_Util.destruct_typ_as_formula x.FStar_Syntax_Syntax.sort)
in (match (uu____27822) with
| FStar_Pervasives_Native.Some (uu____27825) -> begin
(

let uu____27826 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.t_unit)
in (FStar_Syntax_Util.refine uu____27826 x.FStar_Syntax_Syntax.sort))
end
| uu____27827 -> begin
x.FStar_Syntax_Syntax.sort
end))
in (

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
in (

let uu____27831 = (

let uu____27834 = (FStar_Syntax_Syntax.mk_binder (

let uu___139_27837 = x
in {FStar_Syntax_Syntax.ppname = uu___139_27837.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___139_27837.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in (uu____27834)::out)
in ((uu____27831), (rest1)))))
end))
end
| uu____27842 -> begin
(([]), (bindings))
end))
in (

let uu____27849 = (aux tcenv.FStar_TypeChecker_Env.gamma)
in (match (uu____27849) with
| (closing, bindings) -> begin
(

let uu____27874 = (FStar_Syntax_Util.close_forall_no_univs (FStar_List.rev closing) q)
in ((uu____27874), (bindings)))
end)))
in (match (uu____27757) with
| (q1, bindings) -> begin
(

let uu____27897 = (encode_env_bindings env bindings)
in (match (uu____27897) with
| (env_decls, env1) -> begin
((

let uu____27919 = (((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTQuery"))))
in (match (uu____27919) with
| true -> begin
(

let uu____27920 = (FStar_Syntax_Print.term_to_string q1)
in (FStar_Util.print1 "Encoding query formula: %s\n" uu____27920))
end
| uu____27921 -> begin
()
end));
(

let uu____27922 = (encode_formula q1 env1)
in (match (uu____27922) with
| (phi, qdecls) -> begin
(

let uu____27943 = (

let uu____27948 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg uu____27948 phi))
in (match (uu____27943) with
| (labels, phi1) -> begin
(

let uu____27965 = (encode_labels labels)
in (match (uu____27965) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append env_decls (FStar_List.append label_prefix qdecls))
in (

let qry = (

let uu____28002 = (

let uu____28009 = (FStar_SMTEncoding_Util.mkNot phi1)
in (

let uu____28010 = (varops.mk_unique "@query")
in ((uu____28009), (FStar_Pervasives_Native.Some ("query")), (uu____28010))))
in (FStar_SMTEncoding_Util.mkAssume uu____28002))
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




