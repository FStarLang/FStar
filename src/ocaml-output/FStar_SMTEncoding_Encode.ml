
open Prims
open FStar_Pervasives

let add_fuel : 'Auu____7 . 'Auu____7  ->  'Auu____7 Prims.list  ->  'Auu____7 Prims.list = (fun x tl1 -> (

let uu____22 = (FStar_Options.unthrottle_inductives ())
in (match (uu____22) with
| true -> begin
tl1
end
| uu____25 -> begin
(x)::tl1
end)))


let withenv : 'Auu____36 'Auu____37 'Auu____38 . 'Auu____38  ->  ('Auu____37 * 'Auu____36)  ->  ('Auu____37 * 'Auu____36 * 'Auu____38) = (fun c uu____56 -> (match (uu____56) with
| (a, b) -> begin
((a), (b), (c))
end))


let vargs : 'Auu____71 'Auu____72 'Auu____73 . (('Auu____73, 'Auu____72) FStar_Util.either * 'Auu____71) Prims.list  ->  (('Auu____73, 'Auu____72) FStar_Util.either * 'Auu____71) Prims.list = (fun args -> (FStar_List.filter (fun uu___108_119 -> (match (uu___108_119) with
| (FStar_Util.Inl (uu____128), uu____129) -> begin
false
end
| uu____134 -> begin
true
end)) args))


let subst_lcomp_opt : 'Auu____149 . FStar_Syntax_Syntax.subst_elt Prims.list  ->  (FStar_Syntax_Syntax.lcomp, 'Auu____149) FStar_Util.either FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.lcomp, 'Auu____149) FStar_Util.either FStar_Pervasives_Native.option = (fun s l -> (match (l) with
| FStar_Pervasives_Native.Some (FStar_Util.Inl (l1)) -> begin
(

let uu____185 = (

let uu____190 = (

let uu____191 = (

let uu____194 = (l1.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp s uu____194))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____191))
in FStar_Util.Inl (uu____190))
in FStar_Pervasives_Native.Some (uu____185))
end
| uu____201 -> begin
l
end))


let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s 39 (*'*) 95 (*_*)))


let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun lid a -> (

let a1 = (

let uu___132_221 = a
in (

let uu____222 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = uu____222; FStar_Syntax_Syntax.index = uu___132_221.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___132_221.FStar_Syntax_Syntax.sort}))
in (

let uu____223 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str a1.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (FStar_All.pipe_left escape uu____223))))


let primitive_projector_by_pos : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (

let fail = (fun uu____239 -> (

let uu____240 = (FStar_Util.format2 "Projector %s on data constructor %s not found" (Prims.string_of_int i) lid.FStar_Ident.str)
in (failwith uu____240)))
in (

let uu____241 = (FStar_TypeChecker_Env.lookup_datacon env lid)
in (match (uu____241) with
| (uu____246, t) -> begin
(

let uu____248 = (

let uu____249 = (FStar_Syntax_Subst.compress t)
in uu____249.FStar_Syntax_Syntax.n)
in (match (uu____248) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____270 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____270) with
| (binders, uu____276) -> begin
(match (((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders)))) with
| true -> begin
(fail ())
end
| uu____281 -> begin
(

let b = (FStar_List.nth binders i)
in (mk_term_projector_name lid (FStar_Pervasives_Native.fst b)))
end)
end))
end
| uu____291 -> begin
(fail ())
end))
end))))


let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (

let uu____300 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str (Prims.string_of_int i))
in (FStar_All.pipe_left escape uu____300)))


let mk_term_projector : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun lid a -> (

let uu____309 = (

let uu____314 = (mk_term_projector_name lid a)
in ((uu____314), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Util.mkFreeV uu____309)))


let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_SMTEncoding_Term.term = (fun lid i -> (

let uu____323 = (

let uu____328 = (mk_term_projector_name_by_pos lid i)
in ((uu____328), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Util.mkFreeV uu____323)))


let mk_data_tester : 'Auu____337 . 'Auu____337  ->  FStar_Ident.lident  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (fun env l x -> (FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x))

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

let new_scope = (fun uu____718 -> (

let uu____719 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (

let uu____722 = (FStar_Util.smap_create (Prims.parse_int "100"))
in ((uu____719), (uu____722)))))
in (

let scopes = (

let uu____742 = (

let uu____753 = (new_scope ())
in (uu____753)::[])
in (FStar_Util.mk_ref uu____742))
in (

let mk_unique = (fun y -> (

let y1 = (escape y)
in (

let y2 = (

let uu____794 = (

let uu____797 = (FStar_ST.op_Bang scopes)
in (FStar_Util.find_map uu____797 (fun uu____899 -> (match (uu____899) with
| (names1, uu____911) -> begin
(FStar_Util.smap_try_find names1 y1)
end))))
in (match (uu____794) with
| FStar_Pervasives_Native.None -> begin
y1
end
| FStar_Pervasives_Native.Some (uu____920) -> begin
((FStar_Util.incr ctr);
(

let uu____943 = (

let uu____944 = (

let uu____945 = (FStar_ST.op_Bang ctr)
in (Prims.string_of_int uu____945))
in (Prims.strcat "__" uu____944))
in (Prims.strcat y1 uu____943));
)
end))
in (

let top_scope = (

let uu____1009 = (

let uu____1018 = (FStar_ST.op_Bang scopes)
in (FStar_List.hd uu____1018))
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1009))
in ((FStar_Util.smap_add top_scope y2 true);
y2;
)))))
in (

let new_var = (fun pp rn -> (FStar_All.pipe_left mk_unique (Prims.strcat pp.FStar_Ident.idText (Prims.strcat "__" (Prims.string_of_int rn)))))
in (

let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (

let next_id1 = (fun uu____1146 -> ((FStar_Util.incr ctr);
(FStar_ST.op_Bang ctr);
))
in (

let fresh1 = (fun pfx -> (

let uu____1233 = (

let uu____1234 = (next_id1 ())
in (FStar_All.pipe_left Prims.string_of_int uu____1234))
in (FStar_Util.format2 "%s_%s" pfx uu____1233)))
in (

let string_const = (fun s -> (

let uu____1239 = (

let uu____1242 = (FStar_ST.op_Bang scopes)
in (FStar_Util.find_map uu____1242 (fun uu____1344 -> (match (uu____1344) with
| (uu____1355, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))
in (match (uu____1239) with
| FStar_Pervasives_Native.Some (f) -> begin
f
end
| FStar_Pervasives_Native.None -> begin
(

let id = (next_id1 ())
in (

let f = (

let uu____1368 = (FStar_SMTEncoding_Util.mk_String_const id)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1368))
in (

let top_scope = (

let uu____1372 = (

let uu____1381 = (FStar_ST.op_Bang scopes)
in (FStar_List.hd uu____1381))
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1372))
in ((FStar_Util.smap_add top_scope s f);
f;
))))
end)))
in (

let push1 = (fun uu____1498 -> (

let uu____1499 = (

let uu____1510 = (new_scope ())
in (

let uu____1519 = (FStar_ST.op_Bang scopes)
in (uu____1510)::uu____1519))
in (FStar_ST.op_Colon_Equals scopes uu____1499)))
in (

let pop1 = (fun uu____1701 -> (

let uu____1702 = (

let uu____1713 = (FStar_ST.op_Bang scopes)
in (FStar_List.tl uu____1713))
in (FStar_ST.op_Colon_Equals scopes uu____1702)))
in {push = push1; pop = pop1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; string_const = string_const; next_id = next_id1; mk_unique = mk_unique}))))))))))))


let unmangle : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv = (fun x -> (

let uu___133_1896 = x
in (

let uu____1897 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = uu____1897; FStar_Syntax_Syntax.index = uu___133_1896.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___133_1896.FStar_Syntax_Syntax.sort})))

type binding =
| Binding_var of (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term)
| Binding_fvar of (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)


let uu___is_Binding_var : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Binding_var (_0) -> begin
true
end
| uu____1931 -> begin
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
| uu____1969 -> begin
false
end))


let __proj__Binding_fvar__item___0 : binding  ->  (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| Binding_fvar (_0) -> begin
_0
end))


let binder_of_eithervar : 'Auu____2020 'Auu____2021 . 'Auu____2021  ->  ('Auu____2021 * 'Auu____2020 FStar_Pervasives_Native.option) = (fun v1 -> ((v1), (FStar_Pervasives_Native.None)))

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


let mk_cache_entry : 'Auu____2335 . 'Auu____2335  ->  Prims.string  ->  FStar_SMTEncoding_Term.sort Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  cache_entry = (fun env tsym cvar_sorts t_decls -> (

let names1 = (FStar_All.pipe_right t_decls (FStar_List.collect (fun uu___109_2369 -> (match (uu___109_2369) with
| FStar_SMTEncoding_Term.Assume (a) -> begin
(a.FStar_SMTEncoding_Term.assumption_name)::[]
end
| uu____2373 -> begin
[]
end))))
in {cache_symbol_name = tsym; cache_symbol_arg_sorts = cvar_sorts; cache_symbol_decls = t_decls; cache_symbol_assumption_names = names1}))


let use_cache_entry : cache_entry  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun ce -> (FStar_SMTEncoding_Term.RetainAssumptions (ce.cache_symbol_assumption_names))::[])


let print_env : env_t  ->  Prims.string = (fun e -> (

let uu____2384 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun uu___110_2394 -> (match (uu___110_2394) with
| Binding_var (x, uu____2396) -> begin
(FStar_Syntax_Print.bv_to_string x)
end
| Binding_fvar (l, uu____2398, uu____2399, uu____2400) -> begin
(FStar_Syntax_Print.lid_to_string l)
end))))
in (FStar_All.pipe_right uu____2384 (FStar_String.concat ", "))))


let lookup_binding : 'Auu____2417 . env_t  ->  (binding  ->  'Auu____2417 FStar_Pervasives_Native.option)  ->  'Auu____2417 FStar_Pervasives_Native.option = (fun env f -> (FStar_Util.find_map env.bindings f))


let caption_t : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.string FStar_Pervasives_Native.option = (fun env t -> (

let uu____2447 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____2447) with
| true -> begin
(

let uu____2450 = (FStar_Syntax_Print.term_to_string t)
in FStar_Pervasives_Native.Some (uu____2450))
end
| uu____2451 -> begin
FStar_Pervasives_Native.None
end)))


let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (

let xsym = (varops.fresh x)
in (

let uu____2465 = (FStar_SMTEncoding_Util.mkFreeV ((xsym), (s)))
in ((xsym), (uu____2465)))))


let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (Prims.strcat "@x" (Prims.string_of_int env.depth))
in (

let y = (FStar_SMTEncoding_Util.mkFreeV ((ysym), (FStar_SMTEncoding_Term.Term_sort)))
in ((ysym), (y), ((

let uu___134_2483 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = (env.depth + (Prims.parse_int "1")); tcenv = uu___134_2483.tcenv; warn = uu___134_2483.warn; cache = uu___134_2483.cache; nolabels = uu___134_2483.nolabels; use_zfuel_name = uu___134_2483.use_zfuel_name; encode_non_total_function_typ = uu___134_2483.encode_non_total_function_typ; current_module_name = uu___134_2483.current_module_name}))))))


let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let uu___135_2503 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = uu___135_2503.depth; tcenv = uu___135_2503.tcenv; warn = uu___135_2503.warn; cache = uu___135_2503.cache; nolabels = uu___135_2503.nolabels; use_zfuel_name = uu___135_2503.use_zfuel_name; encode_non_total_function_typ = uu___135_2503.encode_non_total_function_typ; current_module_name = uu___135_2503.current_module_name}))))))


let new_term_constant_from_string : env_t  ->  FStar_Syntax_Syntax.bv  ->  Prims.string  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x str -> (

let ysym = (varops.mk_unique str)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let uu___136_2527 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = uu___136_2527.depth; tcenv = uu___136_2527.tcenv; warn = uu___136_2527.warn; cache = uu___136_2527.cache; nolabels = uu___136_2527.nolabels; use_zfuel_name = uu___136_2527.use_zfuel_name; encode_non_total_function_typ = uu___136_2527.encode_non_total_function_typ; current_module_name = uu___136_2527.current_module_name}))))))


let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (

let uu___137_2540 = env
in {bindings = (Binding_var (((x), (t))))::env.bindings; depth = uu___137_2540.depth; tcenv = uu___137_2540.tcenv; warn = uu___137_2540.warn; cache = uu___137_2540.cache; nolabels = uu___137_2540.nolabels; use_zfuel_name = uu___137_2540.use_zfuel_name; encode_non_total_function_typ = uu___137_2540.encode_non_total_function_typ; current_module_name = uu___137_2540.current_module_name}))


let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let aux = (fun a' -> (lookup_binding env (fun uu___111_2566 -> (match (uu___111_2566) with
| Binding_var (b, t) when (FStar_Syntax_Syntax.bv_eq b a') -> begin
FStar_Pervasives_Native.Some (((b), (t)))
end
| uu____2579 -> begin
FStar_Pervasives_Native.None
end))))
in (

let uu____2584 = (aux a)
in (match (uu____2584) with
| FStar_Pervasives_Native.None -> begin
(

let a2 = (unmangle a)
in (

let uu____2596 = (aux a2)
in (match (uu____2596) with
| FStar_Pervasives_Native.None -> begin
(

let uu____2607 = (

let uu____2608 = (FStar_Syntax_Print.bv_to_string a2)
in (

let uu____2609 = (print_env env)
in (FStar_Util.format2 "Bound term variable not found (after unmangling): %s in environment: %s" uu____2608 uu____2609)))
in (failwith uu____2607))
end
| FStar_Pervasives_Native.Some (b, t) -> begin
t
end)))
end
| FStar_Pervasives_Native.Some (b, t) -> begin
t
end))))


let new_term_constant_and_tok_from_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * Prims.string * env_t) = (fun env x -> (

let fname = (varops.new_fvar x)
in (

let ftok = (Prims.strcat fname "@tok")
in (

let uu____2638 = (

let uu___138_2639 = env
in (

let uu____2640 = (

let uu____2643 = (

let uu____2644 = (

let uu____2657 = (

let uu____2660 = (FStar_SMTEncoding_Util.mkApp ((ftok), ([])))
in (FStar_All.pipe_left (fun _0_41 -> FStar_Pervasives_Native.Some (_0_41)) uu____2660))
in ((x), (fname), (uu____2657), (FStar_Pervasives_Native.None)))
in Binding_fvar (uu____2644))
in (uu____2643)::env.bindings)
in {bindings = uu____2640; depth = uu___138_2639.depth; tcenv = uu___138_2639.tcenv; warn = uu___138_2639.warn; cache = uu___138_2639.cache; nolabels = uu___138_2639.nolabels; use_zfuel_name = uu___138_2639.use_zfuel_name; encode_non_total_function_typ = uu___138_2639.encode_non_total_function_typ; current_module_name = uu___138_2639.current_module_name}))
in ((fname), (ftok), (uu____2638))))))


let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option) FStar_Pervasives_Native.option = (fun env a -> (lookup_binding env (fun uu___112_2704 -> (match (uu___112_2704) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
FStar_Pervasives_Native.Some (((t1), (t2), (t3)))
end
| uu____2743 -> begin
FStar_Pervasives_Native.None
end))))


let contains_name : env_t  ->  Prims.string  ->  Prims.bool = (fun env s -> (

let uu____2762 = (lookup_binding env (fun uu___113_2770 -> (match (uu___113_2770) with
| Binding_fvar (b, t1, t2, t3) when (Prims.op_Equality b.FStar_Ident.str s) -> begin
FStar_Pervasives_Native.Some (())
end
| uu____2785 -> begin
FStar_Pervasives_Native.None
end)))
in (FStar_All.pipe_right uu____2762 FStar_Option.isSome)))


let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option) = (fun env a -> (

let uu____2806 = (try_lookup_lid env a)
in (match (uu____2806) with
| FStar_Pervasives_Native.None -> begin
(

let uu____2839 = (

let uu____2840 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" uu____2840))
in (failwith uu____2839))
end
| FStar_Pervasives_Native.Some (s) -> begin
s
end)))


let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  env_t = (fun env x fname ftok -> (

let uu___139_2892 = env
in {bindings = (Binding_fvar (((x), (fname), (ftok), (FStar_Pervasives_Native.None))))::env.bindings; depth = uu___139_2892.depth; tcenv = uu___139_2892.tcenv; warn = uu___139_2892.warn; cache = uu___139_2892.cache; nolabels = uu___139_2892.nolabels; use_zfuel_name = uu___139_2892.use_zfuel_name; encode_non_total_function_typ = uu___139_2892.encode_non_total_function_typ; current_module_name = uu___139_2892.current_module_name}))


let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (

let uu____2909 = (lookup_lid env x)
in (match (uu____2909) with
| (t1, t2, uu____2922) -> begin
(

let t3 = (

let uu____2932 = (

let uu____2939 = (

let uu____2942 = (FStar_SMTEncoding_Util.mkApp (("ZFuel"), ([])))
in (uu____2942)::[])
in ((f), (uu____2939)))
in (FStar_SMTEncoding_Util.mkApp uu____2932))
in (

let uu___140_2947 = env
in {bindings = (Binding_fvar (((x), (t1), (t2), (FStar_Pervasives_Native.Some (t3)))))::env.bindings; depth = uu___140_2947.depth; tcenv = uu___140_2947.tcenv; warn = uu___140_2947.warn; cache = uu___140_2947.cache; nolabels = uu___140_2947.nolabels; use_zfuel_name = uu___140_2947.use_zfuel_name; encode_non_total_function_typ = uu___140_2947.encode_non_total_function_typ; current_module_name = uu___140_2947.current_module_name}))
end)))


let try_lookup_free_var : env_t  ->  FStar_Ident.lident  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun env l -> (

let uu____2962 = (try_lookup_lid env l)
in (match (uu____2962) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (name, sym, zf_opt) -> begin
(match (zf_opt) with
| FStar_Pervasives_Native.Some (f) when env.use_zfuel_name -> begin
FStar_Pervasives_Native.Some (f)
end
| uu____3011 -> begin
(match (sym) with
| FStar_Pervasives_Native.Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (uu____3019, (fuel)::[]) -> begin
(

let uu____3023 = (

let uu____3024 = (

let uu____3025 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right uu____3025 FStar_Pervasives_Native.fst))
in (FStar_Util.starts_with uu____3024 "fuel"))
in (match (uu____3023) with
| true -> begin
(

let uu____3028 = (

let uu____3029 = (FStar_SMTEncoding_Util.mkFreeV ((name), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_ApplyTF uu____3029 fuel))
in (FStar_All.pipe_left (fun _0_42 -> FStar_Pervasives_Native.Some (_0_42)) uu____3028))
end
| uu____3032 -> begin
FStar_Pervasives_Native.Some (t)
end))
end
| uu____3033 -> begin
FStar_Pervasives_Native.Some (t)
end)
end
| uu____3034 -> begin
FStar_Pervasives_Native.None
end)
end)
end)))


let lookup_free_var : env_t  ->  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let uu____3049 = (try_lookup_free_var env a.FStar_Syntax_Syntax.v)
in (match (uu____3049) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let uu____3053 = (

let uu____3054 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" uu____3054))
in (failwith uu____3053))
end)))


let lookup_free_var_name : env_t  ->  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t  ->  Prims.string = (fun env a -> (

let uu____3067 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (uu____3067) with
| (x, uu____3079, uu____3080) -> begin
x
end)))


let lookup_free_var_sym : env_t  ->  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t  ->  (FStar_SMTEncoding_Term.op * FStar_SMTEncoding_Term.term Prims.list) = (fun env a -> (

let uu____3107 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (uu____3107) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| FStar_Pervasives_Native.Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.freevars = uu____3143; FStar_SMTEncoding_Term.rng = uu____3144}) when env.use_zfuel_name -> begin
((g), (zf))
end
| uu____3159 -> begin
(match (sym) with
| FStar_Pervasives_Native.None -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end
| FStar_Pervasives_Native.Some (sym1) -> begin
(match (sym1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, (fuel)::[]) -> begin
((g), ((fuel)::[]))
end
| uu____3183 -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end)
end)
end)
end)))


let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun uu___114_3201 -> (match (uu___114_3201) with
| Binding_fvar (uu____3204, nm', tok, uu____3207) when (Prims.op_Equality nm nm') -> begin
tok
end
| uu____3216 -> begin
FStar_Pervasives_Native.None
end))))


let mkForall_fuel' : 'Auu____3223 . 'Auu____3223  ->  (FStar_SMTEncoding_Term.pat Prims.list Prims.list * FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (fun n1 uu____3241 -> (match (uu____3241) with
| (pats, vars, body) -> begin
(

let fallback = (fun uu____3266 -> (FStar_SMTEncoding_Util.mkForall ((pats), (vars), (body))))
in (

let uu____3271 = (FStar_Options.unthrottle_inductives ())
in (match (uu____3271) with
| true -> begin
(fallback ())
end
| uu____3272 -> begin
(

let uu____3273 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____3273) with
| (fsym, fterm) -> begin
(

let add_fuel1 = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Util.mkApp (("HasTypeFuel"), ((fterm)::args)))
end
| uu____3304 -> begin
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

let uu____3325 = (add_fuel1 guards)
in (FStar_SMTEncoding_Util.mk_and_l uu____3325))
end
| uu____3328 -> begin
(

let uu____3329 = (add_fuel1 ((guard)::[]))
in (FStar_All.pipe_right uu____3329 FStar_List.hd))
end)
in (FStar_SMTEncoding_Util.mkImp ((guard1), (body'))))
end
| uu____3334 -> begin
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
| FStar_Syntax_Syntax.Tm_arrow (uu____3378) -> begin
true
end
| FStar_Syntax_Syntax.Tm_refine (uu____3391) -> begin
true
end
| FStar_Syntax_Syntax.Tm_bvar (uu____3398) -> begin
true
end
| FStar_Syntax_Syntax.Tm_uvar (uu____3399) -> begin
true
end
| FStar_Syntax_Syntax.Tm_abs (uu____3416) -> begin
true
end
| FStar_Syntax_Syntax.Tm_constant (uu____3433) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____3435 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____3435 FStar_Option.isNone))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____3453; FStar_Syntax_Syntax.vars = uu____3454}, uu____3455) -> begin
(

let uu____3476 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____3476 FStar_Option.isNone))
end
| uu____3493 -> begin
false
end)))


let head_redex : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let uu____3502 = (

let uu____3503 = (FStar_Syntax_Util.un_uinst t)
in uu____3503.FStar_Syntax_Syntax.n)
in (match (uu____3502) with
| FStar_Syntax_Syntax.Tm_abs (uu____3506, uu____3507, FStar_Pervasives_Native.Some (rc)) -> begin
(((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_Tot_lid) || (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_GTot_lid)) || (FStar_List.existsb (fun uu___115_3528 -> (match (uu___115_3528) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____3529 -> begin
false
end)) rc.FStar_Syntax_Syntax.residual_flags))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____3531 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____3531 FStar_Option.isSome))
end
| uu____3548 -> begin
false
end)))


let whnf : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____3557 = (head_normal env t)
in (match (uu____3557) with
| true -> begin
t
end
| uu____3558 -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
end)))


let norm : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t))


let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____3571 = (

let uu____3572 = (FStar_Syntax_Syntax.null_binder t)
in (uu____3572)::[])
in (

let uu____3573 = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Util.abs uu____3571 uu____3573 FStar_Pervasives_Native.None))))


let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((FStar_Pervasives_Native.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(

let uu____3613 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out uu____3613))
end
| s -> begin
(

let uu____3618 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Util.mk_ApplyTT out uu____3618))
end)) e)))


let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)))


let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun uu___116_3636 -> (match (uu___116_3636) with
| FStar_SMTEncoding_Term.Var ("ApplyTT") -> begin
true
end
| FStar_SMTEncoding_Term.Var ("ApplyTF") -> begin
true
end
| uu____3637 -> begin
false
end))


let is_an_eta_expansion : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun env vars body -> (

let rec check_partial_applications = (fun t xs -> (match (((t.FStar_SMTEncoding_Term.tm), (xs))) with
| (FStar_SMTEncoding_Term.App (app, (f)::({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.freevars = uu____3676; FStar_SMTEncoding_Term.rng = uu____3677})::[]), (x)::xs1) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(check_partial_applications f xs1)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), uu____3700) -> begin
(

let uu____3709 = ((Prims.op_Equality (FStar_List.length args) (FStar_List.length xs)) && (FStar_List.forall2 (fun a v1 -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v1)
end
| uu____3720 -> begin
false
end)) args (FStar_List.rev xs)))
in (match (uu____3709) with
| true -> begin
(tok_of_name env f)
end
| uu____3723 -> begin
FStar_Pervasives_Native.None
end))
end
| (uu____3724, []) -> begin
(

let fvs = (FStar_SMTEncoding_Term.free_variables t)
in (

let uu____3728 = (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (

let uu____3732 = (FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)
in (not (uu____3732))))))
in (match (uu____3728) with
| true -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____3735 -> begin
FStar_Pervasives_Native.None
end)))
end
| uu____3736 -> begin
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
| uu____3966 -> begin
false
end))

exception Inner_let_rec


let uu___is_Inner_let_rec : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Inner_let_rec -> begin
true
end
| uu____3971 -> begin
false
end))


let encode_const : FStar_Const.sconst  ->  FStar_SMTEncoding_Term.term = (fun uu___117_3975 -> (match (uu___117_3975) with
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
(

let uu____3977 = (

let uu____3984 = (

let uu____3987 = (

let uu____3988 = (FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c))
in (FStar_SMTEncoding_Term.boxInt uu____3988))
in (uu____3987)::[])
in (("FStar.Char.Char"), (uu____3984)))
in (FStar_SMTEncoding_Util.mkApp uu____3977))
end
| FStar_Const.Const_int (i, FStar_Pervasives_Native.None) -> begin
(

let uu____4002 = (FStar_SMTEncoding_Util.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt uu____4002))
end
| FStar_Const.Const_int (i, FStar_Pervasives_Native.Some (uu____4004)) -> begin
(failwith "Machine integers should be desugared")
end
| FStar_Const.Const_string (s, uu____4020) -> begin
(varops.string_const s)
end
| FStar_Const.Const_range (r) -> begin
FStar_SMTEncoding_Term.mk_Range_const
end
| FStar_Const.Const_effect -> begin
FStar_SMTEncoding_Term.mk_Term_type
end
| c -> begin
(

let uu____4023 = (

let uu____4024 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" uu____4024))
in (failwith uu____4023))
end))


let as_function_typ : env_t  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (

let rec aux = (fun norm1 t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____4045) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_refine (uu____4058) -> begin
(

let uu____4065 = (FStar_Syntax_Util.unrefine t1)
in (aux true uu____4065))
end
| uu____4066 -> begin
(match (norm1) with
| true -> begin
(

let uu____4067 = (whnf env t1)
in (aux false uu____4067))
end
| uu____4068 -> begin
(

let uu____4069 = (

let uu____4070 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (

let uu____4071 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" uu____4070 uu____4071)))
in (failwith uu____4069))
end)
end)))
in (aux true t0)))


let curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun k -> (

let k1 = (FStar_Syntax_Subst.compress k)
in (match (k1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| uu____4103 -> begin
(

let uu____4104 = (FStar_Syntax_Syntax.mk_Total k1)
in (([]), (uu____4104)))
end)))


let is_arithmetic_primitive : 'Auu____4121 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  'Auu____4121 Prims.list  ->  Prims.bool = (fun head1 args -> (match (((head1.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____4141)::(uu____4142)::[]) -> begin
(((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Addition) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Subtraction)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Multiply)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Division)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Modulus))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____4146)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus)
end
| uu____4149 -> begin
false
end))


let isInteger : FStar_Syntax_Syntax.term'  ->  Prims.bool = (fun tm -> (match (tm) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (n1, FStar_Pervasives_Native.None)) -> begin
true
end
| uu____4171 -> begin
false
end))


let getInteger : FStar_Syntax_Syntax.term'  ->  Prims.int = (fun tm -> (match (tm) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (n1, FStar_Pervasives_Native.None)) -> begin
(FStar_Util.int_of_string n1)
end
| uu____4187 -> begin
(failwith "Expected an Integer term")
end))


let is_BitVector_primitive : 'Auu____4194 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____4194) Prims.list  ->  Prims.bool = (fun head1 args -> (match (((head1.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((sz_arg, uu____4233))::(uu____4234)::(uu____4235)::[]) -> begin
((((((((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_and_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_xor_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_or_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_shift_left_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_shift_right_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_udiv_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_mod_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_uext_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_mul_lid)) && (isInteger sz_arg.FStar_Syntax_Syntax.n))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((sz_arg, uu____4286))::(uu____4287)::[]) -> begin
(((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_to_nat_lid)) && (isInteger sz_arg.FStar_Syntax_Syntax.n))
end
| uu____4324 -> begin
false
end))


let rec encode_binders : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> ((

let uu____4533 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____4533) with
| true -> begin
(

let uu____4534 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" uu____4534))
end
| uu____4535 -> begin
()
end));
(

let uu____4536 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____4620 b -> (match (uu____4620) with
| (vars, guards, env1, decls, names1) -> begin
(

let uu____4699 = (

let x = (unmangle (FStar_Pervasives_Native.fst b))
in (

let uu____4715 = (gen_term_var env1 x)
in (match (uu____4715) with
| (xxsym, xx, env') -> begin
(

let uu____4739 = (

let uu____4744 = (norm env1 x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt uu____4744 env1 xx))
in (match (uu____4739) with
| (guard_x_t, decls') -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (guard_x_t), (env'), (decls'), (x))
end))
end)))
in (match (uu____4699) with
| (v1, g, env2, decls', n1) -> begin
(((v1)::vars), ((g)::guards), (env2), ((FStar_List.append decls decls')), ((n1)::names1))
end))
end)) (([]), ([]), (env), ([]), ([]))))
in (match (uu____4536) with
| (vars, guards, env1, decls, names1) -> begin
(((FStar_List.rev vars)), ((FStar_List.rev guards)), (env1), (decls), ((FStar_List.rev names1)))
end));
))
and encode_term_pred : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let uu____4903 = (encode_term t env)
in (match (uu____4903) with
| (t1, decls) -> begin
(

let uu____4914 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1)
in ((uu____4914), (decls)))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let uu____4925 = (encode_term t env)
in (match (uu____4925) with
| (t1, decls) -> begin
(match (fuel_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____4940 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t1)
in ((uu____4940), (decls)))
end
| FStar_Pervasives_Native.Some (f) -> begin
(

let uu____4942 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1)
in ((uu____4942), (decls)))
end)
end)))
and encode_arith_term : env_t  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.args  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun env head1 args_e -> (

let uu____4948 = (encode_args args_e env)
in (match (uu____4948) with
| (arg_tms, decls) -> begin
(

let head_fv = (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____4967 -> begin
(failwith "Impossible")
end)
in (

let unary = (fun arg_tms1 -> (

let uu____4976 = (FStar_List.hd arg_tms1)
in (FStar_SMTEncoding_Term.unboxInt uu____4976)))
in (

let binary = (fun arg_tms1 -> (

let uu____4989 = (

let uu____4990 = (FStar_List.hd arg_tms1)
in (FStar_SMTEncoding_Term.unboxInt uu____4990))
in (

let uu____4991 = (

let uu____4992 = (

let uu____4993 = (FStar_List.tl arg_tms1)
in (FStar_List.hd uu____4993))
in (FStar_SMTEncoding_Term.unboxInt uu____4992))
in ((uu____4989), (uu____4991)))))
in (

let mk_default = (fun uu____4999 -> (

let uu____5000 = (lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name)
in (match (uu____5000) with
| (fname, fuel_args) -> begin
(FStar_SMTEncoding_Util.mkApp' ((fname), ((FStar_List.append fuel_args arg_tms))))
end)))
in (

let mk_l = (fun op mk_args ts -> (

let uu____5051 = (FStar_Options.smtencoding_l_arith_native ())
in (match (uu____5051) with
| true -> begin
(

let uu____5052 = (

let uu____5053 = (mk_args ts)
in (op uu____5053))
in (FStar_All.pipe_right uu____5052 FStar_SMTEncoding_Term.boxInt))
end
| uu____5054 -> begin
(mk_default ())
end)))
in (

let mk_nl = (fun nm op ts -> (

let uu____5082 = (FStar_Options.smtencoding_nl_arith_wrapped ())
in (match (uu____5082) with
| true -> begin
(

let uu____5083 = (binary ts)
in (match (uu____5083) with
| (t1, t2) -> begin
(

let uu____5090 = (FStar_SMTEncoding_Util.mkApp ((nm), ((t1)::(t2)::[])))
in (FStar_All.pipe_right uu____5090 FStar_SMTEncoding_Term.boxInt))
end))
end
| uu____5093 -> begin
(

let uu____5094 = (FStar_Options.smtencoding_nl_arith_native ())
in (match (uu____5094) with
| true -> begin
(

let uu____5095 = (op (binary ts))
in (FStar_All.pipe_right uu____5095 FStar_SMTEncoding_Term.boxInt))
end
| uu____5096 -> begin
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

let uu____5226 = (

let uu____5235 = (FStar_List.tryFind (fun uu____5257 -> (match (uu____5257) with
| (l, uu____5267) -> begin
(FStar_Syntax_Syntax.fv_eq_lid head_fv l)
end)) ops)
in (FStar_All.pipe_right uu____5235 FStar_Util.must))
in (match (uu____5226) with
| (uu____5306, op) -> begin
(

let uu____5316 = (op arg_tms)
in ((uu____5316), (decls)))
end)))))))))))))))
end)))
and encode_BitVector_term : env_t  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.arg Prims.list  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list) = (fun env head1 args_e -> (

let uu____5324 = (FStar_List.hd args_e)
in (match (uu____5324) with
| (tm_sz, uu____5332) -> begin
(

let sz = (getInteger tm_sz.FStar_Syntax_Syntax.n)
in (

let sz_key = (FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz))
in (

let sz_decls = (

let uu____5342 = (FStar_Util.smap_try_find env.cache sz_key)
in (match (uu____5342) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
[]
end
| FStar_Pervasives_Native.None -> begin
(

let t_decls = (FStar_SMTEncoding_Term.mkBvConstructor sz)
in ((

let uu____5350 = (mk_cache_entry env "" [] [])
in (FStar_Util.smap_add env.cache sz_key uu____5350));
t_decls;
))
end))
in (

let uu____5351 = (match (((head1.FStar_Syntax_Syntax.n), (args_e))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____5371)::((sz_arg, uu____5373))::(uu____5374)::[]) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_uext_lid) && (isInteger sz_arg.FStar_Syntax_Syntax.n)) -> begin
(

let uu____5423 = (

let uu____5426 = (FStar_List.tail args_e)
in (FStar_List.tail uu____5426))
in (

let uu____5429 = (

let uu____5432 = (getInteger sz_arg.FStar_Syntax_Syntax.n)
in FStar_Pervasives_Native.Some (uu____5432))
in ((uu____5423), (uu____5429))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____5438)::((sz_arg, uu____5440))::(uu____5441)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_uext_lid) -> begin
(

let uu____5490 = (

let uu____5491 = (FStar_Syntax_Print.term_to_string sz_arg)
in (FStar_Util.format1 "Not a constant bitvector extend size: %s" uu____5491))
in (failwith uu____5490))
end
| uu____5500 -> begin
(

let uu____5507 = (FStar_List.tail args_e)
in ((uu____5507), (FStar_Pervasives_Native.None)))
end)
in (match (uu____5351) with
| (arg_tms, ext_sz) -> begin
(

let uu____5530 = (encode_args arg_tms env)
in (match (uu____5530) with
| (arg_tms1, decls) -> begin
(

let head_fv = (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____5551 -> begin
(failwith "Impossible")
end)
in (

let unary = (fun arg_tms2 -> (

let uu____5560 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____5560)))
in (

let unary_arith = (fun arg_tms2 -> (

let uu____5569 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxInt uu____5569)))
in (

let binary = (fun arg_tms2 -> (

let uu____5582 = (

let uu____5583 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____5583))
in (

let uu____5584 = (

let uu____5585 = (

let uu____5586 = (FStar_List.tl arg_tms2)
in (FStar_List.hd uu____5586))
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____5585))
in ((uu____5582), (uu____5584)))))
in (

let binary_arith = (fun arg_tms2 -> (

let uu____5601 = (

let uu____5602 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____5602))
in (

let uu____5603 = (

let uu____5604 = (

let uu____5605 = (FStar_List.tl arg_tms2)
in (FStar_List.hd uu____5605))
in (FStar_SMTEncoding_Term.unboxInt uu____5604))
in ((uu____5601), (uu____5603)))))
in (

let mk_bv = (fun op mk_args resBox ts -> (

let uu____5654 = (

let uu____5655 = (mk_args ts)
in (op uu____5655))
in (FStar_All.pipe_right uu____5654 resBox)))
in (

let bv_and = (mk_bv FStar_SMTEncoding_Util.mkBvAnd binary (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_xor = (mk_bv FStar_SMTEncoding_Util.mkBvXor binary (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_or = (mk_bv FStar_SMTEncoding_Util.mkBvOr binary (FStar_SMTEncoding_Term.boxBitVec sz))
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

let uu____5745 = (

let uu____5748 = (match (ext_sz) with
| FStar_Pervasives_Native.Some (x) -> begin
x
end
| FStar_Pervasives_Native.None -> begin
(failwith "impossible")
end)
in (FStar_SMTEncoding_Util.mkBvUext uu____5748))
in (

let uu____5750 = (

let uu____5753 = (

let uu____5754 = (match (ext_sz) with
| FStar_Pervasives_Native.Some (x) -> begin
x
end
| FStar_Pervasives_Native.None -> begin
(failwith "impossible")
end)
in (sz + uu____5754))
in (FStar_SMTEncoding_Term.boxBitVec uu____5753))
in (mk_bv uu____5745 unary uu____5750 arg_tms2))))
in (

let to_int = (mk_bv FStar_SMTEncoding_Util.mkBvToNat unary FStar_SMTEncoding_Term.boxInt)
in (

let bv_to = (mk_bv (FStar_SMTEncoding_Util.mkNatToBv sz) unary_arith (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let ops = (((FStar_Parser_Const.bv_and_lid), (bv_and)))::(((FStar_Parser_Const.bv_xor_lid), (bv_xor)))::(((FStar_Parser_Const.bv_or_lid), (bv_or)))::(((FStar_Parser_Const.bv_shift_left_lid), (bv_shl)))::(((FStar_Parser_Const.bv_shift_right_lid), (bv_shr)))::(((FStar_Parser_Const.bv_udiv_lid), (bv_udiv)))::(((FStar_Parser_Const.bv_mod_lid), (bv_mod)))::(((FStar_Parser_Const.bv_mul_lid), (bv_mul)))::(((FStar_Parser_Const.bv_ult_lid), (bv_ult)))::(((FStar_Parser_Const.bv_uext_lid), (bv_uext)))::(((FStar_Parser_Const.bv_to_nat_lid), (to_int)))::(((FStar_Parser_Const.nat_to_bv_lid), (bv_to)))::[]
in (

let uu____5929 = (

let uu____5938 = (FStar_List.tryFind (fun uu____5960 -> (match (uu____5960) with
| (l, uu____5970) -> begin
(FStar_Syntax_Syntax.fv_eq_lid head_fv l)
end)) ops)
in (FStar_All.pipe_right uu____5938 FStar_Util.must))
in (match (uu____5929) with
| (uu____6011, op) -> begin
(

let uu____6021 = (op arg_tms1)
in ((uu____6021), ((FStar_List.append sz_decls decls))))
end)))))))))))))))))))))
end))
end)))))
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let t0 = (FStar_Syntax_Subst.compress t)
in ((

let uu____6032 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____6032) with
| true -> begin
(

let uu____6033 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____6034 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____6035 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" uu____6033 uu____6034 uu____6035))))
end
| uu____6036 -> begin
()
end));
(match (t0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____6041) -> begin
(

let uu____6066 = (

let uu____6067 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____6068 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____6069 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____6070 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6067 uu____6068 uu____6069 uu____6070)))))
in (failwith uu____6066))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____6075 = (

let uu____6076 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____6077 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____6078 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____6079 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6076 uu____6077 uu____6078 uu____6079)))))
in (failwith uu____6075))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____6085 = (

let uu____6086 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" uu____6086))
in (failwith uu____6085))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, k, uu____6093) -> begin
(encode_term t1 env)
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____6135) -> begin
(encode_term t1 env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t1 = (lookup_term_var env x)
in ((t1), ([])))
end
| FStar_Syntax_Syntax.Tm_fvar (v1) -> begin
(

let uu____6145 = (lookup_free_var env v1.FStar_Syntax_Syntax.fv_name)
in ((uu____6145), ([])))
end
| FStar_Syntax_Syntax.Tm_type (uu____6148) -> begin
((FStar_SMTEncoding_Term.mk_Term_type), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____6152) -> begin
(encode_term t1 env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____6158 = (encode_const c)
in ((uu____6158), ([])))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let module_name = env.current_module_name
in (

let uu____6180 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____6180) with
| (binders1, res) -> begin
(

let uu____6191 = ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res))
in (match (uu____6191) with
| true -> begin
(

let uu____6196 = (encode_binders FStar_Pervasives_Native.None binders1 env)
in (match (uu____6196) with
| (vars, guards, env', decls, uu____6221) -> begin
(

let fsym = (

let uu____6239 = (varops.fresh "f")
in ((uu____6239), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV fsym)
in (

let app = (mk_Apply f vars)
in (

let uu____6242 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post (

let uu___141_6251 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___141_6251.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___141_6251.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___141_6251.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___141_6251.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___141_6251.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___141_6251.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___141_6251.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___141_6251.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___141_6251.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___141_6251.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___141_6251.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___141_6251.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___141_6251.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___141_6251.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___141_6251.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___141_6251.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___141_6251.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___141_6251.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___141_6251.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___141_6251.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___141_6251.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___141_6251.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___141_6251.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___141_6251.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___141_6251.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___141_6251.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___141_6251.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___141_6251.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___141_6251.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___141_6251.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___141_6251.FStar_TypeChecker_Env.tc_hooks}) res)
in (match (uu____6242) with
| (pre_opt, res_t) -> begin
(

let uu____6262 = (encode_term_pred FStar_Pervasives_Native.None res_t env' app)
in (match (uu____6262) with
| (res_pred, decls') -> begin
(

let uu____6273 = (match (pre_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____6286 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____6286), ([])))
end
| FStar_Pervasives_Native.Some (pre) -> begin
(

let uu____6290 = (encode_formula pre env')
in (match (uu____6290) with
| (guard, decls0) -> begin
(

let uu____6303 = (FStar_SMTEncoding_Util.mk_and_l ((guard)::guards))
in ((uu____6303), (decls0)))
end))
end)
in (match (uu____6273) with
| (guards1, guard_decls) -> begin
(

let t_interp = (

let uu____6315 = (

let uu____6326 = (FStar_SMTEncoding_Util.mkImp ((guards1), (res_pred)))
in ((((app)::[])::[]), (vars), (uu____6326)))
in (FStar_SMTEncoding_Util.mkForall uu____6315))
in (

let cvars = (

let uu____6344 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right uu____6344 (FStar_List.filter (fun uu____6358 -> (match (uu____6358) with
| (x, uu____6364) -> begin
(Prims.op_disEquality x (FStar_Pervasives_Native.fst fsym))
end)))))
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), ((fsym)::cvars), (t_interp)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____6383 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____6383) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
(

let uu____6391 = (

let uu____6392 = (

let uu____6399 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((cache_entry.cache_symbol_name), (uu____6399)))
in (FStar_SMTEncoding_Util.mkApp uu____6392))
in ((uu____6391), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append guard_decls (use_cache_entry cache_entry)))))))
end
| FStar_Pervasives_Native.None -> begin
(

let tsym = (

let uu____6419 = (

let uu____6420 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_arrow_" uu____6420))
in (varops.mk_unique uu____6419))
in (

let cvar_sorts = (FStar_List.map FStar_Pervasives_Native.snd cvars)
in (

let caption = (

let uu____6431 = (FStar_Options.log_queries ())
in (match (uu____6431) with
| true -> begin
(

let uu____6434 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in FStar_Pervasives_Native.Some (uu____6434))
end
| uu____6435 -> begin
FStar_Pervasives_Native.None
end))
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (caption)))
in (

let t1 = (

let uu____6442 = (

let uu____6449 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((tsym), (uu____6449)))
in (FStar_SMTEncoding_Util.mkApp uu____6442))
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t1 FStar_SMTEncoding_Term.mk_Term_type)
in (

let k_assumption = (

let a_name = (Prims.strcat "kinding_" tsym)
in (

let uu____6461 = (

let uu____6468 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((uu____6468), (FStar_Pervasives_Native.Some (a_name)), (a_name)))
in (FStar_SMTEncoding_Util.mkAssume uu____6461)))
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t1)
in (

let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t1)
in (

let pre_typing = (

let a_name = (Prims.strcat "pre_typing_" tsym)
in (

let uu____6489 = (

let uu____6496 = (

let uu____6497 = (

let uu____6508 = (

let uu____6509 = (

let uu____6514 = (

let uu____6515 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____6515))
in ((f_has_t), (uu____6514)))
in (FStar_SMTEncoding_Util.mkImp uu____6509))
in ((((f_has_t)::[])::[]), ((fsym)::cvars), (uu____6508)))
in (mkForall_fuel uu____6497))
in ((uu____6496), (FStar_Pervasives_Native.Some ("pre-typing for functions")), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____6489)))
in (

let t_interp1 = (

let a_name = (Prims.strcat "interpretation_" tsym)
in (

let uu____6538 = (

let uu____6545 = (

let uu____6546 = (

let uu____6557 = (FStar_SMTEncoding_Util.mkIff ((f_has_t_z), (t_interp)))
in ((((f_has_t_z)::[])::[]), ((fsym)::cvars), (uu____6557)))
in (FStar_SMTEncoding_Util.mkForall uu____6546))
in ((uu____6545), (FStar_Pervasives_Native.Some (a_name)), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____6538)))
in (

let t_decls = (FStar_List.append ((tdecl)::decls) (FStar_List.append decls' (FStar_List.append guard_decls ((k_assumption)::(pre_typing)::(t_interp1)::[]))))
in ((

let uu____6582 = (mk_cache_entry env tsym cvar_sorts t_decls)
in (FStar_Util.smap_add env.cache tkey_hash uu____6582));
((t1), (t_decls));
)))))))))))))
end))))))
end))
end))
end)))))
end))
end
| uu____6585 -> begin
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

let uu____6597 = (

let uu____6604 = (FStar_SMTEncoding_Term.mk_HasType t1 FStar_SMTEncoding_Term.mk_Term_type)
in ((uu____6604), (FStar_Pervasives_Native.Some ("Typing for non-total arrows")), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____6597)))
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

let uu____6616 = (

let uu____6623 = (

let uu____6624 = (

let uu____6635 = (

let uu____6636 = (

let uu____6641 = (

let uu____6642 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____6642))
in ((f_has_t), (uu____6641)))
in (FStar_SMTEncoding_Util.mkImp uu____6636))
in ((((f_has_t)::[])::[]), ((fsym)::[]), (uu____6635)))
in (mkForall_fuel uu____6624))
in ((uu____6623), (FStar_Pervasives_Native.Some (a_name)), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____6616)))
in ((t1), ((tdecl)::(t_kinding)::(t_interp)::[]))))))))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (uu____6669) -> begin
(

let uu____6676 = (

let uu____6681 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)
in (match (uu____6681) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.pos = uu____6688; FStar_Syntax_Syntax.vars = uu____6689} -> begin
(

let uu____6696 = (FStar_Syntax_Subst.open_term ((((x), (FStar_Pervasives_Native.None)))::[]) f)
in (match (uu____6696) with
| (b, f1) -> begin
(

let uu____6721 = (

let uu____6722 = (FStar_List.hd b)
in (FStar_Pervasives_Native.fst uu____6722))
in ((uu____6721), (f1)))
end))
end
| uu____6731 -> begin
(failwith "impossible")
end))
in (match (uu____6676) with
| (x, f) -> begin
(

let uu____6742 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (uu____6742) with
| (base_t, decls) -> begin
(

let uu____6753 = (gen_term_var env x)
in (match (uu____6753) with
| (x1, xtm, env') -> begin
(

let uu____6767 = (encode_formula f env')
in (match (uu____6767) with
| (refinement, decls') -> begin
(

let uu____6778 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____6778) with
| (fsym, fterm) -> begin
(

let tm_has_type_with_fuel = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (FStar_Pervasives_Native.Some (fterm)) xtm base_t)
in (

let encoding = (FStar_SMTEncoding_Util.mkAnd ((tm_has_type_with_fuel), (refinement)))
in (

let cvars = (

let uu____6794 = (

let uu____6797 = (FStar_SMTEncoding_Term.free_variables refinement)
in (

let uu____6804 = (FStar_SMTEncoding_Term.free_variables tm_has_type_with_fuel)
in (FStar_List.append uu____6797 uu____6804)))
in (FStar_Util.remove_dups FStar_SMTEncoding_Term.fv_eq uu____6794))
in (

let cvars1 = (FStar_All.pipe_right cvars (FStar_List.filter (fun uu____6837 -> (match (uu____6837) with
| (y, uu____6843) -> begin
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

let uu____6876 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____6876) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
(

let uu____6884 = (

let uu____6885 = (

let uu____6892 = (FStar_All.pipe_right cvars1 (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((cache_entry.cache_symbol_name), (uu____6892)))
in (FStar_SMTEncoding_Util.mkApp uu____6885))
in ((uu____6884), ((FStar_List.append decls (FStar_List.append decls' (use_cache_entry cache_entry))))))
end
| FStar_Pervasives_Native.None -> begin
(

let module_name = env.current_module_name
in (

let tsym = (

let uu____6913 = (

let uu____6914 = (

let uu____6915 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "_Tm_refine_" uu____6915))
in (Prims.strcat module_name uu____6914))
in (varops.mk_unique uu____6913))
in (

let cvar_sorts = (FStar_List.map FStar_Pervasives_Native.snd cvars1)
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let t1 = (

let uu____6929 = (

let uu____6936 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars1)
in ((tsym), (uu____6936)))
in (FStar_SMTEncoding_Util.mkApp uu____6929))
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

let uu____6951 = (

let uu____6958 = (

let uu____6959 = (

let uu____6970 = (FStar_SMTEncoding_Util.mkIff ((t_haseq_ref), (t_haseq_base)))
in ((((t_haseq_ref)::[])::[]), (cvars1), (uu____6970)))
in (FStar_SMTEncoding_Util.mkForall uu____6959))
in ((uu____6958), (FStar_Pervasives_Native.Some ((Prims.strcat "haseq for " tsym))), ((Prims.strcat "haseq" tsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____6951))
in (

let t_valid = (

let xx = ((x1), (FStar_SMTEncoding_Term.Term_sort))
in (

let valid_t = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((t1)::[])))
in (

let uu____6996 = (

let uu____7003 = (

let uu____7004 = (

let uu____7015 = (

let uu____7016 = (

let uu____7021 = (

let uu____7022 = (

let uu____7033 = (FStar_SMTEncoding_Util.mkAnd ((x_has_base_t), (refinement)))
in (([]), ((xx)::[]), (uu____7033)))
in (FStar_SMTEncoding_Util.mkExists uu____7022))
in ((uu____7021), (valid_t)))
in (FStar_SMTEncoding_Util.mkIff uu____7016))
in ((((valid_t)::[])::[]), (cvars1), (uu____7015)))
in (FStar_SMTEncoding_Util.mkForall uu____7004))
in ((uu____7003), (FStar_Pervasives_Native.Some ("validity axiom for refinement")), ((Prims.strcat "ref_valid_" tsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____6996))))
in (

let t_kinding = (

let uu____7071 = (

let uu____7078 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars1), (t_has_kind)))
in ((uu____7078), (FStar_Pervasives_Native.Some ("refinement kinding")), ((Prims.strcat "refinement_kinding_" tsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____7071))
in (

let t_interp = (

let uu____7096 = (

let uu____7103 = (

let uu____7104 = (

let uu____7115 = (FStar_SMTEncoding_Util.mkIff ((x_has_t), (encoding)))
in ((((x_has_t)::[])::[]), ((ffv)::(xfv)::cvars1), (uu____7115)))
in (FStar_SMTEncoding_Util.mkForall uu____7104))
in (

let uu____7138 = (

let uu____7141 = (FStar_Syntax_Print.term_to_string t0)
in FStar_Pervasives_Native.Some (uu____7141))
in ((uu____7103), (uu____7138), ((Prims.strcat "refinement_interpretation_" tsym)))))
in (FStar_SMTEncoding_Util.mkAssume uu____7096))
in (

let t_decls = (FStar_List.append decls (FStar_List.append decls' ((tdecl)::(t_kinding)::(t_valid)::(t_interp)::(t_haseq1)::[])))
in ((

let uu____7148 = (mk_cache_entry env tsym cvar_sorts t_decls)
in (FStar_Util.smap_add env.cache tkey_hash uu____7148));
((t1), (t_decls));
))))))))))))))))
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

let uu____7178 = (FStar_Syntax_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Util.mk_Term_uvar uu____7178))
in (

let uu____7179 = (encode_term_pred FStar_Pervasives_Native.None k env ttm)
in (match (uu____7179) with
| (t_has_k, decls) -> begin
(

let d = (

let uu____7191 = (

let uu____7198 = (

let uu____7199 = (

let uu____7200 = (

let uu____7201 = (FStar_Syntax_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____7201))
in (FStar_Util.format1 "uvar_typing_%s" uu____7200))
in (varops.mk_unique uu____7199))
in ((t_has_k), (FStar_Pervasives_Native.Some ("Uvar typing")), (uu____7198)))
in (FStar_SMTEncoding_Util.mkAssume uu____7191))
in ((ttm), ((FStar_List.append decls ((d)::[])))))
end)))
end
| FStar_Syntax_Syntax.Tm_app (uu____7206) -> begin
(

let uu____7221 = (FStar_Syntax_Util.head_and_args t0)
in (match (uu____7221) with
| (head1, args_e) -> begin
(

let uu____7262 = (

let uu____7275 = (

let uu____7276 = (FStar_Syntax_Subst.compress head1)
in uu____7276.FStar_Syntax_Syntax.n)
in ((uu____7275), (args_e)))
in (match (uu____7262) with
| uu____7291 when (head_redex env head1) -> begin
(

let uu____7304 = (whnf env t)
in (encode_term uu____7304 env))
end
| uu____7305 when (is_arithmetic_primitive head1 args_e) -> begin
(encode_arith_term env head1 args_e)
end
| uu____7324 when (is_BitVector_primitive head1 args_e) -> begin
(encode_BitVector_term env head1 args_e)
end
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____7338; FStar_Syntax_Syntax.vars = uu____7339}, uu____7340), (uu____7341)::((v1, uu____7343))::((v2, uu____7345))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.lexcons_lid) -> begin
(

let uu____7396 = (encode_term v1 env)
in (match (uu____7396) with
| (v11, decls1) -> begin
(

let uu____7407 = (encode_term v2 env)
in (match (uu____7407) with
| (v21, decls2) -> begin
(

let uu____7418 = (FStar_SMTEncoding_Util.mk_LexCons v11 v21)
in ((uu____7418), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____7422)::((v1, uu____7424))::((v2, uu____7426))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.lexcons_lid) -> begin
(

let uu____7473 = (encode_term v1 env)
in (match (uu____7473) with
| (v11, decls1) -> begin
(

let uu____7484 = (encode_term v2 env)
in (match (uu____7484) with
| (v21, decls2) -> begin
(

let uu____7495 = (FStar_SMTEncoding_Util.mk_LexCons v11 v21)
in ((uu____7495), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), uu____7498) -> begin
(

let e0 = (

let uu____7516 = (FStar_List.hd args_e)
in (FStar_TypeChecker_Util.reify_body_with_arg env.tcenv head1 uu____7516))
in ((

let uu____7524 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____7524) with
| true -> begin
(

let uu____7525 = (FStar_Syntax_Print.term_to_string e0)
in (FStar_Util.print1 "Result of normalization %s\n" uu____7525))
end
| uu____7526 -> begin
()
end));
(

let e = (

let uu____7530 = (

let uu____7531 = (FStar_TypeChecker_Util.remove_reify e0)
in (

let uu____7532 = (FStar_List.tl args_e)
in (FStar_Syntax_Syntax.mk_Tm_app uu____7531 uu____7532)))
in (uu____7530 FStar_Pervasives_Native.None t0.FStar_Syntax_Syntax.pos))
in (encode_term e env));
))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____7541)), ((arg, uu____7543))::[]) -> begin
(encode_term arg env)
end
| uu____7568 -> begin
(

let uu____7581 = (encode_args args_e env)
in (match (uu____7581) with
| (args, decls) -> begin
(

let encode_partial_app = (fun ht_opt -> (

let uu____7636 = (encode_term head1 env)
in (match (uu____7636) with
| (head2, decls') -> begin
(

let app_tm = (mk_Apply_args head2 args)
in (match (ht_opt) with
| FStar_Pervasives_Native.None -> begin
((app_tm), ((FStar_List.append decls decls')))
end
| FStar_Pervasives_Native.Some (formals, c) -> begin
(

let uu____7700 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (uu____7700) with
| (formals1, rest) -> begin
(

let subst1 = (FStar_List.map2 (fun uu____7778 uu____7779 -> (match (((uu____7778), (uu____7779))) with
| ((bv, uu____7801), (a, uu____7803)) -> begin
FStar_Syntax_Syntax.NT (((bv), (a)))
end)) formals1 args_e)
in (

let ty = (

let uu____7821 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right uu____7821 (FStar_Syntax_Subst.subst subst1)))
in (

let uu____7826 = (encode_term_pred FStar_Pervasives_Native.None ty env app_tm)
in (match (uu____7826) with
| (has_type, decls'') -> begin
(

let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (

let e_typing = (

let uu____7841 = (

let uu____7848 = (FStar_SMTEncoding_Util.mkForall ((((has_type)::[])::[]), (cvars), (has_type)))
in (

let uu____7857 = (

let uu____7858 = (

let uu____7859 = (

let uu____7860 = (FStar_SMTEncoding_Term.hash_of_term app_tm)
in (FStar_Util.digest_of_string uu____7860))
in (Prims.strcat "partial_app_typing_" uu____7859))
in (varops.mk_unique uu____7858))
in ((uu____7848), (FStar_Pervasives_Native.Some ("Partial app typing")), (uu____7857))))
in (FStar_SMTEncoding_Util.mkAssume uu____7841))
in ((app_tm), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' ((e_typing)::[]))))))))
end))))
end))
end))
end)))
in (

let encode_full_app = (fun fv -> (

let uu____7877 = (lookup_free_var_sym env fv)
in (match (uu____7877) with
| (fname, fuel_args) -> begin
(

let tm = (FStar_SMTEncoding_Util.mkApp' ((fname), ((FStar_List.append fuel_args args))))
in ((tm), (decls)))
end)))
in (

let head2 = (FStar_Syntax_Subst.compress head1)
in (

let head_type = (match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (x); FStar_Syntax_Syntax.pos = uu____7908; FStar_Syntax_Syntax.vars = uu____7909}, uu____7910) -> begin
FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____7921; FStar_Syntax_Syntax.vars = uu____7922}, uu____7923) -> begin
(

let uu____7928 = (

let uu____7929 = (

let uu____7934 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____7934 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____7929 FStar_Pervasives_Native.snd))
in FStar_Pervasives_Native.Some (uu____7928))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____7964 = (

let uu____7965 = (

let uu____7970 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____7970 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____7965 FStar_Pervasives_Native.snd))
in FStar_Pervasives_Native.Some (uu____7964))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____7999, (FStar_Util.Inl (t1), uu____8001), uu____8002) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____8051, (FStar_Util.Inr (c), uu____8053), uu____8054) -> begin
FStar_Pervasives_Native.Some ((FStar_Syntax_Util.comp_result c))
end
| uu____8103 -> begin
FStar_Pervasives_Native.None
end)
in (match (head_type) with
| FStar_Pervasives_Native.None -> begin
(encode_partial_app FStar_Pervasives_Native.None)
end
| FStar_Pervasives_Native.Some (head_type1) -> begin
(

let head_type2 = (

let uu____8130 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type1)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine uu____8130))
in (

let uu____8131 = (curried_arrow_formals_comp head_type2)
in (match (uu____8131) with
| (formals, c) -> begin
(match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____8147; FStar_Syntax_Syntax.vars = uu____8148}, uu____8149) when (Prims.op_Equality (FStar_List.length formals) (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (Prims.op_Equality (FStar_List.length formals) (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| uu____8163 -> begin
(match (((FStar_List.length formals) > (FStar_List.length args))) with
| true -> begin
(encode_partial_app (FStar_Pervasives_Native.Some (((formals), (c)))))
end
| uu____8176 -> begin
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

let uu____8212 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____8212) with
| (bs1, body1, opening) -> begin
(

let fallback = (fun uu____8235 -> (

let f = (varops.fresh "Tm_abs")
in (

let decl = FStar_SMTEncoding_Term.DeclFun (((f), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Imprecise function encoding"))))
in (

let uu____8242 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in ((uu____8242), ((decl)::[]))))))
in (

let is_impure = (fun rc -> (

let uu____8249 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv rc.FStar_Syntax_Syntax.residual_effect)
in (FStar_All.pipe_right uu____8249 Prims.op_Negation)))
in (

let codomain_eff = (fun rc -> (

let res_typ = (match (rc.FStar_Syntax_Syntax.residual_typ) with
| FStar_Pervasives_Native.None -> begin
(

let uu____8259 = (FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange [] FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right uu____8259 FStar_Pervasives_Native.fst))
end
| FStar_Pervasives_Native.Some (t1) -> begin
t1
end)
in (match ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_Tot_lid)) with
| true -> begin
(

let uu____8279 = (FStar_Syntax_Syntax.mk_Total res_typ)
in FStar_Pervasives_Native.Some (uu____8279))
end
| uu____8280 -> begin
(match ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_GTot_lid)) with
| true -> begin
(

let uu____8283 = (FStar_Syntax_Syntax.mk_GTotal res_typ)
in FStar_Pervasives_Native.Some (uu____8283))
end
| uu____8284 -> begin
FStar_Pervasives_Native.None
end)
end)))
in (match (lopt) with
| FStar_Pervasives_Native.None -> begin
((

let uu____8290 = (

let uu____8291 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)" uu____8291))
in (FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____8290));
(fallback ());
)
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____8293 = ((is_impure rc) && (

let uu____8295 = (FStar_TypeChecker_Env.is_reifiable env.tcenv rc)
in (not (uu____8295))))
in (match (uu____8293) with
| true -> begin
(fallback ())
end
| uu____8300 -> begin
(

let cache_size = (FStar_Util.smap_size env.cache)
in (

let uu____8302 = (encode_binders FStar_Pervasives_Native.None bs1 env)
in (match (uu____8302) with
| (vars, guards, envbody, decls, uu____8327) -> begin
(

let body2 = (

let uu____8341 = (FStar_TypeChecker_Env.is_reifiable env.tcenv rc)
in (match (uu____8341) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env.tcenv body1)
end
| uu____8342 -> begin
body1
end))
in (

let uu____8343 = (encode_term body2 envbody)
in (match (uu____8343) with
| (body3, decls') -> begin
(

let uu____8354 = (

let uu____8363 = (codomain_eff rc)
in (match (uu____8363) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), ([]))
end
| FStar_Pervasives_Native.Some (c) -> begin
(

let tfun = (FStar_Syntax_Util.arrow bs1 c)
in (

let uu____8382 = (encode_term tfun env)
in (match (uu____8382) with
| (t1, decls1) -> begin
((FStar_Pervasives_Native.Some (t1)), (decls1))
end)))
end))
in (match (uu____8354) with
| (arrow_t_opt, decls'') -> begin
(

let key_body = (

let uu____8414 = (

let uu____8425 = (

let uu____8426 = (

let uu____8431 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____8431), (body3)))
in (FStar_SMTEncoding_Util.mkImp uu____8426))
in (([]), (vars), (uu____8425)))
in (FStar_SMTEncoding_Util.mkForall uu____8414))
in (

let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (

let cvars1 = (match (arrow_t_opt) with
| FStar_Pervasives_Native.None -> begin
cvars
end
| FStar_Pervasives_Native.Some (t1) -> begin
(

let uu____8443 = (

let uu____8446 = (FStar_SMTEncoding_Term.free_variables t1)
in (FStar_List.append uu____8446 cvars))
in (FStar_Util.remove_dups FStar_SMTEncoding_Term.fv_eq uu____8443))
end)
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), (cvars1), (key_body)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____8465 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____8465) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
(

let uu____8473 = (

let uu____8474 = (

let uu____8481 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars1)
in ((cache_entry.cache_symbol_name), (uu____8481)))
in (FStar_SMTEncoding_Util.mkApp uu____8474))
in ((uu____8473), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' (use_cache_entry cache_entry)))))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____8492 = (is_an_eta_expansion env vars body3)
in (match (uu____8492) with
| FStar_Pervasives_Native.Some (t1) -> begin
(

let decls1 = (

let uu____8503 = (

let uu____8504 = (FStar_Util.smap_size env.cache)
in (Prims.op_Equality uu____8504 cache_size))
in (match (uu____8503) with
| true -> begin
[]
end
| uu____8507 -> begin
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

let uu____8520 = (

let uu____8521 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_abs_" uu____8521))
in (varops.mk_unique uu____8520))
in (Prims.strcat module_name (Prims.strcat "_" fsym))))
in (

let fdecl = FStar_SMTEncoding_Term.DeclFun (((fsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let f = (

let uu____8528 = (

let uu____8535 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars1)
in ((fsym), (uu____8535)))
in (FStar_SMTEncoding_Util.mkApp uu____8528))
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

let uu____8553 = (

let uu____8554 = (

let uu____8561 = (FStar_SMTEncoding_Util.mkForall ((((f)::[])::[]), (cvars1), (f_has_t)))
in ((uu____8561), (FStar_Pervasives_Native.Some (a_name)), (a_name)))
in (FStar_SMTEncoding_Util.mkAssume uu____8554))
in (uu____8553)::[])))
end)
in (

let interp_f = (

let a_name = (Prims.strcat "interpretation_" fsym)
in (

let uu____8574 = (

let uu____8581 = (

let uu____8582 = (

let uu____8593 = (FStar_SMTEncoding_Util.mkEq ((app), (body3)))
in ((((app)::[])::[]), ((FStar_List.append vars cvars1)), (uu____8593)))
in (FStar_SMTEncoding_Util.mkForall uu____8582))
in ((uu____8581), (FStar_Pervasives_Native.Some (a_name)), (a_name)))
in (FStar_SMTEncoding_Util.mkAssume uu____8574)))
in (

let f_decls = (FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' (FStar_List.append ((fdecl)::typing_f) ((interp_f)::[])))))
in ((

let uu____8610 = (mk_cache_entry env fsym cvar_sorts f_decls)
in (FStar_Util.smap_add env.cache tkey_hash uu____8610));
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
| FStar_Syntax_Syntax.Tm_let ((uu____8613, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____8614); FStar_Syntax_Syntax.lbunivs = uu____8615; FStar_Syntax_Syntax.lbtyp = uu____8616; FStar_Syntax_Syntax.lbeff = uu____8617; FStar_Syntax_Syntax.lbdef = uu____8618})::uu____8619), uu____8620) -> begin
(failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____8646; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____8648; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (uu____8669) -> begin
((FStar_Errors.diag t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions, and their enclosings let bindings (including the top-level let) are not yet fully encoded to the SMT solver; you may not be able to prove some facts");
(FStar_Exn.raise Inner_let_rec);
)
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end);
)))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (

let uu____8739 = (encode_term e1 env)
in (match (uu____8739) with
| (ee1, decls1) -> begin
(

let uu____8750 = (FStar_Syntax_Subst.open_term ((((x), (FStar_Pervasives_Native.None)))::[]) e2)
in (match (uu____8750) with
| (xs, e21) -> begin
(

let uu____8775 = (FStar_List.hd xs)
in (match (uu____8775) with
| (x1, uu____8789) -> begin
(

let env' = (push_term_var env x1 ee1)
in (

let uu____8791 = (encode_body e21 env')
in (match (uu____8791) with
| (ee2, decls2) -> begin
((ee2), ((FStar_List.append decls1 decls2)))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (

let uu____8823 = (

let uu____8830 = (

let uu____8831 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.null_bv uu____8831))
in (gen_term_var env uu____8830))
in (match (uu____8823) with
| (scrsym, scr', env1) -> begin
(

let uu____8839 = (encode_term e env1)
in (match (uu____8839) with
| (scr, decls) -> begin
(

let uu____8850 = (

let encode_branch = (fun b uu____8875 -> (match (uu____8875) with
| (else_case, decls1) -> begin
(

let uu____8894 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____8894) with
| (p, w, br) -> begin
(

let uu____8920 = (encode_pat env1 p)
in (match (uu____8920) with
| (env0, pattern) -> begin
(

let guard = (pattern.guard scr')
in (

let projections = (pattern.projections scr')
in (

let env2 = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env2 uu____8957 -> (match (uu____8957) with
| (x, t) -> begin
(push_term_var env2 x t)
end)) env1))
in (

let uu____8964 = (match (w) with
| FStar_Pervasives_Native.None -> begin
((guard), ([]))
end
| FStar_Pervasives_Native.Some (w1) -> begin
(

let uu____8986 = (encode_term w1 env2)
in (match (uu____8986) with
| (w2, decls2) -> begin
(

let uu____8999 = (

let uu____9000 = (

let uu____9005 = (

let uu____9006 = (

let uu____9011 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue)
in ((w2), (uu____9011)))
in (FStar_SMTEncoding_Util.mkEq uu____9006))
in ((guard), (uu____9005)))
in (FStar_SMTEncoding_Util.mkAnd uu____9000))
in ((uu____8999), (decls2)))
end))
end)
in (match (uu____8964) with
| (guard1, decls2) -> begin
(

let uu____9024 = (encode_br br env2)
in (match (uu____9024) with
| (br1, decls3) -> begin
(

let uu____9037 = (FStar_SMTEncoding_Util.mkITE ((guard1), (br1), (else_case)))
in ((uu____9037), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end)))))
end))
end))
end))
in (FStar_List.fold_right encode_branch pats ((default_case), (decls))))
in (match (uu____8850) with
| (match_tm, decls1) -> begin
(

let uu____9056 = (FStar_SMTEncoding_Term.mkLet' (((((((scrsym), (FStar_SMTEncoding_Term.Term_sort))), (scr)))::[]), (match_tm)) FStar_Range.dummyRange)
in ((uu____9056), (decls1)))
end))
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> ((

let uu____9096 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____9096) with
| true -> begin
(

let uu____9097 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" uu____9097))
end
| uu____9098 -> begin
()
end));
(

let uu____9099 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (uu____9099) with
| (vars, pat_term) -> begin
(

let uu____9116 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun uu____9169 v1 -> (match (uu____9169) with
| (env1, vars1) -> begin
(

let uu____9221 = (gen_term_var env1 v1)
in (match (uu____9221) with
| (xx, uu____9243, env2) -> begin
((env2), ((((v1), (((xx), (FStar_SMTEncoding_Term.Term_sort)))))::vars1))
end))
end)) ((env), ([]))))
in (match (uu____9116) with
| (env1, vars1) -> begin
(

let rec mk_guard = (fun pat1 scrutinee -> (match (pat1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_var (uu____9322) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_wild (uu____9323) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____9324) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____9332 = (

let uu____9337 = (encode_const c)
in ((scrutinee), (uu____9337)))
in (FStar_SMTEncoding_Util.mkEq uu____9332))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let is_f = (

let tc_name = (FStar_TypeChecker_Env.typ_of_datacon env1.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let uu____9358 = (FStar_TypeChecker_Env.datacons_of_typ env1.tcenv tc_name)
in (match (uu____9358) with
| (uu____9365, (uu____9366)::[]) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| uu____9369 -> begin
(mk_data_tester env1 f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
end)))
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____9402 -> (match (uu____9402) with
| (arg, uu____9410) -> begin
(

let proj = (primitive_projector_by_pos env1.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____9416 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_guard arg uu____9416)))
end))))
in (FStar_SMTEncoding_Util.mk_and_l ((is_f)::sub_term_guards))))
end))
in (

let rec mk_projections = (fun pat1 scrutinee -> (match (pat1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (x, uu____9443) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_constant (uu____9474) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let uu____9497 = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____9541 -> (match (uu____9541) with
| (arg, uu____9555) -> begin
(

let proj = (primitive_projector_by_pos env1.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____9561 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_projections arg uu____9561)))
end))))
in (FStar_All.pipe_right uu____9497 FStar_List.flatten))
end))
in (

let pat_term1 = (fun uu____9589 -> (encode_term pat_term env1))
in (

let pattern = {pat_vars = vars1; pat_term = pat_term1; guard = (mk_guard pat); projections = (mk_projections pat)}
in ((env1), (pattern))))))
end))
end));
))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (

let uu____9599 = (FStar_All.pipe_right l (FStar_List.fold_left (fun uu____9637 uu____9638 -> (match (((uu____9637), (uu____9638))) with
| ((tms, decls), (t, uu____9674)) -> begin
(

let uu____9695 = (encode_term t env)
in (match (uu____9695) with
| (t1, decls') -> begin
(((t1)::tms), ((FStar_List.append decls decls')))
end))
end)) (([]), ([]))))
in (match (uu____9599) with
| (l1, decls) -> begin
(((FStar_List.rev l1)), (decls))
end)))
and encode_function_type_as_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let list_elements1 = (fun e -> (

let uu____9752 = (FStar_Syntax_Util.list_elements e)
in (match (uu____9752) with
| FStar_Pervasives_Native.Some (l) -> begin
l
end
| FStar_Pervasives_Native.None -> begin
((FStar_Errors.warn e.FStar_Syntax_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern");
[];
)
end)))
in (

let one_pat = (fun p -> (

let uu____9773 = (

let uu____9788 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right uu____9788 FStar_Syntax_Util.head_and_args))
in (match (uu____9773) with
| (head1, args) -> begin
(

let uu____9827 = (

let uu____9840 = (

let uu____9841 = (FStar_Syntax_Util.un_uinst head1)
in uu____9841.FStar_Syntax_Syntax.n)
in ((uu____9840), (args)))
in (match (uu____9827) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((uu____9855, uu____9856))::((e, uu____9858))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpat_lid) -> begin
e
end
| uu____9893 -> begin
(failwith "Unexpected pattern term")
end))
end)))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements1 p)
in (

let smt_pat_or1 = (fun t1 -> (

let uu____9929 = (

let uu____9944 = (FStar_Syntax_Util.unmeta t1)
in (FStar_All.pipe_right uu____9944 FStar_Syntax_Util.head_and_args))
in (match (uu____9929) with
| (head1, args) -> begin
(

let uu____9985 = (

let uu____9998 = (

let uu____9999 = (FStar_Syntax_Util.un_uinst head1)
in uu____9999.FStar_Syntax_Syntax.n)
in ((uu____9998), (args)))
in (match (uu____9985) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, uu____10016))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpatOr_lid) -> begin
FStar_Pervasives_Native.Some (e)
end
| uu____10043 -> begin
FStar_Pervasives_Native.None
end))
end)))
in (match (elts) with
| (t1)::[] -> begin
(

let uu____10065 = (smt_pat_or1 t1)
in (match (uu____10065) with
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____10081 = (list_elements1 e)
in (FStar_All.pipe_right uu____10081 (FStar_List.map (fun branch1 -> (

let uu____10099 = (list_elements1 branch1)
in (FStar_All.pipe_right uu____10099 (FStar_List.map one_pat)))))))
end
| uu____10110 -> begin
(

let uu____10115 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____10115)::[])
end))
end
| uu____10136 -> begin
(

let uu____10139 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____10139)::[])
end))))
in (

let uu____10160 = (

let uu____10179 = (

let uu____10180 = (FStar_Syntax_Subst.compress t)
in uu____10180.FStar_Syntax_Syntax.n)
in (match (uu____10179) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____10219 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____10219) with
| (binders1, c1) -> begin
(match (c1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____10262; FStar_Syntax_Syntax.effect_name = uu____10263; FStar_Syntax_Syntax.result_typ = uu____10264; FStar_Syntax_Syntax.effect_args = ((pre, uu____10266))::((post, uu____10268))::((pats, uu____10270))::[]; FStar_Syntax_Syntax.flags = uu____10271}) -> begin
(

let uu____10312 = (lemma_pats pats)
in ((binders1), (pre), (post), (uu____10312)))
end
| uu____10329 -> begin
(failwith "impos")
end)
end))
end
| uu____10348 -> begin
(failwith "Impos")
end))
in (match (uu____10160) with
| (binders, pre, post, patterns) -> begin
(

let env1 = (

let uu___142_10396 = env
in {bindings = uu___142_10396.bindings; depth = uu___142_10396.depth; tcenv = uu___142_10396.tcenv; warn = uu___142_10396.warn; cache = uu___142_10396.cache; nolabels = uu___142_10396.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___142_10396.encode_non_total_function_typ; current_module_name = uu___142_10396.current_module_name})
in (

let uu____10397 = (encode_binders FStar_Pervasives_Native.None binders env1)
in (match (uu____10397) with
| (vars, guards, env2, decls, uu____10422) -> begin
(

let uu____10435 = (

let uu____10448 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch1 -> (

let uu____10492 = (

let uu____10501 = (FStar_All.pipe_right branch1 (FStar_List.map (fun t1 -> (encode_term t1 env2))))
in (FStar_All.pipe_right uu____10501 FStar_List.unzip))
in (match (uu____10492) with
| (pats, decls1) -> begin
((pats), (decls1))
end)))))
in (FStar_All.pipe_right uu____10448 FStar_List.unzip))
in (match (uu____10435) with
| (pats, decls') -> begin
(

let decls'1 = (FStar_List.flatten decls')
in (

let env3 = (

let uu___143_10610 = env2
in {bindings = uu___143_10610.bindings; depth = uu___143_10610.depth; tcenv = uu___143_10610.tcenv; warn = uu___143_10610.warn; cache = uu___143_10610.cache; nolabels = true; use_zfuel_name = uu___143_10610.use_zfuel_name; encode_non_total_function_typ = uu___143_10610.encode_non_total_function_typ; current_module_name = uu___143_10610.current_module_name})
in (

let uu____10611 = (

let uu____10616 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula uu____10616 env3))
in (match (uu____10611) with
| (pre1, decls'') -> begin
(

let uu____10623 = (

let uu____10628 = (FStar_Syntax_Util.unmeta post)
in (encode_formula uu____10628 env3))
in (match (uu____10623) with
| (post1, decls''') -> begin
(

let decls1 = (FStar_List.append decls (FStar_List.append (FStar_List.flatten decls'1) (FStar_List.append decls'' decls''')))
in (

let uu____10638 = (

let uu____10639 = (

let uu____10650 = (

let uu____10651 = (

let uu____10656 = (FStar_SMTEncoding_Util.mk_and_l ((pre1)::guards))
in ((uu____10656), (post1)))
in (FStar_SMTEncoding_Util.mkImp uu____10651))
in ((pats), (vars), (uu____10650)))
in (FStar_SMTEncoding_Util.mkForall uu____10639))
in ((uu____10638), (decls1))))
end))
end))))
end))
end)))
end))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (

let debug1 = (fun phi1 -> (

let uu____10675 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____10675) with
| true -> begin
(

let uu____10676 = (FStar_Syntax_Print.tag_of_term phi1)
in (

let uu____10677 = (FStar_Syntax_Print.term_to_string phi1)
in (FStar_Util.print2 "Formula (%s)  %s\n" uu____10676 uu____10677)))
end
| uu____10678 -> begin
()
end)))
in (

let enc = (fun f r l -> (

let uu____10710 = (FStar_Util.fold_map (fun decls x -> (

let uu____10738 = (encode_term (FStar_Pervasives_Native.fst x) env)
in (match (uu____10738) with
| (t, decls') -> begin
(((FStar_List.append decls decls')), (t))
end))) [] l)
in (match (uu____10710) with
| (decls, args) -> begin
(

let uu____10767 = (

let uu___144_10768 = (f args)
in {FStar_SMTEncoding_Term.tm = uu___144_10768.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___144_10768.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____10767), (decls)))
end)))
in (

let const_op = (fun f r uu____10799 -> (

let uu____10812 = (f r)
in ((uu____10812), ([]))))
in (

let un_op = (fun f l -> (

let uu____10831 = (FStar_List.hd l)
in (FStar_All.pipe_left f uu____10831)))
in (

let bin_op = (fun f uu___118_10847 -> (match (uu___118_10847) with
| (t1)::(t2)::[] -> begin
(f ((t1), (t2)))
end
| uu____10858 -> begin
(failwith "Impossible")
end))
in (

let enc_prop_c = (fun f r l -> (

let uu____10892 = (FStar_Util.fold_map (fun decls uu____10915 -> (match (uu____10915) with
| (t, uu____10929) -> begin
(

let uu____10930 = (encode_formula t env)
in (match (uu____10930) with
| (phi1, decls') -> begin
(((FStar_List.append decls decls')), (phi1))
end))
end)) [] l)
in (match (uu____10892) with
| (decls, phis) -> begin
(

let uu____10959 = (

let uu___145_10960 = (f phis)
in {FStar_SMTEncoding_Term.tm = uu___145_10960.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___145_10960.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____10959), (decls)))
end)))
in (

let eq_op = (fun r args -> (

let rf = (FStar_List.filter (fun uu____11021 -> (match (uu____11021) with
| (a, q) -> begin
(match (q) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____11040)) -> begin
false
end
| uu____11041 -> begin
true
end)
end)) args)
in (match ((Prims.op_disEquality (FStar_List.length rf) (Prims.parse_int "2"))) with
| true -> begin
(

let uu____11056 = (FStar_Util.format1 "eq_op: got %s non-implicit arguments instead of 2?" (Prims.string_of_int (FStar_List.length rf)))
in (failwith uu____11056))
end
| uu____11069 -> begin
(

let uu____11070 = (enc (bin_op FStar_SMTEncoding_Util.mkEq))
in (uu____11070 r rf))
end)))
in (

let mk_imp1 = (fun r uu___119_11095 -> (match (uu___119_11095) with
| ((lhs, uu____11101))::((rhs, uu____11103))::[] -> begin
(

let uu____11130 = (encode_formula rhs env)
in (match (uu____11130) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____11145) -> begin
((l1), (decls1))
end
| uu____11150 -> begin
(

let uu____11151 = (encode_formula lhs env)
in (match (uu____11151) with
| (l2, decls2) -> begin
(

let uu____11162 = (FStar_SMTEncoding_Term.mkImp ((l2), (l1)) r)
in ((uu____11162), ((FStar_List.append decls1 decls2))))
end))
end)
end))
end
| uu____11165 -> begin
(failwith "impossible")
end))
in (

let mk_ite = (fun r uu___120_11186 -> (match (uu___120_11186) with
| ((guard, uu____11192))::((_then, uu____11194))::((_else, uu____11196))::[] -> begin
(

let uu____11233 = (encode_formula guard env)
in (match (uu____11233) with
| (g, decls1) -> begin
(

let uu____11244 = (encode_formula _then env)
in (match (uu____11244) with
| (t, decls2) -> begin
(

let uu____11255 = (encode_formula _else env)
in (match (uu____11255) with
| (e, decls3) -> begin
(

let res = (FStar_SMTEncoding_Term.mkITE ((g), (t), (e)) r)
in ((res), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end))
end))
end
| uu____11269 -> begin
(failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (

let uu____11294 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f uu____11294)))
in (

let connectives = (

let uu____11312 = (

let uu____11325 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd))
in ((FStar_Parser_Const.and_lid), (uu____11325)))
in (

let uu____11342 = (

let uu____11357 = (

let uu____11370 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr))
in ((FStar_Parser_Const.or_lid), (uu____11370)))
in (

let uu____11387 = (

let uu____11402 = (

let uu____11417 = (

let uu____11430 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff))
in ((FStar_Parser_Const.iff_lid), (uu____11430)))
in (

let uu____11447 = (

let uu____11462 = (

let uu____11477 = (

let uu____11490 = (enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot))
in ((FStar_Parser_Const.not_lid), (uu____11490)))
in (uu____11477)::(((FStar_Parser_Const.eq2_lid), (eq_op)))::(((FStar_Parser_Const.eq3_lid), (eq_op)))::(((FStar_Parser_Const.true_lid), ((const_op FStar_SMTEncoding_Term.mkTrue))))::(((FStar_Parser_Const.false_lid), ((const_op FStar_SMTEncoding_Term.mkFalse))))::[])
in (((FStar_Parser_Const.ite_lid), (mk_ite)))::uu____11462)
in (uu____11417)::uu____11447))
in (((FStar_Parser_Const.imp_lid), (mk_imp1)))::uu____11402)
in (uu____11357)::uu____11387))
in (uu____11312)::uu____11342))
in (

let rec fallback = (fun phi1 -> (match (phi1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(

let uu____11811 = (encode_formula phi' env)
in (match (uu____11811) with
| (phi2, decls) -> begin
(

let uu____11822 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled (((phi2), (msg), (r)))) r)
in ((uu____11822), (decls)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (uu____11823) -> begin
(

let uu____11830 = (FStar_Syntax_Util.unmeta phi1)
in (encode_formula uu____11830 env))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(

let uu____11869 = (encode_match e pats FStar_SMTEncoding_Util.mkFalse env encode_formula)
in (match (uu____11869) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____11881; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____11883; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let uu____11904 = (encode_let x t1 e1 e2 env encode_formula)
in (match (uu____11904) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let head2 = (FStar_Syntax_Util.un_uinst head1)
in (match (((head2.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____11951)::((x, uu____11953))::((t, uu____11955))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.has_type_lid) -> begin
(

let uu____12002 = (encode_term x env)
in (match (uu____12002) with
| (x1, decls) -> begin
(

let uu____12013 = (encode_term t env)
in (match (uu____12013) with
| (t1, decls') -> begin
(

let uu____12024 = (FStar_SMTEncoding_Term.mk_HasType x1 t1)
in ((uu____12024), ((FStar_List.append decls decls'))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((r, uu____12029))::((msg, uu____12031))::((phi2, uu____12033))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.labeled_lid) -> begin
(

let uu____12078 = (

let uu____12083 = (

let uu____12084 = (FStar_Syntax_Subst.compress r)
in uu____12084.FStar_Syntax_Syntax.n)
in (

let uu____12087 = (

let uu____12088 = (FStar_Syntax_Subst.compress msg)
in uu____12088.FStar_Syntax_Syntax.n)
in ((uu____12083), (uu____12087))))
in (match (uu____12078) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____12097))) -> begin
(

let phi3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((phi2), (FStar_Syntax_Syntax.Meta_labeled (((s), (r1), (false))))))) FStar_Pervasives_Native.None r1)
in (fallback phi3))
end
| uu____12103 -> begin
(fallback phi2)
end))
end
| uu____12108 when (head_redex env head2) -> begin
(

let uu____12121 = (whnf env phi1)
in (encode_formula uu____12121 env))
end
| uu____12122 -> begin
(

let uu____12135 = (encode_term phi1 env)
in (match (uu____12135) with
| (tt, decls) -> begin
(

let uu____12146 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___146_12149 = tt
in {FStar_SMTEncoding_Term.tm = uu___146_12149.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___146_12149.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi1.FStar_Syntax_Syntax.pos}))
in ((uu____12146), (decls)))
end))
end))
end
| uu____12150 -> begin
(

let uu____12151 = (encode_term phi1 env)
in (match (uu____12151) with
| (tt, decls) -> begin
(

let uu____12162 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___147_12165 = tt
in {FStar_SMTEncoding_Term.tm = uu___147_12165.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___147_12165.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi1.FStar_Syntax_Syntax.pos}))
in ((uu____12162), (decls)))
end))
end))
in (

let encode_q_body = (fun env1 bs ps body -> (

let uu____12201 = (encode_binders FStar_Pervasives_Native.None bs env1)
in (match (uu____12201) with
| (vars, guards, env2, decls, uu____12240) -> begin
(

let uu____12253 = (

let uu____12266 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let uu____12314 = (

let uu____12323 = (FStar_All.pipe_right p (FStar_List.map (fun uu____12353 -> (match (uu____12353) with
| (t, uu____12363) -> begin
(encode_term t (

let uu___148_12365 = env2
in {bindings = uu___148_12365.bindings; depth = uu___148_12365.depth; tcenv = uu___148_12365.tcenv; warn = uu___148_12365.warn; cache = uu___148_12365.cache; nolabels = uu___148_12365.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___148_12365.encode_non_total_function_typ; current_module_name = uu___148_12365.current_module_name}))
end))))
in (FStar_All.pipe_right uu____12323 FStar_List.unzip))
in (match (uu____12314) with
| (p1, decls1) -> begin
((p1), ((FStar_List.flatten decls1)))
end)))))
in (FStar_All.pipe_right uu____12266 FStar_List.unzip))
in (match (uu____12253) with
| (pats, decls') -> begin
(

let uu____12464 = (encode_formula body env2)
in (match (uu____12464) with
| (body1, decls'') -> begin
(

let guards1 = (match (pats) with
| (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (gf), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____12496; FStar_SMTEncoding_Term.rng = uu____12497})::[])::[] when (Prims.op_Equality (FStar_Ident.text_of_lid FStar_Parser_Const.guard_free) gf) -> begin
[]
end
| uu____12512 -> begin
guards
end)
in (

let uu____12517 = (FStar_SMTEncoding_Util.mk_and_l guards1)
in ((vars), (pats), (uu____12517), (body1), ((FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') decls''))))))
end))
end))
end)))
in ((debug1 phi);
(

let phi1 = (FStar_Syntax_Util.unascribe phi)
in (

let check_pattern_vars = (fun vars pats -> (

let pats1 = (FStar_All.pipe_right pats (FStar_List.map (fun uu____12577 -> (match (uu____12577) with
| (x, uu____12583) -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x)
end))))
in (match (pats1) with
| [] -> begin
()
end
| (hd1)::tl1 -> begin
(

let pat_vars = (

let uu____12591 = (FStar_Syntax_Free.names hd1)
in (FStar_List.fold_left (fun out x -> (

let uu____12603 = (FStar_Syntax_Free.names x)
in (FStar_Util.set_union out uu____12603))) uu____12591 tl1))
in (

let uu____12606 = (FStar_All.pipe_right vars (FStar_Util.find_opt (fun uu____12633 -> (match (uu____12633) with
| (b, uu____12639) -> begin
(

let uu____12640 = (FStar_Util.set_mem b pat_vars)
in (not (uu____12640)))
end))))
in (match (uu____12606) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (x, uu____12646) -> begin
(

let pos = (FStar_List.fold_left (fun out t -> (FStar_Range.union_ranges out t.FStar_Syntax_Syntax.pos)) hd1.FStar_Syntax_Syntax.pos tl1)
in (

let uu____12660 = (

let uu____12661 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "SMT pattern misses at least one bound variable: %s" uu____12661))
in (FStar_Errors.warn pos uu____12660)))
end)))
end)))
in (

let uu____12662 = (FStar_Syntax_Util.destruct_typ_as_formula phi1)
in (match (uu____12662) with
| FStar_Pervasives_Native.None -> begin
(fallback phi1)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(

let uu____12671 = (FStar_All.pipe_right connectives (FStar_List.tryFind (fun uu____12729 -> (match (uu____12729) with
| (l, uu____12743) -> begin
(FStar_Ident.lid_equals op l)
end))))
in (match (uu____12671) with
| FStar_Pervasives_Native.None -> begin
(fallback phi1)
end
| FStar_Pervasives_Native.Some (uu____12776, f) -> begin
(f phi1.FStar_Syntax_Syntax.pos arms)
end))
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____12816 = (encode_q_body env vars pats body)
in (match (uu____12816) with
| (vars1, pats1, guard, body1, decls) -> begin
(

let tm = (

let uu____12861 = (

let uu____12872 = (FStar_SMTEncoding_Util.mkImp ((guard), (body1)))
in ((pats1), (vars1), (uu____12872)))
in (FStar_SMTEncoding_Term.mkForall uu____12861 phi1.FStar_Syntax_Syntax.pos))
in ((tm), (decls)))
end));
)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____12891 = (encode_q_body env vars pats body)
in (match (uu____12891) with
| (vars1, pats1, guard, body1, decls) -> begin
(

let uu____12935 = (

let uu____12936 = (

let uu____12947 = (FStar_SMTEncoding_Util.mkAnd ((guard), (body1)))
in ((pats1), (vars1), (uu____12947)))
in (FStar_SMTEncoding_Term.mkExists uu____12936 phi1.FStar_Syntax_Syntax.pos))
in ((uu____12935), (decls)))
end));
)
end))));
)))))))))))))))

type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list); is : FStar_Ident.lident  ->  Prims.bool}


let __proj__Mkprims_t__item__mk : prims_t  ->  FStar_Ident.lident  ->  Prims.string  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list) = (fun projectee -> (match (projectee) with
| {mk = __fname__mk; is = __fname__is} -> begin
__fname__mk
end))


let __proj__Mkprims_t__item__is : prims_t  ->  FStar_Ident.lident  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {mk = __fname__mk; is = __fname__is} -> begin
__fname__is
end))


let prims : prims_t = (

let uu____13045 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____13045) with
| (asym, a) -> begin
(

let uu____13052 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____13052) with
| (xsym, x) -> begin
(

let uu____13059 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____13059) with
| (ysym, y) -> begin
(

let quant = (fun vars body x1 -> (

let xname_decl = (

let uu____13103 = (

let uu____13114 = (FStar_All.pipe_right vars (FStar_List.map FStar_Pervasives_Native.snd))
in ((x1), (uu____13114), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____13103))
in (

let xtok = (Prims.strcat x1 "@tok")
in (

let xtok_decl = FStar_SMTEncoding_Term.DeclFun (((xtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let xapp = (

let uu____13140 = (

let uu____13147 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((x1), (uu____13147)))
in (FStar_SMTEncoding_Util.mkApp uu____13140))
in (

let xtok1 = (FStar_SMTEncoding_Util.mkApp ((xtok), ([])))
in (

let xtok_app = (mk_Apply xtok1 vars)
in (

let uu____13160 = (

let uu____13163 = (

let uu____13166 = (

let uu____13169 = (

let uu____13170 = (

let uu____13177 = (

let uu____13178 = (

let uu____13189 = (FStar_SMTEncoding_Util.mkEq ((xapp), (body)))
in ((((xapp)::[])::[]), (vars), (uu____13189)))
in (FStar_SMTEncoding_Util.mkForall uu____13178))
in ((uu____13177), (FStar_Pervasives_Native.None), ((Prims.strcat "primitive_" x1))))
in (FStar_SMTEncoding_Util.mkAssume uu____13170))
in (

let uu____13206 = (

let uu____13209 = (

let uu____13210 = (

let uu____13217 = (

let uu____13218 = (

let uu____13229 = (FStar_SMTEncoding_Util.mkEq ((xtok_app), (xapp)))
in ((((xtok_app)::[])::[]), (vars), (uu____13229)))
in (FStar_SMTEncoding_Util.mkForall uu____13218))
in ((uu____13217), (FStar_Pervasives_Native.Some ("Name-token correspondence")), ((Prims.strcat "token_correspondence_" x1))))
in (FStar_SMTEncoding_Util.mkAssume uu____13210))
in (uu____13209)::[])
in (uu____13169)::uu____13206))
in (xtok_decl)::uu____13166)
in (xname_decl)::uu____13163)
in ((xtok1), (uu____13160))))))))))
in (

let axy = (((asym), (FStar_SMTEncoding_Term.Term_sort)))::(((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let xy = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let qx = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let prims1 = (

let uu____13320 = (

let uu____13333 = (

let uu____13342 = (

let uu____13343 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13343))
in (quant axy uu____13342))
in ((FStar_Parser_Const.op_Eq), (uu____13333)))
in (

let uu____13352 = (

let uu____13367 = (

let uu____13380 = (

let uu____13389 = (

let uu____13390 = (

let uu____13391 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_SMTEncoding_Util.mkNot uu____13391))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13390))
in (quant axy uu____13389))
in ((FStar_Parser_Const.op_notEq), (uu____13380)))
in (

let uu____13400 = (

let uu____13415 = (

let uu____13428 = (

let uu____13437 = (

let uu____13438 = (

let uu____13439 = (

let uu____13444 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13445 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13444), (uu____13445))))
in (FStar_SMTEncoding_Util.mkLT uu____13439))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13438))
in (quant xy uu____13437))
in ((FStar_Parser_Const.op_LT), (uu____13428)))
in (

let uu____13454 = (

let uu____13469 = (

let uu____13482 = (

let uu____13491 = (

let uu____13492 = (

let uu____13493 = (

let uu____13498 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13499 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13498), (uu____13499))))
in (FStar_SMTEncoding_Util.mkLTE uu____13493))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13492))
in (quant xy uu____13491))
in ((FStar_Parser_Const.op_LTE), (uu____13482)))
in (

let uu____13508 = (

let uu____13523 = (

let uu____13536 = (

let uu____13545 = (

let uu____13546 = (

let uu____13547 = (

let uu____13552 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13553 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13552), (uu____13553))))
in (FStar_SMTEncoding_Util.mkGT uu____13547))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13546))
in (quant xy uu____13545))
in ((FStar_Parser_Const.op_GT), (uu____13536)))
in (

let uu____13562 = (

let uu____13577 = (

let uu____13590 = (

let uu____13599 = (

let uu____13600 = (

let uu____13601 = (

let uu____13606 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13607 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13606), (uu____13607))))
in (FStar_SMTEncoding_Util.mkGTE uu____13601))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13600))
in (quant xy uu____13599))
in ((FStar_Parser_Const.op_GTE), (uu____13590)))
in (

let uu____13616 = (

let uu____13631 = (

let uu____13644 = (

let uu____13653 = (

let uu____13654 = (

let uu____13655 = (

let uu____13660 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13661 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13660), (uu____13661))))
in (FStar_SMTEncoding_Util.mkSub uu____13655))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____13654))
in (quant xy uu____13653))
in ((FStar_Parser_Const.op_Subtraction), (uu____13644)))
in (

let uu____13670 = (

let uu____13685 = (

let uu____13698 = (

let uu____13707 = (

let uu____13708 = (

let uu____13709 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Util.mkMinus uu____13709))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____13708))
in (quant qx uu____13707))
in ((FStar_Parser_Const.op_Minus), (uu____13698)))
in (

let uu____13718 = (

let uu____13733 = (

let uu____13746 = (

let uu____13755 = (

let uu____13756 = (

let uu____13757 = (

let uu____13762 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13763 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13762), (uu____13763))))
in (FStar_SMTEncoding_Util.mkAdd uu____13757))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____13756))
in (quant xy uu____13755))
in ((FStar_Parser_Const.op_Addition), (uu____13746)))
in (

let uu____13772 = (

let uu____13787 = (

let uu____13800 = (

let uu____13809 = (

let uu____13810 = (

let uu____13811 = (

let uu____13816 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13817 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13816), (uu____13817))))
in (FStar_SMTEncoding_Util.mkMul uu____13811))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____13810))
in (quant xy uu____13809))
in ((FStar_Parser_Const.op_Multiply), (uu____13800)))
in (

let uu____13826 = (

let uu____13841 = (

let uu____13854 = (

let uu____13863 = (

let uu____13864 = (

let uu____13865 = (

let uu____13870 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13871 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13870), (uu____13871))))
in (FStar_SMTEncoding_Util.mkDiv uu____13865))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____13864))
in (quant xy uu____13863))
in ((FStar_Parser_Const.op_Division), (uu____13854)))
in (

let uu____13880 = (

let uu____13895 = (

let uu____13908 = (

let uu____13917 = (

let uu____13918 = (

let uu____13919 = (

let uu____13924 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13925 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13924), (uu____13925))))
in (FStar_SMTEncoding_Util.mkMod uu____13919))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____13918))
in (quant xy uu____13917))
in ((FStar_Parser_Const.op_Modulus), (uu____13908)))
in (

let uu____13934 = (

let uu____13949 = (

let uu____13962 = (

let uu____13971 = (

let uu____13972 = (

let uu____13973 = (

let uu____13978 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____13979 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____13978), (uu____13979))))
in (FStar_SMTEncoding_Util.mkAnd uu____13973))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13972))
in (quant xy uu____13971))
in ((FStar_Parser_Const.op_And), (uu____13962)))
in (

let uu____13988 = (

let uu____14003 = (

let uu____14016 = (

let uu____14025 = (

let uu____14026 = (

let uu____14027 = (

let uu____14032 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____14033 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____14032), (uu____14033))))
in (FStar_SMTEncoding_Util.mkOr uu____14027))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____14026))
in (quant xy uu____14025))
in ((FStar_Parser_Const.op_Or), (uu____14016)))
in (

let uu____14042 = (

let uu____14057 = (

let uu____14070 = (

let uu____14079 = (

let uu____14080 = (

let uu____14081 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Util.mkNot uu____14081))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____14080))
in (quant qx uu____14079))
in ((FStar_Parser_Const.op_Negation), (uu____14070)))
in (uu____14057)::[])
in (uu____14003)::uu____14042))
in (uu____13949)::uu____13988))
in (uu____13895)::uu____13934))
in (uu____13841)::uu____13880))
in (uu____13787)::uu____13826))
in (uu____13733)::uu____13772))
in (uu____13685)::uu____13718))
in (uu____13631)::uu____13670))
in (uu____13577)::uu____13616))
in (uu____13523)::uu____13562))
in (uu____13469)::uu____13508))
in (uu____13415)::uu____13454))
in (uu____13367)::uu____13400))
in (uu____13320)::uu____13352))
in (

let mk1 = (fun l v1 -> (

let uu____14295 = (

let uu____14304 = (FStar_All.pipe_right prims1 (FStar_List.find (fun uu____14362 -> (match (uu____14362) with
| (l', uu____14376) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right uu____14304 (FStar_Option.map (fun uu____14436 -> (match (uu____14436) with
| (uu____14455, b) -> begin
(b v1)
end)))))
in (FStar_All.pipe_right uu____14295 FStar_Option.get)))
in (

let is = (fun l -> (FStar_All.pipe_right prims1 (FStar_Util.for_some (fun uu____14526 -> (match (uu____14526) with
| (l', uu____14540) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk1; is = is})))))))
end))
end))
end))


let pretype_axiom : env_t  ->  FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun env tapp vars -> (

let uu____14581 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____14581) with
| (xxsym, xx) -> begin
(

let uu____14588 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____14588) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let tapp_hash = (FStar_SMTEncoding_Term.hash_of_term tapp)
in (

let module_name = env.current_module_name
in (

let uu____14598 = (

let uu____14605 = (

let uu____14606 = (

let uu____14617 = (

let uu____14618 = (

let uu____14623 = (

let uu____14624 = (

let uu____14629 = (FStar_SMTEncoding_Util.mkApp (("PreType"), ((xx)::[])))
in ((tapp), (uu____14629)))
in (FStar_SMTEncoding_Util.mkEq uu____14624))
in ((xx_has_type), (uu____14623)))
in (FStar_SMTEncoding_Util.mkImp uu____14618))
in ((((xx_has_type)::[])::[]), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars), (uu____14617)))
in (FStar_SMTEncoding_Util.mkForall uu____14606))
in (

let uu____14654 = (

let uu____14655 = (

let uu____14656 = (

let uu____14657 = (FStar_Util.digest_of_string tapp_hash)
in (Prims.strcat "_pretyping_" uu____14657))
in (Prims.strcat module_name uu____14656))
in (varops.mk_unique uu____14655))
in ((uu____14605), (FStar_Pervasives_Native.Some ("pretyping")), (uu____14654))))
in (FStar_SMTEncoding_Util.mkAssume uu____14598)))))
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

let uu____14697 = (

let uu____14698 = (

let uu____14705 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in ((uu____14705), (FStar_Pervasives_Native.Some ("unit typing")), ("unit_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____14698))
in (

let uu____14708 = (

let uu____14711 = (

let uu____14712 = (

let uu____14719 = (

let uu____14720 = (

let uu____14731 = (

let uu____14732 = (

let uu____14737 = (FStar_SMTEncoding_Util.mkEq ((x), (FStar_SMTEncoding_Term.mk_Term_unit)))
in ((typing_pred), (uu____14737)))
in (FStar_SMTEncoding_Util.mkImp uu____14732))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____14731)))
in (mkForall_fuel uu____14720))
in ((uu____14719), (FStar_Pervasives_Native.Some ("unit inversion")), ("unit_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____14712))
in (uu____14711)::[])
in (uu____14697)::uu____14708))))
in (

let mk_bool = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Bool_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____14779 = (

let uu____14780 = (

let uu____14787 = (

let uu____14788 = (

let uu____14799 = (

let uu____14804 = (

let uu____14807 = (FStar_SMTEncoding_Term.boxBool b)
in (uu____14807)::[])
in (uu____14804)::[])
in (

let uu____14812 = (

let uu____14813 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType uu____14813 tt))
in ((uu____14799), ((bb)::[]), (uu____14812))))
in (FStar_SMTEncoding_Util.mkForall uu____14788))
in ((uu____14787), (FStar_Pervasives_Native.Some ("bool typing")), ("bool_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____14780))
in (

let uu____14834 = (

let uu____14837 = (

let uu____14838 = (

let uu____14845 = (

let uu____14846 = (

let uu____14857 = (

let uu____14858 = (

let uu____14863 = (FStar_SMTEncoding_Term.mk_tester (FStar_Pervasives_Native.fst FStar_SMTEncoding_Term.boxBoolFun) x)
in ((typing_pred), (uu____14863)))
in (FStar_SMTEncoding_Util.mkImp uu____14858))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____14857)))
in (mkForall_fuel uu____14846))
in ((uu____14845), (FStar_Pervasives_Native.Some ("bool inversion")), ("bool_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____14838))
in (uu____14837)::[])
in (uu____14779)::uu____14834))))))
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

let uu____14913 = (

let uu____14914 = (

let uu____14921 = (

let uu____14924 = (

let uu____14927 = (

let uu____14930 = (FStar_SMTEncoding_Term.boxInt a)
in (

let uu____14931 = (

let uu____14934 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____14934)::[])
in (uu____14930)::uu____14931))
in (tt)::uu____14927)
in (tt)::uu____14924)
in (("Prims.Precedes"), (uu____14921)))
in (FStar_SMTEncoding_Util.mkApp uu____14914))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14913))
in (

let precedes_y_x = (

let uu____14938 = (FStar_SMTEncoding_Util.mkApp (("Precedes"), ((y)::(x)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14938))
in (

let uu____14941 = (

let uu____14942 = (

let uu____14949 = (

let uu____14950 = (

let uu____14961 = (

let uu____14966 = (

let uu____14969 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____14969)::[])
in (uu____14966)::[])
in (

let uu____14974 = (

let uu____14975 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType uu____14975 tt))
in ((uu____14961), ((bb)::[]), (uu____14974))))
in (FStar_SMTEncoding_Util.mkForall uu____14950))
in ((uu____14949), (FStar_Pervasives_Native.Some ("int typing")), ("int_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____14942))
in (

let uu____14996 = (

let uu____14999 = (

let uu____15000 = (

let uu____15007 = (

let uu____15008 = (

let uu____15019 = (

let uu____15020 = (

let uu____15025 = (FStar_SMTEncoding_Term.mk_tester (FStar_Pervasives_Native.fst FStar_SMTEncoding_Term.boxIntFun) x)
in ((typing_pred), (uu____15025)))
in (FStar_SMTEncoding_Util.mkImp uu____15020))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____15019)))
in (mkForall_fuel uu____15008))
in ((uu____15007), (FStar_Pervasives_Native.Some ("int inversion")), ("int_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____15000))
in (

let uu____15050 = (

let uu____15053 = (

let uu____15054 = (

let uu____15061 = (

let uu____15062 = (

let uu____15073 = (

let uu____15074 = (

let uu____15079 = (

let uu____15080 = (

let uu____15083 = (

let uu____15086 = (

let uu____15089 = (

let uu____15090 = (

let uu____15095 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____15096 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____15095), (uu____15096))))
in (FStar_SMTEncoding_Util.mkGT uu____15090))
in (

let uu____15097 = (

let uu____15100 = (

let uu____15101 = (

let uu____15106 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____15107 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____15106), (uu____15107))))
in (FStar_SMTEncoding_Util.mkGTE uu____15101))
in (

let uu____15108 = (

let uu____15111 = (

let uu____15112 = (

let uu____15117 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____15118 = (FStar_SMTEncoding_Term.unboxInt x)
in ((uu____15117), (uu____15118))))
in (FStar_SMTEncoding_Util.mkLT uu____15112))
in (uu____15111)::[])
in (uu____15100)::uu____15108))
in (uu____15089)::uu____15097))
in (typing_pred_y)::uu____15086)
in (typing_pred)::uu____15083)
in (FStar_SMTEncoding_Util.mk_and_l uu____15080))
in ((uu____15079), (precedes_y_x)))
in (FStar_SMTEncoding_Util.mkImp uu____15074))
in ((((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[]), ((xx)::(yy)::[]), (uu____15073)))
in (mkForall_fuel uu____15062))
in ((uu____15061), (FStar_Pervasives_Native.Some ("well-founded ordering on nat (alt)")), ("well-founded-ordering-on-nat")))
in (FStar_SMTEncoding_Util.mkAssume uu____15054))
in (uu____15053)::[])
in (uu____14999)::uu____15050))
in (uu____14941)::uu____14996)))))))))))
in (

let mk_str = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.String_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____15164 = (

let uu____15165 = (

let uu____15172 = (

let uu____15173 = (

let uu____15184 = (

let uu____15189 = (

let uu____15192 = (FStar_SMTEncoding_Term.boxString b)
in (uu____15192)::[])
in (uu____15189)::[])
in (

let uu____15197 = (

let uu____15198 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType uu____15198 tt))
in ((uu____15184), ((bb)::[]), (uu____15197))))
in (FStar_SMTEncoding_Util.mkForall uu____15173))
in ((uu____15172), (FStar_Pervasives_Native.Some ("string typing")), ("string_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____15165))
in (

let uu____15219 = (

let uu____15222 = (

let uu____15223 = (

let uu____15230 = (

let uu____15231 = (

let uu____15242 = (

let uu____15243 = (

let uu____15248 = (FStar_SMTEncoding_Term.mk_tester (FStar_Pervasives_Native.fst FStar_SMTEncoding_Term.boxStringFun) x)
in ((typing_pred), (uu____15248)))
in (FStar_SMTEncoding_Util.mkImp uu____15243))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____15242)))
in (mkForall_fuel uu____15231))
in ((uu____15230), (FStar_Pervasives_Native.Some ("string inversion")), ("string_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____15223))
in (uu____15222)::[])
in (uu____15164)::uu____15219))))))
in (

let mk_true_interp = (fun env nm true_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((true_tm)::[])))
in ((FStar_SMTEncoding_Util.mkAssume ((valid), (FStar_Pervasives_Native.Some ("True interpretation")), ("true_interp"))))::[]))
in (

let mk_false_interp = (fun env nm false_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((false_tm)::[])))
in (

let uu____15301 = (

let uu____15302 = (

let uu____15309 = (FStar_SMTEncoding_Util.mkIff ((FStar_SMTEncoding_Util.mkFalse), (valid)))
in ((uu____15309), (FStar_Pervasives_Native.Some ("False interpretation")), ("false_interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15302))
in (uu____15301)::[])))
in (

let mk_and_interp = (fun env conj uu____15321 -> (

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

let uu____15346 = (

let uu____15347 = (

let uu____15354 = (

let uu____15355 = (

let uu____15366 = (

let uu____15367 = (

let uu____15372 = (FStar_SMTEncoding_Util.mkAnd ((valid_a), (valid_b)))
in ((uu____15372), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____15367))
in ((((l_and_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____15366)))
in (FStar_SMTEncoding_Util.mkForall uu____15355))
in ((uu____15354), (FStar_Pervasives_Native.Some ("/\\ interpretation")), ("l_and-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15347))
in (uu____15346)::[]))))))))))
in (

let mk_or_interp = (fun env disj uu____15410 -> (

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

let uu____15435 = (

let uu____15436 = (

let uu____15443 = (

let uu____15444 = (

let uu____15455 = (

let uu____15456 = (

let uu____15461 = (FStar_SMTEncoding_Util.mkOr ((valid_a), (valid_b)))
in ((uu____15461), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____15456))
in ((((l_or_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____15455)))
in (FStar_SMTEncoding_Util.mkForall uu____15444))
in ((uu____15443), (FStar_Pervasives_Native.Some ("\\/ interpretation")), ("l_or-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15436))
in (uu____15435)::[]))))))))))
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

let uu____15524 = (

let uu____15525 = (

let uu____15532 = (

let uu____15533 = (

let uu____15544 = (

let uu____15545 = (

let uu____15550 = (FStar_SMTEncoding_Util.mkEq ((x1), (y1)))
in ((uu____15550), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____15545))
in ((((eq2_x_y)::[])::[]), ((aa)::(xx1)::(yy1)::[]), (uu____15544)))
in (FStar_SMTEncoding_Util.mkForall uu____15533))
in ((uu____15532), (FStar_Pervasives_Native.Some ("Eq2 interpretation")), ("eq2-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15525))
in (uu____15524)::[]))))))))))
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

let uu____15623 = (

let uu____15624 = (

let uu____15631 = (

let uu____15632 = (

let uu____15643 = (

let uu____15644 = (

let uu____15649 = (FStar_SMTEncoding_Util.mkEq ((x1), (y1)))
in ((uu____15649), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____15644))
in ((((eq3_x_y)::[])::[]), ((aa)::(bb)::(xx1)::(yy1)::[]), (uu____15643)))
in (FStar_SMTEncoding_Util.mkForall uu____15632))
in ((uu____15631), (FStar_Pervasives_Native.Some ("Eq3 interpretation")), ("eq3-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15624))
in (uu____15623)::[]))))))))))))
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

let uu____15720 = (

let uu____15721 = (

let uu____15728 = (

let uu____15729 = (

let uu____15740 = (

let uu____15741 = (

let uu____15746 = (FStar_SMTEncoding_Util.mkImp ((valid_a), (valid_b)))
in ((uu____15746), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____15741))
in ((((l_imp_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____15740)))
in (FStar_SMTEncoding_Util.mkForall uu____15729))
in ((uu____15728), (FStar_Pervasives_Native.Some ("==> interpretation")), ("l_imp-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15721))
in (uu____15720)::[]))))))))))
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

let uu____15809 = (

let uu____15810 = (

let uu____15817 = (

let uu____15818 = (

let uu____15829 = (

let uu____15830 = (

let uu____15835 = (FStar_SMTEncoding_Util.mkIff ((valid_a), (valid_b)))
in ((uu____15835), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____15830))
in ((((l_iff_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____15829)))
in (FStar_SMTEncoding_Util.mkForall uu____15818))
in ((uu____15817), (FStar_Pervasives_Native.Some ("<==> interpretation")), ("l_iff-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15810))
in (uu____15809)::[]))))))))))
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

let uu____15887 = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____15887))
in (

let uu____15890 = (

let uu____15891 = (

let uu____15898 = (

let uu____15899 = (

let uu____15910 = (FStar_SMTEncoding_Util.mkIff ((not_valid_a), (valid)))
in ((((l_not_a)::[])::[]), ((aa)::[]), (uu____15910)))
in (FStar_SMTEncoding_Util.mkForall uu____15899))
in ((uu____15898), (FStar_Pervasives_Native.Some ("not interpretation")), ("l_not-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15891))
in (uu____15890)::[])))))))
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

let uu____15970 = (

let uu____15977 = (

let uu____15980 = (FStar_SMTEncoding_Util.mk_ApplyTT b x1)
in (uu____15980)::[])
in (("Valid"), (uu____15977)))
in (FStar_SMTEncoding_Util.mkApp uu____15970))
in (

let uu____15983 = (

let uu____15984 = (

let uu____15991 = (

let uu____15992 = (

let uu____16003 = (

let uu____16004 = (

let uu____16009 = (

let uu____16010 = (

let uu____16021 = (

let uu____16026 = (

let uu____16029 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in (uu____16029)::[])
in (uu____16026)::[])
in (

let uu____16034 = (

let uu____16035 = (

let uu____16040 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in ((uu____16040), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp uu____16035))
in ((uu____16021), ((xx1)::[]), (uu____16034))))
in (FStar_SMTEncoding_Util.mkForall uu____16010))
in ((uu____16009), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____16004))
in ((((l_forall_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____16003)))
in (FStar_SMTEncoding_Util.mkForall uu____15992))
in ((uu____15991), (FStar_Pervasives_Native.Some ("forall interpretation")), ("forall-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15984))
in (uu____15983)::[])))))))))))
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

let uu____16122 = (

let uu____16129 = (

let uu____16132 = (FStar_SMTEncoding_Util.mk_ApplyTT b x1)
in (uu____16132)::[])
in (("Valid"), (uu____16129)))
in (FStar_SMTEncoding_Util.mkApp uu____16122))
in (

let uu____16135 = (

let uu____16136 = (

let uu____16143 = (

let uu____16144 = (

let uu____16155 = (

let uu____16156 = (

let uu____16161 = (

let uu____16162 = (

let uu____16173 = (

let uu____16178 = (

let uu____16181 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in (uu____16181)::[])
in (uu____16178)::[])
in (

let uu____16186 = (

let uu____16187 = (

let uu____16192 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in ((uu____16192), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp uu____16187))
in ((uu____16173), ((xx1)::[]), (uu____16186))))
in (FStar_SMTEncoding_Util.mkExists uu____16162))
in ((uu____16161), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____16156))
in ((((l_exists_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____16155)))
in (FStar_SMTEncoding_Util.mkForall uu____16144))
in ((uu____16143), (FStar_Pervasives_Native.Some ("exists interpretation")), ("exists-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16136))
in (uu____16135)::[])))))))))))
in (

let mk_range_interp = (fun env range tt -> (

let range_ty = (FStar_SMTEncoding_Util.mkApp ((range), ([])))
in (

let uu____16252 = (

let uu____16253 = (

let uu____16260 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_ty)
in (

let uu____16261 = (varops.mk_unique "typing_range_const")
in ((uu____16260), (FStar_Pervasives_Native.Some ("Range_const typing")), (uu____16261))))
in (FStar_SMTEncoding_Util.mkAssume uu____16253))
in (uu____16252)::[])))
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

let uu____16295 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1"))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16295 x1 t))
in (

let uu____16296 = (

let uu____16307 = (FStar_SMTEncoding_Util.mkImp ((hastypeZ), (hastypeS)))
in ((((hastypeZ)::[])::[]), ((xx1)::[]), (uu____16307)))
in (FStar_SMTEncoding_Util.mkForall uu____16296))))
in (

let uu____16330 = (

let uu____16331 = (

let uu____16338 = (

let uu____16339 = (

let uu____16350 = (FStar_SMTEncoding_Util.mkImp ((valid), (body)))
in ((((inversion_t)::[])::[]), ((tt1)::[]), (uu____16350)))
in (FStar_SMTEncoding_Util.mkForall uu____16339))
in ((uu____16338), (FStar_Pervasives_Native.Some ("inversion interpretation")), ("inversion-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16331))
in (uu____16330)::[])))))))))
in (

let prims1 = (((FStar_Parser_Const.unit_lid), (mk_unit)))::(((FStar_Parser_Const.bool_lid), (mk_bool)))::(((FStar_Parser_Const.int_lid), (mk_int)))::(((FStar_Parser_Const.string_lid), (mk_str)))::(((FStar_Parser_Const.true_lid), (mk_true_interp)))::(((FStar_Parser_Const.false_lid), (mk_false_interp)))::(((FStar_Parser_Const.and_lid), (mk_and_interp)))::(((FStar_Parser_Const.or_lid), (mk_or_interp)))::(((FStar_Parser_Const.eq2_lid), (mk_eq2_interp)))::(((FStar_Parser_Const.eq3_lid), (mk_eq3_interp)))::(((FStar_Parser_Const.imp_lid), (mk_imp_interp)))::(((FStar_Parser_Const.iff_lid), (mk_iff_interp)))::(((FStar_Parser_Const.not_lid), (mk_not_interp)))::(((FStar_Parser_Const.forall_lid), (mk_forall_interp)))::(((FStar_Parser_Const.exists_lid), (mk_exists_interp)))::(((FStar_Parser_Const.range_lid), (mk_range_interp)))::(((FStar_Parser_Const.inversion_lid), (mk_inversion_axiom)))::[]
in (fun env t s tt -> (

let uu____16674 = (FStar_Util.find_opt (fun uu____16700 -> (match (uu____16700) with
| (l, uu____16712) -> begin
(FStar_Ident.lid_equals l t)
end)) prims1)
in (match (uu____16674) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (uu____16737, f) -> begin
(f env s tt)
end)))))))))))))))))))))))))


let encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____16776 = (encode_function_type_as_formula t env)
in (match (uu____16776) with
| (form, decls) -> begin
(FStar_List.append decls (((FStar_SMTEncoding_Util.mkAssume ((form), (FStar_Pervasives_Native.Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str))), ((Prims.strcat "lemma_" lid.FStar_Ident.str)))))::[]))
end))))


let encode_free_var : Prims.bool  ->  env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun uninterpreted env fv tt t_norm quals -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____16822 = (((

let uu____16825 = ((FStar_Syntax_Util.is_pure_or_ghost_function t_norm) || (FStar_TypeChecker_Env.is_reifiable_function env.tcenv t_norm))
in (FStar_All.pipe_left Prims.op_Negation uu____16825)) || (FStar_Syntax_Util.is_lemma t_norm)) || uninterpreted)
in (match (uu____16822) with
| true -> begin
(

let uu____16832 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____16832) with
| (vname, vtok, env1) -> begin
(

let arg_sorts = (

let uu____16851 = (

let uu____16852 = (FStar_Syntax_Subst.compress t_norm)
in uu____16852.FStar_Syntax_Syntax.n)
in (match (uu____16851) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____16858) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun uu____16888 -> FStar_SMTEncoding_Term.Term_sort)))
end
| uu____16893 -> begin
[]
end))
in (

let d = FStar_SMTEncoding_Term.DeclFun (((vname), (arg_sorts), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Uninterpreted function symbol for impure function"))))
in (

let dd = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Uninterpreted name for impure function"))))
in (((d)::(dd)::[]), (env1)))))
end))
end
| uu____16906 -> begin
(

let uu____16907 = (prims.is lid)
in (match (uu____16907) with
| true -> begin
(

let vname = (varops.new_fvar lid)
in (

let uu____16915 = (prims.mk lid vname)
in (match (uu____16915) with
| (tok, definition) -> begin
(

let env1 = (push_free_var env lid vname (FStar_Pervasives_Native.Some (tok)))
in ((definition), (env1)))
end)))
end
| uu____16937 -> begin
(

let encode_non_total_function_typ = (Prims.op_disEquality lid.FStar_Ident.nsstr "Prims")
in (

let uu____16939 = (

let uu____16950 = (curried_arrow_formals_comp t_norm)
in (match (uu____16950) with
| (args, comp) -> begin
(

let comp1 = (

let uu____16968 = (FStar_TypeChecker_Env.is_reifiable_comp env.tcenv comp)
in (match (uu____16968) with
| true -> begin
(

let uu____16969 = (FStar_TypeChecker_Env.reify_comp (

let uu___149_16972 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___149_16972.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___149_16972.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___149_16972.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___149_16972.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___149_16972.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___149_16972.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___149_16972.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___149_16972.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___149_16972.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___149_16972.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___149_16972.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___149_16972.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___149_16972.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___149_16972.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___149_16972.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___149_16972.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___149_16972.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___149_16972.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___149_16972.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___149_16972.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___149_16972.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___149_16972.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___149_16972.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___149_16972.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___149_16972.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___149_16972.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___149_16972.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___149_16972.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___149_16972.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___149_16972.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___149_16972.FStar_TypeChecker_Env.tc_hooks}) comp FStar_Syntax_Syntax.U_unknown)
in (FStar_Syntax_Syntax.mk_Total uu____16969))
end
| uu____16973 -> begin
comp
end))
in (match (encode_non_total_function_typ) with
| true -> begin
(

let uu____16984 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp1)
in ((args), (uu____16984)))
end
| uu____16997 -> begin
((args), (((FStar_Pervasives_Native.None), ((FStar_Syntax_Util.comp_result comp1)))))
end))
end))
in (match (uu____16939) with
| (formals, (pre_opt, res_t)) -> begin
(

let uu____17029 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____17029) with
| (vname, vtok, env1) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
end
| uu____17050 -> begin
(FStar_SMTEncoding_Util.mkApp ((vtok), ([])))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun uu___121_17092 -> (match (uu___121_17092) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(

let uu____17096 = (FStar_Util.prefix vars)
in (match (uu____17096) with
| (uu____17117, (xxsym, uu____17119)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____17137 = (

let uu____17138 = (

let uu____17145 = (

let uu____17146 = (

let uu____17157 = (

let uu____17158 = (

let uu____17163 = (

let uu____17164 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____17164))
in ((vapp), (uu____17163)))
in (FStar_SMTEncoding_Util.mkEq uu____17158))
in ((((vapp)::[])::[]), (vars), (uu____17157)))
in (FStar_SMTEncoding_Util.mkForall uu____17146))
in ((uu____17145), (FStar_Pervasives_Native.Some ("Discriminator equation")), ((Prims.strcat "disc_equation_" (escape d.FStar_Ident.str)))))
in (FStar_SMTEncoding_Util.mkAssume uu____17138))
in (uu____17137)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(

let uu____17183 = (FStar_Util.prefix vars)
in (match (uu____17183) with
| (uu____17204, (xxsym, uu____17206)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f1 = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (

let tp_name = (mk_term_projector_name d f1)
in (

let prim_app = (FStar_SMTEncoding_Util.mkApp ((tp_name), ((xx)::[])))
in (

let uu____17229 = (

let uu____17230 = (

let uu____17237 = (

let uu____17238 = (

let uu____17249 = (FStar_SMTEncoding_Util.mkEq ((vapp), (prim_app)))
in ((((vapp)::[])::[]), (vars), (uu____17249)))
in (FStar_SMTEncoding_Util.mkForall uu____17238))
in ((uu____17237), (FStar_Pervasives_Native.Some ("Projector equation")), ((Prims.strcat "proj_equation_" tp_name))))
in (FStar_SMTEncoding_Util.mkAssume uu____17230))
in (uu____17229)::[])))))
end))
end
| uu____17266 -> begin
[]
end)))))
in (

let uu____17267 = (encode_binders FStar_Pervasives_Native.None formals env1)
in (match (uu____17267) with
| (vars, guards, env', decls1, uu____17294) -> begin
(

let uu____17307 = (match (pre_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____17316 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____17316), (decls1)))
end
| FStar_Pervasives_Native.Some (p) -> begin
(

let uu____17318 = (encode_formula p env')
in (match (uu____17318) with
| (g, ds) -> begin
(

let uu____17329 = (FStar_SMTEncoding_Util.mk_and_l ((g)::guards))
in ((uu____17329), ((FStar_List.append decls1 ds))))
end))
end)
in (match (uu____17307) with
| (guard, decls11) -> begin
(

let vtok_app = (mk_Apply vtok_tm vars)
in (

let vapp = (

let uu____17342 = (

let uu____17349 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((vname), (uu____17349)))
in (FStar_SMTEncoding_Util.mkApp uu____17342))
in (

let uu____17358 = (

let vname_decl = (

let uu____17366 = (

let uu____17377 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____17387 -> FStar_SMTEncoding_Term.Term_sort)))
in ((vname), (uu____17377), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____17366))
in (

let uu____17396 = (

let env2 = (

let uu___150_17402 = env1
in {bindings = uu___150_17402.bindings; depth = uu___150_17402.depth; tcenv = uu___150_17402.tcenv; warn = uu___150_17402.warn; cache = uu___150_17402.cache; nolabels = uu___150_17402.nolabels; use_zfuel_name = uu___150_17402.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = uu___150_17402.current_module_name})
in (

let uu____17403 = (

let uu____17404 = (head_normal env2 tt)
in (not (uu____17404)))
in (match (uu____17403) with
| true -> begin
(encode_term_pred FStar_Pervasives_Native.None tt env2 vtok_tm)
end
| uu____17409 -> begin
(encode_term_pred FStar_Pervasives_Native.None t_norm env2 vtok_tm)
end)))
in (match (uu____17396) with
| (tok_typing, decls2) -> begin
(

let tok_typing1 = (match (formals) with
| (uu____17419)::uu____17420 -> begin
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

let uu____17460 = (

let uu____17471 = (FStar_SMTEncoding_Term.mk_NoHoist f tok_typing)
in ((((vtok_app_l)::[])::((vtok_app_r)::[])::[]), ((ff)::[]), (uu____17471)))
in (FStar_SMTEncoding_Util.mkForall uu____17460))
in (FStar_SMTEncoding_Util.mkAssume ((guarded_tok_typing), (FStar_Pervasives_Native.Some ("function token typing")), ((Prims.strcat "function_token_typing_" vname)))))))))
end
| uu____17498 -> begin
(FStar_SMTEncoding_Util.mkAssume ((tok_typing), (FStar_Pervasives_Native.Some ("function token typing")), ((Prims.strcat "function_token_typing_" vname))))
end)
in (

let uu____17501 = (match (formals) with
| [] -> begin
(

let uu____17518 = (

let uu____17519 = (

let uu____17522 = (FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left (fun _0_43 -> FStar_Pervasives_Native.Some (_0_43)) uu____17522))
in (push_free_var env1 lid vname uu____17519))
in (((FStar_List.append decls2 ((tok_typing1)::[]))), (uu____17518)))
end
| uu____17527 -> begin
(

let vtok_decl = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let name_tok_corr = (

let uu____17534 = (

let uu____17541 = (

let uu____17542 = (

let uu____17553 = (FStar_SMTEncoding_Util.mkEq ((vtok_app), (vapp)))
in ((((vtok_app)::[])::((vapp)::[])::[]), (vars), (uu____17553)))
in (FStar_SMTEncoding_Util.mkForall uu____17542))
in ((uu____17541), (FStar_Pervasives_Native.Some ("Name-token correspondence")), ((Prims.strcat "token_correspondence_" vname))))
in (FStar_SMTEncoding_Util.mkAssume uu____17534))
in (((FStar_List.append decls2 ((vtok_decl)::(name_tok_corr)::(tok_typing1)::[]))), (env1))))
end)
in (match (uu____17501) with
| (tok_decl, env2) -> begin
(((vname_decl)::tok_decl), (env2))
end)))
end)))
in (match (uu____17358) with
| (decls2, env2) -> begin
(

let uu____17596 = (

let res_t1 = (FStar_Syntax_Subst.compress res_t)
in (

let uu____17604 = (encode_term res_t1 env')
in (match (uu____17604) with
| (encoded_res_t, decls) -> begin
(

let uu____17617 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in ((encoded_res_t), (uu____17617), (decls)))
end)))
in (match (uu____17596) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (

let uu____17628 = (

let uu____17635 = (

let uu____17636 = (

let uu____17647 = (FStar_SMTEncoding_Util.mkImp ((guard), (ty_pred)))
in ((((vapp)::[])::[]), (vars), (uu____17647)))
in (FStar_SMTEncoding_Util.mkForall uu____17636))
in ((uu____17635), (FStar_Pervasives_Native.Some ("free var typing")), ((Prims.strcat "typing_" vname))))
in (FStar_SMTEncoding_Util.mkAssume uu____17628))
in (

let freshness = (

let uu____17663 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New))
in (match (uu____17663) with
| true -> begin
(

let uu____17668 = (

let uu____17669 = (

let uu____17680 = (FStar_All.pipe_right vars (FStar_List.map FStar_Pervasives_Native.snd))
in (

let uu____17691 = (varops.next_id ())
in ((vname), (uu____17680), (FStar_SMTEncoding_Term.Term_sort), (uu____17691))))
in (FStar_SMTEncoding_Term.fresh_constructor uu____17669))
in (

let uu____17694 = (

let uu____17697 = (pretype_axiom env2 vapp vars)
in (uu____17697)::[])
in (uu____17668)::uu____17694))
end
| uu____17698 -> begin
[]
end))
in (

let g = (

let uu____17702 = (

let uu____17705 = (

let uu____17708 = (

let uu____17711 = (

let uu____17714 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::uu____17714)
in (FStar_List.append freshness uu____17711))
in (FStar_List.append decls3 uu____17708))
in (FStar_List.append decls2 uu____17705))
in (FStar_List.append decls11 uu____17702))
in ((g), (env2)))))
end))
end))))
end))
end))))
end))
end)))
end))
end))))


let declare_top_level_let : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  ((Prims.string * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option) * FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env x t t_norm -> (

let uu____17749 = (try_lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____17749) with
| FStar_Pervasives_Native.None -> begin
(

let uu____17786 = (encode_free_var false env x t t_norm [])
in (match (uu____17786) with
| (decls, env1) -> begin
(

let uu____17813 = (lookup_lid env1 x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____17813) with
| (n1, x', uu____17840) -> begin
((((n1), (x'))), (decls), (env1))
end))
end))
end
| FStar_Pervasives_Native.Some (n1, x1, uu____17861) -> begin
((((n1), (x1))), ([]), (env))
end)))


let encode_top_level_val : Prims.bool  ->  env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun uninterpreted env lid t quals -> (

let tt = (norm env t)
in (

let uu____17921 = (encode_free_var uninterpreted env lid t tt quals)
in (match (uu____17921) with
| (decls, env1) -> begin
(

let uu____17940 = (FStar_Syntax_Util.is_smt_lemma t)
in (match (uu____17940) with
| true -> begin
(

let uu____17947 = (

let uu____17950 = (encode_smt_lemma env1 lid tt)
in (FStar_List.append decls uu____17950))
in ((uu____17947), (env1)))
end
| uu____17955 -> begin
((decls), (env1))
end))
end))))


let encode_top_level_vals : env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____18005 lb -> (match (uu____18005) with
| (decls, env1) -> begin
(

let uu____18025 = (

let uu____18032 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val false env1 uu____18032 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (uu____18025) with
| (decls', env2) -> begin
(((FStar_List.append decls decls')), (env2))
end))
end)) (([]), (env)))))


let is_tactic : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let fstar_tactics_tactic_lid = (FStar_Parser_Const.p2l (("FStar")::("Tactics")::("tactic")::[]))
in (

let uu____18054 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____18054) with
| (hd1, args) -> begin
(

let uu____18091 = (

let uu____18092 = (FStar_Syntax_Util.un_uinst hd1)
in uu____18092.FStar_Syntax_Syntax.n)
in (match (uu____18091) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____18096, c) -> begin
(

let effect_name = (FStar_Syntax_Util.comp_effect_name c)
in (FStar_Util.starts_with "FStar.Tactics" effect_name.FStar_Ident.str))
end
| uu____18115 -> begin
false
end))
end))))


let encode_top_level_let : env_t  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env uu____18140 quals -> (match (uu____18140) with
| (is_rec, bindings) -> begin
(

let eta_expand1 = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let uu____18216 = (FStar_Util.first_N nbinders formals)
in (match (uu____18216) with
| (formals1, extra_formals) -> begin
(

let subst1 = (FStar_List.map2 (fun uu____18297 uu____18298 -> (match (((uu____18297), (uu____18298))) with
| ((formal, uu____18316), (binder, uu____18318)) -> begin
(

let uu____18327 = (

let uu____18334 = (FStar_Syntax_Syntax.bv_to_name binder)
in ((formal), (uu____18334)))
in FStar_Syntax_Syntax.NT (uu____18327))
end)) formals1 binders)
in (

let extra_formals1 = (

let uu____18342 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun uu____18373 -> (match (uu____18373) with
| (x, i) -> begin
(

let uu____18384 = (

let uu___151_18385 = x
in (

let uu____18386 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___151_18385.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___151_18385.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____18386}))
in ((uu____18384), (i)))
end))))
in (FStar_All.pipe_right uu____18342 FStar_Syntax_Util.name_binders))
in (

let body1 = (

let uu____18404 = (

let uu____18405 = (FStar_Syntax_Subst.compress body)
in (

let uu____18406 = (

let uu____18407 = (FStar_Syntax_Util.args_of_binders extra_formals1)
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____18407))
in (FStar_Syntax_Syntax.extend_app_n uu____18405 uu____18406)))
in (uu____18404 FStar_Pervasives_Native.None body.FStar_Syntax_Syntax.pos))
in (((FStar_List.append binders extra_formals1)), (body1)))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (

let get_result_type = (fun c -> (

let uu____18468 = (FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c)
in (match (uu____18468) with
| true -> begin
(FStar_TypeChecker_Env.reify_comp (

let uu___152_18471 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___152_18471.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___152_18471.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___152_18471.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___152_18471.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___152_18471.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___152_18471.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___152_18471.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___152_18471.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___152_18471.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___152_18471.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___152_18471.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___152_18471.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___152_18471.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___152_18471.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___152_18471.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___152_18471.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___152_18471.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___152_18471.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___152_18471.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___152_18471.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___152_18471.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___152_18471.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___152_18471.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___152_18471.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___152_18471.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___152_18471.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___152_18471.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___152_18471.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___152_18471.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___152_18471.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___152_18471.FStar_TypeChecker_Env.tc_hooks}) c FStar_Syntax_Syntax.U_unknown)
end
| uu____18472 -> begin
(FStar_Syntax_Util.comp_result c)
end)))
in (

let rec aux = (fun norm1 t_norm1 -> (

let uu____18504 = (FStar_Syntax_Util.abs_formals e)
in (match (uu____18504) with
| (binders, body, lopt) -> begin
(match (binders) with
| (uu____18568)::uu____18569 -> begin
(

let uu____18584 = (

let uu____18585 = (

let uu____18588 = (FStar_Syntax_Subst.compress t_norm1)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____18588))
in uu____18585.FStar_Syntax_Syntax.n)
in (match (uu____18584) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____18631 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____18631) with
| (formals1, c1) -> begin
(

let nformals = (FStar_List.length formals1)
in (

let nbinders = (FStar_List.length binders)
in (

let tres = (get_result_type c1)
in (

let uu____18673 = ((nformals < nbinders) && (FStar_Syntax_Util.is_total_comp c1))
in (match (uu____18673) with
| true -> begin
(

let uu____18708 = (FStar_Util.first_N nformals binders)
in (match (uu____18708) with
| (bs0, rest) -> begin
(

let c2 = (

let subst1 = (FStar_List.map2 (fun uu____18802 uu____18803 -> (match (((uu____18802), (uu____18803))) with
| ((x, uu____18821), (b, uu____18823)) -> begin
(

let uu____18832 = (

let uu____18839 = (FStar_Syntax_Syntax.bv_to_name b)
in ((x), (uu____18839)))
in FStar_Syntax_Syntax.NT (uu____18832))
end)) formals1 bs0)
in (FStar_Syntax_Subst.subst_comp subst1 c1))
in (

let body1 = (FStar_Syntax_Util.abs rest body lopt)
in (

let uu____18841 = (

let uu____18862 = (get_result_type c2)
in ((bs0), (body1), (bs0), (uu____18862)))
in ((uu____18841), (false)))))
end))
end
| uu____18895 -> begin
(match ((nformals > nbinders)) with
| true -> begin
(

let uu____18930 = (eta_expand1 binders formals1 body tres)
in (match (uu____18930) with
| (binders1, body1) -> begin
((((binders1), (body1), (formals1), (tres))), (false))
end))
end
| uu____19009 -> begin
((((binders), (body), (formals1), (tres))), (false))
end)
end)))))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____19019) -> begin
(

let uu____19024 = (

let uu____19045 = (aux norm1 x.FStar_Syntax_Syntax.sort)
in (FStar_Pervasives_Native.fst uu____19045))
in ((uu____19024), (true)))
end
| uu____19110 when (not (norm1)) -> begin
(

let t_norm2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm1)
in (aux true t_norm2))
end
| uu____19112 -> begin
(

let uu____19113 = (

let uu____19114 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____19115 = (FStar_Syntax_Print.term_to_string t_norm1)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str uu____19114 uu____19115)))
in (failwith uu____19113))
end))
end
| uu____19140 -> begin
(

let uu____19141 = (

let uu____19142 = (FStar_Syntax_Subst.compress t_norm1)
in uu____19142.FStar_Syntax_Syntax.n)
in (match (uu____19141) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____19187 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____19187) with
| (formals1, c1) -> begin
(

let tres = (get_result_type c1)
in (

let uu____19219 = (eta_expand1 [] formals1 e tres)
in (match (uu____19219) with
| (binders1, body1) -> begin
((((binders1), (body1), (formals1), (tres))), (false))
end)))
end))
end
| uu____19302 -> begin
(((([]), (e), ([]), (t_norm1))), (false))
end))
end)
end)))
in (aux false t_norm))))
in (FStar_All.try_with (fun uu___154_19351 -> (match (()) with
| () -> begin
(

let uu____19358 = (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> ((FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))))
in (match (uu____19358) with
| true -> begin
(encode_top_level_vals env bindings quals)
end
| uu____19369 -> begin
(

let uu____19370 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____19464 lb -> (match (uu____19464) with
| (toks, typs, decls, env1) -> begin
((

let uu____19559 = (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp)
in (match (uu____19559) with
| true -> begin
(FStar_Exn.raise Let_rec_unencodeable)
end
| uu____19560 -> begin
()
end));
(

let t_norm = (whnf env1 lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____19562 = (

let uu____19577 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env1 uu____19577 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (uu____19562) with
| (tok, decl, env2) -> begin
(

let uu____19623 = (

let uu____19636 = (

let uu____19647 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in ((uu____19647), (tok)))
in (uu____19636)::toks)
in ((uu____19623), ((t_norm)::typs), ((decl)::decls), (env2)))
end)));
)
end)) (([]), ([]), ([]), (env))))
in (match (uu____19370) with
| (toks, typs, decls, env1) -> begin
(

let toks1 = (FStar_List.rev toks)
in (

let decls1 = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (

let typs1 = (FStar_List.rev typs)
in (

let mk_app1 = (fun curry f ftok vars -> (match (vars) with
| [] -> begin
(FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
end
| uu____19830 -> begin
(match (curry) with
| true -> begin
(match (ftok) with
| FStar_Pervasives_Native.Some (ftok1) -> begin
(mk_Apply ftok1 vars)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____19838 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply uu____19838 vars))
end)
end
| uu____19839 -> begin
(

let uu____19840 = (

let uu____19847 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (uu____19847)))
in (FStar_SMTEncoding_Util.mkApp uu____19840))
end)
end))
in (

let encode_non_rec_lbdef = (fun bindings1 typs2 toks2 env2 -> (match (((bindings1), (typs2), (toks2))) with
| (({FStar_Syntax_Syntax.lbname = uu____19929; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____19931; FStar_Syntax_Syntax.lbeff = uu____19932; FStar_Syntax_Syntax.lbdef = e})::[], (t_norm)::[], ((flid_fv, (f, ftok)))::[]) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____19995 = (

let uu____20002 = (FStar_TypeChecker_Env.open_universes_in env2.tcenv uvs ((e)::(t_norm)::[]))
in (match (uu____20002) with
| (tcenv', uu____20020, e_t) -> begin
(

let uu____20026 = (match (e_t) with
| (e1)::(t_norm1)::[] -> begin
((e1), (t_norm1))
end
| uu____20037 -> begin
(failwith "Impossible")
end)
in (match (uu____20026) with
| (e1, t_norm1) -> begin
(((

let uu___155_20053 = env2
in {bindings = uu___155_20053.bindings; depth = uu___155_20053.depth; tcenv = tcenv'; warn = uu___155_20053.warn; cache = uu___155_20053.cache; nolabels = uu___155_20053.nolabels; use_zfuel_name = uu___155_20053.use_zfuel_name; encode_non_total_function_typ = uu___155_20053.encode_non_total_function_typ; current_module_name = uu___155_20053.current_module_name})), (e1), (t_norm1))
end))
end))
in (match (uu____19995) with
| (env', e1, t_norm1) -> begin
(

let uu____20063 = (destruct_bound_function flid t_norm1 e1)
in (match (uu____20063) with
| ((binders, body, uu____20084, uu____20085), curry) -> begin
((

let uu____20096 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____20096) with
| true -> begin
(

let uu____20097 = (FStar_Syntax_Print.binders_to_string ", " binders)
in (

let uu____20098 = (FStar_Syntax_Print.term_to_string body)
in (FStar_Util.print2 "Encoding let : binders=[%s], body=%s\n" uu____20097 uu____20098)))
end
| uu____20099 -> begin
()
end));
(

let uu____20100 = (encode_binders FStar_Pervasives_Native.None binders env')
in (match (uu____20100) with
| (vars, guards, env'1, binder_decls, uu____20127) -> begin
(

let body1 = (

let uu____20141 = (FStar_TypeChecker_Env.is_reifiable_function env'1.tcenv t_norm1)
in (match (uu____20141) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env'1.tcenv body)
end
| uu____20142 -> begin
body
end))
in (

let app = (mk_app1 curry f ftok vars)
in (

let uu____20144 = (

let uu____20153 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic))
in (match (uu____20153) with
| true -> begin
(

let uu____20164 = (FStar_SMTEncoding_Term.mk_Valid app)
in (

let uu____20165 = (encode_formula body1 env'1)
in ((uu____20164), (uu____20165))))
end
| uu____20174 -> begin
(

let uu____20175 = (encode_term body1 env'1)
in ((app), (uu____20175)))
end))
in (match (uu____20144) with
| (app1, (body2, decls2)) -> begin
(

let eqn = (

let uu____20198 = (

let uu____20205 = (

let uu____20206 = (

let uu____20217 = (FStar_SMTEncoding_Util.mkEq ((app1), (body2)))
in ((((app1)::[])::[]), (vars), (uu____20217)))
in (FStar_SMTEncoding_Util.mkForall uu____20206))
in (

let uu____20228 = (

let uu____20231 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in FStar_Pervasives_Native.Some (uu____20231))
in ((uu____20205), (uu____20228), ((Prims.strcat "equation_" f)))))
in (FStar_SMTEncoding_Util.mkAssume uu____20198))
in (

let uu____20234 = (

let uu____20237 = (

let uu____20240 = (

let uu____20243 = (

let uu____20246 = (primitive_type_axioms env2.tcenv flid f app1)
in (FStar_List.append ((eqn)::[]) uu____20246))
in (FStar_List.append decls2 uu____20243))
in (FStar_List.append binder_decls uu____20240))
in (FStar_List.append decls1 uu____20237))
in ((uu____20234), (env2))))
end))))
end));
)
end))
end)))
end
| uu____20251 -> begin
(failwith "Impossible")
end))
in (

let encode_rec_lbdefs = (fun bindings1 typs2 toks2 env2 -> (

let fuel = (

let uu____20336 = (varops.fresh "fuel")
in ((uu____20336), (FStar_SMTEncoding_Term.Fuel_sort)))
in (

let fuel_tm = (FStar_SMTEncoding_Util.mkFreeV fuel)
in (

let env0 = env2
in (

let uu____20339 = (FStar_All.pipe_right toks2 (FStar_List.fold_left (fun uu____20427 uu____20428 -> (match (((uu____20427), (uu____20428))) with
| ((gtoks, env3), (flid_fv, (f, ftok))) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let g = (

let uu____20576 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented")
in (varops.new_fvar uu____20576))
in (

let gtok = (

let uu____20578 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented_token")
in (varops.new_fvar uu____20578))
in (

let env4 = (

let uu____20580 = (

let uu____20583 = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::[])))
in (FStar_All.pipe_left (fun _0_44 -> FStar_Pervasives_Native.Some (_0_44)) uu____20583))
in (push_free_var env3 flid gtok uu____20580))
in (((((flid), (f), (ftok), (g), (gtok)))::gtoks), (env4))))))
end)) (([]), (env2))))
in (match (uu____20339) with
| (gtoks, env3) -> begin
(

let gtoks1 = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env01 uu____20739 t_norm uu____20741 -> (match (((uu____20739), (uu____20741))) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = lbn; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____20785; FStar_Syntax_Syntax.lbeff = uu____20786; FStar_Syntax_Syntax.lbdef = e}) -> begin
(

let uu____20814 = (

let uu____20821 = (FStar_TypeChecker_Env.open_universes_in env3.tcenv uvs ((e)::(t_norm)::[]))
in (match (uu____20821) with
| (tcenv', uu____20843, e_t) -> begin
(

let uu____20849 = (match (e_t) with
| (e1)::(t_norm1)::[] -> begin
((e1), (t_norm1))
end
| uu____20860 -> begin
(failwith "Impossible")
end)
in (match (uu____20849) with
| (e1, t_norm1) -> begin
(((

let uu___156_20876 = env3
in {bindings = uu___156_20876.bindings; depth = uu___156_20876.depth; tcenv = tcenv'; warn = uu___156_20876.warn; cache = uu___156_20876.cache; nolabels = uu___156_20876.nolabels; use_zfuel_name = uu___156_20876.use_zfuel_name; encode_non_total_function_typ = uu___156_20876.encode_non_total_function_typ; current_module_name = uu___156_20876.current_module_name})), (e1), (t_norm1))
end))
end))
in (match (uu____20814) with
| (env', e1, t_norm1) -> begin
((

let uu____20891 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env01.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____20891) with
| true -> begin
(

let uu____20892 = (FStar_Syntax_Print.lbname_to_string lbn)
in (

let uu____20893 = (FStar_Syntax_Print.term_to_string t_norm1)
in (

let uu____20894 = (FStar_Syntax_Print.term_to_string e1)
in (FStar_Util.print3 "Encoding let rec %s : %s = %s\n" uu____20892 uu____20893 uu____20894))))
end
| uu____20895 -> begin
()
end));
(

let uu____20896 = (destruct_bound_function flid t_norm1 e1)
in (match (uu____20896) with
| ((binders, body, formals, tres), curry) -> begin
((

let uu____20933 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env01.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____20933) with
| true -> begin
(

let uu____20934 = (FStar_Syntax_Print.binders_to_string ", " binders)
in (

let uu____20935 = (FStar_Syntax_Print.term_to_string body)
in (

let uu____20936 = (FStar_Syntax_Print.binders_to_string ", " formals)
in (

let uu____20937 = (FStar_Syntax_Print.term_to_string tres)
in (FStar_Util.print4 "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n" uu____20934 uu____20935 uu____20936 uu____20937)))))
end
| uu____20938 -> begin
()
end));
(match (curry) with
| true -> begin
(failwith "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type")
end
| uu____20940 -> begin
()
end);
(

let uu____20941 = (encode_binders FStar_Pervasives_Native.None binders env')
in (match (uu____20941) with
| (vars, guards, env'1, binder_decls, uu____20972) -> begin
(

let decl_g = (

let uu____20986 = (

let uu____20997 = (

let uu____21000 = (FStar_List.map FStar_Pervasives_Native.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::uu____21000)
in ((g), (uu____20997), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Fuel-instrumented function name"))))
in FStar_SMTEncoding_Term.DeclFun (uu____20986))
in (

let env02 = (push_zfuel_name env01 flid g)
in (

let decl_g_tok = FStar_SMTEncoding_Term.DeclFun (((gtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Token for fuel-instrumented partial applications"))))
in (

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let app = (

let uu____21025 = (

let uu____21032 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (uu____21032)))
in (FStar_SMTEncoding_Util.mkApp uu____21025))
in (

let gsapp = (

let uu____21042 = (

let uu____21049 = (

let uu____21052 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (uu____21052)::vars_tm)
in ((g), (uu____21049)))
in (FStar_SMTEncoding_Util.mkApp uu____21042))
in (

let gmax = (

let uu____21058 = (

let uu____21065 = (

let uu____21068 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (uu____21068)::vars_tm)
in ((g), (uu____21065)))
in (FStar_SMTEncoding_Util.mkApp uu____21058))
in (

let body1 = (

let uu____21074 = (FStar_TypeChecker_Env.is_reifiable_function env'1.tcenv t_norm1)
in (match (uu____21074) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env'1.tcenv body)
end
| uu____21075 -> begin
body
end))
in (

let uu____21076 = (encode_term body1 env'1)
in (match (uu____21076) with
| (body_tm, decls2) -> begin
(

let eqn_g = (

let uu____21094 = (

let uu____21101 = (

let uu____21102 = (

let uu____21117 = (FStar_SMTEncoding_Util.mkEq ((gsapp), (body_tm)))
in ((((gsapp)::[])::[]), (FStar_Pervasives_Native.Some ((Prims.parse_int "0"))), ((fuel)::vars), (uu____21117)))
in (FStar_SMTEncoding_Util.mkForall' uu____21102))
in (

let uu____21138 = (

let uu____21141 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in FStar_Pervasives_Native.Some (uu____21141))
in ((uu____21101), (uu____21138), ((Prims.strcat "equation_with_fuel_" g)))))
in (FStar_SMTEncoding_Util.mkAssume uu____21094))
in (

let eqn_f = (

let uu____21145 = (

let uu____21152 = (

let uu____21153 = (

let uu____21164 = (FStar_SMTEncoding_Util.mkEq ((app), (gmax)))
in ((((app)::[])::[]), (vars), (uu____21164)))
in (FStar_SMTEncoding_Util.mkForall uu____21153))
in ((uu____21152), (FStar_Pervasives_Native.Some ("Correspondence of recursive function to instrumented version")), ((Prims.strcat "@fuel_correspondence_" g))))
in (FStar_SMTEncoding_Util.mkAssume uu____21145))
in (

let eqn_g' = (

let uu____21178 = (

let uu____21185 = (

let uu____21186 = (

let uu____21197 = (

let uu____21198 = (

let uu____21203 = (

let uu____21204 = (

let uu____21211 = (

let uu____21214 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "0"))
in (uu____21214)::vars_tm)
in ((g), (uu____21211)))
in (FStar_SMTEncoding_Util.mkApp uu____21204))
in ((gsapp), (uu____21203)))
in (FStar_SMTEncoding_Util.mkEq uu____21198))
in ((((gsapp)::[])::[]), ((fuel)::vars), (uu____21197)))
in (FStar_SMTEncoding_Util.mkForall uu____21186))
in ((uu____21185), (FStar_Pervasives_Native.Some ("Fuel irrelevance")), ((Prims.strcat "@fuel_irrelevance_" g))))
in (FStar_SMTEncoding_Util.mkAssume uu____21178))
in (

let uu____21237 = (

let uu____21246 = (encode_binders FStar_Pervasives_Native.None formals env02)
in (match (uu____21246) with
| (vars1, v_guards, env4, binder_decls1, uu____21275) -> begin
(

let vars_tm1 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars1)
in (

let gapp = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::vars_tm1)))
in (

let tok_corr = (

let tok_app = (

let uu____21300 = (FStar_SMTEncoding_Util.mkFreeV ((gtok), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply uu____21300 ((fuel)::vars1)))
in (

let uu____21305 = (

let uu____21312 = (

let uu____21313 = (

let uu____21324 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (gapp)))
in ((((tok_app)::[])::[]), ((fuel)::vars1), (uu____21324)))
in (FStar_SMTEncoding_Util.mkForall uu____21313))
in ((uu____21312), (FStar_Pervasives_Native.Some ("Fuel token correspondence")), ((Prims.strcat "fuel_token_correspondence_" gtok))))
in (FStar_SMTEncoding_Util.mkAssume uu____21305)))
in (

let uu____21345 = (

let uu____21352 = (encode_term_pred FStar_Pervasives_Native.None tres env4 gapp)
in (match (uu____21352) with
| (g_typing, d3) -> begin
(

let uu____21365 = (

let uu____21368 = (

let uu____21369 = (

let uu____21376 = (

let uu____21377 = (

let uu____21388 = (

let uu____21389 = (

let uu____21394 = (FStar_SMTEncoding_Util.mk_and_l v_guards)
in ((uu____21394), (g_typing)))
in (FStar_SMTEncoding_Util.mkImp uu____21389))
in ((((gapp)::[])::[]), ((fuel)::vars1), (uu____21388)))
in (FStar_SMTEncoding_Util.mkForall uu____21377))
in ((uu____21376), (FStar_Pervasives_Native.Some ("Typing correspondence of token to term")), ((Prims.strcat "token_correspondence_" g))))
in (FStar_SMTEncoding_Util.mkAssume uu____21369))
in (uu____21368)::[])
in ((d3), (uu____21365)))
end))
in (match (uu____21345) with
| (aux_decls, typing_corr) -> begin
(((FStar_List.append binder_decls1 aux_decls)), ((FStar_List.append typing_corr ((tok_corr)::[]))))
end)))))
end))
in (match (uu____21237) with
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

let uu____21459 = (

let uu____21472 = (FStar_List.zip3 gtoks1 typs2 bindings1)
in (FStar_List.fold_left (fun uu____21551 uu____21552 -> (match (((uu____21551), (uu____21552))) with
| ((decls2, eqns, env01), (gtok, ty, lb)) -> begin
(

let uu____21707 = (encode_one_binding env01 gtok ty lb)
in (match (uu____21707) with
| (decls', eqns', env02) -> begin
(((decls')::decls2), ((FStar_List.append eqns' eqns)), (env02))
end))
end)) (((decls1)::[]), ([]), (env0)) uu____21472))
in (match (uu____21459) with
| (decls2, eqns, env01) -> begin
(

let uu____21780 = (

let isDeclFun = (fun uu___122_21792 -> (match (uu___122_21792) with
| FStar_SMTEncoding_Term.DeclFun (uu____21793) -> begin
true
end
| uu____21804 -> begin
false
end))
in (

let uu____21805 = (FStar_All.pipe_right decls2 FStar_List.flatten)
in (FStar_All.pipe_right uu____21805 (FStar_List.partition isDeclFun))))
in (match (uu____21780) with
| (prefix_decls, rest) -> begin
(

let eqns1 = (FStar_List.rev eqns)
in (((FStar_List.append prefix_decls (FStar_List.append rest eqns1))), (env01)))
end))
end))))
end))))))
in (

let uu____21845 = ((FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___123_21849 -> (match (uu___123_21849) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| uu____21850 -> begin
false
end)))) || (FStar_All.pipe_right typs1 (FStar_Util.for_some (fun t -> (

let uu____21856 = ((FStar_Syntax_Util.is_pure_or_ghost_function t) || (FStar_TypeChecker_Env.is_reifiable_function env1.tcenv t))
in (FStar_All.pipe_left Prims.op_Negation uu____21856))))))
in (match (uu____21845) with
| true -> begin
((decls1), (env1))
end
| uu____21865 -> begin
(FStar_All.try_with (fun uu___158_21873 -> (match (()) with
| () -> begin
(match ((not (is_rec))) with
| true -> begin
(encode_non_rec_lbdef bindings typs1 toks1 env1)
end
| uu____21886 -> begin
(encode_rec_lbdefs bindings typs1 toks1 env1)
end)
end)) (fun uu___157_21888 -> (match (uu___157_21888) with
| Inner_let_rec -> begin
((decls1), (env1))
end)))
end))))))))
end))
end))
end)) (fun uu___153_21900 -> (match (uu___153_21900) with
| Let_rec_unencodeable -> begin
(

let msg = (

let uu____21908 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right uu____21908 (FStar_String.concat " and ")))
in (

let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in (((decl)::[]), (env))))
end)))))
end))


let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let nm = (

let uu____21957 = (FStar_Syntax_Util.lid_of_sigelt se)
in (match (uu____21957) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (l) -> begin
l.FStar_Ident.str
end))
in (

let uu____21961 = (encode_sigelt' env se)
in (match (uu____21961) with
| (g, env1) -> begin
(

let g1 = (match (g) with
| [] -> begin
(

let uu____21977 = (

let uu____21978 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (uu____21978))
in (uu____21977)::[])
end
| uu____21979 -> begin
(

let uu____21980 = (

let uu____21983 = (

let uu____21984 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____21984))
in (uu____21983)::g)
in (

let uu____21985 = (

let uu____21988 = (

let uu____21989 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____21989))
in (uu____21988)::[])
in (FStar_List.append uu____21980 uu____21985)))
end)
in ((g1), (env1)))
end))))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let is_opaque_to_smt = (fun t -> (

let uu____22002 = (

let uu____22003 = (FStar_Syntax_Subst.compress t)
in uu____22003.FStar_Syntax_Syntax.n)
in (match (uu____22002) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____22007)) -> begin
(Prims.op_Equality s "opaque_to_smt")
end
| uu____22008 -> begin
false
end)))
in (

let is_uninterpreted_by_smt = (fun t -> (

let uu____22013 = (

let uu____22014 = (FStar_Syntax_Subst.compress t)
in uu____22014.FStar_Syntax_Syntax.n)
in (match (uu____22013) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____22018)) -> begin
(Prims.op_Equality s "uninterpreted_by_smt")
end
| uu____22019 -> begin
false
end)))
in (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____22024) -> begin
(failwith "impossible -- removed by tc.fs")
end
| FStar_Syntax_Syntax.Sig_pragma (uu____22029) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_main (uu____22032) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____22035) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____22050) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(

let uu____22054 = (

let uu____22055 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right uu____22055 Prims.op_Negation))
in (match (uu____22054) with
| true -> begin
(([]), (env))
end
| uu____22064 -> begin
(

let close_effect_params = (fun tm -> (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
tm
end
| uu____22081 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((ed.FStar_Syntax_Syntax.binders), (tm), (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[]))))))) FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)
end))
in (

let encode_action = (fun env1 a -> (

let uu____22101 = (new_term_constant_and_tok_from_lid env1 a.FStar_Syntax_Syntax.action_name)
in (match (uu____22101) with
| (aname, atok, env2) -> begin
(

let uu____22117 = (FStar_Syntax_Util.arrow_formals_comp a.FStar_Syntax_Syntax.action_typ)
in (match (uu____22117) with
| (formals, uu____22135) -> begin
(

let uu____22148 = (

let uu____22153 = (close_effect_params a.FStar_Syntax_Syntax.action_defn)
in (encode_term uu____22153 env2))
in (match (uu____22148) with
| (tm, decls) -> begin
(

let a_decls = (

let uu____22165 = (

let uu____22166 = (

let uu____22177 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____22193 -> FStar_SMTEncoding_Term.Term_sort)))
in ((aname), (uu____22177), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Action"))))
in FStar_SMTEncoding_Term.DeclFun (uu____22166))
in (uu____22165)::(FStar_SMTEncoding_Term.DeclFun (((atok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Action token")))))::[])
in (

let uu____22206 = (

let aux = (fun uu____22258 uu____22259 -> (match (((uu____22258), (uu____22259))) with
| ((bv, uu____22311), (env3, acc_sorts, acc)) -> begin
(

let uu____22349 = (gen_term_var env3 bv)
in (match (uu____22349) with
| (xxsym, xx, env4) -> begin
((env4), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::acc_sorts), ((xx)::acc))
end))
end))
in (FStar_List.fold_right aux formals ((env2), ([]), ([]))))
in (match (uu____22206) with
| (uu____22421, xs_sorts, xs) -> begin
(

let app = (FStar_SMTEncoding_Util.mkApp ((aname), (xs)))
in (

let a_eq = (

let uu____22444 = (

let uu____22451 = (

let uu____22452 = (

let uu____22463 = (

let uu____22464 = (

let uu____22469 = (mk_Apply tm xs_sorts)
in ((app), (uu____22469)))
in (FStar_SMTEncoding_Util.mkEq uu____22464))
in ((((app)::[])::[]), (xs_sorts), (uu____22463)))
in (FStar_SMTEncoding_Util.mkForall uu____22452))
in ((uu____22451), (FStar_Pervasives_Native.Some ("Action equality")), ((Prims.strcat aname "_equality"))))
in (FStar_SMTEncoding_Util.mkAssume uu____22444))
in (

let tok_correspondence = (

let tok_term = (FStar_SMTEncoding_Util.mkFreeV ((atok), (FStar_SMTEncoding_Term.Term_sort)))
in (

let tok_app = (mk_Apply tok_term xs_sorts)
in (

let uu____22489 = (

let uu____22496 = (

let uu____22497 = (

let uu____22508 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (app)))
in ((((tok_app)::[])::[]), (xs_sorts), (uu____22508)))
in (FStar_SMTEncoding_Util.mkForall uu____22497))
in ((uu____22496), (FStar_Pervasives_Native.Some ("Action token correspondence")), ((Prims.strcat aname "_token_correspondence"))))
in (FStar_SMTEncoding_Util.mkAssume uu____22489))))
in ((env2), ((FStar_List.append decls (FStar_List.append a_decls ((a_eq)::(tok_correspondence)::[]))))))))
end)))
end))
end))
end)))
in (

let uu____22527 = (FStar_Util.fold_map encode_action env ed.FStar_Syntax_Syntax.actions)
in (match (uu____22527) with
| (env1, decls2) -> begin
(((FStar_List.flatten decls2)), (env1))
end))))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____22555, uu____22556) when (FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid) -> begin
(

let uu____22557 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____22557) with
| (tname, ttok, env1) -> begin
(([]), (env1))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____22574, t) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let will_encode_definition = (

let uu____22580 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___124_22584 -> (match (uu___124_22584) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.Projector (uu____22585) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____22590) -> begin
true
end
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| uu____22591 -> begin
false
end))))
in (not (uu____22580)))
in (match (will_encode_definition) with
| true -> begin
(([]), (env))
end
| uu____22598 -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____22600 = (

let uu____22607 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs (FStar_Util.for_some is_uninterpreted_by_smt))
in (encode_top_level_val uu____22607 env fv t quals))
in (match (uu____22600) with
| (decls, env1) -> begin
(

let tname = lid.FStar_Ident.str
in (

let tsym = (FStar_SMTEncoding_Util.mkFreeV ((tname), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____22622 = (

let uu____22625 = (primitive_type_axioms env1.tcenv lid tname tsym)
in (FStar_List.append decls uu____22625))
in ((uu____22622), (env1)))))
end)))
end)))
end
| FStar_Syntax_Syntax.Sig_assume (l, us, f) -> begin
(

let uu____22633 = (FStar_Syntax_Subst.open_univ_vars us f)
in (match (uu____22633) with
| (uu____22642, f1) -> begin
(

let uu____22644 = (encode_formula f1 env)
in (match (uu____22644) with
| (f2, decls) -> begin
(

let g = (

let uu____22658 = (

let uu____22659 = (

let uu____22666 = (

let uu____22669 = (

let uu____22670 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" uu____22670))
in FStar_Pervasives_Native.Some (uu____22669))
in (

let uu____22671 = (varops.mk_unique (Prims.strcat "assumption_" l.FStar_Ident.str))
in ((f2), (uu____22666), (uu____22671))))
in (FStar_SMTEncoding_Util.mkAssume uu____22659))
in (uu____22658)::[])
in (((FStar_List.append decls g)), (env)))
end))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____22677) when ((FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) || (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs (FStar_Util.for_some is_opaque_to_smt))) -> begin
(

let attrs = se.FStar_Syntax_Syntax.sigattrs
in (

let uu____22689 = (FStar_Util.fold_map (fun env1 lb -> (

let lid = (

let uu____22707 = (

let uu____22710 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____22710.FStar_Syntax_Syntax.fv_name)
in uu____22707.FStar_Syntax_Syntax.v)
in (

let uu____22711 = (

let uu____22712 = (FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone uu____22712))
in (match (uu____22711) with
| true -> begin
(

let val_decl = (

let uu___159_22740 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = uu___159_22740.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Irreducible)::se.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___159_22740.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___159_22740.FStar_Syntax_Syntax.sigattrs})
in (

let uu____22745 = (encode_sigelt' env1 val_decl)
in (match (uu____22745) with
| (decls, env2) -> begin
((env2), (decls))
end)))
end
| uu____22756 -> begin
((env1), ([]))
end)))) env (FStar_Pervasives_Native.snd lbs))
in (match (uu____22689) with
| (env1, decls) -> begin
(((FStar_List.flatten decls)), (env1))
end)))
end
| FStar_Syntax_Syntax.Sig_let ((uu____22773, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t1); FStar_Syntax_Syntax.lbunivs = uu____22775; FStar_Syntax_Syntax.lbtyp = uu____22776; FStar_Syntax_Syntax.lbeff = uu____22777; FStar_Syntax_Syntax.lbdef = uu____22778})::[]), uu____22779) when (FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid) -> begin
(

let uu____22798 = (new_term_constant_and_tok_from_lid env b2t1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____22798) with
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

let uu____22827 = (

let uu____22830 = (

let uu____22831 = (

let uu____22838 = (

let uu____22839 = (

let uu____22850 = (

let uu____22851 = (

let uu____22856 = (FStar_SMTEncoding_Util.mkApp (((FStar_Pervasives_Native.snd FStar_SMTEncoding_Term.boxBoolFun)), ((x)::[])))
in ((valid_b2t_x), (uu____22856)))
in (FStar_SMTEncoding_Util.mkEq uu____22851))
in ((((b2t_x)::[])::[]), ((xx)::[]), (uu____22850)))
in (FStar_SMTEncoding_Util.mkForall uu____22839))
in ((uu____22838), (FStar_Pervasives_Native.Some ("b2t def")), ("b2t_def")))
in (FStar_SMTEncoding_Util.mkAssume uu____22831))
in (uu____22830)::[])
in (FStar_SMTEncoding_Term.DeclFun (((tname), ((FStar_SMTEncoding_Term.Term_sort)::[]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None))))::uu____22827)
in ((decls), (env1)))))))
end))
end
| FStar_Syntax_Syntax.Sig_let (uu____22889, uu____22890) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___125_22899 -> (match (uu___125_22899) with
| FStar_Syntax_Syntax.Discriminator (uu____22900) -> begin
true
end
| uu____22901 -> begin
false
end)))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let (uu____22904, lids) when ((FStar_All.pipe_right lids (FStar_Util.for_some (fun l -> (

let uu____22915 = (

let uu____22916 = (FStar_List.hd l.FStar_Ident.ns)
in uu____22916.FStar_Ident.idText)
in (Prims.op_Equality uu____22915 "Prims"))))) && (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___126_22920 -> (match (uu___126_22920) with
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
true
end
| uu____22921 -> begin
false
end))))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____22925) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___127_22942 -> (match (uu___127_22942) with
| FStar_Syntax_Syntax.Projector (uu____22943) -> begin
true
end
| uu____22948 -> begin
false
end)))) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____22951 = (try_lookup_free_var env l)
in (match (uu____22951) with
| FStar_Pervasives_Native.Some (uu____22958) -> begin
(([]), (env))
end
| FStar_Pervasives_Native.None -> begin
(

let se1 = (

let uu___160_22962 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l); FStar_Syntax_Syntax.sigquals = uu___160_22962.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___160_22962.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___160_22962.FStar_Syntax_Syntax.sigattrs})
in (encode_sigelt env se1))
end))))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), uu____22969) -> begin
(encode_top_level_let env ((is_rec), (bindings)) se.FStar_Syntax_Syntax.sigquals)
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____22987) -> begin
(

let uu____22996 = (encode_sigelts env ses)
in (match (uu____22996) with
| (g, env1) -> begin
(

let uu____23013 = (FStar_All.pipe_right g (FStar_List.partition (fun uu___128_23036 -> (match (uu___128_23036) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.assumption_term = uu____23037; FStar_SMTEncoding_Term.assumption_caption = FStar_Pervasives_Native.Some ("inversion axiom"); FStar_SMTEncoding_Term.assumption_name = uu____23038; FStar_SMTEncoding_Term.assumption_fact_ids = uu____23039}) -> begin
false
end
| uu____23042 -> begin
true
end))))
in (match (uu____23013) with
| (g', inversions) -> begin
(

let uu____23057 = (FStar_All.pipe_right g' (FStar_List.partition (fun uu___129_23078 -> (match (uu___129_23078) with
| FStar_SMTEncoding_Term.DeclFun (uu____23079) -> begin
true
end
| uu____23090 -> begin
false
end))))
in (match (uu____23057) with
| (decls, rest) -> begin
(((FStar_List.append decls (FStar_List.append rest inversions))), (env1))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, uu____23108, tps, k, uu____23111, datas) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___130_23128 -> (match (uu___130_23128) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____23129 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> (match (is_logical) with
| true -> begin
(

let uu____23138 = c
in (match (uu____23138) with
| (name, args, uu____23143, uu____23144, uu____23145) -> begin
(

let uu____23150 = (

let uu____23151 = (

let uu____23162 = (FStar_All.pipe_right args (FStar_List.map (fun uu____23179 -> (match (uu____23179) with
| (uu____23186, sort, uu____23188) -> begin
sort
end))))
in ((name), (uu____23162), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____23151))
in (uu____23150)::[])
end))
end
| uu____23193 -> begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end))
in (

let inversion_axioms = (fun tapp vars -> (

let uu____23215 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (

let uu____23221 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right uu____23221 FStar_Option.isNone)))))
in (match (uu____23215) with
| true -> begin
[]
end
| uu____23252 -> begin
(

let uu____23253 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____23253) with
| (xxsym, xx) -> begin
(

let uu____23262 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun uu____23301 l -> (match (uu____23301) with
| (out, decls) -> begin
(

let uu____23321 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (uu____23321) with
| (uu____23332, data_t) -> begin
(

let uu____23334 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (uu____23334) with
| (args, res) -> begin
(

let indices = (

let uu____23380 = (

let uu____23381 = (FStar_Syntax_Subst.compress res)
in uu____23381.FStar_Syntax_Syntax.n)
in (match (uu____23380) with
| FStar_Syntax_Syntax.Tm_app (uu____23392, indices) -> begin
indices
end
| uu____23414 -> begin
[]
end))
in (

let env1 = (FStar_All.pipe_right args (FStar_List.fold_left (fun env1 uu____23438 -> (match (uu____23438) with
| (x, uu____23444) -> begin
(

let uu____23445 = (

let uu____23446 = (

let uu____23453 = (mk_term_projector_name l x)
in ((uu____23453), ((xx)::[])))
in (FStar_SMTEncoding_Util.mkApp uu____23446))
in (push_term_var env1 x uu____23445))
end)) env))
in (

let uu____23456 = (encode_args indices env1)
in (match (uu____23456) with
| (indices1, decls') -> begin
((match ((Prims.op_disEquality (FStar_List.length indices1) (FStar_List.length vars))) with
| true -> begin
(failwith "Impossible")
end
| uu____23480 -> begin
()
end);
(

let eqs = (

let uu____23482 = (FStar_List.map2 (fun v1 a -> (

let uu____23498 = (

let uu____23503 = (FStar_SMTEncoding_Util.mkFreeV v1)
in ((uu____23503), (a)))
in (FStar_SMTEncoding_Util.mkEq uu____23498))) vars indices1)
in (FStar_All.pipe_right uu____23482 FStar_SMTEncoding_Util.mk_and_l))
in (

let uu____23506 = (

let uu____23507 = (

let uu____23512 = (

let uu____23513 = (

let uu____23518 = (mk_data_tester env1 l xx)
in ((uu____23518), (eqs)))
in (FStar_SMTEncoding_Util.mkAnd uu____23513))
in ((out), (uu____23512)))
in (FStar_SMTEncoding_Util.mkOr uu____23507))
in ((uu____23506), ((FStar_List.append decls decls')))));
)
end))))
end))
end))
end)) ((FStar_SMTEncoding_Util.mkFalse), ([]))))
in (match (uu____23262) with
| (data_ax, decls) -> begin
(

let uu____23531 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____23531) with
| (ffsym, ff) -> begin
(

let fuel_guarded_inversion = (

let xx_has_type_sfuel = (match (((FStar_List.length datas) > (Prims.parse_int "1"))) with
| true -> begin
(

let uu____23542 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((ff)::[])))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel uu____23542 xx tapp))
end
| uu____23545 -> begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end)
in (

let uu____23546 = (

let uu____23553 = (

let uu____23554 = (

let uu____23565 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (

let uu____23580 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_sfuel), (data_ax)))
in ((((xx_has_type_sfuel)::[])::[]), (uu____23565), (uu____23580))))
in (FStar_SMTEncoding_Util.mkForall uu____23554))
in (

let uu____23595 = (varops.mk_unique (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str))
in ((uu____23553), (FStar_Pervasives_Native.Some ("inversion axiom")), (uu____23595))))
in (FStar_SMTEncoding_Util.mkAssume uu____23546)))
in (FStar_List.append decls ((fuel_guarded_inversion)::[])))
end))
end))
end))
end)))
in (

let uu____23598 = (

let uu____23611 = (

let uu____23612 = (FStar_Syntax_Subst.compress k)
in uu____23612.FStar_Syntax_Syntax.n)
in (match (uu____23611) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
(((FStar_List.append tps formals)), ((FStar_Syntax_Util.comp_result kres)))
end
| uu____23657 -> begin
((tps), (k))
end))
in (match (uu____23598) with
| (formals, res) -> begin
(

let uu____23680 = (FStar_Syntax_Subst.open_term formals res)
in (match (uu____23680) with
| (formals1, res1) -> begin
(

let uu____23691 = (encode_binders FStar_Pervasives_Native.None formals1 env)
in (match (uu____23691) with
| (vars, guards, env', binder_decls, uu____23716) -> begin
(

let uu____23729 = (new_term_constant_and_tok_from_lid env t)
in (match (uu____23729) with
| (tname, ttok, env1) -> begin
(

let ttok_tm = (FStar_SMTEncoding_Util.mkApp ((ttok), ([])))
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let tapp = (

let uu____23748 = (

let uu____23755 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((tname), (uu____23755)))
in (FStar_SMTEncoding_Util.mkApp uu____23748))
in (

let uu____23764 = (

let tname_decl = (

let uu____23774 = (

let uu____23775 = (FStar_All.pipe_right vars (FStar_List.map (fun uu____23807 -> (match (uu____23807) with
| (n1, s) -> begin
(((Prims.strcat tname n1)), (s), (false))
end))))
in (

let uu____23820 = (varops.next_id ())
in ((tname), (uu____23775), (FStar_SMTEncoding_Term.Term_sort), (uu____23820), (false))))
in (constructor_or_logic_type_decl uu____23774))
in (

let uu____23829 = (match (vars) with
| [] -> begin
(

let uu____23842 = (

let uu____23843 = (

let uu____23846 = (FStar_SMTEncoding_Util.mkApp ((tname), ([])))
in (FStar_All.pipe_left (fun _0_45 -> FStar_Pervasives_Native.Some (_0_45)) uu____23846))
in (push_free_var env1 t tname uu____23843))
in (([]), (uu____23842)))
end
| uu____23853 -> begin
(

let ttok_decl = FStar_SMTEncoding_Term.DeclFun (((ttok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("token"))))
in (

let ttok_fresh = (

let uu____23862 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ttok), (FStar_SMTEncoding_Term.Term_sort)) uu____23862))
in (

let ttok_app = (mk_Apply ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (

let uu____23876 = (

let uu____23883 = (

let uu____23884 = (

let uu____23899 = (FStar_SMTEncoding_Util.mkEq ((ttok_app), (tapp)))
in ((pats), (FStar_Pervasives_Native.None), (vars), (uu____23899)))
in (FStar_SMTEncoding_Util.mkForall' uu____23884))
in ((uu____23883), (FStar_Pervasives_Native.Some ("name-token correspondence")), ((Prims.strcat "token_correspondence_" ttok))))
in (FStar_SMTEncoding_Util.mkAssume uu____23876))
in (((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[]), (env1)))))))
end)
in (match (uu____23829) with
| (tok_decls, env2) -> begin
(((FStar_List.append tname_decl tok_decls)), (env2))
end)))
in (match (uu____23764) with
| (decls, env2) -> begin
(

let kindingAx = (

let uu____23939 = (encode_term_pred FStar_Pervasives_Native.None res1 env' tapp)
in (match (uu____23939) with
| (k1, decls1) -> begin
(

let karr = (match (((FStar_List.length formals1) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____23957 = (

let uu____23958 = (

let uu____23965 = (

let uu____23966 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____23966))
in ((uu____23965), (FStar_Pervasives_Native.Some ("kinding")), ((Prims.strcat "pre_kinding_" ttok))))
in (FStar_SMTEncoding_Util.mkAssume uu____23958))
in (uu____23957)::[])
end
| uu____23969 -> begin
[]
end)
in (

let uu____23970 = (

let uu____23973 = (

let uu____23976 = (

let uu____23977 = (

let uu____23984 = (

let uu____23985 = (

let uu____23996 = (FStar_SMTEncoding_Util.mkImp ((guard), (k1)))
in ((((tapp)::[])::[]), (vars), (uu____23996)))
in (FStar_SMTEncoding_Util.mkForall uu____23985))
in ((uu____23984), (FStar_Pervasives_Native.None), ((Prims.strcat "kinding_" ttok))))
in (FStar_SMTEncoding_Util.mkAssume uu____23977))
in (uu____23976)::[])
in (FStar_List.append karr uu____23973))
in (FStar_List.append decls1 uu____23970)))
end))
in (

let aux = (

let uu____24012 = (

let uu____24015 = (inversion_axioms tapp vars)
in (

let uu____24018 = (

let uu____24021 = (pretype_axiom env2 tapp vars)
in (uu____24021)::[])
in (FStar_List.append uu____24015 uu____24018)))
in (FStar_List.append kindingAx uu____24012))
in (

let g = (FStar_List.append decls (FStar_List.append binder_decls aux))
in ((g), (env2)))))
end)))))
end))
end))
end))
end))))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____24028, uu____24029, uu____24030, uu____24031, uu____24032) when (FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____24040, t, uu____24042, n_tps, uu____24044) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____24052 = (new_term_constant_and_tok_from_lid env d)
in (match (uu____24052) with
| (ddconstrsym, ddtok, env1) -> begin
(

let ddtok_tm = (FStar_SMTEncoding_Util.mkApp ((ddtok), ([])))
in (

let uu____24069 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____24069) with
| (formals, t_res) -> begin
(

let uu____24104 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____24104) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (

let uu____24118 = (encode_binders (FStar_Pervasives_Native.Some (fuel_tm)) formals env1)
in (match (uu____24118) with
| (vars, guards, env', binder_decls, names1) -> begin
(

let fields = (FStar_All.pipe_right names1 (FStar_List.mapi (fun n1 x -> (

let projectible = true
in (

let uu____24188 = (mk_term_projector_name d x)
in ((uu____24188), (FStar_SMTEncoding_Term.Term_sort), (projectible)))))))
in (

let datacons = (

let uu____24190 = (

let uu____24209 = (varops.next_id ())
in ((ddconstrsym), (fields), (FStar_SMTEncoding_Term.Term_sort), (uu____24209), (true)))
in (FStar_All.pipe_right uu____24190 FStar_SMTEncoding_Term.constructor_to_decl))
in (

let app = (mk_Apply ddtok_tm vars)
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (

let uu____24248 = (encode_term_pred FStar_Pervasives_Native.None t env1 ddtok_tm)
in (match (uu____24248) with
| (tok_typing, decls3) -> begin
(

let tok_typing1 = (match (fields) with
| (uu____24260)::uu____24261 -> begin
(

let ff = (("ty"), (FStar_SMTEncoding_Term.Term_sort))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV ff)
in (

let vtok_app_l = (mk_Apply ddtok_tm ((ff)::[]))
in (

let vtok_app_r = (mk_Apply f ((((ddtok), (FStar_SMTEncoding_Term.Term_sort)))::[]))
in (

let uu____24306 = (

let uu____24317 = (FStar_SMTEncoding_Term.mk_NoHoist f tok_typing)
in ((((vtok_app_l)::[])::((vtok_app_r)::[])::[]), ((ff)::[]), (uu____24317)))
in (FStar_SMTEncoding_Util.mkForall uu____24306))))))
end
| uu____24342 -> begin
tok_typing
end)
in (

let uu____24351 = (encode_binders (FStar_Pervasives_Native.Some (fuel_tm)) formals env1)
in (match (uu____24351) with
| (vars', guards', env'', decls_formals, uu____24376) -> begin
(

let uu____24389 = (

let xvars1 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars')
in (

let dapp1 = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars1)))
in (encode_term_pred (FStar_Pervasives_Native.Some (fuel_tm)) t_res env'' dapp1)))
in (match (uu____24389) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_SMTEncoding_Util.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| uu____24420 -> begin
(

let uu____24427 = (

let uu____24428 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ddtok), (FStar_SMTEncoding_Term.Term_sort)) uu____24428))
in (uu____24427)::[])
end)
in (

let encode_elim = (fun uu____24438 -> (

let uu____24439 = (FStar_Syntax_Util.head_and_args t_res)
in (match (uu____24439) with
| (head1, args) -> begin
(

let uu____24482 = (

let uu____24483 = (FStar_Syntax_Subst.compress head1)
in uu____24483.FStar_Syntax_Syntax.n)
in (match (uu____24482) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____24493; FStar_Syntax_Syntax.vars = uu____24494}, uu____24495) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let uu____24501 = (encode_args args env')
in (match (uu____24501) with
| (encoded_args, arg_decls) -> begin
(

let guards_for_parameter = (fun orig_arg arg xv -> (

let fv1 = (match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv1) -> begin
fv1
end
| uu____24544 -> begin
(

let uu____24545 = (

let uu____24546 = (

let uu____24551 = (

let uu____24552 = (FStar_Syntax_Print.term_to_string orig_arg)
in (FStar_Util.format1 "Inductive type parameter %s must be a variable ; You may want to change it to an index." uu____24552))
in ((uu____24551), (orig_arg.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____24546))
in (FStar_Exn.raise uu____24545))
end)
in (

let guards1 = (FStar_All.pipe_right guards (FStar_List.collect (fun g -> (

let uu____24568 = (

let uu____24569 = (FStar_SMTEncoding_Term.free_variables g)
in (FStar_List.contains fv1 uu____24569))
in (match (uu____24568) with
| true -> begin
(

let uu____24582 = (FStar_SMTEncoding_Term.subst g fv1 xv)
in (uu____24582)::[])
end
| uu____24583 -> begin
[]
end)))))
in (FStar_SMTEncoding_Util.mk_and_l guards1))))
in (

let uu____24584 = (

let uu____24597 = (FStar_List.zip args encoded_args)
in (FStar_List.fold_left (fun uu____24647 uu____24648 -> (match (((uu____24647), (uu____24648))) with
| ((env2, arg_vars, eqns_or_guards, i), (orig_arg, arg)) -> begin
(

let uu____24743 = (

let uu____24750 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (gen_term_var env2 uu____24750))
in (match (uu____24743) with
| (uu____24763, xv, env3) -> begin
(

let eqns = (match ((i < n_tps)) with
| true -> begin
(

let uu____24771 = (guards_for_parameter (FStar_Pervasives_Native.fst orig_arg) arg xv)
in (uu____24771)::eqns_or_guards)
end
| uu____24772 -> begin
(

let uu____24773 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (uu____24773)::eqns_or_guards)
end)
in ((env3), ((xv)::arg_vars), (eqns), ((i + (Prims.parse_int "1")))))
end))
end)) ((env'), ([]), ([]), ((Prims.parse_int "0"))) uu____24597))
in (match (uu____24584) with
| (uu____24788, arg_vars, elim_eqns_or_guards, uu____24791) -> begin
(

let arg_vars1 = (FStar_List.rev arg_vars)
in (

let ty = (FStar_SMTEncoding_Util.mkApp ((encoded_head), (arg_vars1)))
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

let uu____24821 = (

let uu____24828 = (

let uu____24829 = (

let uu____24840 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____24851 = (

let uu____24852 = (

let uu____24857 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append elim_eqns_or_guards guards))
in ((ty_pred), (uu____24857)))
in (FStar_SMTEncoding_Util.mkImp uu____24852))
in ((((ty_pred)::[])::[]), (uu____24840), (uu____24851))))
in (FStar_SMTEncoding_Util.mkForall uu____24829))
in ((uu____24828), (FStar_Pervasives_Native.Some ("data constructor typing elim")), ((Prims.strcat "data_elim_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____24821))
in (

let subterm_ordering = (match ((FStar_Ident.lid_equals d FStar_Parser_Const.lextop_lid)) with
| true -> begin
(

let x = (

let uu____24880 = (varops.fresh "x")
in ((uu____24880), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (

let uu____24882 = (

let uu____24889 = (

let uu____24890 = (

let uu____24901 = (

let uu____24906 = (

let uu____24909 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in (uu____24909)::[])
in (uu____24906)::[])
in (

let uu____24914 = (

let uu____24915 = (

let uu____24920 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (

let uu____24921 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in ((uu____24920), (uu____24921))))
in (FStar_SMTEncoding_Util.mkImp uu____24915))
in ((uu____24901), ((x)::[]), (uu____24914))))
in (FStar_SMTEncoding_Util.mkForall uu____24890))
in (

let uu____24940 = (varops.mk_unique "lextop")
in ((uu____24889), (FStar_Pervasives_Native.Some ("lextop is top")), (uu____24940))))
in (FStar_SMTEncoding_Util.mkAssume uu____24882))))
end
| uu____24943 -> begin
(

let prec = (

let uu____24947 = (FStar_All.pipe_right vars (FStar_List.mapi (fun i v1 -> (match ((i < n_tps)) with
| true -> begin
[]
end
| uu____24974 -> begin
(

let uu____24975 = (

let uu____24976 = (FStar_SMTEncoding_Util.mkFreeV v1)
in (FStar_SMTEncoding_Util.mk_Precedes uu____24976 dapp1))
in (uu____24975)::[])
end))))
in (FStar_All.pipe_right uu____24947 FStar_List.flatten))
in (

let uu____24983 = (

let uu____24990 = (

let uu____24991 = (

let uu____25002 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____25013 = (

let uu____25014 = (

let uu____25019 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (uu____25019)))
in (FStar_SMTEncoding_Util.mkImp uu____25014))
in ((((ty_pred)::[])::[]), (uu____25002), (uu____25013))))
in (FStar_SMTEncoding_Util.mkForall uu____24991))
in ((uu____24990), (FStar_Pervasives_Native.Some ("subterm ordering")), ((Prims.strcat "subterm_ordering_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____24983)))
end)
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end)))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let uu____25040 = (encode_args args env')
in (match (uu____25040) with
| (encoded_args, arg_decls) -> begin
(

let guards_for_parameter = (fun orig_arg arg xv -> (

let fv1 = (match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv1) -> begin
fv1
end
| uu____25083 -> begin
(

let uu____25084 = (

let uu____25085 = (

let uu____25090 = (

let uu____25091 = (FStar_Syntax_Print.term_to_string orig_arg)
in (FStar_Util.format1 "Inductive type parameter %s must be a variable ; You may want to change it to an index." uu____25091))
in ((uu____25090), (orig_arg.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____25085))
in (FStar_Exn.raise uu____25084))
end)
in (

let guards1 = (FStar_All.pipe_right guards (FStar_List.collect (fun g -> (

let uu____25107 = (

let uu____25108 = (FStar_SMTEncoding_Term.free_variables g)
in (FStar_List.contains fv1 uu____25108))
in (match (uu____25107) with
| true -> begin
(

let uu____25121 = (FStar_SMTEncoding_Term.subst g fv1 xv)
in (uu____25121)::[])
end
| uu____25122 -> begin
[]
end)))))
in (FStar_SMTEncoding_Util.mk_and_l guards1))))
in (

let uu____25123 = (

let uu____25136 = (FStar_List.zip args encoded_args)
in (FStar_List.fold_left (fun uu____25186 uu____25187 -> (match (((uu____25186), (uu____25187))) with
| ((env2, arg_vars, eqns_or_guards, i), (orig_arg, arg)) -> begin
(

let uu____25282 = (

let uu____25289 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (gen_term_var env2 uu____25289))
in (match (uu____25282) with
| (uu____25302, xv, env3) -> begin
(

let eqns = (match ((i < n_tps)) with
| true -> begin
(

let uu____25310 = (guards_for_parameter (FStar_Pervasives_Native.fst orig_arg) arg xv)
in (uu____25310)::eqns_or_guards)
end
| uu____25311 -> begin
(

let uu____25312 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (uu____25312)::eqns_or_guards)
end)
in ((env3), ((xv)::arg_vars), (eqns), ((i + (Prims.parse_int "1")))))
end))
end)) ((env'), ([]), ([]), ((Prims.parse_int "0"))) uu____25136))
in (match (uu____25123) with
| (uu____25327, arg_vars, elim_eqns_or_guards, uu____25330) -> begin
(

let arg_vars1 = (FStar_List.rev arg_vars)
in (

let ty = (FStar_SMTEncoding_Util.mkApp ((encoded_head), (arg_vars1)))
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

let uu____25360 = (

let uu____25367 = (

let uu____25368 = (

let uu____25379 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____25390 = (

let uu____25391 = (

let uu____25396 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append elim_eqns_or_guards guards))
in ((ty_pred), (uu____25396)))
in (FStar_SMTEncoding_Util.mkImp uu____25391))
in ((((ty_pred)::[])::[]), (uu____25379), (uu____25390))))
in (FStar_SMTEncoding_Util.mkForall uu____25368))
in ((uu____25367), (FStar_Pervasives_Native.Some ("data constructor typing elim")), ((Prims.strcat "data_elim_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____25360))
in (

let subterm_ordering = (match ((FStar_Ident.lid_equals d FStar_Parser_Const.lextop_lid)) with
| true -> begin
(

let x = (

let uu____25419 = (varops.fresh "x")
in ((uu____25419), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (

let uu____25421 = (

let uu____25428 = (

let uu____25429 = (

let uu____25440 = (

let uu____25445 = (

let uu____25448 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in (uu____25448)::[])
in (uu____25445)::[])
in (

let uu____25453 = (

let uu____25454 = (

let uu____25459 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (

let uu____25460 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in ((uu____25459), (uu____25460))))
in (FStar_SMTEncoding_Util.mkImp uu____25454))
in ((uu____25440), ((x)::[]), (uu____25453))))
in (FStar_SMTEncoding_Util.mkForall uu____25429))
in (

let uu____25479 = (varops.mk_unique "lextop")
in ((uu____25428), (FStar_Pervasives_Native.Some ("lextop is top")), (uu____25479))))
in (FStar_SMTEncoding_Util.mkAssume uu____25421))))
end
| uu____25482 -> begin
(

let prec = (

let uu____25486 = (FStar_All.pipe_right vars (FStar_List.mapi (fun i v1 -> (match ((i < n_tps)) with
| true -> begin
[]
end
| uu____25513 -> begin
(

let uu____25514 = (

let uu____25515 = (FStar_SMTEncoding_Util.mkFreeV v1)
in (FStar_SMTEncoding_Util.mk_Precedes uu____25515 dapp1))
in (uu____25514)::[])
end))))
in (FStar_All.pipe_right uu____25486 FStar_List.flatten))
in (

let uu____25522 = (

let uu____25529 = (

let uu____25530 = (

let uu____25541 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____25552 = (

let uu____25553 = (

let uu____25558 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (uu____25558)))
in (FStar_SMTEncoding_Util.mkImp uu____25553))
in ((((ty_pred)::[])::[]), (uu____25541), (uu____25552))))
in (FStar_SMTEncoding_Util.mkForall uu____25530))
in ((uu____25529), (FStar_Pervasives_Native.Some ("subterm ordering")), ((Prims.strcat "subterm_ordering_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____25522)))
end)
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end)))
end)))
end
| uu____25577 -> begin
((

let uu____25579 = (

let uu____25580 = (FStar_Syntax_Print.lid_to_string d)
in (

let uu____25581 = (FStar_Syntax_Print.term_to_string head1)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" uu____25580 uu____25581)))
in (FStar_Errors.warn se.FStar_Syntax_Syntax.sigrng uu____25579));
(([]), ([]));
)
end))
end)))
in (

let uu____25586 = (encode_elim ())
in (match (uu____25586) with
| (decls2, elim) -> begin
(

let g = (

let uu____25606 = (

let uu____25609 = (

let uu____25612 = (

let uu____25615 = (

let uu____25618 = (

let uu____25619 = (

let uu____25630 = (

let uu____25633 = (

let uu____25634 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" uu____25634))
in FStar_Pervasives_Native.Some (uu____25633))
in ((ddtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (uu____25630)))
in FStar_SMTEncoding_Term.DeclFun (uu____25619))
in (uu____25618)::[])
in (

let uu____25639 = (

let uu____25642 = (

let uu____25645 = (

let uu____25648 = (

let uu____25651 = (

let uu____25654 = (

let uu____25657 = (

let uu____25658 = (

let uu____25665 = (

let uu____25666 = (

let uu____25677 = (FStar_SMTEncoding_Util.mkEq ((app), (dapp)))
in ((((app)::[])::[]), (vars), (uu____25677)))
in (FStar_SMTEncoding_Util.mkForall uu____25666))
in ((uu____25665), (FStar_Pervasives_Native.Some ("equality for proxy")), ((Prims.strcat "equality_tok_" ddtok))))
in (FStar_SMTEncoding_Util.mkAssume uu____25658))
in (

let uu____25690 = (

let uu____25693 = (

let uu____25694 = (

let uu____25701 = (

let uu____25702 = (

let uu____25713 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) vars')
in (

let uu____25724 = (FStar_SMTEncoding_Util.mkImp ((guard'), (ty_pred')))
in ((((ty_pred')::[])::[]), (uu____25713), (uu____25724))))
in (FStar_SMTEncoding_Util.mkForall uu____25702))
in ((uu____25701), (FStar_Pervasives_Native.Some ("data constructor typing intro")), ((Prims.strcat "data_typing_intro_" ddtok))))
in (FStar_SMTEncoding_Util.mkAssume uu____25694))
in (uu____25693)::[])
in (uu____25657)::uu____25690))
in ((FStar_SMTEncoding_Util.mkAssume ((tok_typing1), (FStar_Pervasives_Native.Some ("typing for data constructor proxy")), ((Prims.strcat "typing_tok_" ddtok)))))::uu____25654)
in (FStar_List.append uu____25651 elim))
in (FStar_List.append decls_pred uu____25648))
in (FStar_List.append decls_formals uu____25645))
in (FStar_List.append proxy_fresh uu____25642))
in (FStar_List.append uu____25615 uu____25639)))
in (FStar_List.append decls3 uu____25612))
in (FStar_List.append decls2 uu____25609))
in (FStar_List.append binder_decls uu____25606))
in (((FStar_List.append datacons g)), (env1)))
end)))))
end))
end)))
end))))))))
end)))
end))
end)))
end)))
end))))
and encode_sigelts : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun uu____25770 se -> (match (uu____25770) with
| (g, env1) -> begin
(

let uu____25790 = (encode_sigelt env1 se)
in (match (uu____25790) with
| (g', env2) -> begin
(((FStar_List.append g g')), (env2))
end))
end)) (([]), (env)))))


let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env bindings -> (

let encode_binding = (fun b uu____25849 -> (match (uu____25849) with
| (i, decls, env1) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (uu____25881) -> begin
(((i + (Prims.parse_int "1"))), ([]), (env1))
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env1.tcenv x.FStar_Syntax_Syntax.sort)
in ((

let uu____25887 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____25887) with
| true -> begin
(

let uu____25888 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____25889 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____25890 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" uu____25888 uu____25889 uu____25890))))
end
| uu____25891 -> begin
()
end));
(

let uu____25892 = (encode_term t1 env1)
in (match (uu____25892) with
| (t, decls') -> begin
(

let t_hash = (FStar_SMTEncoding_Term.hash_of_term t)
in (

let uu____25908 = (

let uu____25915 = (

let uu____25916 = (

let uu____25917 = (FStar_Util.digest_of_string t_hash)
in (Prims.strcat uu____25917 (Prims.strcat "_" (Prims.string_of_int i))))
in (Prims.strcat "x_" uu____25916))
in (new_term_constant_from_string env1 x uu____25915))
in (match (uu____25908) with
| (xxsym, xx, env') -> begin
(

let t2 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel FStar_Pervasives_Native.None xx t)
in (

let caption = (

let uu____25933 = (FStar_Options.log_queries ())
in (match (uu____25933) with
| true -> begin
(

let uu____25936 = (

let uu____25937 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____25938 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____25939 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" uu____25937 uu____25938 uu____25939))))
in FStar_Pervasives_Native.Some (uu____25936))
end
| uu____25940 -> begin
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
| FStar_TypeChecker_Env.Binding_lid (x, (uu____25955, t)) -> begin
(

let t_norm = (whnf env1 t)
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____25969 = (encode_free_var false env1 fv t t_norm [])
in (match (uu____25969) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))))
end
| FStar_TypeChecker_Env.Binding_sig_inst (uu____25992, se, uu____25994) -> begin
(

let uu____25999 = (encode_sigelt env1 se)
in (match (uu____25999) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))
end
| FStar_TypeChecker_Env.Binding_sig (uu____26016, se) -> begin
(

let uu____26022 = (encode_sigelt env1 se)
in (match (uu____26022) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))
end)
end))
in (

let uu____26039 = (FStar_List.fold_right encode_binding bindings (((Prims.parse_int "0")), ([]), (env)))
in (match (uu____26039) with
| (uu____26062, decls, env1) -> begin
((decls), (env1))
end))))


let encode_labels : 'Auu____26077 'Auu____26078 . ((Prims.string * FStar_SMTEncoding_Term.sort) * 'Auu____26078 * 'Auu____26077) Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl Prims.list) = (fun labs -> (

let prefix1 = (FStar_All.pipe_right labs (FStar_List.map (fun uu____26146 -> (match (uu____26146) with
| (l, uu____26158, uu____26159) -> begin
FStar_SMTEncoding_Term.DeclFun ((((FStar_Pervasives_Native.fst l)), ([]), (FStar_SMTEncoding_Term.Bool_sort), (FStar_Pervasives_Native.None)))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun uu____26205 -> (match (uu____26205) with
| (l, uu____26219, uu____26220) -> begin
(

let uu____26229 = (FStar_All.pipe_left (fun _0_46 -> FStar_SMTEncoding_Term.Echo (_0_46)) (FStar_Pervasives_Native.fst l))
in (

let uu____26230 = (

let uu____26233 = (

let uu____26234 = (FStar_SMTEncoding_Util.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (uu____26234))
in (uu____26233)::[])
in (uu____26229)::uu____26230))
end))))
in ((prefix1), (suffix)))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (

let uu____26256 = (

let uu____26259 = (

let uu____26260 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (

let uu____26263 = (

let uu____26264 = (FStar_TypeChecker_Env.current_module tcenv)
in (FStar_All.pipe_right uu____26264 FStar_Ident.string_of_lid))
in {bindings = []; depth = (Prims.parse_int "0"); tcenv = tcenv; warn = true; cache = uu____26260; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true; current_module_name = uu____26263}))
in (uu____26259)::[])
in (FStar_ST.op_Colon_Equals last_env uu____26256)))


let get_env : FStar_Ident.lident  ->  FStar_TypeChecker_Env.env  ->  env_t = (fun cmn tcenv -> (

let uu____26323 = (FStar_ST.op_Bang last_env)
in (match (uu____26323) with
| [] -> begin
(failwith "No env; call init first!")
end
| (e)::uu____26377 -> begin
(

let uu___161_26380 = e
in (

let uu____26381 = (FStar_Ident.string_of_lid cmn)
in {bindings = uu___161_26380.bindings; depth = uu___161_26380.depth; tcenv = tcenv; warn = uu___161_26380.warn; cache = uu___161_26380.cache; nolabels = uu___161_26380.nolabels; use_zfuel_name = uu___161_26380.use_zfuel_name; encode_non_total_function_typ = uu___161_26380.encode_non_total_function_typ; current_module_name = uu____26381}))
end)))


let set_env : env_t  ->  Prims.unit = (fun env -> (

let uu____26386 = (FStar_ST.op_Bang last_env)
in (match (uu____26386) with
| [] -> begin
(failwith "Empty env stack")
end
| (uu____26439)::tl1 -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl1))
end)))


let push_env : Prims.unit  ->  Prims.unit = (fun uu____26496 -> (

let uu____26497 = (FStar_ST.op_Bang last_env)
in (match (uu____26497) with
| [] -> begin
(failwith "Empty env stack")
end
| (hd1)::tl1 -> begin
(

let refs = (FStar_Util.smap_copy hd1.cache)
in (

let top = (

let uu___162_26558 = hd1
in {bindings = uu___162_26558.bindings; depth = uu___162_26558.depth; tcenv = uu___162_26558.tcenv; warn = uu___162_26558.warn; cache = refs; nolabels = uu___162_26558.nolabels; use_zfuel_name = uu___162_26558.use_zfuel_name; encode_non_total_function_typ = uu___162_26558.encode_non_total_function_typ; current_module_name = uu___162_26558.current_module_name})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd1)::tl1))))
end)))


let pop_env : Prims.unit  ->  Prims.unit = (fun uu____26612 -> (

let uu____26613 = (FStar_ST.op_Bang last_env)
in (match (uu____26613) with
| [] -> begin
(failwith "Popping an empty stack")
end
| (uu____26666)::tl1 -> begin
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
| ((uu____26764)::uu____26765, FStar_SMTEncoding_Term.Assume (a)) -> begin
FStar_SMTEncoding_Term.Assume ((

let uu___163_26773 = a
in {FStar_SMTEncoding_Term.assumption_term = uu___163_26773.FStar_SMTEncoding_Term.assumption_term; FStar_SMTEncoding_Term.assumption_caption = uu___163_26773.FStar_SMTEncoding_Term.assumption_caption; FStar_SMTEncoding_Term.assumption_name = uu___163_26773.FStar_SMTEncoding_Term.assumption_name; FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids}))
end
| uu____26774 -> begin
d
end))


let fact_dbs_for_lid : env_t  ->  FStar_Ident.lid  ->  FStar_SMTEncoding_Term.fact_db_id Prims.list = (fun env lid -> (

let uu____26791 = (

let uu____26794 = (

let uu____26795 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in FStar_SMTEncoding_Term.Namespace (uu____26795))
in (

let uu____26796 = (open_fact_db_tags env)
in (uu____26794)::uu____26796))
in (FStar_SMTEncoding_Term.Name (lid))::uu____26791))


let encode_top_level_facts : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env se -> (

let fact_db_ids = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.collect (fact_dbs_for_lid env)))
in (

let uu____26820 = (encode_sigelt env se)
in (match (uu____26820) with
| (g, env1) -> begin
(

let g1 = (FStar_All.pipe_right g (FStar_List.map (place_decl_in_fact_dbs env1 fact_db_ids)))
in ((g1), (env1)))
end))))


let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (

let caption = (fun decls -> (

let uu____26858 = (FStar_Options.log_queries ())
in (match (uu____26858) with
| true -> begin
(

let uu____26861 = (

let uu____26862 = (

let uu____26863 = (

let uu____26864 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.map FStar_Syntax_Print.lid_to_string))
in (FStar_All.pipe_right uu____26864 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " uu____26863))
in FStar_SMTEncoding_Term.Caption (uu____26862))
in (uu____26861)::decls)
end
| uu____26873 -> begin
decls
end)))
in (

let env = (

let uu____26875 = (FStar_TypeChecker_Env.current_module tcenv)
in (get_env uu____26875 tcenv))
in (

let uu____26876 = (encode_top_level_facts env se)
in (match (uu____26876) with
| (decls, env1) -> begin
((set_env env1);
(

let uu____26890 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 uu____26890));
)
end)))))


let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____26902 -> begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in ((

let uu____26904 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____26904) with
| true -> begin
(

let uu____26905 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) Prims.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name uu____26905))
end
| uu____26906 -> begin
()
end));
(

let env = (get_env modul.FStar_Syntax_Syntax.name tcenv)
in (

let encode_signature = (fun env1 ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun uu____26940 se -> (match (uu____26940) with
| (g, env2) -> begin
(

let uu____26960 = (encode_top_level_facts env2 se)
in (match (uu____26960) with
| (g', env3) -> begin
(((FStar_List.append g g')), (env3))
end))
end)) (([]), (env1)))))
in (

let uu____26983 = (encode_signature (

let uu___164_26992 = env
in {bindings = uu___164_26992.bindings; depth = uu___164_26992.depth; tcenv = uu___164_26992.tcenv; warn = false; cache = uu___164_26992.cache; nolabels = uu___164_26992.nolabels; use_zfuel_name = uu___164_26992.use_zfuel_name; encode_non_total_function_typ = uu___164_26992.encode_non_total_function_typ; current_module_name = uu___164_26992.current_module_name}) modul.FStar_Syntax_Syntax.exports)
in (match (uu____26983) with
| (decls, env1) -> begin
(

let caption = (fun decls1 -> (

let uu____27009 = (FStar_Options.log_queries ())
in (match (uu____27009) with
| true -> begin
(

let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::decls1) ((FStar_SMTEncoding_Term.Caption ((Prims.strcat "End " msg)))::[])))
end
| uu____27013 -> begin
decls1
end)))
in ((set_env (

let uu___165_27017 = env1
in {bindings = uu___165_27017.bindings; depth = uu___165_27017.depth; tcenv = uu___165_27017.tcenv; warn = true; cache = uu___165_27017.cache; nolabels = uu___165_27017.nolabels; use_zfuel_name = uu___165_27017.use_zfuel_name; encode_non_total_function_typ = uu___165_27017.encode_non_total_function_typ; current_module_name = uu___165_27017.current_module_name}));
(

let uu____27019 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____27019) with
| true -> begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end
| uu____27020 -> begin
()
end));
(

let decls1 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls1));
))
end))));
)))


let encode_query : (Prims.unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_ErrorReporting.label Prims.list * FStar_SMTEncoding_Term.decl * FStar_SMTEncoding_Term.decl Prims.list) = (fun use_env_msg tcenv q -> ((

let uu____27074 = (

let uu____27075 = (FStar_TypeChecker_Env.current_module tcenv)
in uu____27075.FStar_Ident.str)
in (FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name uu____27074));
(

let env = (

let uu____27077 = (FStar_TypeChecker_Env.current_module tcenv)
in (get_env uu____27077 tcenv))
in (

let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (

let uu____27089 = (

let rec aux = (fun bindings1 -> (match (bindings1) with
| (FStar_TypeChecker_Env.Binding_var (x))::rest -> begin
(

let uu____27124 = (aux rest)
in (match (uu____27124) with
| (out, rest1) -> begin
(

let t = (

let uu____27154 = (FStar_Syntax_Util.destruct_typ_as_formula x.FStar_Syntax_Syntax.sort)
in (match (uu____27154) with
| FStar_Pervasives_Native.Some (uu____27159) -> begin
(

let uu____27160 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.t_unit)
in (FStar_Syntax_Util.refine uu____27160 x.FStar_Syntax_Syntax.sort))
end
| uu____27161 -> begin
x.FStar_Syntax_Syntax.sort
end))
in (

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
in (

let uu____27165 = (

let uu____27168 = (FStar_Syntax_Syntax.mk_binder (

let uu___166_27171 = x
in {FStar_Syntax_Syntax.ppname = uu___166_27171.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___166_27171.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in (uu____27168)::out)
in ((uu____27165), (rest1)))))
end))
end
| uu____27176 -> begin
(([]), (bindings1))
end))
in (

let uu____27183 = (aux bindings)
in (match (uu____27183) with
| (closing, bindings1) -> begin
(

let uu____27208 = (FStar_Syntax_Util.close_forall_no_univs (FStar_List.rev closing) q)
in ((uu____27208), (bindings1)))
end)))
in (match (uu____27089) with
| (q1, bindings1) -> begin
(

let uu____27231 = (

let uu____27236 = (FStar_List.filter (fun uu___131_27241 -> (match (uu___131_27241) with
| FStar_TypeChecker_Env.Binding_sig (uu____27242) -> begin
false
end
| uu____27249 -> begin
true
end)) bindings1)
in (encode_env_bindings env uu____27236))
in (match (uu____27231) with
| (env_decls, env1) -> begin
((

let uu____27267 = (((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTQuery"))))
in (match (uu____27267) with
| true -> begin
(

let uu____27268 = (FStar_Syntax_Print.term_to_string q1)
in (FStar_Util.print1 "Encoding query formula: %s\n" uu____27268))
end
| uu____27269 -> begin
()
end));
(

let uu____27270 = (encode_formula q1 env1)
in (match (uu____27270) with
| (phi, qdecls) -> begin
(

let uu____27291 = (

let uu____27296 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg uu____27296 phi))
in (match (uu____27291) with
| (labels, phi1) -> begin
(

let uu____27313 = (encode_labels labels)
in (match (uu____27313) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append env_decls (FStar_List.append label_prefix qdecls))
in (

let qry = (

let uu____27350 = (

let uu____27357 = (FStar_SMTEncoding_Util.mkNot phi1)
in (

let uu____27358 = (varops.mk_unique "@query")
in ((uu____27357), (FStar_Pervasives_Native.Some ("query")), (uu____27358))))
in (FStar_SMTEncoding_Util.mkAssume uu____27350))
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


let is_trivial : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun tcenv q -> (

let env = (

let uu____27377 = (FStar_TypeChecker_Env.current_module tcenv)
in (get_env uu____27377 tcenv))
in ((FStar_SMTEncoding_Z3.push "query");
(

let uu____27379 = (encode_formula q env)
in (match (uu____27379) with
| (f, uu____27385) -> begin
((FStar_SMTEncoding_Z3.pop "query");
(match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____27387) -> begin
true
end
| uu____27392 -> begin
false
end);
)
end));
)))




