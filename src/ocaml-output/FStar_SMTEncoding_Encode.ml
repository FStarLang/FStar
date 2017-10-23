
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


let vargs : 'Auu____71 'Auu____72 'Auu____73 . (('Auu____73, 'Auu____72) FStar_Util.either * 'Auu____71) Prims.list  ->  (('Auu____73, 'Auu____72) FStar_Util.either * 'Auu____71) Prims.list = (fun args -> (FStar_List.filter (fun uu___132_119 -> (match (uu___132_119) with
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

let uu___155_221 = a
in (

let uu____222 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = uu____222; FStar_Syntax_Syntax.index = uu___155_221.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___155_221.FStar_Syntax_Syntax.sort}))
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

let uu___156_1896 = x
in (

let uu____1897 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = uu____1897; FStar_Syntax_Syntax.index = uu___156_1896.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___156_1896.FStar_Syntax_Syntax.sort})))

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

let names1 = (FStar_All.pipe_right t_decls (FStar_List.collect (fun uu___133_2369 -> (match (uu___133_2369) with
| FStar_SMTEncoding_Term.Assume (a) -> begin
(a.FStar_SMTEncoding_Term.assumption_name)::[]
end
| uu____2373 -> begin
[]
end))))
in {cache_symbol_name = tsym; cache_symbol_arg_sorts = cvar_sorts; cache_symbol_decls = t_decls; cache_symbol_assumption_names = names1}))


let use_cache_entry : cache_entry  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun ce -> (FStar_SMTEncoding_Term.RetainAssumptions (ce.cache_symbol_assumption_names))::[])


let print_env : env_t  ->  Prims.string = (fun e -> (

let uu____2384 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun uu___134_2394 -> (match (uu___134_2394) with
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

let uu___157_2483 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = (env.depth + (Prims.parse_int "1")); tcenv = uu___157_2483.tcenv; warn = uu___157_2483.warn; cache = uu___157_2483.cache; nolabels = uu___157_2483.nolabels; use_zfuel_name = uu___157_2483.use_zfuel_name; encode_non_total_function_typ = uu___157_2483.encode_non_total_function_typ; current_module_name = uu___157_2483.current_module_name}))))))


let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let uu___158_2503 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = uu___158_2503.depth; tcenv = uu___158_2503.tcenv; warn = uu___158_2503.warn; cache = uu___158_2503.cache; nolabels = uu___158_2503.nolabels; use_zfuel_name = uu___158_2503.use_zfuel_name; encode_non_total_function_typ = uu___158_2503.encode_non_total_function_typ; current_module_name = uu___158_2503.current_module_name}))))))


let new_term_constant_from_string : env_t  ->  FStar_Syntax_Syntax.bv  ->  Prims.string  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x str -> (

let ysym = (varops.mk_unique str)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let uu___159_2527 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = uu___159_2527.depth; tcenv = uu___159_2527.tcenv; warn = uu___159_2527.warn; cache = uu___159_2527.cache; nolabels = uu___159_2527.nolabels; use_zfuel_name = uu___159_2527.use_zfuel_name; encode_non_total_function_typ = uu___159_2527.encode_non_total_function_typ; current_module_name = uu___159_2527.current_module_name}))))))


let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (

let uu___160_2540 = env
in {bindings = (Binding_var (((x), (t))))::env.bindings; depth = uu___160_2540.depth; tcenv = uu___160_2540.tcenv; warn = uu___160_2540.warn; cache = uu___160_2540.cache; nolabels = uu___160_2540.nolabels; use_zfuel_name = uu___160_2540.use_zfuel_name; encode_non_total_function_typ = uu___160_2540.encode_non_total_function_typ; current_module_name = uu___160_2540.current_module_name}))


let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let aux = (fun a' -> (lookup_binding env (fun uu___135_2566 -> (match (uu___135_2566) with
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

let uu___161_2639 = env
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
in {bindings = uu____2640; depth = uu___161_2639.depth; tcenv = uu___161_2639.tcenv; warn = uu___161_2639.warn; cache = uu___161_2639.cache; nolabels = uu___161_2639.nolabels; use_zfuel_name = uu___161_2639.use_zfuel_name; encode_non_total_function_typ = uu___161_2639.encode_non_total_function_typ; current_module_name = uu___161_2639.current_module_name}))
in ((fname), (ftok), (uu____2638))))))


let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option) FStar_Pervasives_Native.option = (fun env a -> (lookup_binding env (fun uu___136_2704 -> (match (uu___136_2704) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
FStar_Pervasives_Native.Some (((t1), (t2), (t3)))
end
| uu____2743 -> begin
FStar_Pervasives_Native.None
end))))


let contains_name : env_t  ->  Prims.string  ->  Prims.bool = (fun env s -> (

let uu____2762 = (lookup_binding env (fun uu___137_2770 -> (match (uu___137_2770) with
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

let uu___162_2892 = env
in {bindings = (Binding_fvar (((x), (fname), (ftok), (FStar_Pervasives_Native.None))))::env.bindings; depth = uu___162_2892.depth; tcenv = uu___162_2892.tcenv; warn = uu___162_2892.warn; cache = uu___162_2892.cache; nolabels = uu___162_2892.nolabels; use_zfuel_name = uu___162_2892.use_zfuel_name; encode_non_total_function_typ = uu___162_2892.encode_non_total_function_typ; current_module_name = uu___162_2892.current_module_name}))


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

let uu___163_2947 = env
in {bindings = (Binding_fvar (((x), (t1), (t2), (FStar_Pervasives_Native.Some (t3)))))::env.bindings; depth = uu___163_2947.depth; tcenv = uu___163_2947.tcenv; warn = uu___163_2947.warn; cache = uu___163_2947.cache; nolabels = uu___163_2947.nolabels; use_zfuel_name = uu___163_2947.use_zfuel_name; encode_non_total_function_typ = uu___163_2947.encode_non_total_function_typ; current_module_name = uu___163_2947.current_module_name}))
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


let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun uu___138_3201 -> (match (uu___138_3201) with
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
(((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_Tot_lid) || (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_GTot_lid)) || (FStar_List.existsb (fun uu___139_3528 -> (match (uu___139_3528) with
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
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
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


let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun uu___140_3636 -> (match (uu___140_3636) with
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


let as_function_typ : env_t  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (

let rec aux = (fun norm1 t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____3992) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_refine (uu____4005) -> begin
(

let uu____4012 = (FStar_Syntax_Util.unrefine t1)
in (aux true uu____4012))
end
| uu____4013 -> begin
(match (norm1) with
| true -> begin
(

let uu____4014 = (whnf env t1)
in (aux false uu____4014))
end
| uu____4015 -> begin
(

let uu____4016 = (

let uu____4017 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (

let uu____4018 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" uu____4017 uu____4018)))
in (failwith uu____4016))
end)
end)))
in (aux true t0)))


let curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun k -> (

let k1 = (FStar_Syntax_Subst.compress k)
in (match (k1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| uu____4050 -> begin
(

let uu____4051 = (FStar_Syntax_Syntax.mk_Total k1)
in (([]), (uu____4051)))
end)))


let is_arithmetic_primitive : 'Auu____4068 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  'Auu____4068 Prims.list  ->  Prims.bool = (fun head1 args -> (match (((head1.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____4088)::(uu____4089)::[]) -> begin
(((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Addition) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Subtraction)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Multiply)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Division)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Modulus))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____4093)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus)
end
| uu____4096 -> begin
false
end))


let isInteger : FStar_Syntax_Syntax.term'  ->  Prims.bool = (fun tm -> (match (tm) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (n1, FStar_Pervasives_Native.None)) -> begin
true
end
| uu____4118 -> begin
false
end))


let getInteger : FStar_Syntax_Syntax.term'  ->  Prims.int = (fun tm -> (match (tm) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (n1, FStar_Pervasives_Native.None)) -> begin
(FStar_Util.int_of_string n1)
end
| uu____4134 -> begin
(failwith "Expected an Integer term")
end))


let is_BitVector_primitive : 'Auu____4141 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____4141) Prims.list  ->  Prims.bool = (fun head1 args -> (match (((head1.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((sz_arg, uu____4180))::(uu____4181)::(uu____4182)::[]) -> begin
((((((((((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_and_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_xor_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_or_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_add_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_sub_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_shift_left_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_shift_right_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_udiv_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_mod_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_uext_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_mul_lid)) && (isInteger sz_arg.FStar_Syntax_Syntax.n))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((sz_arg, uu____4233))::(uu____4234)::[]) -> begin
(((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_to_nat_lid)) && (isInteger sz_arg.FStar_Syntax_Syntax.n))
end
| uu____4271 -> begin
false
end))


let rec encode_const : FStar_Const.sconst  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list) = (fun c env -> (match (c) with
| FStar_Const.Const_unit -> begin
((FStar_SMTEncoding_Term.mk_Term_unit), ([]))
end
| FStar_Const.Const_bool (true) -> begin
(

let uu____4478 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue)
in ((uu____4478), ([])))
end
| FStar_Const.Const_bool (false) -> begin
(

let uu____4481 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse)
in ((uu____4481), ([])))
end
| FStar_Const.Const_char (c1) -> begin
(

let uu____4485 = (

let uu____4486 = (

let uu____4493 = (

let uu____4496 = (

let uu____4497 = (FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c1))
in (FStar_SMTEncoding_Term.boxInt uu____4497))
in (uu____4496)::[])
in (("FStar.Char.Char"), (uu____4493)))
in (FStar_SMTEncoding_Util.mkApp uu____4486))
in ((uu____4485), ([])))
end
| FStar_Const.Const_int (i, FStar_Pervasives_Native.None) -> begin
(

let uu____4513 = (

let uu____4514 = (FStar_SMTEncoding_Util.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt uu____4514))
in ((uu____4513), ([])))
end
| FStar_Const.Const_int (repr, FStar_Pervasives_Native.Some (sw)) -> begin
(

let syntax_term = (FStar_ToSyntax_ToSyntax.desugar_machine_integer env.tcenv.FStar_TypeChecker_Env.dsenv repr sw FStar_Range.dummyRange)
in (encode_term syntax_term env))
end
| FStar_Const.Const_string (s, uu____4535) -> begin
(

let uu____4536 = (varops.string_const s)
in ((uu____4536), ([])))
end
| FStar_Const.Const_range (r) -> begin
((FStar_SMTEncoding_Term.mk_Range_const), ([]))
end
| FStar_Const.Const_effect -> begin
((FStar_SMTEncoding_Term.mk_Term_type), ([]))
end
| c1 -> begin
(

let uu____4545 = (

let uu____4546 = (FStar_Syntax_Print.const_to_string c1)
in (FStar_Util.format1 "Unhandled constant: %s" uu____4546))
in (failwith uu____4545))
end))
and encode_binders : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> ((

let uu____4575 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____4575) with
| true -> begin
(

let uu____4576 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" uu____4576))
end
| uu____4577 -> begin
()
end));
(

let uu____4578 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____4662 b -> (match (uu____4662) with
| (vars, guards, env1, decls, names1) -> begin
(

let uu____4741 = (

let x = (unmangle (FStar_Pervasives_Native.fst b))
in (

let uu____4757 = (gen_term_var env1 x)
in (match (uu____4757) with
| (xxsym, xx, env') -> begin
(

let uu____4781 = (

let uu____4786 = (norm env1 x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt uu____4786 env1 xx))
in (match (uu____4781) with
| (guard_x_t, decls') -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (guard_x_t), (env'), (decls'), (x))
end))
end)))
in (match (uu____4741) with
| (v1, g, env2, decls', n1) -> begin
(((v1)::vars), ((g)::guards), (env2), ((FStar_List.append decls decls')), ((n1)::names1))
end))
end)) (([]), ([]), (env), ([]), ([]))))
in (match (uu____4578) with
| (vars, guards, env1, decls, names1) -> begin
(((FStar_List.rev vars)), ((FStar_List.rev guards)), (env1), (decls), ((FStar_List.rev names1)))
end));
))
and encode_term_pred : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let uu____4945 = (encode_term t env)
in (match (uu____4945) with
| (t1, decls) -> begin
(

let uu____4956 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1)
in ((uu____4956), (decls)))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let uu____4967 = (encode_term t env)
in (match (uu____4967) with
| (t1, decls) -> begin
(match (fuel_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____4982 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t1)
in ((uu____4982), (decls)))
end
| FStar_Pervasives_Native.Some (f) -> begin
(

let uu____4984 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1)
in ((uu____4984), (decls)))
end)
end)))
and encode_arith_term : env_t  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.args  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun env head1 args_e -> (

let uu____4990 = (encode_args args_e env)
in (match (uu____4990) with
| (arg_tms, decls) -> begin
(

let head_fv = (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____5009 -> begin
(failwith "Impossible")
end)
in (

let unary = (fun arg_tms1 -> (

let uu____5018 = (FStar_List.hd arg_tms1)
in (FStar_SMTEncoding_Term.unboxInt uu____5018)))
in (

let binary = (fun arg_tms1 -> (

let uu____5031 = (

let uu____5032 = (FStar_List.hd arg_tms1)
in (FStar_SMTEncoding_Term.unboxInt uu____5032))
in (

let uu____5033 = (

let uu____5034 = (

let uu____5035 = (FStar_List.tl arg_tms1)
in (FStar_List.hd uu____5035))
in (FStar_SMTEncoding_Term.unboxInt uu____5034))
in ((uu____5031), (uu____5033)))))
in (

let mk_default = (fun uu____5041 -> (

let uu____5042 = (lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name)
in (match (uu____5042) with
| (fname, fuel_args) -> begin
(FStar_SMTEncoding_Util.mkApp' ((fname), ((FStar_List.append fuel_args arg_tms))))
end)))
in (

let mk_l = (fun op mk_args ts -> (

let uu____5093 = (FStar_Options.smtencoding_l_arith_native ())
in (match (uu____5093) with
| true -> begin
(

let uu____5094 = (

let uu____5095 = (mk_args ts)
in (op uu____5095))
in (FStar_All.pipe_right uu____5094 FStar_SMTEncoding_Term.boxInt))
end
| uu____5096 -> begin
(mk_default ())
end)))
in (

let mk_nl = (fun nm op ts -> (

let uu____5124 = (FStar_Options.smtencoding_nl_arith_wrapped ())
in (match (uu____5124) with
| true -> begin
(

let uu____5125 = (binary ts)
in (match (uu____5125) with
| (t1, t2) -> begin
(

let uu____5132 = (FStar_SMTEncoding_Util.mkApp ((nm), ((t1)::(t2)::[])))
in (FStar_All.pipe_right uu____5132 FStar_SMTEncoding_Term.boxInt))
end))
end
| uu____5135 -> begin
(

let uu____5136 = (FStar_Options.smtencoding_nl_arith_native ())
in (match (uu____5136) with
| true -> begin
(

let uu____5137 = (op (binary ts))
in (FStar_All.pipe_right uu____5137 FStar_SMTEncoding_Term.boxInt))
end
| uu____5138 -> begin
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

let uu____5268 = (

let uu____5277 = (FStar_List.tryFind (fun uu____5299 -> (match (uu____5299) with
| (l, uu____5309) -> begin
(FStar_Syntax_Syntax.fv_eq_lid head_fv l)
end)) ops)
in (FStar_All.pipe_right uu____5277 FStar_Util.must))
in (match (uu____5268) with
| (uu____5348, op) -> begin
(

let uu____5358 = (op arg_tms)
in ((uu____5358), (decls)))
end)))))))))))))))
end)))
and encode_BitVector_term : env_t  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.arg Prims.list  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list) = (fun env head1 args_e -> (

let uu____5366 = (FStar_List.hd args_e)
in (match (uu____5366) with
| (tm_sz, uu____5374) -> begin
(

let sz = (getInteger tm_sz.FStar_Syntax_Syntax.n)
in (

let sz_key = (FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz))
in (

let sz_decls = (

let uu____5384 = (FStar_Util.smap_try_find env.cache sz_key)
in (match (uu____5384) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
[]
end
| FStar_Pervasives_Native.None -> begin
(

let t_decls = (FStar_SMTEncoding_Term.mkBvConstructor sz)
in ((

let uu____5392 = (mk_cache_entry env "" [] [])
in (FStar_Util.smap_add env.cache sz_key uu____5392));
t_decls;
))
end))
in (

let uu____5393 = (match (((head1.FStar_Syntax_Syntax.n), (args_e))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____5413)::((sz_arg, uu____5415))::(uu____5416)::[]) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_uext_lid) && (isInteger sz_arg.FStar_Syntax_Syntax.n)) -> begin
(

let uu____5465 = (

let uu____5468 = (FStar_List.tail args_e)
in (FStar_List.tail uu____5468))
in (

let uu____5471 = (

let uu____5474 = (getInteger sz_arg.FStar_Syntax_Syntax.n)
in FStar_Pervasives_Native.Some (uu____5474))
in ((uu____5465), (uu____5471))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____5480)::((sz_arg, uu____5482))::(uu____5483)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_uext_lid) -> begin
(

let uu____5532 = (

let uu____5533 = (FStar_Syntax_Print.term_to_string sz_arg)
in (FStar_Util.format1 "Not a constant bitvector extend size: %s" uu____5533))
in (failwith uu____5532))
end
| uu____5542 -> begin
(

let uu____5549 = (FStar_List.tail args_e)
in ((uu____5549), (FStar_Pervasives_Native.None)))
end)
in (match (uu____5393) with
| (arg_tms, ext_sz) -> begin
(

let uu____5572 = (encode_args arg_tms env)
in (match (uu____5572) with
| (arg_tms1, decls) -> begin
(

let head_fv = (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____5593 -> begin
(failwith "Impossible")
end)
in (

let unary = (fun arg_tms2 -> (

let uu____5602 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____5602)))
in (

let unary_arith = (fun arg_tms2 -> (

let uu____5611 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxInt uu____5611)))
in (

let binary = (fun arg_tms2 -> (

let uu____5624 = (

let uu____5625 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____5625))
in (

let uu____5626 = (

let uu____5627 = (

let uu____5628 = (FStar_List.tl arg_tms2)
in (FStar_List.hd uu____5628))
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____5627))
in ((uu____5624), (uu____5626)))))
in (

let binary_arith = (fun arg_tms2 -> (

let uu____5643 = (

let uu____5644 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____5644))
in (

let uu____5645 = (

let uu____5646 = (

let uu____5647 = (FStar_List.tl arg_tms2)
in (FStar_List.hd uu____5647))
in (FStar_SMTEncoding_Term.unboxInt uu____5646))
in ((uu____5643), (uu____5645)))))
in (

let mk_bv = (fun op mk_args resBox ts -> (

let uu____5696 = (

let uu____5697 = (mk_args ts)
in (op uu____5697))
in (FStar_All.pipe_right uu____5696 resBox)))
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

let uu____5805 = (

let uu____5808 = (match (ext_sz) with
| FStar_Pervasives_Native.Some (x) -> begin
x
end
| FStar_Pervasives_Native.None -> begin
(failwith "impossible")
end)
in (FStar_SMTEncoding_Util.mkBvUext uu____5808))
in (

let uu____5810 = (

let uu____5813 = (

let uu____5814 = (match (ext_sz) with
| FStar_Pervasives_Native.Some (x) -> begin
x
end
| FStar_Pervasives_Native.None -> begin
(failwith "impossible")
end)
in (sz + uu____5814))
in (FStar_SMTEncoding_Term.boxBitVec uu____5813))
in (mk_bv uu____5805 unary uu____5810 arg_tms2))))
in (

let to_int = (mk_bv FStar_SMTEncoding_Util.mkBvToNat unary FStar_SMTEncoding_Term.boxInt)
in (

let bv_to = (mk_bv (FStar_SMTEncoding_Util.mkNatToBv sz) unary_arith (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let ops = (((FStar_Parser_Const.bv_and_lid), (bv_and)))::(((FStar_Parser_Const.bv_xor_lid), (bv_xor)))::(((FStar_Parser_Const.bv_or_lid), (bv_or)))::(((FStar_Parser_Const.bv_add_lid), (bv_add)))::(((FStar_Parser_Const.bv_sub_lid), (bv_sub)))::(((FStar_Parser_Const.bv_shift_left_lid), (bv_shl)))::(((FStar_Parser_Const.bv_shift_right_lid), (bv_shr)))::(((FStar_Parser_Const.bv_udiv_lid), (bv_udiv)))::(((FStar_Parser_Const.bv_mod_lid), (bv_mod)))::(((FStar_Parser_Const.bv_mul_lid), (bv_mul)))::(((FStar_Parser_Const.bv_ult_lid), (bv_ult)))::(((FStar_Parser_Const.bv_uext_lid), (bv_uext)))::(((FStar_Parser_Const.bv_to_nat_lid), (to_int)))::(((FStar_Parser_Const.nat_to_bv_lid), (bv_to)))::[]
in (

let uu____6013 = (

let uu____6022 = (FStar_List.tryFind (fun uu____6044 -> (match (uu____6044) with
| (l, uu____6054) -> begin
(FStar_Syntax_Syntax.fv_eq_lid head_fv l)
end)) ops)
in (FStar_All.pipe_right uu____6022 FStar_Util.must))
in (match (uu____6013) with
| (uu____6095, op) -> begin
(

let uu____6105 = (op arg_tms1)
in ((uu____6105), ((FStar_List.append sz_decls decls))))
end)))))))))))))))))))))))
end))
end)))))
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let t0 = (FStar_Syntax_Subst.compress t)
in ((

let uu____6116 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____6116) with
| true -> begin
(

let uu____6117 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____6118 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____6119 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" uu____6117 uu____6118 uu____6119))))
end
| uu____6120 -> begin
()
end));
(match (t0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____6125) -> begin
(

let uu____6150 = (

let uu____6151 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____6152 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____6153 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____6154 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6151 uu____6152 uu____6153 uu____6154)))))
in (failwith uu____6150))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____6159 = (

let uu____6160 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____6161 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____6162 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____6163 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6160 uu____6161 uu____6162 uu____6163)))))
in (failwith uu____6159))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____6169 = (

let uu____6170 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" uu____6170))
in (failwith uu____6169))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, k, uu____6177) -> begin
(encode_term t1 env)
end
| FStar_Syntax_Syntax.Tm_meta ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown; FStar_Syntax_Syntax.pos = uu____6218; FStar_Syntax_Syntax.vars = uu____6219}, FStar_Syntax_Syntax.Meta_alien (obj, desc, ty)) -> begin
(

let tsym = (

let uu____6236 = (varops.fresh "t")
in ((uu____6236), (FStar_SMTEncoding_Term.Term_sort)))
in (

let t1 = (FStar_SMTEncoding_Util.mkFreeV tsym)
in (

let decl = (

let uu____6239 = (

let uu____6250 = (

let uu____6253 = (FStar_Util.format1 "alien term (%s)" desc)
in FStar_Pervasives_Native.Some (uu____6253))
in (((FStar_Pervasives_Native.fst tsym)), ([]), (FStar_SMTEncoding_Term.Term_sort), (uu____6250)))
in FStar_SMTEncoding_Term.DeclFun (uu____6239))
in ((t1), ((decl)::[])))))
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____6261) -> begin
(encode_term t1 env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t1 = (lookup_term_var env x)
in ((t1), ([])))
end
| FStar_Syntax_Syntax.Tm_fvar (v1) -> begin
(

let uu____6271 = (lookup_free_var env v1.FStar_Syntax_Syntax.fv_name)
in ((uu____6271), ([])))
end
| FStar_Syntax_Syntax.Tm_type (uu____6274) -> begin
((FStar_SMTEncoding_Term.mk_Term_type), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____6278) -> begin
(encode_term t1 env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(encode_const c env)
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let module_name = env.current_module_name
in (

let uu____6303 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____6303) with
| (binders1, res) -> begin
(

let uu____6314 = ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res))
in (match (uu____6314) with
| true -> begin
(

let uu____6319 = (encode_binders FStar_Pervasives_Native.None binders1 env)
in (match (uu____6319) with
| (vars, guards, env', decls, uu____6344) -> begin
(

let fsym = (

let uu____6362 = (varops.fresh "f")
in ((uu____6362), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV fsym)
in (

let app = (mk_Apply f vars)
in (

let uu____6365 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post (

let uu___164_6374 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___164_6374.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___164_6374.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___164_6374.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___164_6374.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___164_6374.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___164_6374.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___164_6374.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___164_6374.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___164_6374.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___164_6374.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___164_6374.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___164_6374.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___164_6374.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___164_6374.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___164_6374.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___164_6374.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___164_6374.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___164_6374.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___164_6374.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___164_6374.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___164_6374.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___164_6374.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___164_6374.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___164_6374.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___164_6374.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___164_6374.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___164_6374.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___164_6374.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___164_6374.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___164_6374.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___164_6374.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___164_6374.FStar_TypeChecker_Env.dsenv}) res)
in (match (uu____6365) with
| (pre_opt, res_t) -> begin
(

let uu____6385 = (encode_term_pred FStar_Pervasives_Native.None res_t env' app)
in (match (uu____6385) with
| (res_pred, decls') -> begin
(

let uu____6396 = (match (pre_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____6409 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____6409), ([])))
end
| FStar_Pervasives_Native.Some (pre) -> begin
(

let uu____6413 = (encode_formula pre env')
in (match (uu____6413) with
| (guard, decls0) -> begin
(

let uu____6426 = (FStar_SMTEncoding_Util.mk_and_l ((guard)::guards))
in ((uu____6426), (decls0)))
end))
end)
in (match (uu____6396) with
| (guards1, guard_decls) -> begin
(

let t_interp = (

let uu____6438 = (

let uu____6449 = (FStar_SMTEncoding_Util.mkImp ((guards1), (res_pred)))
in ((((app)::[])::[]), (vars), (uu____6449)))
in (FStar_SMTEncoding_Util.mkForall uu____6438))
in (

let cvars = (

let uu____6467 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right uu____6467 (FStar_List.filter (fun uu____6481 -> (match (uu____6481) with
| (x, uu____6487) -> begin
(Prims.op_disEquality x (FStar_Pervasives_Native.fst fsym))
end)))))
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), ((fsym)::cvars), (t_interp)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____6506 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____6506) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
(

let uu____6514 = (

let uu____6515 = (

let uu____6522 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((cache_entry.cache_symbol_name), (uu____6522)))
in (FStar_SMTEncoding_Util.mkApp uu____6515))
in ((uu____6514), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append guard_decls (use_cache_entry cache_entry)))))))
end
| FStar_Pervasives_Native.None -> begin
(

let tsym = (

let uu____6542 = (

let uu____6543 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_arrow_" uu____6543))
in (varops.mk_unique uu____6542))
in (

let cvar_sorts = (FStar_List.map FStar_Pervasives_Native.snd cvars)
in (

let caption = (

let uu____6554 = (FStar_Options.log_queries ())
in (match (uu____6554) with
| true -> begin
(

let uu____6557 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in FStar_Pervasives_Native.Some (uu____6557))
end
| uu____6558 -> begin
FStar_Pervasives_Native.None
end))
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (caption)))
in (

let t1 = (

let uu____6565 = (

let uu____6572 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((tsym), (uu____6572)))
in (FStar_SMTEncoding_Util.mkApp uu____6565))
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t1 FStar_SMTEncoding_Term.mk_Term_type)
in (

let k_assumption = (

let a_name = (Prims.strcat "kinding_" tsym)
in (

let uu____6584 = (

let uu____6591 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((uu____6591), (FStar_Pervasives_Native.Some (a_name)), (a_name)))
in (FStar_SMTEncoding_Util.mkAssume uu____6584)))
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t1)
in (

let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t1)
in (

let pre_typing = (

let a_name = (Prims.strcat "pre_typing_" tsym)
in (

let uu____6612 = (

let uu____6619 = (

let uu____6620 = (

let uu____6631 = (

let uu____6632 = (

let uu____6637 = (

let uu____6638 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____6638))
in ((f_has_t), (uu____6637)))
in (FStar_SMTEncoding_Util.mkImp uu____6632))
in ((((f_has_t)::[])::[]), ((fsym)::cvars), (uu____6631)))
in (mkForall_fuel uu____6620))
in ((uu____6619), (FStar_Pervasives_Native.Some ("pre-typing for functions")), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____6612)))
in (

let t_interp1 = (

let a_name = (Prims.strcat "interpretation_" tsym)
in (

let uu____6661 = (

let uu____6668 = (

let uu____6669 = (

let uu____6680 = (FStar_SMTEncoding_Util.mkIff ((f_has_t_z), (t_interp)))
in ((((f_has_t_z)::[])::[]), ((fsym)::cvars), (uu____6680)))
in (FStar_SMTEncoding_Util.mkForall uu____6669))
in ((uu____6668), (FStar_Pervasives_Native.Some (a_name)), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____6661)))
in (

let t_decls = (FStar_List.append ((tdecl)::decls) (FStar_List.append decls' (FStar_List.append guard_decls ((k_assumption)::(pre_typing)::(t_interp1)::[]))))
in ((

let uu____6705 = (mk_cache_entry env tsym cvar_sorts t_decls)
in (FStar_Util.smap_add env.cache tkey_hash uu____6705));
((t1), (t_decls));
)))))))))))))
end))))))
end))
end))
end)))))
end))
end
| uu____6708 -> begin
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

let uu____6720 = (

let uu____6727 = (FStar_SMTEncoding_Term.mk_HasType t1 FStar_SMTEncoding_Term.mk_Term_type)
in ((uu____6727), (FStar_Pervasives_Native.Some ("Typing for non-total arrows")), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____6720)))
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

let uu____6739 = (

let uu____6746 = (

let uu____6747 = (

let uu____6758 = (

let uu____6759 = (

let uu____6764 = (

let uu____6765 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____6765))
in ((f_has_t), (uu____6764)))
in (FStar_SMTEncoding_Util.mkImp uu____6759))
in ((((f_has_t)::[])::[]), ((fsym)::[]), (uu____6758)))
in (mkForall_fuel uu____6747))
in ((uu____6746), (FStar_Pervasives_Native.Some (a_name)), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____6739)))
in ((t1), ((tdecl)::(t_kinding)::(t_interp)::[]))))))))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (uu____6792) -> begin
(

let uu____6799 = (

let uu____6804 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)
in (match (uu____6804) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.pos = uu____6811; FStar_Syntax_Syntax.vars = uu____6812} -> begin
(

let uu____6819 = (FStar_Syntax_Subst.open_term ((((x), (FStar_Pervasives_Native.None)))::[]) f)
in (match (uu____6819) with
| (b, f1) -> begin
(

let uu____6844 = (

let uu____6845 = (FStar_List.hd b)
in (FStar_Pervasives_Native.fst uu____6845))
in ((uu____6844), (f1)))
end))
end
| uu____6854 -> begin
(failwith "impossible")
end))
in (match (uu____6799) with
| (x, f) -> begin
(

let uu____6865 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (uu____6865) with
| (base_t, decls) -> begin
(

let uu____6876 = (gen_term_var env x)
in (match (uu____6876) with
| (x1, xtm, env') -> begin
(

let uu____6890 = (encode_formula f env')
in (match (uu____6890) with
| (refinement, decls') -> begin
(

let uu____6901 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____6901) with
| (fsym, fterm) -> begin
(

let tm_has_type_with_fuel = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (FStar_Pervasives_Native.Some (fterm)) xtm base_t)
in (

let encoding = (FStar_SMTEncoding_Util.mkAnd ((tm_has_type_with_fuel), (refinement)))
in (

let cvars = (

let uu____6917 = (

let uu____6920 = (FStar_SMTEncoding_Term.free_variables refinement)
in (

let uu____6927 = (FStar_SMTEncoding_Term.free_variables tm_has_type_with_fuel)
in (FStar_List.append uu____6920 uu____6927)))
in (FStar_Util.remove_dups FStar_SMTEncoding_Term.fv_eq uu____6917))
in (

let cvars1 = (FStar_All.pipe_right cvars (FStar_List.filter (fun uu____6960 -> (match (uu____6960) with
| (y, uu____6966) -> begin
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

let uu____6999 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____6999) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
(

let uu____7007 = (

let uu____7008 = (

let uu____7015 = (FStar_All.pipe_right cvars1 (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((cache_entry.cache_symbol_name), (uu____7015)))
in (FStar_SMTEncoding_Util.mkApp uu____7008))
in ((uu____7007), ((FStar_List.append decls (FStar_List.append decls' (use_cache_entry cache_entry))))))
end
| FStar_Pervasives_Native.None -> begin
(

let module_name = env.current_module_name
in (

let tsym = (

let uu____7036 = (

let uu____7037 = (

let uu____7038 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "_Tm_refine_" uu____7038))
in (Prims.strcat module_name uu____7037))
in (varops.mk_unique uu____7036))
in (

let cvar_sorts = (FStar_List.map FStar_Pervasives_Native.snd cvars1)
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let t1 = (

let uu____7052 = (

let uu____7059 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars1)
in ((tsym), (uu____7059)))
in (FStar_SMTEncoding_Util.mkApp uu____7052))
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

let uu____7074 = (

let uu____7081 = (

let uu____7082 = (

let uu____7093 = (FStar_SMTEncoding_Util.mkIff ((t_haseq_ref), (t_haseq_base)))
in ((((t_haseq_ref)::[])::[]), (cvars1), (uu____7093)))
in (FStar_SMTEncoding_Util.mkForall uu____7082))
in ((uu____7081), (FStar_Pervasives_Native.Some ((Prims.strcat "haseq for " tsym))), ((Prims.strcat "haseq" tsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____7074))
in (

let t_kinding = (

let uu____7111 = (

let uu____7118 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars1), (t_has_kind)))
in ((uu____7118), (FStar_Pervasives_Native.Some ("refinement kinding")), ((Prims.strcat "refinement_kinding_" tsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____7111))
in (

let t_interp = (

let uu____7136 = (

let uu____7143 = (

let uu____7144 = (

let uu____7155 = (FStar_SMTEncoding_Util.mkIff ((x_has_t), (encoding)))
in ((((x_has_t)::[])::[]), ((ffv)::(xfv)::cvars1), (uu____7155)))
in (FStar_SMTEncoding_Util.mkForall uu____7144))
in (

let uu____7178 = (

let uu____7181 = (FStar_Syntax_Print.term_to_string t0)
in FStar_Pervasives_Native.Some (uu____7181))
in ((uu____7143), (uu____7178), ((Prims.strcat "refinement_interpretation_" tsym)))))
in (FStar_SMTEncoding_Util.mkAssume uu____7136))
in (

let t_decls = (FStar_List.append decls (FStar_List.append decls' ((tdecl)::(t_kinding)::(t_interp)::(t_haseq1)::[])))
in ((

let uu____7188 = (mk_cache_entry env tsym cvar_sorts t_decls)
in (FStar_Util.smap_add env.cache tkey_hash uu____7188));
((t1), (t_decls));
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

let uu____7218 = (FStar_Syntax_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Util.mk_Term_uvar uu____7218))
in (

let uu____7219 = (encode_term_pred FStar_Pervasives_Native.None k env ttm)
in (match (uu____7219) with
| (t_has_k, decls) -> begin
(

let d = (

let uu____7231 = (

let uu____7238 = (

let uu____7239 = (

let uu____7240 = (

let uu____7241 = (FStar_Syntax_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____7241))
in (FStar_Util.format1 "uvar_typing_%s" uu____7240))
in (varops.mk_unique uu____7239))
in ((t_has_k), (FStar_Pervasives_Native.Some ("Uvar typing")), (uu____7238)))
in (FStar_SMTEncoding_Util.mkAssume uu____7231))
in ((ttm), ((FStar_List.append decls ((d)::[])))))
end)))
end
| FStar_Syntax_Syntax.Tm_app (uu____7246) -> begin
(

let uu____7261 = (FStar_Syntax_Util.head_and_args t0)
in (match (uu____7261) with
| (head1, args_e) -> begin
(

let uu____7302 = (

let uu____7315 = (

let uu____7316 = (FStar_Syntax_Subst.compress head1)
in uu____7316.FStar_Syntax_Syntax.n)
in ((uu____7315), (args_e)))
in (match (uu____7302) with
| uu____7331 when (head_redex env head1) -> begin
(

let uu____7344 = (whnf env t)
in (encode_term uu____7344 env))
end
| uu____7345 when (is_arithmetic_primitive head1 args_e) -> begin
(encode_arith_term env head1 args_e)
end
| uu____7364 when (is_BitVector_primitive head1 args_e) -> begin
(encode_BitVector_term env head1 args_e)
end
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____7378; FStar_Syntax_Syntax.vars = uu____7379}, uu____7380), (uu____7381)::((v1, uu____7383))::((v2, uu____7385))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.lexcons_lid) -> begin
(

let uu____7436 = (encode_term v1 env)
in (match (uu____7436) with
| (v11, decls1) -> begin
(

let uu____7447 = (encode_term v2 env)
in (match (uu____7447) with
| (v21, decls2) -> begin
(

let uu____7458 = (FStar_SMTEncoding_Util.mk_LexCons v11 v21)
in ((uu____7458), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____7462)::((v1, uu____7464))::((v2, uu____7466))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.lexcons_lid) -> begin
(

let uu____7513 = (encode_term v1 env)
in (match (uu____7513) with
| (v11, decls1) -> begin
(

let uu____7524 = (encode_term v2 env)
in (match (uu____7524) with
| (v21, decls2) -> begin
(

let uu____7535 = (FStar_SMTEncoding_Util.mk_LexCons v11 v21)
in ((uu____7535), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), uu____7538) -> begin
(

let e0 = (

let uu____7556 = (FStar_List.hd args_e)
in (FStar_TypeChecker_Util.reify_body_with_arg env.tcenv head1 uu____7556))
in ((

let uu____7564 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____7564) with
| true -> begin
(

let uu____7565 = (FStar_Syntax_Print.term_to_string e0)
in (FStar_Util.print1 "Result of normalization %s\n" uu____7565))
end
| uu____7566 -> begin
()
end));
(

let e = (

let uu____7570 = (

let uu____7571 = (FStar_TypeChecker_Util.remove_reify e0)
in (

let uu____7572 = (FStar_List.tl args_e)
in (FStar_Syntax_Syntax.mk_Tm_app uu____7571 uu____7572)))
in (uu____7570 FStar_Pervasives_Native.None t0.FStar_Syntax_Syntax.pos))
in (encode_term e env));
))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____7581)), ((arg, uu____7583))::[]) -> begin
(encode_term arg env)
end
| uu____7608 -> begin
(

let uu____7621 = (encode_args args_e env)
in (match (uu____7621) with
| (args, decls) -> begin
(

let encode_partial_app = (fun ht_opt -> (

let uu____7676 = (encode_term head1 env)
in (match (uu____7676) with
| (head2, decls') -> begin
(

let app_tm = (mk_Apply_args head2 args)
in (match (ht_opt) with
| FStar_Pervasives_Native.None -> begin
((app_tm), ((FStar_List.append decls decls')))
end
| FStar_Pervasives_Native.Some (formals, c) -> begin
(

let uu____7740 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (uu____7740) with
| (formals1, rest) -> begin
(

let subst1 = (FStar_List.map2 (fun uu____7818 uu____7819 -> (match (((uu____7818), (uu____7819))) with
| ((bv, uu____7841), (a, uu____7843)) -> begin
FStar_Syntax_Syntax.NT (((bv), (a)))
end)) formals1 args_e)
in (

let ty = (

let uu____7861 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right uu____7861 (FStar_Syntax_Subst.subst subst1)))
in (

let uu____7866 = (encode_term_pred FStar_Pervasives_Native.None ty env app_tm)
in (match (uu____7866) with
| (has_type, decls'') -> begin
(

let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (

let e_typing = (

let uu____7881 = (

let uu____7888 = (FStar_SMTEncoding_Util.mkForall ((((has_type)::[])::[]), (cvars), (has_type)))
in (

let uu____7897 = (

let uu____7898 = (

let uu____7899 = (

let uu____7900 = (FStar_SMTEncoding_Term.hash_of_term app_tm)
in (FStar_Util.digest_of_string uu____7900))
in (Prims.strcat "partial_app_typing_" uu____7899))
in (varops.mk_unique uu____7898))
in ((uu____7888), (FStar_Pervasives_Native.Some ("Partial app typing")), (uu____7897))))
in (FStar_SMTEncoding_Util.mkAssume uu____7881))
in ((app_tm), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' ((e_typing)::[]))))))))
end))))
end))
end))
end)))
in (

let encode_full_app = (fun fv -> (

let uu____7917 = (lookup_free_var_sym env fv)
in (match (uu____7917) with
| (fname, fuel_args) -> begin
(

let tm = (FStar_SMTEncoding_Util.mkApp' ((fname), ((FStar_List.append fuel_args args))))
in ((tm), (decls)))
end)))
in (

let head2 = (FStar_Syntax_Subst.compress head1)
in (

let head_type = (match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (x); FStar_Syntax_Syntax.pos = uu____7948; FStar_Syntax_Syntax.vars = uu____7949}, uu____7950) -> begin
FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____7961; FStar_Syntax_Syntax.vars = uu____7962}, uu____7963) -> begin
(

let uu____7968 = (

let uu____7969 = (

let uu____7974 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____7974 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____7969 FStar_Pervasives_Native.snd))
in FStar_Pervasives_Native.Some (uu____7968))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____8004 = (

let uu____8005 = (

let uu____8010 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____8010 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____8005 FStar_Pervasives_Native.snd))
in FStar_Pervasives_Native.Some (uu____8004))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____8039, (FStar_Util.Inl (t1), uu____8041), uu____8042) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____8091, (FStar_Util.Inr (c), uu____8093), uu____8094) -> begin
FStar_Pervasives_Native.Some ((FStar_Syntax_Util.comp_result c))
end
| uu____8143 -> begin
FStar_Pervasives_Native.None
end)
in (match (head_type) with
| FStar_Pervasives_Native.None -> begin
(encode_partial_app FStar_Pervasives_Native.None)
end
| FStar_Pervasives_Native.Some (head_type1) -> begin
(

let head_type2 = (

let uu____8170 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type1)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine uu____8170))
in (

let uu____8171 = (curried_arrow_formals_comp head_type2)
in (match (uu____8171) with
| (formals, c) -> begin
(match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____8187; FStar_Syntax_Syntax.vars = uu____8188}, uu____8189) when (Prims.op_Equality (FStar_List.length formals) (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (Prims.op_Equality (FStar_List.length formals) (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| uu____8203 -> begin
(match (((FStar_List.length formals) > (FStar_List.length args))) with
| true -> begin
(encode_partial_app (FStar_Pervasives_Native.Some (((formals), (c)))))
end
| uu____8216 -> begin
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

let uu____8252 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____8252) with
| (bs1, body1, opening) -> begin
(

let fallback = (fun uu____8275 -> (

let f = (varops.fresh "Tm_abs")
in (

let decl = FStar_SMTEncoding_Term.DeclFun (((f), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Imprecise function encoding"))))
in (

let uu____8282 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in ((uu____8282), ((decl)::[]))))))
in (

let is_impure = (fun rc -> (

let uu____8289 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv rc.FStar_Syntax_Syntax.residual_effect)
in (FStar_All.pipe_right uu____8289 Prims.op_Negation)))
in (

let codomain_eff = (fun rc -> (

let res_typ = (match (rc.FStar_Syntax_Syntax.residual_typ) with
| FStar_Pervasives_Native.None -> begin
(

let uu____8299 = (FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange [] FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right uu____8299 FStar_Pervasives_Native.fst))
end
| FStar_Pervasives_Native.Some (t1) -> begin
t1
end)
in (match ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_Tot_lid)) with
| true -> begin
(

let uu____8319 = (FStar_Syntax_Syntax.mk_Total res_typ)
in FStar_Pervasives_Native.Some (uu____8319))
end
| uu____8320 -> begin
(match ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_GTot_lid)) with
| true -> begin
(

let uu____8323 = (FStar_Syntax_Syntax.mk_GTotal res_typ)
in FStar_Pervasives_Native.Some (uu____8323))
end
| uu____8324 -> begin
FStar_Pervasives_Native.None
end)
end)))
in (match (lopt) with
| FStar_Pervasives_Native.None -> begin
((

let uu____8330 = (

let uu____8331 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)" uu____8331))
in (FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____8330));
(fallback ());
)
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____8333 = ((is_impure rc) && (

let uu____8335 = (FStar_TypeChecker_Env.is_reifiable env.tcenv rc)
in (not (uu____8335))))
in (match (uu____8333) with
| true -> begin
(fallback ())
end
| uu____8340 -> begin
(

let cache_size = (FStar_Util.smap_size env.cache)
in (

let uu____8342 = (encode_binders FStar_Pervasives_Native.None bs1 env)
in (match (uu____8342) with
| (vars, guards, envbody, decls, uu____8367) -> begin
(

let body2 = (

let uu____8381 = (FStar_TypeChecker_Env.is_reifiable env.tcenv rc)
in (match (uu____8381) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env.tcenv body1)
end
| uu____8382 -> begin
body1
end))
in (

let uu____8383 = (encode_term body2 envbody)
in (match (uu____8383) with
| (body3, decls') -> begin
(

let uu____8394 = (

let uu____8403 = (codomain_eff rc)
in (match (uu____8403) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), ([]))
end
| FStar_Pervasives_Native.Some (c) -> begin
(

let tfun = (FStar_Syntax_Util.arrow bs1 c)
in (

let uu____8422 = (encode_term tfun env)
in (match (uu____8422) with
| (t1, decls1) -> begin
((FStar_Pervasives_Native.Some (t1)), (decls1))
end)))
end))
in (match (uu____8394) with
| (arrow_t_opt, decls'') -> begin
(

let key_body = (

let uu____8454 = (

let uu____8465 = (

let uu____8466 = (

let uu____8471 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____8471), (body3)))
in (FStar_SMTEncoding_Util.mkImp uu____8466))
in (([]), (vars), (uu____8465)))
in (FStar_SMTEncoding_Util.mkForall uu____8454))
in (

let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (

let cvars1 = (match (arrow_t_opt) with
| FStar_Pervasives_Native.None -> begin
cvars
end
| FStar_Pervasives_Native.Some (t1) -> begin
(

let uu____8483 = (

let uu____8486 = (FStar_SMTEncoding_Term.free_variables t1)
in (FStar_List.append uu____8486 cvars))
in (FStar_Util.remove_dups FStar_SMTEncoding_Term.fv_eq uu____8483))
end)
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), (cvars1), (key_body)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____8505 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____8505) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
(

let uu____8513 = (

let uu____8514 = (

let uu____8521 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars1)
in ((cache_entry.cache_symbol_name), (uu____8521)))
in (FStar_SMTEncoding_Util.mkApp uu____8514))
in ((uu____8513), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' (use_cache_entry cache_entry)))))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____8532 = (is_an_eta_expansion env vars body3)
in (match (uu____8532) with
| FStar_Pervasives_Native.Some (t1) -> begin
(

let decls1 = (

let uu____8543 = (

let uu____8544 = (FStar_Util.smap_size env.cache)
in (Prims.op_Equality uu____8544 cache_size))
in (match (uu____8543) with
| true -> begin
[]
end
| uu____8547 -> begin
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

let uu____8560 = (

let uu____8561 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_abs_" uu____8561))
in (varops.mk_unique uu____8560))
in (Prims.strcat module_name (Prims.strcat "_" fsym))))
in (

let fdecl = FStar_SMTEncoding_Term.DeclFun (((fsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let f = (

let uu____8568 = (

let uu____8575 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars1)
in ((fsym), (uu____8575)))
in (FStar_SMTEncoding_Util.mkApp uu____8568))
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

let uu____8593 = (

let uu____8594 = (

let uu____8601 = (FStar_SMTEncoding_Util.mkForall ((((f)::[])::[]), (cvars1), (f_has_t)))
in ((uu____8601), (FStar_Pervasives_Native.Some (a_name)), (a_name)))
in (FStar_SMTEncoding_Util.mkAssume uu____8594))
in (uu____8593)::[])))
end)
in (

let interp_f = (

let a_name = (Prims.strcat "interpretation_" fsym)
in (

let uu____8614 = (

let uu____8621 = (

let uu____8622 = (

let uu____8633 = (FStar_SMTEncoding_Util.mkEq ((app), (body3)))
in ((((app)::[])::[]), ((FStar_List.append vars cvars1)), (uu____8633)))
in (FStar_SMTEncoding_Util.mkForall uu____8622))
in ((uu____8621), (FStar_Pervasives_Native.Some (a_name)), (a_name)))
in (FStar_SMTEncoding_Util.mkAssume uu____8614)))
in (

let f_decls = (FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' (FStar_List.append ((fdecl)::typing_f) ((interp_f)::[])))))
in ((

let uu____8650 = (mk_cache_entry env fsym cvar_sorts f_decls)
in (FStar_Util.smap_add env.cache tkey_hash uu____8650));
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
| FStar_Syntax_Syntax.Tm_let ((uu____8653, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____8654); FStar_Syntax_Syntax.lbunivs = uu____8655; FStar_Syntax_Syntax.lbtyp = uu____8656; FStar_Syntax_Syntax.lbeff = uu____8657; FStar_Syntax_Syntax.lbdef = uu____8658})::uu____8659), uu____8660) -> begin
(failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____8686; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____8688; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (uu____8709) -> begin
((FStar_Errors.diag t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions, and their enclosings let bindings (including the top-level let) are not yet fully encoded to the SMT solver; you may not be able to prove some facts");
(FStar_Exn.raise Inner_let_rec);
)
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end);
)))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (

let uu____8779 = (encode_term e1 env)
in (match (uu____8779) with
| (ee1, decls1) -> begin
(

let uu____8790 = (FStar_Syntax_Subst.open_term ((((x), (FStar_Pervasives_Native.None)))::[]) e2)
in (match (uu____8790) with
| (xs, e21) -> begin
(

let uu____8815 = (FStar_List.hd xs)
in (match (uu____8815) with
| (x1, uu____8829) -> begin
(

let env' = (push_term_var env x1 ee1)
in (

let uu____8831 = (encode_body e21 env')
in (match (uu____8831) with
| (ee2, decls2) -> begin
((ee2), ((FStar_List.append decls1 decls2)))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (

let uu____8863 = (

let uu____8870 = (

let uu____8871 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.null_bv uu____8871))
in (gen_term_var env uu____8870))
in (match (uu____8863) with
| (scrsym, scr', env1) -> begin
(

let uu____8879 = (encode_term e env1)
in (match (uu____8879) with
| (scr, decls) -> begin
(

let uu____8890 = (

let encode_branch = (fun b uu____8915 -> (match (uu____8915) with
| (else_case, decls1) -> begin
(

let uu____8934 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____8934) with
| (p, w, br) -> begin
(

let uu____8960 = (encode_pat env1 p)
in (match (uu____8960) with
| (env0, pattern) -> begin
(

let guard = (pattern.guard scr')
in (

let projections = (pattern.projections scr')
in (

let env2 = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env2 uu____8997 -> (match (uu____8997) with
| (x, t) -> begin
(push_term_var env2 x t)
end)) env1))
in (

let uu____9004 = (match (w) with
| FStar_Pervasives_Native.None -> begin
((guard), ([]))
end
| FStar_Pervasives_Native.Some (w1) -> begin
(

let uu____9026 = (encode_term w1 env2)
in (match (uu____9026) with
| (w2, decls2) -> begin
(

let uu____9039 = (

let uu____9040 = (

let uu____9045 = (

let uu____9046 = (

let uu____9051 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue)
in ((w2), (uu____9051)))
in (FStar_SMTEncoding_Util.mkEq uu____9046))
in ((guard), (uu____9045)))
in (FStar_SMTEncoding_Util.mkAnd uu____9040))
in ((uu____9039), (decls2)))
end))
end)
in (match (uu____9004) with
| (guard1, decls2) -> begin
(

let uu____9064 = (encode_br br env2)
in (match (uu____9064) with
| (br1, decls3) -> begin
(

let uu____9077 = (FStar_SMTEncoding_Util.mkITE ((guard1), (br1), (else_case)))
in ((uu____9077), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end)))))
end))
end))
end))
in (FStar_List.fold_right encode_branch pats ((default_case), (decls))))
in (match (uu____8890) with
| (match_tm, decls1) -> begin
(

let uu____9096 = (FStar_SMTEncoding_Term.mkLet' (((((((scrsym), (FStar_SMTEncoding_Term.Term_sort))), (scr)))::[]), (match_tm)) FStar_Range.dummyRange)
in ((uu____9096), (decls1)))
end))
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> ((

let uu____9136 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____9136) with
| true -> begin
(

let uu____9137 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" uu____9137))
end
| uu____9138 -> begin
()
end));
(

let uu____9139 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (uu____9139) with
| (vars, pat_term) -> begin
(

let uu____9156 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun uu____9209 v1 -> (match (uu____9209) with
| (env1, vars1) -> begin
(

let uu____9261 = (gen_term_var env1 v1)
in (match (uu____9261) with
| (xx, uu____9283, env2) -> begin
((env2), ((((v1), (((xx), (FStar_SMTEncoding_Term.Term_sort)))))::vars1))
end))
end)) ((env), ([]))))
in (match (uu____9156) with
| (env1, vars1) -> begin
(

let rec mk_guard = (fun pat1 scrutinee -> (match (pat1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_var (uu____9362) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_wild (uu____9363) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____9364) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____9372 = (encode_const c env1)
in (match (uu____9372) with
| (tm, decls) -> begin
((match (decls) with
| (uu____9386)::uu____9387 -> begin
(failwith "Unexpected encoding of constant pattern")
end
| uu____9390 -> begin
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

let uu____9413 = (FStar_TypeChecker_Env.datacons_of_typ env1.tcenv tc_name)
in (match (uu____9413) with
| (uu____9420, (uu____9421)::[]) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| uu____9424 -> begin
(mk_data_tester env1 f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
end)))
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____9457 -> (match (uu____9457) with
| (arg, uu____9465) -> begin
(

let proj = (primitive_projector_by_pos env1.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____9471 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_guard arg uu____9471)))
end))))
in (FStar_SMTEncoding_Util.mk_and_l ((is_f)::sub_term_guards))))
end))
in (

let rec mk_projections = (fun pat1 scrutinee -> (match (pat1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (x, uu____9498) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_constant (uu____9529) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let uu____9552 = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____9596 -> (match (uu____9596) with
| (arg, uu____9610) -> begin
(

let proj = (primitive_projector_by_pos env1.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____9616 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_projections arg uu____9616)))
end))))
in (FStar_All.pipe_right uu____9552 FStar_List.flatten))
end))
in (

let pat_term1 = (fun uu____9644 -> (encode_term pat_term env1))
in (

let pattern = {pat_vars = vars1; pat_term = pat_term1; guard = (mk_guard pat); projections = (mk_projections pat)}
in ((env1), (pattern))))))
end))
end));
))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (

let uu____9654 = (FStar_All.pipe_right l (FStar_List.fold_left (fun uu____9692 uu____9693 -> (match (((uu____9692), (uu____9693))) with
| ((tms, decls), (t, uu____9729)) -> begin
(

let uu____9750 = (encode_term t env)
in (match (uu____9750) with
| (t1, decls') -> begin
(((t1)::tms), ((FStar_List.append decls decls')))
end))
end)) (([]), ([]))))
in (match (uu____9654) with
| (l1, decls) -> begin
(((FStar_List.rev l1)), (decls))
end)))
and encode_function_type_as_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let list_elements1 = (fun e -> (

let uu____9807 = (FStar_Syntax_Util.list_elements e)
in (match (uu____9807) with
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

let uu____9828 = (

let uu____9843 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right uu____9843 FStar_Syntax_Util.head_and_args))
in (match (uu____9828) with
| (head1, args) -> begin
(

let uu____9882 = (

let uu____9895 = (

let uu____9896 = (FStar_Syntax_Util.un_uinst head1)
in uu____9896.FStar_Syntax_Syntax.n)
in ((uu____9895), (args)))
in (match (uu____9882) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((uu____9910, uu____9911))::((e, uu____9913))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpat_lid) -> begin
e
end
| uu____9948 -> begin
(failwith "Unexpected pattern term")
end))
end)))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements1 p)
in (

let smt_pat_or1 = (fun t1 -> (

let uu____9984 = (

let uu____9999 = (FStar_Syntax_Util.unmeta t1)
in (FStar_All.pipe_right uu____9999 FStar_Syntax_Util.head_and_args))
in (match (uu____9984) with
| (head1, args) -> begin
(

let uu____10040 = (

let uu____10053 = (

let uu____10054 = (FStar_Syntax_Util.un_uinst head1)
in uu____10054.FStar_Syntax_Syntax.n)
in ((uu____10053), (args)))
in (match (uu____10040) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, uu____10071))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpatOr_lid) -> begin
FStar_Pervasives_Native.Some (e)
end
| uu____10098 -> begin
FStar_Pervasives_Native.None
end))
end)))
in (match (elts) with
| (t1)::[] -> begin
(

let uu____10120 = (smt_pat_or1 t1)
in (match (uu____10120) with
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____10136 = (list_elements1 e)
in (FStar_All.pipe_right uu____10136 (FStar_List.map (fun branch1 -> (

let uu____10154 = (list_elements1 branch1)
in (FStar_All.pipe_right uu____10154 (FStar_List.map one_pat)))))))
end
| uu____10165 -> begin
(

let uu____10170 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____10170)::[])
end))
end
| uu____10191 -> begin
(

let uu____10194 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____10194)::[])
end))))
in (

let uu____10215 = (

let uu____10234 = (

let uu____10235 = (FStar_Syntax_Subst.compress t)
in uu____10235.FStar_Syntax_Syntax.n)
in (match (uu____10234) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____10274 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____10274) with
| (binders1, c1) -> begin
(match (c1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____10317; FStar_Syntax_Syntax.effect_name = uu____10318; FStar_Syntax_Syntax.result_typ = uu____10319; FStar_Syntax_Syntax.effect_args = ((pre, uu____10321))::((post, uu____10323))::((pats, uu____10325))::[]; FStar_Syntax_Syntax.flags = uu____10326}) -> begin
(

let uu____10367 = (lemma_pats pats)
in ((binders1), (pre), (post), (uu____10367)))
end
| uu____10384 -> begin
(failwith "impos")
end)
end))
end
| uu____10403 -> begin
(failwith "Impos")
end))
in (match (uu____10215) with
| (binders, pre, post, patterns) -> begin
(

let env1 = (

let uu___165_10451 = env
in {bindings = uu___165_10451.bindings; depth = uu___165_10451.depth; tcenv = uu___165_10451.tcenv; warn = uu___165_10451.warn; cache = uu___165_10451.cache; nolabels = uu___165_10451.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___165_10451.encode_non_total_function_typ; current_module_name = uu___165_10451.current_module_name})
in (

let uu____10452 = (encode_binders FStar_Pervasives_Native.None binders env1)
in (match (uu____10452) with
| (vars, guards, env2, decls, uu____10477) -> begin
(

let uu____10490 = (

let uu____10503 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch1 -> (

let uu____10547 = (

let uu____10556 = (FStar_All.pipe_right branch1 (FStar_List.map (fun t1 -> (encode_term t1 env2))))
in (FStar_All.pipe_right uu____10556 FStar_List.unzip))
in (match (uu____10547) with
| (pats, decls1) -> begin
((pats), (decls1))
end)))))
in (FStar_All.pipe_right uu____10503 FStar_List.unzip))
in (match (uu____10490) with
| (pats, decls') -> begin
(

let decls'1 = (FStar_List.flatten decls')
in (

let post1 = (FStar_Syntax_Util.unthunk_lemma_post post)
in (

let env3 = (

let uu___166_10668 = env2
in {bindings = uu___166_10668.bindings; depth = uu___166_10668.depth; tcenv = uu___166_10668.tcenv; warn = uu___166_10668.warn; cache = uu___166_10668.cache; nolabels = true; use_zfuel_name = uu___166_10668.use_zfuel_name; encode_non_total_function_typ = uu___166_10668.encode_non_total_function_typ; current_module_name = uu___166_10668.current_module_name})
in (

let uu____10669 = (

let uu____10674 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula uu____10674 env3))
in (match (uu____10669) with
| (pre1, decls'') -> begin
(

let uu____10681 = (

let uu____10686 = (FStar_Syntax_Util.unmeta post1)
in (encode_formula uu____10686 env3))
in (match (uu____10681) with
| (post2, decls''') -> begin
(

let decls1 = (FStar_List.append decls (FStar_List.append (FStar_List.flatten decls'1) (FStar_List.append decls'' decls''')))
in (

let uu____10696 = (

let uu____10697 = (

let uu____10708 = (

let uu____10709 = (

let uu____10714 = (FStar_SMTEncoding_Util.mk_and_l ((pre1)::guards))
in ((uu____10714), (post2)))
in (FStar_SMTEncoding_Util.mkImp uu____10709))
in ((pats), (vars), (uu____10708)))
in (FStar_SMTEncoding_Util.mkForall uu____10697))
in ((uu____10696), (decls1))))
end))
end)))))
end))
end)))
end))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (

let debug1 = (fun phi1 -> (

let uu____10733 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____10733) with
| true -> begin
(

let uu____10734 = (FStar_Syntax_Print.tag_of_term phi1)
in (

let uu____10735 = (FStar_Syntax_Print.term_to_string phi1)
in (FStar_Util.print2 "Formula (%s)  %s\n" uu____10734 uu____10735)))
end
| uu____10736 -> begin
()
end)))
in (

let enc = (fun f r l -> (

let uu____10768 = (FStar_Util.fold_map (fun decls x -> (

let uu____10796 = (encode_term (FStar_Pervasives_Native.fst x) env)
in (match (uu____10796) with
| (t, decls') -> begin
(((FStar_List.append decls decls')), (t))
end))) [] l)
in (match (uu____10768) with
| (decls, args) -> begin
(

let uu____10825 = (

let uu___167_10826 = (f args)
in {FStar_SMTEncoding_Term.tm = uu___167_10826.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___167_10826.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____10825), (decls)))
end)))
in (

let const_op = (fun f r uu____10857 -> (

let uu____10870 = (f r)
in ((uu____10870), ([]))))
in (

let un_op = (fun f l -> (

let uu____10889 = (FStar_List.hd l)
in (FStar_All.pipe_left f uu____10889)))
in (

let bin_op = (fun f uu___141_10905 -> (match (uu___141_10905) with
| (t1)::(t2)::[] -> begin
(f ((t1), (t2)))
end
| uu____10916 -> begin
(failwith "Impossible")
end))
in (

let enc_prop_c = (fun f r l -> (

let uu____10950 = (FStar_Util.fold_map (fun decls uu____10973 -> (match (uu____10973) with
| (t, uu____10987) -> begin
(

let uu____10988 = (encode_formula t env)
in (match (uu____10988) with
| (phi1, decls') -> begin
(((FStar_List.append decls decls')), (phi1))
end))
end)) [] l)
in (match (uu____10950) with
| (decls, phis) -> begin
(

let uu____11017 = (

let uu___168_11018 = (f phis)
in {FStar_SMTEncoding_Term.tm = uu___168_11018.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___168_11018.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____11017), (decls)))
end)))
in (

let eq_op = (fun r args -> (

let rf = (FStar_List.filter (fun uu____11079 -> (match (uu____11079) with
| (a, q) -> begin
(match (q) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____11098)) -> begin
false
end
| uu____11099 -> begin
true
end)
end)) args)
in (match ((Prims.op_disEquality (FStar_List.length rf) (Prims.parse_int "2"))) with
| true -> begin
(

let uu____11114 = (FStar_Util.format1 "eq_op: got %s non-implicit arguments instead of 2?" (Prims.string_of_int (FStar_List.length rf)))
in (failwith uu____11114))
end
| uu____11127 -> begin
(

let uu____11128 = (enc (bin_op FStar_SMTEncoding_Util.mkEq))
in (uu____11128 r rf))
end)))
in (

let mk_imp1 = (fun r uu___142_11153 -> (match (uu___142_11153) with
| ((lhs, uu____11159))::((rhs, uu____11161))::[] -> begin
(

let uu____11188 = (encode_formula rhs env)
in (match (uu____11188) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____11203) -> begin
((l1), (decls1))
end
| uu____11208 -> begin
(

let uu____11209 = (encode_formula lhs env)
in (match (uu____11209) with
| (l2, decls2) -> begin
(

let uu____11220 = (FStar_SMTEncoding_Term.mkImp ((l2), (l1)) r)
in ((uu____11220), ((FStar_List.append decls1 decls2))))
end))
end)
end))
end
| uu____11223 -> begin
(failwith "impossible")
end))
in (

let mk_ite = (fun r uu___143_11244 -> (match (uu___143_11244) with
| ((guard, uu____11250))::((_then, uu____11252))::((_else, uu____11254))::[] -> begin
(

let uu____11291 = (encode_formula guard env)
in (match (uu____11291) with
| (g, decls1) -> begin
(

let uu____11302 = (encode_formula _then env)
in (match (uu____11302) with
| (t, decls2) -> begin
(

let uu____11313 = (encode_formula _else env)
in (match (uu____11313) with
| (e, decls3) -> begin
(

let res = (FStar_SMTEncoding_Term.mkITE ((g), (t), (e)) r)
in ((res), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end))
end))
end
| uu____11327 -> begin
(failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (

let uu____11352 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f uu____11352)))
in (

let connectives = (

let uu____11370 = (

let uu____11383 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd))
in ((FStar_Parser_Const.and_lid), (uu____11383)))
in (

let uu____11400 = (

let uu____11415 = (

let uu____11428 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr))
in ((FStar_Parser_Const.or_lid), (uu____11428)))
in (

let uu____11445 = (

let uu____11460 = (

let uu____11475 = (

let uu____11488 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff))
in ((FStar_Parser_Const.iff_lid), (uu____11488)))
in (

let uu____11505 = (

let uu____11520 = (

let uu____11535 = (

let uu____11548 = (enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot))
in ((FStar_Parser_Const.not_lid), (uu____11548)))
in (uu____11535)::(((FStar_Parser_Const.eq2_lid), (eq_op)))::(((FStar_Parser_Const.eq3_lid), (eq_op)))::(((FStar_Parser_Const.true_lid), ((const_op FStar_SMTEncoding_Term.mkTrue))))::(((FStar_Parser_Const.false_lid), ((const_op FStar_SMTEncoding_Term.mkFalse))))::[])
in (((FStar_Parser_Const.ite_lid), (mk_ite)))::uu____11520)
in (uu____11475)::uu____11505))
in (((FStar_Parser_Const.imp_lid), (mk_imp1)))::uu____11460)
in (uu____11415)::uu____11445))
in (uu____11370)::uu____11400))
in (

let rec fallback = (fun phi1 -> (match (phi1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(

let uu____11869 = (encode_formula phi' env)
in (match (uu____11869) with
| (phi2, decls) -> begin
(

let uu____11880 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled (((phi2), (msg), (r)))) r)
in ((uu____11880), (decls)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (uu____11881) -> begin
(

let uu____11888 = (FStar_Syntax_Util.unmeta phi1)
in (encode_formula uu____11888 env))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(

let uu____11927 = (encode_match e pats FStar_SMTEncoding_Util.mkFalse env encode_formula)
in (match (uu____11927) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____11939; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____11941; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let uu____11962 = (encode_let x t1 e1 e2 env encode_formula)
in (match (uu____11962) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let head2 = (FStar_Syntax_Util.un_uinst head1)
in (match (((head2.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____12009)::((x, uu____12011))::((t, uu____12013))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.has_type_lid) -> begin
(

let uu____12060 = (encode_term x env)
in (match (uu____12060) with
| (x1, decls) -> begin
(

let uu____12071 = (encode_term t env)
in (match (uu____12071) with
| (t1, decls') -> begin
(

let uu____12082 = (FStar_SMTEncoding_Term.mk_HasType x1 t1)
in ((uu____12082), ((FStar_List.append decls decls'))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((r, uu____12087))::((msg, uu____12089))::((phi2, uu____12091))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.labeled_lid) -> begin
(

let uu____12136 = (

let uu____12141 = (

let uu____12142 = (FStar_Syntax_Subst.compress r)
in uu____12142.FStar_Syntax_Syntax.n)
in (

let uu____12145 = (

let uu____12146 = (FStar_Syntax_Subst.compress msg)
in uu____12146.FStar_Syntax_Syntax.n)
in ((uu____12141), (uu____12145))))
in (match (uu____12136) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____12155))) -> begin
(

let phi3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((phi2), (FStar_Syntax_Syntax.Meta_labeled (((s), (r1), (false))))))) FStar_Pervasives_Native.None r1)
in (fallback phi3))
end
| uu____12161 -> begin
(fallback phi2)
end))
end
| uu____12166 when (head_redex env head2) -> begin
(

let uu____12179 = (whnf env phi1)
in (encode_formula uu____12179 env))
end
| uu____12180 -> begin
(

let uu____12193 = (encode_term phi1 env)
in (match (uu____12193) with
| (tt, decls) -> begin
(

let uu____12204 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___169_12207 = tt
in {FStar_SMTEncoding_Term.tm = uu___169_12207.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___169_12207.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi1.FStar_Syntax_Syntax.pos}))
in ((uu____12204), (decls)))
end))
end))
end
| uu____12208 -> begin
(

let uu____12209 = (encode_term phi1 env)
in (match (uu____12209) with
| (tt, decls) -> begin
(

let uu____12220 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___170_12223 = tt
in {FStar_SMTEncoding_Term.tm = uu___170_12223.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___170_12223.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi1.FStar_Syntax_Syntax.pos}))
in ((uu____12220), (decls)))
end))
end))
in (

let encode_q_body = (fun env1 bs ps body -> (

let uu____12259 = (encode_binders FStar_Pervasives_Native.None bs env1)
in (match (uu____12259) with
| (vars, guards, env2, decls, uu____12298) -> begin
(

let uu____12311 = (

let uu____12324 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let uu____12372 = (

let uu____12381 = (FStar_All.pipe_right p (FStar_List.map (fun uu____12411 -> (match (uu____12411) with
| (t, uu____12421) -> begin
(encode_term t (

let uu___171_12423 = env2
in {bindings = uu___171_12423.bindings; depth = uu___171_12423.depth; tcenv = uu___171_12423.tcenv; warn = uu___171_12423.warn; cache = uu___171_12423.cache; nolabels = uu___171_12423.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___171_12423.encode_non_total_function_typ; current_module_name = uu___171_12423.current_module_name}))
end))))
in (FStar_All.pipe_right uu____12381 FStar_List.unzip))
in (match (uu____12372) with
| (p1, decls1) -> begin
((p1), ((FStar_List.flatten decls1)))
end)))))
in (FStar_All.pipe_right uu____12324 FStar_List.unzip))
in (match (uu____12311) with
| (pats, decls') -> begin
(

let uu____12522 = (encode_formula body env2)
in (match (uu____12522) with
| (body1, decls'') -> begin
(

let guards1 = (match (pats) with
| (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (gf), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____12554; FStar_SMTEncoding_Term.rng = uu____12555})::[])::[] when (Prims.op_Equality (FStar_Ident.text_of_lid FStar_Parser_Const.guard_free) gf) -> begin
[]
end
| uu____12570 -> begin
guards
end)
in (

let uu____12575 = (FStar_SMTEncoding_Util.mk_and_l guards1)
in ((vars), (pats), (uu____12575), (body1), ((FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') decls''))))))
end))
end))
end)))
in ((debug1 phi);
(

let phi1 = (FStar_Syntax_Util.unascribe phi)
in (

let check_pattern_vars = (fun vars pats -> (

let pats1 = (FStar_All.pipe_right pats (FStar_List.map (fun uu____12635 -> (match (uu____12635) with
| (x, uu____12641) -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x)
end))))
in (match (pats1) with
| [] -> begin
()
end
| (hd1)::tl1 -> begin
(

let pat_vars = (

let uu____12649 = (FStar_Syntax_Free.names hd1)
in (FStar_List.fold_left (fun out x -> (

let uu____12661 = (FStar_Syntax_Free.names x)
in (FStar_Util.set_union out uu____12661))) uu____12649 tl1))
in (

let uu____12664 = (FStar_All.pipe_right vars (FStar_Util.find_opt (fun uu____12691 -> (match (uu____12691) with
| (b, uu____12697) -> begin
(

let uu____12698 = (FStar_Util.set_mem b pat_vars)
in (not (uu____12698)))
end))))
in (match (uu____12664) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (x, uu____12704) -> begin
(

let pos = (FStar_List.fold_left (fun out t -> (FStar_Range.union_ranges out t.FStar_Syntax_Syntax.pos)) hd1.FStar_Syntax_Syntax.pos tl1)
in (

let uu____12718 = (

let uu____12719 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "SMT pattern misses at least one bound variable: %s" uu____12719))
in (FStar_Errors.warn pos uu____12718)))
end)))
end)))
in (

let uu____12720 = (FStar_Syntax_Util.destruct_typ_as_formula phi1)
in (match (uu____12720) with
| FStar_Pervasives_Native.None -> begin
(fallback phi1)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(

let uu____12729 = (FStar_All.pipe_right connectives (FStar_List.tryFind (fun uu____12787 -> (match (uu____12787) with
| (l, uu____12801) -> begin
(FStar_Ident.lid_equals op l)
end))))
in (match (uu____12729) with
| FStar_Pervasives_Native.None -> begin
(fallback phi1)
end
| FStar_Pervasives_Native.Some (uu____12834, f) -> begin
(f phi1.FStar_Syntax_Syntax.pos arms)
end))
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____12874 = (encode_q_body env vars pats body)
in (match (uu____12874) with
| (vars1, pats1, guard, body1, decls) -> begin
(

let tm = (

let uu____12919 = (

let uu____12930 = (FStar_SMTEncoding_Util.mkImp ((guard), (body1)))
in ((pats1), (vars1), (uu____12930)))
in (FStar_SMTEncoding_Term.mkForall uu____12919 phi1.FStar_Syntax_Syntax.pos))
in ((tm), (decls)))
end));
)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____12949 = (encode_q_body env vars pats body)
in (match (uu____12949) with
| (vars1, pats1, guard, body1, decls) -> begin
(

let uu____12993 = (

let uu____12994 = (

let uu____13005 = (FStar_SMTEncoding_Util.mkAnd ((guard), (body1)))
in ((pats1), (vars1), (uu____13005)))
in (FStar_SMTEncoding_Term.mkExists uu____12994 phi1.FStar_Syntax_Syntax.pos))
in ((uu____12993), (decls)))
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

let uu____13103 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____13103) with
| (asym, a) -> begin
(

let uu____13110 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____13110) with
| (xsym, x) -> begin
(

let uu____13117 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____13117) with
| (ysym, y) -> begin
(

let quant = (fun vars body x1 -> (

let xname_decl = (

let uu____13161 = (

let uu____13172 = (FStar_All.pipe_right vars (FStar_List.map FStar_Pervasives_Native.snd))
in ((x1), (uu____13172), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____13161))
in (

let xtok = (Prims.strcat x1 "@tok")
in (

let xtok_decl = FStar_SMTEncoding_Term.DeclFun (((xtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let xapp = (

let uu____13198 = (

let uu____13205 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((x1), (uu____13205)))
in (FStar_SMTEncoding_Util.mkApp uu____13198))
in (

let xtok1 = (FStar_SMTEncoding_Util.mkApp ((xtok), ([])))
in (

let xtok_app = (mk_Apply xtok1 vars)
in (

let uu____13218 = (

let uu____13221 = (

let uu____13224 = (

let uu____13227 = (

let uu____13228 = (

let uu____13235 = (

let uu____13236 = (

let uu____13247 = (FStar_SMTEncoding_Util.mkEq ((xapp), (body)))
in ((((xapp)::[])::[]), (vars), (uu____13247)))
in (FStar_SMTEncoding_Util.mkForall uu____13236))
in ((uu____13235), (FStar_Pervasives_Native.None), ((Prims.strcat "primitive_" x1))))
in (FStar_SMTEncoding_Util.mkAssume uu____13228))
in (

let uu____13264 = (

let uu____13267 = (

let uu____13268 = (

let uu____13275 = (

let uu____13276 = (

let uu____13287 = (FStar_SMTEncoding_Util.mkEq ((xtok_app), (xapp)))
in ((((xtok_app)::[])::[]), (vars), (uu____13287)))
in (FStar_SMTEncoding_Util.mkForall uu____13276))
in ((uu____13275), (FStar_Pervasives_Native.Some ("Name-token correspondence")), ((Prims.strcat "token_correspondence_" x1))))
in (FStar_SMTEncoding_Util.mkAssume uu____13268))
in (uu____13267)::[])
in (uu____13227)::uu____13264))
in (xtok_decl)::uu____13224)
in (xname_decl)::uu____13221)
in ((xtok1), (uu____13218))))))))))
in (

let axy = (((asym), (FStar_SMTEncoding_Term.Term_sort)))::(((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let xy = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let qx = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let prims1 = (

let uu____13378 = (

let uu____13391 = (

let uu____13400 = (

let uu____13401 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13401))
in (quant axy uu____13400))
in ((FStar_Parser_Const.op_Eq), (uu____13391)))
in (

let uu____13410 = (

let uu____13425 = (

let uu____13438 = (

let uu____13447 = (

let uu____13448 = (

let uu____13449 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_SMTEncoding_Util.mkNot uu____13449))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13448))
in (quant axy uu____13447))
in ((FStar_Parser_Const.op_notEq), (uu____13438)))
in (

let uu____13458 = (

let uu____13473 = (

let uu____13486 = (

let uu____13495 = (

let uu____13496 = (

let uu____13497 = (

let uu____13502 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13503 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13502), (uu____13503))))
in (FStar_SMTEncoding_Util.mkLT uu____13497))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13496))
in (quant xy uu____13495))
in ((FStar_Parser_Const.op_LT), (uu____13486)))
in (

let uu____13512 = (

let uu____13527 = (

let uu____13540 = (

let uu____13549 = (

let uu____13550 = (

let uu____13551 = (

let uu____13556 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13557 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13556), (uu____13557))))
in (FStar_SMTEncoding_Util.mkLTE uu____13551))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13550))
in (quant xy uu____13549))
in ((FStar_Parser_Const.op_LTE), (uu____13540)))
in (

let uu____13566 = (

let uu____13581 = (

let uu____13594 = (

let uu____13603 = (

let uu____13604 = (

let uu____13605 = (

let uu____13610 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13611 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13610), (uu____13611))))
in (FStar_SMTEncoding_Util.mkGT uu____13605))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13604))
in (quant xy uu____13603))
in ((FStar_Parser_Const.op_GT), (uu____13594)))
in (

let uu____13620 = (

let uu____13635 = (

let uu____13648 = (

let uu____13657 = (

let uu____13658 = (

let uu____13659 = (

let uu____13664 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13665 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13664), (uu____13665))))
in (FStar_SMTEncoding_Util.mkGTE uu____13659))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13658))
in (quant xy uu____13657))
in ((FStar_Parser_Const.op_GTE), (uu____13648)))
in (

let uu____13674 = (

let uu____13689 = (

let uu____13702 = (

let uu____13711 = (

let uu____13712 = (

let uu____13713 = (

let uu____13718 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13719 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13718), (uu____13719))))
in (FStar_SMTEncoding_Util.mkSub uu____13713))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____13712))
in (quant xy uu____13711))
in ((FStar_Parser_Const.op_Subtraction), (uu____13702)))
in (

let uu____13728 = (

let uu____13743 = (

let uu____13756 = (

let uu____13765 = (

let uu____13766 = (

let uu____13767 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Util.mkMinus uu____13767))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____13766))
in (quant qx uu____13765))
in ((FStar_Parser_Const.op_Minus), (uu____13756)))
in (

let uu____13776 = (

let uu____13791 = (

let uu____13804 = (

let uu____13813 = (

let uu____13814 = (

let uu____13815 = (

let uu____13820 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13821 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13820), (uu____13821))))
in (FStar_SMTEncoding_Util.mkAdd uu____13815))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____13814))
in (quant xy uu____13813))
in ((FStar_Parser_Const.op_Addition), (uu____13804)))
in (

let uu____13830 = (

let uu____13845 = (

let uu____13858 = (

let uu____13867 = (

let uu____13868 = (

let uu____13869 = (

let uu____13874 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13875 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13874), (uu____13875))))
in (FStar_SMTEncoding_Util.mkMul uu____13869))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____13868))
in (quant xy uu____13867))
in ((FStar_Parser_Const.op_Multiply), (uu____13858)))
in (

let uu____13884 = (

let uu____13899 = (

let uu____13912 = (

let uu____13921 = (

let uu____13922 = (

let uu____13923 = (

let uu____13928 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13929 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13928), (uu____13929))))
in (FStar_SMTEncoding_Util.mkDiv uu____13923))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____13922))
in (quant xy uu____13921))
in ((FStar_Parser_Const.op_Division), (uu____13912)))
in (

let uu____13938 = (

let uu____13953 = (

let uu____13966 = (

let uu____13975 = (

let uu____13976 = (

let uu____13977 = (

let uu____13982 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13983 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13982), (uu____13983))))
in (FStar_SMTEncoding_Util.mkMod uu____13977))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____13976))
in (quant xy uu____13975))
in ((FStar_Parser_Const.op_Modulus), (uu____13966)))
in (

let uu____13992 = (

let uu____14007 = (

let uu____14020 = (

let uu____14029 = (

let uu____14030 = (

let uu____14031 = (

let uu____14036 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____14037 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____14036), (uu____14037))))
in (FStar_SMTEncoding_Util.mkAnd uu____14031))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____14030))
in (quant xy uu____14029))
in ((FStar_Parser_Const.op_And), (uu____14020)))
in (

let uu____14046 = (

let uu____14061 = (

let uu____14074 = (

let uu____14083 = (

let uu____14084 = (

let uu____14085 = (

let uu____14090 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____14091 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____14090), (uu____14091))))
in (FStar_SMTEncoding_Util.mkOr uu____14085))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____14084))
in (quant xy uu____14083))
in ((FStar_Parser_Const.op_Or), (uu____14074)))
in (

let uu____14100 = (

let uu____14115 = (

let uu____14128 = (

let uu____14137 = (

let uu____14138 = (

let uu____14139 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Util.mkNot uu____14139))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____14138))
in (quant qx uu____14137))
in ((FStar_Parser_Const.op_Negation), (uu____14128)))
in (uu____14115)::[])
in (uu____14061)::uu____14100))
in (uu____14007)::uu____14046))
in (uu____13953)::uu____13992))
in (uu____13899)::uu____13938))
in (uu____13845)::uu____13884))
in (uu____13791)::uu____13830))
in (uu____13743)::uu____13776))
in (uu____13689)::uu____13728))
in (uu____13635)::uu____13674))
in (uu____13581)::uu____13620))
in (uu____13527)::uu____13566))
in (uu____13473)::uu____13512))
in (uu____13425)::uu____13458))
in (uu____13378)::uu____13410))
in (

let mk1 = (fun l v1 -> (

let uu____14353 = (

let uu____14362 = (FStar_All.pipe_right prims1 (FStar_List.find (fun uu____14420 -> (match (uu____14420) with
| (l', uu____14434) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right uu____14362 (FStar_Option.map (fun uu____14494 -> (match (uu____14494) with
| (uu____14513, b) -> begin
(b v1)
end)))))
in (FStar_All.pipe_right uu____14353 FStar_Option.get)))
in (

let is = (fun l -> (FStar_All.pipe_right prims1 (FStar_Util.for_some (fun uu____14584 -> (match (uu____14584) with
| (l', uu____14598) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk1; is = is})))))))
end))
end))
end))


let pretype_axiom : env_t  ->  FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun env tapp vars -> (

let uu____14639 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____14639) with
| (xxsym, xx) -> begin
(

let uu____14646 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____14646) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let tapp_hash = (FStar_SMTEncoding_Term.hash_of_term tapp)
in (

let module_name = env.current_module_name
in (

let uu____14656 = (

let uu____14663 = (

let uu____14664 = (

let uu____14675 = (

let uu____14676 = (

let uu____14681 = (

let uu____14682 = (

let uu____14687 = (FStar_SMTEncoding_Util.mkApp (("PreType"), ((xx)::[])))
in ((tapp), (uu____14687)))
in (FStar_SMTEncoding_Util.mkEq uu____14682))
in ((xx_has_type), (uu____14681)))
in (FStar_SMTEncoding_Util.mkImp uu____14676))
in ((((xx_has_type)::[])::[]), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars), (uu____14675)))
in (FStar_SMTEncoding_Util.mkForall uu____14664))
in (

let uu____14712 = (

let uu____14713 = (

let uu____14714 = (

let uu____14715 = (FStar_Util.digest_of_string tapp_hash)
in (Prims.strcat "_pretyping_" uu____14715))
in (Prims.strcat module_name uu____14714))
in (varops.mk_unique uu____14713))
in ((uu____14663), (FStar_Pervasives_Native.Some ("pretyping")), (uu____14712))))
in (FStar_SMTEncoding_Util.mkAssume uu____14656)))))
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

let uu____14755 = (

let uu____14756 = (

let uu____14763 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in ((uu____14763), (FStar_Pervasives_Native.Some ("unit typing")), ("unit_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____14756))
in (

let uu____14766 = (

let uu____14769 = (

let uu____14770 = (

let uu____14777 = (

let uu____14778 = (

let uu____14789 = (

let uu____14790 = (

let uu____14795 = (FStar_SMTEncoding_Util.mkEq ((x), (FStar_SMTEncoding_Term.mk_Term_unit)))
in ((typing_pred), (uu____14795)))
in (FStar_SMTEncoding_Util.mkImp uu____14790))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____14789)))
in (mkForall_fuel uu____14778))
in ((uu____14777), (FStar_Pervasives_Native.Some ("unit inversion")), ("unit_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____14770))
in (uu____14769)::[])
in (uu____14755)::uu____14766))))
in (

let mk_bool = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Bool_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____14837 = (

let uu____14838 = (

let uu____14845 = (

let uu____14846 = (

let uu____14857 = (

let uu____14862 = (

let uu____14865 = (FStar_SMTEncoding_Term.boxBool b)
in (uu____14865)::[])
in (uu____14862)::[])
in (

let uu____14870 = (

let uu____14871 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType uu____14871 tt))
in ((uu____14857), ((bb)::[]), (uu____14870))))
in (FStar_SMTEncoding_Util.mkForall uu____14846))
in ((uu____14845), (FStar_Pervasives_Native.Some ("bool typing")), ("bool_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____14838))
in (

let uu____14892 = (

let uu____14895 = (

let uu____14896 = (

let uu____14903 = (

let uu____14904 = (

let uu____14915 = (

let uu____14916 = (

let uu____14921 = (FStar_SMTEncoding_Term.mk_tester (FStar_Pervasives_Native.fst FStar_SMTEncoding_Term.boxBoolFun) x)
in ((typing_pred), (uu____14921)))
in (FStar_SMTEncoding_Util.mkImp uu____14916))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____14915)))
in (mkForall_fuel uu____14904))
in ((uu____14903), (FStar_Pervasives_Native.Some ("bool inversion")), ("bool_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____14896))
in (uu____14895)::[])
in (uu____14837)::uu____14892))))))
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

let uu____14971 = (

let uu____14972 = (

let uu____14979 = (

let uu____14982 = (

let uu____14985 = (

let uu____14988 = (FStar_SMTEncoding_Term.boxInt a)
in (

let uu____14989 = (

let uu____14992 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____14992)::[])
in (uu____14988)::uu____14989))
in (tt)::uu____14985)
in (tt)::uu____14982)
in (("Prims.Precedes"), (uu____14979)))
in (FStar_SMTEncoding_Util.mkApp uu____14972))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14971))
in (

let precedes_y_x = (

let uu____14996 = (FStar_SMTEncoding_Util.mkApp (("Precedes"), ((y)::(x)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14996))
in (

let uu____14999 = (

let uu____15000 = (

let uu____15007 = (

let uu____15008 = (

let uu____15019 = (

let uu____15024 = (

let uu____15027 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____15027)::[])
in (uu____15024)::[])
in (

let uu____15032 = (

let uu____15033 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType uu____15033 tt))
in ((uu____15019), ((bb)::[]), (uu____15032))))
in (FStar_SMTEncoding_Util.mkForall uu____15008))
in ((uu____15007), (FStar_Pervasives_Native.Some ("int typing")), ("int_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____15000))
in (

let uu____15054 = (

let uu____15057 = (

let uu____15058 = (

let uu____15065 = (

let uu____15066 = (

let uu____15077 = (

let uu____15078 = (

let uu____15083 = (FStar_SMTEncoding_Term.mk_tester (FStar_Pervasives_Native.fst FStar_SMTEncoding_Term.boxIntFun) x)
in ((typing_pred), (uu____15083)))
in (FStar_SMTEncoding_Util.mkImp uu____15078))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____15077)))
in (mkForall_fuel uu____15066))
in ((uu____15065), (FStar_Pervasives_Native.Some ("int inversion")), ("int_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____15058))
in (

let uu____15108 = (

let uu____15111 = (

let uu____15112 = (

let uu____15119 = (

let uu____15120 = (

let uu____15131 = (

let uu____15132 = (

let uu____15137 = (

let uu____15138 = (

let uu____15141 = (

let uu____15144 = (

let uu____15147 = (

let uu____15148 = (

let uu____15153 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____15154 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____15153), (uu____15154))))
in (FStar_SMTEncoding_Util.mkGT uu____15148))
in (

let uu____15155 = (

let uu____15158 = (

let uu____15159 = (

let uu____15164 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____15165 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____15164), (uu____15165))))
in (FStar_SMTEncoding_Util.mkGTE uu____15159))
in (

let uu____15166 = (

let uu____15169 = (

let uu____15170 = (

let uu____15175 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____15176 = (FStar_SMTEncoding_Term.unboxInt x)
in ((uu____15175), (uu____15176))))
in (FStar_SMTEncoding_Util.mkLT uu____15170))
in (uu____15169)::[])
in (uu____15158)::uu____15166))
in (uu____15147)::uu____15155))
in (typing_pred_y)::uu____15144)
in (typing_pred)::uu____15141)
in (FStar_SMTEncoding_Util.mk_and_l uu____15138))
in ((uu____15137), (precedes_y_x)))
in (FStar_SMTEncoding_Util.mkImp uu____15132))
in ((((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[]), ((xx)::(yy)::[]), (uu____15131)))
in (mkForall_fuel uu____15120))
in ((uu____15119), (FStar_Pervasives_Native.Some ("well-founded ordering on nat (alt)")), ("well-founded-ordering-on-nat")))
in (FStar_SMTEncoding_Util.mkAssume uu____15112))
in (uu____15111)::[])
in (uu____15057)::uu____15108))
in (uu____14999)::uu____15054)))))))))))
in (

let mk_str = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.String_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____15222 = (

let uu____15223 = (

let uu____15230 = (

let uu____15231 = (

let uu____15242 = (

let uu____15247 = (

let uu____15250 = (FStar_SMTEncoding_Term.boxString b)
in (uu____15250)::[])
in (uu____15247)::[])
in (

let uu____15255 = (

let uu____15256 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType uu____15256 tt))
in ((uu____15242), ((bb)::[]), (uu____15255))))
in (FStar_SMTEncoding_Util.mkForall uu____15231))
in ((uu____15230), (FStar_Pervasives_Native.Some ("string typing")), ("string_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____15223))
in (

let uu____15277 = (

let uu____15280 = (

let uu____15281 = (

let uu____15288 = (

let uu____15289 = (

let uu____15300 = (

let uu____15301 = (

let uu____15306 = (FStar_SMTEncoding_Term.mk_tester (FStar_Pervasives_Native.fst FStar_SMTEncoding_Term.boxStringFun) x)
in ((typing_pred), (uu____15306)))
in (FStar_SMTEncoding_Util.mkImp uu____15301))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____15300)))
in (mkForall_fuel uu____15289))
in ((uu____15288), (FStar_Pervasives_Native.Some ("string inversion")), ("string_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____15281))
in (uu____15280)::[])
in (uu____15222)::uu____15277))))))
in (

let mk_true_interp = (fun env nm true_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((true_tm)::[])))
in ((FStar_SMTEncoding_Util.mkAssume ((valid), (FStar_Pervasives_Native.Some ("True interpretation")), ("true_interp"))))::[]))
in (

let mk_false_interp = (fun env nm false_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((false_tm)::[])))
in (

let uu____15359 = (

let uu____15360 = (

let uu____15367 = (FStar_SMTEncoding_Util.mkIff ((FStar_SMTEncoding_Util.mkFalse), (valid)))
in ((uu____15367), (FStar_Pervasives_Native.Some ("False interpretation")), ("false_interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15360))
in (uu____15359)::[])))
in (

let mk_and_interp = (fun env conj uu____15379 -> (

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

let uu____15404 = (

let uu____15405 = (

let uu____15412 = (

let uu____15413 = (

let uu____15424 = (

let uu____15425 = (

let uu____15430 = (FStar_SMTEncoding_Util.mkAnd ((valid_a), (valid_b)))
in ((uu____15430), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____15425))
in ((((l_and_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____15424)))
in (FStar_SMTEncoding_Util.mkForall uu____15413))
in ((uu____15412), (FStar_Pervasives_Native.Some ("/\\ interpretation")), ("l_and-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15405))
in (uu____15404)::[]))))))))))
in (

let mk_or_interp = (fun env disj uu____15468 -> (

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

let uu____15493 = (

let uu____15494 = (

let uu____15501 = (

let uu____15502 = (

let uu____15513 = (

let uu____15514 = (

let uu____15519 = (FStar_SMTEncoding_Util.mkOr ((valid_a), (valid_b)))
in ((uu____15519), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____15514))
in ((((l_or_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____15513)))
in (FStar_SMTEncoding_Util.mkForall uu____15502))
in ((uu____15501), (FStar_Pervasives_Native.Some ("\\/ interpretation")), ("l_or-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15494))
in (uu____15493)::[]))))))))))
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

let uu____15582 = (

let uu____15583 = (

let uu____15590 = (

let uu____15591 = (

let uu____15602 = (

let uu____15603 = (

let uu____15608 = (FStar_SMTEncoding_Util.mkEq ((x1), (y1)))
in ((uu____15608), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____15603))
in ((((eq2_x_y)::[])::[]), ((aa)::(xx1)::(yy1)::[]), (uu____15602)))
in (FStar_SMTEncoding_Util.mkForall uu____15591))
in ((uu____15590), (FStar_Pervasives_Native.Some ("Eq2 interpretation")), ("eq2-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15583))
in (uu____15582)::[]))))))))))
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

let uu____15681 = (

let uu____15682 = (

let uu____15689 = (

let uu____15690 = (

let uu____15701 = (

let uu____15702 = (

let uu____15707 = (FStar_SMTEncoding_Util.mkEq ((x1), (y1)))
in ((uu____15707), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____15702))
in ((((eq3_x_y)::[])::[]), ((aa)::(bb)::(xx1)::(yy1)::[]), (uu____15701)))
in (FStar_SMTEncoding_Util.mkForall uu____15690))
in ((uu____15689), (FStar_Pervasives_Native.Some ("Eq3 interpretation")), ("eq3-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15682))
in (uu____15681)::[]))))))))))))
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

let uu____15778 = (

let uu____15779 = (

let uu____15786 = (

let uu____15787 = (

let uu____15798 = (

let uu____15799 = (

let uu____15804 = (FStar_SMTEncoding_Util.mkImp ((valid_a), (valid_b)))
in ((uu____15804), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____15799))
in ((((l_imp_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____15798)))
in (FStar_SMTEncoding_Util.mkForall uu____15787))
in ((uu____15786), (FStar_Pervasives_Native.Some ("==> interpretation")), ("l_imp-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15779))
in (uu____15778)::[]))))))))))
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

let uu____15867 = (

let uu____15868 = (

let uu____15875 = (

let uu____15876 = (

let uu____15887 = (

let uu____15888 = (

let uu____15893 = (FStar_SMTEncoding_Util.mkIff ((valid_a), (valid_b)))
in ((uu____15893), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____15888))
in ((((l_iff_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____15887)))
in (FStar_SMTEncoding_Util.mkForall uu____15876))
in ((uu____15875), (FStar_Pervasives_Native.Some ("<==> interpretation")), ("l_iff-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15868))
in (uu____15867)::[]))))))))))
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

let uu____15945 = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____15945))
in (

let uu____15948 = (

let uu____15949 = (

let uu____15956 = (

let uu____15957 = (

let uu____15968 = (FStar_SMTEncoding_Util.mkIff ((not_valid_a), (valid)))
in ((((l_not_a)::[])::[]), ((aa)::[]), (uu____15968)))
in (FStar_SMTEncoding_Util.mkForall uu____15957))
in ((uu____15956), (FStar_Pervasives_Native.Some ("not interpretation")), ("l_not-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15949))
in (uu____15948)::[])))))))
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

let uu____16028 = (

let uu____16035 = (

let uu____16038 = (FStar_SMTEncoding_Util.mk_ApplyTT b x1)
in (uu____16038)::[])
in (("Valid"), (uu____16035)))
in (FStar_SMTEncoding_Util.mkApp uu____16028))
in (

let uu____16041 = (

let uu____16042 = (

let uu____16049 = (

let uu____16050 = (

let uu____16061 = (

let uu____16062 = (

let uu____16067 = (

let uu____16068 = (

let uu____16079 = (

let uu____16084 = (

let uu____16087 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in (uu____16087)::[])
in (uu____16084)::[])
in (

let uu____16092 = (

let uu____16093 = (

let uu____16098 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in ((uu____16098), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp uu____16093))
in ((uu____16079), ((xx1)::[]), (uu____16092))))
in (FStar_SMTEncoding_Util.mkForall uu____16068))
in ((uu____16067), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____16062))
in ((((l_forall_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____16061)))
in (FStar_SMTEncoding_Util.mkForall uu____16050))
in ((uu____16049), (FStar_Pervasives_Native.Some ("forall interpretation")), ("forall-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16042))
in (uu____16041)::[])))))))))))
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

let uu____16180 = (

let uu____16187 = (

let uu____16190 = (FStar_SMTEncoding_Util.mk_ApplyTT b x1)
in (uu____16190)::[])
in (("Valid"), (uu____16187)))
in (FStar_SMTEncoding_Util.mkApp uu____16180))
in (

let uu____16193 = (

let uu____16194 = (

let uu____16201 = (

let uu____16202 = (

let uu____16213 = (

let uu____16214 = (

let uu____16219 = (

let uu____16220 = (

let uu____16231 = (

let uu____16236 = (

let uu____16239 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in (uu____16239)::[])
in (uu____16236)::[])
in (

let uu____16244 = (

let uu____16245 = (

let uu____16250 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in ((uu____16250), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp uu____16245))
in ((uu____16231), ((xx1)::[]), (uu____16244))))
in (FStar_SMTEncoding_Util.mkExists uu____16220))
in ((uu____16219), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____16214))
in ((((l_exists_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____16213)))
in (FStar_SMTEncoding_Util.mkForall uu____16202))
in ((uu____16201), (FStar_Pervasives_Native.Some ("exists interpretation")), ("exists-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16194))
in (uu____16193)::[])))))))))))
in (

let mk_range_interp = (fun env range tt -> (

let range_ty = (FStar_SMTEncoding_Util.mkApp ((range), ([])))
in (

let uu____16310 = (

let uu____16311 = (

let uu____16318 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_ty)
in (

let uu____16319 = (varops.mk_unique "typing_range_const")
in ((uu____16318), (FStar_Pervasives_Native.Some ("Range_const typing")), (uu____16319))))
in (FStar_SMTEncoding_Util.mkAssume uu____16311))
in (uu____16310)::[])))
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

let uu____16353 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1"))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16353 x1 t))
in (

let uu____16354 = (

let uu____16365 = (FStar_SMTEncoding_Util.mkImp ((hastypeZ), (hastypeS)))
in ((((hastypeZ)::[])::[]), ((xx1)::[]), (uu____16365)))
in (FStar_SMTEncoding_Util.mkForall uu____16354))))
in (

let uu____16388 = (

let uu____16389 = (

let uu____16396 = (

let uu____16397 = (

let uu____16408 = (FStar_SMTEncoding_Util.mkImp ((valid), (body)))
in ((((inversion_t)::[])::[]), ((tt1)::[]), (uu____16408)))
in (FStar_SMTEncoding_Util.mkForall uu____16397))
in ((uu____16396), (FStar_Pervasives_Native.Some ("inversion interpretation")), ("inversion-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16389))
in (uu____16388)::[])))))))))
in (

let prims1 = (((FStar_Parser_Const.unit_lid), (mk_unit)))::(((FStar_Parser_Const.bool_lid), (mk_bool)))::(((FStar_Parser_Const.int_lid), (mk_int)))::(((FStar_Parser_Const.string_lid), (mk_str)))::(((FStar_Parser_Const.true_lid), (mk_true_interp)))::(((FStar_Parser_Const.false_lid), (mk_false_interp)))::(((FStar_Parser_Const.and_lid), (mk_and_interp)))::(((FStar_Parser_Const.or_lid), (mk_or_interp)))::(((FStar_Parser_Const.eq2_lid), (mk_eq2_interp)))::(((FStar_Parser_Const.eq3_lid), (mk_eq3_interp)))::(((FStar_Parser_Const.imp_lid), (mk_imp_interp)))::(((FStar_Parser_Const.iff_lid), (mk_iff_interp)))::(((FStar_Parser_Const.not_lid), (mk_not_interp)))::(((FStar_Parser_Const.forall_lid), (mk_forall_interp)))::(((FStar_Parser_Const.exists_lid), (mk_exists_interp)))::(((FStar_Parser_Const.range_lid), (mk_range_interp)))::(((FStar_Parser_Const.inversion_lid), (mk_inversion_axiom)))::[]
in (fun env t s tt -> (

let uu____16732 = (FStar_Util.find_opt (fun uu____16758 -> (match (uu____16758) with
| (l, uu____16770) -> begin
(FStar_Ident.lid_equals l t)
end)) prims1)
in (match (uu____16732) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (uu____16795, f) -> begin
(f env s tt)
end)))))))))))))))))))))))))


let encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____16834 = (encode_function_type_as_formula t env)
in (match (uu____16834) with
| (form, decls) -> begin
(FStar_List.append decls (((FStar_SMTEncoding_Util.mkAssume ((form), (FStar_Pervasives_Native.Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str))), ((Prims.strcat "lemma_" lid.FStar_Ident.str)))))::[]))
end))))


let encode_free_var : Prims.bool  ->  env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun uninterpreted env fv tt t_norm quals -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____16880 = (((

let uu____16883 = ((FStar_Syntax_Util.is_pure_or_ghost_function t_norm) || (FStar_TypeChecker_Env.is_reifiable_function env.tcenv t_norm))
in (FStar_All.pipe_left Prims.op_Negation uu____16883)) || (FStar_Syntax_Util.is_lemma t_norm)) || uninterpreted)
in (match (uu____16880) with
| true -> begin
(

let uu____16890 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____16890) with
| (vname, vtok, env1) -> begin
(

let arg_sorts = (

let uu____16909 = (

let uu____16910 = (FStar_Syntax_Subst.compress t_norm)
in uu____16910.FStar_Syntax_Syntax.n)
in (match (uu____16909) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____16916) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun uu____16946 -> FStar_SMTEncoding_Term.Term_sort)))
end
| uu____16951 -> begin
[]
end))
in (

let d = FStar_SMTEncoding_Term.DeclFun (((vname), (arg_sorts), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Uninterpreted function symbol for impure function"))))
in (

let dd = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Uninterpreted name for impure function"))))
in (((d)::(dd)::[]), (env1)))))
end))
end
| uu____16964 -> begin
(

let uu____16965 = (prims.is lid)
in (match (uu____16965) with
| true -> begin
(

let vname = (varops.new_fvar lid)
in (

let uu____16973 = (prims.mk lid vname)
in (match (uu____16973) with
| (tok, definition) -> begin
(

let env1 = (push_free_var env lid vname (FStar_Pervasives_Native.Some (tok)))
in ((definition), (env1)))
end)))
end
| uu____16995 -> begin
(

let encode_non_total_function_typ = (Prims.op_disEquality lid.FStar_Ident.nsstr "Prims")
in (

let uu____16997 = (

let uu____17008 = (curried_arrow_formals_comp t_norm)
in (match (uu____17008) with
| (args, comp) -> begin
(

let comp1 = (

let uu____17026 = (FStar_TypeChecker_Env.is_reifiable_comp env.tcenv comp)
in (match (uu____17026) with
| true -> begin
(

let uu____17027 = (FStar_TypeChecker_Env.reify_comp (

let uu___172_17030 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___172_17030.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___172_17030.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___172_17030.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___172_17030.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___172_17030.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___172_17030.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___172_17030.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___172_17030.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___172_17030.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___172_17030.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___172_17030.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___172_17030.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___172_17030.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___172_17030.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___172_17030.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___172_17030.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___172_17030.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___172_17030.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___172_17030.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___172_17030.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___172_17030.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___172_17030.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___172_17030.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___172_17030.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___172_17030.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___172_17030.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___172_17030.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___172_17030.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___172_17030.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___172_17030.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___172_17030.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___172_17030.FStar_TypeChecker_Env.dsenv}) comp FStar_Syntax_Syntax.U_unknown)
in (FStar_Syntax_Syntax.mk_Total uu____17027))
end
| uu____17031 -> begin
comp
end))
in (match (encode_non_total_function_typ) with
| true -> begin
(

let uu____17042 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp1)
in ((args), (uu____17042)))
end
| uu____17055 -> begin
((args), (((FStar_Pervasives_Native.None), ((FStar_Syntax_Util.comp_result comp1)))))
end))
end))
in (match (uu____16997) with
| (formals, (pre_opt, res_t)) -> begin
(

let uu____17087 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____17087) with
| (vname, vtok, env1) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
end
| uu____17108 -> begin
(FStar_SMTEncoding_Util.mkApp ((vtok), ([])))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun uu___144_17150 -> (match (uu___144_17150) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(

let uu____17154 = (FStar_Util.prefix vars)
in (match (uu____17154) with
| (uu____17175, (xxsym, uu____17177)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____17195 = (

let uu____17196 = (

let uu____17203 = (

let uu____17204 = (

let uu____17215 = (

let uu____17216 = (

let uu____17221 = (

let uu____17222 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____17222))
in ((vapp), (uu____17221)))
in (FStar_SMTEncoding_Util.mkEq uu____17216))
in ((((vapp)::[])::[]), (vars), (uu____17215)))
in (FStar_SMTEncoding_Util.mkForall uu____17204))
in ((uu____17203), (FStar_Pervasives_Native.Some ("Discriminator equation")), ((Prims.strcat "disc_equation_" (escape d.FStar_Ident.str)))))
in (FStar_SMTEncoding_Util.mkAssume uu____17196))
in (uu____17195)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(

let uu____17241 = (FStar_Util.prefix vars)
in (match (uu____17241) with
| (uu____17262, (xxsym, uu____17264)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f1 = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (

let tp_name = (mk_term_projector_name d f1)
in (

let prim_app = (FStar_SMTEncoding_Util.mkApp ((tp_name), ((xx)::[])))
in (

let uu____17287 = (

let uu____17288 = (

let uu____17295 = (

let uu____17296 = (

let uu____17307 = (FStar_SMTEncoding_Util.mkEq ((vapp), (prim_app)))
in ((((vapp)::[])::[]), (vars), (uu____17307)))
in (FStar_SMTEncoding_Util.mkForall uu____17296))
in ((uu____17295), (FStar_Pervasives_Native.Some ("Projector equation")), ((Prims.strcat "proj_equation_" tp_name))))
in (FStar_SMTEncoding_Util.mkAssume uu____17288))
in (uu____17287)::[])))))
end))
end
| uu____17324 -> begin
[]
end)))))
in (

let uu____17325 = (encode_binders FStar_Pervasives_Native.None formals env1)
in (match (uu____17325) with
| (vars, guards, env', decls1, uu____17352) -> begin
(

let uu____17365 = (match (pre_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____17374 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____17374), (decls1)))
end
| FStar_Pervasives_Native.Some (p) -> begin
(

let uu____17376 = (encode_formula p env')
in (match (uu____17376) with
| (g, ds) -> begin
(

let uu____17387 = (FStar_SMTEncoding_Util.mk_and_l ((g)::guards))
in ((uu____17387), ((FStar_List.append decls1 ds))))
end))
end)
in (match (uu____17365) with
| (guard, decls11) -> begin
(

let vtok_app = (mk_Apply vtok_tm vars)
in (

let vapp = (

let uu____17400 = (

let uu____17407 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((vname), (uu____17407)))
in (FStar_SMTEncoding_Util.mkApp uu____17400))
in (

let uu____17416 = (

let vname_decl = (

let uu____17424 = (

let uu____17435 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____17445 -> FStar_SMTEncoding_Term.Term_sort)))
in ((vname), (uu____17435), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____17424))
in (

let uu____17454 = (

let env2 = (

let uu___173_17460 = env1
in {bindings = uu___173_17460.bindings; depth = uu___173_17460.depth; tcenv = uu___173_17460.tcenv; warn = uu___173_17460.warn; cache = uu___173_17460.cache; nolabels = uu___173_17460.nolabels; use_zfuel_name = uu___173_17460.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = uu___173_17460.current_module_name})
in (

let uu____17461 = (

let uu____17462 = (head_normal env2 tt)
in (not (uu____17462)))
in (match (uu____17461) with
| true -> begin
(encode_term_pred FStar_Pervasives_Native.None tt env2 vtok_tm)
end
| uu____17467 -> begin
(encode_term_pred FStar_Pervasives_Native.None t_norm env2 vtok_tm)
end)))
in (match (uu____17454) with
| (tok_typing, decls2) -> begin
(

let tok_typing1 = (match (formals) with
| (uu____17477)::uu____17478 -> begin
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

let uu____17518 = (

let uu____17529 = (FStar_SMTEncoding_Term.mk_NoHoist f tok_typing)
in ((((vtok_app_l)::[])::((vtok_app_r)::[])::[]), ((ff)::[]), (uu____17529)))
in (FStar_SMTEncoding_Util.mkForall uu____17518))
in (FStar_SMTEncoding_Util.mkAssume ((guarded_tok_typing), (FStar_Pervasives_Native.Some ("function token typing")), ((Prims.strcat "function_token_typing_" vname)))))))))
end
| uu____17556 -> begin
(FStar_SMTEncoding_Util.mkAssume ((tok_typing), (FStar_Pervasives_Native.Some ("function token typing")), ((Prims.strcat "function_token_typing_" vname))))
end)
in (

let uu____17559 = (match (formals) with
| [] -> begin
(

let uu____17576 = (

let uu____17577 = (

let uu____17580 = (FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left (fun _0_43 -> FStar_Pervasives_Native.Some (_0_43)) uu____17580))
in (push_free_var env1 lid vname uu____17577))
in (((FStar_List.append decls2 ((tok_typing1)::[]))), (uu____17576)))
end
| uu____17585 -> begin
(

let vtok_decl = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let name_tok_corr = (

let uu____17592 = (

let uu____17599 = (

let uu____17600 = (

let uu____17611 = (FStar_SMTEncoding_Util.mkEq ((vtok_app), (vapp)))
in ((((vtok_app)::[])::((vapp)::[])::[]), (vars), (uu____17611)))
in (FStar_SMTEncoding_Util.mkForall uu____17600))
in ((uu____17599), (FStar_Pervasives_Native.Some ("Name-token correspondence")), ((Prims.strcat "token_correspondence_" vname))))
in (FStar_SMTEncoding_Util.mkAssume uu____17592))
in (((FStar_List.append decls2 ((vtok_decl)::(name_tok_corr)::(tok_typing1)::[]))), (env1))))
end)
in (match (uu____17559) with
| (tok_decl, env2) -> begin
(((vname_decl)::tok_decl), (env2))
end)))
end)))
in (match (uu____17416) with
| (decls2, env2) -> begin
(

let uu____17654 = (

let res_t1 = (FStar_Syntax_Subst.compress res_t)
in (

let uu____17662 = (encode_term res_t1 env')
in (match (uu____17662) with
| (encoded_res_t, decls) -> begin
(

let uu____17675 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in ((encoded_res_t), (uu____17675), (decls)))
end)))
in (match (uu____17654) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (

let uu____17686 = (

let uu____17693 = (

let uu____17694 = (

let uu____17705 = (FStar_SMTEncoding_Util.mkImp ((guard), (ty_pred)))
in ((((vapp)::[])::[]), (vars), (uu____17705)))
in (FStar_SMTEncoding_Util.mkForall uu____17694))
in ((uu____17693), (FStar_Pervasives_Native.Some ("free var typing")), ((Prims.strcat "typing_" vname))))
in (FStar_SMTEncoding_Util.mkAssume uu____17686))
in (

let freshness = (

let uu____17721 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New))
in (match (uu____17721) with
| true -> begin
(

let uu____17726 = (

let uu____17727 = (

let uu____17738 = (FStar_All.pipe_right vars (FStar_List.map FStar_Pervasives_Native.snd))
in (

let uu____17749 = (varops.next_id ())
in ((vname), (uu____17738), (FStar_SMTEncoding_Term.Term_sort), (uu____17749))))
in (FStar_SMTEncoding_Term.fresh_constructor uu____17727))
in (

let uu____17752 = (

let uu____17755 = (pretype_axiom env2 vapp vars)
in (uu____17755)::[])
in (uu____17726)::uu____17752))
end
| uu____17756 -> begin
[]
end))
in (

let g = (

let uu____17760 = (

let uu____17763 = (

let uu____17766 = (

let uu____17769 = (

let uu____17772 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::uu____17772)
in (FStar_List.append freshness uu____17769))
in (FStar_List.append decls3 uu____17766))
in (FStar_List.append decls2 uu____17763))
in (FStar_List.append decls11 uu____17760))
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

let uu____17807 = (try_lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____17807) with
| FStar_Pervasives_Native.None -> begin
(

let uu____17844 = (encode_free_var false env x t t_norm [])
in (match (uu____17844) with
| (decls, env1) -> begin
(

let uu____17871 = (lookup_lid env1 x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____17871) with
| (n1, x', uu____17898) -> begin
((((n1), (x'))), (decls), (env1))
end))
end))
end
| FStar_Pervasives_Native.Some (n1, x1, uu____17919) -> begin
((((n1), (x1))), ([]), (env))
end)))


let encode_top_level_val : Prims.bool  ->  env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun uninterpreted env lid t quals -> (

let tt = (norm env t)
in (

let uu____17979 = (encode_free_var uninterpreted env lid t tt quals)
in (match (uu____17979) with
| (decls, env1) -> begin
(

let uu____17998 = (FStar_Syntax_Util.is_smt_lemma t)
in (match (uu____17998) with
| true -> begin
(

let uu____18005 = (

let uu____18008 = (encode_smt_lemma env1 lid tt)
in (FStar_List.append decls uu____18008))
in ((uu____18005), (env1)))
end
| uu____18013 -> begin
((decls), (env1))
end))
end))))


let encode_top_level_vals : env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____18063 lb -> (match (uu____18063) with
| (decls, env1) -> begin
(

let uu____18083 = (

let uu____18090 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val false env1 uu____18090 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (uu____18083) with
| (decls', env2) -> begin
(((FStar_List.append decls decls')), (env2))
end))
end)) (([]), (env)))))


let is_tactic : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let fstar_tactics_tactic_lid = (FStar_Parser_Const.p2l (("FStar")::("Tactics")::("tactic")::[]))
in (

let uu____18112 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____18112) with
| (hd1, args) -> begin
(

let uu____18149 = (

let uu____18150 = (FStar_Syntax_Util.un_uinst hd1)
in uu____18150.FStar_Syntax_Syntax.n)
in (match (uu____18149) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____18154, c) -> begin
(

let effect_name = (FStar_Syntax_Util.comp_effect_name c)
in (FStar_Util.starts_with "FStar.Tactics" effect_name.FStar_Ident.str))
end
| uu____18173 -> begin
false
end))
end))))


let encode_top_level_let : env_t  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env uu____18198 quals -> (match (uu____18198) with
| (is_rec, bindings) -> begin
(

let eta_expand1 = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let uu____18274 = (FStar_Util.first_N nbinders formals)
in (match (uu____18274) with
| (formals1, extra_formals) -> begin
(

let subst1 = (FStar_List.map2 (fun uu____18355 uu____18356 -> (match (((uu____18355), (uu____18356))) with
| ((formal, uu____18374), (binder, uu____18376)) -> begin
(

let uu____18385 = (

let uu____18392 = (FStar_Syntax_Syntax.bv_to_name binder)
in ((formal), (uu____18392)))
in FStar_Syntax_Syntax.NT (uu____18385))
end)) formals1 binders)
in (

let extra_formals1 = (

let uu____18400 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun uu____18431 -> (match (uu____18431) with
| (x, i) -> begin
(

let uu____18442 = (

let uu___174_18443 = x
in (

let uu____18444 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___174_18443.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___174_18443.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____18444}))
in ((uu____18442), (i)))
end))))
in (FStar_All.pipe_right uu____18400 FStar_Syntax_Util.name_binders))
in (

let body1 = (

let uu____18462 = (

let uu____18463 = (FStar_Syntax_Subst.compress body)
in (

let uu____18464 = (

let uu____18465 = (FStar_Syntax_Util.args_of_binders extra_formals1)
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____18465))
in (FStar_Syntax_Syntax.extend_app_n uu____18463 uu____18464)))
in (uu____18462 FStar_Pervasives_Native.None body.FStar_Syntax_Syntax.pos))
in (((FStar_List.append binders extra_formals1)), (body1)))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (

let get_result_type = (fun c -> (

let uu____18526 = (FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c)
in (match (uu____18526) with
| true -> begin
(FStar_TypeChecker_Env.reify_comp (

let uu___175_18529 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___175_18529.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___175_18529.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___175_18529.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___175_18529.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___175_18529.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___175_18529.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___175_18529.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___175_18529.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___175_18529.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___175_18529.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___175_18529.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___175_18529.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___175_18529.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___175_18529.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___175_18529.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___175_18529.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___175_18529.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___175_18529.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___175_18529.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___175_18529.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___175_18529.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___175_18529.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___175_18529.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___175_18529.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___175_18529.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___175_18529.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___175_18529.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___175_18529.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___175_18529.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___175_18529.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___175_18529.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___175_18529.FStar_TypeChecker_Env.dsenv}) c FStar_Syntax_Syntax.U_unknown)
end
| uu____18530 -> begin
(FStar_Syntax_Util.comp_result c)
end)))
in (

let rec aux = (fun norm1 t_norm1 -> (

let uu____18562 = (FStar_Syntax_Util.abs_formals e)
in (match (uu____18562) with
| (binders, body, lopt) -> begin
(match (binders) with
| (uu____18626)::uu____18627 -> begin
(

let uu____18642 = (

let uu____18643 = (

let uu____18646 = (FStar_Syntax_Subst.compress t_norm1)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____18646))
in uu____18643.FStar_Syntax_Syntax.n)
in (match (uu____18642) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____18689 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____18689) with
| (formals1, c1) -> begin
(

let nformals = (FStar_List.length formals1)
in (

let nbinders = (FStar_List.length binders)
in (

let tres = (get_result_type c1)
in (

let uu____18731 = ((nformals < nbinders) && (FStar_Syntax_Util.is_total_comp c1))
in (match (uu____18731) with
| true -> begin
(

let uu____18766 = (FStar_Util.first_N nformals binders)
in (match (uu____18766) with
| (bs0, rest) -> begin
(

let c2 = (

let subst1 = (FStar_List.map2 (fun uu____18860 uu____18861 -> (match (((uu____18860), (uu____18861))) with
| ((x, uu____18879), (b, uu____18881)) -> begin
(

let uu____18890 = (

let uu____18897 = (FStar_Syntax_Syntax.bv_to_name b)
in ((x), (uu____18897)))
in FStar_Syntax_Syntax.NT (uu____18890))
end)) formals1 bs0)
in (FStar_Syntax_Subst.subst_comp subst1 c1))
in (

let body1 = (FStar_Syntax_Util.abs rest body lopt)
in (

let uu____18899 = (

let uu____18920 = (get_result_type c2)
in ((bs0), (body1), (bs0), (uu____18920)))
in ((uu____18899), (false)))))
end))
end
| uu____18953 -> begin
(match ((nformals > nbinders)) with
| true -> begin
(

let uu____18988 = (eta_expand1 binders formals1 body tres)
in (match (uu____18988) with
| (binders1, body1) -> begin
((((binders1), (body1), (formals1), (tres))), (false))
end))
end
| uu____19067 -> begin
((((binders), (body), (formals1), (tres))), (false))
end)
end)))))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____19077) -> begin
(

let uu____19082 = (

let uu____19103 = (aux norm1 x.FStar_Syntax_Syntax.sort)
in (FStar_Pervasives_Native.fst uu____19103))
in ((uu____19082), (true)))
end
| uu____19168 when (not (norm1)) -> begin
(

let t_norm2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm1)
in (aux true t_norm2))
end
| uu____19170 -> begin
(

let uu____19171 = (

let uu____19172 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____19173 = (FStar_Syntax_Print.term_to_string t_norm1)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str uu____19172 uu____19173)))
in (failwith uu____19171))
end))
end
| uu____19198 -> begin
(

let uu____19199 = (

let uu____19200 = (FStar_Syntax_Subst.compress t_norm1)
in uu____19200.FStar_Syntax_Syntax.n)
in (match (uu____19199) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____19245 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____19245) with
| (formals1, c1) -> begin
(

let tres = (get_result_type c1)
in (

let uu____19277 = (eta_expand1 [] formals1 e tres)
in (match (uu____19277) with
| (binders1, body1) -> begin
((((binders1), (body1), (formals1), (tres))), (false))
end)))
end))
end
| uu____19360 -> begin
(((([]), (e), ([]), (t_norm1))), (false))
end))
end)
end)))
in (aux false t_norm))))
in (FStar_All.try_with (fun uu___177_19409 -> (match (()) with
| () -> begin
(

let uu____19416 = (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> ((FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))))
in (match (uu____19416) with
| true -> begin
(encode_top_level_vals env bindings quals)
end
| uu____19427 -> begin
(

let uu____19428 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____19522 lb -> (match (uu____19522) with
| (toks, typs, decls, env1) -> begin
((

let uu____19617 = (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp)
in (match (uu____19617) with
| true -> begin
(FStar_Exn.raise Let_rec_unencodeable)
end
| uu____19618 -> begin
()
end));
(

let t_norm = (whnf env1 lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____19620 = (

let uu____19635 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env1 uu____19635 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (uu____19620) with
| (tok, decl, env2) -> begin
(

let uu____19681 = (

let uu____19694 = (

let uu____19705 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in ((uu____19705), (tok)))
in (uu____19694)::toks)
in ((uu____19681), ((t_norm)::typs), ((decl)::decls), (env2)))
end)));
)
end)) (([]), ([]), ([]), (env))))
in (match (uu____19428) with
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
| uu____19888 -> begin
(match (curry) with
| true -> begin
(match (ftok) with
| FStar_Pervasives_Native.Some (ftok1) -> begin
(mk_Apply ftok1 vars)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____19896 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply uu____19896 vars))
end)
end
| uu____19897 -> begin
(

let uu____19898 = (

let uu____19905 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (uu____19905)))
in (FStar_SMTEncoding_Util.mkApp uu____19898))
end)
end))
in (

let encode_non_rec_lbdef = (fun bindings1 typs2 toks2 env2 -> (match (((bindings1), (typs2), (toks2))) with
| (({FStar_Syntax_Syntax.lbname = uu____19987; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____19989; FStar_Syntax_Syntax.lbeff = uu____19990; FStar_Syntax_Syntax.lbdef = e})::[], (t_norm)::[], ((flid_fv, (f, ftok)))::[]) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____20053 = (

let uu____20060 = (FStar_TypeChecker_Env.open_universes_in env2.tcenv uvs ((e)::(t_norm)::[]))
in (match (uu____20060) with
| (tcenv', uu____20078, e_t) -> begin
(

let uu____20084 = (match (e_t) with
| (e1)::(t_norm1)::[] -> begin
((e1), (t_norm1))
end
| uu____20095 -> begin
(failwith "Impossible")
end)
in (match (uu____20084) with
| (e1, t_norm1) -> begin
(((

let uu___178_20111 = env2
in {bindings = uu___178_20111.bindings; depth = uu___178_20111.depth; tcenv = tcenv'; warn = uu___178_20111.warn; cache = uu___178_20111.cache; nolabels = uu___178_20111.nolabels; use_zfuel_name = uu___178_20111.use_zfuel_name; encode_non_total_function_typ = uu___178_20111.encode_non_total_function_typ; current_module_name = uu___178_20111.current_module_name})), (e1), (t_norm1))
end))
end))
in (match (uu____20053) with
| (env', e1, t_norm1) -> begin
(

let uu____20121 = (destruct_bound_function flid t_norm1 e1)
in (match (uu____20121) with
| ((binders, body, uu____20142, uu____20143), curry) -> begin
((

let uu____20154 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____20154) with
| true -> begin
(

let uu____20155 = (FStar_Syntax_Print.binders_to_string ", " binders)
in (

let uu____20156 = (FStar_Syntax_Print.term_to_string body)
in (FStar_Util.print2 "Encoding let : binders=[%s], body=%s\n" uu____20155 uu____20156)))
end
| uu____20157 -> begin
()
end));
(

let uu____20158 = (encode_binders FStar_Pervasives_Native.None binders env')
in (match (uu____20158) with
| (vars, guards, env'1, binder_decls, uu____20185) -> begin
(

let body1 = (

let uu____20199 = (FStar_TypeChecker_Env.is_reifiable_function env'1.tcenv t_norm1)
in (match (uu____20199) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env'1.tcenv body)
end
| uu____20200 -> begin
body
end))
in (

let app = (mk_app1 curry f ftok vars)
in (

let uu____20202 = (

let uu____20211 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic))
in (match (uu____20211) with
| true -> begin
(

let uu____20222 = (FStar_SMTEncoding_Term.mk_Valid app)
in (

let uu____20223 = (encode_formula body1 env'1)
in ((uu____20222), (uu____20223))))
end
| uu____20232 -> begin
(

let uu____20233 = (encode_term body1 env'1)
in ((app), (uu____20233)))
end))
in (match (uu____20202) with
| (app1, (body2, decls2)) -> begin
(

let eqn = (

let uu____20256 = (

let uu____20263 = (

let uu____20264 = (

let uu____20275 = (FStar_SMTEncoding_Util.mkEq ((app1), (body2)))
in ((((app1)::[])::[]), (vars), (uu____20275)))
in (FStar_SMTEncoding_Util.mkForall uu____20264))
in (

let uu____20286 = (

let uu____20289 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in FStar_Pervasives_Native.Some (uu____20289))
in ((uu____20263), (uu____20286), ((Prims.strcat "equation_" f)))))
in (FStar_SMTEncoding_Util.mkAssume uu____20256))
in (

let uu____20292 = (

let uu____20295 = (

let uu____20298 = (

let uu____20301 = (

let uu____20304 = (primitive_type_axioms env2.tcenv flid f app1)
in (FStar_List.append ((eqn)::[]) uu____20304))
in (FStar_List.append decls2 uu____20301))
in (FStar_List.append binder_decls uu____20298))
in (FStar_List.append decls1 uu____20295))
in ((uu____20292), (env2))))
end))))
end));
)
end))
end)))
end
| uu____20309 -> begin
(failwith "Impossible")
end))
in (

let encode_rec_lbdefs = (fun bindings1 typs2 toks2 env2 -> (

let fuel = (

let uu____20394 = (varops.fresh "fuel")
in ((uu____20394), (FStar_SMTEncoding_Term.Fuel_sort)))
in (

let fuel_tm = (FStar_SMTEncoding_Util.mkFreeV fuel)
in (

let env0 = env2
in (

let uu____20397 = (FStar_All.pipe_right toks2 (FStar_List.fold_left (fun uu____20485 uu____20486 -> (match (((uu____20485), (uu____20486))) with
| ((gtoks, env3), (flid_fv, (f, ftok))) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let g = (

let uu____20634 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented")
in (varops.new_fvar uu____20634))
in (

let gtok = (

let uu____20636 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented_token")
in (varops.new_fvar uu____20636))
in (

let env4 = (

let uu____20638 = (

let uu____20641 = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::[])))
in (FStar_All.pipe_left (fun _0_44 -> FStar_Pervasives_Native.Some (_0_44)) uu____20641))
in (push_free_var env3 flid gtok uu____20638))
in (((((flid), (f), (ftok), (g), (gtok)))::gtoks), (env4))))))
end)) (([]), (env2))))
in (match (uu____20397) with
| (gtoks, env3) -> begin
(

let gtoks1 = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env01 uu____20797 t_norm uu____20799 -> (match (((uu____20797), (uu____20799))) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = lbn; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____20843; FStar_Syntax_Syntax.lbeff = uu____20844; FStar_Syntax_Syntax.lbdef = e}) -> begin
(

let uu____20872 = (

let uu____20879 = (FStar_TypeChecker_Env.open_universes_in env3.tcenv uvs ((e)::(t_norm)::[]))
in (match (uu____20879) with
| (tcenv', uu____20901, e_t) -> begin
(

let uu____20907 = (match (e_t) with
| (e1)::(t_norm1)::[] -> begin
((e1), (t_norm1))
end
| uu____20918 -> begin
(failwith "Impossible")
end)
in (match (uu____20907) with
| (e1, t_norm1) -> begin
(((

let uu___179_20934 = env3
in {bindings = uu___179_20934.bindings; depth = uu___179_20934.depth; tcenv = tcenv'; warn = uu___179_20934.warn; cache = uu___179_20934.cache; nolabels = uu___179_20934.nolabels; use_zfuel_name = uu___179_20934.use_zfuel_name; encode_non_total_function_typ = uu___179_20934.encode_non_total_function_typ; current_module_name = uu___179_20934.current_module_name})), (e1), (t_norm1))
end))
end))
in (match (uu____20872) with
| (env', e1, t_norm1) -> begin
((

let uu____20949 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env01.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____20949) with
| true -> begin
(

let uu____20950 = (FStar_Syntax_Print.lbname_to_string lbn)
in (

let uu____20951 = (FStar_Syntax_Print.term_to_string t_norm1)
in (

let uu____20952 = (FStar_Syntax_Print.term_to_string e1)
in (FStar_Util.print3 "Encoding let rec %s : %s = %s\n" uu____20950 uu____20951 uu____20952))))
end
| uu____20953 -> begin
()
end));
(

let uu____20954 = (destruct_bound_function flid t_norm1 e1)
in (match (uu____20954) with
| ((binders, body, formals, tres), curry) -> begin
((

let uu____20991 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env01.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____20991) with
| true -> begin
(

let uu____20992 = (FStar_Syntax_Print.binders_to_string ", " binders)
in (

let uu____20993 = (FStar_Syntax_Print.term_to_string body)
in (

let uu____20994 = (FStar_Syntax_Print.binders_to_string ", " formals)
in (

let uu____20995 = (FStar_Syntax_Print.term_to_string tres)
in (FStar_Util.print4 "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n" uu____20992 uu____20993 uu____20994 uu____20995)))))
end
| uu____20996 -> begin
()
end));
(match (curry) with
| true -> begin
(failwith "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type")
end
| uu____20998 -> begin
()
end);
(

let uu____20999 = (encode_binders FStar_Pervasives_Native.None binders env')
in (match (uu____20999) with
| (vars, guards, env'1, binder_decls, uu____21030) -> begin
(

let decl_g = (

let uu____21044 = (

let uu____21055 = (

let uu____21058 = (FStar_List.map FStar_Pervasives_Native.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::uu____21058)
in ((g), (uu____21055), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Fuel-instrumented function name"))))
in FStar_SMTEncoding_Term.DeclFun (uu____21044))
in (

let env02 = (push_zfuel_name env01 flid g)
in (

let decl_g_tok = FStar_SMTEncoding_Term.DeclFun (((gtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Token for fuel-instrumented partial applications"))))
in (

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let app = (

let uu____21083 = (

let uu____21090 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (uu____21090)))
in (FStar_SMTEncoding_Util.mkApp uu____21083))
in (

let gsapp = (

let uu____21100 = (

let uu____21107 = (

let uu____21110 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (uu____21110)::vars_tm)
in ((g), (uu____21107)))
in (FStar_SMTEncoding_Util.mkApp uu____21100))
in (

let gmax = (

let uu____21116 = (

let uu____21123 = (

let uu____21126 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (uu____21126)::vars_tm)
in ((g), (uu____21123)))
in (FStar_SMTEncoding_Util.mkApp uu____21116))
in (

let body1 = (

let uu____21132 = (FStar_TypeChecker_Env.is_reifiable_function env'1.tcenv t_norm1)
in (match (uu____21132) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env'1.tcenv body)
end
| uu____21133 -> begin
body
end))
in (

let uu____21134 = (encode_term body1 env'1)
in (match (uu____21134) with
| (body_tm, decls2) -> begin
(

let eqn_g = (

let uu____21152 = (

let uu____21159 = (

let uu____21160 = (

let uu____21175 = (FStar_SMTEncoding_Util.mkEq ((gsapp), (body_tm)))
in ((((gsapp)::[])::[]), (FStar_Pervasives_Native.Some ((Prims.parse_int "0"))), ((fuel)::vars), (uu____21175)))
in (FStar_SMTEncoding_Util.mkForall' uu____21160))
in (

let uu____21196 = (

let uu____21199 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in FStar_Pervasives_Native.Some (uu____21199))
in ((uu____21159), (uu____21196), ((Prims.strcat "equation_with_fuel_" g)))))
in (FStar_SMTEncoding_Util.mkAssume uu____21152))
in (

let eqn_f = (

let uu____21203 = (

let uu____21210 = (

let uu____21211 = (

let uu____21222 = (FStar_SMTEncoding_Util.mkEq ((app), (gmax)))
in ((((app)::[])::[]), (vars), (uu____21222)))
in (FStar_SMTEncoding_Util.mkForall uu____21211))
in ((uu____21210), (FStar_Pervasives_Native.Some ("Correspondence of recursive function to instrumented version")), ((Prims.strcat "@fuel_correspondence_" g))))
in (FStar_SMTEncoding_Util.mkAssume uu____21203))
in (

let eqn_g' = (

let uu____21236 = (

let uu____21243 = (

let uu____21244 = (

let uu____21255 = (

let uu____21256 = (

let uu____21261 = (

let uu____21262 = (

let uu____21269 = (

let uu____21272 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "0"))
in (uu____21272)::vars_tm)
in ((g), (uu____21269)))
in (FStar_SMTEncoding_Util.mkApp uu____21262))
in ((gsapp), (uu____21261)))
in (FStar_SMTEncoding_Util.mkEq uu____21256))
in ((((gsapp)::[])::[]), ((fuel)::vars), (uu____21255)))
in (FStar_SMTEncoding_Util.mkForall uu____21244))
in ((uu____21243), (FStar_Pervasives_Native.Some ("Fuel irrelevance")), ((Prims.strcat "@fuel_irrelevance_" g))))
in (FStar_SMTEncoding_Util.mkAssume uu____21236))
in (

let uu____21295 = (

let uu____21304 = (encode_binders FStar_Pervasives_Native.None formals env02)
in (match (uu____21304) with
| (vars1, v_guards, env4, binder_decls1, uu____21333) -> begin
(

let vars_tm1 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars1)
in (

let gapp = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::vars_tm1)))
in (

let tok_corr = (

let tok_app = (

let uu____21358 = (FStar_SMTEncoding_Util.mkFreeV ((gtok), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply uu____21358 ((fuel)::vars1)))
in (

let uu____21363 = (

let uu____21370 = (

let uu____21371 = (

let uu____21382 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (gapp)))
in ((((tok_app)::[])::[]), ((fuel)::vars1), (uu____21382)))
in (FStar_SMTEncoding_Util.mkForall uu____21371))
in ((uu____21370), (FStar_Pervasives_Native.Some ("Fuel token correspondence")), ((Prims.strcat "fuel_token_correspondence_" gtok))))
in (FStar_SMTEncoding_Util.mkAssume uu____21363)))
in (

let uu____21403 = (

let uu____21410 = (encode_term_pred FStar_Pervasives_Native.None tres env4 gapp)
in (match (uu____21410) with
| (g_typing, d3) -> begin
(

let uu____21423 = (

let uu____21426 = (

let uu____21427 = (

let uu____21434 = (

let uu____21435 = (

let uu____21446 = (

let uu____21447 = (

let uu____21452 = (FStar_SMTEncoding_Util.mk_and_l v_guards)
in ((uu____21452), (g_typing)))
in (FStar_SMTEncoding_Util.mkImp uu____21447))
in ((((gapp)::[])::[]), ((fuel)::vars1), (uu____21446)))
in (FStar_SMTEncoding_Util.mkForall uu____21435))
in ((uu____21434), (FStar_Pervasives_Native.Some ("Typing correspondence of token to term")), ((Prims.strcat "token_correspondence_" g))))
in (FStar_SMTEncoding_Util.mkAssume uu____21427))
in (uu____21426)::[])
in ((d3), (uu____21423)))
end))
in (match (uu____21403) with
| (aux_decls, typing_corr) -> begin
(((FStar_List.append binder_decls1 aux_decls)), ((FStar_List.append typing_corr ((tok_corr)::[]))))
end)))))
end))
in (match (uu____21295) with
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

let uu____21517 = (

let uu____21530 = (FStar_List.zip3 gtoks1 typs2 bindings1)
in (FStar_List.fold_left (fun uu____21609 uu____21610 -> (match (((uu____21609), (uu____21610))) with
| ((decls2, eqns, env01), (gtok, ty, lb)) -> begin
(

let uu____21765 = (encode_one_binding env01 gtok ty lb)
in (match (uu____21765) with
| (decls', eqns', env02) -> begin
(((decls')::decls2), ((FStar_List.append eqns' eqns)), (env02))
end))
end)) (((decls1)::[]), ([]), (env0)) uu____21530))
in (match (uu____21517) with
| (decls2, eqns, env01) -> begin
(

let uu____21838 = (

let isDeclFun = (fun uu___145_21850 -> (match (uu___145_21850) with
| FStar_SMTEncoding_Term.DeclFun (uu____21851) -> begin
true
end
| uu____21862 -> begin
false
end))
in (

let uu____21863 = (FStar_All.pipe_right decls2 FStar_List.flatten)
in (FStar_All.pipe_right uu____21863 (FStar_List.partition isDeclFun))))
in (match (uu____21838) with
| (prefix_decls, rest) -> begin
(

let eqns1 = (FStar_List.rev eqns)
in (((FStar_List.append prefix_decls (FStar_List.append rest eqns1))), (env01)))
end))
end))))
end))))))
in (

let uu____21903 = ((FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___146_21907 -> (match (uu___146_21907) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| uu____21908 -> begin
false
end)))) || (FStar_All.pipe_right typs1 (FStar_Util.for_some (fun t -> (

let uu____21914 = ((FStar_Syntax_Util.is_pure_or_ghost_function t) || (FStar_TypeChecker_Env.is_reifiable_function env1.tcenv t))
in (FStar_All.pipe_left Prims.op_Negation uu____21914))))))
in (match (uu____21903) with
| true -> begin
((decls1), (env1))
end
| uu____21923 -> begin
(FStar_All.try_with (fun uu___181_21931 -> (match (()) with
| () -> begin
(match ((not (is_rec))) with
| true -> begin
(encode_non_rec_lbdef bindings typs1 toks1 env1)
end
| uu____21944 -> begin
(encode_rec_lbdefs bindings typs1 toks1 env1)
end)
end)) (fun uu___180_21946 -> (match (uu___180_21946) with
| Inner_let_rec -> begin
((decls1), (env1))
end)))
end))))))))
end))
end))
end)) (fun uu___176_21958 -> (match (uu___176_21958) with
| Let_rec_unencodeable -> begin
(

let msg = (

let uu____21966 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right uu____21966 (FStar_String.concat " and ")))
in (

let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in (((decl)::[]), (env))))
end)))))
end))


let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let nm = (

let uu____22015 = (FStar_Syntax_Util.lid_of_sigelt se)
in (match (uu____22015) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (l) -> begin
l.FStar_Ident.str
end))
in (

let uu____22019 = (encode_sigelt' env se)
in (match (uu____22019) with
| (g, env1) -> begin
(

let g1 = (match (g) with
| [] -> begin
(

let uu____22035 = (

let uu____22036 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (uu____22036))
in (uu____22035)::[])
end
| uu____22037 -> begin
(

let uu____22038 = (

let uu____22041 = (

let uu____22042 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____22042))
in (uu____22041)::g)
in (

let uu____22043 = (

let uu____22046 = (

let uu____22047 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____22047))
in (uu____22046)::[])
in (FStar_List.append uu____22038 uu____22043)))
end)
in ((g1), (env1)))
end))))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let is_opaque_to_smt = (fun t -> (

let uu____22060 = (

let uu____22061 = (FStar_Syntax_Subst.compress t)
in uu____22061.FStar_Syntax_Syntax.n)
in (match (uu____22060) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____22065)) -> begin
(Prims.op_Equality s "opaque_to_smt")
end
| uu____22066 -> begin
false
end)))
in (

let is_uninterpreted_by_smt = (fun t -> (

let uu____22071 = (

let uu____22072 = (FStar_Syntax_Subst.compress t)
in uu____22072.FStar_Syntax_Syntax.n)
in (match (uu____22071) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____22076)) -> begin
(Prims.op_Equality s "uninterpreted_by_smt")
end
| uu____22077 -> begin
false
end)))
in (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____22082) -> begin
(failwith "impossible -- removed by tc.fs")
end
| FStar_Syntax_Syntax.Sig_pragma (uu____22087) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_main (uu____22090) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____22093) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____22108) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(

let uu____22112 = (

let uu____22113 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right uu____22113 Prims.op_Negation))
in (match (uu____22112) with
| true -> begin
(([]), (env))
end
| uu____22122 -> begin
(

let close_effect_params = (fun tm -> (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
tm
end
| uu____22139 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((ed.FStar_Syntax_Syntax.binders), (tm), (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[]))))))) FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)
end))
in (

let encode_action = (fun env1 a -> (

let uu____22159 = (new_term_constant_and_tok_from_lid env1 a.FStar_Syntax_Syntax.action_name)
in (match (uu____22159) with
| (aname, atok, env2) -> begin
(

let uu____22175 = (FStar_Syntax_Util.arrow_formals_comp a.FStar_Syntax_Syntax.action_typ)
in (match (uu____22175) with
| (formals, uu____22193) -> begin
(

let uu____22206 = (

let uu____22211 = (close_effect_params a.FStar_Syntax_Syntax.action_defn)
in (encode_term uu____22211 env2))
in (match (uu____22206) with
| (tm, decls) -> begin
(

let a_decls = (

let uu____22223 = (

let uu____22224 = (

let uu____22235 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____22251 -> FStar_SMTEncoding_Term.Term_sort)))
in ((aname), (uu____22235), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Action"))))
in FStar_SMTEncoding_Term.DeclFun (uu____22224))
in (uu____22223)::(FStar_SMTEncoding_Term.DeclFun (((atok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Action token")))))::[])
in (

let uu____22264 = (

let aux = (fun uu____22316 uu____22317 -> (match (((uu____22316), (uu____22317))) with
| ((bv, uu____22369), (env3, acc_sorts, acc)) -> begin
(

let uu____22407 = (gen_term_var env3 bv)
in (match (uu____22407) with
| (xxsym, xx, env4) -> begin
((env4), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::acc_sorts), ((xx)::acc))
end))
end))
in (FStar_List.fold_right aux formals ((env2), ([]), ([]))))
in (match (uu____22264) with
| (uu____22479, xs_sorts, xs) -> begin
(

let app = (FStar_SMTEncoding_Util.mkApp ((aname), (xs)))
in (

let a_eq = (

let uu____22502 = (

let uu____22509 = (

let uu____22510 = (

let uu____22521 = (

let uu____22522 = (

let uu____22527 = (mk_Apply tm xs_sorts)
in ((app), (uu____22527)))
in (FStar_SMTEncoding_Util.mkEq uu____22522))
in ((((app)::[])::[]), (xs_sorts), (uu____22521)))
in (FStar_SMTEncoding_Util.mkForall uu____22510))
in ((uu____22509), (FStar_Pervasives_Native.Some ("Action equality")), ((Prims.strcat aname "_equality"))))
in (FStar_SMTEncoding_Util.mkAssume uu____22502))
in (

let tok_correspondence = (

let tok_term = (FStar_SMTEncoding_Util.mkFreeV ((atok), (FStar_SMTEncoding_Term.Term_sort)))
in (

let tok_app = (mk_Apply tok_term xs_sorts)
in (

let uu____22547 = (

let uu____22554 = (

let uu____22555 = (

let uu____22566 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (app)))
in ((((tok_app)::[])::[]), (xs_sorts), (uu____22566)))
in (FStar_SMTEncoding_Util.mkForall uu____22555))
in ((uu____22554), (FStar_Pervasives_Native.Some ("Action token correspondence")), ((Prims.strcat aname "_token_correspondence"))))
in (FStar_SMTEncoding_Util.mkAssume uu____22547))))
in ((env2), ((FStar_List.append decls (FStar_List.append a_decls ((a_eq)::(tok_correspondence)::[]))))))))
end)))
end))
end))
end)))
in (

let uu____22585 = (FStar_Util.fold_map encode_action env ed.FStar_Syntax_Syntax.actions)
in (match (uu____22585) with
| (env1, decls2) -> begin
(((FStar_List.flatten decls2)), (env1))
end))))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____22613, uu____22614) when (FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid) -> begin
(

let uu____22615 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____22615) with
| (tname, ttok, env1) -> begin
(([]), (env1))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____22632, t) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let will_encode_definition = (

let uu____22638 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___147_22642 -> (match (uu___147_22642) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.Projector (uu____22643) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____22648) -> begin
true
end
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| uu____22649 -> begin
false
end))))
in (not (uu____22638)))
in (match (will_encode_definition) with
| true -> begin
(([]), (env))
end
| uu____22656 -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____22658 = (

let uu____22665 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs (FStar_Util.for_some is_uninterpreted_by_smt))
in (encode_top_level_val uu____22665 env fv t quals))
in (match (uu____22658) with
| (decls, env1) -> begin
(

let tname = lid.FStar_Ident.str
in (

let tsym = (FStar_SMTEncoding_Util.mkFreeV ((tname), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____22680 = (

let uu____22683 = (primitive_type_axioms env1.tcenv lid tname tsym)
in (FStar_List.append decls uu____22683))
in ((uu____22680), (env1)))))
end)))
end)))
end
| FStar_Syntax_Syntax.Sig_assume (l, us, f) -> begin
(

let uu____22691 = (FStar_Syntax_Subst.open_univ_vars us f)
in (match (uu____22691) with
| (uu____22700, f1) -> begin
(

let uu____22702 = (encode_formula f1 env)
in (match (uu____22702) with
| (f2, decls) -> begin
(

let g = (

let uu____22716 = (

let uu____22717 = (

let uu____22724 = (

let uu____22727 = (

let uu____22728 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" uu____22728))
in FStar_Pervasives_Native.Some (uu____22727))
in (

let uu____22729 = (varops.mk_unique (Prims.strcat "assumption_" l.FStar_Ident.str))
in ((f2), (uu____22724), (uu____22729))))
in (FStar_SMTEncoding_Util.mkAssume uu____22717))
in (uu____22716)::[])
in (((FStar_List.append decls g)), (env)))
end))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____22735) when ((FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) || (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs (FStar_Util.for_some is_opaque_to_smt))) -> begin
(

let attrs = se.FStar_Syntax_Syntax.sigattrs
in (

let uu____22747 = (FStar_Util.fold_map (fun env1 lb -> (

let lid = (

let uu____22765 = (

let uu____22768 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____22768.FStar_Syntax_Syntax.fv_name)
in uu____22765.FStar_Syntax_Syntax.v)
in (

let uu____22769 = (

let uu____22770 = (FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone uu____22770))
in (match (uu____22769) with
| true -> begin
(

let val_decl = (

let uu___182_22798 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = uu___182_22798.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Irreducible)::se.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___182_22798.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___182_22798.FStar_Syntax_Syntax.sigattrs})
in (

let uu____22803 = (encode_sigelt' env1 val_decl)
in (match (uu____22803) with
| (decls, env2) -> begin
((env2), (decls))
end)))
end
| uu____22814 -> begin
((env1), ([]))
end)))) env (FStar_Pervasives_Native.snd lbs))
in (match (uu____22747) with
| (env1, decls) -> begin
(((FStar_List.flatten decls)), (env1))
end)))
end
| FStar_Syntax_Syntax.Sig_let ((uu____22831, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t1); FStar_Syntax_Syntax.lbunivs = uu____22833; FStar_Syntax_Syntax.lbtyp = uu____22834; FStar_Syntax_Syntax.lbeff = uu____22835; FStar_Syntax_Syntax.lbdef = uu____22836})::[]), uu____22837) when (FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid) -> begin
(

let uu____22856 = (new_term_constant_and_tok_from_lid env b2t1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____22856) with
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

let uu____22885 = (

let uu____22888 = (

let uu____22889 = (

let uu____22896 = (

let uu____22897 = (

let uu____22908 = (

let uu____22909 = (

let uu____22914 = (FStar_SMTEncoding_Util.mkApp (((FStar_Pervasives_Native.snd FStar_SMTEncoding_Term.boxBoolFun)), ((x)::[])))
in ((valid_b2t_x), (uu____22914)))
in (FStar_SMTEncoding_Util.mkEq uu____22909))
in ((((b2t_x)::[])::[]), ((xx)::[]), (uu____22908)))
in (FStar_SMTEncoding_Util.mkForall uu____22897))
in ((uu____22896), (FStar_Pervasives_Native.Some ("b2t def")), ("b2t_def")))
in (FStar_SMTEncoding_Util.mkAssume uu____22889))
in (uu____22888)::[])
in (FStar_SMTEncoding_Term.DeclFun (((tname), ((FStar_SMTEncoding_Term.Term_sort)::[]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None))))::uu____22885)
in ((decls), (env1)))))))
end))
end
| FStar_Syntax_Syntax.Sig_let (uu____22947, uu____22948) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___148_22957 -> (match (uu___148_22957) with
| FStar_Syntax_Syntax.Discriminator (uu____22958) -> begin
true
end
| uu____22959 -> begin
false
end)))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let (uu____22962, lids) when ((FStar_All.pipe_right lids (FStar_Util.for_some (fun l -> (

let uu____22973 = (

let uu____22974 = (FStar_List.hd l.FStar_Ident.ns)
in uu____22974.FStar_Ident.idText)
in (Prims.op_Equality uu____22973 "Prims"))))) && (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___149_22978 -> (match (uu___149_22978) with
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
true
end
| uu____22979 -> begin
false
end))))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____22983) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___150_23000 -> (match (uu___150_23000) with
| FStar_Syntax_Syntax.Projector (uu____23001) -> begin
true
end
| uu____23006 -> begin
false
end)))) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____23009 = (try_lookup_free_var env l)
in (match (uu____23009) with
| FStar_Pervasives_Native.Some (uu____23016) -> begin
(([]), (env))
end
| FStar_Pervasives_Native.None -> begin
(

let se1 = (

let uu___183_23020 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l); FStar_Syntax_Syntax.sigquals = uu___183_23020.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___183_23020.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___183_23020.FStar_Syntax_Syntax.sigattrs})
in (encode_sigelt env se1))
end))))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), uu____23027) -> begin
(encode_top_level_let env ((is_rec), (bindings)) se.FStar_Syntax_Syntax.sigquals)
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____23045) -> begin
(

let uu____23054 = (encode_sigelts env ses)
in (match (uu____23054) with
| (g, env1) -> begin
(

let uu____23071 = (FStar_All.pipe_right g (FStar_List.partition (fun uu___151_23094 -> (match (uu___151_23094) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.assumption_term = uu____23095; FStar_SMTEncoding_Term.assumption_caption = FStar_Pervasives_Native.Some ("inversion axiom"); FStar_SMTEncoding_Term.assumption_name = uu____23096; FStar_SMTEncoding_Term.assumption_fact_ids = uu____23097}) -> begin
false
end
| uu____23100 -> begin
true
end))))
in (match (uu____23071) with
| (g', inversions) -> begin
(

let uu____23115 = (FStar_All.pipe_right g' (FStar_List.partition (fun uu___152_23136 -> (match (uu___152_23136) with
| FStar_SMTEncoding_Term.DeclFun (uu____23137) -> begin
true
end
| uu____23148 -> begin
false
end))))
in (match (uu____23115) with
| (decls, rest) -> begin
(((FStar_List.append decls (FStar_List.append rest inversions))), (env1))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, uu____23166, tps, k, uu____23169, datas) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___153_23186 -> (match (uu___153_23186) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____23187 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> (match (is_logical) with
| true -> begin
(

let uu____23196 = c
in (match (uu____23196) with
| (name, args, uu____23201, uu____23202, uu____23203) -> begin
(

let uu____23208 = (

let uu____23209 = (

let uu____23220 = (FStar_All.pipe_right args (FStar_List.map (fun uu____23237 -> (match (uu____23237) with
| (uu____23244, sort, uu____23246) -> begin
sort
end))))
in ((name), (uu____23220), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____23209))
in (uu____23208)::[])
end))
end
| uu____23251 -> begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end))
in (

let inversion_axioms = (fun tapp vars -> (

let uu____23273 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (

let uu____23279 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right uu____23279 FStar_Option.isNone)))))
in (match (uu____23273) with
| true -> begin
[]
end
| uu____23310 -> begin
(

let uu____23311 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____23311) with
| (xxsym, xx) -> begin
(

let uu____23320 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun uu____23359 l -> (match (uu____23359) with
| (out, decls) -> begin
(

let uu____23379 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (uu____23379) with
| (uu____23390, data_t) -> begin
(

let uu____23392 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (uu____23392) with
| (args, res) -> begin
(

let indices = (

let uu____23438 = (

let uu____23439 = (FStar_Syntax_Subst.compress res)
in uu____23439.FStar_Syntax_Syntax.n)
in (match (uu____23438) with
| FStar_Syntax_Syntax.Tm_app (uu____23450, indices) -> begin
indices
end
| uu____23472 -> begin
[]
end))
in (

let env1 = (FStar_All.pipe_right args (FStar_List.fold_left (fun env1 uu____23496 -> (match (uu____23496) with
| (x, uu____23502) -> begin
(

let uu____23503 = (

let uu____23504 = (

let uu____23511 = (mk_term_projector_name l x)
in ((uu____23511), ((xx)::[])))
in (FStar_SMTEncoding_Util.mkApp uu____23504))
in (push_term_var env1 x uu____23503))
end)) env))
in (

let uu____23514 = (encode_args indices env1)
in (match (uu____23514) with
| (indices1, decls') -> begin
((match ((Prims.op_disEquality (FStar_List.length indices1) (FStar_List.length vars))) with
| true -> begin
(failwith "Impossible")
end
| uu____23538 -> begin
()
end);
(

let eqs = (

let uu____23540 = (FStar_List.map2 (fun v1 a -> (

let uu____23556 = (

let uu____23561 = (FStar_SMTEncoding_Util.mkFreeV v1)
in ((uu____23561), (a)))
in (FStar_SMTEncoding_Util.mkEq uu____23556))) vars indices1)
in (FStar_All.pipe_right uu____23540 FStar_SMTEncoding_Util.mk_and_l))
in (

let uu____23564 = (

let uu____23565 = (

let uu____23570 = (

let uu____23571 = (

let uu____23576 = (mk_data_tester env1 l xx)
in ((uu____23576), (eqs)))
in (FStar_SMTEncoding_Util.mkAnd uu____23571))
in ((out), (uu____23570)))
in (FStar_SMTEncoding_Util.mkOr uu____23565))
in ((uu____23564), ((FStar_List.append decls decls')))));
)
end))))
end))
end))
end)) ((FStar_SMTEncoding_Util.mkFalse), ([]))))
in (match (uu____23320) with
| (data_ax, decls) -> begin
(

let uu____23589 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____23589) with
| (ffsym, ff) -> begin
(

let fuel_guarded_inversion = (

let xx_has_type_sfuel = (match (((FStar_List.length datas) > (Prims.parse_int "1"))) with
| true -> begin
(

let uu____23600 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((ff)::[])))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel uu____23600 xx tapp))
end
| uu____23603 -> begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end)
in (

let uu____23604 = (

let uu____23611 = (

let uu____23612 = (

let uu____23623 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (

let uu____23638 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_sfuel), (data_ax)))
in ((((xx_has_type_sfuel)::[])::[]), (uu____23623), (uu____23638))))
in (FStar_SMTEncoding_Util.mkForall uu____23612))
in (

let uu____23653 = (varops.mk_unique (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str))
in ((uu____23611), (FStar_Pervasives_Native.Some ("inversion axiom")), (uu____23653))))
in (FStar_SMTEncoding_Util.mkAssume uu____23604)))
in (FStar_List.append decls ((fuel_guarded_inversion)::[])))
end))
end))
end))
end)))
in (

let uu____23656 = (

let uu____23669 = (

let uu____23670 = (FStar_Syntax_Subst.compress k)
in uu____23670.FStar_Syntax_Syntax.n)
in (match (uu____23669) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
(((FStar_List.append tps formals)), ((FStar_Syntax_Util.comp_result kres)))
end
| uu____23715 -> begin
((tps), (k))
end))
in (match (uu____23656) with
| (formals, res) -> begin
(

let uu____23738 = (FStar_Syntax_Subst.open_term formals res)
in (match (uu____23738) with
| (formals1, res1) -> begin
(

let uu____23749 = (encode_binders FStar_Pervasives_Native.None formals1 env)
in (match (uu____23749) with
| (vars, guards, env', binder_decls, uu____23774) -> begin
(

let uu____23787 = (new_term_constant_and_tok_from_lid env t)
in (match (uu____23787) with
| (tname, ttok, env1) -> begin
(

let ttok_tm = (FStar_SMTEncoding_Util.mkApp ((ttok), ([])))
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let tapp = (

let uu____23806 = (

let uu____23813 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((tname), (uu____23813)))
in (FStar_SMTEncoding_Util.mkApp uu____23806))
in (

let uu____23822 = (

let tname_decl = (

let uu____23832 = (

let uu____23833 = (FStar_All.pipe_right vars (FStar_List.map (fun uu____23865 -> (match (uu____23865) with
| (n1, s) -> begin
(((Prims.strcat tname n1)), (s), (false))
end))))
in (

let uu____23878 = (varops.next_id ())
in ((tname), (uu____23833), (FStar_SMTEncoding_Term.Term_sort), (uu____23878), (false))))
in (constructor_or_logic_type_decl uu____23832))
in (

let uu____23887 = (match (vars) with
| [] -> begin
(

let uu____23900 = (

let uu____23901 = (

let uu____23904 = (FStar_SMTEncoding_Util.mkApp ((tname), ([])))
in (FStar_All.pipe_left (fun _0_45 -> FStar_Pervasives_Native.Some (_0_45)) uu____23904))
in (push_free_var env1 t tname uu____23901))
in (([]), (uu____23900)))
end
| uu____23911 -> begin
(

let ttok_decl = FStar_SMTEncoding_Term.DeclFun (((ttok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("token"))))
in (

let ttok_fresh = (

let uu____23920 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ttok), (FStar_SMTEncoding_Term.Term_sort)) uu____23920))
in (

let ttok_app = (mk_Apply ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (

let uu____23934 = (

let uu____23941 = (

let uu____23942 = (

let uu____23957 = (FStar_SMTEncoding_Util.mkEq ((ttok_app), (tapp)))
in ((pats), (FStar_Pervasives_Native.None), (vars), (uu____23957)))
in (FStar_SMTEncoding_Util.mkForall' uu____23942))
in ((uu____23941), (FStar_Pervasives_Native.Some ("name-token correspondence")), ((Prims.strcat "token_correspondence_" ttok))))
in (FStar_SMTEncoding_Util.mkAssume uu____23934))
in (((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[]), (env1)))))))
end)
in (match (uu____23887) with
| (tok_decls, env2) -> begin
(((FStar_List.append tname_decl tok_decls)), (env2))
end)))
in (match (uu____23822) with
| (decls, env2) -> begin
(

let kindingAx = (

let uu____23997 = (encode_term_pred FStar_Pervasives_Native.None res1 env' tapp)
in (match (uu____23997) with
| (k1, decls1) -> begin
(

let karr = (match (((FStar_List.length formals1) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____24015 = (

let uu____24016 = (

let uu____24023 = (

let uu____24024 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____24024))
in ((uu____24023), (FStar_Pervasives_Native.Some ("kinding")), ((Prims.strcat "pre_kinding_" ttok))))
in (FStar_SMTEncoding_Util.mkAssume uu____24016))
in (uu____24015)::[])
end
| uu____24027 -> begin
[]
end)
in (

let uu____24028 = (

let uu____24031 = (

let uu____24034 = (

let uu____24035 = (

let uu____24042 = (

let uu____24043 = (

let uu____24054 = (FStar_SMTEncoding_Util.mkImp ((guard), (k1)))
in ((((tapp)::[])::[]), (vars), (uu____24054)))
in (FStar_SMTEncoding_Util.mkForall uu____24043))
in ((uu____24042), (FStar_Pervasives_Native.None), ((Prims.strcat "kinding_" ttok))))
in (FStar_SMTEncoding_Util.mkAssume uu____24035))
in (uu____24034)::[])
in (FStar_List.append karr uu____24031))
in (FStar_List.append decls1 uu____24028)))
end))
in (

let aux = (

let uu____24070 = (

let uu____24073 = (inversion_axioms tapp vars)
in (

let uu____24076 = (

let uu____24079 = (pretype_axiom env2 tapp vars)
in (uu____24079)::[])
in (FStar_List.append uu____24073 uu____24076)))
in (FStar_List.append kindingAx uu____24070))
in (

let g = (FStar_List.append decls (FStar_List.append binder_decls aux))
in ((g), (env2)))))
end)))))
end))
end))
end))
end))))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____24086, uu____24087, uu____24088, uu____24089, uu____24090) when (FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____24098, t, uu____24100, n_tps, uu____24102) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____24110 = (new_term_constant_and_tok_from_lid env d)
in (match (uu____24110) with
| (ddconstrsym, ddtok, env1) -> begin
(

let ddtok_tm = (FStar_SMTEncoding_Util.mkApp ((ddtok), ([])))
in (

let uu____24127 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____24127) with
| (formals, t_res) -> begin
(

let uu____24162 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____24162) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (

let uu____24176 = (encode_binders (FStar_Pervasives_Native.Some (fuel_tm)) formals env1)
in (match (uu____24176) with
| (vars, guards, env', binder_decls, names1) -> begin
(

let fields = (FStar_All.pipe_right names1 (FStar_List.mapi (fun n1 x -> (

let projectible = true
in (

let uu____24246 = (mk_term_projector_name d x)
in ((uu____24246), (FStar_SMTEncoding_Term.Term_sort), (projectible)))))))
in (

let datacons = (

let uu____24248 = (

let uu____24267 = (varops.next_id ())
in ((ddconstrsym), (fields), (FStar_SMTEncoding_Term.Term_sort), (uu____24267), (true)))
in (FStar_All.pipe_right uu____24248 FStar_SMTEncoding_Term.constructor_to_decl))
in (

let app = (mk_Apply ddtok_tm vars)
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (

let uu____24306 = (encode_term_pred FStar_Pervasives_Native.None t env1 ddtok_tm)
in (match (uu____24306) with
| (tok_typing, decls3) -> begin
(

let tok_typing1 = (match (fields) with
| (uu____24318)::uu____24319 -> begin
(

let ff = (("ty"), (FStar_SMTEncoding_Term.Term_sort))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV ff)
in (

let vtok_app_l = (mk_Apply ddtok_tm ((ff)::[]))
in (

let vtok_app_r = (mk_Apply f ((((ddtok), (FStar_SMTEncoding_Term.Term_sort)))::[]))
in (

let uu____24364 = (

let uu____24375 = (FStar_SMTEncoding_Term.mk_NoHoist f tok_typing)
in ((((vtok_app_l)::[])::((vtok_app_r)::[])::[]), ((ff)::[]), (uu____24375)))
in (FStar_SMTEncoding_Util.mkForall uu____24364))))))
end
| uu____24400 -> begin
tok_typing
end)
in (

let uu____24409 = (encode_binders (FStar_Pervasives_Native.Some (fuel_tm)) formals env1)
in (match (uu____24409) with
| (vars', guards', env'', decls_formals, uu____24434) -> begin
(

let uu____24447 = (

let xvars1 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars')
in (

let dapp1 = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars1)))
in (encode_term_pred (FStar_Pervasives_Native.Some (fuel_tm)) t_res env'' dapp1)))
in (match (uu____24447) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_SMTEncoding_Util.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| uu____24478 -> begin
(

let uu____24485 = (

let uu____24486 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ddtok), (FStar_SMTEncoding_Term.Term_sort)) uu____24486))
in (uu____24485)::[])
end)
in (

let encode_elim = (fun uu____24496 -> (

let uu____24497 = (FStar_Syntax_Util.head_and_args t_res)
in (match (uu____24497) with
| (head1, args) -> begin
(

let uu____24540 = (

let uu____24541 = (FStar_Syntax_Subst.compress head1)
in uu____24541.FStar_Syntax_Syntax.n)
in (match (uu____24540) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____24551; FStar_Syntax_Syntax.vars = uu____24552}, uu____24553) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let uu____24559 = (encode_args args env')
in (match (uu____24559) with
| (encoded_args, arg_decls) -> begin
(

let guards_for_parameter = (fun orig_arg arg xv -> (

let fv1 = (match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv1) -> begin
fv1
end
| uu____24602 -> begin
(

let uu____24603 = (

let uu____24604 = (

let uu____24609 = (

let uu____24610 = (FStar_Syntax_Print.term_to_string orig_arg)
in (FStar_Util.format1 "Inductive type parameter %s must be a variable ; You may want to change it to an index." uu____24610))
in ((uu____24609), (orig_arg.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____24604))
in (FStar_Exn.raise uu____24603))
end)
in (

let guards1 = (FStar_All.pipe_right guards (FStar_List.collect (fun g -> (

let uu____24626 = (

let uu____24627 = (FStar_SMTEncoding_Term.free_variables g)
in (FStar_List.contains fv1 uu____24627))
in (match (uu____24626) with
| true -> begin
(

let uu____24640 = (FStar_SMTEncoding_Term.subst g fv1 xv)
in (uu____24640)::[])
end
| uu____24641 -> begin
[]
end)))))
in (FStar_SMTEncoding_Util.mk_and_l guards1))))
in (

let uu____24642 = (

let uu____24655 = (FStar_List.zip args encoded_args)
in (FStar_List.fold_left (fun uu____24705 uu____24706 -> (match (((uu____24705), (uu____24706))) with
| ((env2, arg_vars, eqns_or_guards, i), (orig_arg, arg)) -> begin
(

let uu____24801 = (

let uu____24808 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (gen_term_var env2 uu____24808))
in (match (uu____24801) with
| (uu____24821, xv, env3) -> begin
(

let eqns = (match ((i < n_tps)) with
| true -> begin
(

let uu____24829 = (guards_for_parameter (FStar_Pervasives_Native.fst orig_arg) arg xv)
in (uu____24829)::eqns_or_guards)
end
| uu____24830 -> begin
(

let uu____24831 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (uu____24831)::eqns_or_guards)
end)
in ((env3), ((xv)::arg_vars), (eqns), ((i + (Prims.parse_int "1")))))
end))
end)) ((env'), ([]), ([]), ((Prims.parse_int "0"))) uu____24655))
in (match (uu____24642) with
| (uu____24846, arg_vars, elim_eqns_or_guards, uu____24849) -> begin
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

let uu____24879 = (

let uu____24886 = (

let uu____24887 = (

let uu____24898 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____24909 = (

let uu____24910 = (

let uu____24915 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append elim_eqns_or_guards guards))
in ((ty_pred), (uu____24915)))
in (FStar_SMTEncoding_Util.mkImp uu____24910))
in ((((ty_pred)::[])::[]), (uu____24898), (uu____24909))))
in (FStar_SMTEncoding_Util.mkForall uu____24887))
in ((uu____24886), (FStar_Pervasives_Native.Some ("data constructor typing elim")), ((Prims.strcat "data_elim_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____24879))
in (

let subterm_ordering = (match ((FStar_Ident.lid_equals d FStar_Parser_Const.lextop_lid)) with
| true -> begin
(

let x = (

let uu____24938 = (varops.fresh "x")
in ((uu____24938), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (

let uu____24940 = (

let uu____24947 = (

let uu____24948 = (

let uu____24959 = (

let uu____24964 = (

let uu____24967 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in (uu____24967)::[])
in (uu____24964)::[])
in (

let uu____24972 = (

let uu____24973 = (

let uu____24978 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (

let uu____24979 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in ((uu____24978), (uu____24979))))
in (FStar_SMTEncoding_Util.mkImp uu____24973))
in ((uu____24959), ((x)::[]), (uu____24972))))
in (FStar_SMTEncoding_Util.mkForall uu____24948))
in (

let uu____24998 = (varops.mk_unique "lextop")
in ((uu____24947), (FStar_Pervasives_Native.Some ("lextop is top")), (uu____24998))))
in (FStar_SMTEncoding_Util.mkAssume uu____24940))))
end
| uu____25001 -> begin
(

let prec = (

let uu____25005 = (FStar_All.pipe_right vars (FStar_List.mapi (fun i v1 -> (match ((i < n_tps)) with
| true -> begin
[]
end
| uu____25032 -> begin
(

let uu____25033 = (

let uu____25034 = (FStar_SMTEncoding_Util.mkFreeV v1)
in (FStar_SMTEncoding_Util.mk_Precedes uu____25034 dapp1))
in (uu____25033)::[])
end))))
in (FStar_All.pipe_right uu____25005 FStar_List.flatten))
in (

let uu____25041 = (

let uu____25048 = (

let uu____25049 = (

let uu____25060 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____25071 = (

let uu____25072 = (

let uu____25077 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (uu____25077)))
in (FStar_SMTEncoding_Util.mkImp uu____25072))
in ((((ty_pred)::[])::[]), (uu____25060), (uu____25071))))
in (FStar_SMTEncoding_Util.mkForall uu____25049))
in ((uu____25048), (FStar_Pervasives_Native.Some ("subterm ordering")), ((Prims.strcat "subterm_ordering_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____25041)))
end)
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end)))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let uu____25098 = (encode_args args env')
in (match (uu____25098) with
| (encoded_args, arg_decls) -> begin
(

let guards_for_parameter = (fun orig_arg arg xv -> (

let fv1 = (match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv1) -> begin
fv1
end
| uu____25141 -> begin
(

let uu____25142 = (

let uu____25143 = (

let uu____25148 = (

let uu____25149 = (FStar_Syntax_Print.term_to_string orig_arg)
in (FStar_Util.format1 "Inductive type parameter %s must be a variable ; You may want to change it to an index." uu____25149))
in ((uu____25148), (orig_arg.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____25143))
in (FStar_Exn.raise uu____25142))
end)
in (

let guards1 = (FStar_All.pipe_right guards (FStar_List.collect (fun g -> (

let uu____25165 = (

let uu____25166 = (FStar_SMTEncoding_Term.free_variables g)
in (FStar_List.contains fv1 uu____25166))
in (match (uu____25165) with
| true -> begin
(

let uu____25179 = (FStar_SMTEncoding_Term.subst g fv1 xv)
in (uu____25179)::[])
end
| uu____25180 -> begin
[]
end)))))
in (FStar_SMTEncoding_Util.mk_and_l guards1))))
in (

let uu____25181 = (

let uu____25194 = (FStar_List.zip args encoded_args)
in (FStar_List.fold_left (fun uu____25244 uu____25245 -> (match (((uu____25244), (uu____25245))) with
| ((env2, arg_vars, eqns_or_guards, i), (orig_arg, arg)) -> begin
(

let uu____25340 = (

let uu____25347 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (gen_term_var env2 uu____25347))
in (match (uu____25340) with
| (uu____25360, xv, env3) -> begin
(

let eqns = (match ((i < n_tps)) with
| true -> begin
(

let uu____25368 = (guards_for_parameter (FStar_Pervasives_Native.fst orig_arg) arg xv)
in (uu____25368)::eqns_or_guards)
end
| uu____25369 -> begin
(

let uu____25370 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (uu____25370)::eqns_or_guards)
end)
in ((env3), ((xv)::arg_vars), (eqns), ((i + (Prims.parse_int "1")))))
end))
end)) ((env'), ([]), ([]), ((Prims.parse_int "0"))) uu____25194))
in (match (uu____25181) with
| (uu____25385, arg_vars, elim_eqns_or_guards, uu____25388) -> begin
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

let uu____25418 = (

let uu____25425 = (

let uu____25426 = (

let uu____25437 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____25448 = (

let uu____25449 = (

let uu____25454 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append elim_eqns_or_guards guards))
in ((ty_pred), (uu____25454)))
in (FStar_SMTEncoding_Util.mkImp uu____25449))
in ((((ty_pred)::[])::[]), (uu____25437), (uu____25448))))
in (FStar_SMTEncoding_Util.mkForall uu____25426))
in ((uu____25425), (FStar_Pervasives_Native.Some ("data constructor typing elim")), ((Prims.strcat "data_elim_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____25418))
in (

let subterm_ordering = (match ((FStar_Ident.lid_equals d FStar_Parser_Const.lextop_lid)) with
| true -> begin
(

let x = (

let uu____25477 = (varops.fresh "x")
in ((uu____25477), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (

let uu____25479 = (

let uu____25486 = (

let uu____25487 = (

let uu____25498 = (

let uu____25503 = (

let uu____25506 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in (uu____25506)::[])
in (uu____25503)::[])
in (

let uu____25511 = (

let uu____25512 = (

let uu____25517 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (

let uu____25518 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in ((uu____25517), (uu____25518))))
in (FStar_SMTEncoding_Util.mkImp uu____25512))
in ((uu____25498), ((x)::[]), (uu____25511))))
in (FStar_SMTEncoding_Util.mkForall uu____25487))
in (

let uu____25537 = (varops.mk_unique "lextop")
in ((uu____25486), (FStar_Pervasives_Native.Some ("lextop is top")), (uu____25537))))
in (FStar_SMTEncoding_Util.mkAssume uu____25479))))
end
| uu____25540 -> begin
(

let prec = (

let uu____25544 = (FStar_All.pipe_right vars (FStar_List.mapi (fun i v1 -> (match ((i < n_tps)) with
| true -> begin
[]
end
| uu____25571 -> begin
(

let uu____25572 = (

let uu____25573 = (FStar_SMTEncoding_Util.mkFreeV v1)
in (FStar_SMTEncoding_Util.mk_Precedes uu____25573 dapp1))
in (uu____25572)::[])
end))))
in (FStar_All.pipe_right uu____25544 FStar_List.flatten))
in (

let uu____25580 = (

let uu____25587 = (

let uu____25588 = (

let uu____25599 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____25610 = (

let uu____25611 = (

let uu____25616 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (uu____25616)))
in (FStar_SMTEncoding_Util.mkImp uu____25611))
in ((((ty_pred)::[])::[]), (uu____25599), (uu____25610))))
in (FStar_SMTEncoding_Util.mkForall uu____25588))
in ((uu____25587), (FStar_Pervasives_Native.Some ("subterm ordering")), ((Prims.strcat "subterm_ordering_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____25580)))
end)
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end)))
end)))
end
| uu____25635 -> begin
((

let uu____25637 = (

let uu____25638 = (FStar_Syntax_Print.lid_to_string d)
in (

let uu____25639 = (FStar_Syntax_Print.term_to_string head1)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" uu____25638 uu____25639)))
in (FStar_Errors.warn se.FStar_Syntax_Syntax.sigrng uu____25637));
(([]), ([]));
)
end))
end)))
in (

let uu____25644 = (encode_elim ())
in (match (uu____25644) with
| (decls2, elim) -> begin
(

let g = (

let uu____25664 = (

let uu____25667 = (

let uu____25670 = (

let uu____25673 = (

let uu____25676 = (

let uu____25677 = (

let uu____25688 = (

let uu____25691 = (

let uu____25692 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" uu____25692))
in FStar_Pervasives_Native.Some (uu____25691))
in ((ddtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (uu____25688)))
in FStar_SMTEncoding_Term.DeclFun (uu____25677))
in (uu____25676)::[])
in (

let uu____25697 = (

let uu____25700 = (

let uu____25703 = (

let uu____25706 = (

let uu____25709 = (

let uu____25712 = (

let uu____25715 = (

let uu____25716 = (

let uu____25723 = (

let uu____25724 = (

let uu____25735 = (FStar_SMTEncoding_Util.mkEq ((app), (dapp)))
in ((((app)::[])::[]), (vars), (uu____25735)))
in (FStar_SMTEncoding_Util.mkForall uu____25724))
in ((uu____25723), (FStar_Pervasives_Native.Some ("equality for proxy")), ((Prims.strcat "equality_tok_" ddtok))))
in (FStar_SMTEncoding_Util.mkAssume uu____25716))
in (

let uu____25748 = (

let uu____25751 = (

let uu____25752 = (

let uu____25759 = (

let uu____25760 = (

let uu____25771 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) vars')
in (

let uu____25782 = (FStar_SMTEncoding_Util.mkImp ((guard'), (ty_pred')))
in ((((ty_pred')::[])::[]), (uu____25771), (uu____25782))))
in (FStar_SMTEncoding_Util.mkForall uu____25760))
in ((uu____25759), (FStar_Pervasives_Native.Some ("data constructor typing intro")), ((Prims.strcat "data_typing_intro_" ddtok))))
in (FStar_SMTEncoding_Util.mkAssume uu____25752))
in (uu____25751)::[])
in (uu____25715)::uu____25748))
in ((FStar_SMTEncoding_Util.mkAssume ((tok_typing1), (FStar_Pervasives_Native.Some ("typing for data constructor proxy")), ((Prims.strcat "typing_tok_" ddtok)))))::uu____25712)
in (FStar_List.append uu____25709 elim))
in (FStar_List.append decls_pred uu____25706))
in (FStar_List.append decls_formals uu____25703))
in (FStar_List.append proxy_fresh uu____25700))
in (FStar_List.append uu____25673 uu____25697)))
in (FStar_List.append decls3 uu____25670))
in (FStar_List.append decls2 uu____25667))
in (FStar_List.append binder_decls uu____25664))
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
and encode_sigelts : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun uu____25828 se -> (match (uu____25828) with
| (g, env1) -> begin
(

let uu____25848 = (encode_sigelt env1 se)
in (match (uu____25848) with
| (g', env2) -> begin
(((FStar_List.append g g')), (env2))
end))
end)) (([]), (env)))))


let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env bindings -> (

let encode_binding = (fun b uu____25907 -> (match (uu____25907) with
| (i, decls, env1) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (uu____25939) -> begin
(((i + (Prims.parse_int "1"))), ([]), (env1))
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env1.tcenv x.FStar_Syntax_Syntax.sort)
in ((

let uu____25945 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____25945) with
| true -> begin
(

let uu____25946 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____25947 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____25948 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" uu____25946 uu____25947 uu____25948))))
end
| uu____25949 -> begin
()
end));
(

let uu____25950 = (encode_term t1 env1)
in (match (uu____25950) with
| (t, decls') -> begin
(

let t_hash = (FStar_SMTEncoding_Term.hash_of_term t)
in (

let uu____25966 = (

let uu____25973 = (

let uu____25974 = (

let uu____25975 = (FStar_Util.digest_of_string t_hash)
in (Prims.strcat uu____25975 (Prims.strcat "_" (Prims.string_of_int i))))
in (Prims.strcat "x_" uu____25974))
in (new_term_constant_from_string env1 x uu____25973))
in (match (uu____25966) with
| (xxsym, xx, env') -> begin
(

let t2 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel FStar_Pervasives_Native.None xx t)
in (

let caption = (

let uu____25991 = (FStar_Options.log_queries ())
in (match (uu____25991) with
| true -> begin
(

let uu____25994 = (

let uu____25995 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____25996 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____25997 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" uu____25995 uu____25996 uu____25997))))
in FStar_Pervasives_Native.Some (uu____25994))
end
| uu____25998 -> begin
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
| FStar_TypeChecker_Env.Binding_lid (x, (uu____26013, t)) -> begin
(

let t_norm = (whnf env1 t)
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____26027 = (encode_free_var false env1 fv t t_norm [])
in (match (uu____26027) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))))
end
| FStar_TypeChecker_Env.Binding_sig_inst (uu____26050, se, uu____26052) -> begin
(

let uu____26057 = (encode_sigelt env1 se)
in (match (uu____26057) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))
end
| FStar_TypeChecker_Env.Binding_sig (uu____26074, se) -> begin
(

let uu____26080 = (encode_sigelt env1 se)
in (match (uu____26080) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))
end)
end))
in (

let uu____26097 = (FStar_List.fold_right encode_binding bindings (((Prims.parse_int "0")), ([]), (env)))
in (match (uu____26097) with
| (uu____26120, decls, env1) -> begin
((decls), (env1))
end))))


let encode_labels : 'Auu____26135 'Auu____26136 . ((Prims.string * FStar_SMTEncoding_Term.sort) * 'Auu____26136 * 'Auu____26135) Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl Prims.list) = (fun labs -> (

let prefix1 = (FStar_All.pipe_right labs (FStar_List.map (fun uu____26204 -> (match (uu____26204) with
| (l, uu____26216, uu____26217) -> begin
FStar_SMTEncoding_Term.DeclFun ((((FStar_Pervasives_Native.fst l)), ([]), (FStar_SMTEncoding_Term.Bool_sort), (FStar_Pervasives_Native.None)))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun uu____26263 -> (match (uu____26263) with
| (l, uu____26277, uu____26278) -> begin
(

let uu____26287 = (FStar_All.pipe_left (fun _0_46 -> FStar_SMTEncoding_Term.Echo (_0_46)) (FStar_Pervasives_Native.fst l))
in (

let uu____26288 = (

let uu____26291 = (

let uu____26292 = (FStar_SMTEncoding_Util.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (uu____26292))
in (uu____26291)::[])
in (uu____26287)::uu____26288))
end))))
in ((prefix1), (suffix)))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (

let uu____26314 = (

let uu____26317 = (

let uu____26318 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (

let uu____26321 = (

let uu____26322 = (FStar_TypeChecker_Env.current_module tcenv)
in (FStar_All.pipe_right uu____26322 FStar_Ident.string_of_lid))
in {bindings = []; depth = (Prims.parse_int "0"); tcenv = tcenv; warn = true; cache = uu____26318; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true; current_module_name = uu____26321}))
in (uu____26317)::[])
in (FStar_ST.op_Colon_Equals last_env uu____26314)))


let get_env : FStar_Ident.lident  ->  FStar_TypeChecker_Env.env  ->  env_t = (fun cmn tcenv -> (

let uu____26381 = (FStar_ST.op_Bang last_env)
in (match (uu____26381) with
| [] -> begin
(failwith "No env; call init first!")
end
| (e)::uu____26435 -> begin
(

let uu___184_26438 = e
in (

let uu____26439 = (FStar_Ident.string_of_lid cmn)
in {bindings = uu___184_26438.bindings; depth = uu___184_26438.depth; tcenv = tcenv; warn = uu___184_26438.warn; cache = uu___184_26438.cache; nolabels = uu___184_26438.nolabels; use_zfuel_name = uu___184_26438.use_zfuel_name; encode_non_total_function_typ = uu___184_26438.encode_non_total_function_typ; current_module_name = uu____26439}))
end)))


let set_env : env_t  ->  Prims.unit = (fun env -> (

let uu____26444 = (FStar_ST.op_Bang last_env)
in (match (uu____26444) with
| [] -> begin
(failwith "Empty env stack")
end
| (uu____26497)::tl1 -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl1))
end)))


let push_env : Prims.unit  ->  Prims.unit = (fun uu____26554 -> (

let uu____26555 = (FStar_ST.op_Bang last_env)
in (match (uu____26555) with
| [] -> begin
(failwith "Empty env stack")
end
| (hd1)::tl1 -> begin
(

let refs = (FStar_Util.smap_copy hd1.cache)
in (

let top = (

let uu___185_26616 = hd1
in {bindings = uu___185_26616.bindings; depth = uu___185_26616.depth; tcenv = uu___185_26616.tcenv; warn = uu___185_26616.warn; cache = refs; nolabels = uu___185_26616.nolabels; use_zfuel_name = uu___185_26616.use_zfuel_name; encode_non_total_function_typ = uu___185_26616.encode_non_total_function_typ; current_module_name = uu___185_26616.current_module_name})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd1)::tl1))))
end)))


let pop_env : Prims.unit  ->  Prims.unit = (fun uu____26670 -> (

let uu____26671 = (FStar_ST.op_Bang last_env)
in (match (uu____26671) with
| [] -> begin
(failwith "Popping an empty stack")
end
| (uu____26724)::tl1 -> begin
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
| ((uu____26822)::uu____26823, FStar_SMTEncoding_Term.Assume (a)) -> begin
FStar_SMTEncoding_Term.Assume ((

let uu___186_26831 = a
in {FStar_SMTEncoding_Term.assumption_term = uu___186_26831.FStar_SMTEncoding_Term.assumption_term; FStar_SMTEncoding_Term.assumption_caption = uu___186_26831.FStar_SMTEncoding_Term.assumption_caption; FStar_SMTEncoding_Term.assumption_name = uu___186_26831.FStar_SMTEncoding_Term.assumption_name; FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids}))
end
| uu____26832 -> begin
d
end))


let fact_dbs_for_lid : env_t  ->  FStar_Ident.lid  ->  FStar_SMTEncoding_Term.fact_db_id Prims.list = (fun env lid -> (

let uu____26849 = (

let uu____26852 = (

let uu____26853 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in FStar_SMTEncoding_Term.Namespace (uu____26853))
in (

let uu____26854 = (open_fact_db_tags env)
in (uu____26852)::uu____26854))
in (FStar_SMTEncoding_Term.Name (lid))::uu____26849))


let encode_top_level_facts : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env se -> (

let fact_db_ids = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.collect (fact_dbs_for_lid env)))
in (

let uu____26878 = (encode_sigelt env se)
in (match (uu____26878) with
| (g, env1) -> begin
(

let g1 = (FStar_All.pipe_right g (FStar_List.map (place_decl_in_fact_dbs env1 fact_db_ids)))
in ((g1), (env1)))
end))))


let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (

let caption = (fun decls -> (

let uu____26916 = (FStar_Options.log_queries ())
in (match (uu____26916) with
| true -> begin
(

let uu____26919 = (

let uu____26920 = (

let uu____26921 = (

let uu____26922 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.map FStar_Syntax_Print.lid_to_string))
in (FStar_All.pipe_right uu____26922 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " uu____26921))
in FStar_SMTEncoding_Term.Caption (uu____26920))
in (uu____26919)::decls)
end
| uu____26931 -> begin
decls
end)))
in ((

let uu____26933 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____26933) with
| true -> begin
(

let uu____26934 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____26934))
end
| uu____26935 -> begin
()
end));
(

let env = (

let uu____26937 = (FStar_TypeChecker_Env.current_module tcenv)
in (get_env uu____26937 tcenv))
in (

let uu____26938 = (encode_top_level_facts env se)
in (match (uu____26938) with
| (decls, env1) -> begin
((set_env env1);
(

let uu____26952 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 uu____26952));
)
end)));
)))


let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____26964 -> begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in ((

let uu____26966 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____26966) with
| true -> begin
(

let uu____26967 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) Prims.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name uu____26967))
end
| uu____26968 -> begin
()
end));
(

let env = (get_env modul.FStar_Syntax_Syntax.name tcenv)
in (

let encode_signature = (fun env1 ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun uu____27002 se -> (match (uu____27002) with
| (g, env2) -> begin
(

let uu____27022 = (encode_top_level_facts env2 se)
in (match (uu____27022) with
| (g', env3) -> begin
(((FStar_List.append g g')), (env3))
end))
end)) (([]), (env1)))))
in (

let uu____27045 = (encode_signature (

let uu___187_27054 = env
in {bindings = uu___187_27054.bindings; depth = uu___187_27054.depth; tcenv = uu___187_27054.tcenv; warn = false; cache = uu___187_27054.cache; nolabels = uu___187_27054.nolabels; use_zfuel_name = uu___187_27054.use_zfuel_name; encode_non_total_function_typ = uu___187_27054.encode_non_total_function_typ; current_module_name = uu___187_27054.current_module_name}) modul.FStar_Syntax_Syntax.exports)
in (match (uu____27045) with
| (decls, env1) -> begin
(

let caption = (fun decls1 -> (

let uu____27071 = (FStar_Options.log_queries ())
in (match (uu____27071) with
| true -> begin
(

let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::decls1) ((FStar_SMTEncoding_Term.Caption ((Prims.strcat "End " msg)))::[])))
end
| uu____27075 -> begin
decls1
end)))
in ((set_env (

let uu___188_27079 = env1
in {bindings = uu___188_27079.bindings; depth = uu___188_27079.depth; tcenv = uu___188_27079.tcenv; warn = true; cache = uu___188_27079.cache; nolabels = uu___188_27079.nolabels; use_zfuel_name = uu___188_27079.use_zfuel_name; encode_non_total_function_typ = uu___188_27079.encode_non_total_function_typ; current_module_name = uu___188_27079.current_module_name}));
(

let uu____27081 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____27081) with
| true -> begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end
| uu____27082 -> begin
()
end));
(

let decls1 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls1));
))
end))));
)))


let encode_query : (Prims.unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_ErrorReporting.label Prims.list * FStar_SMTEncoding_Term.decl * FStar_SMTEncoding_Term.decl Prims.list) = (fun use_env_msg tcenv q -> ((

let uu____27136 = (

let uu____27137 = (FStar_TypeChecker_Env.current_module tcenv)
in uu____27137.FStar_Ident.str)
in (FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name uu____27136));
(

let env = (

let uu____27139 = (FStar_TypeChecker_Env.current_module tcenv)
in (get_env uu____27139 tcenv))
in (

let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (

let uu____27151 = (

let rec aux = (fun bindings1 -> (match (bindings1) with
| (FStar_TypeChecker_Env.Binding_var (x))::rest -> begin
(

let uu____27186 = (aux rest)
in (match (uu____27186) with
| (out, rest1) -> begin
(

let t = (

let uu____27216 = (FStar_Syntax_Util.destruct_typ_as_formula x.FStar_Syntax_Syntax.sort)
in (match (uu____27216) with
| FStar_Pervasives_Native.Some (uu____27221) -> begin
(

let uu____27222 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.t_unit)
in (FStar_Syntax_Util.refine uu____27222 x.FStar_Syntax_Syntax.sort))
end
| uu____27223 -> begin
x.FStar_Syntax_Syntax.sort
end))
in (

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
in (

let uu____27227 = (

let uu____27230 = (FStar_Syntax_Syntax.mk_binder (

let uu___189_27233 = x
in {FStar_Syntax_Syntax.ppname = uu___189_27233.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___189_27233.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in (uu____27230)::out)
in ((uu____27227), (rest1)))))
end))
end
| uu____27238 -> begin
(([]), (bindings1))
end))
in (

let uu____27245 = (aux bindings)
in (match (uu____27245) with
| (closing, bindings1) -> begin
(

let uu____27270 = (FStar_Syntax_Util.close_forall_no_univs (FStar_List.rev closing) q)
in ((uu____27270), (bindings1)))
end)))
in (match (uu____27151) with
| (q1, bindings1) -> begin
(

let uu____27293 = (

let uu____27298 = (FStar_List.filter (fun uu___154_27303 -> (match (uu___154_27303) with
| FStar_TypeChecker_Env.Binding_sig (uu____27304) -> begin
false
end
| uu____27311 -> begin
true
end)) bindings1)
in (encode_env_bindings env uu____27298))
in (match (uu____27293) with
| (env_decls, env1) -> begin
((

let uu____27329 = (((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTQuery"))))
in (match (uu____27329) with
| true -> begin
(

let uu____27330 = (FStar_Syntax_Print.term_to_string q1)
in (FStar_Util.print1 "Encoding query formula: %s\n" uu____27330))
end
| uu____27331 -> begin
()
end));
(

let uu____27332 = (encode_formula q1 env1)
in (match (uu____27332) with
| (phi, qdecls) -> begin
(

let uu____27353 = (

let uu____27358 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg uu____27358 phi))
in (match (uu____27353) with
| (labels, phi1) -> begin
(

let uu____27375 = (encode_labels labels)
in (match (uu____27375) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append env_decls (FStar_List.append label_prefix qdecls))
in (

let qry = (

let uu____27412 = (

let uu____27419 = (FStar_SMTEncoding_Util.mkNot phi1)
in (

let uu____27420 = (varops.mk_unique "@query")
in ((uu____27419), (FStar_Pervasives_Native.Some ("query")), (uu____27420))))
in (FStar_SMTEncoding_Util.mkAssume uu____27412))
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




