
open Prims
open FStar_Pervasives

let add_fuel = (fun x tl1 -> (

let uu____19 = (FStar_Options.unthrottle_inductives ())
in (match (uu____19) with
| true -> begin
tl1
end
| uu____21 -> begin
(x)::tl1
end)))


let withenv = (fun c uu____47 -> (match (uu____47) with
| (a, b) -> begin
((a), (b), (c))
end))


let vargs = (fun args -> (FStar_List.filter (fun uu___102_89 -> (match (uu___102_89) with
| (FStar_Util.Inl (uu____94), uu____95) -> begin
false
end
| uu____98 -> begin
true
end)) args))


let subst_lcomp_opt = (fun s l -> (match (l) with
| FStar_Pervasives_Native.Some (FStar_Util.Inl (l1)) -> begin
(

let uu____132 = (

let uu____135 = (

let uu____136 = (

let uu____139 = (l1.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp s uu____139))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____136))
in FStar_Util.Inl (uu____135))
in FStar_Pervasives_Native.Some (uu____132))
end
| uu____144 -> begin
l
end))


let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s '\'' '_'))


let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun lid a -> (

let a1 = (

let uu___126_161 = a
in (

let uu____162 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = uu____162; FStar_Syntax_Syntax.index = uu___126_161.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___126_161.FStar_Syntax_Syntax.sort}))
in (

let uu____163 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str a1.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (FStar_All.pipe_left escape uu____163))))


let primitive_projector_by_pos : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (

let fail = (fun uu____179 -> (

let uu____180 = (FStar_Util.format2 "Projector %s on data constructor %s not found" (Prims.string_of_int i) lid.FStar_Ident.str)
in (failwith uu____180)))
in (

let uu____181 = (FStar_TypeChecker_Env.lookup_datacon env lid)
in (match (uu____181) with
| (uu____184, t) -> begin
(

let uu____186 = (

let uu____187 = (FStar_Syntax_Subst.compress t)
in uu____187.FStar_Syntax_Syntax.n)
in (match (uu____186) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____202 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____202) with
| (binders, uu____206) -> begin
(match (((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders)))) with
| true -> begin
(fail ())
end
| uu____213 -> begin
(

let b = (FStar_List.nth binders i)
in (mk_term_projector_name lid (FStar_Pervasives_Native.fst b)))
end)
end))
end
| uu____219 -> begin
(fail ())
end))
end))))


let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (

let uu____228 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str (Prims.string_of_int i))
in (FStar_All.pipe_left escape uu____228)))


let mk_term_projector : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun lid a -> (

let uu____237 = (

let uu____240 = (mk_term_projector_name lid a)
in ((uu____240), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Util.mkFreeV uu____237)))


let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_SMTEncoding_Term.term = (fun lid i -> (

let uu____249 = (

let uu____252 = (mk_term_projector_name_by_pos lid i)
in ((uu____252), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Util.mkFreeV uu____249)))


let mk_data_tester = (fun env l x -> (FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x))

type varops_t =
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; mark : Prims.unit  ->  Prims.unit; reset_mark : Prims.unit  ->  Prims.unit; commit_mark : Prims.unit  ->  Prims.unit; new_var : FStar_Ident.ident  ->  Prims.int  ->  Prims.string; new_fvar : FStar_Ident.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_SMTEncoding_Term.term; next_id : Prims.unit  ->  Prims.int; mk_unique : Prims.string  ->  Prims.string}


let __proj__Mkvarops_t__item__push : varops_t  ->  Prims.unit  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {push = __fname__push; pop = __fname__pop; mark = __fname__mark; reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark; new_var = __fname__new_var; new_fvar = __fname__new_fvar; fresh = __fname__fresh; string_const = __fname__string_const; next_id = __fname__next_id; mk_unique = __fname__mk_unique} -> begin
__fname__push
end))


let __proj__Mkvarops_t__item__pop : varops_t  ->  Prims.unit  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {push = __fname__push; pop = __fname__pop; mark = __fname__mark; reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark; new_var = __fname__new_var; new_fvar = __fname__new_fvar; fresh = __fname__fresh; string_const = __fname__string_const; next_id = __fname__next_id; mk_unique = __fname__mk_unique} -> begin
__fname__pop
end))


let __proj__Mkvarops_t__item__mark : varops_t  ->  Prims.unit  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {push = __fname__push; pop = __fname__pop; mark = __fname__mark; reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark; new_var = __fname__new_var; new_fvar = __fname__new_fvar; fresh = __fname__fresh; string_const = __fname__string_const; next_id = __fname__next_id; mk_unique = __fname__mk_unique} -> begin
__fname__mark
end))


let __proj__Mkvarops_t__item__reset_mark : varops_t  ->  Prims.unit  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {push = __fname__push; pop = __fname__pop; mark = __fname__mark; reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark; new_var = __fname__new_var; new_fvar = __fname__new_fvar; fresh = __fname__fresh; string_const = __fname__string_const; next_id = __fname__next_id; mk_unique = __fname__mk_unique} -> begin
__fname__reset_mark
end))


let __proj__Mkvarops_t__item__commit_mark : varops_t  ->  Prims.unit  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {push = __fname__push; pop = __fname__pop; mark = __fname__mark; reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark; new_var = __fname__new_var; new_fvar = __fname__new_fvar; fresh = __fname__fresh; string_const = __fname__string_const; next_id = __fname__next_id; mk_unique = __fname__mk_unique} -> begin
__fname__commit_mark
end))


let __proj__Mkvarops_t__item__new_var : varops_t  ->  FStar_Ident.ident  ->  Prims.int  ->  Prims.string = (fun projectee -> (match (projectee) with
| {push = __fname__push; pop = __fname__pop; mark = __fname__mark; reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark; new_var = __fname__new_var; new_fvar = __fname__new_fvar; fresh = __fname__fresh; string_const = __fname__string_const; next_id = __fname__next_id; mk_unique = __fname__mk_unique} -> begin
__fname__new_var
end))


let __proj__Mkvarops_t__item__new_fvar : varops_t  ->  FStar_Ident.lident  ->  Prims.string = (fun projectee -> (match (projectee) with
| {push = __fname__push; pop = __fname__pop; mark = __fname__mark; reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark; new_var = __fname__new_var; new_fvar = __fname__new_fvar; fresh = __fname__fresh; string_const = __fname__string_const; next_id = __fname__next_id; mk_unique = __fname__mk_unique} -> begin
__fname__new_fvar
end))


let __proj__Mkvarops_t__item__fresh : varops_t  ->  Prims.string  ->  Prims.string = (fun projectee -> (match (projectee) with
| {push = __fname__push; pop = __fname__pop; mark = __fname__mark; reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark; new_var = __fname__new_var; new_fvar = __fname__new_fvar; fresh = __fname__fresh; string_const = __fname__string_const; next_id = __fname__next_id; mk_unique = __fname__mk_unique} -> begin
__fname__fresh
end))


let __proj__Mkvarops_t__item__string_const : varops_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term = (fun projectee -> (match (projectee) with
| {push = __fname__push; pop = __fname__pop; mark = __fname__mark; reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark; new_var = __fname__new_var; new_fvar = __fname__new_fvar; fresh = __fname__fresh; string_const = __fname__string_const; next_id = __fname__next_id; mk_unique = __fname__mk_unique} -> begin
__fname__string_const
end))


let __proj__Mkvarops_t__item__next_id : varops_t  ->  Prims.unit  ->  Prims.int = (fun projectee -> (match (projectee) with
| {push = __fname__push; pop = __fname__pop; mark = __fname__mark; reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark; new_var = __fname__new_var; new_fvar = __fname__new_fvar; fresh = __fname__fresh; string_const = __fname__string_const; next_id = __fname__next_id; mk_unique = __fname__mk_unique} -> begin
__fname__next_id
end))


let __proj__Mkvarops_t__item__mk_unique : varops_t  ->  Prims.string  ->  Prims.string = (fun projectee -> (match (projectee) with
| {push = __fname__push; pop = __fname__pop; mark = __fname__mark; reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark; new_var = __fname__new_var; new_fvar = __fname__new_fvar; fresh = __fname__fresh; string_const = __fname__string_const; next_id = __fname__next_id; mk_unique = __fname__mk_unique} -> begin
__fname__mk_unique
end))


let varops : varops_t = (

let initial_ctr = (Prims.parse_int "100")
in (

let ctr = (FStar_Util.mk_ref initial_ctr)
in (

let new_scope = (fun uu____866 -> (

let uu____867 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (

let uu____869 = (FStar_Util.smap_create (Prims.parse_int "100"))
in ((uu____867), (uu____869)))))
in (

let scopes = (

let uu____880 = (

let uu____886 = (new_scope ())
in (uu____886)::[])
in (FStar_Util.mk_ref uu____880))
in (

let mk_unique = (fun y -> (

let y1 = (escape y)
in (

let y2 = (

let uu____911 = (

let uu____913 = (FStar_ST.read scopes)
in (FStar_Util.find_map uu____913 (fun uu____933 -> (match (uu____933) with
| (names1, uu____940) -> begin
(FStar_Util.smap_try_find names1 y1)
end))))
in (match (uu____911) with
| FStar_Pervasives_Native.None -> begin
y1
end
| FStar_Pervasives_Native.Some (uu____945) -> begin
((FStar_Util.incr ctr);
(

let uu____950 = (

let uu____951 = (

let uu____952 = (FStar_ST.read ctr)
in (Prims.string_of_int uu____952))
in (Prims.strcat "__" uu____951))
in (Prims.strcat y1 uu____950));
)
end))
in (

let top_scope = (

let uu____957 = (

let uu____962 = (FStar_ST.read scopes)
in (FStar_List.hd uu____962))
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____957))
in ((FStar_Util.smap_add top_scope y2 true);
y2;
)))))
in (

let new_var = (fun pp rn -> (FStar_All.pipe_left mk_unique (Prims.strcat pp.FStar_Ident.idText (Prims.strcat "__" (Prims.string_of_int rn)))))
in (

let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (

let next_id1 = (fun uu____1001 -> ((FStar_Util.incr ctr);
(FStar_ST.read ctr);
))
in (

let fresh1 = (fun pfx -> (

let uu____1012 = (

let uu____1013 = (next_id1 ())
in (FStar_All.pipe_left Prims.string_of_int uu____1013))
in (FStar_Util.format2 "%s_%s" pfx uu____1012)))
in (

let string_const = (fun s -> (

let uu____1018 = (

let uu____1020 = (FStar_ST.read scopes)
in (FStar_Util.find_map uu____1020 (fun uu____1040 -> (match (uu____1040) with
| (uu____1046, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))
in (match (uu____1018) with
| FStar_Pervasives_Native.Some (f) -> begin
f
end
| FStar_Pervasives_Native.None -> begin
(

let id = (next_id1 ())
in (

let f = (

let uu____1055 = (FStar_SMTEncoding_Util.mk_String_const id)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1055))
in (

let top_scope = (

let uu____1058 = (

let uu____1063 = (FStar_ST.read scopes)
in (FStar_List.hd uu____1063))
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1058))
in ((FStar_Util.smap_add top_scope s f);
f;
))))
end)))
in (

let push1 = (fun uu____1091 -> (

let uu____1092 = (

let uu____1098 = (new_scope ())
in (

let uu____1103 = (FStar_ST.read scopes)
in (uu____1098)::uu____1103))
in (FStar_ST.write scopes uu____1092)))
in (

let pop1 = (fun uu____1130 -> (

let uu____1131 = (

let uu____1137 = (FStar_ST.read scopes)
in (FStar_List.tl uu____1137))
in (FStar_ST.write scopes uu____1131)))
in (

let mark1 = (fun uu____1164 -> (push1 ()))
in (

let reset_mark1 = (fun uu____1168 -> (pop1 ()))
in (

let commit_mark1 = (fun uu____1172 -> (

let uu____1173 = (FStar_ST.read scopes)
in (match (uu____1173) with
| ((hd1, hd2))::((next1, next2))::tl1 -> begin
((FStar_Util.smap_fold hd1 (fun key value v1 -> (FStar_Util.smap_add next1 key value)) ());
(FStar_Util.smap_fold hd2 (fun key value v1 -> (FStar_Util.smap_add next2 key value)) ());
(FStar_ST.write scopes ((((next1), (next2)))::tl1));
)
end
| uu____1239 -> begin
(failwith "Impossible")
end)))
in {push = push1; pop = pop1; mark = mark1; reset_mark = reset_mark1; commit_mark = commit_mark1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; string_const = string_const; next_id = next_id1; mk_unique = mk_unique})))))))))))))))


let unmangle : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv = (fun x -> (

let uu___127_1249 = x
in (

let uu____1250 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = uu____1250; FStar_Syntax_Syntax.index = uu___127_1249.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___127_1249.FStar_Syntax_Syntax.sort})))

type binding =
| Binding_var of (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term)
| Binding_fvar of (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)


let uu___is_Binding_var : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Binding_var (_0) -> begin
true
end
| uu____1274 -> begin
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
| uu____1300 -> begin
false
end))


let __proj__Binding_fvar__item___0 : binding  ->  (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| Binding_fvar (_0) -> begin
_0
end))


let binder_of_eithervar = (fun v1 -> ((v1), (FStar_Pervasives_Native.None)))

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


let mk_cache_entry = (fun env tsym cvar_sorts t_decls -> (

let names1 = (FStar_All.pipe_right t_decls (FStar_List.collect (fun uu___103_1626 -> (match (uu___103_1626) with
| FStar_SMTEncoding_Term.Assume (a) -> begin
(a.FStar_SMTEncoding_Term.assumption_name)::[]
end
| uu____1629 -> begin
[]
end))))
in {cache_symbol_name = tsym; cache_symbol_arg_sorts = cvar_sorts; cache_symbol_decls = t_decls; cache_symbol_assumption_names = names1}))


let use_cache_entry : cache_entry  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun ce -> (FStar_SMTEncoding_Term.RetainAssumptions (ce.cache_symbol_assumption_names))::[])


let print_env : env_t  ->  Prims.string = (fun e -> (

let uu____1639 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun uu___104_1646 -> (match (uu___104_1646) with
| Binding_var (x, uu____1648) -> begin
(FStar_Syntax_Print.bv_to_string x)
end
| Binding_fvar (l, uu____1650, uu____1651, uu____1652) -> begin
(FStar_Syntax_Print.lid_to_string l)
end))))
in (FStar_All.pipe_right uu____1639 (FStar_String.concat ", "))))


let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))


let caption_t : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.string FStar_Pervasives_Native.option = (fun env t -> (

let uu____1690 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____1690) with
| true -> begin
(

let uu____1692 = (FStar_Syntax_Print.term_to_string t)
in FStar_Pervasives_Native.Some (uu____1692))
end
| uu____1693 -> begin
FStar_Pervasives_Native.None
end)))


let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (

let xsym = (varops.fresh x)
in (

let uu____1705 = (FStar_SMTEncoding_Util.mkFreeV ((xsym), (s)))
in ((xsym), (uu____1705)))))


let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (Prims.strcat "@x" (Prims.string_of_int env.depth))
in (

let y = (FStar_SMTEncoding_Util.mkFreeV ((ysym), (FStar_SMTEncoding_Term.Term_sort)))
in ((ysym), (y), ((

let uu___128_1720 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = (env.depth + (Prims.parse_int "1")); tcenv = uu___128_1720.tcenv; warn = uu___128_1720.warn; cache = uu___128_1720.cache; nolabels = uu___128_1720.nolabels; use_zfuel_name = uu___128_1720.use_zfuel_name; encode_non_total_function_typ = uu___128_1720.encode_non_total_function_typ; current_module_name = uu___128_1720.current_module_name}))))))


let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let uu___129_1736 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = uu___129_1736.depth; tcenv = uu___129_1736.tcenv; warn = uu___129_1736.warn; cache = uu___129_1736.cache; nolabels = uu___129_1736.nolabels; use_zfuel_name = uu___129_1736.use_zfuel_name; encode_non_total_function_typ = uu___129_1736.encode_non_total_function_typ; current_module_name = uu___129_1736.current_module_name}))))))


let new_term_constant_from_string : env_t  ->  FStar_Syntax_Syntax.bv  ->  Prims.string  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x str -> (

let ysym = (varops.mk_unique str)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let uu___130_1756 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = uu___130_1756.depth; tcenv = uu___130_1756.tcenv; warn = uu___130_1756.warn; cache = uu___130_1756.cache; nolabels = uu___130_1756.nolabels; use_zfuel_name = uu___130_1756.use_zfuel_name; encode_non_total_function_typ = uu___130_1756.encode_non_total_function_typ; current_module_name = uu___130_1756.current_module_name}))))))


let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (

let uu___131_1769 = env
in {bindings = (Binding_var (((x), (t))))::env.bindings; depth = uu___131_1769.depth; tcenv = uu___131_1769.tcenv; warn = uu___131_1769.warn; cache = uu___131_1769.cache; nolabels = uu___131_1769.nolabels; use_zfuel_name = uu___131_1769.use_zfuel_name; encode_non_total_function_typ = uu___131_1769.encode_non_total_function_typ; current_module_name = uu___131_1769.current_module_name}))


let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let aux = (fun a' -> (lookup_binding env (fun uu___105_1790 -> (match (uu___105_1790) with
| Binding_var (b, t) when (FStar_Syntax_Syntax.bv_eq b a') -> begin
FStar_Pervasives_Native.Some (((b), (t)))
end
| uu____1798 -> begin
FStar_Pervasives_Native.None
end))))
in (

let uu____1801 = (aux a)
in (match (uu____1801) with
| FStar_Pervasives_Native.None -> begin
(

let a2 = (unmangle a)
in (

let uu____1808 = (aux a2)
in (match (uu____1808) with
| FStar_Pervasives_Native.None -> begin
(

let uu____1814 = (

let uu____1815 = (FStar_Syntax_Print.bv_to_string a2)
in (

let uu____1816 = (print_env env)
in (FStar_Util.format2 "Bound term variable not found (after unmangling): %s in environment: %s" uu____1815 uu____1816)))
in (failwith uu____1814))
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

let uu____1838 = (

let uu___132_1839 = env
in (

let uu____1840 = (

let uu____1842 = (

let uu____1843 = (

let uu____1850 = (

let uu____1852 = (FStar_SMTEncoding_Util.mkApp ((ftok), ([])))
in (FStar_All.pipe_left (fun _0_39 -> FStar_Pervasives_Native.Some (_0_39)) uu____1852))
in ((x), (fname), (uu____1850), (FStar_Pervasives_Native.None)))
in Binding_fvar (uu____1843))
in (uu____1842)::env.bindings)
in {bindings = uu____1840; depth = uu___132_1839.depth; tcenv = uu___132_1839.tcenv; warn = uu___132_1839.warn; cache = uu___132_1839.cache; nolabels = uu___132_1839.nolabels; use_zfuel_name = uu___132_1839.use_zfuel_name; encode_non_total_function_typ = uu___132_1839.encode_non_total_function_typ; current_module_name = uu___132_1839.current_module_name}))
in ((fname), (ftok), (uu____1838))))))


let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option) FStar_Pervasives_Native.option = (fun env a -> (lookup_binding env (fun uu___106_1881 -> (match (uu___106_1881) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
FStar_Pervasives_Native.Some (((t1), (t2), (t3)))
end
| uu____1903 -> begin
FStar_Pervasives_Native.None
end))))


let contains_name : env_t  ->  Prims.string  ->  Prims.bool = (fun env s -> (

let uu____1917 = (lookup_binding env (fun uu___107_1924 -> (match (uu___107_1924) with
| Binding_fvar (b, t1, t2, t3) when (b.FStar_Ident.str = s) -> begin
FStar_Pervasives_Native.Some (())
end
| uu____1934 -> begin
FStar_Pervasives_Native.None
end)))
in (FStar_All.pipe_right uu____1917 FStar_Option.isSome)))


let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option) = (fun env a -> (

let uu____1949 = (try_lookup_lid env a)
in (match (uu____1949) with
| FStar_Pervasives_Native.None -> begin
(

let uu____1966 = (

let uu____1967 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" uu____1967))
in (failwith uu____1966))
end
| FStar_Pervasives_Native.Some (s) -> begin
s
end)))


let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  env_t = (fun env x fname ftok -> (

let uu___133_2002 = env
in {bindings = (Binding_fvar (((x), (fname), (ftok), (FStar_Pervasives_Native.None))))::env.bindings; depth = uu___133_2002.depth; tcenv = uu___133_2002.tcenv; warn = uu___133_2002.warn; cache = uu___133_2002.cache; nolabels = uu___133_2002.nolabels; use_zfuel_name = uu___133_2002.use_zfuel_name; encode_non_total_function_typ = uu___133_2002.encode_non_total_function_typ; current_module_name = uu___133_2002.current_module_name}))


let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (

let uu____2017 = (lookup_lid env x)
in (match (uu____2017) with
| (t1, t2, uu____2025) -> begin
(

let t3 = (

let uu____2031 = (

let uu____2035 = (

let uu____2037 = (FStar_SMTEncoding_Util.mkApp (("ZFuel"), ([])))
in (uu____2037)::[])
in ((f), (uu____2035)))
in (FStar_SMTEncoding_Util.mkApp uu____2031))
in (

let uu___134_2040 = env
in {bindings = (Binding_fvar (((x), (t1), (t2), (FStar_Pervasives_Native.Some (t3)))))::env.bindings; depth = uu___134_2040.depth; tcenv = uu___134_2040.tcenv; warn = uu___134_2040.warn; cache = uu___134_2040.cache; nolabels = uu___134_2040.nolabels; use_zfuel_name = uu___134_2040.use_zfuel_name; encode_non_total_function_typ = uu___134_2040.encode_non_total_function_typ; current_module_name = uu___134_2040.current_module_name}))
end)))


let try_lookup_free_var : env_t  ->  FStar_Ident.lident  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun env l -> (

let uu____2052 = (try_lookup_lid env l)
in (match (uu____2052) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (name, sym, zf_opt) -> begin
(match (zf_opt) with
| FStar_Pervasives_Native.Some (f) when env.use_zfuel_name -> begin
FStar_Pervasives_Native.Some (f)
end
| uu____2079 -> begin
(match (sym) with
| FStar_Pervasives_Native.Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (uu____2084, (fuel)::[]) -> begin
(

let uu____2087 = (

let uu____2088 = (

let uu____2089 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right uu____2089 FStar_Pervasives_Native.fst))
in (FStar_Util.starts_with uu____2088 "fuel"))
in (match (uu____2087) with
| true -> begin
(

let uu____2091 = (

let uu____2092 = (FStar_SMTEncoding_Util.mkFreeV ((name), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_ApplyTF uu____2092 fuel))
in (FStar_All.pipe_left (fun _0_40 -> FStar_Pervasives_Native.Some (_0_40)) uu____2091))
end
| uu____2094 -> begin
FStar_Pervasives_Native.Some (t)
end))
end
| uu____2095 -> begin
FStar_Pervasives_Native.Some (t)
end)
end
| uu____2096 -> begin
FStar_Pervasives_Native.None
end)
end)
end)))


let lookup_free_var : env_t  ->  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let uu____2108 = (try_lookup_free_var env a.FStar_Syntax_Syntax.v)
in (match (uu____2108) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let uu____2111 = (

let uu____2112 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" uu____2112))
in (failwith uu____2111))
end)))


let lookup_free_var_name : env_t  ->  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t  ->  Prims.string = (fun env a -> (

let uu____2123 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (uu____2123) with
| (x, uu____2130, uu____2131) -> begin
x
end)))


let lookup_free_var_sym : env_t  ->  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t  ->  (FStar_SMTEncoding_Term.op * FStar_SMTEncoding_Term.term Prims.list) = (fun env a -> (

let uu____2149 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (uu____2149) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| FStar_Pervasives_Native.Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.freevars = uu____2170; FStar_SMTEncoding_Term.rng = uu____2171}) when env.use_zfuel_name -> begin
((g), (zf))
end
| uu____2179 -> begin
(match (sym) with
| FStar_Pervasives_Native.None -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end
| FStar_Pervasives_Native.Some (sym1) -> begin
(match (sym1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, (fuel)::[]) -> begin
((g), ((fuel)::[]))
end
| uu____2193 -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end)
end)
end)
end)))


let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun uu___108_2209 -> (match (uu___108_2209) with
| Binding_fvar (uu____2211, nm', tok, uu____2214) when (nm = nm') -> begin
tok
end
| uu____2219 -> begin
FStar_Pervasives_Native.None
end))))


let mkForall_fuel' = (fun n1 uu____2239 -> (match (uu____2239) with
| (pats, vars, body) -> begin
(

let fallback = (fun uu____2255 -> (FStar_SMTEncoding_Util.mkForall ((pats), (vars), (body))))
in (

let uu____2258 = (FStar_Options.unthrottle_inductives ())
in (match (uu____2258) with
| true -> begin
(fallback ())
end
| uu____2259 -> begin
(

let uu____2260 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____2260) with
| (fsym, fterm) -> begin
(

let add_fuel1 = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Util.mkApp (("HasTypeFuel"), ((fterm)::args)))
end
| uu____2281 -> begin
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

let uu____2295 = (add_fuel1 guards)
in (FStar_SMTEncoding_Util.mk_and_l uu____2295))
end
| uu____2297 -> begin
(

let uu____2298 = (add_fuel1 ((guard)::[]))
in (FStar_All.pipe_right uu____2298 FStar_List.hd))
end)
in (FStar_SMTEncoding_Util.mkImp ((guard1), (body'))))
end
| uu____2301 -> begin
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
| FStar_Syntax_Syntax.Tm_arrow (uu____2330) -> begin
true
end
| FStar_Syntax_Syntax.Tm_refine (uu____2338) -> begin
true
end
| FStar_Syntax_Syntax.Tm_bvar (uu____2343) -> begin
true
end
| FStar_Syntax_Syntax.Tm_uvar (uu____2344) -> begin
true
end
| FStar_Syntax_Syntax.Tm_abs (uu____2355) -> begin
true
end
| FStar_Syntax_Syntax.Tm_constant (uu____2365) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____2367 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____2367 FStar_Option.isNone))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____2377; FStar_Syntax_Syntax.pos = uu____2378; FStar_Syntax_Syntax.vars = uu____2379}, uu____2380) -> begin
(

let uu____2395 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____2395 FStar_Option.isNone))
end
| uu____2404 -> begin
false
end)))


let head_redex : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let uu____2413 = (

let uu____2414 = (FStar_Syntax_Util.un_uinst t)
in uu____2414.FStar_Syntax_Syntax.n)
in (match (uu____2413) with
| FStar_Syntax_Syntax.Tm_abs (uu____2417, uu____2418, FStar_Pervasives_Native.Some (rc)) -> begin
(((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_Tot_lid) || (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_GTot_lid)) || (FStar_List.existsb (fun uu___109_2432 -> (match (uu___109_2432) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____2433 -> begin
false
end)) rc.FStar_Syntax_Syntax.residual_flags))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____2435 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____2435 FStar_Option.isSome))
end
| uu____2444 -> begin
false
end)))


let whnf : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____2453 = (head_normal env t)
in (match (uu____2453) with
| true -> begin
t
end
| uu____2454 -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
end)))


let norm : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t))


let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____2467 = (

let uu____2468 = (FStar_Syntax_Syntax.null_binder t)
in (uu____2468)::[])
in (

let uu____2469 = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Util.abs uu____2467 uu____2469 FStar_Pervasives_Native.None))))


let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((FStar_Pervasives_Native.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(

let uu____2496 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out uu____2496))
end
| s -> begin
(

let uu____2500 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Util.mk_ApplyTT out uu____2500))
end)) e)))


let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)))


let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun uu___110_2515 -> (match (uu___110_2515) with
| FStar_SMTEncoding_Term.Var ("ApplyTT") -> begin
true
end
| FStar_SMTEncoding_Term.Var ("ApplyTF") -> begin
true
end
| uu____2516 -> begin
false
end))


let is_an_eta_expansion : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun env vars body -> (

let rec check_partial_applications = (fun t xs -> (match (((t.FStar_SMTEncoding_Term.tm), (xs))) with
| (FStar_SMTEncoding_Term.App (app, (f)::({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.freevars = uu____2547; FStar_SMTEncoding_Term.rng = uu____2548})::[]), (x)::xs1) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(check_partial_applications f xs1)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), uu____2562) -> begin
(

let uu____2567 = (((FStar_List.length args) = (FStar_List.length xs)) && (FStar_List.forall2 (fun a v1 -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v1)
end
| uu____2584 -> begin
false
end)) args (FStar_List.rev xs)))
in (match (uu____2567) with
| true -> begin
(tok_of_name env f)
end
| uu____2586 -> begin
FStar_Pervasives_Native.None
end))
end
| (uu____2587, []) -> begin
(

let fvs = (FStar_SMTEncoding_Term.free_variables t)
in (

let uu____2590 = (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (

let uu____2594 = (FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)
in (not (uu____2594))))))
in (match (uu____2590) with
| true -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____2596 -> begin
FStar_Pervasives_Native.None
end)))
end
| uu____2597 -> begin
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
| uu____2764 -> begin
false
end))


let encode_const : FStar_Const.sconst  ->  FStar_SMTEncoding_Term.term = (fun uu___111_2768 -> (match (uu___111_2768) with
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

let uu____2770 = (

let uu____2774 = (

let uu____2776 = (

let uu____2777 = (FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c))
in (FStar_SMTEncoding_Term.boxInt uu____2777))
in (uu____2776)::[])
in (("FStar.Char.Char"), (uu____2774)))
in (FStar_SMTEncoding_Util.mkApp uu____2770))
end
| FStar_Const.Const_int (i, FStar_Pervasives_Native.None) -> begin
(

let uu____2785 = (FStar_SMTEncoding_Util.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt uu____2785))
end
| FStar_Const.Const_int (i, FStar_Pervasives_Native.Some (uu____2787)) -> begin
(failwith "Machine integers should be desugared")
end
| FStar_Const.Const_string (bytes, uu____2796) -> begin
(

let uu____2799 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const uu____2799))
end
| FStar_Const.Const_range (r) -> begin
FStar_SMTEncoding_Term.mk_Range_const
end
| FStar_Const.Const_effect -> begin
FStar_SMTEncoding_Term.mk_Term_type
end
| c -> begin
(

let uu____2803 = (

let uu____2804 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" uu____2804))
in (failwith uu____2803))
end))


let as_function_typ : env_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (

let rec aux = (fun norm1 t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____2825) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_refine (uu____2833) -> begin
(

let uu____2838 = (FStar_Syntax_Util.unrefine t1)
in (aux true uu____2838))
end
| uu____2839 -> begin
(match (norm1) with
| true -> begin
(

let uu____2840 = (whnf env t1)
in (aux false uu____2840))
end
| uu____2841 -> begin
(

let uu____2842 = (

let uu____2843 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (

let uu____2844 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" uu____2843 uu____2844)))
in (failwith uu____2842))
end)
end)))
in (aux true t0)))


let curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun k -> (

let k1 = (FStar_Syntax_Subst.compress k)
in (match (k1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| uu____2866 -> begin
(

let uu____2867 = (FStar_Syntax_Syntax.mk_Total k1)
in (([]), (uu____2867)))
end)))


let is_arithmetic_primitive = (fun head1 args -> (match (((head1.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____2899)::(uu____2900)::[]) -> begin
(((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Addition) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Subtraction)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Multiply)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Division)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Modulus))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____2903)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus)
end
| uu____2905 -> begin
false
end))


let isInteger : FStar_Syntax_Syntax.term'  ->  Prims.bool = (fun tm -> (match (tm) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (n1, FStar_Pervasives_Native.None)) -> begin
true
end
| uu____2919 -> begin
false
end))


let getInteger : FStar_Syntax_Syntax.term'  ->  Prims.int = (fun tm -> (match (tm) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (n1, FStar_Pervasives_Native.None)) -> begin
(FStar_Util.int_of_string n1)
end
| uu____2930 -> begin
(failwith "Expected an Integer term")
end))


let is_BitVector_primitive = (fun head1 args -> (match (((head1.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((sz_arg, uu____2973))::(uu____2974)::(uu____2975)::[]) -> begin
((((((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_and_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_xor_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_or_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_shift_left_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_shift_right_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_udiv_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_mod_lid)) && (isInteger sz_arg.FStar_Syntax_Syntax.n))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((sz_arg, uu____3011))::(uu____3012)::[]) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid) && (isInteger sz_arg.FStar_Syntax_Syntax.n))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((sz_arg, uu____3040))::[]) -> begin
(((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_zero_vec_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_ones_vec_lid)) && (isInteger sz_arg.FStar_Syntax_Syntax.n))
end
| uu____3058 -> begin
false
end))


let rec encode_binders : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> ((

let uu____3212 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____3212) with
| true -> begin
(

let uu____3213 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" uu____3213))
end
| uu____3214 -> begin
()
end));
(

let uu____3215 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____3264 b -> (match (uu____3264) with
| (vars, guards, env1, decls, names1) -> begin
(

let uu____3307 = (

let x = (unmangle (FStar_Pervasives_Native.fst b))
in (

let uu____3316 = (gen_term_var env1 x)
in (match (uu____3316) with
| (xxsym, xx, env') -> begin
(

let uu____3330 = (

let uu____3333 = (norm env1 x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt uu____3333 env1 xx))
in (match (uu____3330) with
| (guard_x_t, decls') -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (guard_x_t), (env'), (decls'), (x))
end))
end)))
in (match (uu____3307) with
| (v1, g, env2, decls', n1) -> begin
(((v1)::vars), ((g)::guards), (env2), ((FStar_List.append decls decls')), ((n1)::names1))
end))
end)) (([]), ([]), (env), ([]), ([]))))
in (match (uu____3215) with
| (vars, guards, env1, decls, names1) -> begin
(((FStar_List.rev vars)), ((FStar_List.rev guards)), (env1), (decls), ((FStar_List.rev names1)))
end));
))
and encode_term_pred : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let uu____3421 = (encode_term t env)
in (match (uu____3421) with
| (t1, decls) -> begin
(

let uu____3428 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1)
in ((uu____3428), (decls)))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let uu____3436 = (encode_term t env)
in (match (uu____3436) with
| (t1, decls) -> begin
(match (fuel_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____3445 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t1)
in ((uu____3445), (decls)))
end
| FStar_Pervasives_Native.Some (f) -> begin
(

let uu____3447 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1)
in ((uu____3447), (decls)))
end)
end)))
and encode_arith_term : env_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.args  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun env head1 args_e -> (

let uu____3453 = (encode_args args_e env)
in (match (uu____3453) with
| (arg_tms, decls) -> begin
(

let head_fv = (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____3465 -> begin
(failwith "Impossible")
end)
in (

let unary = (fun arg_tms1 -> (

let uu____3472 = (FStar_List.hd arg_tms1)
in (FStar_SMTEncoding_Term.unboxInt uu____3472)))
in (

let binary = (fun arg_tms1 -> (

let uu____3481 = (

let uu____3482 = (FStar_List.hd arg_tms1)
in (FStar_SMTEncoding_Term.unboxInt uu____3482))
in (

let uu____3483 = (

let uu____3484 = (

let uu____3485 = (FStar_List.tl arg_tms1)
in (FStar_List.hd uu____3485))
in (FStar_SMTEncoding_Term.unboxInt uu____3484))
in ((uu____3481), (uu____3483)))))
in (

let mk_default = (fun uu____3490 -> (

let uu____3491 = (lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name)
in (match (uu____3491) with
| (fname, fuel_args) -> begin
(FStar_SMTEncoding_Util.mkApp' ((fname), ((FStar_List.append fuel_args arg_tms))))
end)))
in (

let mk_l = (fun op mk_args ts -> (

let uu____3532 = (FStar_Options.smtencoding_l_arith_native ())
in (match (uu____3532) with
| true -> begin
(

let uu____3533 = (

let uu____3534 = (mk_args ts)
in (op uu____3534))
in (FStar_All.pipe_right uu____3533 FStar_SMTEncoding_Term.boxInt))
end
| uu____3535 -> begin
(mk_default ())
end)))
in (

let mk_nl = (fun nm op ts -> (

let uu____3557 = (FStar_Options.smtencoding_nl_arith_wrapped ())
in (match (uu____3557) with
| true -> begin
(

let uu____3558 = (binary ts)
in (match (uu____3558) with
| (t1, t2) -> begin
(

let uu____3563 = (FStar_SMTEncoding_Util.mkApp ((nm), ((t1)::(t2)::[])))
in (FStar_All.pipe_right uu____3563 FStar_SMTEncoding_Term.boxInt))
end))
end
| uu____3565 -> begin
(

let uu____3566 = (FStar_Options.smtencoding_nl_arith_native ())
in (match (uu____3566) with
| true -> begin
(

let uu____3567 = (op (binary ts))
in (FStar_All.pipe_right uu____3567 FStar_SMTEncoding_Term.boxInt))
end
| uu____3568 -> begin
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

let uu____3657 = (

let uu____3663 = (FStar_List.tryFind (fun uu____3678 -> (match (uu____3678) with
| (l, uu____3685) -> begin
(FStar_Syntax_Syntax.fv_eq_lid head_fv l)
end)) ops)
in (FStar_All.pipe_right uu____3663 FStar_Util.must))
in (match (uu____3657) with
| (uu____3710, op) -> begin
(

let uu____3718 = (op arg_tms)
in ((uu____3718), (decls)))
end)))))))))))))))
end)))
and encode_BitVector_term : env_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.arg Prims.list  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list) = (fun env head1 args_e -> (

let uu____3725 = (FStar_List.hd args_e)
in (match (uu____3725) with
| (tm_sz, uu____3730) -> begin
(

let sz = (getInteger tm_sz.FStar_Syntax_Syntax.n)
in (

let sz_key = (FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz))
in (

let sz_decls = (

let uu____3739 = (FStar_Util.smap_try_find env.cache sz_key)
in (match (uu____3739) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
[]
end
| FStar_Pervasives_Native.None -> begin
(

let t_decls = (FStar_SMTEncoding_Term.mkBvConstructor sz)
in ((

let uu____3745 = (mk_cache_entry env "" [] [])
in (FStar_Util.smap_add env.cache sz_key uu____3745));
t_decls;
))
end))
in (

let uu____3746 = (

let uu____3750 = (FStar_List.tail args_e)
in (encode_args uu____3750 env))
in (match (uu____3746) with
| (arg_tms, decls) -> begin
(

let head_fv = (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____3760 -> begin
(failwith "Impossible")
end)
in (

let unary = (fun arg_tms1 -> (

let uu____3767 = (FStar_List.hd arg_tms1)
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____3767)))
in (

let unary_arith = (fun arg_tms1 -> (

let uu____3774 = (FStar_List.hd arg_tms1)
in (FStar_SMTEncoding_Term.unboxInt uu____3774)))
in (

let binary = (fun arg_tms1 -> (

let uu____3783 = (

let uu____3784 = (FStar_List.hd arg_tms1)
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____3784))
in (

let uu____3785 = (

let uu____3786 = (

let uu____3787 = (FStar_List.tl arg_tms1)
in (FStar_List.hd uu____3787))
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____3786))
in ((uu____3783), (uu____3785)))))
in (

let binary_arith = (fun arg_tms1 -> (

let uu____3797 = (

let uu____3798 = (FStar_List.hd arg_tms1)
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____3798))
in (

let uu____3799 = (

let uu____3800 = (

let uu____3801 = (FStar_List.tl arg_tms1)
in (FStar_List.hd uu____3801))
in (FStar_SMTEncoding_Term.unboxInt uu____3800))
in ((uu____3797), (uu____3799)))))
in (

let mk_bv = (fun op mk_args ts -> (

let uu____3835 = (

let uu____3836 = (mk_args ts)
in (op uu____3836))
in (FStar_All.pipe_right uu____3835 (FStar_SMTEncoding_Term.boxBitVec sz))))
in (

let bv_and = (mk_bv FStar_SMTEncoding_Util.mkBvAnd binary)
in (

let bv_xor = (mk_bv FStar_SMTEncoding_Util.mkBvXor binary)
in (

let bv_or = (mk_bv FStar_SMTEncoding_Util.mkBvOr binary)
in (

let bv_shl = (mk_bv (FStar_SMTEncoding_Util.mkBvShl sz) binary_arith)
in (

let bv_shr = (mk_bv (FStar_SMTEncoding_Util.mkBvShr sz) binary_arith)
in (

let bv_udiv = (mk_bv (FStar_SMTEncoding_Util.mkBvUdiv sz) binary_arith)
in (

let bv_mod = (mk_bv (FStar_SMTEncoding_Util.mkBvMod sz) binary_arith)
in (

let bv_to = (mk_bv (FStar_SMTEncoding_Util.mkNatToBv sz) unary_arith)
in (

let ops = (((FStar_Parser_Const.bv_and_lid), (bv_and)))::(((FStar_Parser_Const.bv_xor_lid), (bv_xor)))::(((FStar_Parser_Const.bv_or_lid), (bv_or)))::(((FStar_Parser_Const.bv_shift_left_lid), (bv_shl)))::(((FStar_Parser_Const.bv_shift_right_lid), (bv_shr)))::(((FStar_Parser_Const.bv_udiv_lid), (bv_udiv)))::(((FStar_Parser_Const.bv_mod_lid), (bv_mod)))::(((FStar_Parser_Const.nat_to_bv_lid), (bv_to)))::[]
in (

let uu____3959 = (

let uu____3965 = (FStar_List.tryFind (fun uu____3980 -> (match (uu____3980) with
| (l, uu____3987) -> begin
(FStar_Syntax_Syntax.fv_eq_lid head_fv l)
end)) ops)
in (FStar_All.pipe_right uu____3965 FStar_Util.must))
in (match (uu____3959) with
| (uu____4013, op) -> begin
(

let uu____4021 = (op arg_tms)
in ((uu____4021), ((FStar_List.append sz_decls decls))))
end)))))))))))))))))
end)))))
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let t0 = (FStar_Syntax_Subst.compress t)
in ((

let uu____4029 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____4029) with
| true -> begin
(

let uu____4030 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____4031 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____4032 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" uu____4030 uu____4031 uu____4032))))
end
| uu____4033 -> begin
()
end));
(match (t0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____4036) -> begin
(

let uu____4051 = (

let uu____4052 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____4053 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____4054 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____4055 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4052 uu____4053 uu____4054 uu____4055)))))
in (failwith uu____4051))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____4058 = (

let uu____4059 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____4060 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____4061 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____4062 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4059 uu____4060 uu____4061 uu____4062)))))
in (failwith uu____4058))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____4066 = (

let uu____4067 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" uu____4067))
in (failwith uu____4066))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, k, uu____4072) -> begin
(encode_term t1 env)
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____4102) -> begin
(encode_term t1 env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t1 = (lookup_term_var env x)
in ((t1), ([])))
end
| FStar_Syntax_Syntax.Tm_fvar (v1) -> begin
(

let uu____4111 = (lookup_free_var env v1.FStar_Syntax_Syntax.fv_name)
in ((uu____4111), ([])))
end
| FStar_Syntax_Syntax.Tm_type (uu____4113) -> begin
((FStar_SMTEncoding_Term.mk_Term_type), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____4116) -> begin
(encode_term t1 env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____4122 = (encode_const c)
in ((uu____4122), ([])))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let module_name = env.current_module_name
in (

let uu____4137 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____4137) with
| (binders1, res) -> begin
(

let uu____4144 = ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res))
in (match (uu____4144) with
| true -> begin
(

let uu____4147 = (encode_binders FStar_Pervasives_Native.None binders1 env)
in (match (uu____4147) with
| (vars, guards, env', decls, uu____4162) -> begin
(

let fsym = (

let uu____4172 = (varops.fresh "f")
in ((uu____4172), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV fsym)
in (

let app = (mk_Apply f vars)
in (

let uu____4175 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post (

let uu___135_4181 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___135_4181.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___135_4181.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___135_4181.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___135_4181.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___135_4181.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___135_4181.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___135_4181.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___135_4181.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___135_4181.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___135_4181.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___135_4181.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___135_4181.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___135_4181.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___135_4181.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___135_4181.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___135_4181.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___135_4181.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___135_4181.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___135_4181.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___135_4181.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___135_4181.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___135_4181.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___135_4181.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___135_4181.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___135_4181.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___135_4181.FStar_TypeChecker_Env.is_native_tactic}) res)
in (match (uu____4175) with
| (pre_opt, res_t) -> begin
(

let uu____4188 = (encode_term_pred FStar_Pervasives_Native.None res_t env' app)
in (match (uu____4188) with
| (res_pred, decls') -> begin
(

let uu____4195 = (match (pre_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____4202 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____4202), ([])))
end
| FStar_Pervasives_Native.Some (pre) -> begin
(

let uu____4205 = (encode_formula pre env')
in (match (uu____4205) with
| (guard, decls0) -> begin
(

let uu____4213 = (FStar_SMTEncoding_Util.mk_and_l ((guard)::guards))
in ((uu____4213), (decls0)))
end))
end)
in (match (uu____4195) with
| (guards1, guard_decls) -> begin
(

let t_interp = (

let uu____4221 = (

let uu____4227 = (FStar_SMTEncoding_Util.mkImp ((guards1), (res_pred)))
in ((((app)::[])::[]), (vars), (uu____4227)))
in (FStar_SMTEncoding_Util.mkForall uu____4221))
in (

let cvars = (

let uu____4237 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right uu____4237 (FStar_List.filter (fun uu____4246 -> (match (uu____4246) with
| (x, uu____4250) -> begin
(x <> (FStar_Pervasives_Native.fst fsym))
end)))))
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), ((fsym)::cvars), (t_interp)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____4261 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____4261) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
(

let uu____4266 = (

let uu____4267 = (

let uu____4271 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((cache_entry.cache_symbol_name), (uu____4271)))
in (FStar_SMTEncoding_Util.mkApp uu____4267))
in ((uu____4266), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append guard_decls (use_cache_entry cache_entry)))))))
end
| FStar_Pervasives_Native.None -> begin
(

let tsym = (

let uu____4282 = (

let uu____4283 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_arrow_" uu____4283))
in (varops.mk_unique uu____4282))
in (

let cvar_sorts = (FStar_List.map FStar_Pervasives_Native.snd cvars)
in (

let caption = (

let uu____4290 = (FStar_Options.log_queries ())
in (match (uu____4290) with
| true -> begin
(

let uu____4292 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in FStar_Pervasives_Native.Some (uu____4292))
end
| uu____4293 -> begin
FStar_Pervasives_Native.None
end))
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (caption)))
in (

let t1 = (

let uu____4298 = (

let uu____4302 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((tsym), (uu____4302)))
in (FStar_SMTEncoding_Util.mkApp uu____4298))
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t1 FStar_SMTEncoding_Term.mk_Term_type)
in (

let k_assumption = (

let a_name = (Prims.strcat "kinding_" tsym)
in (

let uu____4310 = (

let uu____4314 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((uu____4314), (FStar_Pervasives_Native.Some (a_name)), (a_name)))
in (FStar_SMTEncoding_Util.mkAssume uu____4310)))
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t1)
in (

let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t1)
in (

let pre_typing = (

let a_name = (Prims.strcat "pre_typing_" tsym)
in (

let uu____4327 = (

let uu____4331 = (

let uu____4332 = (

let uu____4338 = (

let uu____4339 = (

let uu____4342 = (

let uu____4343 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____4343))
in ((f_has_t), (uu____4342)))
in (FStar_SMTEncoding_Util.mkImp uu____4339))
in ((((f_has_t)::[])::[]), ((fsym)::cvars), (uu____4338)))
in (mkForall_fuel uu____4332))
in ((uu____4331), (FStar_Pervasives_Native.Some ("pre-typing for functions")), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____4327)))
in (

let t_interp1 = (

let a_name = (Prims.strcat "interpretation_" tsym)
in (

let uu____4356 = (

let uu____4360 = (

let uu____4361 = (

let uu____4367 = (FStar_SMTEncoding_Util.mkIff ((f_has_t_z), (t_interp)))
in ((((f_has_t_z)::[])::[]), ((fsym)::cvars), (uu____4367)))
in (FStar_SMTEncoding_Util.mkForall uu____4361))
in ((uu____4360), (FStar_Pervasives_Native.Some (a_name)), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____4356)))
in (

let t_decls = (FStar_List.append ((tdecl)::decls) (FStar_List.append decls' (FStar_List.append guard_decls ((k_assumption)::(pre_typing)::(t_interp1)::[]))))
in ((

let uu____4381 = (mk_cache_entry env tsym cvar_sorts t_decls)
in (FStar_Util.smap_add env.cache tkey_hash uu____4381));
((t1), (t_decls));
)))))))))))))
end))))))
end))
end))
end)))))
end))
end
| uu____4383 -> begin
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

let uu____4392 = (

let uu____4396 = (FStar_SMTEncoding_Term.mk_HasType t1 FStar_SMTEncoding_Term.mk_Term_type)
in ((uu____4396), (FStar_Pervasives_Native.Some ("Typing for non-total arrows")), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____4392)))
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

let uu____4405 = (

let uu____4409 = (

let uu____4410 = (

let uu____4416 = (

let uu____4417 = (

let uu____4420 = (

let uu____4421 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____4421))
in ((f_has_t), (uu____4420)))
in (FStar_SMTEncoding_Util.mkImp uu____4417))
in ((((f_has_t)::[])::[]), ((fsym)::[]), (uu____4416)))
in (mkForall_fuel uu____4410))
in ((uu____4409), (FStar_Pervasives_Native.Some (a_name)), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____4405)))
in ((t1), ((tdecl)::(t_kinding)::(t_interp)::[]))))))))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (uu____4435) -> begin
(

let uu____4440 = (

let uu____4443 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)
in (match (uu____4443) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.tk = uu____4448; FStar_Syntax_Syntax.pos = uu____4449; FStar_Syntax_Syntax.vars = uu____4450} -> begin
(

let uu____4457 = (FStar_Syntax_Subst.open_term ((((x), (FStar_Pervasives_Native.None)))::[]) f)
in (match (uu____4457) with
| (b, f1) -> begin
(

let uu____4471 = (

let uu____4472 = (FStar_List.hd b)
in (FStar_Pervasives_Native.fst uu____4472))
in ((uu____4471), (f1)))
end))
end
| uu____4477 -> begin
(failwith "impossible")
end))
in (match (uu____4440) with
| (x, f) -> begin
(

let uu____4484 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (uu____4484) with
| (base_t, decls) -> begin
(

let uu____4491 = (gen_term_var env x)
in (match (uu____4491) with
| (x1, xtm, env') -> begin
(

let uu____4500 = (encode_formula f env')
in (match (uu____4500) with
| (refinement, decls') -> begin
(

let uu____4507 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____4507) with
| (fsym, fterm) -> begin
(

let tm_has_type_with_fuel = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (FStar_Pervasives_Native.Some (fterm)) xtm base_t)
in (

let encoding = (FStar_SMTEncoding_Util.mkAnd ((tm_has_type_with_fuel), (refinement)))
in (

let cvars = (

let uu____4518 = (

let uu____4520 = (FStar_SMTEncoding_Term.free_variables refinement)
in (

let uu____4524 = (FStar_SMTEncoding_Term.free_variables tm_has_type_with_fuel)
in (FStar_List.append uu____4520 uu____4524)))
in (FStar_Util.remove_dups FStar_SMTEncoding_Term.fv_eq uu____4518))
in (

let cvars1 = (FStar_All.pipe_right cvars (FStar_List.filter (fun uu____4543 -> (match (uu____4543) with
| (y, uu____4547) -> begin
((y <> x1) && (y <> fsym))
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

let uu____4566 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____4566) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
(

let uu____4571 = (

let uu____4572 = (

let uu____4576 = (FStar_All.pipe_right cvars1 (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((cache_entry.cache_symbol_name), (uu____4576)))
in (FStar_SMTEncoding_Util.mkApp uu____4572))
in ((uu____4571), ((FStar_List.append decls (FStar_List.append decls' (use_cache_entry cache_entry))))))
end
| FStar_Pervasives_Native.None -> begin
(

let module_name = env.current_module_name
in (

let tsym = (

let uu____4588 = (

let uu____4589 = (

let uu____4590 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "_Tm_refine_" uu____4590))
in (Prims.strcat module_name uu____4589))
in (varops.mk_unique uu____4588))
in (

let cvar_sorts = (FStar_List.map FStar_Pervasives_Native.snd cvars1)
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let t1 = (

let uu____4599 = (

let uu____4603 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars1)
in ((tsym), (uu____4603)))
in (FStar_SMTEncoding_Util.mkApp uu____4599))
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

let uu____4614 = (

let uu____4618 = (

let uu____4619 = (

let uu____4625 = (FStar_SMTEncoding_Util.mkIff ((t_haseq_ref), (t_haseq_base)))
in ((((t_haseq_ref)::[])::[]), (cvars1), (uu____4625)))
in (FStar_SMTEncoding_Util.mkForall uu____4619))
in ((uu____4618), (FStar_Pervasives_Native.Some ((Prims.strcat "haseq for " tsym))), ((Prims.strcat "haseq" tsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____4614))
in (

let t_valid = (

let xx = ((x1), (FStar_SMTEncoding_Term.Term_sort))
in (

let valid_t = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((t1)::[])))
in (

let uu____4640 = (

let uu____4644 = (

let uu____4645 = (

let uu____4651 = (

let uu____4652 = (

let uu____4655 = (

let uu____4656 = (

let uu____4662 = (FStar_SMTEncoding_Util.mkAnd ((x_has_base_t), (refinement)))
in (([]), ((xx)::[]), (uu____4662)))
in (FStar_SMTEncoding_Util.mkExists uu____4656))
in ((uu____4655), (valid_t)))
in (FStar_SMTEncoding_Util.mkIff uu____4652))
in ((((valid_t)::[])::[]), (cvars1), (uu____4651)))
in (FStar_SMTEncoding_Util.mkForall uu____4645))
in ((uu____4644), (FStar_Pervasives_Native.Some ("validity axiom for refinement")), ((Prims.strcat "ref_valid_" tsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____4640))))
in (

let t_kinding = (

let uu____4682 = (

let uu____4686 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars1), (t_has_kind)))
in ((uu____4686), (FStar_Pervasives_Native.Some ("refinement kinding")), ((Prims.strcat "refinement_kinding_" tsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____4682))
in (

let t_interp = (

let uu____4696 = (

let uu____4700 = (

let uu____4701 = (

let uu____4707 = (FStar_SMTEncoding_Util.mkIff ((x_has_t), (encoding)))
in ((((x_has_t)::[])::[]), ((ffv)::(xfv)::cvars1), (uu____4707)))
in (FStar_SMTEncoding_Util.mkForall uu____4701))
in (

let uu____4719 = (

let uu____4721 = (FStar_Syntax_Print.term_to_string t0)
in FStar_Pervasives_Native.Some (uu____4721))
in ((uu____4700), (uu____4719), ((Prims.strcat "refinement_interpretation_" tsym)))))
in (FStar_SMTEncoding_Util.mkAssume uu____4696))
in (

let t_decls = (FStar_List.append decls (FStar_List.append decls' ((tdecl)::(t_kinding)::(t_valid)::(t_interp)::(t_haseq1)::[])))
in ((

let uu____4726 = (mk_cache_entry env tsym cvar_sorts t_decls)
in (FStar_Util.smap_add env.cache tkey_hash uu____4726));
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

let uu____4747 = (FStar_Syntax_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Util.mk_Term_uvar uu____4747))
in (

let uu____4748 = (encode_term_pred FStar_Pervasives_Native.None k env ttm)
in (match (uu____4748) with
| (t_has_k, decls) -> begin
(

let d = (

let uu____4756 = (

let uu____4760 = (

let uu____4761 = (

let uu____4762 = (

let uu____4763 = (FStar_Syntax_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____4763))
in (FStar_Util.format1 "uvar_typing_%s" uu____4762))
in (varops.mk_unique uu____4761))
in ((t_has_k), (FStar_Pervasives_Native.Some ("Uvar typing")), (uu____4760)))
in (FStar_SMTEncoding_Util.mkAssume uu____4756))
in ((ttm), ((FStar_List.append decls ((d)::[])))))
end)))
end
| FStar_Syntax_Syntax.Tm_app (uu____4766) -> begin
(

let uu____4776 = (FStar_Syntax_Util.head_and_args t0)
in (match (uu____4776) with
| (head1, args_e) -> begin
(

let uu____4804 = (

let uu____4812 = (

let uu____4813 = (FStar_Syntax_Subst.compress head1)
in uu____4813.FStar_Syntax_Syntax.n)
in ((uu____4812), (args_e)))
in (match (uu____4804) with
| uu____4823 when (head_redex env head1) -> begin
(

let uu____4831 = (whnf env t)
in (encode_term uu____4831 env))
end
| uu____4832 when (is_arithmetic_primitive head1 args_e) -> begin
(encode_arith_term env head1 args_e)
end
| uu____4844 when (is_BitVector_primitive head1 args_e) -> begin
(encode_BitVector_term env head1 args_e)
end
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____4853; FStar_Syntax_Syntax.pos = uu____4854; FStar_Syntax_Syntax.vars = uu____4855}, uu____4856), (uu____4857)::((v1, uu____4859))::((v2, uu____4861))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.lexcons_lid) -> begin
(

let uu____4899 = (encode_term v1 env)
in (match (uu____4899) with
| (v11, decls1) -> begin
(

let uu____4906 = (encode_term v2 env)
in (match (uu____4906) with
| (v21, decls2) -> begin
(

let uu____4913 = (FStar_SMTEncoding_Util.mk_LexCons v11 v21)
in ((uu____4913), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____4916)::((v1, uu____4918))::((v2, uu____4920))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.lexcons_lid) -> begin
(

let uu____4954 = (encode_term v1 env)
in (match (uu____4954) with
| (v11, decls1) -> begin
(

let uu____4961 = (encode_term v2 env)
in (match (uu____4961) with
| (v21, decls2) -> begin
(

let uu____4968 = (FStar_SMTEncoding_Util.mk_LexCons v11 v21)
in ((uu____4968), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), uu____4970) -> begin
(

let e0 = (

let uu____4982 = (FStar_List.hd args_e)
in (FStar_TypeChecker_Util.reify_body_with_arg env.tcenv head1 uu____4982))
in ((

let uu____4988 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____4988) with
| true -> begin
(

let uu____4989 = (FStar_Syntax_Print.term_to_string e0)
in (FStar_Util.print1 "Result of normalization %s\n" uu____4989))
end
| uu____4990 -> begin
()
end));
(

let e = (

let uu____4994 = (

let uu____4995 = (FStar_TypeChecker_Util.remove_reify e0)
in (

let uu____4996 = (FStar_List.tl args_e)
in (FStar_Syntax_Syntax.mk_Tm_app uu____4995 uu____4996)))
in (uu____4994 FStar_Pervasives_Native.None t0.FStar_Syntax_Syntax.pos))
in (encode_term e env));
))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____5005)), ((arg, uu____5007))::[]) -> begin
(encode_term arg env)
end
| uu____5025 -> begin
(

let uu____5033 = (encode_args args_e env)
in (match (uu____5033) with
| (args, decls) -> begin
(

let encode_partial_app = (fun ht_opt -> (

let uu____5066 = (encode_term head1 env)
in (match (uu____5066) with
| (head2, decls') -> begin
(

let app_tm = (mk_Apply_args head2 args)
in (match (ht_opt) with
| FStar_Pervasives_Native.None -> begin
((app_tm), ((FStar_List.append decls decls')))
end
| FStar_Pervasives_Native.Some (formals, c) -> begin
(

let uu____5105 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (uu____5105) with
| (formals1, rest) -> begin
(

let subst1 = (FStar_List.map2 (fun uu____5155 uu____5156 -> (match (((uu____5155), (uu____5156))) with
| ((bv, uu____5170), (a, uu____5172)) -> begin
FStar_Syntax_Syntax.NT (((bv), (a)))
end)) formals1 args_e)
in (

let ty = (

let uu____5186 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right uu____5186 (FStar_Syntax_Subst.subst subst1)))
in (

let uu____5191 = (encode_term_pred FStar_Pervasives_Native.None ty env app_tm)
in (match (uu____5191) with
| (has_type, decls'') -> begin
(

let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (

let e_typing = (

let uu____5201 = (

let uu____5205 = (FStar_SMTEncoding_Util.mkForall ((((has_type)::[])::[]), (cvars), (has_type)))
in (

let uu____5210 = (

let uu____5211 = (

let uu____5212 = (

let uu____5213 = (FStar_SMTEncoding_Term.hash_of_term app_tm)
in (FStar_Util.digest_of_string uu____5213))
in (Prims.strcat "partial_app_typing_" uu____5212))
in (varops.mk_unique uu____5211))
in ((uu____5205), (FStar_Pervasives_Native.Some ("Partial app typing")), (uu____5210))))
in (FStar_SMTEncoding_Util.mkAssume uu____5201))
in ((app_tm), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' ((e_typing)::[]))))))))
end))))
end))
end))
end)))
in (

let encode_full_app = (fun fv -> (

let uu____5224 = (lookup_free_var_sym env fv)
in (match (uu____5224) with
| (fname, fuel_args) -> begin
(

let tm = (FStar_SMTEncoding_Util.mkApp' ((fname), ((FStar_List.append fuel_args args))))
in ((tm), (decls)))
end)))
in (

let head2 = (FStar_Syntax_Subst.compress head1)
in (

let head_type = (match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (x); FStar_Syntax_Syntax.tk = uu____5245; FStar_Syntax_Syntax.pos = uu____5246; FStar_Syntax_Syntax.vars = uu____5247}, uu____5248) -> begin
FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____5259; FStar_Syntax_Syntax.pos = uu____5260; FStar_Syntax_Syntax.vars = uu____5261}, uu____5262) -> begin
(

let uu____5267 = (

let uu____5268 = (

let uu____5271 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____5271 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____5268 FStar_Pervasives_Native.snd))
in FStar_Pervasives_Native.Some (uu____5267))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____5287 = (

let uu____5288 = (

let uu____5291 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____5291 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____5288 FStar_Pervasives_Native.snd))
in FStar_Pervasives_Native.Some (uu____5287))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____5306, (FStar_Util.Inl (t1), uu____5308), uu____5309) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____5347, (FStar_Util.Inr (c), uu____5349), uu____5350) -> begin
FStar_Pervasives_Native.Some ((FStar_Syntax_Util.comp_result c))
end
| uu____5388 -> begin
FStar_Pervasives_Native.None
end)
in (match (head_type) with
| FStar_Pervasives_Native.None -> begin
(encode_partial_app FStar_Pervasives_Native.None)
end
| FStar_Pervasives_Native.Some (head_type1) -> begin
(

let head_type2 = (

let uu____5408 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type1)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine uu____5408))
in (

let uu____5409 = (curried_arrow_formals_comp head_type2)
in (match (uu____5409) with
| (formals, c) -> begin
(match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____5419; FStar_Syntax_Syntax.pos = uu____5420; FStar_Syntax_Syntax.vars = uu____5421}, uu____5422) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| uu____5448 -> begin
(match (((FStar_List.length formals) > (FStar_List.length args))) with
| true -> begin
(encode_partial_app (FStar_Pervasives_Native.Some (((formals), (c)))))
end
| uu____5465 -> begin
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

let uu____5488 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____5488) with
| (bs1, body1, opening) -> begin
(

let fallback = (fun uu____5503 -> (

let f = (varops.fresh "Tm_abs")
in (

let decl = FStar_SMTEncoding_Term.DeclFun (((f), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Imprecise function encoding"))))
in (

let uu____5508 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in ((uu____5508), ((decl)::[]))))))
in (

let is_impure = (fun rc -> (

let uu____5514 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv rc.FStar_Syntax_Syntax.residual_effect)
in (FStar_All.pipe_right uu____5514 Prims.op_Negation)))
in (

let codomain_eff = (fun rc -> (

let res_typ = (match (rc.FStar_Syntax_Syntax.residual_typ) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5523 = (FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange [] FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right uu____5523 FStar_Pervasives_Native.fst))
end
| FStar_Pervasives_Native.Some (t1) -> begin
t1
end)
in (match ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_Tot_lid)) with
| true -> begin
(

let uu____5536 = (FStar_Syntax_Syntax.mk_Total res_typ)
in FStar_Pervasives_Native.Some (uu____5536))
end
| uu____5537 -> begin
(match ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_GTot_lid)) with
| true -> begin
(

let uu____5539 = (FStar_Syntax_Syntax.mk_GTotal res_typ)
in FStar_Pervasives_Native.Some (uu____5539))
end
| uu____5540 -> begin
FStar_Pervasives_Native.None
end)
end)))
in (match (lopt) with
| FStar_Pervasives_Native.None -> begin
((

let uu____5544 = (

let uu____5545 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)" uu____5545))
in (FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____5544));
(fallback ());
)
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____5547 = ((is_impure rc) && (

let uu____5549 = (FStar_TypeChecker_Env.is_reifiable env.tcenv rc)
in (not (uu____5549))))
in (match (uu____5547) with
| true -> begin
(fallback ())
end
| uu____5552 -> begin
(

let cache_size = (FStar_Util.smap_size env.cache)
in (

let uu____5554 = (encode_binders FStar_Pervasives_Native.None bs1 env)
in (match (uu____5554) with
| (vars, guards, envbody, decls, uu____5569) -> begin
(

let body2 = (FStar_TypeChecker_Util.reify_body env.tcenv body1)
in (

let uu____5577 = (encode_term body2 envbody)
in (match (uu____5577) with
| (body3, decls') -> begin
(

let uu____5584 = (

let uu____5589 = (codomain_eff rc)
in (match (uu____5589) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), ([]))
end
| FStar_Pervasives_Native.Some (c) -> begin
(

let tfun = (FStar_Syntax_Util.arrow bs1 c)
in (

let uu____5601 = (encode_term tfun env)
in (match (uu____5601) with
| (t1, decls1) -> begin
((FStar_Pervasives_Native.Some (t1)), (decls1))
end)))
end))
in (match (uu____5584) with
| (arrow_t_opt, decls'') -> begin
(

let key_body = (

let uu____5620 = (

let uu____5626 = (

let uu____5627 = (

let uu____5630 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____5630), (body3)))
in (FStar_SMTEncoding_Util.mkImp uu____5627))
in (([]), (vars), (uu____5626)))
in (FStar_SMTEncoding_Util.mkForall uu____5620))
in (

let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (

let cvars1 = (match (arrow_t_opt) with
| FStar_Pervasives_Native.None -> begin
cvars
end
| FStar_Pervasives_Native.Some (t1) -> begin
(

let uu____5638 = (

let uu____5640 = (FStar_SMTEncoding_Term.free_variables t1)
in (FStar_List.append uu____5640 cvars))
in (FStar_Util.remove_dups FStar_SMTEncoding_Term.fv_eq uu____5638))
end)
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), (cvars1), (key_body)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____5651 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____5651) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
(

let uu____5656 = (

let uu____5657 = (

let uu____5661 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars1)
in ((cache_entry.cache_symbol_name), (uu____5661)))
in (FStar_SMTEncoding_Util.mkApp uu____5657))
in ((uu____5656), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' (use_cache_entry cache_entry)))))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____5667 = (is_an_eta_expansion env vars body3)
in (match (uu____5667) with
| FStar_Pervasives_Native.Some (t1) -> begin
(

let decls1 = (

let uu____5674 = (

let uu____5675 = (FStar_Util.smap_size env.cache)
in (uu____5675 = cache_size))
in (match (uu____5674) with
| true -> begin
[]
end
| uu____5677 -> begin
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

let uu____5686 = (

let uu____5687 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_abs_" uu____5687))
in (varops.mk_unique uu____5686))
in (Prims.strcat module_name (Prims.strcat "_" fsym))))
in (

let fdecl = FStar_SMTEncoding_Term.DeclFun (((fsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let f = (

let uu____5692 = (

let uu____5696 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars1)
in ((fsym), (uu____5696)))
in (FStar_SMTEncoding_Util.mkApp uu____5692))
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

let uu____5708 = (

let uu____5709 = (

let uu____5713 = (FStar_SMTEncoding_Util.mkForall ((((f)::[])::[]), (cvars1), (f_has_t)))
in ((uu____5713), (FStar_Pervasives_Native.Some (a_name)), (a_name)))
in (FStar_SMTEncoding_Util.mkAssume uu____5709))
in (uu____5708)::[])))
end)
in (

let interp_f = (

let a_name = (Prims.strcat "interpretation_" fsym)
in (

let uu____5721 = (

let uu____5725 = (

let uu____5726 = (

let uu____5732 = (FStar_SMTEncoding_Util.mkEq ((app), (body3)))
in ((((app)::[])::[]), ((FStar_List.append vars cvars1)), (uu____5732)))
in (FStar_SMTEncoding_Util.mkForall uu____5726))
in ((uu____5725), (FStar_Pervasives_Native.Some (a_name)), (a_name)))
in (FStar_SMTEncoding_Util.mkAssume uu____5721)))
in (

let f_decls = (FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' (FStar_List.append ((fdecl)::typing_f) ((interp_f)::[])))))
in ((

let uu____5742 = (mk_cache_entry env fsym cvar_sorts f_decls)
in (FStar_Util.smap_add env.cache tkey_hash uu____5742));
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
| FStar_Syntax_Syntax.Tm_let ((uu____5744, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____5745); FStar_Syntax_Syntax.lbunivs = uu____5746; FStar_Syntax_Syntax.lbtyp = uu____5747; FStar_Syntax_Syntax.lbeff = uu____5748; FStar_Syntax_Syntax.lbdef = uu____5749})::uu____5750), uu____5751) -> begin
(failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____5769; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____5771; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (uu____5787) -> begin
((FStar_Errors.diag t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts");
(

let e = (varops.fresh "let-rec")
in (

let decl_e = FStar_SMTEncoding_Term.DeclFun (((e), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let uu____5800 = (FStar_SMTEncoding_Util.mkFreeV ((e), (FStar_SMTEncoding_Term.Term_sort)))
in ((uu____5800), ((decl_e)::[])))));
)
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end);
)))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (

let uu____5840 = (encode_term e1 env)
in (match (uu____5840) with
| (ee1, decls1) -> begin
(

let uu____5847 = (FStar_Syntax_Subst.open_term ((((x), (FStar_Pervasives_Native.None)))::[]) e2)
in (match (uu____5847) with
| (xs, e21) -> begin
(

let uu____5861 = (FStar_List.hd xs)
in (match (uu____5861) with
| (x1, uu____5869) -> begin
(

let env' = (push_term_var env x1 ee1)
in (

let uu____5871 = (encode_body e21 env')
in (match (uu____5871) with
| (ee2, decls2) -> begin
((ee2), ((FStar_List.append decls1 decls2)))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (

let uu____5893 = (

let uu____5897 = (

let uu____5898 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.null_bv uu____5898))
in (gen_term_var env uu____5897))
in (match (uu____5893) with
| (scrsym, scr', env1) -> begin
(

let uu____5908 = (encode_term e env1)
in (match (uu____5908) with
| (scr, decls) -> begin
(

let uu____5915 = (

let encode_branch = (fun b uu____5931 -> (match (uu____5931) with
| (else_case, decls1) -> begin
(

let uu____5942 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____5942) with
| (p, w, br) -> begin
(

let uu____5961 = (encode_pat env1 p)
in (match (uu____5961) with
| (env0, pattern) -> begin
(

let guard = (pattern.guard scr')
in (

let projections = (pattern.projections scr')
in (

let env2 = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env2 uu____5985 -> (match (uu____5985) with
| (x, t) -> begin
(push_term_var env2 x t)
end)) env1))
in (

let uu____5990 = (match (w) with
| FStar_Pervasives_Native.None -> begin
((guard), ([]))
end
| FStar_Pervasives_Native.Some (w1) -> begin
(

let uu____6005 = (encode_term w1 env2)
in (match (uu____6005) with
| (w2, decls2) -> begin
(

let uu____6013 = (

let uu____6014 = (

let uu____6017 = (

let uu____6018 = (

let uu____6021 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue)
in ((w2), (uu____6021)))
in (FStar_SMTEncoding_Util.mkEq uu____6018))
in ((guard), (uu____6017)))
in (FStar_SMTEncoding_Util.mkAnd uu____6014))
in ((uu____6013), (decls2)))
end))
end)
in (match (uu____5990) with
| (guard1, decls2) -> begin
(

let uu____6029 = (encode_br br env2)
in (match (uu____6029) with
| (br1, decls3) -> begin
(

let uu____6037 = (FStar_SMTEncoding_Util.mkITE ((guard1), (br1), (else_case)))
in ((uu____6037), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end)))))
end))
end))
end))
in (FStar_List.fold_right encode_branch pats ((default_case), (decls))))
in (match (uu____5915) with
| (match_tm, decls1) -> begin
(

let uu____6048 = (FStar_SMTEncoding_Term.mkLet' (((((((scrsym), (FStar_SMTEncoding_Term.Term_sort))), (scr)))::[]), (match_tm)) FStar_Range.dummyRange)
in ((uu____6048), (decls1)))
end))
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> ((

let uu____6070 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____6070) with
| true -> begin
(

let uu____6071 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" uu____6071))
end
| uu____6072 -> begin
()
end));
(

let uu____6073 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (uu____6073) with
| (vars, pat_term) -> begin
(

let uu____6083 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun uu____6114 v1 -> (match (uu____6114) with
| (env1, vars1) -> begin
(

let uu____6142 = (gen_term_var env1 v1)
in (match (uu____6142) with
| (xx, uu____6154, env2) -> begin
((env2), ((((v1), (((xx), (FStar_SMTEncoding_Term.Term_sort)))))::vars1))
end))
end)) ((env), ([]))))
in (match (uu____6083) with
| (env1, vars1) -> begin
(

let rec mk_guard = (fun pat1 scrutinee -> (match (pat1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_var (uu____6199) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_wild (uu____6200) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____6201) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____6207 = (

let uu____6210 = (encode_const c)
in ((scrutinee), (uu____6210)))
in (FStar_SMTEncoding_Util.mkEq uu____6207))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let is_f = (

let tc_name = (FStar_TypeChecker_Env.typ_of_datacon env1.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let uu____6223 = (FStar_TypeChecker_Env.datacons_of_typ env1.tcenv tc_name)
in (match (uu____6223) with
| (uu____6227, (uu____6228)::[]) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| uu____6230 -> begin
(mk_data_tester env1 f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
end)))
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____6251 -> (match (uu____6251) with
| (arg, uu____6256) -> begin
(

let proj = (primitive_projector_by_pos env1.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____6260 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_guard arg uu____6260)))
end))))
in (FStar_SMTEncoding_Util.mk_and_l ((is_f)::sub_term_guards))))
end))
in (

let rec mk_projections = (fun pat1 scrutinee -> (match (pat1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (x, uu____6278) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_constant (uu____6297) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let uu____6310 = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____6336 -> (match (uu____6336) with
| (arg, uu____6344) -> begin
(

let proj = (primitive_projector_by_pos env1.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____6348 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_projections arg uu____6348)))
end))))
in (FStar_All.pipe_right uu____6310 FStar_List.flatten))
end))
in (

let pat_term1 = (fun uu____6364 -> (encode_term pat_term env1))
in (

let pattern = {pat_vars = vars1; pat_term = pat_term1; guard = (mk_guard pat); projections = (mk_projections pat)}
in ((env1), (pattern))))))
end))
end));
))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (

let uu____6371 = (FStar_All.pipe_right l (FStar_List.fold_left (fun uu____6395 uu____6396 -> (match (((uu____6395), (uu____6396))) with
| ((tms, decls), (t, uu____6416)) -> begin
(

let uu____6427 = (encode_term t env)
in (match (uu____6427) with
| (t1, decls') -> begin
(((t1)::tms), ((FStar_List.append decls decls')))
end))
end)) (([]), ([]))))
in (match (uu____6371) with
| (l1, decls) -> begin
(((FStar_List.rev l1)), (decls))
end)))
and encode_function_type_as_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let list_elements1 = (fun e -> (

let uu____6461 = (FStar_Syntax_Util.list_elements e)
in (match (uu____6461) with
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

let uu____6476 = (

let uu____6486 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right uu____6486 FStar_Syntax_Util.head_and_args))
in (match (uu____6476) with
| (head1, args) -> begin
(

let uu____6514 = (

let uu____6522 = (

let uu____6523 = (FStar_Syntax_Util.un_uinst head1)
in uu____6523.FStar_Syntax_Syntax.n)
in ((uu____6522), (args)))
in (match (uu____6514) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((uu____6534, uu____6535))::((e, uu____6537))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpat_lid) -> begin
e
end
| uu____6563 -> begin
(failwith "Unexpected pattern term")
end))
end)))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements1 p)
in (

let smt_pat_or1 = (fun t1 -> (

let uu____6590 = (

let uu____6600 = (FStar_Syntax_Util.unmeta t1)
in (FStar_All.pipe_right uu____6600 FStar_Syntax_Util.head_and_args))
in (match (uu____6590) with
| (head1, args) -> begin
(

let uu____6629 = (

let uu____6637 = (

let uu____6638 = (FStar_Syntax_Util.un_uinst head1)
in uu____6638.FStar_Syntax_Syntax.n)
in ((uu____6637), (args)))
in (match (uu____6629) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, uu____6651))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpatOr_lid) -> begin
FStar_Pervasives_Native.Some (e)
end
| uu____6671 -> begin
FStar_Pervasives_Native.None
end))
end)))
in (match (elts) with
| (t1)::[] -> begin
(

let uu____6686 = (smt_pat_or1 t1)
in (match (uu____6686) with
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____6699 = (list_elements1 e)
in (FStar_All.pipe_right uu____6699 (FStar_List.map (fun branch1 -> (

let uu____6712 = (list_elements1 branch1)
in (FStar_All.pipe_right uu____6712 (FStar_List.map one_pat)))))))
end
| uu____6720 -> begin
(

let uu____6724 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____6724)::[])
end))
end
| uu____6740 -> begin
(

let uu____6742 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____6742)::[])
end))))
in (

let uu____6758 = (

let uu____6771 = (

let uu____6772 = (FStar_Syntax_Subst.compress t)
in uu____6772.FStar_Syntax_Syntax.n)
in (match (uu____6771) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____6799 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____6799) with
| (binders1, c1) -> begin
(match (c1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____6828; FStar_Syntax_Syntax.effect_name = uu____6829; FStar_Syntax_Syntax.result_typ = uu____6830; FStar_Syntax_Syntax.effect_args = ((pre, uu____6832))::((post, uu____6834))::((pats, uu____6836))::[]; FStar_Syntax_Syntax.flags = uu____6837}) -> begin
(

let uu____6869 = (lemma_pats pats)
in ((binders1), (pre), (post), (uu____6869)))
end
| uu____6882 -> begin
(failwith "impos")
end)
end))
end
| uu____6895 -> begin
(failwith "Impos")
end))
in (match (uu____6758) with
| (binders, pre, post, patterns) -> begin
(

let env1 = (

let uu___136_6931 = env
in {bindings = uu___136_6931.bindings; depth = uu___136_6931.depth; tcenv = uu___136_6931.tcenv; warn = uu___136_6931.warn; cache = uu___136_6931.cache; nolabels = uu___136_6931.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___136_6931.encode_non_total_function_typ; current_module_name = uu___136_6931.current_module_name})
in (

let uu____6932 = (encode_binders FStar_Pervasives_Native.None binders env1)
in (match (uu____6932) with
| (vars, guards, env2, decls, uu____6947) -> begin
(

let uu____6954 = (

let uu____6961 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch1 -> (

let uu____6987 = (

let uu____6992 = (FStar_All.pipe_right branch1 (FStar_List.map (fun t1 -> (encode_term t1 env2))))
in (FStar_All.pipe_right uu____6992 FStar_List.unzip))
in (match (uu____6987) with
| (pats, decls1) -> begin
((pats), (decls1))
end)))))
in (FStar_All.pipe_right uu____6961 FStar_List.unzip))
in (match (uu____6954) with
| (pats, decls') -> begin
(

let decls'1 = (FStar_List.flatten decls')
in (

let env3 = (

let uu___137_7051 = env2
in {bindings = uu___137_7051.bindings; depth = uu___137_7051.depth; tcenv = uu___137_7051.tcenv; warn = uu___137_7051.warn; cache = uu___137_7051.cache; nolabels = true; use_zfuel_name = uu___137_7051.use_zfuel_name; encode_non_total_function_typ = uu___137_7051.encode_non_total_function_typ; current_module_name = uu___137_7051.current_module_name})
in (

let uu____7052 = (

let uu____7055 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula uu____7055 env3))
in (match (uu____7052) with
| (pre1, decls'') -> begin
(

let uu____7060 = (

let uu____7063 = (FStar_Syntax_Util.unmeta post)
in (encode_formula uu____7063 env3))
in (match (uu____7060) with
| (post1, decls''') -> begin
(

let decls1 = (FStar_List.append decls (FStar_List.append (FStar_List.flatten decls'1) (FStar_List.append decls'' decls''')))
in (

let uu____7070 = (

let uu____7071 = (

let uu____7077 = (

let uu____7078 = (

let uu____7081 = (FStar_SMTEncoding_Util.mk_and_l ((pre1)::guards))
in ((uu____7081), (post1)))
in (FStar_SMTEncoding_Util.mkImp uu____7078))
in ((pats), (vars), (uu____7077)))
in (FStar_SMTEncoding_Util.mkForall uu____7071))
in ((uu____7070), (decls1))))
end))
end))))
end))
end)))
end))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (

let debug1 = (fun phi1 -> (

let uu____7094 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____7094) with
| true -> begin
(

let uu____7095 = (FStar_Syntax_Print.tag_of_term phi1)
in (

let uu____7096 = (FStar_Syntax_Print.term_to_string phi1)
in (FStar_Util.print2 "Formula (%s)  %s\n" uu____7095 uu____7096)))
end
| uu____7097 -> begin
()
end)))
in (

let enc = (fun f r l -> (

let uu____7123 = (FStar_Util.fold_map (fun decls x -> (

let uu____7141 = (encode_term (FStar_Pervasives_Native.fst x) env)
in (match (uu____7141) with
| (t, decls') -> begin
(((FStar_List.append decls decls')), (t))
end))) [] l)
in (match (uu____7123) with
| (decls, args) -> begin
(

let uu____7158 = (

let uu___138_7159 = (f args)
in {FStar_SMTEncoding_Term.tm = uu___138_7159.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___138_7159.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____7158), (decls)))
end)))
in (

let const_op = (fun f r uu____7184 -> (

let uu____7193 = (f r)
in ((uu____7193), ([]))))
in (

let un_op = (fun f l -> (

let uu____7209 = (FStar_List.hd l)
in (FStar_All.pipe_left f uu____7209)))
in (

let bin_op = (fun f uu___112_7222 -> (match (uu___112_7222) with
| (t1)::(t2)::[] -> begin
(f ((t1), (t2)))
end
| uu____7230 -> begin
(failwith "Impossible")
end))
in (

let enc_prop_c = (fun f r l -> (

let uu____7257 = (FStar_Util.fold_map (fun decls uu____7273 -> (match (uu____7273) with
| (t, uu____7281) -> begin
(

let uu____7282 = (encode_formula t env)
in (match (uu____7282) with
| (phi1, decls') -> begin
(((FStar_List.append decls decls')), (phi1))
end))
end)) [] l)
in (match (uu____7257) with
| (decls, phis) -> begin
(

let uu____7299 = (

let uu___139_7300 = (f phis)
in {FStar_SMTEncoding_Term.tm = uu___139_7300.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___139_7300.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____7299), (decls)))
end)))
in (

let eq_op = (fun r args -> (

let rf = (FStar_List.filter (fun uu____7343 -> (match (uu____7343) with
| (a, q) -> begin
(match (q) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____7357)) -> begin
false
end
| uu____7358 -> begin
true
end)
end)) args)
in (match (((FStar_List.length rf) <> (Prims.parse_int "2"))) with
| true -> begin
(

let uu____7371 = (FStar_Util.format1 "eq_op: got %s non-implicit arguments instead of 2?" (Prims.string_of_int (FStar_List.length rf)))
in (failwith uu____7371))
end
| uu____7385 -> begin
(

let uu____7386 = (enc (bin_op FStar_SMTEncoding_Util.mkEq))
in (uu____7386 r rf))
end)))
in (

let mk_imp1 = (fun r uu___113_7405 -> (match (uu___113_7405) with
| ((lhs, uu____7409))::((rhs, uu____7411))::[] -> begin
(

let uu____7432 = (encode_formula rhs env)
in (match (uu____7432) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____7441) -> begin
((l1), (decls1))
end
| uu____7444 -> begin
(

let uu____7445 = (encode_formula lhs env)
in (match (uu____7445) with
| (l2, decls2) -> begin
(

let uu____7452 = (FStar_SMTEncoding_Term.mkImp ((l2), (l1)) r)
in ((uu____7452), ((FStar_List.append decls1 decls2))))
end))
end)
end))
end
| uu____7454 -> begin
(failwith "impossible")
end))
in (

let mk_ite = (fun r uu___114_7469 -> (match (uu___114_7469) with
| ((guard, uu____7473))::((_then, uu____7475))::((_else, uu____7477))::[] -> begin
(

let uu____7506 = (encode_formula guard env)
in (match (uu____7506) with
| (g, decls1) -> begin
(

let uu____7513 = (encode_formula _then env)
in (match (uu____7513) with
| (t, decls2) -> begin
(

let uu____7520 = (encode_formula _else env)
in (match (uu____7520) with
| (e, decls3) -> begin
(

let res = (FStar_SMTEncoding_Term.mkITE ((g), (t), (e)) r)
in ((res), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end))
end))
end
| uu____7529 -> begin
(failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (

let uu____7548 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f uu____7548)))
in (

let connectives = (

let uu____7560 = (

let uu____7569 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd))
in ((FStar_Parser_Const.and_lid), (uu____7569)))
in (

let uu____7582 = (

let uu____7592 = (

let uu____7601 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr))
in ((FStar_Parser_Const.or_lid), (uu____7601)))
in (

let uu____7614 = (

let uu____7624 = (

let uu____7634 = (

let uu____7643 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff))
in ((FStar_Parser_Const.iff_lid), (uu____7643)))
in (

let uu____7656 = (

let uu____7666 = (

let uu____7676 = (

let uu____7685 = (enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot))
in ((FStar_Parser_Const.not_lid), (uu____7685)))
in (uu____7676)::(((FStar_Parser_Const.eq2_lid), (eq_op)))::(((FStar_Parser_Const.eq3_lid), (eq_op)))::(((FStar_Parser_Const.true_lid), ((const_op FStar_SMTEncoding_Term.mkTrue))))::(((FStar_Parser_Const.false_lid), ((const_op FStar_SMTEncoding_Term.mkFalse))))::[])
in (((FStar_Parser_Const.ite_lid), (mk_ite)))::uu____7666)
in (uu____7634)::uu____7656))
in (((FStar_Parser_Const.imp_lid), (mk_imp1)))::uu____7624)
in (uu____7592)::uu____7614))
in (uu____7560)::uu____7582))
in (

let rec fallback = (fun phi1 -> (match (phi1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(

let uu____7901 = (encode_formula phi' env)
in (match (uu____7901) with
| (phi2, decls) -> begin
(

let uu____7908 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled (((phi2), (msg), (r)))) r)
in ((uu____7908), (decls)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (uu____7909) -> begin
(

let uu____7914 = (FStar_Syntax_Util.unmeta phi1)
in (encode_formula uu____7914 env))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(

let uu____7941 = (encode_match e pats FStar_SMTEncoding_Util.mkFalse env encode_formula)
in (match (uu____7941) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____7949; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____7951; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let uu____7967 = (encode_let x t1 e1 e2 env encode_formula)
in (match (uu____7967) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let head2 = (FStar_Syntax_Util.un_uinst head1)
in (match (((head2.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____7999)::((x, uu____8001))::((t, uu____8003))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.has_type_lid) -> begin
(

let uu____8037 = (encode_term x env)
in (match (uu____8037) with
| (x1, decls) -> begin
(

let uu____8044 = (encode_term t env)
in (match (uu____8044) with
| (t1, decls') -> begin
(

let uu____8051 = (FStar_SMTEncoding_Term.mk_HasType x1 t1)
in ((uu____8051), ((FStar_List.append decls decls'))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((r, uu____8055))::((msg, uu____8057))::((phi2, uu____8059))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.labeled_lid) -> begin
(

let uu____8093 = (

let uu____8096 = (

let uu____8097 = (FStar_Syntax_Subst.compress r)
in uu____8097.FStar_Syntax_Syntax.n)
in (

let uu____8100 = (

let uu____8101 = (FStar_Syntax_Subst.compress msg)
in uu____8101.FStar_Syntax_Syntax.n)
in ((uu____8096), (uu____8100))))
in (match (uu____8093) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____8108))) -> begin
(

let phi3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((phi2), (FStar_Syntax_Syntax.Meta_labeled ((((FStar_Util.string_of_unicode s)), (r1), (false))))))) FStar_Pervasives_Native.None r1)
in (fallback phi3))
end
| uu____8120 -> begin
(fallback phi2)
end))
end
| uu____8123 when (head_redex env head2) -> begin
(

let uu____8131 = (whnf env phi1)
in (encode_formula uu____8131 env))
end
| uu____8132 -> begin
(

let uu____8140 = (encode_term phi1 env)
in (match (uu____8140) with
| (tt, decls) -> begin
(

let uu____8147 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___140_8150 = tt
in {FStar_SMTEncoding_Term.tm = uu___140_8150.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___140_8150.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi1.FStar_Syntax_Syntax.pos}))
in ((uu____8147), (decls)))
end))
end))
end
| uu____8153 -> begin
(

let uu____8154 = (encode_term phi1 env)
in (match (uu____8154) with
| (tt, decls) -> begin
(

let uu____8161 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___141_8164 = tt
in {FStar_SMTEncoding_Term.tm = uu___141_8164.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___141_8164.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi1.FStar_Syntax_Syntax.pos}))
in ((uu____8161), (decls)))
end))
end))
in (

let encode_q_body = (fun env1 bs ps body -> (

let uu____8191 = (encode_binders FStar_Pervasives_Native.None bs env1)
in (match (uu____8191) with
| (vars, guards, env2, decls, uu____8213) -> begin
(

let uu____8220 = (

let uu____8227 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let uu____8254 = (

let uu____8259 = (FStar_All.pipe_right p (FStar_List.map (fun uu____8276 -> (match (uu____8276) with
| (t, uu____8282) -> begin
(encode_term t (

let uu___142_8284 = env2
in {bindings = uu___142_8284.bindings; depth = uu___142_8284.depth; tcenv = uu___142_8284.tcenv; warn = uu___142_8284.warn; cache = uu___142_8284.cache; nolabels = uu___142_8284.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___142_8284.encode_non_total_function_typ; current_module_name = uu___142_8284.current_module_name}))
end))))
in (FStar_All.pipe_right uu____8259 FStar_List.unzip))
in (match (uu____8254) with
| (p1, decls1) -> begin
((p1), ((FStar_List.flatten decls1)))
end)))))
in (FStar_All.pipe_right uu____8227 FStar_List.unzip))
in (match (uu____8220) with
| (pats, decls') -> begin
(

let uu____8336 = (encode_formula body env2)
in (match (uu____8336) with
| (body1, decls'') -> begin
(

let guards1 = (match (pats) with
| (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (gf), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____8355; FStar_SMTEncoding_Term.rng = uu____8356})::[])::[] when ((FStar_Ident.text_of_lid FStar_Parser_Const.guard_free) = gf) -> begin
[]
end
| uu____8364 -> begin
guards
end)
in (

let uu____8367 = (FStar_SMTEncoding_Util.mk_and_l guards1)
in ((vars), (pats), (uu____8367), (body1), ((FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') decls''))))))
end))
end))
end)))
in ((debug1 phi);
(

let phi1 = (FStar_Syntax_Util.unascribe phi)
in (

let check_pattern_vars = (fun vars pats -> (

let pats1 = (FStar_All.pipe_right pats (FStar_List.map (fun uu____8404 -> (match (uu____8404) with
| (x, uu____8408) -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x)
end))))
in (match (pats1) with
| [] -> begin
()
end
| (hd1)::tl1 -> begin
(

let pat_vars = (

let uu____8414 = (FStar_Syntax_Free.names hd1)
in (FStar_List.fold_left (fun out x -> (

let uu____8423 = (FStar_Syntax_Free.names x)
in (FStar_Util.set_union out uu____8423))) uu____8414 tl1))
in (

let uu____8425 = (FStar_All.pipe_right vars (FStar_Util.find_opt (fun uu____8441 -> (match (uu____8441) with
| (b, uu____8445) -> begin
(

let uu____8446 = (FStar_Util.set_mem b pat_vars)
in (not (uu____8446)))
end))))
in (match (uu____8425) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (x, uu____8450) -> begin
(

let pos = (FStar_List.fold_left (fun out t -> (FStar_Range.union_ranges out t.FStar_Syntax_Syntax.pos)) hd1.FStar_Syntax_Syntax.pos tl1)
in (

let uu____8462 = (

let uu____8463 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "SMT pattern misses at least one bound variable: %s" uu____8463))
in (FStar_Errors.warn pos uu____8462)))
end)))
end)))
in (

let uu____8464 = (FStar_Syntax_Util.destruct_typ_as_formula phi1)
in (match (uu____8464) with
| FStar_Pervasives_Native.None -> begin
(fallback phi1)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(

let uu____8470 = (FStar_All.pipe_right connectives (FStar_List.tryFind (fun uu____8509 -> (match (uu____8509) with
| (l, uu____8519) -> begin
(FStar_Ident.lid_equals op l)
end))))
in (match (uu____8470) with
| FStar_Pervasives_Native.None -> begin
(fallback phi1)
end
| FStar_Pervasives_Native.Some (uu____8542, f) -> begin
(f phi1.FStar_Syntax_Syntax.pos arms)
end))
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____8571 = (encode_q_body env vars pats body)
in (match (uu____8571) with
| (vars1, pats1, guard, body1, decls) -> begin
(

let tm = (

let uu____8597 = (

let uu____8603 = (FStar_SMTEncoding_Util.mkImp ((guard), (body1)))
in ((pats1), (vars1), (uu____8603)))
in (FStar_SMTEncoding_Term.mkForall uu____8597 phi1.FStar_Syntax_Syntax.pos))
in ((tm), (decls)))
end));
)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____8615 = (encode_q_body env vars pats body)
in (match (uu____8615) with
| (vars1, pats1, guard, body1, decls) -> begin
(

let uu____8640 = (

let uu____8641 = (

let uu____8647 = (FStar_SMTEncoding_Util.mkAnd ((guard), (body1)))
in ((pats1), (vars1), (uu____8647)))
in (FStar_SMTEncoding_Term.mkExists uu____8641 phi1.FStar_Syntax_Syntax.pos))
in ((uu____8640), (decls)))
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

let uu____8726 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____8726) with
| (asym, a) -> begin
(

let uu____8731 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____8731) with
| (xsym, x) -> begin
(

let uu____8736 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____8736) with
| (ysym, y) -> begin
(

let quant = (fun vars body x1 -> (

let xname_decl = (

let uu____8766 = (

let uu____8772 = (FStar_All.pipe_right vars (FStar_List.map FStar_Pervasives_Native.snd))
in ((x1), (uu____8772), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____8766))
in (

let xtok = (Prims.strcat x1 "@tok")
in (

let xtok_decl = FStar_SMTEncoding_Term.DeclFun (((xtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let xapp = (

let uu____8787 = (

let uu____8791 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((x1), (uu____8791)))
in (FStar_SMTEncoding_Util.mkApp uu____8787))
in (

let xtok1 = (FStar_SMTEncoding_Util.mkApp ((xtok), ([])))
in (

let xtok_app = (mk_Apply xtok1 vars)
in (

let uu____8799 = (

let uu____8801 = (

let uu____8803 = (

let uu____8805 = (

let uu____8806 = (

let uu____8810 = (

let uu____8811 = (

let uu____8817 = (FStar_SMTEncoding_Util.mkEq ((xapp), (body)))
in ((((xapp)::[])::[]), (vars), (uu____8817)))
in (FStar_SMTEncoding_Util.mkForall uu____8811))
in ((uu____8810), (FStar_Pervasives_Native.None), ((Prims.strcat "primitive_" x1))))
in (FStar_SMTEncoding_Util.mkAssume uu____8806))
in (

let uu____8826 = (

let uu____8828 = (

let uu____8829 = (

let uu____8833 = (

let uu____8834 = (

let uu____8840 = (FStar_SMTEncoding_Util.mkEq ((xtok_app), (xapp)))
in ((((xtok_app)::[])::[]), (vars), (uu____8840)))
in (FStar_SMTEncoding_Util.mkForall uu____8834))
in ((uu____8833), (FStar_Pervasives_Native.Some ("Name-token correspondence")), ((Prims.strcat "token_correspondence_" x1))))
in (FStar_SMTEncoding_Util.mkAssume uu____8829))
in (uu____8828)::[])
in (uu____8805)::uu____8826))
in (xtok_decl)::uu____8803)
in (xname_decl)::uu____8801)
in ((xtok1), (uu____8799))))))))))
in (

let axy = (((asym), (FStar_SMTEncoding_Term.Term_sort)))::(((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let xy = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let qx = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let prims1 = (

let uu____8889 = (

let uu____8897 = (

let uu____8903 = (

let uu____8904 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____8904))
in (quant axy uu____8903))
in ((FStar_Parser_Const.op_Eq), (uu____8897)))
in (

let uu____8910 = (

let uu____8919 = (

let uu____8927 = (

let uu____8933 = (

let uu____8934 = (

let uu____8935 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_SMTEncoding_Util.mkNot uu____8935))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____8934))
in (quant axy uu____8933))
in ((FStar_Parser_Const.op_notEq), (uu____8927)))
in (

let uu____8941 = (

let uu____8950 = (

let uu____8958 = (

let uu____8964 = (

let uu____8965 = (

let uu____8966 = (

let uu____8969 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____8970 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____8969), (uu____8970))))
in (FStar_SMTEncoding_Util.mkLT uu____8966))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____8965))
in (quant xy uu____8964))
in ((FStar_Parser_Const.op_LT), (uu____8958)))
in (

let uu____8976 = (

let uu____8985 = (

let uu____8993 = (

let uu____8999 = (

let uu____9000 = (

let uu____9001 = (

let uu____9004 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____9005 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____9004), (uu____9005))))
in (FStar_SMTEncoding_Util.mkLTE uu____9001))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____9000))
in (quant xy uu____8999))
in ((FStar_Parser_Const.op_LTE), (uu____8993)))
in (

let uu____9011 = (

let uu____9020 = (

let uu____9028 = (

let uu____9034 = (

let uu____9035 = (

let uu____9036 = (

let uu____9039 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____9040 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____9039), (uu____9040))))
in (FStar_SMTEncoding_Util.mkGT uu____9036))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____9035))
in (quant xy uu____9034))
in ((FStar_Parser_Const.op_GT), (uu____9028)))
in (

let uu____9046 = (

let uu____9055 = (

let uu____9063 = (

let uu____9069 = (

let uu____9070 = (

let uu____9071 = (

let uu____9074 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____9075 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____9074), (uu____9075))))
in (FStar_SMTEncoding_Util.mkGTE uu____9071))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____9070))
in (quant xy uu____9069))
in ((FStar_Parser_Const.op_GTE), (uu____9063)))
in (

let uu____9081 = (

let uu____9090 = (

let uu____9098 = (

let uu____9104 = (

let uu____9105 = (

let uu____9106 = (

let uu____9109 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____9110 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____9109), (uu____9110))))
in (FStar_SMTEncoding_Util.mkSub uu____9106))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____9105))
in (quant xy uu____9104))
in ((FStar_Parser_Const.op_Subtraction), (uu____9098)))
in (

let uu____9116 = (

let uu____9125 = (

let uu____9133 = (

let uu____9139 = (

let uu____9140 = (

let uu____9141 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Util.mkMinus uu____9141))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____9140))
in (quant qx uu____9139))
in ((FStar_Parser_Const.op_Minus), (uu____9133)))
in (

let uu____9147 = (

let uu____9156 = (

let uu____9164 = (

let uu____9170 = (

let uu____9171 = (

let uu____9172 = (

let uu____9175 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____9176 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____9175), (uu____9176))))
in (FStar_SMTEncoding_Util.mkAdd uu____9172))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____9171))
in (quant xy uu____9170))
in ((FStar_Parser_Const.op_Addition), (uu____9164)))
in (

let uu____9182 = (

let uu____9191 = (

let uu____9199 = (

let uu____9205 = (

let uu____9206 = (

let uu____9207 = (

let uu____9210 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____9211 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____9210), (uu____9211))))
in (FStar_SMTEncoding_Util.mkMul uu____9207))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____9206))
in (quant xy uu____9205))
in ((FStar_Parser_Const.op_Multiply), (uu____9199)))
in (

let uu____9217 = (

let uu____9226 = (

let uu____9234 = (

let uu____9240 = (

let uu____9241 = (

let uu____9242 = (

let uu____9245 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____9246 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____9245), (uu____9246))))
in (FStar_SMTEncoding_Util.mkDiv uu____9242))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____9241))
in (quant xy uu____9240))
in ((FStar_Parser_Const.op_Division), (uu____9234)))
in (

let uu____9252 = (

let uu____9261 = (

let uu____9269 = (

let uu____9275 = (

let uu____9276 = (

let uu____9277 = (

let uu____9280 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____9281 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____9280), (uu____9281))))
in (FStar_SMTEncoding_Util.mkMod uu____9277))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____9276))
in (quant xy uu____9275))
in ((FStar_Parser_Const.op_Modulus), (uu____9269)))
in (

let uu____9287 = (

let uu____9296 = (

let uu____9304 = (

let uu____9310 = (

let uu____9311 = (

let uu____9312 = (

let uu____9315 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____9316 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____9315), (uu____9316))))
in (FStar_SMTEncoding_Util.mkAnd uu____9312))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____9311))
in (quant xy uu____9310))
in ((FStar_Parser_Const.op_And), (uu____9304)))
in (

let uu____9322 = (

let uu____9331 = (

let uu____9339 = (

let uu____9345 = (

let uu____9346 = (

let uu____9347 = (

let uu____9350 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____9351 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____9350), (uu____9351))))
in (FStar_SMTEncoding_Util.mkOr uu____9347))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____9346))
in (quant xy uu____9345))
in ((FStar_Parser_Const.op_Or), (uu____9339)))
in (

let uu____9357 = (

let uu____9366 = (

let uu____9374 = (

let uu____9380 = (

let uu____9381 = (

let uu____9382 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Util.mkNot uu____9382))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____9381))
in (quant qx uu____9380))
in ((FStar_Parser_Const.op_Negation), (uu____9374)))
in (uu____9366)::[])
in (uu____9331)::uu____9357))
in (uu____9296)::uu____9322))
in (uu____9261)::uu____9287))
in (uu____9226)::uu____9252))
in (uu____9191)::uu____9217))
in (uu____9156)::uu____9182))
in (uu____9125)::uu____9147))
in (uu____9090)::uu____9116))
in (uu____9055)::uu____9081))
in (uu____9020)::uu____9046))
in (uu____8985)::uu____9011))
in (uu____8950)::uu____8976))
in (uu____8919)::uu____8941))
in (uu____8889)::uu____8910))
in (

let mk1 = (fun l v1 -> (

let uu____9510 = (

let uu____9515 = (FStar_All.pipe_right prims1 (FStar_List.find (fun uu____9550 -> (match (uu____9550) with
| (l', uu____9559) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right uu____9515 (FStar_Option.map (fun uu____9595 -> (match (uu____9595) with
| (uu____9606, b) -> begin
(b v1)
end)))))
in (FStar_All.pipe_right uu____9510 FStar_Option.get)))
in (

let is = (fun l -> (FStar_All.pipe_right prims1 (FStar_Util.for_some (fun uu____9650 -> (match (uu____9650) with
| (l', uu____9659) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk1; is = is})))))))
end))
end))
end))


let pretype_axiom : env_t  ->  FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun env tapp vars -> (

let uu____9688 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____9688) with
| (xxsym, xx) -> begin
(

let uu____9693 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____9693) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let tapp_hash = (FStar_SMTEncoding_Term.hash_of_term tapp)
in (

let module_name = env.current_module_name
in (

let uu____9701 = (

let uu____9705 = (

let uu____9706 = (

let uu____9712 = (

let uu____9713 = (

let uu____9716 = (

let uu____9717 = (

let uu____9720 = (FStar_SMTEncoding_Util.mkApp (("PreType"), ((xx)::[])))
in ((tapp), (uu____9720)))
in (FStar_SMTEncoding_Util.mkEq uu____9717))
in ((xx_has_type), (uu____9716)))
in (FStar_SMTEncoding_Util.mkImp uu____9713))
in ((((xx_has_type)::[])::[]), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars), (uu____9712)))
in (FStar_SMTEncoding_Util.mkForall uu____9706))
in (

let uu____9733 = (

let uu____9734 = (

let uu____9735 = (

let uu____9736 = (FStar_Util.digest_of_string tapp_hash)
in (Prims.strcat "_pretyping_" uu____9736))
in (Prims.strcat module_name uu____9735))
in (varops.mk_unique uu____9734))
in ((uu____9705), (FStar_Pervasives_Native.Some ("pretyping")), (uu____9733))))
in (FStar_SMTEncoding_Util.mkAssume uu____9701)))))
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

let uu____9770 = (

let uu____9771 = (

let uu____9775 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in ((uu____9775), (FStar_Pervasives_Native.Some ("unit typing")), ("unit_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____9771))
in (

let uu____9777 = (

let uu____9779 = (

let uu____9780 = (

let uu____9784 = (

let uu____9785 = (

let uu____9791 = (

let uu____9792 = (

let uu____9795 = (FStar_SMTEncoding_Util.mkEq ((x), (FStar_SMTEncoding_Term.mk_Term_unit)))
in ((typing_pred), (uu____9795)))
in (FStar_SMTEncoding_Util.mkImp uu____9792))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____9791)))
in (mkForall_fuel uu____9785))
in ((uu____9784), (FStar_Pervasives_Native.Some ("unit inversion")), ("unit_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____9780))
in (uu____9779)::[])
in (uu____9770)::uu____9777))))
in (

let mk_bool = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Bool_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____9823 = (

let uu____9824 = (

let uu____9828 = (

let uu____9829 = (

let uu____9835 = (

let uu____9838 = (

let uu____9840 = (FStar_SMTEncoding_Term.boxBool b)
in (uu____9840)::[])
in (uu____9838)::[])
in (

let uu____9843 = (

let uu____9844 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType uu____9844 tt))
in ((uu____9835), ((bb)::[]), (uu____9843))))
in (FStar_SMTEncoding_Util.mkForall uu____9829))
in ((uu____9828), (FStar_Pervasives_Native.Some ("bool typing")), ("bool_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____9824))
in (

let uu____9855 = (

let uu____9857 = (

let uu____9858 = (

let uu____9862 = (

let uu____9863 = (

let uu____9869 = (

let uu____9870 = (

let uu____9873 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in ((typing_pred), (uu____9873)))
in (FStar_SMTEncoding_Util.mkImp uu____9870))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____9869)))
in (mkForall_fuel uu____9863))
in ((uu____9862), (FStar_Pervasives_Native.Some ("bool inversion")), ("bool_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____9858))
in (uu____9857)::[])
in (uu____9823)::uu____9855))))))
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

let uu____9907 = (

let uu____9908 = (

let uu____9912 = (

let uu____9914 = (

let uu____9916 = (

let uu____9918 = (FStar_SMTEncoding_Term.boxInt a)
in (

let uu____9919 = (

let uu____9921 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____9921)::[])
in (uu____9918)::uu____9919))
in (tt)::uu____9916)
in (tt)::uu____9914)
in (("Prims.Precedes"), (uu____9912)))
in (FStar_SMTEncoding_Util.mkApp uu____9908))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____9907))
in (

let precedes_y_x = (

let uu____9924 = (FStar_SMTEncoding_Util.mkApp (("Precedes"), ((y)::(x)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____9924))
in (

let uu____9926 = (

let uu____9927 = (

let uu____9931 = (

let uu____9932 = (

let uu____9938 = (

let uu____9941 = (

let uu____9943 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____9943)::[])
in (uu____9941)::[])
in (

let uu____9946 = (

let uu____9947 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType uu____9947 tt))
in ((uu____9938), ((bb)::[]), (uu____9946))))
in (FStar_SMTEncoding_Util.mkForall uu____9932))
in ((uu____9931), (FStar_Pervasives_Native.Some ("int typing")), ("int_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____9927))
in (

let uu____9958 = (

let uu____9960 = (

let uu____9961 = (

let uu____9965 = (

let uu____9966 = (

let uu____9972 = (

let uu____9973 = (

let uu____9976 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in ((typing_pred), (uu____9976)))
in (FStar_SMTEncoding_Util.mkImp uu____9973))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____9972)))
in (mkForall_fuel uu____9966))
in ((uu____9965), (FStar_Pervasives_Native.Some ("int inversion")), ("int_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____9961))
in (

let uu____9989 = (

let uu____9991 = (

let uu____9992 = (

let uu____9996 = (

let uu____9997 = (

let uu____10003 = (

let uu____10004 = (

let uu____10007 = (

let uu____10008 = (

let uu____10010 = (

let uu____10012 = (

let uu____10014 = (

let uu____10015 = (

let uu____10018 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____10019 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____10018), (uu____10019))))
in (FStar_SMTEncoding_Util.mkGT uu____10015))
in (

let uu____10020 = (

let uu____10022 = (

let uu____10023 = (

let uu____10026 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____10027 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____10026), (uu____10027))))
in (FStar_SMTEncoding_Util.mkGTE uu____10023))
in (

let uu____10028 = (

let uu____10030 = (

let uu____10031 = (

let uu____10034 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____10035 = (FStar_SMTEncoding_Term.unboxInt x)
in ((uu____10034), (uu____10035))))
in (FStar_SMTEncoding_Util.mkLT uu____10031))
in (uu____10030)::[])
in (uu____10022)::uu____10028))
in (uu____10014)::uu____10020))
in (typing_pred_y)::uu____10012)
in (typing_pred)::uu____10010)
in (FStar_SMTEncoding_Util.mk_and_l uu____10008))
in ((uu____10007), (precedes_y_x)))
in (FStar_SMTEncoding_Util.mkImp uu____10004))
in ((((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[]), ((xx)::(yy)::[]), (uu____10003)))
in (mkForall_fuel uu____9997))
in ((uu____9996), (FStar_Pervasives_Native.Some ("well-founded ordering on nat (alt)")), ("well-founded-ordering-on-nat")))
in (FStar_SMTEncoding_Util.mkAssume uu____9992))
in (uu____9991)::[])
in (uu____9960)::uu____9989))
in (uu____9926)::uu____9958)))))))))))
in (

let mk_str = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.String_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____10065 = (

let uu____10066 = (

let uu____10070 = (

let uu____10071 = (

let uu____10077 = (

let uu____10080 = (

let uu____10082 = (FStar_SMTEncoding_Term.boxString b)
in (uu____10082)::[])
in (uu____10080)::[])
in (

let uu____10085 = (

let uu____10086 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType uu____10086 tt))
in ((uu____10077), ((bb)::[]), (uu____10085))))
in (FStar_SMTEncoding_Util.mkForall uu____10071))
in ((uu____10070), (FStar_Pervasives_Native.Some ("string typing")), ("string_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____10066))
in (

let uu____10097 = (

let uu____10099 = (

let uu____10100 = (

let uu____10104 = (

let uu____10105 = (

let uu____10111 = (

let uu____10112 = (

let uu____10115 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in ((typing_pred), (uu____10115)))
in (FStar_SMTEncoding_Util.mkImp uu____10112))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____10111)))
in (mkForall_fuel uu____10105))
in ((uu____10104), (FStar_Pervasives_Native.Some ("string inversion")), ("string_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____10100))
in (uu____10099)::[])
in (uu____10065)::uu____10097))))))
in (

let mk_ref1 = (fun env reft_name uu____10137 -> (

let r = (("r"), (FStar_SMTEncoding_Term.Ref_sort))
in (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let refa = (

let uu____10148 = (

let uu____10152 = (

let uu____10154 = (FStar_SMTEncoding_Util.mkFreeV aa)
in (uu____10154)::[])
in ((reft_name), (uu____10152)))
in (FStar_SMTEncoding_Util.mkApp uu____10148))
in (

let refb = (

let uu____10157 = (

let uu____10161 = (

let uu____10163 = (FStar_SMTEncoding_Util.mkFreeV bb)
in (uu____10163)::[])
in ((reft_name), (uu____10161)))
in (FStar_SMTEncoding_Util.mkApp uu____10157))
in (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (

let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (

let uu____10167 = (

let uu____10168 = (

let uu____10172 = (

let uu____10173 = (

let uu____10179 = (

let uu____10180 = (

let uu____10183 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in ((typing_pred), (uu____10183)))
in (FStar_SMTEncoding_Util.mkImp uu____10180))
in ((((typing_pred)::[])::[]), ((xx)::(aa)::[]), (uu____10179)))
in (mkForall_fuel uu____10173))
in ((uu____10172), (FStar_Pervasives_Native.Some ("ref inversion")), ("ref_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____10168))
in (uu____10167)::[])))))))))
in (

let mk_true_interp = (fun env nm true_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((true_tm)::[])))
in ((FStar_SMTEncoding_Util.mkAssume ((valid), (FStar_Pervasives_Native.Some ("True interpretation")), ("true_interp"))))::[]))
in (

let mk_false_interp = (fun env nm false_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((false_tm)::[])))
in (

let uu____10223 = (

let uu____10224 = (

let uu____10228 = (FStar_SMTEncoding_Util.mkIff ((FStar_SMTEncoding_Util.mkFalse), (valid)))
in ((uu____10228), (FStar_Pervasives_Native.Some ("False interpretation")), ("false_interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____10224))
in (uu____10223)::[])))
in (

let mk_and_interp = (fun env conj uu____10239 -> (

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

let uu____10256 = (

let uu____10257 = (

let uu____10261 = (

let uu____10262 = (

let uu____10268 = (

let uu____10269 = (

let uu____10272 = (FStar_SMTEncoding_Util.mkAnd ((valid_a), (valid_b)))
in ((uu____10272), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____10269))
in ((((l_and_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____10268)))
in (FStar_SMTEncoding_Util.mkForall uu____10262))
in ((uu____10261), (FStar_Pervasives_Native.Some ("/\\ interpretation")), ("l_and-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____10257))
in (uu____10256)::[]))))))))))
in (

let mk_or_interp = (fun env disj uu____10296 -> (

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

let uu____10313 = (

let uu____10314 = (

let uu____10318 = (

let uu____10319 = (

let uu____10325 = (

let uu____10326 = (

let uu____10329 = (FStar_SMTEncoding_Util.mkOr ((valid_a), (valid_b)))
in ((uu____10329), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____10326))
in ((((l_or_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____10325)))
in (FStar_SMTEncoding_Util.mkForall uu____10319))
in ((uu____10318), (FStar_Pervasives_Native.Some ("\\/ interpretation")), ("l_or-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____10314))
in (uu____10313)::[]))))))))))
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

let uu____10370 = (

let uu____10371 = (

let uu____10375 = (

let uu____10376 = (

let uu____10382 = (

let uu____10383 = (

let uu____10386 = (FStar_SMTEncoding_Util.mkEq ((x1), (y1)))
in ((uu____10386), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____10383))
in ((((eq2_x_y)::[])::[]), ((aa)::(xx1)::(yy1)::[]), (uu____10382)))
in (FStar_SMTEncoding_Util.mkForall uu____10376))
in ((uu____10375), (FStar_Pervasives_Native.Some ("Eq2 interpretation")), ("eq2-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____10371))
in (uu____10370)::[]))))))))))
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

let uu____10433 = (

let uu____10434 = (

let uu____10438 = (

let uu____10439 = (

let uu____10445 = (

let uu____10446 = (

let uu____10449 = (FStar_SMTEncoding_Util.mkEq ((x1), (y1)))
in ((uu____10449), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____10446))
in ((((eq3_x_y)::[])::[]), ((aa)::(bb)::(xx1)::(yy1)::[]), (uu____10445)))
in (FStar_SMTEncoding_Util.mkForall uu____10439))
in ((uu____10438), (FStar_Pervasives_Native.Some ("Eq3 interpretation")), ("eq3-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____10434))
in (uu____10433)::[]))))))))))))
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

let uu____10494 = (

let uu____10495 = (

let uu____10499 = (

let uu____10500 = (

let uu____10506 = (

let uu____10507 = (

let uu____10510 = (FStar_SMTEncoding_Util.mkImp ((valid_a), (valid_b)))
in ((uu____10510), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____10507))
in ((((l_imp_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____10506)))
in (FStar_SMTEncoding_Util.mkForall uu____10500))
in ((uu____10499), (FStar_Pervasives_Native.Some ("==> interpretation")), ("l_imp-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____10495))
in (uu____10494)::[]))))))))))
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

let uu____10551 = (

let uu____10552 = (

let uu____10556 = (

let uu____10557 = (

let uu____10563 = (

let uu____10564 = (

let uu____10567 = (FStar_SMTEncoding_Util.mkIff ((valid_a), (valid_b)))
in ((uu____10567), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____10564))
in ((((l_iff_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____10563)))
in (FStar_SMTEncoding_Util.mkForall uu____10557))
in ((uu____10556), (FStar_Pervasives_Native.Some ("<==> interpretation")), ("l_iff-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____10552))
in (uu____10551)::[]))))))))))
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

let uu____10601 = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____10601))
in (

let uu____10603 = (

let uu____10604 = (

let uu____10608 = (

let uu____10609 = (

let uu____10615 = (FStar_SMTEncoding_Util.mkIff ((not_valid_a), (valid)))
in ((((l_not_a)::[])::[]), ((aa)::[]), (uu____10615)))
in (FStar_SMTEncoding_Util.mkForall uu____10609))
in ((uu____10608), (FStar_Pervasives_Native.Some ("not interpretation")), ("l_not-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____10604))
in (uu____10603)::[])))))))
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

let uu____10655 = (

let uu____10659 = (

let uu____10661 = (FStar_SMTEncoding_Util.mk_ApplyTT b x1)
in (uu____10661)::[])
in (("Valid"), (uu____10659)))
in (FStar_SMTEncoding_Util.mkApp uu____10655))
in (

let uu____10663 = (

let uu____10664 = (

let uu____10668 = (

let uu____10669 = (

let uu____10675 = (

let uu____10676 = (

let uu____10679 = (

let uu____10680 = (

let uu____10686 = (

let uu____10689 = (

let uu____10691 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in (uu____10691)::[])
in (uu____10689)::[])
in (

let uu____10694 = (

let uu____10695 = (

let uu____10698 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in ((uu____10698), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp uu____10695))
in ((uu____10686), ((xx1)::[]), (uu____10694))))
in (FStar_SMTEncoding_Util.mkForall uu____10680))
in ((uu____10679), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____10676))
in ((((l_forall_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____10675)))
in (FStar_SMTEncoding_Util.mkForall uu____10669))
in ((uu____10668), (FStar_Pervasives_Native.Some ("forall interpretation")), ("forall-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____10664))
in (uu____10663)::[])))))))))))
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

let uu____10749 = (

let uu____10753 = (

let uu____10755 = (FStar_SMTEncoding_Util.mk_ApplyTT b x1)
in (uu____10755)::[])
in (("Valid"), (uu____10753)))
in (FStar_SMTEncoding_Util.mkApp uu____10749))
in (

let uu____10757 = (

let uu____10758 = (

let uu____10762 = (

let uu____10763 = (

let uu____10769 = (

let uu____10770 = (

let uu____10773 = (

let uu____10774 = (

let uu____10780 = (

let uu____10783 = (

let uu____10785 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in (uu____10785)::[])
in (uu____10783)::[])
in (

let uu____10788 = (

let uu____10789 = (

let uu____10792 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in ((uu____10792), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp uu____10789))
in ((uu____10780), ((xx1)::[]), (uu____10788))))
in (FStar_SMTEncoding_Util.mkExists uu____10774))
in ((uu____10773), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____10770))
in ((((l_exists_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____10769)))
in (FStar_SMTEncoding_Util.mkForall uu____10763))
in ((uu____10762), (FStar_Pervasives_Native.Some ("exists interpretation")), ("exists-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____10758))
in (uu____10757)::[])))))))))))
in (

let mk_range_interp = (fun env range tt -> (

let range_ty = (FStar_SMTEncoding_Util.mkApp ((range), ([])))
in (

let uu____10828 = (

let uu____10829 = (

let uu____10833 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_ty)
in (

let uu____10834 = (varops.mk_unique "typing_range_const")
in ((uu____10833), (FStar_Pervasives_Native.Some ("Range_const typing")), (uu____10834))))
in (FStar_SMTEncoding_Util.mkAssume uu____10829))
in (uu____10828)::[])))
in (

let prims1 = (((FStar_Parser_Const.unit_lid), (mk_unit)))::(((FStar_Parser_Const.bool_lid), (mk_bool)))::(((FStar_Parser_Const.int_lid), (mk_int)))::(((FStar_Parser_Const.string_lid), (mk_str)))::(((FStar_Parser_Const.ref_lid), (mk_ref1)))::(((FStar_Parser_Const.true_lid), (mk_true_interp)))::(((FStar_Parser_Const.false_lid), (mk_false_interp)))::(((FStar_Parser_Const.and_lid), (mk_and_interp)))::(((FStar_Parser_Const.or_lid), (mk_or_interp)))::(((FStar_Parser_Const.eq2_lid), (mk_eq2_interp)))::(((FStar_Parser_Const.eq3_lid), (mk_eq3_interp)))::(((FStar_Parser_Const.imp_lid), (mk_imp_interp)))::(((FStar_Parser_Const.iff_lid), (mk_iff_interp)))::(((FStar_Parser_Const.not_lid), (mk_not_interp)))::(((FStar_Parser_Const.forall_lid), (mk_forall_interp)))::(((FStar_Parser_Const.exists_lid), (mk_exists_interp)))::(((FStar_Parser_Const.range_lid), (mk_range_interp)))::[]
in (fun env t s tt -> (

let uu____11096 = (FStar_Util.find_opt (fun uu____11117 -> (match (uu____11117) with
| (l, uu____11127) -> begin
(FStar_Ident.lid_equals l t)
end)) prims1)
in (match (uu____11096) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (uu____11149, f) -> begin
(f env s tt)
end)))))))))))))))))))))))))


let encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____11185 = (encode_function_type_as_formula t env)
in (match (uu____11185) with
| (form, decls) -> begin
(FStar_List.append decls (((FStar_SMTEncoding_Util.mkAssume ((form), (FStar_Pervasives_Native.Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str))), ((Prims.strcat "lemma_" lid.FStar_Ident.str)))))::[]))
end))))


let encode_free_var : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env fv tt t_norm quals -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____11218 = ((

let uu____11221 = ((FStar_Syntax_Util.is_pure_or_ghost_function t_norm) || (FStar_TypeChecker_Env.is_reifiable_function env.tcenv t_norm))
in (FStar_All.pipe_left Prims.op_Negation uu____11221)) || (FStar_Syntax_Util.is_lemma t_norm))
in (match (uu____11218) with
| true -> begin
(

let uu____11225 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____11225) with
| (vname, vtok, env1) -> begin
(

let arg_sorts = (

let uu____11237 = (

let uu____11238 = (FStar_Syntax_Subst.compress t_norm)
in uu____11238.FStar_Syntax_Syntax.n)
in (match (uu____11237) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____11243) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun uu____11261 -> FStar_SMTEncoding_Term.Term_sort)))
end
| uu____11264 -> begin
[]
end))
in (

let d = FStar_SMTEncoding_Term.DeclFun (((vname), (arg_sorts), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Uninterpreted function symbol for impure function"))))
in (

let dd = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Uninterpreted name for impure function"))))
in (((d)::(dd)::[]), (env1)))))
end))
end
| uu____11272 -> begin
(

let uu____11273 = (prims.is lid)
in (match (uu____11273) with
| true -> begin
(

let vname = (varops.new_fvar lid)
in (

let uu____11278 = (prims.mk lid vname)
in (match (uu____11278) with
| (tok, definition) -> begin
(

let env1 = (push_free_var env lid vname (FStar_Pervasives_Native.Some (tok)))
in ((definition), (env1)))
end)))
end
| uu____11291 -> begin
(

let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (

let uu____11293 = (

let uu____11299 = (curried_arrow_formals_comp t_norm)
in (match (uu____11299) with
| (args, comp) -> begin
(

let comp1 = (

let uu____11310 = (FStar_TypeChecker_Env.is_reifiable_comp env.tcenv comp)
in (match (uu____11310) with
| true -> begin
(

let uu____11311 = (FStar_TypeChecker_Env.reify_comp (

let uu___143_11314 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___143_11314.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___143_11314.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___143_11314.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___143_11314.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___143_11314.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___143_11314.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___143_11314.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___143_11314.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___143_11314.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___143_11314.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___143_11314.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___143_11314.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___143_11314.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___143_11314.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___143_11314.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___143_11314.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___143_11314.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___143_11314.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___143_11314.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___143_11314.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___143_11314.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___143_11314.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___143_11314.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___143_11314.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___143_11314.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___143_11314.FStar_TypeChecker_Env.is_native_tactic}) comp FStar_Syntax_Syntax.U_unknown)
in (FStar_Syntax_Syntax.mk_Total uu____11311))
end
| uu____11315 -> begin
comp
end))
in (match (encode_non_total_function_typ) with
| true -> begin
(

let uu____11321 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp1)
in ((args), (uu____11321)))
end
| uu____11328 -> begin
((args), (((FStar_Pervasives_Native.None), ((FStar_Syntax_Util.comp_result comp1)))))
end))
end))
in (match (uu____11293) with
| (formals, (pre_opt, res_t)) -> begin
(

let uu____11348 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____11348) with
| (vname, vtok, env1) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
end
| uu____11361 -> begin
(FStar_SMTEncoding_Util.mkApp ((vtok), ([])))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun uu___115_11393 -> (match (uu___115_11393) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(

let uu____11396 = (FStar_Util.prefix vars)
in (match (uu____11396) with
| (uu____11407, (xxsym, uu____11409)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____11419 = (

let uu____11420 = (

let uu____11424 = (

let uu____11425 = (

let uu____11431 = (

let uu____11432 = (

let uu____11435 = (

let uu____11436 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____11436))
in ((vapp), (uu____11435)))
in (FStar_SMTEncoding_Util.mkEq uu____11432))
in ((((vapp)::[])::[]), (vars), (uu____11431)))
in (FStar_SMTEncoding_Util.mkForall uu____11425))
in ((uu____11424), (FStar_Pervasives_Native.Some ("Discriminator equation")), ((Prims.strcat "disc_equation_" (escape d.FStar_Ident.str)))))
in (FStar_SMTEncoding_Util.mkAssume uu____11420))
in (uu____11419)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(

let uu____11447 = (FStar_Util.prefix vars)
in (match (uu____11447) with
| (uu____11458, (xxsym, uu____11460)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f1 = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (

let tp_name = (mk_term_projector_name d f1)
in (

let prim_app = (FStar_SMTEncoding_Util.mkApp ((tp_name), ((xx)::[])))
in (

let uu____11474 = (

let uu____11475 = (

let uu____11479 = (

let uu____11480 = (

let uu____11486 = (FStar_SMTEncoding_Util.mkEq ((vapp), (prim_app)))
in ((((vapp)::[])::[]), (vars), (uu____11486)))
in (FStar_SMTEncoding_Util.mkForall uu____11480))
in ((uu____11479), (FStar_Pervasives_Native.Some ("Projector equation")), ((Prims.strcat "proj_equation_" tp_name))))
in (FStar_SMTEncoding_Util.mkAssume uu____11475))
in (uu____11474)::[])))))
end))
end
| uu____11495 -> begin
[]
end)))))
in (

let uu____11496 = (encode_binders FStar_Pervasives_Native.None formals env1)
in (match (uu____11496) with
| (vars, guards, env', decls1, uu____11512) -> begin
(

let uu____11519 = (match (pre_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____11524 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____11524), (decls1)))
end
| FStar_Pervasives_Native.Some (p) -> begin
(

let uu____11526 = (encode_formula p env')
in (match (uu____11526) with
| (g, ds) -> begin
(

let uu____11533 = (FStar_SMTEncoding_Util.mk_and_l ((g)::guards))
in ((uu____11533), ((FStar_List.append decls1 ds))))
end))
end)
in (match (uu____11519) with
| (guard, decls11) -> begin
(

let vtok_app = (mk_Apply vtok_tm vars)
in (

let vapp = (

let uu____11542 = (

let uu____11546 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((vname), (uu____11546)))
in (FStar_SMTEncoding_Util.mkApp uu____11542))
in (

let uu____11551 = (

let vname_decl = (

let uu____11556 = (

let uu____11562 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____11568 -> FStar_SMTEncoding_Term.Term_sort)))
in ((vname), (uu____11562), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____11556))
in (

let uu____11573 = (

let env2 = (

let uu___144_11577 = env1
in {bindings = uu___144_11577.bindings; depth = uu___144_11577.depth; tcenv = uu___144_11577.tcenv; warn = uu___144_11577.warn; cache = uu___144_11577.cache; nolabels = uu___144_11577.nolabels; use_zfuel_name = uu___144_11577.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = uu___144_11577.current_module_name})
in (

let uu____11578 = (

let uu____11579 = (head_normal env2 tt)
in (not (uu____11579)))
in (match (uu____11578) with
| true -> begin
(encode_term_pred FStar_Pervasives_Native.None tt env2 vtok_tm)
end
| uu____11582 -> begin
(encode_term_pred FStar_Pervasives_Native.None t_norm env2 vtok_tm)
end)))
in (match (uu____11573) with
| (tok_typing, decls2) -> begin
(

let tok_typing1 = (match (formals) with
| (uu____11589)::uu____11590 -> begin
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

let uu____11613 = (

let uu____11619 = (FStar_SMTEncoding_Term.mk_NoHoist f tok_typing)
in ((((vtok_app_l)::[])::((vtok_app_r)::[])::[]), ((ff)::[]), (uu____11619)))
in (FStar_SMTEncoding_Util.mkForall uu____11613))
in (FStar_SMTEncoding_Util.mkAssume ((guarded_tok_typing), (FStar_Pervasives_Native.Some ("function token typing")), ((Prims.strcat "function_token_typing_" vname)))))))))
end
| uu____11633 -> begin
(FStar_SMTEncoding_Util.mkAssume ((tok_typing), (FStar_Pervasives_Native.Some ("function token typing")), ((Prims.strcat "function_token_typing_" vname))))
end)
in (

let uu____11635 = (match (formals) with
| [] -> begin
(

let uu____11644 = (

let uu____11645 = (

let uu____11647 = (FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left (fun _0_41 -> FStar_Pervasives_Native.Some (_0_41)) uu____11647))
in (push_free_var env1 lid vname uu____11645))
in (((FStar_List.append decls2 ((tok_typing1)::[]))), (uu____11644)))
end
| uu____11650 -> begin
(

let vtok_decl = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let vtok_fresh = (

let uu____11655 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((vtok), (FStar_SMTEncoding_Term.Term_sort)) uu____11655))
in (

let name_tok_corr = (

let uu____11657 = (

let uu____11661 = (

let uu____11662 = (

let uu____11668 = (FStar_SMTEncoding_Util.mkEq ((vtok_app), (vapp)))
in ((((vtok_app)::[])::((vapp)::[])::[]), (vars), (uu____11668)))
in (FStar_SMTEncoding_Util.mkForall uu____11662))
in ((uu____11661), (FStar_Pervasives_Native.Some ("Name-token correspondence")), ((Prims.strcat "token_correspondence_" vname))))
in (FStar_SMTEncoding_Util.mkAssume uu____11657))
in (((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing1)::[]))), (env1)))))
end)
in (match (uu____11635) with
| (tok_decl, env2) -> begin
(((vname_decl)::tok_decl), (env2))
end)))
end)))
in (match (uu____11551) with
| (decls2, env2) -> begin
(

let uu____11692 = (

let res_t1 = (FStar_Syntax_Subst.compress res_t)
in (

let uu____11697 = (encode_term res_t1 env')
in (match (uu____11697) with
| (encoded_res_t, decls) -> begin
(

let uu____11705 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in ((encoded_res_t), (uu____11705), (decls)))
end)))
in (match (uu____11692) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (

let uu____11713 = (

let uu____11717 = (

let uu____11718 = (

let uu____11724 = (FStar_SMTEncoding_Util.mkImp ((guard), (ty_pred)))
in ((((vapp)::[])::[]), (vars), (uu____11724)))
in (FStar_SMTEncoding_Util.mkForall uu____11718))
in ((uu____11717), (FStar_Pervasives_Native.Some ("free var typing")), ((Prims.strcat "typing_" vname))))
in (FStar_SMTEncoding_Util.mkAssume uu____11713))
in (

let freshness = (

let uu____11733 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New))
in (match (uu____11733) with
| true -> begin
(

let uu____11736 = (

let uu____11737 = (

let uu____11743 = (FStar_All.pipe_right vars (FStar_List.map FStar_Pervasives_Native.snd))
in (

let uu____11749 = (varops.next_id ())
in ((vname), (uu____11743), (FStar_SMTEncoding_Term.Term_sort), (uu____11749))))
in (FStar_SMTEncoding_Term.fresh_constructor uu____11737))
in (

let uu____11751 = (

let uu____11753 = (pretype_axiom env2 vapp vars)
in (uu____11753)::[])
in (uu____11736)::uu____11751))
end
| uu____11754 -> begin
[]
end))
in (

let g = (

let uu____11757 = (

let uu____11759 = (

let uu____11761 = (

let uu____11763 = (

let uu____11765 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::uu____11765)
in (FStar_List.append freshness uu____11763))
in (FStar_List.append decls3 uu____11761))
in (FStar_List.append decls2 uu____11759))
in (FStar_List.append decls11 uu____11757))
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

let uu____11791 = (try_lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____11791) with
| FStar_Pervasives_Native.None -> begin
(

let uu____11810 = (encode_free_var env x t t_norm [])
in (match (uu____11810) with
| (decls, env1) -> begin
(

let uu____11825 = (lookup_lid env1 x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____11825) with
| (n1, x', uu____11840) -> begin
((((n1), (x'))), (decls), (env1))
end))
end))
end
| FStar_Pervasives_Native.Some (n1, x1, uu____11852) -> begin
((((n1), (x1))), ([]), (env))
end)))


let encode_top_level_val : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env lid t quals -> (

let tt = (norm env t)
in (

let uu____11889 = (encode_free_var env lid t tt quals)
in (match (uu____11889) with
| (decls, env1) -> begin
(

let uu____11900 = (FStar_Syntax_Util.is_smt_lemma t)
in (match (uu____11900) with
| true -> begin
(

let uu____11904 = (

let uu____11906 = (encode_smt_lemma env1 lid tt)
in (FStar_List.append decls uu____11906))
in ((uu____11904), (env1)))
end
| uu____11909 -> begin
((decls), (env1))
end))
end))))


let encode_top_level_vals : env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____11944 lb -> (match (uu____11944) with
| (decls, env1) -> begin
(

let uu____11956 = (

let uu____11960 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env1 uu____11960 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (uu____11956) with
| (decls', env2) -> begin
(((FStar_List.append decls decls')), (env2))
end))
end)) (([]), (env)))))


let is_tactic : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let fstar_tactics_tactic_lid = (FStar_Parser_Const.p2l (("FStar")::("Tactics")::("tactic")::[]))
in (

let uu____11975 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____11975) with
| (hd1, args) -> begin
(

let uu____12001 = (

let uu____12002 = (FStar_Syntax_Util.un_uinst hd1)
in uu____12002.FStar_Syntax_Syntax.n)
in (match (uu____12001) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____12006, c) -> begin
(

let effect_name = (FStar_Syntax_Util.comp_effect_name c)
in (FStar_Util.starts_with "FStar.Tactics" effect_name.FStar_Ident.str))
end
| uu____12019 -> begin
false
end))
end))))


let encode_top_level_let : env_t  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env uu____12037 quals -> (match (uu____12037) with
| (is_rec, bindings) -> begin
(

let eta_expand1 = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let uu____12087 = (FStar_Util.first_N nbinders formals)
in (match (uu____12087) with
| (formals1, extra_formals) -> begin
(

let subst1 = (FStar_List.map2 (fun uu____12136 uu____12137 -> (match (((uu____12136), (uu____12137))) with
| ((formal, uu____12147), (binder, uu____12149)) -> begin
(

let uu____12154 = (

let uu____12159 = (FStar_Syntax_Syntax.bv_to_name binder)
in ((formal), (uu____12159)))
in FStar_Syntax_Syntax.NT (uu____12154))
end)) formals1 binders)
in (

let extra_formals1 = (

let uu____12164 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun uu____12182 -> (match (uu____12182) with
| (x, i) -> begin
(

let uu____12189 = (

let uu___145_12190 = x
in (

let uu____12191 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___145_12190.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___145_12190.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____12191}))
in ((uu____12189), (i)))
end))))
in (FStar_All.pipe_right uu____12164 FStar_Syntax_Util.name_binders))
in (

let body1 = (

let uu____12203 = (

let uu____12205 = (

let uu____12206 = (FStar_Syntax_Subst.subst subst1 t)
in uu____12206.FStar_Syntax_Syntax.n)
in (FStar_All.pipe_left (fun _0_42 -> FStar_Pervasives_Native.Some (_0_42)) uu____12205))
in (

let uu____12210 = (

let uu____12211 = (FStar_Syntax_Subst.compress body)
in (

let uu____12212 = (

let uu____12213 = (FStar_Syntax_Util.args_of_binders extra_formals1)
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____12213))
in (FStar_Syntax_Syntax.extend_app_n uu____12211 uu____12212)))
in (uu____12210 uu____12203 body.FStar_Syntax_Syntax.pos)))
in (((FStar_List.append binders extra_formals1)), (body1)))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (

let get_result_type = (fun c -> (

let uu____12255 = (FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c)
in (match (uu____12255) with
| true -> begin
(FStar_TypeChecker_Env.reify_comp (

let uu___146_12258 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___146_12258.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___146_12258.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___146_12258.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___146_12258.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___146_12258.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___146_12258.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___146_12258.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___146_12258.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___146_12258.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___146_12258.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___146_12258.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___146_12258.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___146_12258.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___146_12258.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___146_12258.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___146_12258.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___146_12258.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___146_12258.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___146_12258.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___146_12258.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___146_12258.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___146_12258.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___146_12258.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___146_12258.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___146_12258.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___146_12258.FStar_TypeChecker_Env.is_native_tactic}) c FStar_Syntax_Syntax.U_unknown)
end
| uu____12259 -> begin
(FStar_Syntax_Util.comp_result c)
end)))
in (

let rec aux = (fun norm1 t_norm1 -> (

let uu____12279 = (FStar_Syntax_Util.abs_formals e)
in (match (uu____12279) with
| (binders, body, lopt) -> begin
(match (binders) with
| (uu____12313)::uu____12314 -> begin
(

let uu____12322 = (

let uu____12323 = (FStar_Syntax_Subst.compress t_norm1)
in uu____12323.FStar_Syntax_Syntax.n)
in (match (uu____12322) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____12350 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____12350) with
| (formals1, c1) -> begin
(

let nformals = (FStar_List.length formals1)
in (

let nbinders = (FStar_List.length binders)
in (

let tres = (get_result_type c1)
in (

let uu____12378 = ((nformals < nbinders) && (FStar_Syntax_Util.is_total_comp c1))
in (match (uu____12378) with
| true -> begin
(

let uu____12401 = (FStar_Util.first_N nformals binders)
in (match (uu____12401) with
| (bs0, rest) -> begin
(

let c2 = (

let subst1 = (FStar_List.map2 (fun uu____12456 uu____12457 -> (match (((uu____12456), (uu____12457))) with
| ((x, uu____12467), (b, uu____12469)) -> begin
(

let uu____12474 = (

let uu____12479 = (FStar_Syntax_Syntax.bv_to_name b)
in ((x), (uu____12479)))
in FStar_Syntax_Syntax.NT (uu____12474))
end)) formals1 bs0)
in (FStar_Syntax_Subst.subst_comp subst1 c1))
in (

let body1 = (FStar_Syntax_Util.abs rest body lopt)
in (

let uu____12481 = (

let uu____12492 = (get_result_type c2)
in ((bs0), (body1), (bs0), (uu____12492)))
in ((uu____12481), (false)))))
end))
end
| uu____12509 -> begin
(match ((nformals > nbinders)) with
| true -> begin
(

let uu____12532 = (eta_expand1 binders formals1 body tres)
in (match (uu____12532) with
| (binders1, body1) -> begin
((((binders1), (body1), (formals1), (tres))), (false))
end))
end
| uu____12578 -> begin
((((binders), (body), (formals1), (tres))), (false))
end)
end)))))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____12584) -> begin
(

let uu____12589 = (

let uu____12600 = (aux norm1 x.FStar_Syntax_Syntax.sort)
in (FStar_Pervasives_Native.fst uu____12600))
in ((uu____12589), (true)))
end
| uu____12633 when (not (norm1)) -> begin
(

let t_norm2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm1)
in (aux true t_norm2))
end
| uu____12635 -> begin
(

let uu____12636 = (

let uu____12637 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____12638 = (FStar_Syntax_Print.term_to_string t_norm1)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str uu____12637 uu____12638)))
in (failwith uu____12636))
end))
end
| uu____12651 -> begin
(

let uu____12652 = (

let uu____12653 = (FStar_Syntax_Subst.compress t_norm1)
in uu____12653.FStar_Syntax_Syntax.n)
in (match (uu____12652) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____12680 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____12680) with
| (formals1, c1) -> begin
(

let tres = (get_result_type c1)
in (

let uu____12698 = (eta_expand1 [] formals1 e tres)
in (match (uu____12698) with
| (binders1, body1) -> begin
((((binders1), (body1), (formals1), (tres))), (false))
end)))
end))
end
| uu____12746 -> begin
(((([]), (e), ([]), (t_norm1))), (false))
end))
end)
end)))
in (aux false t_norm))))
in try
(match (()) with
| () -> begin
(

let uu____12776 = (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> ((FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))))
in (match (uu____12776) with
| true -> begin
(encode_top_level_vals env bindings quals)
end
| uu____12783 -> begin
(

let uu____12784 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____12838 lb -> (match (uu____12838) with
| (toks, typs, decls, env1) -> begin
((

let uu____12889 = (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp)
in (match (uu____12889) with
| true -> begin
(FStar_Pervasives.raise Let_rec_unencodeable)
end
| uu____12890 -> begin
()
end));
(

let t_norm = (whnf env1 lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____12892 = (

let uu____12900 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env1 uu____12900 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (uu____12892) with
| (tok, decl, env2) -> begin
(

let uu____12925 = (

let uu____12932 = (

let uu____12938 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in ((uu____12938), (tok)))
in (uu____12932)::toks)
in ((uu____12925), ((t_norm)::typs), ((decl)::decls), (env2)))
end)));
)
end)) (([]), ([]), ([]), (env))))
in (match (uu____12784) with
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
| uu____13040 -> begin
(match (curry) with
| true -> begin
(match (ftok) with
| FStar_Pervasives_Native.Some (ftok1) -> begin
(mk_Apply ftok1 vars)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____13045 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply uu____13045 vars))
end)
end
| uu____13046 -> begin
(

let uu____13047 = (

let uu____13051 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (uu____13051)))
in (FStar_SMTEncoding_Util.mkApp uu____13047))
end)
end))
in (

let uu____13056 = ((FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___116_13059 -> (match (uu___116_13059) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| uu____13060 -> begin
false
end)))) || (FStar_All.pipe_right typs1 (FStar_Util.for_some (fun t -> (

let uu____13065 = ((FStar_Syntax_Util.is_pure_or_ghost_function t) || (FStar_TypeChecker_Env.is_reifiable_function env1.tcenv t))
in (FStar_All.pipe_left Prims.op_Negation uu____13065))))))
in (match (uu____13056) with
| true -> begin
((decls1), (env1))
end
| uu____13070 -> begin
(match ((not (is_rec))) with
| true -> begin
(match (((bindings), (typs1), (toks1))) with
| (({FStar_Syntax_Syntax.lbname = uu____13085; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____13087; FStar_Syntax_Syntax.lbeff = uu____13088; FStar_Syntax_Syntax.lbdef = e})::[], (t_norm)::[], ((flid_fv, (f, ftok)))::[]) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____13125 = (

let uu____13129 = (FStar_TypeChecker_Env.open_universes_in env1.tcenv uvs ((e)::(t_norm)::[]))
in (match (uu____13129) with
| (tcenv', uu____13140, e_t) -> begin
(

let uu____13144 = (match (e_t) with
| (e1)::(t_norm1)::[] -> begin
((e1), (t_norm1))
end
| uu____13151 -> begin
(failwith "Impossible")
end)
in (match (uu____13144) with
| (e1, t_norm1) -> begin
(((

let uu___149_13161 = env1
in {bindings = uu___149_13161.bindings; depth = uu___149_13161.depth; tcenv = tcenv'; warn = uu___149_13161.warn; cache = uu___149_13161.cache; nolabels = uu___149_13161.nolabels; use_zfuel_name = uu___149_13161.use_zfuel_name; encode_non_total_function_typ = uu___149_13161.encode_non_total_function_typ; current_module_name = uu___149_13161.current_module_name})), (e1), (t_norm1))
end))
end))
in (match (uu____13125) with
| (env', e1, t_norm1) -> begin
(

let uu____13168 = (destruct_bound_function flid t_norm1 e1)
in (match (uu____13168) with
| ((binders, body, uu____13180, uu____13181), curry) -> begin
((

let uu____13188 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____13188) with
| true -> begin
(

let uu____13189 = (FStar_Syntax_Print.binders_to_string ", " binders)
in (

let uu____13190 = (FStar_Syntax_Print.term_to_string body)
in (FStar_Util.print2 "Encoding let : binders=[%s], body=%s\n" uu____13189 uu____13190)))
end
| uu____13191 -> begin
()
end));
(

let uu____13192 = (encode_binders FStar_Pervasives_Native.None binders env')
in (match (uu____13192) with
| (vars, guards, env'1, binder_decls, uu____13208) -> begin
(

let body1 = (

let uu____13216 = (FStar_TypeChecker_Env.is_reifiable_function env'1.tcenv t_norm1)
in (match (uu____13216) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env'1.tcenv body)
end
| uu____13217 -> begin
body
end))
in (

let app = (mk_app1 curry f ftok vars)
in (

let uu____13219 = (

let uu____13224 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic))
in (match (uu____13224) with
| true -> begin
(

let uu____13230 = (FStar_SMTEncoding_Term.mk_Valid app)
in (

let uu____13231 = (encode_formula body1 env'1)
in ((uu____13230), (uu____13231))))
end
| uu____13236 -> begin
(

let uu____13237 = (encode_term body1 env'1)
in ((app), (uu____13237)))
end))
in (match (uu____13219) with
| (app1, (body2, decls2)) -> begin
(

let eqn = (

let uu____13251 = (

let uu____13255 = (

let uu____13256 = (

let uu____13262 = (FStar_SMTEncoding_Util.mkEq ((app1), (body2)))
in ((((app1)::[])::[]), (vars), (uu____13262)))
in (FStar_SMTEncoding_Util.mkForall uu____13256))
in (

let uu____13268 = (

let uu____13270 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in FStar_Pervasives_Native.Some (uu____13270))
in ((uu____13255), (uu____13268), ((Prims.strcat "equation_" f)))))
in (FStar_SMTEncoding_Util.mkAssume uu____13251))
in (

let uu____13272 = (

let uu____13274 = (

let uu____13276 = (

let uu____13278 = (

let uu____13280 = (primitive_type_axioms env1.tcenv flid f app1)
in (FStar_List.append ((eqn)::[]) uu____13280))
in (FStar_List.append decls2 uu____13278))
in (FStar_List.append binder_decls uu____13276))
in (FStar_List.append decls1 uu____13274))
in ((uu____13272), (env1))))
end))))
end));
)
end))
end)))
end
| uu____13283 -> begin
(failwith "Impossible")
end)
end
| uu____13298 -> begin
(

let fuel = (

let uu____13302 = (varops.fresh "fuel")
in ((uu____13302), (FStar_SMTEncoding_Term.Fuel_sort)))
in (

let fuel_tm = (FStar_SMTEncoding_Util.mkFreeV fuel)
in (

let env0 = env1
in (

let uu____13305 = (FStar_All.pipe_right toks1 (FStar_List.fold_left (fun uu____13355 uu____13356 -> (match (((uu____13355), (uu____13356))) with
| ((gtoks, env2), (flid_fv, (f, ftok))) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let g = (

let uu____13434 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented")
in (varops.new_fvar uu____13434))
in (

let gtok = (

let uu____13436 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented_token")
in (varops.new_fvar uu____13436))
in (

let env3 = (

let uu____13438 = (

let uu____13440 = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::[])))
in (FStar_All.pipe_left (fun _0_43 -> FStar_Pervasives_Native.Some (_0_43)) uu____13440))
in (push_free_var env2 flid gtok uu____13438))
in (((((flid), (f), (ftok), (g), (gtok)))::gtoks), (env3))))))
end)) (([]), (env1))))
in (match (uu____13305) with
| (gtoks, env2) -> begin
(

let gtoks1 = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env01 uu____13526 t_norm uu____13528 -> (match (((uu____13526), (uu____13528))) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = lbn; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____13555; FStar_Syntax_Syntax.lbeff = uu____13556; FStar_Syntax_Syntax.lbdef = e}) -> begin
(

let uu____13573 = (

let uu____13577 = (FStar_TypeChecker_Env.open_universes_in env2.tcenv uvs ((e)::(t_norm)::[]))
in (match (uu____13577) with
| (tcenv', uu____13592, e_t) -> begin
(

let uu____13596 = (match (e_t) with
| (e1)::(t_norm1)::[] -> begin
((e1), (t_norm1))
end
| uu____13603 -> begin
(failwith "Impossible")
end)
in (match (uu____13596) with
| (e1, t_norm1) -> begin
(((

let uu___150_13613 = env2
in {bindings = uu___150_13613.bindings; depth = uu___150_13613.depth; tcenv = tcenv'; warn = uu___150_13613.warn; cache = uu___150_13613.cache; nolabels = uu___150_13613.nolabels; use_zfuel_name = uu___150_13613.use_zfuel_name; encode_non_total_function_typ = uu___150_13613.encode_non_total_function_typ; current_module_name = uu___150_13613.current_module_name})), (e1), (t_norm1))
end))
end))
in (match (uu____13573) with
| (env', e1, t_norm1) -> begin
((

let uu____13623 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env01.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____13623) with
| true -> begin
(

let uu____13624 = (FStar_Syntax_Print.lbname_to_string lbn)
in (

let uu____13625 = (FStar_Syntax_Print.term_to_string t_norm1)
in (

let uu____13626 = (FStar_Syntax_Print.term_to_string e1)
in (FStar_Util.print3 "Encoding let rec %s : %s = %s\n" uu____13624 uu____13625 uu____13626))))
end
| uu____13627 -> begin
()
end));
(

let uu____13628 = (destruct_bound_function flid t_norm1 e1)
in (match (uu____13628) with
| ((binders, body, formals, tres), curry) -> begin
((

let uu____13650 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env01.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____13650) with
| true -> begin
(

let uu____13651 = (FStar_Syntax_Print.binders_to_string ", " binders)
in (

let uu____13652 = (FStar_Syntax_Print.term_to_string body)
in (

let uu____13653 = (FStar_Syntax_Print.binders_to_string ", " formals)
in (

let uu____13654 = (FStar_Syntax_Print.term_to_string tres)
in (FStar_Util.print4 "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n" uu____13651 uu____13652 uu____13653 uu____13654)))))
end
| uu____13655 -> begin
()
end));
(match (curry) with
| true -> begin
(failwith "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type")
end
| uu____13657 -> begin
()
end);
(

let uu____13658 = (encode_binders FStar_Pervasives_Native.None binders env')
in (match (uu____13658) with
| (vars, guards, env'1, binder_decls, uu____13676) -> begin
(

let decl_g = (

let uu____13684 = (

let uu____13690 = (

let uu____13692 = (FStar_List.map FStar_Pervasives_Native.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::uu____13692)
in ((g), (uu____13690), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Fuel-instrumented function name"))))
in FStar_SMTEncoding_Term.DeclFun (uu____13684))
in (

let env02 = (push_zfuel_name env01 flid g)
in (

let decl_g_tok = FStar_SMTEncoding_Term.DeclFun (((gtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Token for fuel-instrumented partial applications"))))
in (

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let app = (

let uu____13707 = (

let uu____13711 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (uu____13711)))
in (FStar_SMTEncoding_Util.mkApp uu____13707))
in (

let gsapp = (

let uu____13717 = (

let uu____13721 = (

let uu____13723 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (uu____13723)::vars_tm)
in ((g), (uu____13721)))
in (FStar_SMTEncoding_Util.mkApp uu____13717))
in (

let gmax = (

let uu____13727 = (

let uu____13731 = (

let uu____13733 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (uu____13733)::vars_tm)
in ((g), (uu____13731)))
in (FStar_SMTEncoding_Util.mkApp uu____13727))
in (

let body1 = (

let uu____13737 = (FStar_TypeChecker_Env.is_reifiable_function env'1.tcenv t_norm1)
in (match (uu____13737) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env'1.tcenv body)
end
| uu____13738 -> begin
body
end))
in (

let uu____13739 = (encode_term body1 env'1)
in (match (uu____13739) with
| (body_tm, decls2) -> begin
(

let eqn_g = (

let uu____13750 = (

let uu____13754 = (

let uu____13755 = (

let uu____13763 = (FStar_SMTEncoding_Util.mkEq ((gsapp), (body_tm)))
in ((((gsapp)::[])::[]), (FStar_Pervasives_Native.Some ((Prims.parse_int "0"))), ((fuel)::vars), (uu____13763)))
in (FStar_SMTEncoding_Util.mkForall' uu____13755))
in (

let uu____13774 = (

let uu____13776 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in FStar_Pervasives_Native.Some (uu____13776))
in ((uu____13754), (uu____13774), ((Prims.strcat "equation_with_fuel_" g)))))
in (FStar_SMTEncoding_Util.mkAssume uu____13750))
in (

let eqn_f = (

let uu____13779 = (

let uu____13783 = (

let uu____13784 = (

let uu____13790 = (FStar_SMTEncoding_Util.mkEq ((app), (gmax)))
in ((((app)::[])::[]), (vars), (uu____13790)))
in (FStar_SMTEncoding_Util.mkForall uu____13784))
in ((uu____13783), (FStar_Pervasives_Native.Some ("Correspondence of recursive function to instrumented version")), ((Prims.strcat "@fuel_correspondence_" g))))
in (FStar_SMTEncoding_Util.mkAssume uu____13779))
in (

let eqn_g' = (

let uu____13798 = (

let uu____13802 = (

let uu____13803 = (

let uu____13809 = (

let uu____13810 = (

let uu____13813 = (

let uu____13814 = (

let uu____13818 = (

let uu____13820 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "0"))
in (uu____13820)::vars_tm)
in ((g), (uu____13818)))
in (FStar_SMTEncoding_Util.mkApp uu____13814))
in ((gsapp), (uu____13813)))
in (FStar_SMTEncoding_Util.mkEq uu____13810))
in ((((gsapp)::[])::[]), ((fuel)::vars), (uu____13809)))
in (FStar_SMTEncoding_Util.mkForall uu____13803))
in ((uu____13802), (FStar_Pervasives_Native.Some ("Fuel irrelevance")), ((Prims.strcat "@fuel_irrelevance_" g))))
in (FStar_SMTEncoding_Util.mkAssume uu____13798))
in (

let uu____13832 = (

let uu____13837 = (encode_binders FStar_Pervasives_Native.None formals env02)
in (match (uu____13837) with
| (vars1, v_guards, env3, binder_decls1, uu____13854) -> begin
(

let vars_tm1 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars1)
in (

let gapp = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::vars_tm1)))
in (

let tok_corr = (

let tok_app = (

let uu____13869 = (FStar_SMTEncoding_Util.mkFreeV ((gtok), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply uu____13869 ((fuel)::vars1)))
in (

let uu____13872 = (

let uu____13876 = (

let uu____13877 = (

let uu____13883 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (gapp)))
in ((((tok_app)::[])::[]), ((fuel)::vars1), (uu____13883)))
in (FStar_SMTEncoding_Util.mkForall uu____13877))
in ((uu____13876), (FStar_Pervasives_Native.Some ("Fuel token correspondence")), ((Prims.strcat "fuel_token_correspondence_" gtok))))
in (FStar_SMTEncoding_Util.mkAssume uu____13872)))
in (

let uu____13894 = (

let uu____13898 = (encode_term_pred FStar_Pervasives_Native.None tres env3 gapp)
in (match (uu____13898) with
| (g_typing, d3) -> begin
(

let uu____13906 = (

let uu____13908 = (

let uu____13909 = (

let uu____13913 = (

let uu____13914 = (

let uu____13920 = (

let uu____13921 = (

let uu____13924 = (FStar_SMTEncoding_Util.mk_and_l v_guards)
in ((uu____13924), (g_typing)))
in (FStar_SMTEncoding_Util.mkImp uu____13921))
in ((((gapp)::[])::[]), ((fuel)::vars1), (uu____13920)))
in (FStar_SMTEncoding_Util.mkForall uu____13914))
in ((uu____13913), (FStar_Pervasives_Native.Some ("Typing correspondence of token to term")), ((Prims.strcat "token_correspondence_" g))))
in (FStar_SMTEncoding_Util.mkAssume uu____13909))
in (uu____13908)::[])
in ((d3), (uu____13906)))
end))
in (match (uu____13894) with
| (aux_decls, typing_corr) -> begin
(((FStar_List.append binder_decls1 aux_decls)), ((FStar_List.append typing_corr ((tok_corr)::[]))))
end)))))
end))
in (match (uu____13832) with
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

let uu____13959 = (

let uu____13966 = (FStar_List.zip3 gtoks1 typs1 bindings)
in (FStar_List.fold_left (fun uu____14014 uu____14015 -> (match (((uu____14014), (uu____14015))) with
| ((decls2, eqns, env01), (gtok, ty, lb)) -> begin
(

let uu____14101 = (encode_one_binding env01 gtok ty lb)
in (match (uu____14101) with
| (decls', eqns', env02) -> begin
(((decls')::decls2), ((FStar_List.append eqns' eqns)), (env02))
end))
end)) (((decls1)::[]), ([]), (env0)) uu____13966))
in (match (uu____13959) with
| (decls2, eqns, env01) -> begin
(

let uu____14141 = (

let isDeclFun = (fun uu___117_14149 -> (match (uu___117_14149) with
| FStar_SMTEncoding_Term.DeclFun (uu____14150) -> begin
true
end
| uu____14156 -> begin
false
end))
in (

let uu____14157 = (FStar_All.pipe_right decls2 FStar_List.flatten)
in (FStar_All.pipe_right uu____14157 (FStar_List.partition isDeclFun))))
in (match (uu____14141) with
| (prefix_decls, rest) -> begin
(

let eqns1 = (FStar_List.rev eqns)
in (((FStar_List.append prefix_decls (FStar_List.append rest eqns1))), (env01)))
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

let msg = (

let uu____14187 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right uu____14187 (FStar_String.concat " and ")))
in (

let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in (((decl)::[]), (env))))
end))
end))


let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let nm = (

let uu____14221 = (FStar_Syntax_Util.lid_of_sigelt se)
in (match (uu____14221) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (l) -> begin
l.FStar_Ident.str
end))
in (

let uu____14224 = (encode_sigelt' env se)
in (match (uu____14224) with
| (g, env1) -> begin
(

let g1 = (match (g) with
| [] -> begin
(

let uu____14234 = (

let uu____14235 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (uu____14235))
in (uu____14234)::[])
end
| uu____14236 -> begin
(

let uu____14237 = (

let uu____14239 = (

let uu____14240 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____14240))
in (uu____14239)::g)
in (

let uu____14241 = (

let uu____14243 = (

let uu____14244 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____14244))
in (uu____14243)::[])
in (FStar_List.append uu____14237 uu____14241)))
end)
in ((g1), (env1)))
end))))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let is_opaque_to_smt = (fun t -> (

let uu____14254 = (

let uu____14255 = (FStar_Syntax_Subst.compress t)
in uu____14255.FStar_Syntax_Syntax.n)
in (match (uu____14254) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (bytes, uu____14259)) -> begin
((FStar_Util.string_of_bytes bytes) = "opaque_to_smt")
end
| uu____14262 -> begin
false
end)))
in (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____14265) -> begin
(failwith "impossible -- removed by tc.fs")
end
| FStar_Syntax_Syntax.Sig_pragma (uu____14268) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_main (uu____14270) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____14272) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____14280) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(

let uu____14283 = (

let uu____14284 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right uu____14284 Prims.op_Negation))
in (match (uu____14283) with
| true -> begin
(([]), (env))
end
| uu____14289 -> begin
(

let close_effect_params = (fun tm -> (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
tm
end
| uu____14304 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((ed.FStar_Syntax_Syntax.binders), (tm), (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[]))))))) FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)
end))
in (

let encode_action = (fun env1 a -> (

let uu____14324 = (new_term_constant_and_tok_from_lid env1 a.FStar_Syntax_Syntax.action_name)
in (match (uu____14324) with
| (aname, atok, env2) -> begin
(

let uu____14334 = (FStar_Syntax_Util.arrow_formals_comp a.FStar_Syntax_Syntax.action_typ)
in (match (uu____14334) with
| (formals, uu____14344) -> begin
(

let uu____14351 = (

let uu____14354 = (close_effect_params a.FStar_Syntax_Syntax.action_defn)
in (encode_term uu____14354 env2))
in (match (uu____14351) with
| (tm, decls) -> begin
(

let a_decls = (

let uu____14362 = (

let uu____14363 = (

let uu____14369 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____14378 -> FStar_SMTEncoding_Term.Term_sort)))
in ((aname), (uu____14369), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Action"))))
in FStar_SMTEncoding_Term.DeclFun (uu____14363))
in (uu____14362)::(FStar_SMTEncoding_Term.DeclFun (((atok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Action token")))))::[])
in (

let uu____14385 = (

let aux = (fun uu____14414 uu____14415 -> (match (((uu____14414), (uu____14415))) with
| ((bv, uu____14442), (env3, acc_sorts, acc)) -> begin
(

let uu____14463 = (gen_term_var env3 bv)
in (match (uu____14463) with
| (xxsym, xx, env4) -> begin
((env4), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::acc_sorts), ((xx)::acc))
end))
end))
in (FStar_List.fold_right aux formals ((env2), ([]), ([]))))
in (match (uu____14385) with
| (uu____14501, xs_sorts, xs) -> begin
(

let app = (FStar_SMTEncoding_Util.mkApp ((aname), (xs)))
in (

let a_eq = (

let uu____14515 = (

let uu____14519 = (

let uu____14520 = (

let uu____14526 = (

let uu____14527 = (

let uu____14530 = (mk_Apply tm xs_sorts)
in ((app), (uu____14530)))
in (FStar_SMTEncoding_Util.mkEq uu____14527))
in ((((app)::[])::[]), (xs_sorts), (uu____14526)))
in (FStar_SMTEncoding_Util.mkForall uu____14520))
in ((uu____14519), (FStar_Pervasives_Native.Some ("Action equality")), ((Prims.strcat aname "_equality"))))
in (FStar_SMTEncoding_Util.mkAssume uu____14515))
in (

let tok_correspondence = (

let tok_term = (FStar_SMTEncoding_Util.mkFreeV ((atok), (FStar_SMTEncoding_Term.Term_sort)))
in (

let tok_app = (mk_Apply tok_term xs_sorts)
in (

let uu____14542 = (

let uu____14546 = (

let uu____14547 = (

let uu____14553 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (app)))
in ((((tok_app)::[])::[]), (xs_sorts), (uu____14553)))
in (FStar_SMTEncoding_Util.mkForall uu____14547))
in ((uu____14546), (FStar_Pervasives_Native.Some ("Action token correspondence")), ((Prims.strcat aname "_token_correspondence"))))
in (FStar_SMTEncoding_Util.mkAssume uu____14542))))
in ((env2), ((FStar_List.append decls (FStar_List.append a_decls ((a_eq)::(tok_correspondence)::[]))))))))
end)))
end))
end))
end)))
in (

let uu____14563 = (FStar_Util.fold_map encode_action env ed.FStar_Syntax_Syntax.actions)
in (match (uu____14563) with
| (env1, decls2) -> begin
(((FStar_List.flatten decls2)), (env1))
end))))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____14579, uu____14580) when (FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid) -> begin
(

let uu____14581 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____14581) with
| (tname, ttok, env1) -> begin
(([]), (env1))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____14592, t) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let will_encode_definition = (

let uu____14597 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___118_14600 -> (match (uu___118_14600) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.Projector (uu____14601) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____14604) -> begin
true
end
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| uu____14605 -> begin
false
end))))
in (not (uu____14597)))
in (match (will_encode_definition) with
| true -> begin
(([]), (env))
end
| uu____14609 -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____14611 = (encode_top_level_val env fv t quals)
in (match (uu____14611) with
| (decls, env1) -> begin
(

let tname = lid.FStar_Ident.str
in (

let tsym = (FStar_SMTEncoding_Util.mkFreeV ((tname), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____14623 = (

let uu____14625 = (primitive_type_axioms env1.tcenv lid tname tsym)
in (FStar_List.append decls uu____14625))
in ((uu____14623), (env1)))))
end)))
end)))
end
| FStar_Syntax_Syntax.Sig_assume (l, us, f) -> begin
(

let uu____14631 = (FStar_Syntax_Subst.open_univ_vars us f)
in (match (uu____14631) with
| (uu____14636, f1) -> begin
(

let uu____14638 = (encode_formula f1 env)
in (match (uu____14638) with
| (f2, decls) -> begin
(

let g = (

let uu____14647 = (

let uu____14648 = (

let uu____14652 = (

let uu____14654 = (

let uu____14655 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" uu____14655))
in FStar_Pervasives_Native.Some (uu____14654))
in (

let uu____14656 = (varops.mk_unique (Prims.strcat "assumption_" l.FStar_Ident.str))
in ((f2), (uu____14652), (uu____14656))))
in (FStar_SMTEncoding_Util.mkAssume uu____14648))
in (uu____14647)::[])
in (((FStar_List.append decls g)), (env)))
end))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____14660) when ((FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) || (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs (FStar_Util.for_some is_opaque_to_smt))) -> begin
(

let attrs = se.FStar_Syntax_Syntax.sigattrs
in (

let uu____14667 = (FStar_Util.fold_map (fun env1 lb -> (

let lid = (

let uu____14682 = (

let uu____14684 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____14684.FStar_Syntax_Syntax.fv_name)
in uu____14682.FStar_Syntax_Syntax.v)
in (

let uu____14685 = (

let uu____14686 = (FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone uu____14686))
in (match (uu____14685) with
| true -> begin
(

let val_decl = (

let uu___151_14701 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = uu___151_14701.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Irreducible)::se.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___151_14701.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___151_14701.FStar_Syntax_Syntax.sigattrs})
in (

let uu____14705 = (encode_sigelt' env1 val_decl)
in (match (uu____14705) with
| (decls, env2) -> begin
((env2), (decls))
end)))
end
| uu____14712 -> begin
((env1), ([]))
end)))) env (FStar_Pervasives_Native.snd lbs))
in (match (uu____14667) with
| (env1, decls) -> begin
(((FStar_List.flatten decls)), (env1))
end)))
end
| FStar_Syntax_Syntax.Sig_let ((uu____14722, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t1); FStar_Syntax_Syntax.lbunivs = uu____14724; FStar_Syntax_Syntax.lbtyp = uu____14725; FStar_Syntax_Syntax.lbeff = uu____14726; FStar_Syntax_Syntax.lbdef = uu____14727})::[]), uu____14728) when (FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid) -> begin
(

let uu____14740 = (new_term_constant_and_tok_from_lid env b2t1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____14740) with
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

let uu____14759 = (

let uu____14761 = (

let uu____14762 = (

let uu____14766 = (

let uu____14767 = (

let uu____14773 = (

let uu____14774 = (

let uu____14777 = (FStar_SMTEncoding_Util.mkApp (("BoxBool_proj_0"), ((x)::[])))
in ((valid_b2t_x), (uu____14777)))
in (FStar_SMTEncoding_Util.mkEq uu____14774))
in ((((b2t_x)::[])::[]), ((xx)::[]), (uu____14773)))
in (FStar_SMTEncoding_Util.mkForall uu____14767))
in ((uu____14766), (FStar_Pervasives_Native.Some ("b2t def")), ("b2t_def")))
in (FStar_SMTEncoding_Util.mkAssume uu____14762))
in (uu____14761)::[])
in (FStar_SMTEncoding_Term.DeclFun (((tname), ((FStar_SMTEncoding_Term.Term_sort)::[]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None))))::uu____14759)
in ((decls), (env1)))))))
end))
end
| FStar_Syntax_Syntax.Sig_let (uu____14794, uu____14795) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___119_14801 -> (match (uu___119_14801) with
| FStar_Syntax_Syntax.Discriminator (uu____14802) -> begin
true
end
| uu____14803 -> begin
false
end)))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let (uu____14805, lids) when ((FStar_All.pipe_right lids (FStar_Util.for_some (fun l -> (

let uu____14813 = (

let uu____14814 = (FStar_List.hd l.FStar_Ident.ns)
in uu____14814.FStar_Ident.idText)
in (uu____14813 = "Prims"))))) && (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___120_14817 -> (match (uu___120_14817) with
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
true
end
| uu____14818 -> begin
false
end))))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____14821) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___121_14831 -> (match (uu___121_14831) with
| FStar_Syntax_Syntax.Projector (uu____14832) -> begin
true
end
| uu____14835 -> begin
false
end)))) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____14838 = (try_lookup_free_var env l)
in (match (uu____14838) with
| FStar_Pervasives_Native.Some (uu____14842) -> begin
(([]), (env))
end
| FStar_Pervasives_Native.None -> begin
(

let se1 = (

let uu___152_14845 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l); FStar_Syntax_Syntax.sigquals = uu___152_14845.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___152_14845.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___152_14845.FStar_Syntax_Syntax.sigattrs})
in (encode_sigelt env se1))
end))))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), uu____14851) -> begin
(encode_top_level_let env ((is_rec), (bindings)) se.FStar_Syntax_Syntax.sigquals)
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____14861) -> begin
(

let uu____14866 = (encode_sigelts env ses)
in (match (uu____14866) with
| (g, env1) -> begin
(

let uu____14876 = (FStar_All.pipe_right g (FStar_List.partition (fun uu___122_14890 -> (match (uu___122_14890) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.assumption_term = uu____14891; FStar_SMTEncoding_Term.assumption_caption = FStar_Pervasives_Native.Some ("inversion axiom"); FStar_SMTEncoding_Term.assumption_name = uu____14892; FStar_SMTEncoding_Term.assumption_fact_ids = uu____14893}) -> begin
false
end
| uu____14895 -> begin
true
end))))
in (match (uu____14876) with
| (g', inversions) -> begin
(

let uu____14904 = (FStar_All.pipe_right g' (FStar_List.partition (fun uu___123_14916 -> (match (uu___123_14916) with
| FStar_SMTEncoding_Term.DeclFun (uu____14917) -> begin
true
end
| uu____14923 -> begin
false
end))))
in (match (uu____14904) with
| (decls, rest) -> begin
(((FStar_List.append decls (FStar_List.append rest inversions))), (env1))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, uu____14934, tps, k, uu____14937, datas) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___124_14948 -> (match (uu___124_14948) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____14949 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> (match (is_logical) with
| true -> begin
(

let uu____14956 = c
in (match (uu____14956) with
| (name, args, uu____14960, uu____14961, uu____14962) -> begin
(

let uu____14965 = (

let uu____14966 = (

let uu____14972 = (FStar_All.pipe_right args (FStar_List.map (fun uu____14983 -> (match (uu____14983) with
| (uu____14987, sort, uu____14989) -> begin
sort
end))))
in ((name), (uu____14972), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____14966))
in (uu____14965)::[])
end))
end
| uu____14992 -> begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end))
in (

let inversion_axioms = (fun tapp vars -> (

let uu____15007 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (

let uu____15012 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right uu____15012 FStar_Option.isNone)))))
in (match (uu____15007) with
| true -> begin
[]
end
| uu____15028 -> begin
(

let uu____15029 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____15029) with
| (xxsym, xx) -> begin
(

let uu____15035 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun uu____15064 l -> (match (uu____15064) with
| (out, decls) -> begin
(

let uu____15076 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (uu____15076) with
| (uu____15082, data_t) -> begin
(

let uu____15084 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (uu____15084) with
| (args, res) -> begin
(

let indices = (

let uu____15113 = (

let uu____15114 = (FStar_Syntax_Subst.compress res)
in uu____15114.FStar_Syntax_Syntax.n)
in (match (uu____15113) with
| FStar_Syntax_Syntax.Tm_app (uu____15122, indices) -> begin
indices
end
| uu____15138 -> begin
[]
end))
in (

let env1 = (FStar_All.pipe_right args (FStar_List.fold_left (fun env1 uu____15155 -> (match (uu____15155) with
| (x, uu____15159) -> begin
(

let uu____15160 = (

let uu____15161 = (

let uu____15165 = (mk_term_projector_name l x)
in ((uu____15165), ((xx)::[])))
in (FStar_SMTEncoding_Util.mkApp uu____15161))
in (push_term_var env1 x uu____15160))
end)) env))
in (

let uu____15167 = (encode_args indices env1)
in (match (uu____15167) with
| (indices1, decls') -> begin
((match (((FStar_List.length indices1) <> (FStar_List.length vars))) with
| true -> begin
(failwith "Impossible")
end
| uu____15189 -> begin
()
end);
(

let eqs = (

let uu____15191 = (FStar_List.map2 (fun v1 a -> (

let uu____15202 = (

let uu____15205 = (FStar_SMTEncoding_Util.mkFreeV v1)
in ((uu____15205), (a)))
in (FStar_SMTEncoding_Util.mkEq uu____15202))) vars indices1)
in (FStar_All.pipe_right uu____15191 FStar_SMTEncoding_Util.mk_and_l))
in (

let uu____15207 = (

let uu____15208 = (

let uu____15211 = (

let uu____15212 = (

let uu____15215 = (mk_data_tester env1 l xx)
in ((uu____15215), (eqs)))
in (FStar_SMTEncoding_Util.mkAnd uu____15212))
in ((out), (uu____15211)))
in (FStar_SMTEncoding_Util.mkOr uu____15208))
in ((uu____15207), ((FStar_List.append decls decls')))));
)
end))))
end))
end))
end)) ((FStar_SMTEncoding_Util.mkFalse), ([]))))
in (match (uu____15035) with
| (data_ax, decls) -> begin
(

let uu____15223 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____15223) with
| (ffsym, ff) -> begin
(

let fuel_guarded_inversion = (

let xx_has_type_sfuel = (match (((FStar_List.length datas) > (Prims.parse_int "1"))) with
| true -> begin
(

let uu____15237 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((ff)::[])))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel uu____15237 xx tapp))
end
| uu____15239 -> begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end)
in (

let uu____15240 = (

let uu____15244 = (

let uu____15245 = (

let uu____15251 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (

let uu____15259 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_sfuel), (data_ax)))
in ((((xx_has_type_sfuel)::[])::[]), (uu____15251), (uu____15259))))
in (FStar_SMTEncoding_Util.mkForall uu____15245))
in (

let uu____15267 = (varops.mk_unique (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str))
in ((uu____15244), (FStar_Pervasives_Native.Some ("inversion axiom")), (uu____15267))))
in (FStar_SMTEncoding_Util.mkAssume uu____15240)))
in (

let pattern_guarded_inversion = (

let uu____15271 = ((contains_name env "Prims.inversion") && ((FStar_List.length datas) > (Prims.parse_int "1")))
in (match (uu____15271) with
| true -> begin
(

let xx_has_type_fuel = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let pattern_guard = (FStar_SMTEncoding_Util.mkApp (("Prims.inversion"), ((tapp)::[])))
in (

let uu____15282 = (

let uu____15283 = (

let uu____15287 = (

let uu____15288 = (

let uu____15294 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (

let uu____15302 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_fuel), (data_ax)))
in ((((xx_has_type_fuel)::(pattern_guard)::[])::[]), (uu____15294), (uu____15302))))
in (FStar_SMTEncoding_Util.mkForall uu____15288))
in (

let uu____15310 = (varops.mk_unique (Prims.strcat "pattern_guarded_inversion_" t.FStar_Ident.str))
in ((uu____15287), (FStar_Pervasives_Native.Some ("inversion axiom")), (uu____15310))))
in (FStar_SMTEncoding_Util.mkAssume uu____15283))
in (uu____15282)::[])))
end
| uu____15312 -> begin
[]
end))
in (FStar_List.append decls (FStar_List.append ((fuel_guarded_inversion)::[]) pattern_guarded_inversion))))
end))
end))
end))
end)))
in (

let uu____15313 = (

let uu____15321 = (

let uu____15322 = (FStar_Syntax_Subst.compress k)
in uu____15322.FStar_Syntax_Syntax.n)
in (match (uu____15321) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
(((FStar_List.append tps formals)), ((FStar_Syntax_Util.comp_result kres)))
end
| uu____15351 -> begin
((tps), (k))
end))
in (match (uu____15313) with
| (formals, res) -> begin
(

let uu____15366 = (FStar_Syntax_Subst.open_term formals res)
in (match (uu____15366) with
| (formals1, res1) -> begin
(

let uu____15373 = (encode_binders FStar_Pervasives_Native.None formals1 env)
in (match (uu____15373) with
| (vars, guards, env', binder_decls, uu____15388) -> begin
(

let uu____15395 = (new_term_constant_and_tok_from_lid env t)
in (match (uu____15395) with
| (tname, ttok, env1) -> begin
(

let ttok_tm = (FStar_SMTEncoding_Util.mkApp ((ttok), ([])))
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let tapp = (

let uu____15408 = (

let uu____15412 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((tname), (uu____15412)))
in (FStar_SMTEncoding_Util.mkApp uu____15408))
in (

let uu____15417 = (

let tname_decl = (

let uu____15423 = (

let uu____15424 = (FStar_All.pipe_right vars (FStar_List.map (fun uu____15442 -> (match (uu____15442) with
| (n1, s) -> begin
(((Prims.strcat tname n1)), (s), (false))
end))))
in (

let uu____15450 = (varops.next_id ())
in ((tname), (uu____15424), (FStar_SMTEncoding_Term.Term_sort), (uu____15450), (false))))
in (constructor_or_logic_type_decl uu____15423))
in (

let uu____15455 = (match (vars) with
| [] -> begin
(

let uu____15462 = (

let uu____15463 = (

let uu____15465 = (FStar_SMTEncoding_Util.mkApp ((tname), ([])))
in (FStar_All.pipe_left (fun _0_44 -> FStar_Pervasives_Native.Some (_0_44)) uu____15465))
in (push_free_var env1 t tname uu____15463))
in (([]), (uu____15462)))
end
| uu____15469 -> begin
(

let ttok_decl = FStar_SMTEncoding_Term.DeclFun (((ttok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("token"))))
in (

let ttok_fresh = (

let uu____15475 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ttok), (FStar_SMTEncoding_Term.Term_sort)) uu____15475))
in (

let ttok_app = (mk_Apply ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (

let uu____15484 = (

let uu____15488 = (

let uu____15489 = (

let uu____15497 = (FStar_SMTEncoding_Util.mkEq ((ttok_app), (tapp)))
in ((pats), (FStar_Pervasives_Native.None), (vars), (uu____15497)))
in (FStar_SMTEncoding_Util.mkForall' uu____15489))
in ((uu____15488), (FStar_Pervasives_Native.Some ("name-token correspondence")), ((Prims.strcat "token_correspondence_" ttok))))
in (FStar_SMTEncoding_Util.mkAssume uu____15484))
in (((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[]), (env1)))))))
end)
in (match (uu____15455) with
| (tok_decls, env2) -> begin
(((FStar_List.append tname_decl tok_decls)), (env2))
end)))
in (match (uu____15417) with
| (decls, env2) -> begin
(

let kindingAx = (

let uu____15520 = (encode_term_pred FStar_Pervasives_Native.None res1 env' tapp)
in (match (uu____15520) with
| (k1, decls1) -> begin
(

let karr = (match (((FStar_List.length formals1) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____15537 = (

let uu____15538 = (

let uu____15542 = (

let uu____15543 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____15543))
in ((uu____15542), (FStar_Pervasives_Native.Some ("kinding")), ((Prims.strcat "pre_kinding_" ttok))))
in (FStar_SMTEncoding_Util.mkAssume uu____15538))
in (uu____15537)::[])
end
| uu____15545 -> begin
[]
end)
in (

let uu____15546 = (

let uu____15548 = (

let uu____15550 = (

let uu____15551 = (

let uu____15555 = (

let uu____15556 = (

let uu____15562 = (FStar_SMTEncoding_Util.mkImp ((guard), (k1)))
in ((((tapp)::[])::[]), (vars), (uu____15562)))
in (FStar_SMTEncoding_Util.mkForall uu____15556))
in ((uu____15555), (FStar_Pervasives_Native.None), ((Prims.strcat "kinding_" ttok))))
in (FStar_SMTEncoding_Util.mkAssume uu____15551))
in (uu____15550)::[])
in (FStar_List.append karr uu____15548))
in (FStar_List.append decls1 uu____15546)))
end))
in (

let aux = (

let uu____15571 = (

let uu____15573 = (inversion_axioms tapp vars)
in (

let uu____15575 = (

let uu____15577 = (pretype_axiom env2 tapp vars)
in (uu____15577)::[])
in (FStar_List.append uu____15573 uu____15575)))
in (FStar_List.append kindingAx uu____15571))
in (

let g = (FStar_List.append decls (FStar_List.append binder_decls aux))
in ((g), (env2)))))
end)))))
end))
end))
end))
end))))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____15582, uu____15583, uu____15584, uu____15585, uu____15586) when (FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____15591, t, uu____15593, n_tps, uu____15595) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____15600 = (new_term_constant_and_tok_from_lid env d)
in (match (uu____15600) with
| (ddconstrsym, ddtok, env1) -> begin
(

let ddtok_tm = (FStar_SMTEncoding_Util.mkApp ((ddtok), ([])))
in (

let uu____15611 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____15611) with
| (formals, t_res) -> begin
(

let uu____15633 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____15633) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (

let uu____15642 = (encode_binders (FStar_Pervasives_Native.Some (fuel_tm)) formals env1)
in (match (uu____15642) with
| (vars, guards, env', binder_decls, names1) -> begin
(

let fields = (FStar_All.pipe_right names1 (FStar_List.mapi (fun n1 x -> (

let projectible = true
in (

let uu____15684 = (mk_term_projector_name d x)
in ((uu____15684), (FStar_SMTEncoding_Term.Term_sort), (projectible)))))))
in (

let datacons = (

let uu____15686 = (

let uu____15696 = (varops.next_id ())
in ((ddconstrsym), (fields), (FStar_SMTEncoding_Term.Term_sort), (uu____15696), (true)))
in (FStar_All.pipe_right uu____15686 FStar_SMTEncoding_Term.constructor_to_decl))
in (

let app = (mk_Apply ddtok_tm vars)
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (

let uu____15718 = (encode_term_pred FStar_Pervasives_Native.None t env1 ddtok_tm)
in (match (uu____15718) with
| (tok_typing, decls3) -> begin
(

let tok_typing1 = (match (fields) with
| (uu____15726)::uu____15727 -> begin
(

let ff = (("ty"), (FStar_SMTEncoding_Term.Term_sort))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV ff)
in (

let vtok_app_l = (mk_Apply ddtok_tm ((ff)::[]))
in (

let vtok_app_r = (mk_Apply f ((((ddtok), (FStar_SMTEncoding_Term.Term_sort)))::[]))
in (

let uu____15752 = (

let uu____15758 = (FStar_SMTEncoding_Term.mk_NoHoist f tok_typing)
in ((((vtok_app_l)::[])::((vtok_app_r)::[])::[]), ((ff)::[]), (uu____15758)))
in (FStar_SMTEncoding_Util.mkForall uu____15752))))))
end
| uu____15771 -> begin
tok_typing
end)
in (

let uu____15776 = (encode_binders (FStar_Pervasives_Native.Some (fuel_tm)) formals env1)
in (match (uu____15776) with
| (vars', guards', env'', decls_formals, uu____15791) -> begin
(

let uu____15798 = (

let xvars1 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars')
in (

let dapp1 = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars1)))
in (encode_term_pred (FStar_Pervasives_Native.Some (fuel_tm)) t_res env'' dapp1)))
in (match (uu____15798) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_SMTEncoding_Util.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| uu____15817 -> begin
(

let uu____15821 = (

let uu____15822 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ddtok), (FStar_SMTEncoding_Term.Term_sort)) uu____15822))
in (uu____15821)::[])
end)
in (

let encode_elim = (fun uu____15829 -> (

let uu____15830 = (FStar_Syntax_Util.head_and_args t_res)
in (match (uu____15830) with
| (head1, args) -> begin
(

let uu____15859 = (

let uu____15860 = (FStar_Syntax_Subst.compress head1)
in uu____15860.FStar_Syntax_Syntax.n)
in (match (uu____15859) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____15867; FStar_Syntax_Syntax.pos = uu____15868; FStar_Syntax_Syntax.vars = uu____15869}, uu____15870) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let uu____15876 = (encode_args args env')
in (match (uu____15876) with
| (encoded_args, arg_decls) -> begin
(

let guards_for_parameter = (fun orig_arg arg xv -> (

let fv1 = (match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv1) -> begin
fv1
end
| uu____15905 -> begin
(

let uu____15906 = (

let uu____15907 = (

let uu____15910 = (

let uu____15911 = (FStar_Syntax_Print.term_to_string orig_arg)
in (FStar_Util.format1 "Inductive type parameter %s must be a variable ; You may want to change it to an index." uu____15911))
in ((uu____15910), (orig_arg.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____15907))
in (FStar_Pervasives.raise uu____15906))
end)
in (

let guards1 = (FStar_All.pipe_right guards (FStar_List.collect (fun g -> (

let uu____15922 = (

let uu____15923 = (FStar_SMTEncoding_Term.free_variables g)
in (FStar_List.contains fv1 uu____15923))
in (match (uu____15922) with
| true -> begin
(

let uu____15930 = (FStar_SMTEncoding_Term.subst g fv1 xv)
in (uu____15930)::[])
end
| uu____15931 -> begin
[]
end)))))
in (FStar_SMTEncoding_Util.mk_and_l guards1))))
in (

let uu____15932 = (

let uu____15939 = (FStar_List.zip args encoded_args)
in (FStar_List.fold_left (fun uu____15972 uu____15973 -> (match (((uu____15972), (uu____15973))) with
| ((env2, arg_vars, eqns_or_guards, i), (orig_arg, arg)) -> begin
(

let uu____16024 = (

let uu____16028 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (gen_term_var env2 uu____16028))
in (match (uu____16024) with
| (uu____16035, xv, env3) -> begin
(

let eqns = (match ((i < n_tps)) with
| true -> begin
(

let uu____16041 = (guards_for_parameter (FStar_Pervasives_Native.fst orig_arg) arg xv)
in (uu____16041)::eqns_or_guards)
end
| uu____16042 -> begin
(

let uu____16043 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (uu____16043)::eqns_or_guards)
end)
in ((env3), ((xv)::arg_vars), (eqns), ((i + (Prims.parse_int "1")))))
end))
end)) ((env'), ([]), ([]), ((Prims.parse_int "0"))) uu____15939))
in (match (uu____15932) with
| (uu____16051, arg_vars, elim_eqns_or_guards, uu____16054) -> begin
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

let uu____16073 = (

let uu____16077 = (

let uu____16078 = (

let uu____16084 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____16090 = (

let uu____16091 = (

let uu____16094 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append elim_eqns_or_guards guards))
in ((ty_pred), (uu____16094)))
in (FStar_SMTEncoding_Util.mkImp uu____16091))
in ((((ty_pred)::[])::[]), (uu____16084), (uu____16090))))
in (FStar_SMTEncoding_Util.mkForall uu____16078))
in ((uu____16077), (FStar_Pervasives_Native.Some ("data constructor typing elim")), ((Prims.strcat "data_elim_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____16073))
in (

let subterm_ordering = (match ((FStar_Ident.lid_equals d FStar_Parser_Const.lextop_lid)) with
| true -> begin
(

let x = (

let uu____16107 = (varops.fresh "x")
in ((uu____16107), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (

let uu____16109 = (

let uu____16113 = (

let uu____16114 = (

let uu____16120 = (

let uu____16123 = (

let uu____16125 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in (uu____16125)::[])
in (uu____16123)::[])
in (

let uu____16128 = (

let uu____16129 = (

let uu____16132 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (

let uu____16133 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in ((uu____16132), (uu____16133))))
in (FStar_SMTEncoding_Util.mkImp uu____16129))
in ((uu____16120), ((x)::[]), (uu____16128))))
in (FStar_SMTEncoding_Util.mkForall uu____16114))
in (

let uu____16143 = (varops.mk_unique "lextop")
in ((uu____16113), (FStar_Pervasives_Native.Some ("lextop is top")), (uu____16143))))
in (FStar_SMTEncoding_Util.mkAssume uu____16109))))
end
| uu____16145 -> begin
(

let prec = (

let uu____16148 = (FStar_All.pipe_right vars (FStar_List.mapi (fun i v1 -> (match ((i < n_tps)) with
| true -> begin
[]
end
| uu____16164 -> begin
(

let uu____16165 = (

let uu____16166 = (FStar_SMTEncoding_Util.mkFreeV v1)
in (FStar_SMTEncoding_Util.mk_Precedes uu____16166 dapp1))
in (uu____16165)::[])
end))))
in (FStar_All.pipe_right uu____16148 FStar_List.flatten))
in (

let uu____16170 = (

let uu____16174 = (

let uu____16175 = (

let uu____16181 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____16187 = (

let uu____16188 = (

let uu____16191 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (uu____16191)))
in (FStar_SMTEncoding_Util.mkImp uu____16188))
in ((((ty_pred)::[])::[]), (uu____16181), (uu____16187))))
in (FStar_SMTEncoding_Util.mkForall uu____16175))
in ((uu____16174), (FStar_Pervasives_Native.Some ("subterm ordering")), ((Prims.strcat "subterm_ordering_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____16170)))
end)
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end)))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let uu____16203 = (encode_args args env')
in (match (uu____16203) with
| (encoded_args, arg_decls) -> begin
(

let guards_for_parameter = (fun orig_arg arg xv -> (

let fv1 = (match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv1) -> begin
fv1
end
| uu____16232 -> begin
(

let uu____16233 = (

let uu____16234 = (

let uu____16237 = (

let uu____16238 = (FStar_Syntax_Print.term_to_string orig_arg)
in (FStar_Util.format1 "Inductive type parameter %s must be a variable ; You may want to change it to an index." uu____16238))
in ((uu____16237), (orig_arg.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____16234))
in (FStar_Pervasives.raise uu____16233))
end)
in (

let guards1 = (FStar_All.pipe_right guards (FStar_List.collect (fun g -> (

let uu____16249 = (

let uu____16250 = (FStar_SMTEncoding_Term.free_variables g)
in (FStar_List.contains fv1 uu____16250))
in (match (uu____16249) with
| true -> begin
(

let uu____16257 = (FStar_SMTEncoding_Term.subst g fv1 xv)
in (uu____16257)::[])
end
| uu____16258 -> begin
[]
end)))))
in (FStar_SMTEncoding_Util.mk_and_l guards1))))
in (

let uu____16259 = (

let uu____16266 = (FStar_List.zip args encoded_args)
in (FStar_List.fold_left (fun uu____16299 uu____16300 -> (match (((uu____16299), (uu____16300))) with
| ((env2, arg_vars, eqns_or_guards, i), (orig_arg, arg)) -> begin
(

let uu____16351 = (

let uu____16355 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (gen_term_var env2 uu____16355))
in (match (uu____16351) with
| (uu____16362, xv, env3) -> begin
(

let eqns = (match ((i < n_tps)) with
| true -> begin
(

let uu____16368 = (guards_for_parameter (FStar_Pervasives_Native.fst orig_arg) arg xv)
in (uu____16368)::eqns_or_guards)
end
| uu____16369 -> begin
(

let uu____16370 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (uu____16370)::eqns_or_guards)
end)
in ((env3), ((xv)::arg_vars), (eqns), ((i + (Prims.parse_int "1")))))
end))
end)) ((env'), ([]), ([]), ((Prims.parse_int "0"))) uu____16266))
in (match (uu____16259) with
| (uu____16378, arg_vars, elim_eqns_or_guards, uu____16381) -> begin
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

let uu____16400 = (

let uu____16404 = (

let uu____16405 = (

let uu____16411 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____16417 = (

let uu____16418 = (

let uu____16421 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append elim_eqns_or_guards guards))
in ((ty_pred), (uu____16421)))
in (FStar_SMTEncoding_Util.mkImp uu____16418))
in ((((ty_pred)::[])::[]), (uu____16411), (uu____16417))))
in (FStar_SMTEncoding_Util.mkForall uu____16405))
in ((uu____16404), (FStar_Pervasives_Native.Some ("data constructor typing elim")), ((Prims.strcat "data_elim_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____16400))
in (

let subterm_ordering = (match ((FStar_Ident.lid_equals d FStar_Parser_Const.lextop_lid)) with
| true -> begin
(

let x = (

let uu____16434 = (varops.fresh "x")
in ((uu____16434), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (

let uu____16436 = (

let uu____16440 = (

let uu____16441 = (

let uu____16447 = (

let uu____16450 = (

let uu____16452 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in (uu____16452)::[])
in (uu____16450)::[])
in (

let uu____16455 = (

let uu____16456 = (

let uu____16459 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (

let uu____16460 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in ((uu____16459), (uu____16460))))
in (FStar_SMTEncoding_Util.mkImp uu____16456))
in ((uu____16447), ((x)::[]), (uu____16455))))
in (FStar_SMTEncoding_Util.mkForall uu____16441))
in (

let uu____16470 = (varops.mk_unique "lextop")
in ((uu____16440), (FStar_Pervasives_Native.Some ("lextop is top")), (uu____16470))))
in (FStar_SMTEncoding_Util.mkAssume uu____16436))))
end
| uu____16472 -> begin
(

let prec = (

let uu____16475 = (FStar_All.pipe_right vars (FStar_List.mapi (fun i v1 -> (match ((i < n_tps)) with
| true -> begin
[]
end
| uu____16491 -> begin
(

let uu____16492 = (

let uu____16493 = (FStar_SMTEncoding_Util.mkFreeV v1)
in (FStar_SMTEncoding_Util.mk_Precedes uu____16493 dapp1))
in (uu____16492)::[])
end))))
in (FStar_All.pipe_right uu____16475 FStar_List.flatten))
in (

let uu____16497 = (

let uu____16501 = (

let uu____16502 = (

let uu____16508 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____16514 = (

let uu____16515 = (

let uu____16518 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (uu____16518)))
in (FStar_SMTEncoding_Util.mkImp uu____16515))
in ((((ty_pred)::[])::[]), (uu____16508), (uu____16514))))
in (FStar_SMTEncoding_Util.mkForall uu____16502))
in ((uu____16501), (FStar_Pervasives_Native.Some ("subterm ordering")), ((Prims.strcat "subterm_ordering_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____16497)))
end)
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end)))
end)))
end
| uu____16528 -> begin
((

let uu____16530 = (

let uu____16531 = (FStar_Syntax_Print.lid_to_string d)
in (

let uu____16532 = (FStar_Syntax_Print.term_to_string head1)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" uu____16531 uu____16532)))
in (FStar_Errors.warn se.FStar_Syntax_Syntax.sigrng uu____16530));
(([]), ([]));
)
end))
end)))
in (

let uu____16535 = (encode_elim ())
in (match (uu____16535) with
| (decls2, elim) -> begin
(

let g = (

let uu____16547 = (

let uu____16549 = (

let uu____16551 = (

let uu____16553 = (

let uu____16555 = (

let uu____16556 = (

let uu____16562 = (

let uu____16564 = (

let uu____16565 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" uu____16565))
in FStar_Pervasives_Native.Some (uu____16564))
in ((ddtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (uu____16562)))
in FStar_SMTEncoding_Term.DeclFun (uu____16556))
in (uu____16555)::[])
in (

let uu____16568 = (

let uu____16570 = (

let uu____16572 = (

let uu____16574 = (

let uu____16576 = (

let uu____16578 = (

let uu____16580 = (

let uu____16581 = (

let uu____16585 = (

let uu____16586 = (

let uu____16592 = (FStar_SMTEncoding_Util.mkEq ((app), (dapp)))
in ((((app)::[])::[]), (vars), (uu____16592)))
in (FStar_SMTEncoding_Util.mkForall uu____16586))
in ((uu____16585), (FStar_Pervasives_Native.Some ("equality for proxy")), ((Prims.strcat "equality_tok_" ddtok))))
in (FStar_SMTEncoding_Util.mkAssume uu____16581))
in (

let uu____16599 = (

let uu____16601 = (

let uu____16602 = (

let uu____16606 = (

let uu____16607 = (

let uu____16613 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) vars')
in (

let uu____16619 = (FStar_SMTEncoding_Util.mkImp ((guard'), (ty_pred')))
in ((((ty_pred')::[])::[]), (uu____16613), (uu____16619))))
in (FStar_SMTEncoding_Util.mkForall uu____16607))
in ((uu____16606), (FStar_Pervasives_Native.Some ("data constructor typing intro")), ((Prims.strcat "data_typing_intro_" ddtok))))
in (FStar_SMTEncoding_Util.mkAssume uu____16602))
in (uu____16601)::[])
in (uu____16580)::uu____16599))
in ((FStar_SMTEncoding_Util.mkAssume ((tok_typing1), (FStar_Pervasives_Native.Some ("typing for data constructor proxy")), ((Prims.strcat "typing_tok_" ddtok)))))::uu____16578)
in (FStar_List.append uu____16576 elim))
in (FStar_List.append decls_pred uu____16574))
in (FStar_List.append decls_formals uu____16572))
in (FStar_List.append proxy_fresh uu____16570))
in (FStar_List.append uu____16553 uu____16568)))
in (FStar_List.append decls3 uu____16551))
in (FStar_List.append decls2 uu____16549))
in (FStar_List.append binder_decls uu____16547))
in (((FStar_List.append datacons g)), (env1)))
end)))))
end))
end)))
end))))))))
end)))
end))
end)))
end)))
end)))
and encode_sigelts : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun uu____16647 se -> (match (uu____16647) with
| (g, env1) -> begin
(

let uu____16659 = (encode_sigelt env1 se)
in (match (uu____16659) with
| (g', env2) -> begin
(((FStar_List.append g g')), (env2))
end))
end)) (([]), (env)))))


let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env bindings -> (

let encode_binding = (fun b uu____16697 -> (match (uu____16697) with
| (i, decls, env1) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (uu____16715) -> begin
(((i + (Prims.parse_int "1"))), ([]), (env1))
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env1.tcenv x.FStar_Syntax_Syntax.sort)
in ((

let uu____16720 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____16720) with
| true -> begin
(

let uu____16721 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____16722 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____16723 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" uu____16721 uu____16722 uu____16723))))
end
| uu____16724 -> begin
()
end));
(

let uu____16725 = (encode_term t1 env1)
in (match (uu____16725) with
| (t, decls') -> begin
(

let t_hash = (FStar_SMTEncoding_Term.hash_of_term t)
in (

let uu____16735 = (

let uu____16739 = (

let uu____16740 = (

let uu____16741 = (FStar_Util.digest_of_string t_hash)
in (Prims.strcat uu____16741 (Prims.strcat "_" (Prims.string_of_int i))))
in (Prims.strcat "x_" uu____16740))
in (new_term_constant_from_string env1 x uu____16739))
in (match (uu____16735) with
| (xxsym, xx, env') -> begin
(

let t2 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel FStar_Pervasives_Native.None xx t)
in (

let caption = (

let uu____16752 = (FStar_Options.log_queries ())
in (match (uu____16752) with
| true -> begin
(

let uu____16754 = (

let uu____16755 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____16756 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____16757 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" uu____16755 uu____16756 uu____16757))))
in FStar_Pervasives_Native.Some (uu____16754))
end
| uu____16758 -> begin
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
| FStar_TypeChecker_Env.Binding_lid (x, (uu____16768, t)) -> begin
(

let t_norm = (whnf env1 t)
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____16777 = (encode_free_var env1 fv t t_norm [])
in (match (uu____16777) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))))
end
| FStar_TypeChecker_Env.Binding_sig_inst (uu____16790, se, uu____16792) -> begin
(

let uu____16795 = (encode_sigelt env1 se)
in (match (uu____16795) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))
end
| FStar_TypeChecker_Env.Binding_sig (uu____16805, se) -> begin
(

let uu____16809 = (encode_sigelt env1 se)
in (match (uu____16809) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))
end)
end))
in (

let uu____16819 = (FStar_List.fold_right encode_binding bindings (((Prims.parse_int "0")), ([]), (env)))
in (match (uu____16819) with
| (uu____16831, decls, env1) -> begin
((decls), (env1))
end))))


let encode_labels = (fun labs -> (

let prefix1 = (FStar_All.pipe_right labs (FStar_List.map (fun uu____16883 -> (match (uu____16883) with
| (l, uu____16890, uu____16891) -> begin
FStar_SMTEncoding_Term.DeclFun ((((FStar_Pervasives_Native.fst l)), ([]), (FStar_SMTEncoding_Term.Bool_sort), (FStar_Pervasives_Native.None)))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun uu____16918 -> (match (uu____16918) with
| (l, uu____16926, uu____16927) -> begin
(

let uu____16932 = (FStar_All.pipe_left (fun _0_45 -> FStar_SMTEncoding_Term.Echo (_0_45)) (FStar_Pervasives_Native.fst l))
in (

let uu____16933 = (

let uu____16935 = (

let uu____16936 = (FStar_SMTEncoding_Util.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (uu____16936))
in (uu____16935)::[])
in (uu____16932)::uu____16933))
end))))
in ((prefix1), (suffix)))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (

let uu____16948 = (

let uu____16950 = (

let uu____16951 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (

let uu____16953 = (

let uu____16954 = (FStar_TypeChecker_Env.current_module tcenv)
in (FStar_All.pipe_right uu____16954 FStar_Ident.string_of_lid))
in {bindings = []; depth = (Prims.parse_int "0"); tcenv = tcenv; warn = true; cache = uu____16951; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true; current_module_name = uu____16953}))
in (uu____16950)::[])
in (FStar_ST.write last_env uu____16948)))


let get_env : FStar_Ident.lident  ->  FStar_TypeChecker_Env.env  ->  env_t = (fun cmn tcenv -> (

let uu____16966 = (FStar_ST.read last_env)
in (match (uu____16966) with
| [] -> begin
(failwith "No env; call init first!")
end
| (e)::uu____16972 -> begin
(

let uu___153_16974 = e
in (

let uu____16975 = (FStar_Ident.string_of_lid cmn)
in {bindings = uu___153_16974.bindings; depth = uu___153_16974.depth; tcenv = tcenv; warn = uu___153_16974.warn; cache = uu___153_16974.cache; nolabels = uu___153_16974.nolabels; use_zfuel_name = uu___153_16974.use_zfuel_name; encode_non_total_function_typ = uu___153_16974.encode_non_total_function_typ; current_module_name = uu____16975}))
end)))


let set_env : env_t  ->  Prims.unit = (fun env -> (

let uu____16980 = (FStar_ST.read last_env)
in (match (uu____16980) with
| [] -> begin
(failwith "Empty env stack")
end
| (uu____16985)::tl1 -> begin
(FStar_ST.write last_env ((env)::tl1))
end)))


let push_env : Prims.unit  ->  Prims.unit = (fun uu____16994 -> (

let uu____16995 = (FStar_ST.read last_env)
in (match (uu____16995) with
| [] -> begin
(failwith "Empty env stack")
end
| (hd1)::tl1 -> begin
(

let refs = (FStar_Util.smap_copy hd1.cache)
in (

let top = (

let uu___154_17006 = hd1
in {bindings = uu___154_17006.bindings; depth = uu___154_17006.depth; tcenv = uu___154_17006.tcenv; warn = uu___154_17006.warn; cache = refs; nolabels = uu___154_17006.nolabels; use_zfuel_name = uu___154_17006.use_zfuel_name; encode_non_total_function_typ = uu___154_17006.encode_non_total_function_typ; current_module_name = uu___154_17006.current_module_name})
in (FStar_ST.write last_env ((top)::(hd1)::tl1))))
end)))


let pop_env : Prims.unit  ->  Prims.unit = (fun uu____17013 -> (

let uu____17014 = (FStar_ST.read last_env)
in (match (uu____17014) with
| [] -> begin
(failwith "Popping an empty stack")
end
| (uu____17019)::tl1 -> begin
(FStar_ST.write last_env tl1)
end)))


let mark_env : Prims.unit  ->  Prims.unit = (fun uu____17028 -> (push_env ()))


let reset_mark_env : Prims.unit  ->  Prims.unit = (fun uu____17032 -> (pop_env ()))


let commit_mark_env : Prims.unit  ->  Prims.unit = (fun uu____17036 -> (

let uu____17037 = (FStar_ST.read last_env)
in (match (uu____17037) with
| (hd1)::(uu____17043)::tl1 -> begin
(FStar_ST.write last_env ((hd1)::tl1))
end
| uu____17049 -> begin
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


let open_fact_db_tags : env_t  ->  FStar_SMTEncoding_Term.fact_db_id Prims.list = (fun env -> [])


let place_decl_in_fact_dbs : env_t  ->  FStar_SMTEncoding_Term.fact_db_id Prims.list  ->  FStar_SMTEncoding_Term.decl  ->  FStar_SMTEncoding_Term.decl = (fun env fact_db_ids d -> (match (((fact_db_ids), (d))) with
| ((uu____17108)::uu____17109, FStar_SMTEncoding_Term.Assume (a)) -> begin
FStar_SMTEncoding_Term.Assume ((

let uu___155_17115 = a
in {FStar_SMTEncoding_Term.assumption_term = uu___155_17115.FStar_SMTEncoding_Term.assumption_term; FStar_SMTEncoding_Term.assumption_caption = uu___155_17115.FStar_SMTEncoding_Term.assumption_caption; FStar_SMTEncoding_Term.assumption_name = uu___155_17115.FStar_SMTEncoding_Term.assumption_name; FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids}))
end
| uu____17116 -> begin
d
end))


let fact_dbs_for_lid : env_t  ->  FStar_Ident.lid  ->  FStar_SMTEncoding_Term.fact_db_id Prims.list = (fun env lid -> (

let uu____17129 = (

let uu____17131 = (

let uu____17132 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in FStar_SMTEncoding_Term.Namespace (uu____17132))
in (

let uu____17133 = (open_fact_db_tags env)
in (uu____17131)::uu____17133))
in (FStar_SMTEncoding_Term.Name (lid))::uu____17129))


let encode_top_level_facts : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env se -> (

let fact_db_ids = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.collect (fact_dbs_for_lid env)))
in (

let uu____17150 = (encode_sigelt env se)
in (match (uu____17150) with
| (g, env1) -> begin
(

let g1 = (FStar_All.pipe_right g (FStar_List.map (place_decl_in_fact_dbs env1 fact_db_ids)))
in ((g1), (env1)))
end))))


let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (

let caption = (fun decls -> (

let uu____17177 = (FStar_Options.log_queries ())
in (match (uu____17177) with
| true -> begin
(

let uu____17179 = (

let uu____17180 = (

let uu____17181 = (

let uu____17182 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.map FStar_Syntax_Print.lid_to_string))
in (FStar_All.pipe_right uu____17182 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " uu____17181))
in FStar_SMTEncoding_Term.Caption (uu____17180))
in (uu____17179)::decls)
end
| uu____17187 -> begin
decls
end)))
in (

let env = (

let uu____17189 = (FStar_TypeChecker_Env.current_module tcenv)
in (get_env uu____17189 tcenv))
in (

let uu____17190 = (encode_top_level_facts env se)
in (match (uu____17190) with
| (decls, env1) -> begin
((set_env env1);
(

let uu____17199 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 uu____17199));
)
end)))))


let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____17210 -> begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in ((

let uu____17212 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____17212) with
| true -> begin
(

let uu____17213 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) Prims.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name uu____17213))
end
| uu____17218 -> begin
()
end));
(

let env = (get_env modul.FStar_Syntax_Syntax.name tcenv)
in (

let encode_signature = (fun env1 ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun uu____17243 se -> (match (uu____17243) with
| (g, env2) -> begin
(

let uu____17255 = (encode_top_level_facts env2 se)
in (match (uu____17255) with
| (g', env3) -> begin
(((FStar_List.append g g')), (env3))
end))
end)) (([]), (env1)))))
in (

let uu____17268 = (encode_signature (

let uu___156_17274 = env
in {bindings = uu___156_17274.bindings; depth = uu___156_17274.depth; tcenv = uu___156_17274.tcenv; warn = false; cache = uu___156_17274.cache; nolabels = uu___156_17274.nolabels; use_zfuel_name = uu___156_17274.use_zfuel_name; encode_non_total_function_typ = uu___156_17274.encode_non_total_function_typ; current_module_name = uu___156_17274.current_module_name}) modul.FStar_Syntax_Syntax.exports)
in (match (uu____17268) with
| (decls, env1) -> begin
(

let caption = (fun decls1 -> (

let uu____17286 = (FStar_Options.log_queries ())
in (match (uu____17286) with
| true -> begin
(

let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::decls1) ((FStar_SMTEncoding_Term.Caption ((Prims.strcat "End " msg)))::[])))
end
| uu____17289 -> begin
decls1
end)))
in ((set_env (

let uu___157_17293 = env1
in {bindings = uu___157_17293.bindings; depth = uu___157_17293.depth; tcenv = uu___157_17293.tcenv; warn = true; cache = uu___157_17293.cache; nolabels = uu___157_17293.nolabels; use_zfuel_name = uu___157_17293.use_zfuel_name; encode_non_total_function_typ = uu___157_17293.encode_non_total_function_typ; current_module_name = uu___157_17293.current_module_name}));
(

let uu____17295 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____17295) with
| true -> begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end
| uu____17296 -> begin
()
end));
(

let decls1 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls1));
))
end))));
)))


let encode_query : (Prims.unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_ErrorReporting.label Prims.list * FStar_SMTEncoding_Term.decl * FStar_SMTEncoding_Term.decl Prims.list) = (fun use_env_msg tcenv q -> ((

let uu____17333 = (

let uu____17334 = (FStar_TypeChecker_Env.current_module tcenv)
in uu____17334.FStar_Ident.str)
in (FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name uu____17333));
(

let env = (

let uu____17336 = (FStar_TypeChecker_Env.current_module tcenv)
in (get_env uu____17336 tcenv))
in (

let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (

let uu____17345 = (

let rec aux = (fun bindings1 -> (match (bindings1) with
| (FStar_TypeChecker_Env.Binding_var (x))::rest -> begin
(

let uu____17366 = (aux rest)
in (match (uu____17366) with
| (out, rest1) -> begin
(

let t = (

let uu____17384 = (FStar_Syntax_Util.destruct_typ_as_formula x.FStar_Syntax_Syntax.sort)
in (match (uu____17384) with
| FStar_Pervasives_Native.Some (uu____17388) -> begin
(

let uu____17389 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.refine uu____17389 x.FStar_Syntax_Syntax.sort))
end
| uu____17390 -> begin
x.FStar_Syntax_Syntax.sort
end))
in (

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
in (

let uu____17393 = (

let uu____17395 = (FStar_Syntax_Syntax.mk_binder (

let uu___158_17398 = x
in {FStar_Syntax_Syntax.ppname = uu___158_17398.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___158_17398.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in (uu____17395)::out)
in ((uu____17393), (rest1)))))
end))
end
| uu____17401 -> begin
(([]), (bindings1))
end))
in (

let uu____17405 = (aux bindings)
in (match (uu____17405) with
| (closing, bindings1) -> begin
(

let uu____17419 = (FStar_Syntax_Util.close_forall_no_univs (FStar_List.rev closing) q)
in ((uu____17419), (bindings1)))
end)))
in (match (uu____17345) with
| (q1, bindings1) -> begin
(

let uu____17432 = (

let uu____17435 = (FStar_List.filter (fun uu___125_17439 -> (match (uu___125_17439) with
| FStar_TypeChecker_Env.Binding_sig (uu____17440) -> begin
false
end
| uu____17444 -> begin
true
end)) bindings1)
in (encode_env_bindings env uu____17435))
in (match (uu____17432) with
| (env_decls, env1) -> begin
((

let uu____17455 = (((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTQuery"))))
in (match (uu____17455) with
| true -> begin
(

let uu____17456 = (FStar_Syntax_Print.term_to_string q1)
in (FStar_Util.print1 "Encoding query formula: %s\n" uu____17456))
end
| uu____17457 -> begin
()
end));
(

let uu____17458 = (encode_formula q1 env1)
in (match (uu____17458) with
| (phi, qdecls) -> begin
(

let uu____17470 = (

let uu____17473 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg uu____17473 phi))
in (match (uu____17470) with
| (labels, phi1) -> begin
(

let uu____17483 = (encode_labels labels)
in (match (uu____17483) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append env_decls (FStar_List.append label_prefix qdecls))
in (

let qry = (

let uu____17504 = (

let uu____17508 = (FStar_SMTEncoding_Util.mkNot phi1)
in (

let uu____17509 = (varops.mk_unique "@query")
in ((uu____17508), (FStar_Pervasives_Native.Some ("query")), (uu____17509))))
in (FStar_SMTEncoding_Util.mkAssume uu____17504))
in (

let suffix = (FStar_List.append label_suffix ((FStar_SMTEncoding_Term.Echo ("Done!"))::[]))
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

let uu____17524 = (FStar_TypeChecker_Env.current_module tcenv)
in (get_env uu____17524 tcenv))
in ((FStar_SMTEncoding_Z3.push "query");
(

let uu____17526 = (encode_formula q env)
in (match (uu____17526) with
| (f, uu____17530) -> begin
((FStar_SMTEncoding_Z3.pop "query");
(match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____17532) -> begin
true
end
| uu____17535 -> begin
false
end);
)
end));
)))




