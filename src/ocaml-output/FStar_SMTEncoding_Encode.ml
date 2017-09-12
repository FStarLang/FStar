
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


let vargs : 'Auu____71 'Auu____72 'Auu____73 . (('Auu____73, 'Auu____72) FStar_Util.either * 'Auu____71) Prims.list  ->  (('Auu____73, 'Auu____72) FStar_Util.either * 'Auu____71) Prims.list = (fun args -> (FStar_List.filter (fun uu___106_119 -> (match (uu___106_119) with
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

let uu___130_221 = a
in (

let uu____222 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = uu____222; FStar_Syntax_Syntax.index = uu___130_221.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___130_221.FStar_Syntax_Syntax.sort}))
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

let new_scope = (fun uu____946 -> (

let uu____947 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (

let uu____950 = (FStar_Util.smap_create (Prims.parse_int "100"))
in ((uu____947), (uu____950)))))
in (

let scopes = (

let uu____970 = (

let uu____981 = (new_scope ())
in (uu____981)::[])
in (FStar_Util.mk_ref uu____970))
in (

let mk_unique = (fun y -> (

let y1 = (escape y)
in (

let y2 = (

let uu____1022 = (

let uu____1025 = (FStar_ST.op_Bang scopes)
in (FStar_Util.find_map uu____1025 (fun uu____1111 -> (match (uu____1111) with
| (names1, uu____1123) -> begin
(FStar_Util.smap_try_find names1 y1)
end))))
in (match (uu____1022) with
| FStar_Pervasives_Native.None -> begin
y1
end
| FStar_Pervasives_Native.Some (uu____1132) -> begin
((FStar_Util.incr ctr);
(

let uu____1155 = (

let uu____1156 = (

let uu____1157 = (FStar_ST.op_Bang ctr)
in (Prims.string_of_int uu____1157))
in (Prims.strcat "__" uu____1156))
in (Prims.strcat y1 uu____1155));
)
end))
in (

let top_scope = (

let uu____1185 = (

let uu____1194 = (FStar_ST.op_Bang scopes)
in (FStar_List.hd uu____1194))
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1185))
in ((FStar_Util.smap_add top_scope y2 true);
y2;
)))))
in (

let new_var = (fun pp rn -> (FStar_All.pipe_left mk_unique (Prims.strcat pp.FStar_Ident.idText (Prims.strcat "__" (Prims.string_of_int rn)))))
in (

let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (

let next_id1 = (fun uu____1306 -> ((FStar_Util.incr ctr);
(FStar_ST.op_Bang ctr);
))
in (

let fresh1 = (fun pfx -> (

let uu____1357 = (

let uu____1358 = (next_id1 ())
in (FStar_All.pipe_left Prims.string_of_int uu____1358))
in (FStar_Util.format2 "%s_%s" pfx uu____1357)))
in (

let string_const = (fun s -> (

let uu____1363 = (

let uu____1366 = (FStar_ST.op_Bang scopes)
in (FStar_Util.find_map uu____1366 (fun uu____1452 -> (match (uu____1452) with
| (uu____1463, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))
in (match (uu____1363) with
| FStar_Pervasives_Native.Some (f) -> begin
f
end
| FStar_Pervasives_Native.None -> begin
(

let id = (next_id1 ())
in (

let f = (

let uu____1476 = (FStar_SMTEncoding_Util.mk_String_const id)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1476))
in (

let top_scope = (

let uu____1480 = (

let uu____1489 = (FStar_ST.op_Bang scopes)
in (FStar_List.hd uu____1489))
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1480))
in ((FStar_Util.smap_add top_scope s f);
f;
))))
end)))
in (

let push1 = (fun uu____1590 -> (

let uu____1591 = (

let uu____1602 = (new_scope ())
in (

let uu____1611 = (FStar_ST.op_Bang scopes)
in (uu____1602)::uu____1611))
in (FStar_ST.op_Colon_Equals scopes uu____1591)))
in (

let pop1 = (fun uu____1761 -> (

let uu____1762 = (

let uu____1773 = (FStar_ST.op_Bang scopes)
in (FStar_List.tl uu____1773))
in (FStar_ST.op_Colon_Equals scopes uu____1762)))
in (

let mark1 = (fun uu____1923 -> (push1 ()))
in (

let reset_mark1 = (fun uu____1927 -> (pop1 ()))
in (

let commit_mark1 = (fun uu____1931 -> (

let uu____1932 = (FStar_ST.op_Bang scopes)
in (match (uu____1932) with
| ((hd1, hd2))::((next1, next2))::tl1 -> begin
((FStar_Util.smap_fold hd1 (fun key value v1 -> (FStar_Util.smap_add next1 key value)) ());
(FStar_Util.smap_fold hd2 (fun key value v1 -> (FStar_Util.smap_add next2 key value)) ());
(FStar_ST.op_Colon_Equals scopes ((((next1), (next2)))::tl1));
)
end
| uu____2144 -> begin
(failwith "Impossible")
end)))
in {push = push1; pop = pop1; mark = mark1; reset_mark = reset_mark1; commit_mark = commit_mark1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; string_const = string_const; next_id = next_id1; mk_unique = mk_unique})))))))))))))))


let unmangle : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv = (fun x -> (

let uu___131_2159 = x
in (

let uu____2160 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = uu____2160; FStar_Syntax_Syntax.index = uu___131_2159.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___131_2159.FStar_Syntax_Syntax.sort})))

type binding =
| Binding_var of (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term)
| Binding_fvar of (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)


let uu___is_Binding_var : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Binding_var (_0) -> begin
true
end
| uu____2194 -> begin
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
| uu____2232 -> begin
false
end))


let __proj__Binding_fvar__item___0 : binding  ->  (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| Binding_fvar (_0) -> begin
_0
end))


let binder_of_eithervar : 'Auu____2283 'Auu____2284 . 'Auu____2284  ->  ('Auu____2284 * 'Auu____2283 FStar_Pervasives_Native.option) = (fun v1 -> ((v1), (FStar_Pervasives_Native.None)))

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


let mk_cache_entry : 'Auu____2598 . 'Auu____2598  ->  Prims.string  ->  FStar_SMTEncoding_Term.sort Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  cache_entry = (fun env tsym cvar_sorts t_decls -> (

let names1 = (FStar_All.pipe_right t_decls (FStar_List.collect (fun uu___107_2632 -> (match (uu___107_2632) with
| FStar_SMTEncoding_Term.Assume (a) -> begin
(a.FStar_SMTEncoding_Term.assumption_name)::[]
end
| uu____2636 -> begin
[]
end))))
in {cache_symbol_name = tsym; cache_symbol_arg_sorts = cvar_sorts; cache_symbol_decls = t_decls; cache_symbol_assumption_names = names1}))


let use_cache_entry : cache_entry  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun ce -> (FStar_SMTEncoding_Term.RetainAssumptions (ce.cache_symbol_assumption_names))::[])


let print_env : env_t  ->  Prims.string = (fun e -> (

let uu____2647 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun uu___108_2657 -> (match (uu___108_2657) with
| Binding_var (x, uu____2659) -> begin
(FStar_Syntax_Print.bv_to_string x)
end
| Binding_fvar (l, uu____2661, uu____2662, uu____2663) -> begin
(FStar_Syntax_Print.lid_to_string l)
end))))
in (FStar_All.pipe_right uu____2647 (FStar_String.concat ", "))))


let lookup_binding : 'Auu____2680 . env_t  ->  (binding  ->  'Auu____2680 FStar_Pervasives_Native.option)  ->  'Auu____2680 FStar_Pervasives_Native.option = (fun env f -> (FStar_Util.find_map env.bindings f))


let caption_t : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.string FStar_Pervasives_Native.option = (fun env t -> (

let uu____2710 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____2710) with
| true -> begin
(

let uu____2713 = (FStar_Syntax_Print.term_to_string t)
in FStar_Pervasives_Native.Some (uu____2713))
end
| uu____2714 -> begin
FStar_Pervasives_Native.None
end)))


let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (

let xsym = (varops.fresh x)
in (

let uu____2728 = (FStar_SMTEncoding_Util.mkFreeV ((xsym), (s)))
in ((xsym), (uu____2728)))))


let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (Prims.strcat "@x" (Prims.string_of_int env.depth))
in (

let y = (FStar_SMTEncoding_Util.mkFreeV ((ysym), (FStar_SMTEncoding_Term.Term_sort)))
in ((ysym), (y), ((

let uu___132_2746 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = (env.depth + (Prims.parse_int "1")); tcenv = uu___132_2746.tcenv; warn = uu___132_2746.warn; cache = uu___132_2746.cache; nolabels = uu___132_2746.nolabels; use_zfuel_name = uu___132_2746.use_zfuel_name; encode_non_total_function_typ = uu___132_2746.encode_non_total_function_typ; current_module_name = uu___132_2746.current_module_name}))))))


let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let uu___133_2766 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = uu___133_2766.depth; tcenv = uu___133_2766.tcenv; warn = uu___133_2766.warn; cache = uu___133_2766.cache; nolabels = uu___133_2766.nolabels; use_zfuel_name = uu___133_2766.use_zfuel_name; encode_non_total_function_typ = uu___133_2766.encode_non_total_function_typ; current_module_name = uu___133_2766.current_module_name}))))))


let new_term_constant_from_string : env_t  ->  FStar_Syntax_Syntax.bv  ->  Prims.string  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x str -> (

let ysym = (varops.mk_unique str)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let uu___134_2790 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = uu___134_2790.depth; tcenv = uu___134_2790.tcenv; warn = uu___134_2790.warn; cache = uu___134_2790.cache; nolabels = uu___134_2790.nolabels; use_zfuel_name = uu___134_2790.use_zfuel_name; encode_non_total_function_typ = uu___134_2790.encode_non_total_function_typ; current_module_name = uu___134_2790.current_module_name}))))))


let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (

let uu___135_2803 = env
in {bindings = (Binding_var (((x), (t))))::env.bindings; depth = uu___135_2803.depth; tcenv = uu___135_2803.tcenv; warn = uu___135_2803.warn; cache = uu___135_2803.cache; nolabels = uu___135_2803.nolabels; use_zfuel_name = uu___135_2803.use_zfuel_name; encode_non_total_function_typ = uu___135_2803.encode_non_total_function_typ; current_module_name = uu___135_2803.current_module_name}))


let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let aux = (fun a' -> (lookup_binding env (fun uu___109_2829 -> (match (uu___109_2829) with
| Binding_var (b, t) when (FStar_Syntax_Syntax.bv_eq b a') -> begin
FStar_Pervasives_Native.Some (((b), (t)))
end
| uu____2842 -> begin
FStar_Pervasives_Native.None
end))))
in (

let uu____2847 = (aux a)
in (match (uu____2847) with
| FStar_Pervasives_Native.None -> begin
(

let a2 = (unmangle a)
in (

let uu____2859 = (aux a2)
in (match (uu____2859) with
| FStar_Pervasives_Native.None -> begin
(

let uu____2870 = (

let uu____2871 = (FStar_Syntax_Print.bv_to_string a2)
in (

let uu____2872 = (print_env env)
in (FStar_Util.format2 "Bound term variable not found (after unmangling): %s in environment: %s" uu____2871 uu____2872)))
in (failwith uu____2870))
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

let uu____2901 = (

let uu___136_2902 = env
in (

let uu____2903 = (

let uu____2906 = (

let uu____2907 = (

let uu____2920 = (

let uu____2923 = (FStar_SMTEncoding_Util.mkApp ((ftok), ([])))
in (FStar_All.pipe_left (fun _0_41 -> FStar_Pervasives_Native.Some (_0_41)) uu____2923))
in ((x), (fname), (uu____2920), (FStar_Pervasives_Native.None)))
in Binding_fvar (uu____2907))
in (uu____2906)::env.bindings)
in {bindings = uu____2903; depth = uu___136_2902.depth; tcenv = uu___136_2902.tcenv; warn = uu___136_2902.warn; cache = uu___136_2902.cache; nolabels = uu___136_2902.nolabels; use_zfuel_name = uu___136_2902.use_zfuel_name; encode_non_total_function_typ = uu___136_2902.encode_non_total_function_typ; current_module_name = uu___136_2902.current_module_name}))
in ((fname), (ftok), (uu____2901))))))


let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option) FStar_Pervasives_Native.option = (fun env a -> (lookup_binding env (fun uu___110_2967 -> (match (uu___110_2967) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
FStar_Pervasives_Native.Some (((t1), (t2), (t3)))
end
| uu____3006 -> begin
FStar_Pervasives_Native.None
end))))


let contains_name : env_t  ->  Prims.string  ->  Prims.bool = (fun env s -> (

let uu____3025 = (lookup_binding env (fun uu___111_3033 -> (match (uu___111_3033) with
| Binding_fvar (b, t1, t2, t3) when (b.FStar_Ident.str = s) -> begin
FStar_Pervasives_Native.Some (())
end
| uu____3048 -> begin
FStar_Pervasives_Native.None
end)))
in (FStar_All.pipe_right uu____3025 FStar_Option.isSome)))


let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option) = (fun env a -> (

let uu____3069 = (try_lookup_lid env a)
in (match (uu____3069) with
| FStar_Pervasives_Native.None -> begin
(

let uu____3102 = (

let uu____3103 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" uu____3103))
in (failwith uu____3102))
end
| FStar_Pervasives_Native.Some (s) -> begin
s
end)))


let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  env_t = (fun env x fname ftok -> (

let uu___137_3155 = env
in {bindings = (Binding_fvar (((x), (fname), (ftok), (FStar_Pervasives_Native.None))))::env.bindings; depth = uu___137_3155.depth; tcenv = uu___137_3155.tcenv; warn = uu___137_3155.warn; cache = uu___137_3155.cache; nolabels = uu___137_3155.nolabels; use_zfuel_name = uu___137_3155.use_zfuel_name; encode_non_total_function_typ = uu___137_3155.encode_non_total_function_typ; current_module_name = uu___137_3155.current_module_name}))


let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (

let uu____3172 = (lookup_lid env x)
in (match (uu____3172) with
| (t1, t2, uu____3185) -> begin
(

let t3 = (

let uu____3195 = (

let uu____3202 = (

let uu____3205 = (FStar_SMTEncoding_Util.mkApp (("ZFuel"), ([])))
in (uu____3205)::[])
in ((f), (uu____3202)))
in (FStar_SMTEncoding_Util.mkApp uu____3195))
in (

let uu___138_3210 = env
in {bindings = (Binding_fvar (((x), (t1), (t2), (FStar_Pervasives_Native.Some (t3)))))::env.bindings; depth = uu___138_3210.depth; tcenv = uu___138_3210.tcenv; warn = uu___138_3210.warn; cache = uu___138_3210.cache; nolabels = uu___138_3210.nolabels; use_zfuel_name = uu___138_3210.use_zfuel_name; encode_non_total_function_typ = uu___138_3210.encode_non_total_function_typ; current_module_name = uu___138_3210.current_module_name}))
end)))


let try_lookup_free_var : env_t  ->  FStar_Ident.lident  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun env l -> (

let uu____3225 = (try_lookup_lid env l)
in (match (uu____3225) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (name, sym, zf_opt) -> begin
(match (zf_opt) with
| FStar_Pervasives_Native.Some (f) when env.use_zfuel_name -> begin
FStar_Pervasives_Native.Some (f)
end
| uu____3274 -> begin
(match (sym) with
| FStar_Pervasives_Native.Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (uu____3282, (fuel)::[]) -> begin
(

let uu____3286 = (

let uu____3287 = (

let uu____3288 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right uu____3288 FStar_Pervasives_Native.fst))
in (FStar_Util.starts_with uu____3287 "fuel"))
in (match (uu____3286) with
| true -> begin
(

let uu____3291 = (

let uu____3292 = (FStar_SMTEncoding_Util.mkFreeV ((name), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_ApplyTF uu____3292 fuel))
in (FStar_All.pipe_left (fun _0_42 -> FStar_Pervasives_Native.Some (_0_42)) uu____3291))
end
| uu____3295 -> begin
FStar_Pervasives_Native.Some (t)
end))
end
| uu____3296 -> begin
FStar_Pervasives_Native.Some (t)
end)
end
| uu____3297 -> begin
FStar_Pervasives_Native.None
end)
end)
end)))


let lookup_free_var : env_t  ->  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let uu____3312 = (try_lookup_free_var env a.FStar_Syntax_Syntax.v)
in (match (uu____3312) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let uu____3316 = (

let uu____3317 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" uu____3317))
in (failwith uu____3316))
end)))


let lookup_free_var_name : env_t  ->  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t  ->  Prims.string = (fun env a -> (

let uu____3330 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (uu____3330) with
| (x, uu____3342, uu____3343) -> begin
x
end)))


let lookup_free_var_sym : env_t  ->  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t  ->  (FStar_SMTEncoding_Term.op * FStar_SMTEncoding_Term.term Prims.list) = (fun env a -> (

let uu____3370 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (uu____3370) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| FStar_Pervasives_Native.Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.freevars = uu____3406; FStar_SMTEncoding_Term.rng = uu____3407}) when env.use_zfuel_name -> begin
((g), (zf))
end
| uu____3422 -> begin
(match (sym) with
| FStar_Pervasives_Native.None -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end
| FStar_Pervasives_Native.Some (sym1) -> begin
(match (sym1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, (fuel)::[]) -> begin
((g), ((fuel)::[]))
end
| uu____3446 -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end)
end)
end)
end)))


let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun uu___112_3464 -> (match (uu___112_3464) with
| Binding_fvar (uu____3467, nm', tok, uu____3470) when (nm = nm') -> begin
tok
end
| uu____3479 -> begin
FStar_Pervasives_Native.None
end))))


let mkForall_fuel' : 'Auu____3486 . 'Auu____3486  ->  (FStar_SMTEncoding_Term.pat Prims.list Prims.list * FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (fun n1 uu____3504 -> (match (uu____3504) with
| (pats, vars, body) -> begin
(

let fallback = (fun uu____3529 -> (FStar_SMTEncoding_Util.mkForall ((pats), (vars), (body))))
in (

let uu____3534 = (FStar_Options.unthrottle_inductives ())
in (match (uu____3534) with
| true -> begin
(fallback ())
end
| uu____3535 -> begin
(

let uu____3536 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____3536) with
| (fsym, fterm) -> begin
(

let add_fuel1 = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Util.mkApp (("HasTypeFuel"), ((fterm)::args)))
end
| uu____3567 -> begin
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

let uu____3588 = (add_fuel1 guards)
in (FStar_SMTEncoding_Util.mk_and_l uu____3588))
end
| uu____3591 -> begin
(

let uu____3592 = (add_fuel1 ((guard)::[]))
in (FStar_All.pipe_right uu____3592 FStar_List.hd))
end)
in (FStar_SMTEncoding_Util.mkImp ((guard1), (body'))))
end
| uu____3597 -> begin
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
| FStar_Syntax_Syntax.Tm_arrow (uu____3641) -> begin
true
end
| FStar_Syntax_Syntax.Tm_refine (uu____3654) -> begin
true
end
| FStar_Syntax_Syntax.Tm_bvar (uu____3661) -> begin
true
end
| FStar_Syntax_Syntax.Tm_uvar (uu____3662) -> begin
true
end
| FStar_Syntax_Syntax.Tm_abs (uu____3679) -> begin
true
end
| FStar_Syntax_Syntax.Tm_constant (uu____3696) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____3698 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____3698 FStar_Option.isNone))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____3716; FStar_Syntax_Syntax.vars = uu____3717}, uu____3718) -> begin
(

let uu____3739 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____3739 FStar_Option.isNone))
end
| uu____3756 -> begin
false
end)))


let head_redex : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let uu____3765 = (

let uu____3766 = (FStar_Syntax_Util.un_uinst t)
in uu____3766.FStar_Syntax_Syntax.n)
in (match (uu____3765) with
| FStar_Syntax_Syntax.Tm_abs (uu____3769, uu____3770, FStar_Pervasives_Native.Some (rc)) -> begin
(((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_Tot_lid) || (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_GTot_lid)) || (FStar_List.existsb (fun uu___113_3791 -> (match (uu___113_3791) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____3792 -> begin
false
end)) rc.FStar_Syntax_Syntax.residual_flags))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____3794 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____3794 FStar_Option.isSome))
end
| uu____3811 -> begin
false
end)))


let whnf : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____3820 = (head_normal env t)
in (match (uu____3820) with
| true -> begin
t
end
| uu____3821 -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
end)))


let norm : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t))


let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____3834 = (

let uu____3835 = (FStar_Syntax_Syntax.null_binder t)
in (uu____3835)::[])
in (

let uu____3836 = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Util.abs uu____3834 uu____3836 FStar_Pervasives_Native.None))))


let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((FStar_Pervasives_Native.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(

let uu____3876 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out uu____3876))
end
| s -> begin
(

let uu____3881 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Util.mk_ApplyTT out uu____3881))
end)) e)))


let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)))


let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun uu___114_3899 -> (match (uu___114_3899) with
| FStar_SMTEncoding_Term.Var ("ApplyTT") -> begin
true
end
| FStar_SMTEncoding_Term.Var ("ApplyTF") -> begin
true
end
| uu____3900 -> begin
false
end))


let is_an_eta_expansion : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun env vars body -> (

let rec check_partial_applications = (fun t xs -> (match (((t.FStar_SMTEncoding_Term.tm), (xs))) with
| (FStar_SMTEncoding_Term.App (app, (f)::({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.freevars = uu____3939; FStar_SMTEncoding_Term.rng = uu____3940})::[]), (x)::xs1) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(check_partial_applications f xs1)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), uu____3963) -> begin
(

let uu____3972 = (((FStar_List.length args) = (FStar_List.length xs)) && (FStar_List.forall2 (fun a v1 -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v1)
end
| uu____3983 -> begin
false
end)) args (FStar_List.rev xs)))
in (match (uu____3972) with
| true -> begin
(tok_of_name env f)
end
| uu____3986 -> begin
FStar_Pervasives_Native.None
end))
end
| (uu____3987, []) -> begin
(

let fvs = (FStar_SMTEncoding_Term.free_variables t)
in (

let uu____3991 = (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (

let uu____3995 = (FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)
in (not (uu____3995))))))
in (match (uu____3991) with
| true -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____3998 -> begin
FStar_Pervasives_Native.None
end)))
end
| uu____3999 -> begin
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
| uu____4229 -> begin
false
end))


let encode_const : FStar_Const.sconst  ->  FStar_SMTEncoding_Term.term = (fun uu___115_4233 -> (match (uu___115_4233) with
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

let uu____4235 = (

let uu____4242 = (

let uu____4245 = (

let uu____4246 = (FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c))
in (FStar_SMTEncoding_Term.boxInt uu____4246))
in (uu____4245)::[])
in (("FStar.Char.Char"), (uu____4242)))
in (FStar_SMTEncoding_Util.mkApp uu____4235))
end
| FStar_Const.Const_int (i, FStar_Pervasives_Native.None) -> begin
(

let uu____4260 = (FStar_SMTEncoding_Util.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt uu____4260))
end
| FStar_Const.Const_int (i, FStar_Pervasives_Native.Some (uu____4262)) -> begin
(failwith "Machine integers should be desugared")
end
| FStar_Const.Const_string (s, uu____4278) -> begin
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

let uu____4281 = (

let uu____4282 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" uu____4282))
in (failwith uu____4281))
end))


let as_function_typ : env_t  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (

let rec aux = (fun norm1 t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____4303) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_refine (uu____4316) -> begin
(

let uu____4323 = (FStar_Syntax_Util.unrefine t1)
in (aux true uu____4323))
end
| uu____4324 -> begin
(match (norm1) with
| true -> begin
(

let uu____4325 = (whnf env t1)
in (aux false uu____4325))
end
| uu____4326 -> begin
(

let uu____4327 = (

let uu____4328 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (

let uu____4329 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" uu____4328 uu____4329)))
in (failwith uu____4327))
end)
end)))
in (aux true t0)))


let curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun k -> (

let k1 = (FStar_Syntax_Subst.compress k)
in (match (k1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| uu____4361 -> begin
(

let uu____4362 = (FStar_Syntax_Syntax.mk_Total k1)
in (([]), (uu____4362)))
end)))


let is_arithmetic_primitive : 'Auu____4379 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  'Auu____4379 Prims.list  ->  Prims.bool = (fun head1 args -> (match (((head1.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____4399)::(uu____4400)::[]) -> begin
(((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Addition) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Subtraction)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Multiply)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Division)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Modulus))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____4404)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus)
end
| uu____4407 -> begin
false
end))


let isInteger : FStar_Syntax_Syntax.term'  ->  Prims.bool = (fun tm -> (match (tm) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (n1, FStar_Pervasives_Native.None)) -> begin
true
end
| uu____4429 -> begin
false
end))


let getInteger : FStar_Syntax_Syntax.term'  ->  Prims.int = (fun tm -> (match (tm) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (n1, FStar_Pervasives_Native.None)) -> begin
(FStar_Util.int_of_string n1)
end
| uu____4445 -> begin
(failwith "Expected an Integer term")
end))


let is_BitVector_primitive : 'Auu____4452 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____4452) Prims.list  ->  Prims.bool = (fun head1 args -> (match (((head1.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((sz_arg, uu____4491))::(uu____4492)::(uu____4493)::[]) -> begin
((((((((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_and_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_xor_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_or_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_shift_left_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_shift_right_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_udiv_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_mod_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_uext_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_mul_lid)) && (isInteger sz_arg.FStar_Syntax_Syntax.n))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((sz_arg, uu____4544))::(uu____4545)::[]) -> begin
(((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_to_nat_lid)) && (isInteger sz_arg.FStar_Syntax_Syntax.n))
end
| uu____4582 -> begin
false
end))


let rec encode_binders : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> ((

let uu____4791 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____4791) with
| true -> begin
(

let uu____4792 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" uu____4792))
end
| uu____4793 -> begin
()
end));
(

let uu____4794 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____4878 b -> (match (uu____4878) with
| (vars, guards, env1, decls, names1) -> begin
(

let uu____4957 = (

let x = (unmangle (FStar_Pervasives_Native.fst b))
in (

let uu____4973 = (gen_term_var env1 x)
in (match (uu____4973) with
| (xxsym, xx, env') -> begin
(

let uu____4997 = (

let uu____5002 = (norm env1 x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt uu____5002 env1 xx))
in (match (uu____4997) with
| (guard_x_t, decls') -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (guard_x_t), (env'), (decls'), (x))
end))
end)))
in (match (uu____4957) with
| (v1, g, env2, decls', n1) -> begin
(((v1)::vars), ((g)::guards), (env2), ((FStar_List.append decls decls')), ((n1)::names1))
end))
end)) (([]), ([]), (env), ([]), ([]))))
in (match (uu____4794) with
| (vars, guards, env1, decls, names1) -> begin
(((FStar_List.rev vars)), ((FStar_List.rev guards)), (env1), (decls), ((FStar_List.rev names1)))
end));
))
and encode_term_pred : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let uu____5161 = (encode_term t env)
in (match (uu____5161) with
| (t1, decls) -> begin
(

let uu____5172 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1)
in ((uu____5172), (decls)))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let uu____5183 = (encode_term t env)
in (match (uu____5183) with
| (t1, decls) -> begin
(match (fuel_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5198 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t1)
in ((uu____5198), (decls)))
end
| FStar_Pervasives_Native.Some (f) -> begin
(

let uu____5200 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1)
in ((uu____5200), (decls)))
end)
end)))
and encode_arith_term : env_t  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.args  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun env head1 args_e -> (

let uu____5206 = (encode_args args_e env)
in (match (uu____5206) with
| (arg_tms, decls) -> begin
(

let head_fv = (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____5225 -> begin
(failwith "Impossible")
end)
in (

let unary = (fun arg_tms1 -> (

let uu____5234 = (FStar_List.hd arg_tms1)
in (FStar_SMTEncoding_Term.unboxInt uu____5234)))
in (

let binary = (fun arg_tms1 -> (

let uu____5247 = (

let uu____5248 = (FStar_List.hd arg_tms1)
in (FStar_SMTEncoding_Term.unboxInt uu____5248))
in (

let uu____5249 = (

let uu____5250 = (

let uu____5251 = (FStar_List.tl arg_tms1)
in (FStar_List.hd uu____5251))
in (FStar_SMTEncoding_Term.unboxInt uu____5250))
in ((uu____5247), (uu____5249)))))
in (

let mk_default = (fun uu____5257 -> (

let uu____5258 = (lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name)
in (match (uu____5258) with
| (fname, fuel_args) -> begin
(FStar_SMTEncoding_Util.mkApp' ((fname), ((FStar_List.append fuel_args arg_tms))))
end)))
in (

let mk_l = (fun op mk_args ts -> (

let uu____5309 = (FStar_Options.smtencoding_l_arith_native ())
in (match (uu____5309) with
| true -> begin
(

let uu____5310 = (

let uu____5311 = (mk_args ts)
in (op uu____5311))
in (FStar_All.pipe_right uu____5310 FStar_SMTEncoding_Term.boxInt))
end
| uu____5312 -> begin
(mk_default ())
end)))
in (

let mk_nl = (fun nm op ts -> (

let uu____5340 = (FStar_Options.smtencoding_nl_arith_wrapped ())
in (match (uu____5340) with
| true -> begin
(

let uu____5341 = (binary ts)
in (match (uu____5341) with
| (t1, t2) -> begin
(

let uu____5348 = (FStar_SMTEncoding_Util.mkApp ((nm), ((t1)::(t2)::[])))
in (FStar_All.pipe_right uu____5348 FStar_SMTEncoding_Term.boxInt))
end))
end
| uu____5351 -> begin
(

let uu____5352 = (FStar_Options.smtencoding_nl_arith_native ())
in (match (uu____5352) with
| true -> begin
(

let uu____5353 = (op (binary ts))
in (FStar_All.pipe_right uu____5353 FStar_SMTEncoding_Term.boxInt))
end
| uu____5354 -> begin
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

let uu____5484 = (

let uu____5493 = (FStar_List.tryFind (fun uu____5515 -> (match (uu____5515) with
| (l, uu____5525) -> begin
(FStar_Syntax_Syntax.fv_eq_lid head_fv l)
end)) ops)
in (FStar_All.pipe_right uu____5493 FStar_Util.must))
in (match (uu____5484) with
| (uu____5564, op) -> begin
(

let uu____5574 = (op arg_tms)
in ((uu____5574), (decls)))
end)))))))))))))))
end)))
and encode_BitVector_term : env_t  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.arg Prims.list  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list) = (fun env head1 args_e -> (

let uu____5582 = (FStar_List.hd args_e)
in (match (uu____5582) with
| (tm_sz, uu____5590) -> begin
(

let sz = (getInteger tm_sz.FStar_Syntax_Syntax.n)
in (

let sz_key = (FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz))
in (

let sz_decls = (

let uu____5600 = (FStar_Util.smap_try_find env.cache sz_key)
in (match (uu____5600) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
[]
end
| FStar_Pervasives_Native.None -> begin
(

let t_decls = (FStar_SMTEncoding_Term.mkBvConstructor sz)
in ((

let uu____5608 = (mk_cache_entry env "" [] [])
in (FStar_Util.smap_add env.cache sz_key uu____5608));
t_decls;
))
end))
in (

let uu____5609 = (match (((head1.FStar_Syntax_Syntax.n), (args_e))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____5629)::((sz_arg, uu____5631))::(uu____5632)::[]) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_uext_lid) && (isInteger sz_arg.FStar_Syntax_Syntax.n)) -> begin
(

let uu____5681 = (

let uu____5684 = (FStar_List.tail args_e)
in (FStar_List.tail uu____5684))
in (

let uu____5687 = (

let uu____5690 = (getInteger sz_arg.FStar_Syntax_Syntax.n)
in FStar_Pervasives_Native.Some (uu____5690))
in ((uu____5681), (uu____5687))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____5696)::((sz_arg, uu____5698))::(uu____5699)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_uext_lid) -> begin
(

let uu____5748 = (

let uu____5749 = (FStar_Syntax_Print.term_to_string sz_arg)
in (FStar_Util.format1 "Not a constant bitvector extend size: %s" uu____5749))
in (failwith uu____5748))
end
| uu____5758 -> begin
(

let uu____5765 = (FStar_List.tail args_e)
in ((uu____5765), (FStar_Pervasives_Native.None)))
end)
in (match (uu____5609) with
| (arg_tms, ext_sz) -> begin
(

let uu____5788 = (encode_args arg_tms env)
in (match (uu____5788) with
| (arg_tms1, decls) -> begin
(

let head_fv = (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____5809 -> begin
(failwith "Impossible")
end)
in (

let unary = (fun arg_tms2 -> (

let uu____5818 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____5818)))
in (

let unary_arith = (fun arg_tms2 -> (

let uu____5827 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxInt uu____5827)))
in (

let binary = (fun arg_tms2 -> (

let uu____5840 = (

let uu____5841 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____5841))
in (

let uu____5842 = (

let uu____5843 = (

let uu____5844 = (FStar_List.tl arg_tms2)
in (FStar_List.hd uu____5844))
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____5843))
in ((uu____5840), (uu____5842)))))
in (

let binary_arith = (fun arg_tms2 -> (

let uu____5859 = (

let uu____5860 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____5860))
in (

let uu____5861 = (

let uu____5862 = (

let uu____5863 = (FStar_List.tl arg_tms2)
in (FStar_List.hd uu____5863))
in (FStar_SMTEncoding_Term.unboxInt uu____5862))
in ((uu____5859), (uu____5861)))))
in (

let mk_bv = (fun op mk_args resBox ts -> (

let uu____5912 = (

let uu____5913 = (mk_args ts)
in (op uu____5913))
in (FStar_All.pipe_right uu____5912 resBox)))
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

let uu____6003 = (

let uu____6006 = (match (ext_sz) with
| FStar_Pervasives_Native.Some (x) -> begin
x
end
| FStar_Pervasives_Native.None -> begin
(failwith "impossible")
end)
in (FStar_SMTEncoding_Util.mkBvUext uu____6006))
in (

let uu____6008 = (

let uu____6011 = (

let uu____6012 = (match (ext_sz) with
| FStar_Pervasives_Native.Some (x) -> begin
x
end
| FStar_Pervasives_Native.None -> begin
(failwith "impossible")
end)
in (sz + uu____6012))
in (FStar_SMTEncoding_Term.boxBitVec uu____6011))
in (mk_bv uu____6003 unary uu____6008 arg_tms2))))
in (

let to_int = (mk_bv FStar_SMTEncoding_Util.mkBvToNat unary FStar_SMTEncoding_Term.boxInt)
in (

let bv_to = (mk_bv (FStar_SMTEncoding_Util.mkNatToBv sz) unary_arith (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let ops = (((FStar_Parser_Const.bv_and_lid), (bv_and)))::(((FStar_Parser_Const.bv_xor_lid), (bv_xor)))::(((FStar_Parser_Const.bv_or_lid), (bv_or)))::(((FStar_Parser_Const.bv_shift_left_lid), (bv_shl)))::(((FStar_Parser_Const.bv_shift_right_lid), (bv_shr)))::(((FStar_Parser_Const.bv_udiv_lid), (bv_udiv)))::(((FStar_Parser_Const.bv_mod_lid), (bv_mod)))::(((FStar_Parser_Const.bv_mul_lid), (bv_mul)))::(((FStar_Parser_Const.bv_ult_lid), (bv_ult)))::(((FStar_Parser_Const.bv_uext_lid), (bv_uext)))::(((FStar_Parser_Const.bv_to_nat_lid), (to_int)))::(((FStar_Parser_Const.nat_to_bv_lid), (bv_to)))::[]
in (

let uu____6187 = (

let uu____6196 = (FStar_List.tryFind (fun uu____6218 -> (match (uu____6218) with
| (l, uu____6228) -> begin
(FStar_Syntax_Syntax.fv_eq_lid head_fv l)
end)) ops)
in (FStar_All.pipe_right uu____6196 FStar_Util.must))
in (match (uu____6187) with
| (uu____6269, op) -> begin
(

let uu____6279 = (op arg_tms1)
in ((uu____6279), ((FStar_List.append sz_decls decls))))
end)))))))))))))))))))))
end))
end)))))
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let t0 = (FStar_Syntax_Subst.compress t)
in ((

let uu____6290 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____6290) with
| true -> begin
(

let uu____6291 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____6292 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____6293 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" uu____6291 uu____6292 uu____6293))))
end
| uu____6294 -> begin
()
end));
(match (t0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____6299) -> begin
(

let uu____6324 = (

let uu____6325 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____6326 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____6327 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____6328 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6325 uu____6326 uu____6327 uu____6328)))))
in (failwith uu____6324))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____6333 = (

let uu____6334 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____6335 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____6336 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____6337 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6334 uu____6335 uu____6336 uu____6337)))))
in (failwith uu____6333))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____6343 = (

let uu____6344 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" uu____6344))
in (failwith uu____6343))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, k, uu____6351) -> begin
(encode_term t1 env)
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____6393) -> begin
(encode_term t1 env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t1 = (lookup_term_var env x)
in ((t1), ([])))
end
| FStar_Syntax_Syntax.Tm_fvar (v1) -> begin
(

let uu____6403 = (lookup_free_var env v1.FStar_Syntax_Syntax.fv_name)
in ((uu____6403), ([])))
end
| FStar_Syntax_Syntax.Tm_type (uu____6406) -> begin
((FStar_SMTEncoding_Term.mk_Term_type), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____6410) -> begin
(encode_term t1 env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____6416 = (encode_const c)
in ((uu____6416), ([])))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let module_name = env.current_module_name
in (

let uu____6438 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____6438) with
| (binders1, res) -> begin
(

let uu____6449 = ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res))
in (match (uu____6449) with
| true -> begin
(

let uu____6454 = (encode_binders FStar_Pervasives_Native.None binders1 env)
in (match (uu____6454) with
| (vars, guards, env', decls, uu____6479) -> begin
(

let fsym = (

let uu____6497 = (varops.fresh "f")
in ((uu____6497), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV fsym)
in (

let app = (mk_Apply f vars)
in (

let uu____6500 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post (

let uu___139_6509 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___139_6509.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___139_6509.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___139_6509.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___139_6509.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___139_6509.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___139_6509.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___139_6509.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___139_6509.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___139_6509.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___139_6509.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___139_6509.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___139_6509.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___139_6509.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___139_6509.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___139_6509.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___139_6509.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___139_6509.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___139_6509.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___139_6509.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___139_6509.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___139_6509.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.type_of = uu___139_6509.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___139_6509.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___139_6509.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___139_6509.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___139_6509.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___139_6509.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___139_6509.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___139_6509.FStar_TypeChecker_Env.identifier_info}) res)
in (match (uu____6500) with
| (pre_opt, res_t) -> begin
(

let uu____6520 = (encode_term_pred FStar_Pervasives_Native.None res_t env' app)
in (match (uu____6520) with
| (res_pred, decls') -> begin
(

let uu____6531 = (match (pre_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____6544 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____6544), ([])))
end
| FStar_Pervasives_Native.Some (pre) -> begin
(

let uu____6548 = (encode_formula pre env')
in (match (uu____6548) with
| (guard, decls0) -> begin
(

let uu____6561 = (FStar_SMTEncoding_Util.mk_and_l ((guard)::guards))
in ((uu____6561), (decls0)))
end))
end)
in (match (uu____6531) with
| (guards1, guard_decls) -> begin
(

let t_interp = (

let uu____6573 = (

let uu____6584 = (FStar_SMTEncoding_Util.mkImp ((guards1), (res_pred)))
in ((((app)::[])::[]), (vars), (uu____6584)))
in (FStar_SMTEncoding_Util.mkForall uu____6573))
in (

let cvars = (

let uu____6602 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right uu____6602 (FStar_List.filter (fun uu____6616 -> (match (uu____6616) with
| (x, uu____6622) -> begin
(x <> (FStar_Pervasives_Native.fst fsym))
end)))))
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), ((fsym)::cvars), (t_interp)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____6641 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____6641) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
(

let uu____6649 = (

let uu____6650 = (

let uu____6657 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((cache_entry.cache_symbol_name), (uu____6657)))
in (FStar_SMTEncoding_Util.mkApp uu____6650))
in ((uu____6649), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append guard_decls (use_cache_entry cache_entry)))))))
end
| FStar_Pervasives_Native.None -> begin
(

let tsym = (

let uu____6677 = (

let uu____6678 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_arrow_" uu____6678))
in (varops.mk_unique uu____6677))
in (

let cvar_sorts = (FStar_List.map FStar_Pervasives_Native.snd cvars)
in (

let caption = (

let uu____6689 = (FStar_Options.log_queries ())
in (match (uu____6689) with
| true -> begin
(

let uu____6692 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in FStar_Pervasives_Native.Some (uu____6692))
end
| uu____6693 -> begin
FStar_Pervasives_Native.None
end))
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (caption)))
in (

let t1 = (

let uu____6700 = (

let uu____6707 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((tsym), (uu____6707)))
in (FStar_SMTEncoding_Util.mkApp uu____6700))
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t1 FStar_SMTEncoding_Term.mk_Term_type)
in (

let k_assumption = (

let a_name = (Prims.strcat "kinding_" tsym)
in (

let uu____6719 = (

let uu____6726 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((uu____6726), (FStar_Pervasives_Native.Some (a_name)), (a_name)))
in (FStar_SMTEncoding_Util.mkAssume uu____6719)))
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t1)
in (

let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t1)
in (

let pre_typing = (

let a_name = (Prims.strcat "pre_typing_" tsym)
in (

let uu____6747 = (

let uu____6754 = (

let uu____6755 = (

let uu____6766 = (

let uu____6767 = (

let uu____6772 = (

let uu____6773 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____6773))
in ((f_has_t), (uu____6772)))
in (FStar_SMTEncoding_Util.mkImp uu____6767))
in ((((f_has_t)::[])::[]), ((fsym)::cvars), (uu____6766)))
in (mkForall_fuel uu____6755))
in ((uu____6754), (FStar_Pervasives_Native.Some ("pre-typing for functions")), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____6747)))
in (

let t_interp1 = (

let a_name = (Prims.strcat "interpretation_" tsym)
in (

let uu____6796 = (

let uu____6803 = (

let uu____6804 = (

let uu____6815 = (FStar_SMTEncoding_Util.mkIff ((f_has_t_z), (t_interp)))
in ((((f_has_t_z)::[])::[]), ((fsym)::cvars), (uu____6815)))
in (FStar_SMTEncoding_Util.mkForall uu____6804))
in ((uu____6803), (FStar_Pervasives_Native.Some (a_name)), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____6796)))
in (

let t_decls = (FStar_List.append ((tdecl)::decls) (FStar_List.append decls' (FStar_List.append guard_decls ((k_assumption)::(pre_typing)::(t_interp1)::[]))))
in ((

let uu____6840 = (mk_cache_entry env tsym cvar_sorts t_decls)
in (FStar_Util.smap_add env.cache tkey_hash uu____6840));
((t1), (t_decls));
)))))))))))))
end))))))
end))
end))
end)))))
end))
end
| uu____6843 -> begin
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

let uu____6855 = (

let uu____6862 = (FStar_SMTEncoding_Term.mk_HasType t1 FStar_SMTEncoding_Term.mk_Term_type)
in ((uu____6862), (FStar_Pervasives_Native.Some ("Typing for non-total arrows")), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____6855)))
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

let uu____6874 = (

let uu____6881 = (

let uu____6882 = (

let uu____6893 = (

let uu____6894 = (

let uu____6899 = (

let uu____6900 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____6900))
in ((f_has_t), (uu____6899)))
in (FStar_SMTEncoding_Util.mkImp uu____6894))
in ((((f_has_t)::[])::[]), ((fsym)::[]), (uu____6893)))
in (mkForall_fuel uu____6882))
in ((uu____6881), (FStar_Pervasives_Native.Some (a_name)), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____6874)))
in ((t1), ((tdecl)::(t_kinding)::(t_interp)::[]))))))))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (uu____6927) -> begin
(

let uu____6934 = (

let uu____6939 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)
in (match (uu____6939) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.pos = uu____6946; FStar_Syntax_Syntax.vars = uu____6947} -> begin
(

let uu____6954 = (FStar_Syntax_Subst.open_term ((((x), (FStar_Pervasives_Native.None)))::[]) f)
in (match (uu____6954) with
| (b, f1) -> begin
(

let uu____6979 = (

let uu____6980 = (FStar_List.hd b)
in (FStar_Pervasives_Native.fst uu____6980))
in ((uu____6979), (f1)))
end))
end
| uu____6989 -> begin
(failwith "impossible")
end))
in (match (uu____6934) with
| (x, f) -> begin
(

let uu____7000 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (uu____7000) with
| (base_t, decls) -> begin
(

let uu____7011 = (gen_term_var env x)
in (match (uu____7011) with
| (x1, xtm, env') -> begin
(

let uu____7025 = (encode_formula f env')
in (match (uu____7025) with
| (refinement, decls') -> begin
(

let uu____7036 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____7036) with
| (fsym, fterm) -> begin
(

let tm_has_type_with_fuel = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (FStar_Pervasives_Native.Some (fterm)) xtm base_t)
in (

let encoding = (FStar_SMTEncoding_Util.mkAnd ((tm_has_type_with_fuel), (refinement)))
in (

let cvars = (

let uu____7052 = (

let uu____7055 = (FStar_SMTEncoding_Term.free_variables refinement)
in (

let uu____7062 = (FStar_SMTEncoding_Term.free_variables tm_has_type_with_fuel)
in (FStar_List.append uu____7055 uu____7062)))
in (FStar_Util.remove_dups FStar_SMTEncoding_Term.fv_eq uu____7052))
in (

let cvars1 = (FStar_All.pipe_right cvars (FStar_List.filter (fun uu____7095 -> (match (uu____7095) with
| (y, uu____7101) -> begin
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

let uu____7134 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____7134) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
(

let uu____7142 = (

let uu____7143 = (

let uu____7150 = (FStar_All.pipe_right cvars1 (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((cache_entry.cache_symbol_name), (uu____7150)))
in (FStar_SMTEncoding_Util.mkApp uu____7143))
in ((uu____7142), ((FStar_List.append decls (FStar_List.append decls' (use_cache_entry cache_entry))))))
end
| FStar_Pervasives_Native.None -> begin
(

let module_name = env.current_module_name
in (

let tsym = (

let uu____7171 = (

let uu____7172 = (

let uu____7173 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "_Tm_refine_" uu____7173))
in (Prims.strcat module_name uu____7172))
in (varops.mk_unique uu____7171))
in (

let cvar_sorts = (FStar_List.map FStar_Pervasives_Native.snd cvars1)
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let t1 = (

let uu____7187 = (

let uu____7194 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars1)
in ((tsym), (uu____7194)))
in (FStar_SMTEncoding_Util.mkApp uu____7187))
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

let uu____7209 = (

let uu____7216 = (

let uu____7217 = (

let uu____7228 = (FStar_SMTEncoding_Util.mkIff ((t_haseq_ref), (t_haseq_base)))
in ((((t_haseq_ref)::[])::[]), (cvars1), (uu____7228)))
in (FStar_SMTEncoding_Util.mkForall uu____7217))
in ((uu____7216), (FStar_Pervasives_Native.Some ((Prims.strcat "haseq for " tsym))), ((Prims.strcat "haseq" tsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____7209))
in (

let t_valid = (

let xx = ((x1), (FStar_SMTEncoding_Term.Term_sort))
in (

let valid_t = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((t1)::[])))
in (

let uu____7254 = (

let uu____7261 = (

let uu____7262 = (

let uu____7273 = (

let uu____7274 = (

let uu____7279 = (

let uu____7280 = (

let uu____7291 = (FStar_SMTEncoding_Util.mkAnd ((x_has_base_t), (refinement)))
in (([]), ((xx)::[]), (uu____7291)))
in (FStar_SMTEncoding_Util.mkExists uu____7280))
in ((uu____7279), (valid_t)))
in (FStar_SMTEncoding_Util.mkIff uu____7274))
in ((((valid_t)::[])::[]), (cvars1), (uu____7273)))
in (FStar_SMTEncoding_Util.mkForall uu____7262))
in ((uu____7261), (FStar_Pervasives_Native.Some ("validity axiom for refinement")), ((Prims.strcat "ref_valid_" tsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____7254))))
in (

let t_kinding = (

let uu____7329 = (

let uu____7336 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars1), (t_has_kind)))
in ((uu____7336), (FStar_Pervasives_Native.Some ("refinement kinding")), ((Prims.strcat "refinement_kinding_" tsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____7329))
in (

let t_interp = (

let uu____7354 = (

let uu____7361 = (

let uu____7362 = (

let uu____7373 = (FStar_SMTEncoding_Util.mkIff ((x_has_t), (encoding)))
in ((((x_has_t)::[])::[]), ((ffv)::(xfv)::cvars1), (uu____7373)))
in (FStar_SMTEncoding_Util.mkForall uu____7362))
in (

let uu____7396 = (

let uu____7399 = (FStar_Syntax_Print.term_to_string t0)
in FStar_Pervasives_Native.Some (uu____7399))
in ((uu____7361), (uu____7396), ((Prims.strcat "refinement_interpretation_" tsym)))))
in (FStar_SMTEncoding_Util.mkAssume uu____7354))
in (

let t_decls = (FStar_List.append decls (FStar_List.append decls' ((tdecl)::(t_kinding)::(t_valid)::(t_interp)::(t_haseq1)::[])))
in ((

let uu____7406 = (mk_cache_entry env tsym cvar_sorts t_decls)
in (FStar_Util.smap_add env.cache tkey_hash uu____7406));
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

let uu____7436 = (FStar_Syntax_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Util.mk_Term_uvar uu____7436))
in (

let uu____7437 = (encode_term_pred FStar_Pervasives_Native.None k env ttm)
in (match (uu____7437) with
| (t_has_k, decls) -> begin
(

let d = (

let uu____7449 = (

let uu____7456 = (

let uu____7457 = (

let uu____7458 = (

let uu____7459 = (FStar_Syntax_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____7459))
in (FStar_Util.format1 "uvar_typing_%s" uu____7458))
in (varops.mk_unique uu____7457))
in ((t_has_k), (FStar_Pervasives_Native.Some ("Uvar typing")), (uu____7456)))
in (FStar_SMTEncoding_Util.mkAssume uu____7449))
in ((ttm), ((FStar_List.append decls ((d)::[])))))
end)))
end
| FStar_Syntax_Syntax.Tm_app (uu____7464) -> begin
(

let uu____7479 = (FStar_Syntax_Util.head_and_args t0)
in (match (uu____7479) with
| (head1, args_e) -> begin
(

let uu____7520 = (

let uu____7533 = (

let uu____7534 = (FStar_Syntax_Subst.compress head1)
in uu____7534.FStar_Syntax_Syntax.n)
in ((uu____7533), (args_e)))
in (match (uu____7520) with
| uu____7549 when (head_redex env head1) -> begin
(

let uu____7562 = (whnf env t)
in (encode_term uu____7562 env))
end
| uu____7563 when (is_arithmetic_primitive head1 args_e) -> begin
(encode_arith_term env head1 args_e)
end
| uu____7582 when (is_BitVector_primitive head1 args_e) -> begin
(encode_BitVector_term env head1 args_e)
end
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____7596; FStar_Syntax_Syntax.vars = uu____7597}, uu____7598), (uu____7599)::((v1, uu____7601))::((v2, uu____7603))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.lexcons_lid) -> begin
(

let uu____7654 = (encode_term v1 env)
in (match (uu____7654) with
| (v11, decls1) -> begin
(

let uu____7665 = (encode_term v2 env)
in (match (uu____7665) with
| (v21, decls2) -> begin
(

let uu____7676 = (FStar_SMTEncoding_Util.mk_LexCons v11 v21)
in ((uu____7676), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____7680)::((v1, uu____7682))::((v2, uu____7684))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.lexcons_lid) -> begin
(

let uu____7731 = (encode_term v1 env)
in (match (uu____7731) with
| (v11, decls1) -> begin
(

let uu____7742 = (encode_term v2 env)
in (match (uu____7742) with
| (v21, decls2) -> begin
(

let uu____7753 = (FStar_SMTEncoding_Util.mk_LexCons v11 v21)
in ((uu____7753), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), uu____7756) -> begin
(

let e0 = (

let uu____7774 = (FStar_List.hd args_e)
in (FStar_TypeChecker_Util.reify_body_with_arg env.tcenv head1 uu____7774))
in ((

let uu____7782 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____7782) with
| true -> begin
(

let uu____7783 = (FStar_Syntax_Print.term_to_string e0)
in (FStar_Util.print1 "Result of normalization %s\n" uu____7783))
end
| uu____7784 -> begin
()
end));
(

let e = (

let uu____7788 = (

let uu____7789 = (FStar_TypeChecker_Util.remove_reify e0)
in (

let uu____7790 = (FStar_List.tl args_e)
in (FStar_Syntax_Syntax.mk_Tm_app uu____7789 uu____7790)))
in (uu____7788 FStar_Pervasives_Native.None t0.FStar_Syntax_Syntax.pos))
in (encode_term e env));
))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____7799)), ((arg, uu____7801))::[]) -> begin
(encode_term arg env)
end
| uu____7826 -> begin
(

let uu____7839 = (encode_args args_e env)
in (match (uu____7839) with
| (args, decls) -> begin
(

let encode_partial_app = (fun ht_opt -> (

let uu____7894 = (encode_term head1 env)
in (match (uu____7894) with
| (head2, decls') -> begin
(

let app_tm = (mk_Apply_args head2 args)
in (match (ht_opt) with
| FStar_Pervasives_Native.None -> begin
((app_tm), ((FStar_List.append decls decls')))
end
| FStar_Pervasives_Native.Some (formals, c) -> begin
(

let uu____7958 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (uu____7958) with
| (formals1, rest) -> begin
(

let subst1 = (FStar_List.map2 (fun uu____8036 uu____8037 -> (match (((uu____8036), (uu____8037))) with
| ((bv, uu____8059), (a, uu____8061)) -> begin
FStar_Syntax_Syntax.NT (((bv), (a)))
end)) formals1 args_e)
in (

let ty = (

let uu____8079 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right uu____8079 (FStar_Syntax_Subst.subst subst1)))
in (

let uu____8084 = (encode_term_pred FStar_Pervasives_Native.None ty env app_tm)
in (match (uu____8084) with
| (has_type, decls'') -> begin
(

let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (

let e_typing = (

let uu____8099 = (

let uu____8106 = (FStar_SMTEncoding_Util.mkForall ((((has_type)::[])::[]), (cvars), (has_type)))
in (

let uu____8115 = (

let uu____8116 = (

let uu____8117 = (

let uu____8118 = (FStar_SMTEncoding_Term.hash_of_term app_tm)
in (FStar_Util.digest_of_string uu____8118))
in (Prims.strcat "partial_app_typing_" uu____8117))
in (varops.mk_unique uu____8116))
in ((uu____8106), (FStar_Pervasives_Native.Some ("Partial app typing")), (uu____8115))))
in (FStar_SMTEncoding_Util.mkAssume uu____8099))
in ((app_tm), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' ((e_typing)::[]))))))))
end))))
end))
end))
end)))
in (

let encode_full_app = (fun fv -> (

let uu____8135 = (lookup_free_var_sym env fv)
in (match (uu____8135) with
| (fname, fuel_args) -> begin
(

let tm = (FStar_SMTEncoding_Util.mkApp' ((fname), ((FStar_List.append fuel_args args))))
in ((tm), (decls)))
end)))
in (

let head2 = (FStar_Syntax_Subst.compress head1)
in (

let head_type = (match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (x); FStar_Syntax_Syntax.pos = uu____8166; FStar_Syntax_Syntax.vars = uu____8167}, uu____8168) -> begin
FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____8179; FStar_Syntax_Syntax.vars = uu____8180}, uu____8181) -> begin
(

let uu____8186 = (

let uu____8187 = (

let uu____8192 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____8192 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____8187 FStar_Pervasives_Native.snd))
in FStar_Pervasives_Native.Some (uu____8186))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____8222 = (

let uu____8223 = (

let uu____8228 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____8228 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____8223 FStar_Pervasives_Native.snd))
in FStar_Pervasives_Native.Some (uu____8222))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____8257, (FStar_Util.Inl (t1), uu____8259), uu____8260) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____8309, (FStar_Util.Inr (c), uu____8311), uu____8312) -> begin
FStar_Pervasives_Native.Some ((FStar_Syntax_Util.comp_result c))
end
| uu____8361 -> begin
FStar_Pervasives_Native.None
end)
in (match (head_type) with
| FStar_Pervasives_Native.None -> begin
(encode_partial_app FStar_Pervasives_Native.None)
end
| FStar_Pervasives_Native.Some (head_type1) -> begin
(

let head_type2 = (

let uu____8388 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type1)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine uu____8388))
in (

let uu____8389 = (curried_arrow_formals_comp head_type2)
in (match (uu____8389) with
| (formals, c) -> begin
(match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____8405; FStar_Syntax_Syntax.vars = uu____8406}, uu____8407) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| uu____8421 -> begin
(match (((FStar_List.length formals) > (FStar_List.length args))) with
| true -> begin
(encode_partial_app (FStar_Pervasives_Native.Some (((formals), (c)))))
end
| uu____8434 -> begin
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

let uu____8470 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____8470) with
| (bs1, body1, opening) -> begin
(

let fallback = (fun uu____8493 -> (

let f = (varops.fresh "Tm_abs")
in (

let decl = FStar_SMTEncoding_Term.DeclFun (((f), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Imprecise function encoding"))))
in (

let uu____8500 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in ((uu____8500), ((decl)::[]))))))
in (

let is_impure = (fun rc -> (

let uu____8507 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv rc.FStar_Syntax_Syntax.residual_effect)
in (FStar_All.pipe_right uu____8507 Prims.op_Negation)))
in (

let codomain_eff = (fun rc -> (

let res_typ = (match (rc.FStar_Syntax_Syntax.residual_typ) with
| FStar_Pervasives_Native.None -> begin
(

let uu____8517 = (FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange [] FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right uu____8517 FStar_Pervasives_Native.fst))
end
| FStar_Pervasives_Native.Some (t1) -> begin
t1
end)
in (match ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_Tot_lid)) with
| true -> begin
(

let uu____8537 = (FStar_Syntax_Syntax.mk_Total res_typ)
in FStar_Pervasives_Native.Some (uu____8537))
end
| uu____8538 -> begin
(match ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_GTot_lid)) with
| true -> begin
(

let uu____8541 = (FStar_Syntax_Syntax.mk_GTotal res_typ)
in FStar_Pervasives_Native.Some (uu____8541))
end
| uu____8542 -> begin
FStar_Pervasives_Native.None
end)
end)))
in (match (lopt) with
| FStar_Pervasives_Native.None -> begin
((

let uu____8548 = (

let uu____8549 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)" uu____8549))
in (FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____8548));
(fallback ());
)
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____8551 = ((is_impure rc) && (

let uu____8553 = (FStar_TypeChecker_Env.is_reifiable env.tcenv rc)
in (not (uu____8553))))
in (match (uu____8551) with
| true -> begin
(fallback ())
end
| uu____8558 -> begin
(

let cache_size = (FStar_Util.smap_size env.cache)
in (

let uu____8560 = (encode_binders FStar_Pervasives_Native.None bs1 env)
in (match (uu____8560) with
| (vars, guards, envbody, decls, uu____8585) -> begin
(

let body2 = (

let uu____8599 = (FStar_TypeChecker_Env.is_reifiable env.tcenv rc)
in (match (uu____8599) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env.tcenv body1)
end
| uu____8600 -> begin
body1
end))
in (

let uu____8601 = (encode_term body2 envbody)
in (match (uu____8601) with
| (body3, decls') -> begin
(

let uu____8612 = (

let uu____8621 = (codomain_eff rc)
in (match (uu____8621) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), ([]))
end
| FStar_Pervasives_Native.Some (c) -> begin
(

let tfun = (FStar_Syntax_Util.arrow bs1 c)
in (

let uu____8640 = (encode_term tfun env)
in (match (uu____8640) with
| (t1, decls1) -> begin
((FStar_Pervasives_Native.Some (t1)), (decls1))
end)))
end))
in (match (uu____8612) with
| (arrow_t_opt, decls'') -> begin
(

let key_body = (

let uu____8672 = (

let uu____8683 = (

let uu____8684 = (

let uu____8689 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____8689), (body3)))
in (FStar_SMTEncoding_Util.mkImp uu____8684))
in (([]), (vars), (uu____8683)))
in (FStar_SMTEncoding_Util.mkForall uu____8672))
in (

let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (

let cvars1 = (match (arrow_t_opt) with
| FStar_Pervasives_Native.None -> begin
cvars
end
| FStar_Pervasives_Native.Some (t1) -> begin
(

let uu____8701 = (

let uu____8704 = (FStar_SMTEncoding_Term.free_variables t1)
in (FStar_List.append uu____8704 cvars))
in (FStar_Util.remove_dups FStar_SMTEncoding_Term.fv_eq uu____8701))
end)
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), (cvars1), (key_body)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____8723 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____8723) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
(

let uu____8731 = (

let uu____8732 = (

let uu____8739 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars1)
in ((cache_entry.cache_symbol_name), (uu____8739)))
in (FStar_SMTEncoding_Util.mkApp uu____8732))
in ((uu____8731), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' (use_cache_entry cache_entry)))))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____8750 = (is_an_eta_expansion env vars body3)
in (match (uu____8750) with
| FStar_Pervasives_Native.Some (t1) -> begin
(

let decls1 = (

let uu____8761 = (

let uu____8762 = (FStar_Util.smap_size env.cache)
in (uu____8762 = cache_size))
in (match (uu____8761) with
| true -> begin
[]
end
| uu____8765 -> begin
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

let uu____8778 = (

let uu____8779 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_abs_" uu____8779))
in (varops.mk_unique uu____8778))
in (Prims.strcat module_name (Prims.strcat "_" fsym))))
in (

let fdecl = FStar_SMTEncoding_Term.DeclFun (((fsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let f = (

let uu____8786 = (

let uu____8793 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars1)
in ((fsym), (uu____8793)))
in (FStar_SMTEncoding_Util.mkApp uu____8786))
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

let uu____8811 = (

let uu____8812 = (

let uu____8819 = (FStar_SMTEncoding_Util.mkForall ((((f)::[])::[]), (cvars1), (f_has_t)))
in ((uu____8819), (FStar_Pervasives_Native.Some (a_name)), (a_name)))
in (FStar_SMTEncoding_Util.mkAssume uu____8812))
in (uu____8811)::[])))
end)
in (

let interp_f = (

let a_name = (Prims.strcat "interpretation_" fsym)
in (

let uu____8832 = (

let uu____8839 = (

let uu____8840 = (

let uu____8851 = (FStar_SMTEncoding_Util.mkEq ((app), (body3)))
in ((((app)::[])::[]), ((FStar_List.append vars cvars1)), (uu____8851)))
in (FStar_SMTEncoding_Util.mkForall uu____8840))
in ((uu____8839), (FStar_Pervasives_Native.Some (a_name)), (a_name)))
in (FStar_SMTEncoding_Util.mkAssume uu____8832)))
in (

let f_decls = (FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' (FStar_List.append ((fdecl)::typing_f) ((interp_f)::[])))))
in ((

let uu____8868 = (mk_cache_entry env fsym cvar_sorts f_decls)
in (FStar_Util.smap_add env.cache tkey_hash uu____8868));
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
| FStar_Syntax_Syntax.Tm_let ((uu____8871, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____8872); FStar_Syntax_Syntax.lbunivs = uu____8873; FStar_Syntax_Syntax.lbtyp = uu____8874; FStar_Syntax_Syntax.lbeff = uu____8875; FStar_Syntax_Syntax.lbdef = uu____8876})::uu____8877), uu____8878) -> begin
(failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____8904; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____8906; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (uu____8927) -> begin
((FStar_Errors.diag t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts");
(

let e = (varops.fresh "let-rec")
in (

let decl_e = FStar_SMTEncoding_Term.DeclFun (((e), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let uu____8947 = (FStar_SMTEncoding_Util.mkFreeV ((e), (FStar_SMTEncoding_Term.Term_sort)))
in ((uu____8947), ((decl_e)::[])))));
)
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end);
)))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (

let uu____9002 = (encode_term e1 env)
in (match (uu____9002) with
| (ee1, decls1) -> begin
(

let uu____9013 = (FStar_Syntax_Subst.open_term ((((x), (FStar_Pervasives_Native.None)))::[]) e2)
in (match (uu____9013) with
| (xs, e21) -> begin
(

let uu____9038 = (FStar_List.hd xs)
in (match (uu____9038) with
| (x1, uu____9052) -> begin
(

let env' = (push_term_var env x1 ee1)
in (

let uu____9054 = (encode_body e21 env')
in (match (uu____9054) with
| (ee2, decls2) -> begin
((ee2), ((FStar_List.append decls1 decls2)))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (

let uu____9086 = (

let uu____9093 = (

let uu____9094 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.null_bv uu____9094))
in (gen_term_var env uu____9093))
in (match (uu____9086) with
| (scrsym, scr', env1) -> begin
(

let uu____9102 = (encode_term e env1)
in (match (uu____9102) with
| (scr, decls) -> begin
(

let uu____9113 = (

let encode_branch = (fun b uu____9138 -> (match (uu____9138) with
| (else_case, decls1) -> begin
(

let uu____9157 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____9157) with
| (p, w, br) -> begin
(

let uu____9183 = (encode_pat env1 p)
in (match (uu____9183) with
| (env0, pattern) -> begin
(

let guard = (pattern.guard scr')
in (

let projections = (pattern.projections scr')
in (

let env2 = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env2 uu____9220 -> (match (uu____9220) with
| (x, t) -> begin
(push_term_var env2 x t)
end)) env1))
in (

let uu____9227 = (match (w) with
| FStar_Pervasives_Native.None -> begin
((guard), ([]))
end
| FStar_Pervasives_Native.Some (w1) -> begin
(

let uu____9249 = (encode_term w1 env2)
in (match (uu____9249) with
| (w2, decls2) -> begin
(

let uu____9262 = (

let uu____9263 = (

let uu____9268 = (

let uu____9269 = (

let uu____9274 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue)
in ((w2), (uu____9274)))
in (FStar_SMTEncoding_Util.mkEq uu____9269))
in ((guard), (uu____9268)))
in (FStar_SMTEncoding_Util.mkAnd uu____9263))
in ((uu____9262), (decls2)))
end))
end)
in (match (uu____9227) with
| (guard1, decls2) -> begin
(

let uu____9287 = (encode_br br env2)
in (match (uu____9287) with
| (br1, decls3) -> begin
(

let uu____9300 = (FStar_SMTEncoding_Util.mkITE ((guard1), (br1), (else_case)))
in ((uu____9300), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end)))))
end))
end))
end))
in (FStar_List.fold_right encode_branch pats ((default_case), (decls))))
in (match (uu____9113) with
| (match_tm, decls1) -> begin
(

let uu____9319 = (FStar_SMTEncoding_Term.mkLet' (((((((scrsym), (FStar_SMTEncoding_Term.Term_sort))), (scr)))::[]), (match_tm)) FStar_Range.dummyRange)
in ((uu____9319), (decls1)))
end))
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> ((

let uu____9359 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____9359) with
| true -> begin
(

let uu____9360 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" uu____9360))
end
| uu____9361 -> begin
()
end));
(

let uu____9362 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (uu____9362) with
| (vars, pat_term) -> begin
(

let uu____9379 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun uu____9432 v1 -> (match (uu____9432) with
| (env1, vars1) -> begin
(

let uu____9484 = (gen_term_var env1 v1)
in (match (uu____9484) with
| (xx, uu____9506, env2) -> begin
((env2), ((((v1), (((xx), (FStar_SMTEncoding_Term.Term_sort)))))::vars1))
end))
end)) ((env), ([]))))
in (match (uu____9379) with
| (env1, vars1) -> begin
(

let rec mk_guard = (fun pat1 scrutinee -> (match (pat1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_var (uu____9585) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_wild (uu____9586) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____9587) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____9595 = (

let uu____9600 = (encode_const c)
in ((scrutinee), (uu____9600)))
in (FStar_SMTEncoding_Util.mkEq uu____9595))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let is_f = (

let tc_name = (FStar_TypeChecker_Env.typ_of_datacon env1.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let uu____9621 = (FStar_TypeChecker_Env.datacons_of_typ env1.tcenv tc_name)
in (match (uu____9621) with
| (uu____9628, (uu____9629)::[]) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| uu____9632 -> begin
(mk_data_tester env1 f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
end)))
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____9665 -> (match (uu____9665) with
| (arg, uu____9673) -> begin
(

let proj = (primitive_projector_by_pos env1.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____9679 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_guard arg uu____9679)))
end))))
in (FStar_SMTEncoding_Util.mk_and_l ((is_f)::sub_term_guards))))
end))
in (

let rec mk_projections = (fun pat1 scrutinee -> (match (pat1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (x, uu____9706) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_constant (uu____9737) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let uu____9760 = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____9804 -> (match (uu____9804) with
| (arg, uu____9818) -> begin
(

let proj = (primitive_projector_by_pos env1.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____9824 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_projections arg uu____9824)))
end))))
in (FStar_All.pipe_right uu____9760 FStar_List.flatten))
end))
in (

let pat_term1 = (fun uu____9852 -> (encode_term pat_term env1))
in (

let pattern = {pat_vars = vars1; pat_term = pat_term1; guard = (mk_guard pat); projections = (mk_projections pat)}
in ((env1), (pattern))))))
end))
end));
))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (

let uu____9862 = (FStar_All.pipe_right l (FStar_List.fold_left (fun uu____9900 uu____9901 -> (match (((uu____9900), (uu____9901))) with
| ((tms, decls), (t, uu____9937)) -> begin
(

let uu____9958 = (encode_term t env)
in (match (uu____9958) with
| (t1, decls') -> begin
(((t1)::tms), ((FStar_List.append decls decls')))
end))
end)) (([]), ([]))))
in (match (uu____9862) with
| (l1, decls) -> begin
(((FStar_List.rev l1)), (decls))
end)))
and encode_function_type_as_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let list_elements1 = (fun e -> (

let uu____10015 = (FStar_Syntax_Util.list_elements e)
in (match (uu____10015) with
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

let uu____10036 = (

let uu____10051 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right uu____10051 FStar_Syntax_Util.head_and_args))
in (match (uu____10036) with
| (head1, args) -> begin
(

let uu____10090 = (

let uu____10103 = (

let uu____10104 = (FStar_Syntax_Util.un_uinst head1)
in uu____10104.FStar_Syntax_Syntax.n)
in ((uu____10103), (args)))
in (match (uu____10090) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((uu____10118, uu____10119))::((e, uu____10121))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpat_lid) -> begin
e
end
| uu____10156 -> begin
(failwith "Unexpected pattern term")
end))
end)))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements1 p)
in (

let smt_pat_or1 = (fun t1 -> (

let uu____10192 = (

let uu____10207 = (FStar_Syntax_Util.unmeta t1)
in (FStar_All.pipe_right uu____10207 FStar_Syntax_Util.head_and_args))
in (match (uu____10192) with
| (head1, args) -> begin
(

let uu____10248 = (

let uu____10261 = (

let uu____10262 = (FStar_Syntax_Util.un_uinst head1)
in uu____10262.FStar_Syntax_Syntax.n)
in ((uu____10261), (args)))
in (match (uu____10248) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, uu____10279))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpatOr_lid) -> begin
FStar_Pervasives_Native.Some (e)
end
| uu____10306 -> begin
FStar_Pervasives_Native.None
end))
end)))
in (match (elts) with
| (t1)::[] -> begin
(

let uu____10328 = (smt_pat_or1 t1)
in (match (uu____10328) with
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____10344 = (list_elements1 e)
in (FStar_All.pipe_right uu____10344 (FStar_List.map (fun branch1 -> (

let uu____10362 = (list_elements1 branch1)
in (FStar_All.pipe_right uu____10362 (FStar_List.map one_pat)))))))
end
| uu____10373 -> begin
(

let uu____10378 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____10378)::[])
end))
end
| uu____10399 -> begin
(

let uu____10402 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____10402)::[])
end))))
in (

let uu____10423 = (

let uu____10442 = (

let uu____10443 = (FStar_Syntax_Subst.compress t)
in uu____10443.FStar_Syntax_Syntax.n)
in (match (uu____10442) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____10482 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____10482) with
| (binders1, c1) -> begin
(match (c1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____10525; FStar_Syntax_Syntax.effect_name = uu____10526; FStar_Syntax_Syntax.result_typ = uu____10527; FStar_Syntax_Syntax.effect_args = ((pre, uu____10529))::((post, uu____10531))::((pats, uu____10533))::[]; FStar_Syntax_Syntax.flags = uu____10534}) -> begin
(

let uu____10575 = (lemma_pats pats)
in ((binders1), (pre), (post), (uu____10575)))
end
| uu____10592 -> begin
(failwith "impos")
end)
end))
end
| uu____10611 -> begin
(failwith "Impos")
end))
in (match (uu____10423) with
| (binders, pre, post, patterns) -> begin
(

let env1 = (

let uu___140_10659 = env
in {bindings = uu___140_10659.bindings; depth = uu___140_10659.depth; tcenv = uu___140_10659.tcenv; warn = uu___140_10659.warn; cache = uu___140_10659.cache; nolabels = uu___140_10659.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___140_10659.encode_non_total_function_typ; current_module_name = uu___140_10659.current_module_name})
in (

let uu____10660 = (encode_binders FStar_Pervasives_Native.None binders env1)
in (match (uu____10660) with
| (vars, guards, env2, decls, uu____10685) -> begin
(

let uu____10698 = (

let uu____10711 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch1 -> (

let uu____10755 = (

let uu____10764 = (FStar_All.pipe_right branch1 (FStar_List.map (fun t1 -> (encode_term t1 env2))))
in (FStar_All.pipe_right uu____10764 FStar_List.unzip))
in (match (uu____10755) with
| (pats, decls1) -> begin
((pats), (decls1))
end)))))
in (FStar_All.pipe_right uu____10711 FStar_List.unzip))
in (match (uu____10698) with
| (pats, decls') -> begin
(

let decls'1 = (FStar_List.flatten decls')
in (

let env3 = (

let uu___141_10873 = env2
in {bindings = uu___141_10873.bindings; depth = uu___141_10873.depth; tcenv = uu___141_10873.tcenv; warn = uu___141_10873.warn; cache = uu___141_10873.cache; nolabels = true; use_zfuel_name = uu___141_10873.use_zfuel_name; encode_non_total_function_typ = uu___141_10873.encode_non_total_function_typ; current_module_name = uu___141_10873.current_module_name})
in (

let uu____10874 = (

let uu____10879 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula uu____10879 env3))
in (match (uu____10874) with
| (pre1, decls'') -> begin
(

let uu____10886 = (

let uu____10891 = (FStar_Syntax_Util.unmeta post)
in (encode_formula uu____10891 env3))
in (match (uu____10886) with
| (post1, decls''') -> begin
(

let decls1 = (FStar_List.append decls (FStar_List.append (FStar_List.flatten decls'1) (FStar_List.append decls'' decls''')))
in (

let uu____10901 = (

let uu____10902 = (

let uu____10913 = (

let uu____10914 = (

let uu____10919 = (FStar_SMTEncoding_Util.mk_and_l ((pre1)::guards))
in ((uu____10919), (post1)))
in (FStar_SMTEncoding_Util.mkImp uu____10914))
in ((pats), (vars), (uu____10913)))
in (FStar_SMTEncoding_Util.mkForall uu____10902))
in ((uu____10901), (decls1))))
end))
end))))
end))
end)))
end))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (

let debug1 = (fun phi1 -> (

let uu____10938 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____10938) with
| true -> begin
(

let uu____10939 = (FStar_Syntax_Print.tag_of_term phi1)
in (

let uu____10940 = (FStar_Syntax_Print.term_to_string phi1)
in (FStar_Util.print2 "Formula (%s)  %s\n" uu____10939 uu____10940)))
end
| uu____10941 -> begin
()
end)))
in (

let enc = (fun f r l -> (

let uu____10973 = (FStar_Util.fold_map (fun decls x -> (

let uu____11001 = (encode_term (FStar_Pervasives_Native.fst x) env)
in (match (uu____11001) with
| (t, decls') -> begin
(((FStar_List.append decls decls')), (t))
end))) [] l)
in (match (uu____10973) with
| (decls, args) -> begin
(

let uu____11030 = (

let uu___142_11031 = (f args)
in {FStar_SMTEncoding_Term.tm = uu___142_11031.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___142_11031.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____11030), (decls)))
end)))
in (

let const_op = (fun f r uu____11062 -> (

let uu____11075 = (f r)
in ((uu____11075), ([]))))
in (

let un_op = (fun f l -> (

let uu____11094 = (FStar_List.hd l)
in (FStar_All.pipe_left f uu____11094)))
in (

let bin_op = (fun f uu___116_11110 -> (match (uu___116_11110) with
| (t1)::(t2)::[] -> begin
(f ((t1), (t2)))
end
| uu____11121 -> begin
(failwith "Impossible")
end))
in (

let enc_prop_c = (fun f r l -> (

let uu____11155 = (FStar_Util.fold_map (fun decls uu____11178 -> (match (uu____11178) with
| (t, uu____11192) -> begin
(

let uu____11193 = (encode_formula t env)
in (match (uu____11193) with
| (phi1, decls') -> begin
(((FStar_List.append decls decls')), (phi1))
end))
end)) [] l)
in (match (uu____11155) with
| (decls, phis) -> begin
(

let uu____11222 = (

let uu___143_11223 = (f phis)
in {FStar_SMTEncoding_Term.tm = uu___143_11223.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___143_11223.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____11222), (decls)))
end)))
in (

let eq_op = (fun r args -> (

let rf = (FStar_List.filter (fun uu____11284 -> (match (uu____11284) with
| (a, q) -> begin
(match (q) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____11303)) -> begin
false
end
| uu____11304 -> begin
true
end)
end)) args)
in (match (((FStar_List.length rf) <> (Prims.parse_int "2"))) with
| true -> begin
(

let uu____11319 = (FStar_Util.format1 "eq_op: got %s non-implicit arguments instead of 2?" (Prims.string_of_int (FStar_List.length rf)))
in (failwith uu____11319))
end
| uu____11332 -> begin
(

let uu____11333 = (enc (bin_op FStar_SMTEncoding_Util.mkEq))
in (uu____11333 r rf))
end)))
in (

let mk_imp1 = (fun r uu___117_11358 -> (match (uu___117_11358) with
| ((lhs, uu____11364))::((rhs, uu____11366))::[] -> begin
(

let uu____11393 = (encode_formula rhs env)
in (match (uu____11393) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____11408) -> begin
((l1), (decls1))
end
| uu____11413 -> begin
(

let uu____11414 = (encode_formula lhs env)
in (match (uu____11414) with
| (l2, decls2) -> begin
(

let uu____11425 = (FStar_SMTEncoding_Term.mkImp ((l2), (l1)) r)
in ((uu____11425), ((FStar_List.append decls1 decls2))))
end))
end)
end))
end
| uu____11428 -> begin
(failwith "impossible")
end))
in (

let mk_ite = (fun r uu___118_11449 -> (match (uu___118_11449) with
| ((guard, uu____11455))::((_then, uu____11457))::((_else, uu____11459))::[] -> begin
(

let uu____11496 = (encode_formula guard env)
in (match (uu____11496) with
| (g, decls1) -> begin
(

let uu____11507 = (encode_formula _then env)
in (match (uu____11507) with
| (t, decls2) -> begin
(

let uu____11518 = (encode_formula _else env)
in (match (uu____11518) with
| (e, decls3) -> begin
(

let res = (FStar_SMTEncoding_Term.mkITE ((g), (t), (e)) r)
in ((res), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end))
end))
end
| uu____11532 -> begin
(failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (

let uu____11557 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f uu____11557)))
in (

let connectives = (

let uu____11575 = (

let uu____11588 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd))
in ((FStar_Parser_Const.and_lid), (uu____11588)))
in (

let uu____11605 = (

let uu____11620 = (

let uu____11633 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr))
in ((FStar_Parser_Const.or_lid), (uu____11633)))
in (

let uu____11650 = (

let uu____11665 = (

let uu____11680 = (

let uu____11693 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff))
in ((FStar_Parser_Const.iff_lid), (uu____11693)))
in (

let uu____11710 = (

let uu____11725 = (

let uu____11740 = (

let uu____11753 = (enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot))
in ((FStar_Parser_Const.not_lid), (uu____11753)))
in (uu____11740)::(((FStar_Parser_Const.eq2_lid), (eq_op)))::(((FStar_Parser_Const.eq3_lid), (eq_op)))::(((FStar_Parser_Const.true_lid), ((const_op FStar_SMTEncoding_Term.mkTrue))))::(((FStar_Parser_Const.false_lid), ((const_op FStar_SMTEncoding_Term.mkFalse))))::[])
in (((FStar_Parser_Const.ite_lid), (mk_ite)))::uu____11725)
in (uu____11680)::uu____11710))
in (((FStar_Parser_Const.imp_lid), (mk_imp1)))::uu____11665)
in (uu____11620)::uu____11650))
in (uu____11575)::uu____11605))
in (

let rec fallback = (fun phi1 -> (match (phi1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(

let uu____12074 = (encode_formula phi' env)
in (match (uu____12074) with
| (phi2, decls) -> begin
(

let uu____12085 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled (((phi2), (msg), (r)))) r)
in ((uu____12085), (decls)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (uu____12086) -> begin
(

let uu____12093 = (FStar_Syntax_Util.unmeta phi1)
in (encode_formula uu____12093 env))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(

let uu____12132 = (encode_match e pats FStar_SMTEncoding_Util.mkFalse env encode_formula)
in (match (uu____12132) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____12144; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____12146; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let uu____12167 = (encode_let x t1 e1 e2 env encode_formula)
in (match (uu____12167) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let head2 = (FStar_Syntax_Util.un_uinst head1)
in (match (((head2.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____12214)::((x, uu____12216))::((t, uu____12218))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.has_type_lid) -> begin
(

let uu____12265 = (encode_term x env)
in (match (uu____12265) with
| (x1, decls) -> begin
(

let uu____12276 = (encode_term t env)
in (match (uu____12276) with
| (t1, decls') -> begin
(

let uu____12287 = (FStar_SMTEncoding_Term.mk_HasType x1 t1)
in ((uu____12287), ((FStar_List.append decls decls'))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((r, uu____12292))::((msg, uu____12294))::((phi2, uu____12296))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.labeled_lid) -> begin
(

let uu____12341 = (

let uu____12346 = (

let uu____12347 = (FStar_Syntax_Subst.compress r)
in uu____12347.FStar_Syntax_Syntax.n)
in (

let uu____12350 = (

let uu____12351 = (FStar_Syntax_Subst.compress msg)
in uu____12351.FStar_Syntax_Syntax.n)
in ((uu____12346), (uu____12350))))
in (match (uu____12341) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____12360))) -> begin
(

let phi3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((phi2), (FStar_Syntax_Syntax.Meta_labeled (((s), (r1), (false))))))) FStar_Pervasives_Native.None r1)
in (fallback phi3))
end
| uu____12366 -> begin
(fallback phi2)
end))
end
| uu____12371 when (head_redex env head2) -> begin
(

let uu____12384 = (whnf env phi1)
in (encode_formula uu____12384 env))
end
| uu____12385 -> begin
(

let uu____12398 = (encode_term phi1 env)
in (match (uu____12398) with
| (tt, decls) -> begin
(

let uu____12409 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___144_12412 = tt
in {FStar_SMTEncoding_Term.tm = uu___144_12412.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___144_12412.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi1.FStar_Syntax_Syntax.pos}))
in ((uu____12409), (decls)))
end))
end))
end
| uu____12413 -> begin
(

let uu____12414 = (encode_term phi1 env)
in (match (uu____12414) with
| (tt, decls) -> begin
(

let uu____12425 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___145_12428 = tt
in {FStar_SMTEncoding_Term.tm = uu___145_12428.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___145_12428.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi1.FStar_Syntax_Syntax.pos}))
in ((uu____12425), (decls)))
end))
end))
in (

let encode_q_body = (fun env1 bs ps body -> (

let uu____12464 = (encode_binders FStar_Pervasives_Native.None bs env1)
in (match (uu____12464) with
| (vars, guards, env2, decls, uu____12503) -> begin
(

let uu____12516 = (

let uu____12529 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let uu____12577 = (

let uu____12586 = (FStar_All.pipe_right p (FStar_List.map (fun uu____12616 -> (match (uu____12616) with
| (t, uu____12626) -> begin
(encode_term t (

let uu___146_12628 = env2
in {bindings = uu___146_12628.bindings; depth = uu___146_12628.depth; tcenv = uu___146_12628.tcenv; warn = uu___146_12628.warn; cache = uu___146_12628.cache; nolabels = uu___146_12628.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___146_12628.encode_non_total_function_typ; current_module_name = uu___146_12628.current_module_name}))
end))))
in (FStar_All.pipe_right uu____12586 FStar_List.unzip))
in (match (uu____12577) with
| (p1, decls1) -> begin
((p1), ((FStar_List.flatten decls1)))
end)))))
in (FStar_All.pipe_right uu____12529 FStar_List.unzip))
in (match (uu____12516) with
| (pats, decls') -> begin
(

let uu____12727 = (encode_formula body env2)
in (match (uu____12727) with
| (body1, decls'') -> begin
(

let guards1 = (match (pats) with
| (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (gf), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____12759; FStar_SMTEncoding_Term.rng = uu____12760})::[])::[] when ((FStar_Ident.text_of_lid FStar_Parser_Const.guard_free) = gf) -> begin
[]
end
| uu____12775 -> begin
guards
end)
in (

let uu____12780 = (FStar_SMTEncoding_Util.mk_and_l guards1)
in ((vars), (pats), (uu____12780), (body1), ((FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') decls''))))))
end))
end))
end)))
in ((debug1 phi);
(

let phi1 = (FStar_Syntax_Util.unascribe phi)
in (

let check_pattern_vars = (fun vars pats -> (

let pats1 = (FStar_All.pipe_right pats (FStar_List.map (fun uu____12840 -> (match (uu____12840) with
| (x, uu____12846) -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x)
end))))
in (match (pats1) with
| [] -> begin
()
end
| (hd1)::tl1 -> begin
(

let pat_vars = (

let uu____12854 = (FStar_Syntax_Free.names hd1)
in (FStar_List.fold_left (fun out x -> (

let uu____12866 = (FStar_Syntax_Free.names x)
in (FStar_Util.set_union out uu____12866))) uu____12854 tl1))
in (

let uu____12869 = (FStar_All.pipe_right vars (FStar_Util.find_opt (fun uu____12896 -> (match (uu____12896) with
| (b, uu____12902) -> begin
(

let uu____12903 = (FStar_Util.set_mem b pat_vars)
in (not (uu____12903)))
end))))
in (match (uu____12869) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (x, uu____12909) -> begin
(

let pos = (FStar_List.fold_left (fun out t -> (FStar_Range.union_ranges out t.FStar_Syntax_Syntax.pos)) hd1.FStar_Syntax_Syntax.pos tl1)
in (

let uu____12923 = (

let uu____12924 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "SMT pattern misses at least one bound variable: %s" uu____12924))
in (FStar_Errors.warn pos uu____12923)))
end)))
end)))
in (

let uu____12925 = (FStar_Syntax_Util.destruct_typ_as_formula phi1)
in (match (uu____12925) with
| FStar_Pervasives_Native.None -> begin
(fallback phi1)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(

let uu____12934 = (FStar_All.pipe_right connectives (FStar_List.tryFind (fun uu____12992 -> (match (uu____12992) with
| (l, uu____13006) -> begin
(FStar_Ident.lid_equals op l)
end))))
in (match (uu____12934) with
| FStar_Pervasives_Native.None -> begin
(fallback phi1)
end
| FStar_Pervasives_Native.Some (uu____13039, f) -> begin
(f phi1.FStar_Syntax_Syntax.pos arms)
end))
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____13079 = (encode_q_body env vars pats body)
in (match (uu____13079) with
| (vars1, pats1, guard, body1, decls) -> begin
(

let tm = (

let uu____13124 = (

let uu____13135 = (FStar_SMTEncoding_Util.mkImp ((guard), (body1)))
in ((pats1), (vars1), (uu____13135)))
in (FStar_SMTEncoding_Term.mkForall uu____13124 phi1.FStar_Syntax_Syntax.pos))
in ((tm), (decls)))
end));
)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____13154 = (encode_q_body env vars pats body)
in (match (uu____13154) with
| (vars1, pats1, guard, body1, decls) -> begin
(

let uu____13198 = (

let uu____13199 = (

let uu____13210 = (FStar_SMTEncoding_Util.mkAnd ((guard), (body1)))
in ((pats1), (vars1), (uu____13210)))
in (FStar_SMTEncoding_Term.mkExists uu____13199 phi1.FStar_Syntax_Syntax.pos))
in ((uu____13198), (decls)))
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

let uu____13308 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____13308) with
| (asym, a) -> begin
(

let uu____13315 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____13315) with
| (xsym, x) -> begin
(

let uu____13322 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____13322) with
| (ysym, y) -> begin
(

let quant = (fun vars body x1 -> (

let xname_decl = (

let uu____13366 = (

let uu____13377 = (FStar_All.pipe_right vars (FStar_List.map FStar_Pervasives_Native.snd))
in ((x1), (uu____13377), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____13366))
in (

let xtok = (Prims.strcat x1 "@tok")
in (

let xtok_decl = FStar_SMTEncoding_Term.DeclFun (((xtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let xapp = (

let uu____13403 = (

let uu____13410 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((x1), (uu____13410)))
in (FStar_SMTEncoding_Util.mkApp uu____13403))
in (

let xtok1 = (FStar_SMTEncoding_Util.mkApp ((xtok), ([])))
in (

let xtok_app = (mk_Apply xtok1 vars)
in (

let uu____13423 = (

let uu____13426 = (

let uu____13429 = (

let uu____13432 = (

let uu____13433 = (

let uu____13440 = (

let uu____13441 = (

let uu____13452 = (FStar_SMTEncoding_Util.mkEq ((xapp), (body)))
in ((((xapp)::[])::[]), (vars), (uu____13452)))
in (FStar_SMTEncoding_Util.mkForall uu____13441))
in ((uu____13440), (FStar_Pervasives_Native.None), ((Prims.strcat "primitive_" x1))))
in (FStar_SMTEncoding_Util.mkAssume uu____13433))
in (

let uu____13469 = (

let uu____13472 = (

let uu____13473 = (

let uu____13480 = (

let uu____13481 = (

let uu____13492 = (FStar_SMTEncoding_Util.mkEq ((xtok_app), (xapp)))
in ((((xtok_app)::[])::[]), (vars), (uu____13492)))
in (FStar_SMTEncoding_Util.mkForall uu____13481))
in ((uu____13480), (FStar_Pervasives_Native.Some ("Name-token correspondence")), ((Prims.strcat "token_correspondence_" x1))))
in (FStar_SMTEncoding_Util.mkAssume uu____13473))
in (uu____13472)::[])
in (uu____13432)::uu____13469))
in (xtok_decl)::uu____13429)
in (xname_decl)::uu____13426)
in ((xtok1), (uu____13423))))))))))
in (

let axy = (((asym), (FStar_SMTEncoding_Term.Term_sort)))::(((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let xy = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let qx = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let prims1 = (

let uu____13583 = (

let uu____13596 = (

let uu____13605 = (

let uu____13606 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13606))
in (quant axy uu____13605))
in ((FStar_Parser_Const.op_Eq), (uu____13596)))
in (

let uu____13615 = (

let uu____13630 = (

let uu____13643 = (

let uu____13652 = (

let uu____13653 = (

let uu____13654 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_SMTEncoding_Util.mkNot uu____13654))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13653))
in (quant axy uu____13652))
in ((FStar_Parser_Const.op_notEq), (uu____13643)))
in (

let uu____13663 = (

let uu____13678 = (

let uu____13691 = (

let uu____13700 = (

let uu____13701 = (

let uu____13702 = (

let uu____13707 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13708 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13707), (uu____13708))))
in (FStar_SMTEncoding_Util.mkLT uu____13702))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13701))
in (quant xy uu____13700))
in ((FStar_Parser_Const.op_LT), (uu____13691)))
in (

let uu____13717 = (

let uu____13732 = (

let uu____13745 = (

let uu____13754 = (

let uu____13755 = (

let uu____13756 = (

let uu____13761 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13762 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13761), (uu____13762))))
in (FStar_SMTEncoding_Util.mkLTE uu____13756))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13755))
in (quant xy uu____13754))
in ((FStar_Parser_Const.op_LTE), (uu____13745)))
in (

let uu____13771 = (

let uu____13786 = (

let uu____13799 = (

let uu____13808 = (

let uu____13809 = (

let uu____13810 = (

let uu____13815 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13816 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13815), (uu____13816))))
in (FStar_SMTEncoding_Util.mkGT uu____13810))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13809))
in (quant xy uu____13808))
in ((FStar_Parser_Const.op_GT), (uu____13799)))
in (

let uu____13825 = (

let uu____13840 = (

let uu____13853 = (

let uu____13862 = (

let uu____13863 = (

let uu____13864 = (

let uu____13869 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13870 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13869), (uu____13870))))
in (FStar_SMTEncoding_Util.mkGTE uu____13864))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13863))
in (quant xy uu____13862))
in ((FStar_Parser_Const.op_GTE), (uu____13853)))
in (

let uu____13879 = (

let uu____13894 = (

let uu____13907 = (

let uu____13916 = (

let uu____13917 = (

let uu____13918 = (

let uu____13923 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13924 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13923), (uu____13924))))
in (FStar_SMTEncoding_Util.mkSub uu____13918))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____13917))
in (quant xy uu____13916))
in ((FStar_Parser_Const.op_Subtraction), (uu____13907)))
in (

let uu____13933 = (

let uu____13948 = (

let uu____13961 = (

let uu____13970 = (

let uu____13971 = (

let uu____13972 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Util.mkMinus uu____13972))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____13971))
in (quant qx uu____13970))
in ((FStar_Parser_Const.op_Minus), (uu____13961)))
in (

let uu____13981 = (

let uu____13996 = (

let uu____14009 = (

let uu____14018 = (

let uu____14019 = (

let uu____14020 = (

let uu____14025 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____14026 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____14025), (uu____14026))))
in (FStar_SMTEncoding_Util.mkAdd uu____14020))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____14019))
in (quant xy uu____14018))
in ((FStar_Parser_Const.op_Addition), (uu____14009)))
in (

let uu____14035 = (

let uu____14050 = (

let uu____14063 = (

let uu____14072 = (

let uu____14073 = (

let uu____14074 = (

let uu____14079 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____14080 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____14079), (uu____14080))))
in (FStar_SMTEncoding_Util.mkMul uu____14074))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____14073))
in (quant xy uu____14072))
in ((FStar_Parser_Const.op_Multiply), (uu____14063)))
in (

let uu____14089 = (

let uu____14104 = (

let uu____14117 = (

let uu____14126 = (

let uu____14127 = (

let uu____14128 = (

let uu____14133 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____14134 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____14133), (uu____14134))))
in (FStar_SMTEncoding_Util.mkDiv uu____14128))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____14127))
in (quant xy uu____14126))
in ((FStar_Parser_Const.op_Division), (uu____14117)))
in (

let uu____14143 = (

let uu____14158 = (

let uu____14171 = (

let uu____14180 = (

let uu____14181 = (

let uu____14182 = (

let uu____14187 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____14188 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____14187), (uu____14188))))
in (FStar_SMTEncoding_Util.mkMod uu____14182))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____14181))
in (quant xy uu____14180))
in ((FStar_Parser_Const.op_Modulus), (uu____14171)))
in (

let uu____14197 = (

let uu____14212 = (

let uu____14225 = (

let uu____14234 = (

let uu____14235 = (

let uu____14236 = (

let uu____14241 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____14242 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____14241), (uu____14242))))
in (FStar_SMTEncoding_Util.mkAnd uu____14236))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____14235))
in (quant xy uu____14234))
in ((FStar_Parser_Const.op_And), (uu____14225)))
in (

let uu____14251 = (

let uu____14266 = (

let uu____14279 = (

let uu____14288 = (

let uu____14289 = (

let uu____14290 = (

let uu____14295 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____14296 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____14295), (uu____14296))))
in (FStar_SMTEncoding_Util.mkOr uu____14290))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____14289))
in (quant xy uu____14288))
in ((FStar_Parser_Const.op_Or), (uu____14279)))
in (

let uu____14305 = (

let uu____14320 = (

let uu____14333 = (

let uu____14342 = (

let uu____14343 = (

let uu____14344 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Util.mkNot uu____14344))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____14343))
in (quant qx uu____14342))
in ((FStar_Parser_Const.op_Negation), (uu____14333)))
in (uu____14320)::[])
in (uu____14266)::uu____14305))
in (uu____14212)::uu____14251))
in (uu____14158)::uu____14197))
in (uu____14104)::uu____14143))
in (uu____14050)::uu____14089))
in (uu____13996)::uu____14035))
in (uu____13948)::uu____13981))
in (uu____13894)::uu____13933))
in (uu____13840)::uu____13879))
in (uu____13786)::uu____13825))
in (uu____13732)::uu____13771))
in (uu____13678)::uu____13717))
in (uu____13630)::uu____13663))
in (uu____13583)::uu____13615))
in (

let mk1 = (fun l v1 -> (

let uu____14558 = (

let uu____14567 = (FStar_All.pipe_right prims1 (FStar_List.find (fun uu____14625 -> (match (uu____14625) with
| (l', uu____14639) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right uu____14567 (FStar_Option.map (fun uu____14699 -> (match (uu____14699) with
| (uu____14718, b) -> begin
(b v1)
end)))))
in (FStar_All.pipe_right uu____14558 FStar_Option.get)))
in (

let is = (fun l -> (FStar_All.pipe_right prims1 (FStar_Util.for_some (fun uu____14789 -> (match (uu____14789) with
| (l', uu____14803) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk1; is = is})))))))
end))
end))
end))


let pretype_axiom : env_t  ->  FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun env tapp vars -> (

let uu____14844 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____14844) with
| (xxsym, xx) -> begin
(

let uu____14851 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____14851) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let tapp_hash = (FStar_SMTEncoding_Term.hash_of_term tapp)
in (

let module_name = env.current_module_name
in (

let uu____14861 = (

let uu____14868 = (

let uu____14869 = (

let uu____14880 = (

let uu____14881 = (

let uu____14886 = (

let uu____14887 = (

let uu____14892 = (FStar_SMTEncoding_Util.mkApp (("PreType"), ((xx)::[])))
in ((tapp), (uu____14892)))
in (FStar_SMTEncoding_Util.mkEq uu____14887))
in ((xx_has_type), (uu____14886)))
in (FStar_SMTEncoding_Util.mkImp uu____14881))
in ((((xx_has_type)::[])::[]), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars), (uu____14880)))
in (FStar_SMTEncoding_Util.mkForall uu____14869))
in (

let uu____14917 = (

let uu____14918 = (

let uu____14919 = (

let uu____14920 = (FStar_Util.digest_of_string tapp_hash)
in (Prims.strcat "_pretyping_" uu____14920))
in (Prims.strcat module_name uu____14919))
in (varops.mk_unique uu____14918))
in ((uu____14868), (FStar_Pervasives_Native.Some ("pretyping")), (uu____14917))))
in (FStar_SMTEncoding_Util.mkAssume uu____14861)))))
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

let uu____14960 = (

let uu____14961 = (

let uu____14968 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in ((uu____14968), (FStar_Pervasives_Native.Some ("unit typing")), ("unit_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____14961))
in (

let uu____14971 = (

let uu____14974 = (

let uu____14975 = (

let uu____14982 = (

let uu____14983 = (

let uu____14994 = (

let uu____14995 = (

let uu____15000 = (FStar_SMTEncoding_Util.mkEq ((x), (FStar_SMTEncoding_Term.mk_Term_unit)))
in ((typing_pred), (uu____15000)))
in (FStar_SMTEncoding_Util.mkImp uu____14995))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____14994)))
in (mkForall_fuel uu____14983))
in ((uu____14982), (FStar_Pervasives_Native.Some ("unit inversion")), ("unit_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____14975))
in (uu____14974)::[])
in (uu____14960)::uu____14971))))
in (

let mk_bool = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Bool_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____15042 = (

let uu____15043 = (

let uu____15050 = (

let uu____15051 = (

let uu____15062 = (

let uu____15067 = (

let uu____15070 = (FStar_SMTEncoding_Term.boxBool b)
in (uu____15070)::[])
in (uu____15067)::[])
in (

let uu____15075 = (

let uu____15076 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType uu____15076 tt))
in ((uu____15062), ((bb)::[]), (uu____15075))))
in (FStar_SMTEncoding_Util.mkForall uu____15051))
in ((uu____15050), (FStar_Pervasives_Native.Some ("bool typing")), ("bool_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____15043))
in (

let uu____15097 = (

let uu____15100 = (

let uu____15101 = (

let uu____15108 = (

let uu____15109 = (

let uu____15120 = (

let uu____15121 = (

let uu____15126 = (FStar_SMTEncoding_Term.mk_tester (FStar_Pervasives_Native.fst FStar_SMTEncoding_Term.boxBoolFun) x)
in ((typing_pred), (uu____15126)))
in (FStar_SMTEncoding_Util.mkImp uu____15121))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____15120)))
in (mkForall_fuel uu____15109))
in ((uu____15108), (FStar_Pervasives_Native.Some ("bool inversion")), ("bool_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____15101))
in (uu____15100)::[])
in (uu____15042)::uu____15097))))))
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

let uu____15176 = (

let uu____15177 = (

let uu____15184 = (

let uu____15187 = (

let uu____15190 = (

let uu____15193 = (FStar_SMTEncoding_Term.boxInt a)
in (

let uu____15194 = (

let uu____15197 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____15197)::[])
in (uu____15193)::uu____15194))
in (tt)::uu____15190)
in (tt)::uu____15187)
in (("Prims.Precedes"), (uu____15184)))
in (FStar_SMTEncoding_Util.mkApp uu____15177))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15176))
in (

let precedes_y_x = (

let uu____15201 = (FStar_SMTEncoding_Util.mkApp (("Precedes"), ((y)::(x)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15201))
in (

let uu____15204 = (

let uu____15205 = (

let uu____15212 = (

let uu____15213 = (

let uu____15224 = (

let uu____15229 = (

let uu____15232 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____15232)::[])
in (uu____15229)::[])
in (

let uu____15237 = (

let uu____15238 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType uu____15238 tt))
in ((uu____15224), ((bb)::[]), (uu____15237))))
in (FStar_SMTEncoding_Util.mkForall uu____15213))
in ((uu____15212), (FStar_Pervasives_Native.Some ("int typing")), ("int_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____15205))
in (

let uu____15259 = (

let uu____15262 = (

let uu____15263 = (

let uu____15270 = (

let uu____15271 = (

let uu____15282 = (

let uu____15283 = (

let uu____15288 = (FStar_SMTEncoding_Term.mk_tester (FStar_Pervasives_Native.fst FStar_SMTEncoding_Term.boxIntFun) x)
in ((typing_pred), (uu____15288)))
in (FStar_SMTEncoding_Util.mkImp uu____15283))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____15282)))
in (mkForall_fuel uu____15271))
in ((uu____15270), (FStar_Pervasives_Native.Some ("int inversion")), ("int_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____15263))
in (

let uu____15313 = (

let uu____15316 = (

let uu____15317 = (

let uu____15324 = (

let uu____15325 = (

let uu____15336 = (

let uu____15337 = (

let uu____15342 = (

let uu____15343 = (

let uu____15346 = (

let uu____15349 = (

let uu____15352 = (

let uu____15353 = (

let uu____15358 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____15359 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____15358), (uu____15359))))
in (FStar_SMTEncoding_Util.mkGT uu____15353))
in (

let uu____15360 = (

let uu____15363 = (

let uu____15364 = (

let uu____15369 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____15370 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____15369), (uu____15370))))
in (FStar_SMTEncoding_Util.mkGTE uu____15364))
in (

let uu____15371 = (

let uu____15374 = (

let uu____15375 = (

let uu____15380 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____15381 = (FStar_SMTEncoding_Term.unboxInt x)
in ((uu____15380), (uu____15381))))
in (FStar_SMTEncoding_Util.mkLT uu____15375))
in (uu____15374)::[])
in (uu____15363)::uu____15371))
in (uu____15352)::uu____15360))
in (typing_pred_y)::uu____15349)
in (typing_pred)::uu____15346)
in (FStar_SMTEncoding_Util.mk_and_l uu____15343))
in ((uu____15342), (precedes_y_x)))
in (FStar_SMTEncoding_Util.mkImp uu____15337))
in ((((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[]), ((xx)::(yy)::[]), (uu____15336)))
in (mkForall_fuel uu____15325))
in ((uu____15324), (FStar_Pervasives_Native.Some ("well-founded ordering on nat (alt)")), ("well-founded-ordering-on-nat")))
in (FStar_SMTEncoding_Util.mkAssume uu____15317))
in (uu____15316)::[])
in (uu____15262)::uu____15313))
in (uu____15204)::uu____15259)))))))))))
in (

let mk_str = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.String_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____15427 = (

let uu____15428 = (

let uu____15435 = (

let uu____15436 = (

let uu____15447 = (

let uu____15452 = (

let uu____15455 = (FStar_SMTEncoding_Term.boxString b)
in (uu____15455)::[])
in (uu____15452)::[])
in (

let uu____15460 = (

let uu____15461 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType uu____15461 tt))
in ((uu____15447), ((bb)::[]), (uu____15460))))
in (FStar_SMTEncoding_Util.mkForall uu____15436))
in ((uu____15435), (FStar_Pervasives_Native.Some ("string typing")), ("string_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____15428))
in (

let uu____15482 = (

let uu____15485 = (

let uu____15486 = (

let uu____15493 = (

let uu____15494 = (

let uu____15505 = (

let uu____15506 = (

let uu____15511 = (FStar_SMTEncoding_Term.mk_tester (FStar_Pervasives_Native.fst FStar_SMTEncoding_Term.boxStringFun) x)
in ((typing_pred), (uu____15511)))
in (FStar_SMTEncoding_Util.mkImp uu____15506))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____15505)))
in (mkForall_fuel uu____15494))
in ((uu____15493), (FStar_Pervasives_Native.Some ("string inversion")), ("string_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____15486))
in (uu____15485)::[])
in (uu____15427)::uu____15482))))))
in (

let mk_true_interp = (fun env nm true_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((true_tm)::[])))
in ((FStar_SMTEncoding_Util.mkAssume ((valid), (FStar_Pervasives_Native.Some ("True interpretation")), ("true_interp"))))::[]))
in (

let mk_false_interp = (fun env nm false_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((false_tm)::[])))
in (

let uu____15564 = (

let uu____15565 = (

let uu____15572 = (FStar_SMTEncoding_Util.mkIff ((FStar_SMTEncoding_Util.mkFalse), (valid)))
in ((uu____15572), (FStar_Pervasives_Native.Some ("False interpretation")), ("false_interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15565))
in (uu____15564)::[])))
in (

let mk_and_interp = (fun env conj uu____15584 -> (

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

let uu____15609 = (

let uu____15610 = (

let uu____15617 = (

let uu____15618 = (

let uu____15629 = (

let uu____15630 = (

let uu____15635 = (FStar_SMTEncoding_Util.mkAnd ((valid_a), (valid_b)))
in ((uu____15635), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____15630))
in ((((l_and_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____15629)))
in (FStar_SMTEncoding_Util.mkForall uu____15618))
in ((uu____15617), (FStar_Pervasives_Native.Some ("/\\ interpretation")), ("l_and-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15610))
in (uu____15609)::[]))))))))))
in (

let mk_or_interp = (fun env disj uu____15673 -> (

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

let uu____15698 = (

let uu____15699 = (

let uu____15706 = (

let uu____15707 = (

let uu____15718 = (

let uu____15719 = (

let uu____15724 = (FStar_SMTEncoding_Util.mkOr ((valid_a), (valid_b)))
in ((uu____15724), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____15719))
in ((((l_or_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____15718)))
in (FStar_SMTEncoding_Util.mkForall uu____15707))
in ((uu____15706), (FStar_Pervasives_Native.Some ("\\/ interpretation")), ("l_or-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15699))
in (uu____15698)::[]))))))))))
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

let uu____15787 = (

let uu____15788 = (

let uu____15795 = (

let uu____15796 = (

let uu____15807 = (

let uu____15808 = (

let uu____15813 = (FStar_SMTEncoding_Util.mkEq ((x1), (y1)))
in ((uu____15813), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____15808))
in ((((eq2_x_y)::[])::[]), ((aa)::(xx1)::(yy1)::[]), (uu____15807)))
in (FStar_SMTEncoding_Util.mkForall uu____15796))
in ((uu____15795), (FStar_Pervasives_Native.Some ("Eq2 interpretation")), ("eq2-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15788))
in (uu____15787)::[]))))))))))
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

let uu____15886 = (

let uu____15887 = (

let uu____15894 = (

let uu____15895 = (

let uu____15906 = (

let uu____15907 = (

let uu____15912 = (FStar_SMTEncoding_Util.mkEq ((x1), (y1)))
in ((uu____15912), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____15907))
in ((((eq3_x_y)::[])::[]), ((aa)::(bb)::(xx1)::(yy1)::[]), (uu____15906)))
in (FStar_SMTEncoding_Util.mkForall uu____15895))
in ((uu____15894), (FStar_Pervasives_Native.Some ("Eq3 interpretation")), ("eq3-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15887))
in (uu____15886)::[]))))))))))))
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

let uu____15983 = (

let uu____15984 = (

let uu____15991 = (

let uu____15992 = (

let uu____16003 = (

let uu____16004 = (

let uu____16009 = (FStar_SMTEncoding_Util.mkImp ((valid_a), (valid_b)))
in ((uu____16009), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____16004))
in ((((l_imp_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____16003)))
in (FStar_SMTEncoding_Util.mkForall uu____15992))
in ((uu____15991), (FStar_Pervasives_Native.Some ("==> interpretation")), ("l_imp-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15984))
in (uu____15983)::[]))))))))))
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

let uu____16072 = (

let uu____16073 = (

let uu____16080 = (

let uu____16081 = (

let uu____16092 = (

let uu____16093 = (

let uu____16098 = (FStar_SMTEncoding_Util.mkIff ((valid_a), (valid_b)))
in ((uu____16098), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____16093))
in ((((l_iff_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____16092)))
in (FStar_SMTEncoding_Util.mkForall uu____16081))
in ((uu____16080), (FStar_Pervasives_Native.Some ("<==> interpretation")), ("l_iff-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16073))
in (uu____16072)::[]))))))))))
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

let uu____16150 = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____16150))
in (

let uu____16153 = (

let uu____16154 = (

let uu____16161 = (

let uu____16162 = (

let uu____16173 = (FStar_SMTEncoding_Util.mkIff ((not_valid_a), (valid)))
in ((((l_not_a)::[])::[]), ((aa)::[]), (uu____16173)))
in (FStar_SMTEncoding_Util.mkForall uu____16162))
in ((uu____16161), (FStar_Pervasives_Native.Some ("not interpretation")), ("l_not-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16154))
in (uu____16153)::[])))))))
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

let uu____16233 = (

let uu____16240 = (

let uu____16243 = (FStar_SMTEncoding_Util.mk_ApplyTT b x1)
in (uu____16243)::[])
in (("Valid"), (uu____16240)))
in (FStar_SMTEncoding_Util.mkApp uu____16233))
in (

let uu____16246 = (

let uu____16247 = (

let uu____16254 = (

let uu____16255 = (

let uu____16266 = (

let uu____16267 = (

let uu____16272 = (

let uu____16273 = (

let uu____16284 = (

let uu____16289 = (

let uu____16292 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in (uu____16292)::[])
in (uu____16289)::[])
in (

let uu____16297 = (

let uu____16298 = (

let uu____16303 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in ((uu____16303), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp uu____16298))
in ((uu____16284), ((xx1)::[]), (uu____16297))))
in (FStar_SMTEncoding_Util.mkForall uu____16273))
in ((uu____16272), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____16267))
in ((((l_forall_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____16266)))
in (FStar_SMTEncoding_Util.mkForall uu____16255))
in ((uu____16254), (FStar_Pervasives_Native.Some ("forall interpretation")), ("forall-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16247))
in (uu____16246)::[])))))))))))
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

let uu____16385 = (

let uu____16392 = (

let uu____16395 = (FStar_SMTEncoding_Util.mk_ApplyTT b x1)
in (uu____16395)::[])
in (("Valid"), (uu____16392)))
in (FStar_SMTEncoding_Util.mkApp uu____16385))
in (

let uu____16398 = (

let uu____16399 = (

let uu____16406 = (

let uu____16407 = (

let uu____16418 = (

let uu____16419 = (

let uu____16424 = (

let uu____16425 = (

let uu____16436 = (

let uu____16441 = (

let uu____16444 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in (uu____16444)::[])
in (uu____16441)::[])
in (

let uu____16449 = (

let uu____16450 = (

let uu____16455 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in ((uu____16455), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp uu____16450))
in ((uu____16436), ((xx1)::[]), (uu____16449))))
in (FStar_SMTEncoding_Util.mkExists uu____16425))
in ((uu____16424), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____16419))
in ((((l_exists_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____16418)))
in (FStar_SMTEncoding_Util.mkForall uu____16407))
in ((uu____16406), (FStar_Pervasives_Native.Some ("exists interpretation")), ("exists-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16399))
in (uu____16398)::[])))))))))))
in (

let mk_range_interp = (fun env range tt -> (

let range_ty = (FStar_SMTEncoding_Util.mkApp ((range), ([])))
in (

let uu____16515 = (

let uu____16516 = (

let uu____16523 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_ty)
in (

let uu____16524 = (varops.mk_unique "typing_range_const")
in ((uu____16523), (FStar_Pervasives_Native.Some ("Range_const typing")), (uu____16524))))
in (FStar_SMTEncoding_Util.mkAssume uu____16516))
in (uu____16515)::[])))
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

let uu____16558 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1"))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16558 x1 t))
in (

let uu____16559 = (

let uu____16570 = (FStar_SMTEncoding_Util.mkImp ((hastypeZ), (hastypeS)))
in ((((hastypeZ)::[])::[]), ((xx1)::[]), (uu____16570)))
in (FStar_SMTEncoding_Util.mkForall uu____16559))))
in (

let uu____16593 = (

let uu____16594 = (

let uu____16601 = (

let uu____16602 = (

let uu____16613 = (FStar_SMTEncoding_Util.mkImp ((valid), (body)))
in ((((inversion_t)::[])::[]), ((tt1)::[]), (uu____16613)))
in (FStar_SMTEncoding_Util.mkForall uu____16602))
in ((uu____16601), (FStar_Pervasives_Native.Some ("inversion interpretation")), ("inversion-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16594))
in (uu____16593)::[])))))))))
in (

let prims1 = (((FStar_Parser_Const.unit_lid), (mk_unit)))::(((FStar_Parser_Const.bool_lid), (mk_bool)))::(((FStar_Parser_Const.int_lid), (mk_int)))::(((FStar_Parser_Const.string_lid), (mk_str)))::(((FStar_Parser_Const.true_lid), (mk_true_interp)))::(((FStar_Parser_Const.false_lid), (mk_false_interp)))::(((FStar_Parser_Const.and_lid), (mk_and_interp)))::(((FStar_Parser_Const.or_lid), (mk_or_interp)))::(((FStar_Parser_Const.eq2_lid), (mk_eq2_interp)))::(((FStar_Parser_Const.eq3_lid), (mk_eq3_interp)))::(((FStar_Parser_Const.imp_lid), (mk_imp_interp)))::(((FStar_Parser_Const.iff_lid), (mk_iff_interp)))::(((FStar_Parser_Const.not_lid), (mk_not_interp)))::(((FStar_Parser_Const.forall_lid), (mk_forall_interp)))::(((FStar_Parser_Const.exists_lid), (mk_exists_interp)))::(((FStar_Parser_Const.range_lid), (mk_range_interp)))::(((FStar_Parser_Const.inversion_lid), (mk_inversion_axiom)))::[]
in (fun env t s tt -> (

let uu____16937 = (FStar_Util.find_opt (fun uu____16963 -> (match (uu____16963) with
| (l, uu____16975) -> begin
(FStar_Ident.lid_equals l t)
end)) prims1)
in (match (uu____16937) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (uu____17000, f) -> begin
(f env s tt)
end)))))))))))))))))))))))))


let encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____17039 = (encode_function_type_as_formula t env)
in (match (uu____17039) with
| (form, decls) -> begin
(FStar_List.append decls (((FStar_SMTEncoding_Util.mkAssume ((form), (FStar_Pervasives_Native.Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str))), ((Prims.strcat "lemma_" lid.FStar_Ident.str)))))::[]))
end))))


let encode_free_var : Prims.bool  ->  env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun uninterpreted env fv tt t_norm quals -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____17085 = (((

let uu____17088 = ((FStar_Syntax_Util.is_pure_or_ghost_function t_norm) || (FStar_TypeChecker_Env.is_reifiable_function env.tcenv t_norm))
in (FStar_All.pipe_left Prims.op_Negation uu____17088)) || (FStar_Syntax_Util.is_lemma t_norm)) || uninterpreted)
in (match (uu____17085) with
| true -> begin
(

let uu____17095 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____17095) with
| (vname, vtok, env1) -> begin
(

let arg_sorts = (

let uu____17114 = (

let uu____17115 = (FStar_Syntax_Subst.compress t_norm)
in uu____17115.FStar_Syntax_Syntax.n)
in (match (uu____17114) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____17121) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun uu____17151 -> FStar_SMTEncoding_Term.Term_sort)))
end
| uu____17156 -> begin
[]
end))
in (

let d = FStar_SMTEncoding_Term.DeclFun (((vname), (arg_sorts), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Uninterpreted function symbol for impure function"))))
in (

let dd = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Uninterpreted name for impure function"))))
in (((d)::(dd)::[]), (env1)))))
end))
end
| uu____17169 -> begin
(

let uu____17170 = (prims.is lid)
in (match (uu____17170) with
| true -> begin
(

let vname = (varops.new_fvar lid)
in (

let uu____17178 = (prims.mk lid vname)
in (match (uu____17178) with
| (tok, definition) -> begin
(

let env1 = (push_free_var env lid vname (FStar_Pervasives_Native.Some (tok)))
in ((definition), (env1)))
end)))
end
| uu____17200 -> begin
(

let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (

let uu____17202 = (

let uu____17213 = (curried_arrow_formals_comp t_norm)
in (match (uu____17213) with
| (args, comp) -> begin
(

let comp1 = (

let uu____17231 = (FStar_TypeChecker_Env.is_reifiable_comp env.tcenv comp)
in (match (uu____17231) with
| true -> begin
(

let uu____17232 = (FStar_TypeChecker_Env.reify_comp (

let uu___147_17235 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___147_17235.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___147_17235.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___147_17235.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___147_17235.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___147_17235.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___147_17235.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___147_17235.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___147_17235.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___147_17235.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___147_17235.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___147_17235.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___147_17235.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___147_17235.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___147_17235.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___147_17235.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___147_17235.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___147_17235.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___147_17235.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___147_17235.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___147_17235.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___147_17235.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.type_of = uu___147_17235.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___147_17235.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___147_17235.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___147_17235.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___147_17235.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___147_17235.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___147_17235.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___147_17235.FStar_TypeChecker_Env.identifier_info}) comp FStar_Syntax_Syntax.U_unknown)
in (FStar_Syntax_Syntax.mk_Total uu____17232))
end
| uu____17236 -> begin
comp
end))
in (match (encode_non_total_function_typ) with
| true -> begin
(

let uu____17247 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp1)
in ((args), (uu____17247)))
end
| uu____17260 -> begin
((args), (((FStar_Pervasives_Native.None), ((FStar_Syntax_Util.comp_result comp1)))))
end))
end))
in (match (uu____17202) with
| (formals, (pre_opt, res_t)) -> begin
(

let uu____17292 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____17292) with
| (vname, vtok, env1) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
end
| uu____17313 -> begin
(FStar_SMTEncoding_Util.mkApp ((vtok), ([])))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun uu___119_17355 -> (match (uu___119_17355) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(

let uu____17359 = (FStar_Util.prefix vars)
in (match (uu____17359) with
| (uu____17380, (xxsym, uu____17382)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____17400 = (

let uu____17401 = (

let uu____17408 = (

let uu____17409 = (

let uu____17420 = (

let uu____17421 = (

let uu____17426 = (

let uu____17427 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____17427))
in ((vapp), (uu____17426)))
in (FStar_SMTEncoding_Util.mkEq uu____17421))
in ((((vapp)::[])::[]), (vars), (uu____17420)))
in (FStar_SMTEncoding_Util.mkForall uu____17409))
in ((uu____17408), (FStar_Pervasives_Native.Some ("Discriminator equation")), ((Prims.strcat "disc_equation_" (escape d.FStar_Ident.str)))))
in (FStar_SMTEncoding_Util.mkAssume uu____17401))
in (uu____17400)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(

let uu____17446 = (FStar_Util.prefix vars)
in (match (uu____17446) with
| (uu____17467, (xxsym, uu____17469)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f1 = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (

let tp_name = (mk_term_projector_name d f1)
in (

let prim_app = (FStar_SMTEncoding_Util.mkApp ((tp_name), ((xx)::[])))
in (

let uu____17492 = (

let uu____17493 = (

let uu____17500 = (

let uu____17501 = (

let uu____17512 = (FStar_SMTEncoding_Util.mkEq ((vapp), (prim_app)))
in ((((vapp)::[])::[]), (vars), (uu____17512)))
in (FStar_SMTEncoding_Util.mkForall uu____17501))
in ((uu____17500), (FStar_Pervasives_Native.Some ("Projector equation")), ((Prims.strcat "proj_equation_" tp_name))))
in (FStar_SMTEncoding_Util.mkAssume uu____17493))
in (uu____17492)::[])))))
end))
end
| uu____17529 -> begin
[]
end)))))
in (

let uu____17530 = (encode_binders FStar_Pervasives_Native.None formals env1)
in (match (uu____17530) with
| (vars, guards, env', decls1, uu____17557) -> begin
(

let uu____17570 = (match (pre_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____17579 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____17579), (decls1)))
end
| FStar_Pervasives_Native.Some (p) -> begin
(

let uu____17581 = (encode_formula p env')
in (match (uu____17581) with
| (g, ds) -> begin
(

let uu____17592 = (FStar_SMTEncoding_Util.mk_and_l ((g)::guards))
in ((uu____17592), ((FStar_List.append decls1 ds))))
end))
end)
in (match (uu____17570) with
| (guard, decls11) -> begin
(

let vtok_app = (mk_Apply vtok_tm vars)
in (

let vapp = (

let uu____17605 = (

let uu____17612 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((vname), (uu____17612)))
in (FStar_SMTEncoding_Util.mkApp uu____17605))
in (

let uu____17621 = (

let vname_decl = (

let uu____17629 = (

let uu____17640 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____17650 -> FStar_SMTEncoding_Term.Term_sort)))
in ((vname), (uu____17640), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____17629))
in (

let uu____17659 = (

let env2 = (

let uu___148_17665 = env1
in {bindings = uu___148_17665.bindings; depth = uu___148_17665.depth; tcenv = uu___148_17665.tcenv; warn = uu___148_17665.warn; cache = uu___148_17665.cache; nolabels = uu___148_17665.nolabels; use_zfuel_name = uu___148_17665.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = uu___148_17665.current_module_name})
in (

let uu____17666 = (

let uu____17667 = (head_normal env2 tt)
in (not (uu____17667)))
in (match (uu____17666) with
| true -> begin
(encode_term_pred FStar_Pervasives_Native.None tt env2 vtok_tm)
end
| uu____17672 -> begin
(encode_term_pred FStar_Pervasives_Native.None t_norm env2 vtok_tm)
end)))
in (match (uu____17659) with
| (tok_typing, decls2) -> begin
(

let tok_typing1 = (match (formals) with
| (uu____17682)::uu____17683 -> begin
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

let uu____17723 = (

let uu____17734 = (FStar_SMTEncoding_Term.mk_NoHoist f tok_typing)
in ((((vtok_app_l)::[])::((vtok_app_r)::[])::[]), ((ff)::[]), (uu____17734)))
in (FStar_SMTEncoding_Util.mkForall uu____17723))
in (FStar_SMTEncoding_Util.mkAssume ((guarded_tok_typing), (FStar_Pervasives_Native.Some ("function token typing")), ((Prims.strcat "function_token_typing_" vname)))))))))
end
| uu____17761 -> begin
(FStar_SMTEncoding_Util.mkAssume ((tok_typing), (FStar_Pervasives_Native.Some ("function token typing")), ((Prims.strcat "function_token_typing_" vname))))
end)
in (

let uu____17764 = (match (formals) with
| [] -> begin
(

let uu____17781 = (

let uu____17782 = (

let uu____17785 = (FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left (fun _0_43 -> FStar_Pervasives_Native.Some (_0_43)) uu____17785))
in (push_free_var env1 lid vname uu____17782))
in (((FStar_List.append decls2 ((tok_typing1)::[]))), (uu____17781)))
end
| uu____17790 -> begin
(

let vtok_decl = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let vtok_fresh = (

let uu____17797 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((vtok), (FStar_SMTEncoding_Term.Term_sort)) uu____17797))
in (

let name_tok_corr = (

let uu____17799 = (

let uu____17806 = (

let uu____17807 = (

let uu____17818 = (FStar_SMTEncoding_Util.mkEq ((vtok_app), (vapp)))
in ((((vtok_app)::[])::((vapp)::[])::[]), (vars), (uu____17818)))
in (FStar_SMTEncoding_Util.mkForall uu____17807))
in ((uu____17806), (FStar_Pervasives_Native.Some ("Name-token correspondence")), ((Prims.strcat "token_correspondence_" vname))))
in (FStar_SMTEncoding_Util.mkAssume uu____17799))
in (((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing1)::[]))), (env1)))))
end)
in (match (uu____17764) with
| (tok_decl, env2) -> begin
(((vname_decl)::tok_decl), (env2))
end)))
end)))
in (match (uu____17621) with
| (decls2, env2) -> begin
(

let uu____17861 = (

let res_t1 = (FStar_Syntax_Subst.compress res_t)
in (

let uu____17869 = (encode_term res_t1 env')
in (match (uu____17869) with
| (encoded_res_t, decls) -> begin
(

let uu____17882 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in ((encoded_res_t), (uu____17882), (decls)))
end)))
in (match (uu____17861) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (

let uu____17893 = (

let uu____17900 = (

let uu____17901 = (

let uu____17912 = (FStar_SMTEncoding_Util.mkImp ((guard), (ty_pred)))
in ((((vapp)::[])::[]), (vars), (uu____17912)))
in (FStar_SMTEncoding_Util.mkForall uu____17901))
in ((uu____17900), (FStar_Pervasives_Native.Some ("free var typing")), ((Prims.strcat "typing_" vname))))
in (FStar_SMTEncoding_Util.mkAssume uu____17893))
in (

let freshness = (

let uu____17928 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New))
in (match (uu____17928) with
| true -> begin
(

let uu____17933 = (

let uu____17934 = (

let uu____17945 = (FStar_All.pipe_right vars (FStar_List.map FStar_Pervasives_Native.snd))
in (

let uu____17956 = (varops.next_id ())
in ((vname), (uu____17945), (FStar_SMTEncoding_Term.Term_sort), (uu____17956))))
in (FStar_SMTEncoding_Term.fresh_constructor uu____17934))
in (

let uu____17959 = (

let uu____17962 = (pretype_axiom env2 vapp vars)
in (uu____17962)::[])
in (uu____17933)::uu____17959))
end
| uu____17963 -> begin
[]
end))
in (

let g = (

let uu____17967 = (

let uu____17970 = (

let uu____17973 = (

let uu____17976 = (

let uu____17979 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::uu____17979)
in (FStar_List.append freshness uu____17976))
in (FStar_List.append decls3 uu____17973))
in (FStar_List.append decls2 uu____17970))
in (FStar_List.append decls11 uu____17967))
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

let uu____18014 = (try_lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____18014) with
| FStar_Pervasives_Native.None -> begin
(

let uu____18051 = (encode_free_var false env x t t_norm [])
in (match (uu____18051) with
| (decls, env1) -> begin
(

let uu____18078 = (lookup_lid env1 x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____18078) with
| (n1, x', uu____18105) -> begin
((((n1), (x'))), (decls), (env1))
end))
end))
end
| FStar_Pervasives_Native.Some (n1, x1, uu____18126) -> begin
((((n1), (x1))), ([]), (env))
end)))


let encode_top_level_val : Prims.bool  ->  env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun uninterpreted env lid t quals -> (

let tt = (norm env t)
in (

let uu____18186 = (encode_free_var uninterpreted env lid t tt quals)
in (match (uu____18186) with
| (decls, env1) -> begin
(

let uu____18205 = (FStar_Syntax_Util.is_smt_lemma t)
in (match (uu____18205) with
| true -> begin
(

let uu____18212 = (

let uu____18215 = (encode_smt_lemma env1 lid tt)
in (FStar_List.append decls uu____18215))
in ((uu____18212), (env1)))
end
| uu____18220 -> begin
((decls), (env1))
end))
end))))


let encode_top_level_vals : env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____18270 lb -> (match (uu____18270) with
| (decls, env1) -> begin
(

let uu____18290 = (

let uu____18297 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val false env1 uu____18297 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (uu____18290) with
| (decls', env2) -> begin
(((FStar_List.append decls decls')), (env2))
end))
end)) (([]), (env)))))


let is_tactic : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let fstar_tactics_tactic_lid = (FStar_Parser_Const.p2l (("FStar")::("Tactics")::("tactic")::[]))
in (

let uu____18319 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____18319) with
| (hd1, args) -> begin
(

let uu____18356 = (

let uu____18357 = (FStar_Syntax_Util.un_uinst hd1)
in uu____18357.FStar_Syntax_Syntax.n)
in (match (uu____18356) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____18361, c) -> begin
(

let effect_name = (FStar_Syntax_Util.comp_effect_name c)
in (FStar_Util.starts_with "FStar.Tactics" effect_name.FStar_Ident.str))
end
| uu____18380 -> begin
false
end))
end))))


let encode_top_level_let : env_t  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env uu____18405 quals -> (match (uu____18405) with
| (is_rec, bindings) -> begin
(

let eta_expand1 = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let uu____18481 = (FStar_Util.first_N nbinders formals)
in (match (uu____18481) with
| (formals1, extra_formals) -> begin
(

let subst1 = (FStar_List.map2 (fun uu____18562 uu____18563 -> (match (((uu____18562), (uu____18563))) with
| ((formal, uu____18581), (binder, uu____18583)) -> begin
(

let uu____18592 = (

let uu____18599 = (FStar_Syntax_Syntax.bv_to_name binder)
in ((formal), (uu____18599)))
in FStar_Syntax_Syntax.NT (uu____18592))
end)) formals1 binders)
in (

let extra_formals1 = (

let uu____18607 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun uu____18638 -> (match (uu____18638) with
| (x, i) -> begin
(

let uu____18649 = (

let uu___149_18650 = x
in (

let uu____18651 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___149_18650.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___149_18650.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____18651}))
in ((uu____18649), (i)))
end))))
in (FStar_All.pipe_right uu____18607 FStar_Syntax_Util.name_binders))
in (

let body1 = (

let uu____18669 = (

let uu____18670 = (FStar_Syntax_Subst.compress body)
in (

let uu____18671 = (

let uu____18672 = (FStar_Syntax_Util.args_of_binders extra_formals1)
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____18672))
in (FStar_Syntax_Syntax.extend_app_n uu____18670 uu____18671)))
in (uu____18669 FStar_Pervasives_Native.None body.FStar_Syntax_Syntax.pos))
in (((FStar_List.append binders extra_formals1)), (body1)))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (

let get_result_type = (fun c -> (

let uu____18733 = (FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c)
in (match (uu____18733) with
| true -> begin
(FStar_TypeChecker_Env.reify_comp (

let uu___150_18736 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___150_18736.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___150_18736.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___150_18736.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___150_18736.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___150_18736.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___150_18736.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___150_18736.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___150_18736.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___150_18736.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___150_18736.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___150_18736.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___150_18736.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___150_18736.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___150_18736.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___150_18736.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___150_18736.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___150_18736.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___150_18736.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___150_18736.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___150_18736.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___150_18736.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.type_of = uu___150_18736.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___150_18736.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___150_18736.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___150_18736.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___150_18736.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___150_18736.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___150_18736.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___150_18736.FStar_TypeChecker_Env.identifier_info}) c FStar_Syntax_Syntax.U_unknown)
end
| uu____18737 -> begin
(FStar_Syntax_Util.comp_result c)
end)))
in (

let rec aux = (fun norm1 t_norm1 -> (

let uu____18769 = (FStar_Syntax_Util.abs_formals e)
in (match (uu____18769) with
| (binders, body, lopt) -> begin
(match (binders) with
| (uu____18833)::uu____18834 -> begin
(

let uu____18849 = (

let uu____18850 = (FStar_Syntax_Subst.compress t_norm1)
in uu____18850.FStar_Syntax_Syntax.n)
in (match (uu____18849) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____18895 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____18895) with
| (formals1, c1) -> begin
(

let nformals = (FStar_List.length formals1)
in (

let nbinders = (FStar_List.length binders)
in (

let tres = (get_result_type c1)
in (

let uu____18937 = ((nformals < nbinders) && (FStar_Syntax_Util.is_total_comp c1))
in (match (uu____18937) with
| true -> begin
(

let uu____18972 = (FStar_Util.first_N nformals binders)
in (match (uu____18972) with
| (bs0, rest) -> begin
(

let c2 = (

let subst1 = (FStar_List.map2 (fun uu____19066 uu____19067 -> (match (((uu____19066), (uu____19067))) with
| ((x, uu____19085), (b, uu____19087)) -> begin
(

let uu____19096 = (

let uu____19103 = (FStar_Syntax_Syntax.bv_to_name b)
in ((x), (uu____19103)))
in FStar_Syntax_Syntax.NT (uu____19096))
end)) formals1 bs0)
in (FStar_Syntax_Subst.subst_comp subst1 c1))
in (

let body1 = (FStar_Syntax_Util.abs rest body lopt)
in (

let uu____19105 = (

let uu____19126 = (get_result_type c2)
in ((bs0), (body1), (bs0), (uu____19126)))
in ((uu____19105), (false)))))
end))
end
| uu____19159 -> begin
(match ((nformals > nbinders)) with
| true -> begin
(

let uu____19194 = (eta_expand1 binders formals1 body tres)
in (match (uu____19194) with
| (binders1, body1) -> begin
((((binders1), (body1), (formals1), (tres))), (false))
end))
end
| uu____19273 -> begin
((((binders), (body), (formals1), (tres))), (false))
end)
end)))))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____19283) -> begin
(

let uu____19288 = (

let uu____19309 = (aux norm1 x.FStar_Syntax_Syntax.sort)
in (FStar_Pervasives_Native.fst uu____19309))
in ((uu____19288), (true)))
end
| uu____19374 when (not (norm1)) -> begin
(

let t_norm2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm1)
in (aux true t_norm2))
end
| uu____19376 -> begin
(

let uu____19377 = (

let uu____19378 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____19379 = (FStar_Syntax_Print.term_to_string t_norm1)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str uu____19378 uu____19379)))
in (failwith uu____19377))
end))
end
| uu____19404 -> begin
(

let uu____19405 = (

let uu____19406 = (FStar_Syntax_Subst.compress t_norm1)
in uu____19406.FStar_Syntax_Syntax.n)
in (match (uu____19405) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____19451 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____19451) with
| (formals1, c1) -> begin
(

let tres = (get_result_type c1)
in (

let uu____19483 = (eta_expand1 [] formals1 e tres)
in (match (uu____19483) with
| (binders1, body1) -> begin
((((binders1), (body1), (formals1), (tres))), (false))
end)))
end))
end
| uu____19566 -> begin
(((([]), (e), ([]), (t_norm1))), (false))
end))
end)
end)))
in (aux false t_norm))))
in try
(match (()) with
| () -> begin
(

let uu____19622 = (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> ((FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))))
in (match (uu____19622) with
| true -> begin
(encode_top_level_vals env bindings quals)
end
| uu____19633 -> begin
(

let uu____19634 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____19728 lb -> (match (uu____19728) with
| (toks, typs, decls, env1) -> begin
((

let uu____19823 = (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp)
in (match (uu____19823) with
| true -> begin
(FStar_Exn.raise Let_rec_unencodeable)
end
| uu____19824 -> begin
()
end));
(

let t_norm = (whnf env1 lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____19826 = (

let uu____19841 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env1 uu____19841 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (uu____19826) with
| (tok, decl, env2) -> begin
(

let uu____19887 = (

let uu____19900 = (

let uu____19911 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in ((uu____19911), (tok)))
in (uu____19900)::toks)
in ((uu____19887), ((t_norm)::typs), ((decl)::decls), (env2)))
end)));
)
end)) (([]), ([]), ([]), (env))))
in (match (uu____19634) with
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
| uu____20094 -> begin
(match (curry) with
| true -> begin
(match (ftok) with
| FStar_Pervasives_Native.Some (ftok1) -> begin
(mk_Apply ftok1 vars)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____20102 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply uu____20102 vars))
end)
end
| uu____20103 -> begin
(

let uu____20104 = (

let uu____20111 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (uu____20111)))
in (FStar_SMTEncoding_Util.mkApp uu____20104))
end)
end))
in (

let uu____20120 = ((FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___120_20124 -> (match (uu___120_20124) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| uu____20125 -> begin
false
end)))) || (FStar_All.pipe_right typs1 (FStar_Util.for_some (fun t -> (

let uu____20131 = ((FStar_Syntax_Util.is_pure_or_ghost_function t) || (FStar_TypeChecker_Env.is_reifiable_function env1.tcenv t))
in (FStar_All.pipe_left Prims.op_Negation uu____20131))))))
in (match (uu____20120) with
| true -> begin
((decls1), (env1))
end
| uu____20140 -> begin
(match ((not (is_rec))) with
| true -> begin
(match (((bindings), (typs1), (toks1))) with
| (({FStar_Syntax_Syntax.lbname = uu____20169; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____20171; FStar_Syntax_Syntax.lbeff = uu____20172; FStar_Syntax_Syntax.lbdef = e})::[], (t_norm)::[], ((flid_fv, (f, ftok)))::[]) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____20235 = (

let uu____20242 = (FStar_TypeChecker_Env.open_universes_in env1.tcenv uvs ((e)::(t_norm)::[]))
in (match (uu____20242) with
| (tcenv', uu____20260, e_t) -> begin
(

let uu____20266 = (match (e_t) with
| (e1)::(t_norm1)::[] -> begin
((e1), (t_norm1))
end
| uu____20277 -> begin
(failwith "Impossible")
end)
in (match (uu____20266) with
| (e1, t_norm1) -> begin
(((

let uu___153_20293 = env1
in {bindings = uu___153_20293.bindings; depth = uu___153_20293.depth; tcenv = tcenv'; warn = uu___153_20293.warn; cache = uu___153_20293.cache; nolabels = uu___153_20293.nolabels; use_zfuel_name = uu___153_20293.use_zfuel_name; encode_non_total_function_typ = uu___153_20293.encode_non_total_function_typ; current_module_name = uu___153_20293.current_module_name})), (e1), (t_norm1))
end))
end))
in (match (uu____20235) with
| (env', e1, t_norm1) -> begin
(

let uu____20303 = (destruct_bound_function flid t_norm1 e1)
in (match (uu____20303) with
| ((binders, body, uu____20324, uu____20325), curry) -> begin
((

let uu____20336 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____20336) with
| true -> begin
(

let uu____20337 = (FStar_Syntax_Print.binders_to_string ", " binders)
in (

let uu____20338 = (FStar_Syntax_Print.term_to_string body)
in (FStar_Util.print2 "Encoding let : binders=[%s], body=%s\n" uu____20337 uu____20338)))
end
| uu____20339 -> begin
()
end));
(

let uu____20340 = (encode_binders FStar_Pervasives_Native.None binders env')
in (match (uu____20340) with
| (vars, guards, env'1, binder_decls, uu____20367) -> begin
(

let body1 = (

let uu____20381 = (FStar_TypeChecker_Env.is_reifiable_function env'1.tcenv t_norm1)
in (match (uu____20381) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env'1.tcenv body)
end
| uu____20382 -> begin
body
end))
in (

let app = (mk_app1 curry f ftok vars)
in (

let uu____20384 = (

let uu____20393 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic))
in (match (uu____20393) with
| true -> begin
(

let uu____20404 = (FStar_SMTEncoding_Term.mk_Valid app)
in (

let uu____20405 = (encode_formula body1 env'1)
in ((uu____20404), (uu____20405))))
end
| uu____20414 -> begin
(

let uu____20415 = (encode_term body1 env'1)
in ((app), (uu____20415)))
end))
in (match (uu____20384) with
| (app1, (body2, decls2)) -> begin
(

let eqn = (

let uu____20438 = (

let uu____20445 = (

let uu____20446 = (

let uu____20457 = (FStar_SMTEncoding_Util.mkEq ((app1), (body2)))
in ((((app1)::[])::[]), (vars), (uu____20457)))
in (FStar_SMTEncoding_Util.mkForall uu____20446))
in (

let uu____20468 = (

let uu____20471 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in FStar_Pervasives_Native.Some (uu____20471))
in ((uu____20445), (uu____20468), ((Prims.strcat "equation_" f)))))
in (FStar_SMTEncoding_Util.mkAssume uu____20438))
in (

let uu____20474 = (

let uu____20477 = (

let uu____20480 = (

let uu____20483 = (

let uu____20486 = (primitive_type_axioms env1.tcenv flid f app1)
in (FStar_List.append ((eqn)::[]) uu____20486))
in (FStar_List.append decls2 uu____20483))
in (FStar_List.append binder_decls uu____20480))
in (FStar_List.append decls1 uu____20477))
in ((uu____20474), (env1))))
end))))
end));
)
end))
end)))
end
| uu____20491 -> begin
(failwith "Impossible")
end)
end
| uu____20520 -> begin
(

let fuel = (

let uu____20526 = (varops.fresh "fuel")
in ((uu____20526), (FStar_SMTEncoding_Term.Fuel_sort)))
in (

let fuel_tm = (FStar_SMTEncoding_Util.mkFreeV fuel)
in (

let env0 = env1
in (

let uu____20529 = (FStar_All.pipe_right toks1 (FStar_List.fold_left (fun uu____20617 uu____20618 -> (match (((uu____20617), (uu____20618))) with
| ((gtoks, env2), (flid_fv, (f, ftok))) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let g = (

let uu____20766 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented")
in (varops.new_fvar uu____20766))
in (

let gtok = (

let uu____20768 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented_token")
in (varops.new_fvar uu____20768))
in (

let env3 = (

let uu____20770 = (

let uu____20773 = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::[])))
in (FStar_All.pipe_left (fun _0_44 -> FStar_Pervasives_Native.Some (_0_44)) uu____20773))
in (push_free_var env2 flid gtok uu____20770))
in (((((flid), (f), (ftok), (g), (gtok)))::gtoks), (env3))))))
end)) (([]), (env1))))
in (match (uu____20529) with
| (gtoks, env2) -> begin
(

let gtoks1 = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env01 uu____20929 t_norm uu____20931 -> (match (((uu____20929), (uu____20931))) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = lbn; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____20975; FStar_Syntax_Syntax.lbeff = uu____20976; FStar_Syntax_Syntax.lbdef = e}) -> begin
(

let uu____21004 = (

let uu____21011 = (FStar_TypeChecker_Env.open_universes_in env2.tcenv uvs ((e)::(t_norm)::[]))
in (match (uu____21011) with
| (tcenv', uu____21033, e_t) -> begin
(

let uu____21039 = (match (e_t) with
| (e1)::(t_norm1)::[] -> begin
((e1), (t_norm1))
end
| uu____21050 -> begin
(failwith "Impossible")
end)
in (match (uu____21039) with
| (e1, t_norm1) -> begin
(((

let uu___154_21066 = env2
in {bindings = uu___154_21066.bindings; depth = uu___154_21066.depth; tcenv = tcenv'; warn = uu___154_21066.warn; cache = uu___154_21066.cache; nolabels = uu___154_21066.nolabels; use_zfuel_name = uu___154_21066.use_zfuel_name; encode_non_total_function_typ = uu___154_21066.encode_non_total_function_typ; current_module_name = uu___154_21066.current_module_name})), (e1), (t_norm1))
end))
end))
in (match (uu____21004) with
| (env', e1, t_norm1) -> begin
((

let uu____21081 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env01.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____21081) with
| true -> begin
(

let uu____21082 = (FStar_Syntax_Print.lbname_to_string lbn)
in (

let uu____21083 = (FStar_Syntax_Print.term_to_string t_norm1)
in (

let uu____21084 = (FStar_Syntax_Print.term_to_string e1)
in (FStar_Util.print3 "Encoding let rec %s : %s = %s\n" uu____21082 uu____21083 uu____21084))))
end
| uu____21085 -> begin
()
end));
(

let uu____21086 = (destruct_bound_function flid t_norm1 e1)
in (match (uu____21086) with
| ((binders, body, formals, tres), curry) -> begin
((

let uu____21123 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env01.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____21123) with
| true -> begin
(

let uu____21124 = (FStar_Syntax_Print.binders_to_string ", " binders)
in (

let uu____21125 = (FStar_Syntax_Print.term_to_string body)
in (

let uu____21126 = (FStar_Syntax_Print.binders_to_string ", " formals)
in (

let uu____21127 = (FStar_Syntax_Print.term_to_string tres)
in (FStar_Util.print4 "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n" uu____21124 uu____21125 uu____21126 uu____21127)))))
end
| uu____21128 -> begin
()
end));
(match (curry) with
| true -> begin
(failwith "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type")
end
| uu____21130 -> begin
()
end);
(

let uu____21131 = (encode_binders FStar_Pervasives_Native.None binders env')
in (match (uu____21131) with
| (vars, guards, env'1, binder_decls, uu____21162) -> begin
(

let decl_g = (

let uu____21176 = (

let uu____21187 = (

let uu____21190 = (FStar_List.map FStar_Pervasives_Native.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::uu____21190)
in ((g), (uu____21187), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Fuel-instrumented function name"))))
in FStar_SMTEncoding_Term.DeclFun (uu____21176))
in (

let env02 = (push_zfuel_name env01 flid g)
in (

let decl_g_tok = FStar_SMTEncoding_Term.DeclFun (((gtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Token for fuel-instrumented partial applications"))))
in (

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let app = (

let uu____21215 = (

let uu____21222 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (uu____21222)))
in (FStar_SMTEncoding_Util.mkApp uu____21215))
in (

let gsapp = (

let uu____21232 = (

let uu____21239 = (

let uu____21242 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (uu____21242)::vars_tm)
in ((g), (uu____21239)))
in (FStar_SMTEncoding_Util.mkApp uu____21232))
in (

let gmax = (

let uu____21248 = (

let uu____21255 = (

let uu____21258 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (uu____21258)::vars_tm)
in ((g), (uu____21255)))
in (FStar_SMTEncoding_Util.mkApp uu____21248))
in (

let body1 = (

let uu____21264 = (FStar_TypeChecker_Env.is_reifiable_function env'1.tcenv t_norm1)
in (match (uu____21264) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env'1.tcenv body)
end
| uu____21265 -> begin
body
end))
in (

let uu____21266 = (encode_term body1 env'1)
in (match (uu____21266) with
| (body_tm, decls2) -> begin
(

let eqn_g = (

let uu____21284 = (

let uu____21291 = (

let uu____21292 = (

let uu____21307 = (FStar_SMTEncoding_Util.mkEq ((gsapp), (body_tm)))
in ((((gsapp)::[])::[]), (FStar_Pervasives_Native.Some ((Prims.parse_int "0"))), ((fuel)::vars), (uu____21307)))
in (FStar_SMTEncoding_Util.mkForall' uu____21292))
in (

let uu____21328 = (

let uu____21331 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in FStar_Pervasives_Native.Some (uu____21331))
in ((uu____21291), (uu____21328), ((Prims.strcat "equation_with_fuel_" g)))))
in (FStar_SMTEncoding_Util.mkAssume uu____21284))
in (

let eqn_f = (

let uu____21335 = (

let uu____21342 = (

let uu____21343 = (

let uu____21354 = (FStar_SMTEncoding_Util.mkEq ((app), (gmax)))
in ((((app)::[])::[]), (vars), (uu____21354)))
in (FStar_SMTEncoding_Util.mkForall uu____21343))
in ((uu____21342), (FStar_Pervasives_Native.Some ("Correspondence of recursive function to instrumented version")), ((Prims.strcat "@fuel_correspondence_" g))))
in (FStar_SMTEncoding_Util.mkAssume uu____21335))
in (

let eqn_g' = (

let uu____21368 = (

let uu____21375 = (

let uu____21376 = (

let uu____21387 = (

let uu____21388 = (

let uu____21393 = (

let uu____21394 = (

let uu____21401 = (

let uu____21404 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "0"))
in (uu____21404)::vars_tm)
in ((g), (uu____21401)))
in (FStar_SMTEncoding_Util.mkApp uu____21394))
in ((gsapp), (uu____21393)))
in (FStar_SMTEncoding_Util.mkEq uu____21388))
in ((((gsapp)::[])::[]), ((fuel)::vars), (uu____21387)))
in (FStar_SMTEncoding_Util.mkForall uu____21376))
in ((uu____21375), (FStar_Pervasives_Native.Some ("Fuel irrelevance")), ((Prims.strcat "@fuel_irrelevance_" g))))
in (FStar_SMTEncoding_Util.mkAssume uu____21368))
in (

let uu____21427 = (

let uu____21436 = (encode_binders FStar_Pervasives_Native.None formals env02)
in (match (uu____21436) with
| (vars1, v_guards, env3, binder_decls1, uu____21465) -> begin
(

let vars_tm1 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars1)
in (

let gapp = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::vars_tm1)))
in (

let tok_corr = (

let tok_app = (

let uu____21490 = (FStar_SMTEncoding_Util.mkFreeV ((gtok), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply uu____21490 ((fuel)::vars1)))
in (

let uu____21495 = (

let uu____21502 = (

let uu____21503 = (

let uu____21514 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (gapp)))
in ((((tok_app)::[])::[]), ((fuel)::vars1), (uu____21514)))
in (FStar_SMTEncoding_Util.mkForall uu____21503))
in ((uu____21502), (FStar_Pervasives_Native.Some ("Fuel token correspondence")), ((Prims.strcat "fuel_token_correspondence_" gtok))))
in (FStar_SMTEncoding_Util.mkAssume uu____21495)))
in (

let uu____21535 = (

let uu____21542 = (encode_term_pred FStar_Pervasives_Native.None tres env3 gapp)
in (match (uu____21542) with
| (g_typing, d3) -> begin
(

let uu____21555 = (

let uu____21558 = (

let uu____21559 = (

let uu____21566 = (

let uu____21567 = (

let uu____21578 = (

let uu____21579 = (

let uu____21584 = (FStar_SMTEncoding_Util.mk_and_l v_guards)
in ((uu____21584), (g_typing)))
in (FStar_SMTEncoding_Util.mkImp uu____21579))
in ((((gapp)::[])::[]), ((fuel)::vars1), (uu____21578)))
in (FStar_SMTEncoding_Util.mkForall uu____21567))
in ((uu____21566), (FStar_Pervasives_Native.Some ("Typing correspondence of token to term")), ((Prims.strcat "token_correspondence_" g))))
in (FStar_SMTEncoding_Util.mkAssume uu____21559))
in (uu____21558)::[])
in ((d3), (uu____21555)))
end))
in (match (uu____21535) with
| (aux_decls, typing_corr) -> begin
(((FStar_List.append binder_decls1 aux_decls)), ((FStar_List.append typing_corr ((tok_corr)::[]))))
end)))))
end))
in (match (uu____21427) with
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

let uu____21649 = (

let uu____21662 = (FStar_List.zip3 gtoks1 typs1 bindings)
in (FStar_List.fold_left (fun uu____21741 uu____21742 -> (match (((uu____21741), (uu____21742))) with
| ((decls2, eqns, env01), (gtok, ty, lb)) -> begin
(

let uu____21897 = (encode_one_binding env01 gtok ty lb)
in (match (uu____21897) with
| (decls', eqns', env02) -> begin
(((decls')::decls2), ((FStar_List.append eqns' eqns)), (env02))
end))
end)) (((decls1)::[]), ([]), (env0)) uu____21662))
in (match (uu____21649) with
| (decls2, eqns, env01) -> begin
(

let uu____21970 = (

let isDeclFun = (fun uu___121_21982 -> (match (uu___121_21982) with
| FStar_SMTEncoding_Term.DeclFun (uu____21983) -> begin
true
end
| uu____21994 -> begin
false
end))
in (

let uu____21995 = (FStar_All.pipe_right decls2 FStar_List.flatten)
in (FStar_All.pipe_right uu____21995 (FStar_List.partition isDeclFun))))
in (match (uu____21970) with
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

let uu____22046 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right uu____22046 (FStar_String.concat " and ")))
in (

let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in (((decl)::[]), (env))))
end))
end))


let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let nm = (

let uu____22095 = (FStar_Syntax_Util.lid_of_sigelt se)
in (match (uu____22095) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (l) -> begin
l.FStar_Ident.str
end))
in (

let uu____22099 = (encode_sigelt' env se)
in (match (uu____22099) with
| (g, env1) -> begin
(

let g1 = (match (g) with
| [] -> begin
(

let uu____22115 = (

let uu____22116 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (uu____22116))
in (uu____22115)::[])
end
| uu____22117 -> begin
(

let uu____22118 = (

let uu____22121 = (

let uu____22122 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____22122))
in (uu____22121)::g)
in (

let uu____22123 = (

let uu____22126 = (

let uu____22127 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____22127))
in (uu____22126)::[])
in (FStar_List.append uu____22118 uu____22123)))
end)
in ((g1), (env1)))
end))))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let is_opaque_to_smt = (fun t -> (

let uu____22140 = (

let uu____22141 = (FStar_Syntax_Subst.compress t)
in uu____22141.FStar_Syntax_Syntax.n)
in (match (uu____22140) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____22145)) -> begin
(s = "opaque_to_smt")
end
| uu____22146 -> begin
false
end)))
in (

let is_uninterpreted_by_smt = (fun t -> (

let uu____22151 = (

let uu____22152 = (FStar_Syntax_Subst.compress t)
in uu____22152.FStar_Syntax_Syntax.n)
in (match (uu____22151) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____22156)) -> begin
(s = "uninterpreted_by_smt")
end
| uu____22157 -> begin
false
end)))
in (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____22162) -> begin
(failwith "impossible -- removed by tc.fs")
end
| FStar_Syntax_Syntax.Sig_pragma (uu____22167) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_main (uu____22170) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____22173) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____22188) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(

let uu____22192 = (

let uu____22193 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right uu____22193 Prims.op_Negation))
in (match (uu____22192) with
| true -> begin
(([]), (env))
end
| uu____22202 -> begin
(

let close_effect_params = (fun tm -> (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
tm
end
| uu____22219 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((ed.FStar_Syntax_Syntax.binders), (tm), (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[]))))))) FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)
end))
in (

let encode_action = (fun env1 a -> (

let uu____22239 = (new_term_constant_and_tok_from_lid env1 a.FStar_Syntax_Syntax.action_name)
in (match (uu____22239) with
| (aname, atok, env2) -> begin
(

let uu____22255 = (FStar_Syntax_Util.arrow_formals_comp a.FStar_Syntax_Syntax.action_typ)
in (match (uu____22255) with
| (formals, uu____22273) -> begin
(

let uu____22286 = (

let uu____22291 = (close_effect_params a.FStar_Syntax_Syntax.action_defn)
in (encode_term uu____22291 env2))
in (match (uu____22286) with
| (tm, decls) -> begin
(

let a_decls = (

let uu____22303 = (

let uu____22304 = (

let uu____22315 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____22331 -> FStar_SMTEncoding_Term.Term_sort)))
in ((aname), (uu____22315), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Action"))))
in FStar_SMTEncoding_Term.DeclFun (uu____22304))
in (uu____22303)::(FStar_SMTEncoding_Term.DeclFun (((atok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Action token")))))::[])
in (

let uu____22344 = (

let aux = (fun uu____22396 uu____22397 -> (match (((uu____22396), (uu____22397))) with
| ((bv, uu____22449), (env3, acc_sorts, acc)) -> begin
(

let uu____22487 = (gen_term_var env3 bv)
in (match (uu____22487) with
| (xxsym, xx, env4) -> begin
((env4), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::acc_sorts), ((xx)::acc))
end))
end))
in (FStar_List.fold_right aux formals ((env2), ([]), ([]))))
in (match (uu____22344) with
| (uu____22559, xs_sorts, xs) -> begin
(

let app = (FStar_SMTEncoding_Util.mkApp ((aname), (xs)))
in (

let a_eq = (

let uu____22582 = (

let uu____22589 = (

let uu____22590 = (

let uu____22601 = (

let uu____22602 = (

let uu____22607 = (mk_Apply tm xs_sorts)
in ((app), (uu____22607)))
in (FStar_SMTEncoding_Util.mkEq uu____22602))
in ((((app)::[])::[]), (xs_sorts), (uu____22601)))
in (FStar_SMTEncoding_Util.mkForall uu____22590))
in ((uu____22589), (FStar_Pervasives_Native.Some ("Action equality")), ((Prims.strcat aname "_equality"))))
in (FStar_SMTEncoding_Util.mkAssume uu____22582))
in (

let tok_correspondence = (

let tok_term = (FStar_SMTEncoding_Util.mkFreeV ((atok), (FStar_SMTEncoding_Term.Term_sort)))
in (

let tok_app = (mk_Apply tok_term xs_sorts)
in (

let uu____22627 = (

let uu____22634 = (

let uu____22635 = (

let uu____22646 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (app)))
in ((((tok_app)::[])::[]), (xs_sorts), (uu____22646)))
in (FStar_SMTEncoding_Util.mkForall uu____22635))
in ((uu____22634), (FStar_Pervasives_Native.Some ("Action token correspondence")), ((Prims.strcat aname "_token_correspondence"))))
in (FStar_SMTEncoding_Util.mkAssume uu____22627))))
in ((env2), ((FStar_List.append decls (FStar_List.append a_decls ((a_eq)::(tok_correspondence)::[]))))))))
end)))
end))
end))
end)))
in (

let uu____22665 = (FStar_Util.fold_map encode_action env ed.FStar_Syntax_Syntax.actions)
in (match (uu____22665) with
| (env1, decls2) -> begin
(((FStar_List.flatten decls2)), (env1))
end))))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____22693, uu____22694) when (FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid) -> begin
(

let uu____22695 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____22695) with
| (tname, ttok, env1) -> begin
(([]), (env1))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____22712, t) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let will_encode_definition = (

let uu____22718 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___122_22722 -> (match (uu___122_22722) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.Projector (uu____22723) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____22728) -> begin
true
end
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| uu____22729 -> begin
false
end))))
in (not (uu____22718)))
in (match (will_encode_definition) with
| true -> begin
(([]), (env))
end
| uu____22736 -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____22738 = (

let uu____22745 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs (FStar_Util.for_some is_uninterpreted_by_smt))
in (encode_top_level_val uu____22745 env fv t quals))
in (match (uu____22738) with
| (decls, env1) -> begin
(

let tname = lid.FStar_Ident.str
in (

let tsym = (FStar_SMTEncoding_Util.mkFreeV ((tname), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____22760 = (

let uu____22763 = (primitive_type_axioms env1.tcenv lid tname tsym)
in (FStar_List.append decls uu____22763))
in ((uu____22760), (env1)))))
end)))
end)))
end
| FStar_Syntax_Syntax.Sig_assume (l, us, f) -> begin
(

let uu____22771 = (FStar_Syntax_Subst.open_univ_vars us f)
in (match (uu____22771) with
| (uu____22780, f1) -> begin
(

let uu____22782 = (encode_formula f1 env)
in (match (uu____22782) with
| (f2, decls) -> begin
(

let g = (

let uu____22796 = (

let uu____22797 = (

let uu____22804 = (

let uu____22807 = (

let uu____22808 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" uu____22808))
in FStar_Pervasives_Native.Some (uu____22807))
in (

let uu____22809 = (varops.mk_unique (Prims.strcat "assumption_" l.FStar_Ident.str))
in ((f2), (uu____22804), (uu____22809))))
in (FStar_SMTEncoding_Util.mkAssume uu____22797))
in (uu____22796)::[])
in (((FStar_List.append decls g)), (env)))
end))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____22815) when ((FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) || (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs (FStar_Util.for_some is_opaque_to_smt))) -> begin
(

let attrs = se.FStar_Syntax_Syntax.sigattrs
in (

let uu____22827 = (FStar_Util.fold_map (fun env1 lb -> (

let lid = (

let uu____22845 = (

let uu____22848 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____22848.FStar_Syntax_Syntax.fv_name)
in uu____22845.FStar_Syntax_Syntax.v)
in (

let uu____22849 = (

let uu____22850 = (FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone uu____22850))
in (match (uu____22849) with
| true -> begin
(

let val_decl = (

let uu___155_22878 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = uu___155_22878.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Irreducible)::se.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___155_22878.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___155_22878.FStar_Syntax_Syntax.sigattrs})
in (

let uu____22883 = (encode_sigelt' env1 val_decl)
in (match (uu____22883) with
| (decls, env2) -> begin
((env2), (decls))
end)))
end
| uu____22894 -> begin
((env1), ([]))
end)))) env (FStar_Pervasives_Native.snd lbs))
in (match (uu____22827) with
| (env1, decls) -> begin
(((FStar_List.flatten decls)), (env1))
end)))
end
| FStar_Syntax_Syntax.Sig_let ((uu____22911, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t1); FStar_Syntax_Syntax.lbunivs = uu____22913; FStar_Syntax_Syntax.lbtyp = uu____22914; FStar_Syntax_Syntax.lbeff = uu____22915; FStar_Syntax_Syntax.lbdef = uu____22916})::[]), uu____22917) when (FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid) -> begin
(

let uu____22936 = (new_term_constant_and_tok_from_lid env b2t1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____22936) with
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

let uu____22965 = (

let uu____22968 = (

let uu____22969 = (

let uu____22976 = (

let uu____22977 = (

let uu____22988 = (

let uu____22989 = (

let uu____22994 = (FStar_SMTEncoding_Util.mkApp (((FStar_Pervasives_Native.snd FStar_SMTEncoding_Term.boxBoolFun)), ((x)::[])))
in ((valid_b2t_x), (uu____22994)))
in (FStar_SMTEncoding_Util.mkEq uu____22989))
in ((((b2t_x)::[])::[]), ((xx)::[]), (uu____22988)))
in (FStar_SMTEncoding_Util.mkForall uu____22977))
in ((uu____22976), (FStar_Pervasives_Native.Some ("b2t def")), ("b2t_def")))
in (FStar_SMTEncoding_Util.mkAssume uu____22969))
in (uu____22968)::[])
in (FStar_SMTEncoding_Term.DeclFun (((tname), ((FStar_SMTEncoding_Term.Term_sort)::[]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None))))::uu____22965)
in ((decls), (env1)))))))
end))
end
| FStar_Syntax_Syntax.Sig_let (uu____23027, uu____23028) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___123_23037 -> (match (uu___123_23037) with
| FStar_Syntax_Syntax.Discriminator (uu____23038) -> begin
true
end
| uu____23039 -> begin
false
end)))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let (uu____23042, lids) when ((FStar_All.pipe_right lids (FStar_Util.for_some (fun l -> (

let uu____23053 = (

let uu____23054 = (FStar_List.hd l.FStar_Ident.ns)
in uu____23054.FStar_Ident.idText)
in (uu____23053 = "Prims"))))) && (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___124_23058 -> (match (uu___124_23058) with
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
true
end
| uu____23059 -> begin
false
end))))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____23063) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___125_23080 -> (match (uu___125_23080) with
| FStar_Syntax_Syntax.Projector (uu____23081) -> begin
true
end
| uu____23086 -> begin
false
end)))) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____23089 = (try_lookup_free_var env l)
in (match (uu____23089) with
| FStar_Pervasives_Native.Some (uu____23096) -> begin
(([]), (env))
end
| FStar_Pervasives_Native.None -> begin
(

let se1 = (

let uu___156_23100 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l); FStar_Syntax_Syntax.sigquals = uu___156_23100.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___156_23100.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___156_23100.FStar_Syntax_Syntax.sigattrs})
in (encode_sigelt env se1))
end))))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), uu____23107) -> begin
(encode_top_level_let env ((is_rec), (bindings)) se.FStar_Syntax_Syntax.sigquals)
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____23125) -> begin
(

let uu____23134 = (encode_sigelts env ses)
in (match (uu____23134) with
| (g, env1) -> begin
(

let uu____23151 = (FStar_All.pipe_right g (FStar_List.partition (fun uu___126_23174 -> (match (uu___126_23174) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.assumption_term = uu____23175; FStar_SMTEncoding_Term.assumption_caption = FStar_Pervasives_Native.Some ("inversion axiom"); FStar_SMTEncoding_Term.assumption_name = uu____23176; FStar_SMTEncoding_Term.assumption_fact_ids = uu____23177}) -> begin
false
end
| uu____23180 -> begin
true
end))))
in (match (uu____23151) with
| (g', inversions) -> begin
(

let uu____23195 = (FStar_All.pipe_right g' (FStar_List.partition (fun uu___127_23216 -> (match (uu___127_23216) with
| FStar_SMTEncoding_Term.DeclFun (uu____23217) -> begin
true
end
| uu____23228 -> begin
false
end))))
in (match (uu____23195) with
| (decls, rest) -> begin
(((FStar_List.append decls (FStar_List.append rest inversions))), (env1))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, uu____23246, tps, k, uu____23249, datas) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___128_23266 -> (match (uu___128_23266) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____23267 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> (match (is_logical) with
| true -> begin
(

let uu____23276 = c
in (match (uu____23276) with
| (name, args, uu____23281, uu____23282, uu____23283) -> begin
(

let uu____23288 = (

let uu____23289 = (

let uu____23300 = (FStar_All.pipe_right args (FStar_List.map (fun uu____23317 -> (match (uu____23317) with
| (uu____23324, sort, uu____23326) -> begin
sort
end))))
in ((name), (uu____23300), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____23289))
in (uu____23288)::[])
end))
end
| uu____23331 -> begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end))
in (

let inversion_axioms = (fun tapp vars -> (

let uu____23353 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (

let uu____23359 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right uu____23359 FStar_Option.isNone)))))
in (match (uu____23353) with
| true -> begin
[]
end
| uu____23390 -> begin
(

let uu____23391 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____23391) with
| (xxsym, xx) -> begin
(

let uu____23400 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun uu____23439 l -> (match (uu____23439) with
| (out, decls) -> begin
(

let uu____23459 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (uu____23459) with
| (uu____23470, data_t) -> begin
(

let uu____23472 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (uu____23472) with
| (args, res) -> begin
(

let indices = (

let uu____23518 = (

let uu____23519 = (FStar_Syntax_Subst.compress res)
in uu____23519.FStar_Syntax_Syntax.n)
in (match (uu____23518) with
| FStar_Syntax_Syntax.Tm_app (uu____23530, indices) -> begin
indices
end
| uu____23552 -> begin
[]
end))
in (

let env1 = (FStar_All.pipe_right args (FStar_List.fold_left (fun env1 uu____23576 -> (match (uu____23576) with
| (x, uu____23582) -> begin
(

let uu____23583 = (

let uu____23584 = (

let uu____23591 = (mk_term_projector_name l x)
in ((uu____23591), ((xx)::[])))
in (FStar_SMTEncoding_Util.mkApp uu____23584))
in (push_term_var env1 x uu____23583))
end)) env))
in (

let uu____23594 = (encode_args indices env1)
in (match (uu____23594) with
| (indices1, decls') -> begin
((match (((FStar_List.length indices1) <> (FStar_List.length vars))) with
| true -> begin
(failwith "Impossible")
end
| uu____23618 -> begin
()
end);
(

let eqs = (

let uu____23620 = (FStar_List.map2 (fun v1 a -> (

let uu____23636 = (

let uu____23641 = (FStar_SMTEncoding_Util.mkFreeV v1)
in ((uu____23641), (a)))
in (FStar_SMTEncoding_Util.mkEq uu____23636))) vars indices1)
in (FStar_All.pipe_right uu____23620 FStar_SMTEncoding_Util.mk_and_l))
in (

let uu____23644 = (

let uu____23645 = (

let uu____23650 = (

let uu____23651 = (

let uu____23656 = (mk_data_tester env1 l xx)
in ((uu____23656), (eqs)))
in (FStar_SMTEncoding_Util.mkAnd uu____23651))
in ((out), (uu____23650)))
in (FStar_SMTEncoding_Util.mkOr uu____23645))
in ((uu____23644), ((FStar_List.append decls decls')))));
)
end))))
end))
end))
end)) ((FStar_SMTEncoding_Util.mkFalse), ([]))))
in (match (uu____23400) with
| (data_ax, decls) -> begin
(

let uu____23669 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____23669) with
| (ffsym, ff) -> begin
(

let fuel_guarded_inversion = (

let xx_has_type_sfuel = (match (((FStar_List.length datas) > (Prims.parse_int "1"))) with
| true -> begin
(

let uu____23680 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((ff)::[])))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel uu____23680 xx tapp))
end
| uu____23683 -> begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end)
in (

let uu____23684 = (

let uu____23691 = (

let uu____23692 = (

let uu____23703 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (

let uu____23718 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_sfuel), (data_ax)))
in ((((xx_has_type_sfuel)::[])::[]), (uu____23703), (uu____23718))))
in (FStar_SMTEncoding_Util.mkForall uu____23692))
in (

let uu____23733 = (varops.mk_unique (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str))
in ((uu____23691), (FStar_Pervasives_Native.Some ("inversion axiom")), (uu____23733))))
in (FStar_SMTEncoding_Util.mkAssume uu____23684)))
in (FStar_List.append decls ((fuel_guarded_inversion)::[])))
end))
end))
end))
end)))
in (

let uu____23736 = (

let uu____23749 = (

let uu____23750 = (FStar_Syntax_Subst.compress k)
in uu____23750.FStar_Syntax_Syntax.n)
in (match (uu____23749) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
(((FStar_List.append tps formals)), ((FStar_Syntax_Util.comp_result kres)))
end
| uu____23795 -> begin
((tps), (k))
end))
in (match (uu____23736) with
| (formals, res) -> begin
(

let uu____23818 = (FStar_Syntax_Subst.open_term formals res)
in (match (uu____23818) with
| (formals1, res1) -> begin
(

let uu____23829 = (encode_binders FStar_Pervasives_Native.None formals1 env)
in (match (uu____23829) with
| (vars, guards, env', binder_decls, uu____23854) -> begin
(

let uu____23867 = (new_term_constant_and_tok_from_lid env t)
in (match (uu____23867) with
| (tname, ttok, env1) -> begin
(

let ttok_tm = (FStar_SMTEncoding_Util.mkApp ((ttok), ([])))
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let tapp = (

let uu____23886 = (

let uu____23893 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((tname), (uu____23893)))
in (FStar_SMTEncoding_Util.mkApp uu____23886))
in (

let uu____23902 = (

let tname_decl = (

let uu____23912 = (

let uu____23913 = (FStar_All.pipe_right vars (FStar_List.map (fun uu____23945 -> (match (uu____23945) with
| (n1, s) -> begin
(((Prims.strcat tname n1)), (s), (false))
end))))
in (

let uu____23958 = (varops.next_id ())
in ((tname), (uu____23913), (FStar_SMTEncoding_Term.Term_sort), (uu____23958), (false))))
in (constructor_or_logic_type_decl uu____23912))
in (

let uu____23967 = (match (vars) with
| [] -> begin
(

let uu____23980 = (

let uu____23981 = (

let uu____23984 = (FStar_SMTEncoding_Util.mkApp ((tname), ([])))
in (FStar_All.pipe_left (fun _0_45 -> FStar_Pervasives_Native.Some (_0_45)) uu____23984))
in (push_free_var env1 t tname uu____23981))
in (([]), (uu____23980)))
end
| uu____23991 -> begin
(

let ttok_decl = FStar_SMTEncoding_Term.DeclFun (((ttok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("token"))))
in (

let ttok_fresh = (

let uu____24000 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ttok), (FStar_SMTEncoding_Term.Term_sort)) uu____24000))
in (

let ttok_app = (mk_Apply ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (

let uu____24014 = (

let uu____24021 = (

let uu____24022 = (

let uu____24037 = (FStar_SMTEncoding_Util.mkEq ((ttok_app), (tapp)))
in ((pats), (FStar_Pervasives_Native.None), (vars), (uu____24037)))
in (FStar_SMTEncoding_Util.mkForall' uu____24022))
in ((uu____24021), (FStar_Pervasives_Native.Some ("name-token correspondence")), ((Prims.strcat "token_correspondence_" ttok))))
in (FStar_SMTEncoding_Util.mkAssume uu____24014))
in (((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[]), (env1)))))))
end)
in (match (uu____23967) with
| (tok_decls, env2) -> begin
(((FStar_List.append tname_decl tok_decls)), (env2))
end)))
in (match (uu____23902) with
| (decls, env2) -> begin
(

let kindingAx = (

let uu____24077 = (encode_term_pred FStar_Pervasives_Native.None res1 env' tapp)
in (match (uu____24077) with
| (k1, decls1) -> begin
(

let karr = (match (((FStar_List.length formals1) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____24095 = (

let uu____24096 = (

let uu____24103 = (

let uu____24104 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____24104))
in ((uu____24103), (FStar_Pervasives_Native.Some ("kinding")), ((Prims.strcat "pre_kinding_" ttok))))
in (FStar_SMTEncoding_Util.mkAssume uu____24096))
in (uu____24095)::[])
end
| uu____24107 -> begin
[]
end)
in (

let uu____24108 = (

let uu____24111 = (

let uu____24114 = (

let uu____24115 = (

let uu____24122 = (

let uu____24123 = (

let uu____24134 = (FStar_SMTEncoding_Util.mkImp ((guard), (k1)))
in ((((tapp)::[])::[]), (vars), (uu____24134)))
in (FStar_SMTEncoding_Util.mkForall uu____24123))
in ((uu____24122), (FStar_Pervasives_Native.None), ((Prims.strcat "kinding_" ttok))))
in (FStar_SMTEncoding_Util.mkAssume uu____24115))
in (uu____24114)::[])
in (FStar_List.append karr uu____24111))
in (FStar_List.append decls1 uu____24108)))
end))
in (

let aux = (

let uu____24150 = (

let uu____24153 = (inversion_axioms tapp vars)
in (

let uu____24156 = (

let uu____24159 = (pretype_axiom env2 tapp vars)
in (uu____24159)::[])
in (FStar_List.append uu____24153 uu____24156)))
in (FStar_List.append kindingAx uu____24150))
in (

let g = (FStar_List.append decls (FStar_List.append binder_decls aux))
in ((g), (env2)))))
end)))))
end))
end))
end))
end))))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____24166, uu____24167, uu____24168, uu____24169, uu____24170) when (FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____24178, t, uu____24180, n_tps, uu____24182) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____24190 = (new_term_constant_and_tok_from_lid env d)
in (match (uu____24190) with
| (ddconstrsym, ddtok, env1) -> begin
(

let ddtok_tm = (FStar_SMTEncoding_Util.mkApp ((ddtok), ([])))
in (

let uu____24207 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____24207) with
| (formals, t_res) -> begin
(

let uu____24242 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____24242) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (

let uu____24256 = (encode_binders (FStar_Pervasives_Native.Some (fuel_tm)) formals env1)
in (match (uu____24256) with
| (vars, guards, env', binder_decls, names1) -> begin
(

let fields = (FStar_All.pipe_right names1 (FStar_List.mapi (fun n1 x -> (

let projectible = true
in (

let uu____24326 = (mk_term_projector_name d x)
in ((uu____24326), (FStar_SMTEncoding_Term.Term_sort), (projectible)))))))
in (

let datacons = (

let uu____24328 = (

let uu____24347 = (varops.next_id ())
in ((ddconstrsym), (fields), (FStar_SMTEncoding_Term.Term_sort), (uu____24347), (true)))
in (FStar_All.pipe_right uu____24328 FStar_SMTEncoding_Term.constructor_to_decl))
in (

let app = (mk_Apply ddtok_tm vars)
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (

let uu____24386 = (encode_term_pred FStar_Pervasives_Native.None t env1 ddtok_tm)
in (match (uu____24386) with
| (tok_typing, decls3) -> begin
(

let tok_typing1 = (match (fields) with
| (uu____24398)::uu____24399 -> begin
(

let ff = (("ty"), (FStar_SMTEncoding_Term.Term_sort))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV ff)
in (

let vtok_app_l = (mk_Apply ddtok_tm ((ff)::[]))
in (

let vtok_app_r = (mk_Apply f ((((ddtok), (FStar_SMTEncoding_Term.Term_sort)))::[]))
in (

let uu____24444 = (

let uu____24455 = (FStar_SMTEncoding_Term.mk_NoHoist f tok_typing)
in ((((vtok_app_l)::[])::((vtok_app_r)::[])::[]), ((ff)::[]), (uu____24455)))
in (FStar_SMTEncoding_Util.mkForall uu____24444))))))
end
| uu____24480 -> begin
tok_typing
end)
in (

let uu____24489 = (encode_binders (FStar_Pervasives_Native.Some (fuel_tm)) formals env1)
in (match (uu____24489) with
| (vars', guards', env'', decls_formals, uu____24514) -> begin
(

let uu____24527 = (

let xvars1 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars')
in (

let dapp1 = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars1)))
in (encode_term_pred (FStar_Pervasives_Native.Some (fuel_tm)) t_res env'' dapp1)))
in (match (uu____24527) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_SMTEncoding_Util.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| uu____24558 -> begin
(

let uu____24565 = (

let uu____24566 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ddtok), (FStar_SMTEncoding_Term.Term_sort)) uu____24566))
in (uu____24565)::[])
end)
in (

let encode_elim = (fun uu____24576 -> (

let uu____24577 = (FStar_Syntax_Util.head_and_args t_res)
in (match (uu____24577) with
| (head1, args) -> begin
(

let uu____24620 = (

let uu____24621 = (FStar_Syntax_Subst.compress head1)
in uu____24621.FStar_Syntax_Syntax.n)
in (match (uu____24620) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____24631; FStar_Syntax_Syntax.vars = uu____24632}, uu____24633) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let uu____24639 = (encode_args args env')
in (match (uu____24639) with
| (encoded_args, arg_decls) -> begin
(

let guards_for_parameter = (fun orig_arg arg xv -> (

let fv1 = (match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv1) -> begin
fv1
end
| uu____24682 -> begin
(

let uu____24683 = (

let uu____24684 = (

let uu____24689 = (

let uu____24690 = (FStar_Syntax_Print.term_to_string orig_arg)
in (FStar_Util.format1 "Inductive type parameter %s must be a variable ; You may want to change it to an index." uu____24690))
in ((uu____24689), (orig_arg.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____24684))
in (FStar_Exn.raise uu____24683))
end)
in (

let guards1 = (FStar_All.pipe_right guards (FStar_List.collect (fun g -> (

let uu____24706 = (

let uu____24707 = (FStar_SMTEncoding_Term.free_variables g)
in (FStar_List.contains fv1 uu____24707))
in (match (uu____24706) with
| true -> begin
(

let uu____24720 = (FStar_SMTEncoding_Term.subst g fv1 xv)
in (uu____24720)::[])
end
| uu____24721 -> begin
[]
end)))))
in (FStar_SMTEncoding_Util.mk_and_l guards1))))
in (

let uu____24722 = (

let uu____24735 = (FStar_List.zip args encoded_args)
in (FStar_List.fold_left (fun uu____24785 uu____24786 -> (match (((uu____24785), (uu____24786))) with
| ((env2, arg_vars, eqns_or_guards, i), (orig_arg, arg)) -> begin
(

let uu____24881 = (

let uu____24888 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (gen_term_var env2 uu____24888))
in (match (uu____24881) with
| (uu____24901, xv, env3) -> begin
(

let eqns = (match ((i < n_tps)) with
| true -> begin
(

let uu____24909 = (guards_for_parameter (FStar_Pervasives_Native.fst orig_arg) arg xv)
in (uu____24909)::eqns_or_guards)
end
| uu____24910 -> begin
(

let uu____24911 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (uu____24911)::eqns_or_guards)
end)
in ((env3), ((xv)::arg_vars), (eqns), ((i + (Prims.parse_int "1")))))
end))
end)) ((env'), ([]), ([]), ((Prims.parse_int "0"))) uu____24735))
in (match (uu____24722) with
| (uu____24926, arg_vars, elim_eqns_or_guards, uu____24929) -> begin
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

let uu____24959 = (

let uu____24966 = (

let uu____24967 = (

let uu____24978 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____24989 = (

let uu____24990 = (

let uu____24995 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append elim_eqns_or_guards guards))
in ((ty_pred), (uu____24995)))
in (FStar_SMTEncoding_Util.mkImp uu____24990))
in ((((ty_pred)::[])::[]), (uu____24978), (uu____24989))))
in (FStar_SMTEncoding_Util.mkForall uu____24967))
in ((uu____24966), (FStar_Pervasives_Native.Some ("data constructor typing elim")), ((Prims.strcat "data_elim_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____24959))
in (

let subterm_ordering = (match ((FStar_Ident.lid_equals d FStar_Parser_Const.lextop_lid)) with
| true -> begin
(

let x = (

let uu____25018 = (varops.fresh "x")
in ((uu____25018), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (

let uu____25020 = (

let uu____25027 = (

let uu____25028 = (

let uu____25039 = (

let uu____25044 = (

let uu____25047 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in (uu____25047)::[])
in (uu____25044)::[])
in (

let uu____25052 = (

let uu____25053 = (

let uu____25058 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (

let uu____25059 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in ((uu____25058), (uu____25059))))
in (FStar_SMTEncoding_Util.mkImp uu____25053))
in ((uu____25039), ((x)::[]), (uu____25052))))
in (FStar_SMTEncoding_Util.mkForall uu____25028))
in (

let uu____25078 = (varops.mk_unique "lextop")
in ((uu____25027), (FStar_Pervasives_Native.Some ("lextop is top")), (uu____25078))))
in (FStar_SMTEncoding_Util.mkAssume uu____25020))))
end
| uu____25081 -> begin
(

let prec = (

let uu____25085 = (FStar_All.pipe_right vars (FStar_List.mapi (fun i v1 -> (match ((i < n_tps)) with
| true -> begin
[]
end
| uu____25112 -> begin
(

let uu____25113 = (

let uu____25114 = (FStar_SMTEncoding_Util.mkFreeV v1)
in (FStar_SMTEncoding_Util.mk_Precedes uu____25114 dapp1))
in (uu____25113)::[])
end))))
in (FStar_All.pipe_right uu____25085 FStar_List.flatten))
in (

let uu____25121 = (

let uu____25128 = (

let uu____25129 = (

let uu____25140 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____25151 = (

let uu____25152 = (

let uu____25157 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (uu____25157)))
in (FStar_SMTEncoding_Util.mkImp uu____25152))
in ((((ty_pred)::[])::[]), (uu____25140), (uu____25151))))
in (FStar_SMTEncoding_Util.mkForall uu____25129))
in ((uu____25128), (FStar_Pervasives_Native.Some ("subterm ordering")), ((Prims.strcat "subterm_ordering_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____25121)))
end)
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end)))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let uu____25178 = (encode_args args env')
in (match (uu____25178) with
| (encoded_args, arg_decls) -> begin
(

let guards_for_parameter = (fun orig_arg arg xv -> (

let fv1 = (match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv1) -> begin
fv1
end
| uu____25221 -> begin
(

let uu____25222 = (

let uu____25223 = (

let uu____25228 = (

let uu____25229 = (FStar_Syntax_Print.term_to_string orig_arg)
in (FStar_Util.format1 "Inductive type parameter %s must be a variable ; You may want to change it to an index." uu____25229))
in ((uu____25228), (orig_arg.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____25223))
in (FStar_Exn.raise uu____25222))
end)
in (

let guards1 = (FStar_All.pipe_right guards (FStar_List.collect (fun g -> (

let uu____25245 = (

let uu____25246 = (FStar_SMTEncoding_Term.free_variables g)
in (FStar_List.contains fv1 uu____25246))
in (match (uu____25245) with
| true -> begin
(

let uu____25259 = (FStar_SMTEncoding_Term.subst g fv1 xv)
in (uu____25259)::[])
end
| uu____25260 -> begin
[]
end)))))
in (FStar_SMTEncoding_Util.mk_and_l guards1))))
in (

let uu____25261 = (

let uu____25274 = (FStar_List.zip args encoded_args)
in (FStar_List.fold_left (fun uu____25324 uu____25325 -> (match (((uu____25324), (uu____25325))) with
| ((env2, arg_vars, eqns_or_guards, i), (orig_arg, arg)) -> begin
(

let uu____25420 = (

let uu____25427 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (gen_term_var env2 uu____25427))
in (match (uu____25420) with
| (uu____25440, xv, env3) -> begin
(

let eqns = (match ((i < n_tps)) with
| true -> begin
(

let uu____25448 = (guards_for_parameter (FStar_Pervasives_Native.fst orig_arg) arg xv)
in (uu____25448)::eqns_or_guards)
end
| uu____25449 -> begin
(

let uu____25450 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (uu____25450)::eqns_or_guards)
end)
in ((env3), ((xv)::arg_vars), (eqns), ((i + (Prims.parse_int "1")))))
end))
end)) ((env'), ([]), ([]), ((Prims.parse_int "0"))) uu____25274))
in (match (uu____25261) with
| (uu____25465, arg_vars, elim_eqns_or_guards, uu____25468) -> begin
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

let uu____25498 = (

let uu____25505 = (

let uu____25506 = (

let uu____25517 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____25528 = (

let uu____25529 = (

let uu____25534 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append elim_eqns_or_guards guards))
in ((ty_pred), (uu____25534)))
in (FStar_SMTEncoding_Util.mkImp uu____25529))
in ((((ty_pred)::[])::[]), (uu____25517), (uu____25528))))
in (FStar_SMTEncoding_Util.mkForall uu____25506))
in ((uu____25505), (FStar_Pervasives_Native.Some ("data constructor typing elim")), ((Prims.strcat "data_elim_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____25498))
in (

let subterm_ordering = (match ((FStar_Ident.lid_equals d FStar_Parser_Const.lextop_lid)) with
| true -> begin
(

let x = (

let uu____25557 = (varops.fresh "x")
in ((uu____25557), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (

let uu____25559 = (

let uu____25566 = (

let uu____25567 = (

let uu____25578 = (

let uu____25583 = (

let uu____25586 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in (uu____25586)::[])
in (uu____25583)::[])
in (

let uu____25591 = (

let uu____25592 = (

let uu____25597 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (

let uu____25598 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in ((uu____25597), (uu____25598))))
in (FStar_SMTEncoding_Util.mkImp uu____25592))
in ((uu____25578), ((x)::[]), (uu____25591))))
in (FStar_SMTEncoding_Util.mkForall uu____25567))
in (

let uu____25617 = (varops.mk_unique "lextop")
in ((uu____25566), (FStar_Pervasives_Native.Some ("lextop is top")), (uu____25617))))
in (FStar_SMTEncoding_Util.mkAssume uu____25559))))
end
| uu____25620 -> begin
(

let prec = (

let uu____25624 = (FStar_All.pipe_right vars (FStar_List.mapi (fun i v1 -> (match ((i < n_tps)) with
| true -> begin
[]
end
| uu____25651 -> begin
(

let uu____25652 = (

let uu____25653 = (FStar_SMTEncoding_Util.mkFreeV v1)
in (FStar_SMTEncoding_Util.mk_Precedes uu____25653 dapp1))
in (uu____25652)::[])
end))))
in (FStar_All.pipe_right uu____25624 FStar_List.flatten))
in (

let uu____25660 = (

let uu____25667 = (

let uu____25668 = (

let uu____25679 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____25690 = (

let uu____25691 = (

let uu____25696 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (uu____25696)))
in (FStar_SMTEncoding_Util.mkImp uu____25691))
in ((((ty_pred)::[])::[]), (uu____25679), (uu____25690))))
in (FStar_SMTEncoding_Util.mkForall uu____25668))
in ((uu____25667), (FStar_Pervasives_Native.Some ("subterm ordering")), ((Prims.strcat "subterm_ordering_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____25660)))
end)
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end)))
end)))
end
| uu____25715 -> begin
((

let uu____25717 = (

let uu____25718 = (FStar_Syntax_Print.lid_to_string d)
in (

let uu____25719 = (FStar_Syntax_Print.term_to_string head1)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" uu____25718 uu____25719)))
in (FStar_Errors.warn se.FStar_Syntax_Syntax.sigrng uu____25717));
(([]), ([]));
)
end))
end)))
in (

let uu____25724 = (encode_elim ())
in (match (uu____25724) with
| (decls2, elim) -> begin
(

let g = (

let uu____25744 = (

let uu____25747 = (

let uu____25750 = (

let uu____25753 = (

let uu____25756 = (

let uu____25757 = (

let uu____25768 = (

let uu____25771 = (

let uu____25772 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" uu____25772))
in FStar_Pervasives_Native.Some (uu____25771))
in ((ddtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (uu____25768)))
in FStar_SMTEncoding_Term.DeclFun (uu____25757))
in (uu____25756)::[])
in (

let uu____25777 = (

let uu____25780 = (

let uu____25783 = (

let uu____25786 = (

let uu____25789 = (

let uu____25792 = (

let uu____25795 = (

let uu____25796 = (

let uu____25803 = (

let uu____25804 = (

let uu____25815 = (FStar_SMTEncoding_Util.mkEq ((app), (dapp)))
in ((((app)::[])::[]), (vars), (uu____25815)))
in (FStar_SMTEncoding_Util.mkForall uu____25804))
in ((uu____25803), (FStar_Pervasives_Native.Some ("equality for proxy")), ((Prims.strcat "equality_tok_" ddtok))))
in (FStar_SMTEncoding_Util.mkAssume uu____25796))
in (

let uu____25828 = (

let uu____25831 = (

let uu____25832 = (

let uu____25839 = (

let uu____25840 = (

let uu____25851 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) vars')
in (

let uu____25862 = (FStar_SMTEncoding_Util.mkImp ((guard'), (ty_pred')))
in ((((ty_pred')::[])::[]), (uu____25851), (uu____25862))))
in (FStar_SMTEncoding_Util.mkForall uu____25840))
in ((uu____25839), (FStar_Pervasives_Native.Some ("data constructor typing intro")), ((Prims.strcat "data_typing_intro_" ddtok))))
in (FStar_SMTEncoding_Util.mkAssume uu____25832))
in (uu____25831)::[])
in (uu____25795)::uu____25828))
in ((FStar_SMTEncoding_Util.mkAssume ((tok_typing1), (FStar_Pervasives_Native.Some ("typing for data constructor proxy")), ((Prims.strcat "typing_tok_" ddtok)))))::uu____25792)
in (FStar_List.append uu____25789 elim))
in (FStar_List.append decls_pred uu____25786))
in (FStar_List.append decls_formals uu____25783))
in (FStar_List.append proxy_fresh uu____25780))
in (FStar_List.append uu____25753 uu____25777)))
in (FStar_List.append decls3 uu____25750))
in (FStar_List.append decls2 uu____25747))
in (FStar_List.append binder_decls uu____25744))
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
and encode_sigelts : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun uu____25908 se -> (match (uu____25908) with
| (g, env1) -> begin
(

let uu____25928 = (encode_sigelt env1 se)
in (match (uu____25928) with
| (g', env2) -> begin
(((FStar_List.append g g')), (env2))
end))
end)) (([]), (env)))))


let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env bindings -> (

let encode_binding = (fun b uu____25987 -> (match (uu____25987) with
| (i, decls, env1) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (uu____26019) -> begin
(((i + (Prims.parse_int "1"))), ([]), (env1))
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env1.tcenv x.FStar_Syntax_Syntax.sort)
in ((

let uu____26025 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____26025) with
| true -> begin
(

let uu____26026 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____26027 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____26028 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" uu____26026 uu____26027 uu____26028))))
end
| uu____26029 -> begin
()
end));
(

let uu____26030 = (encode_term t1 env1)
in (match (uu____26030) with
| (t, decls') -> begin
(

let t_hash = (FStar_SMTEncoding_Term.hash_of_term t)
in (

let uu____26046 = (

let uu____26053 = (

let uu____26054 = (

let uu____26055 = (FStar_Util.digest_of_string t_hash)
in (Prims.strcat uu____26055 (Prims.strcat "_" (Prims.string_of_int i))))
in (Prims.strcat "x_" uu____26054))
in (new_term_constant_from_string env1 x uu____26053))
in (match (uu____26046) with
| (xxsym, xx, env') -> begin
(

let t2 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel FStar_Pervasives_Native.None xx t)
in (

let caption = (

let uu____26071 = (FStar_Options.log_queries ())
in (match (uu____26071) with
| true -> begin
(

let uu____26074 = (

let uu____26075 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____26076 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____26077 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" uu____26075 uu____26076 uu____26077))))
in FStar_Pervasives_Native.Some (uu____26074))
end
| uu____26078 -> begin
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
| FStar_TypeChecker_Env.Binding_lid (x, (uu____26093, t)) -> begin
(

let t_norm = (whnf env1 t)
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____26107 = (encode_free_var false env1 fv t t_norm [])
in (match (uu____26107) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))))
end
| FStar_TypeChecker_Env.Binding_sig_inst (uu____26130, se, uu____26132) -> begin
(

let uu____26137 = (encode_sigelt env1 se)
in (match (uu____26137) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))
end
| FStar_TypeChecker_Env.Binding_sig (uu____26154, se) -> begin
(

let uu____26160 = (encode_sigelt env1 se)
in (match (uu____26160) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))
end)
end))
in (

let uu____26177 = (FStar_List.fold_right encode_binding bindings (((Prims.parse_int "0")), ([]), (env)))
in (match (uu____26177) with
| (uu____26200, decls, env1) -> begin
((decls), (env1))
end))))


let encode_labels : 'Auu____26215 'Auu____26216 . ((Prims.string * FStar_SMTEncoding_Term.sort) * 'Auu____26216 * 'Auu____26215) Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl Prims.list) = (fun labs -> (

let prefix1 = (FStar_All.pipe_right labs (FStar_List.map (fun uu____26284 -> (match (uu____26284) with
| (l, uu____26296, uu____26297) -> begin
FStar_SMTEncoding_Term.DeclFun ((((FStar_Pervasives_Native.fst l)), ([]), (FStar_SMTEncoding_Term.Bool_sort), (FStar_Pervasives_Native.None)))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun uu____26343 -> (match (uu____26343) with
| (l, uu____26357, uu____26358) -> begin
(

let uu____26367 = (FStar_All.pipe_left (fun _0_46 -> FStar_SMTEncoding_Term.Echo (_0_46)) (FStar_Pervasives_Native.fst l))
in (

let uu____26368 = (

let uu____26371 = (

let uu____26372 = (FStar_SMTEncoding_Util.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (uu____26372))
in (uu____26371)::[])
in (uu____26367)::uu____26368))
end))))
in ((prefix1), (suffix)))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (

let uu____26394 = (

let uu____26397 = (

let uu____26398 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (

let uu____26401 = (

let uu____26402 = (FStar_TypeChecker_Env.current_module tcenv)
in (FStar_All.pipe_right uu____26402 FStar_Ident.string_of_lid))
in {bindings = []; depth = (Prims.parse_int "0"); tcenv = tcenv; warn = true; cache = uu____26398; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true; current_module_name = uu____26401}))
in (uu____26397)::[])
in (FStar_ST.op_Colon_Equals last_env uu____26394)))


let get_env : FStar_Ident.lident  ->  FStar_TypeChecker_Env.env  ->  env_t = (fun cmn tcenv -> (

let uu____26429 = (FStar_ST.op_Bang last_env)
in (match (uu____26429) with
| [] -> begin
(failwith "No env; call init first!")
end
| (e)::uu____26451 -> begin
(

let uu___157_26454 = e
in (

let uu____26455 = (FStar_Ident.string_of_lid cmn)
in {bindings = uu___157_26454.bindings; depth = uu___157_26454.depth; tcenv = tcenv; warn = uu___157_26454.warn; cache = uu___157_26454.cache; nolabels = uu___157_26454.nolabels; use_zfuel_name = uu___157_26454.use_zfuel_name; encode_non_total_function_typ = uu___157_26454.encode_non_total_function_typ; current_module_name = uu____26455}))
end)))


let set_env : env_t  ->  Prims.unit = (fun env -> (

let uu____26460 = (FStar_ST.op_Bang last_env)
in (match (uu____26460) with
| [] -> begin
(failwith "Empty env stack")
end
| (uu____26481)::tl1 -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl1))
end)))


let push_env : Prims.unit  ->  Prims.unit = (fun uu____26506 -> (

let uu____26507 = (FStar_ST.op_Bang last_env)
in (match (uu____26507) with
| [] -> begin
(failwith "Empty env stack")
end
| (hd1)::tl1 -> begin
(

let refs = (FStar_Util.smap_copy hd1.cache)
in (

let top = (

let uu___158_26536 = hd1
in {bindings = uu___158_26536.bindings; depth = uu___158_26536.depth; tcenv = uu___158_26536.tcenv; warn = uu___158_26536.warn; cache = refs; nolabels = uu___158_26536.nolabels; use_zfuel_name = uu___158_26536.use_zfuel_name; encode_non_total_function_typ = uu___158_26536.encode_non_total_function_typ; current_module_name = uu___158_26536.current_module_name})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd1)::tl1))))
end)))


let pop_env : Prims.unit  ->  Prims.unit = (fun uu____26558 -> (

let uu____26559 = (FStar_ST.op_Bang last_env)
in (match (uu____26559) with
| [] -> begin
(failwith "Popping an empty stack")
end
| (uu____26580)::tl1 -> begin
(FStar_ST.op_Colon_Equals last_env tl1)
end)))


let mark_env : Prims.unit  ->  Prims.unit = (fun uu____26605 -> (push_env ()))


let reset_mark_env : Prims.unit  ->  Prims.unit = (fun uu____26609 -> (pop_env ()))


let commit_mark_env : Prims.unit  ->  Prims.unit = (fun uu____26613 -> (

let uu____26614 = (FStar_ST.op_Bang last_env)
in (match (uu____26614) with
| (hd1)::(uu____26636)::tl1 -> begin
(FStar_ST.op_Colon_Equals last_env ((hd1)::tl1))
end
| uu____26658 -> begin
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
| ((uu____26723)::uu____26724, FStar_SMTEncoding_Term.Assume (a)) -> begin
FStar_SMTEncoding_Term.Assume ((

let uu___159_26732 = a
in {FStar_SMTEncoding_Term.assumption_term = uu___159_26732.FStar_SMTEncoding_Term.assumption_term; FStar_SMTEncoding_Term.assumption_caption = uu___159_26732.FStar_SMTEncoding_Term.assumption_caption; FStar_SMTEncoding_Term.assumption_name = uu___159_26732.FStar_SMTEncoding_Term.assumption_name; FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids}))
end
| uu____26733 -> begin
d
end))


let fact_dbs_for_lid : env_t  ->  FStar_Ident.lid  ->  FStar_SMTEncoding_Term.fact_db_id Prims.list = (fun env lid -> (

let uu____26750 = (

let uu____26753 = (

let uu____26754 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in FStar_SMTEncoding_Term.Namespace (uu____26754))
in (

let uu____26755 = (open_fact_db_tags env)
in (uu____26753)::uu____26755))
in (FStar_SMTEncoding_Term.Name (lid))::uu____26750))


let encode_top_level_facts : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env se -> (

let fact_db_ids = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.collect (fact_dbs_for_lid env)))
in (

let uu____26779 = (encode_sigelt env se)
in (match (uu____26779) with
| (g, env1) -> begin
(

let g1 = (FStar_All.pipe_right g (FStar_List.map (place_decl_in_fact_dbs env1 fact_db_ids)))
in ((g1), (env1)))
end))))


let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (

let caption = (fun decls -> (

let uu____26817 = (FStar_Options.log_queries ())
in (match (uu____26817) with
| true -> begin
(

let uu____26820 = (

let uu____26821 = (

let uu____26822 = (

let uu____26823 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.map FStar_Syntax_Print.lid_to_string))
in (FStar_All.pipe_right uu____26823 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " uu____26822))
in FStar_SMTEncoding_Term.Caption (uu____26821))
in (uu____26820)::decls)
end
| uu____26832 -> begin
decls
end)))
in (

let env = (

let uu____26834 = (FStar_TypeChecker_Env.current_module tcenv)
in (get_env uu____26834 tcenv))
in (

let uu____26835 = (encode_top_level_facts env se)
in (match (uu____26835) with
| (decls, env1) -> begin
((set_env env1);
(

let uu____26849 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 uu____26849));
)
end)))))


let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____26861 -> begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in ((

let uu____26863 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____26863) with
| true -> begin
(

let uu____26864 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) Prims.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name uu____26864))
end
| uu____26865 -> begin
()
end));
(

let env = (get_env modul.FStar_Syntax_Syntax.name tcenv)
in (

let encode_signature = (fun env1 ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun uu____26899 se -> (match (uu____26899) with
| (g, env2) -> begin
(

let uu____26919 = (encode_top_level_facts env2 se)
in (match (uu____26919) with
| (g', env3) -> begin
(((FStar_List.append g g')), (env3))
end))
end)) (([]), (env1)))))
in (

let uu____26942 = (encode_signature (

let uu___160_26951 = env
in {bindings = uu___160_26951.bindings; depth = uu___160_26951.depth; tcenv = uu___160_26951.tcenv; warn = false; cache = uu___160_26951.cache; nolabels = uu___160_26951.nolabels; use_zfuel_name = uu___160_26951.use_zfuel_name; encode_non_total_function_typ = uu___160_26951.encode_non_total_function_typ; current_module_name = uu___160_26951.current_module_name}) modul.FStar_Syntax_Syntax.exports)
in (match (uu____26942) with
| (decls, env1) -> begin
(

let caption = (fun decls1 -> (

let uu____26968 = (FStar_Options.log_queries ())
in (match (uu____26968) with
| true -> begin
(

let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::decls1) ((FStar_SMTEncoding_Term.Caption ((Prims.strcat "End " msg)))::[])))
end
| uu____26972 -> begin
decls1
end)))
in ((set_env (

let uu___161_26976 = env1
in {bindings = uu___161_26976.bindings; depth = uu___161_26976.depth; tcenv = uu___161_26976.tcenv; warn = true; cache = uu___161_26976.cache; nolabels = uu___161_26976.nolabels; use_zfuel_name = uu___161_26976.use_zfuel_name; encode_non_total_function_typ = uu___161_26976.encode_non_total_function_typ; current_module_name = uu___161_26976.current_module_name}));
(

let uu____26978 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____26978) with
| true -> begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end
| uu____26979 -> begin
()
end));
(

let decls1 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls1));
))
end))));
)))


let encode_query : (Prims.unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_ErrorReporting.label Prims.list * FStar_SMTEncoding_Term.decl * FStar_SMTEncoding_Term.decl Prims.list) = (fun use_env_msg tcenv q -> ((

let uu____27033 = (

let uu____27034 = (FStar_TypeChecker_Env.current_module tcenv)
in uu____27034.FStar_Ident.str)
in (FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name uu____27033));
(

let env = (

let uu____27036 = (FStar_TypeChecker_Env.current_module tcenv)
in (get_env uu____27036 tcenv))
in (

let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (

let uu____27048 = (

let rec aux = (fun bindings1 -> (match (bindings1) with
| (FStar_TypeChecker_Env.Binding_var (x))::rest -> begin
(

let uu____27083 = (aux rest)
in (match (uu____27083) with
| (out, rest1) -> begin
(

let t = (

let uu____27113 = (FStar_Syntax_Util.destruct_typ_as_formula x.FStar_Syntax_Syntax.sort)
in (match (uu____27113) with
| FStar_Pervasives_Native.Some (uu____27118) -> begin
(

let uu____27119 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.t_unit)
in (FStar_Syntax_Util.refine uu____27119 x.FStar_Syntax_Syntax.sort))
end
| uu____27120 -> begin
x.FStar_Syntax_Syntax.sort
end))
in (

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
in (

let uu____27124 = (

let uu____27127 = (FStar_Syntax_Syntax.mk_binder (

let uu___162_27130 = x
in {FStar_Syntax_Syntax.ppname = uu___162_27130.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___162_27130.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in (uu____27127)::out)
in ((uu____27124), (rest1)))))
end))
end
| uu____27135 -> begin
(([]), (bindings1))
end))
in (

let uu____27142 = (aux bindings)
in (match (uu____27142) with
| (closing, bindings1) -> begin
(

let uu____27167 = (FStar_Syntax_Util.close_forall_no_univs (FStar_List.rev closing) q)
in ((uu____27167), (bindings1)))
end)))
in (match (uu____27048) with
| (q1, bindings1) -> begin
(

let uu____27190 = (

let uu____27195 = (FStar_List.filter (fun uu___129_27200 -> (match (uu___129_27200) with
| FStar_TypeChecker_Env.Binding_sig (uu____27201) -> begin
false
end
| uu____27208 -> begin
true
end)) bindings1)
in (encode_env_bindings env uu____27195))
in (match (uu____27190) with
| (env_decls, env1) -> begin
((

let uu____27226 = (((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTQuery"))))
in (match (uu____27226) with
| true -> begin
(

let uu____27227 = (FStar_Syntax_Print.term_to_string q1)
in (FStar_Util.print1 "Encoding query formula: %s\n" uu____27227))
end
| uu____27228 -> begin
()
end));
(

let uu____27229 = (encode_formula q1 env1)
in (match (uu____27229) with
| (phi, qdecls) -> begin
(

let uu____27250 = (

let uu____27255 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg uu____27255 phi))
in (match (uu____27250) with
| (labels, phi1) -> begin
(

let uu____27272 = (encode_labels labels)
in (match (uu____27272) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append env_decls (FStar_List.append label_prefix qdecls))
in (

let qry = (

let uu____27309 = (

let uu____27316 = (FStar_SMTEncoding_Util.mkNot phi1)
in (

let uu____27317 = (varops.mk_unique "@query")
in ((uu____27316), (FStar_Pervasives_Native.Some ("query")), (uu____27317))))
in (FStar_SMTEncoding_Util.mkAssume uu____27309))
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

let uu____27336 = (FStar_TypeChecker_Env.current_module tcenv)
in (get_env uu____27336 tcenv))
in ((FStar_SMTEncoding_Z3.push "query");
(

let uu____27338 = (encode_formula q env)
in (match (uu____27338) with
| (f, uu____27344) -> begin
((FStar_SMTEncoding_Z3.pop "query");
(match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____27346) -> begin
true
end
| uu____27351 -> begin
false
end);
)
end));
)))




