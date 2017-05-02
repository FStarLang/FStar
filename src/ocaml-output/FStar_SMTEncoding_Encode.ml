
open Prims

let add_fuel = (fun x tl1 -> (

let uu____16 = (FStar_Options.unthrottle_inductives ())
in (match (uu____16) with
| true -> begin
tl1
end
| uu____18 -> begin
(x)::tl1
end)))


let withenv = (fun c uu____39 -> (match (uu____39) with
| (a, b) -> begin
((a), (b), (c))
end))


let vargs = (fun args -> (FStar_List.filter (fun uu___113_74 -> (match (uu___113_74) with
| (FStar_Util.Inl (uu____79), uu____80) -> begin
false
end
| uu____83 -> begin
true
end)) args))


let subst_lcomp_opt = (fun s l -> (match (l) with
| Some (FStar_Util.Inl (l1)) -> begin
(

let uu____114 = (

let uu____117 = (

let uu____118 = (

let uu____121 = (l1.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp s uu____121))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____118))
in FStar_Util.Inl (uu____117))
in Some (uu____114))
end
| uu____126 -> begin
l
end))


let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s '\'' '_'))


let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun lid a -> (

let a1 = (

let uu___137_140 = a
in (

let uu____141 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = uu____141; FStar_Syntax_Syntax.index = uu___137_140.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___137_140.FStar_Syntax_Syntax.sort}))
in (

let uu____142 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str a1.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (FStar_All.pipe_left escape uu____142))))


let primitive_projector_by_pos : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (

let fail = (fun uu____155 -> (

let uu____156 = (FStar_Util.format2 "Projector %s on data constructor %s not found" (Prims.string_of_int i) lid.FStar_Ident.str)
in (failwith uu____156)))
in (

let uu____157 = (FStar_TypeChecker_Env.lookup_datacon env lid)
in (match (uu____157) with
| (uu____160, t) -> begin
(

let uu____162 = (

let uu____163 = (FStar_Syntax_Subst.compress t)
in uu____163.FStar_Syntax_Syntax.n)
in (match (uu____162) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____178 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____178) with
| (binders, uu____182) -> begin
(match (((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders)))) with
| true -> begin
(fail ())
end
| uu____187 -> begin
(

let b = (FStar_List.nth binders i)
in (mk_term_projector_name lid (Prims.fst b)))
end)
end))
end
| uu____193 -> begin
(fail ())
end))
end))))


let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (

let uu____200 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str (Prims.string_of_int i))
in (FStar_All.pipe_left escape uu____200)))


let mk_term_projector : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun lid a -> (

let uu____207 = (

let uu____210 = (mk_term_projector_name lid a)
in ((uu____210), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Util.mkFreeV uu____207)))


let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_SMTEncoding_Term.term = (fun lid i -> (

let uu____217 = (

let uu____220 = (mk_term_projector_name_by_pos lid i)
in ((uu____220), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Util.mkFreeV uu____217)))


let mk_data_tester = (fun env l x -> (FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x))

type varops_t =
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; mark : Prims.unit  ->  Prims.unit; reset_mark : Prims.unit  ->  Prims.unit; commit_mark : Prims.unit  ->  Prims.unit; new_var : FStar_Ident.ident  ->  Prims.int  ->  Prims.string; new_fvar : FStar_Ident.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_SMTEncoding_Term.term; next_id : Prims.unit  ->  Prims.int; mk_unique : Prims.string  ->  Prims.string}


let varops : varops_t = (

let initial_ctr = (Prims.parse_int "100")
in (

let ctr = (FStar_Util.mk_ref initial_ctr)
in (

let new_scope = (fun uu____410 -> (

let uu____411 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (

let uu____413 = (FStar_Util.smap_create (Prims.parse_int "100"))
in ((uu____411), (uu____413)))))
in (

let scopes = (

let uu____424 = (

let uu____430 = (new_scope ())
in (uu____430)::[])
in (FStar_Util.mk_ref uu____424))
in (

let mk_unique = (fun y -> (

let y1 = (escape y)
in (

let y2 = (

let uu____455 = (

let uu____457 = (FStar_ST.read scopes)
in (FStar_Util.find_map uu____457 (fun uu____474 -> (match (uu____474) with
| (names1, uu____481) -> begin
(FStar_Util.smap_try_find names1 y1)
end))))
in (match (uu____455) with
| None -> begin
y1
end
| Some (uu____486) -> begin
((FStar_Util.incr ctr);
(

let uu____491 = (

let uu____492 = (

let uu____493 = (FStar_ST.read ctr)
in (Prims.string_of_int uu____493))
in (Prims.strcat "__" uu____492))
in (Prims.strcat y1 uu____491));
)
end))
in (

let top_scope = (

let uu____498 = (

let uu____503 = (FStar_ST.read scopes)
in (FStar_List.hd uu____503))
in (FStar_All.pipe_left Prims.fst uu____498))
in ((FStar_Util.smap_add top_scope y2 true);
y2;
)))))
in (

let new_var = (fun pp rn -> (FStar_All.pipe_left mk_unique (Prims.strcat pp.FStar_Ident.idText (Prims.strcat "__" (Prims.string_of_int rn)))))
in (

let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (

let next_id1 = (fun uu____542 -> ((FStar_Util.incr ctr);
(FStar_ST.read ctr);
))
in (

let fresh1 = (fun pfx -> (

let uu____553 = (

let uu____554 = (next_id1 ())
in (FStar_All.pipe_left Prims.string_of_int uu____554))
in (FStar_Util.format2 "%s_%s" pfx uu____553)))
in (

let string_const = (fun s -> (

let uu____559 = (

let uu____561 = (FStar_ST.read scopes)
in (FStar_Util.find_map uu____561 (fun uu____578 -> (match (uu____578) with
| (uu____584, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))
in (match (uu____559) with
| Some (f) -> begin
f
end
| None -> begin
(

let id = (next_id1 ())
in (

let f = (

let uu____593 = (FStar_SMTEncoding_Util.mk_String_const id)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____593))
in (

let top_scope = (

let uu____596 = (

let uu____601 = (FStar_ST.read scopes)
in (FStar_List.hd uu____601))
in (FStar_All.pipe_left Prims.snd uu____596))
in ((FStar_Util.smap_add top_scope s f);
f;
))))
end)))
in (

let push1 = (fun uu____629 -> (

let uu____630 = (

let uu____636 = (new_scope ())
in (

let uu____641 = (FStar_ST.read scopes)
in (uu____636)::uu____641))
in (FStar_ST.write scopes uu____630)))
in (

let pop1 = (fun uu____668 -> (

let uu____669 = (

let uu____675 = (FStar_ST.read scopes)
in (FStar_List.tl uu____675))
in (FStar_ST.write scopes uu____669)))
in (

let mark1 = (fun uu____702 -> (push1 ()))
in (

let reset_mark1 = (fun uu____706 -> (pop1 ()))
in (

let commit_mark1 = (fun uu____710 -> (

let uu____711 = (FStar_ST.read scopes)
in (match (uu____711) with
| ((hd1, hd2))::((next1, next2))::tl1 -> begin
((FStar_Util.smap_fold hd1 (fun key value v1 -> (FStar_Util.smap_add next1 key value)) ());
(FStar_Util.smap_fold hd2 (fun key value v1 -> (FStar_Util.smap_add next2 key value)) ());
(FStar_ST.write scopes ((((next1), (next2)))::tl1));
)
end
| uu____771 -> begin
(failwith "Impossible")
end)))
in {push = push1; pop = pop1; mark = mark1; reset_mark = reset_mark1; commit_mark = commit_mark1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; string_const = string_const; next_id = next_id1; mk_unique = mk_unique})))))))))))))))


let unmangle : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv = (fun x -> (

let uu___138_780 = x
in (

let uu____781 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = uu____781; FStar_Syntax_Syntax.index = uu___138_780.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___138_780.FStar_Syntax_Syntax.sort})))

type binding =
| Binding_var of (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term)
| Binding_fvar of (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option)


let uu___is_Binding_var : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Binding_var (_0) -> begin
true
end
| uu____802 -> begin
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
| uu____826 -> begin
false
end))


let __proj__Binding_fvar__item___0 : binding  ->  (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun projectee -> (match (projectee) with
| Binding_fvar (_0) -> begin
_0
end))


let binder_of_eithervar = (fun v1 -> ((v1), (None)))

type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_TypeChecker_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_SMTEncoding_Term.sort Prims.list * FStar_SMTEncoding_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool; current_module_name : Prims.string}


let print_env : env_t  ->  Prims.string = (fun e -> (

let uu____952 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun uu___114_956 -> (match (uu___114_956) with
| Binding_var (x, uu____958) -> begin
(FStar_Syntax_Print.bv_to_string x)
end
| Binding_fvar (l, uu____960, uu____961, uu____962) -> begin
(FStar_Syntax_Print.lid_to_string l)
end))))
in (FStar_All.pipe_right uu____952 (FStar_String.concat ", "))))


let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))


let caption_t : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.string Prims.option = (fun env t -> (

let uu____995 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____995) with
| true -> begin
(

let uu____997 = (FStar_Syntax_Print.term_to_string t)
in Some (uu____997))
end
| uu____998 -> begin
None
end)))


let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (

let xsym = (varops.fresh x)
in (

let uu____1008 = (FStar_SMTEncoding_Util.mkFreeV ((xsym), (s)))
in ((xsym), (uu____1008)))))


let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (Prims.strcat "@x" (Prims.string_of_int env.depth))
in (

let y = (FStar_SMTEncoding_Util.mkFreeV ((ysym), (FStar_SMTEncoding_Term.Term_sort)))
in ((ysym), (y), ((

let uu___139_1020 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = (env.depth + (Prims.parse_int "1")); tcenv = uu___139_1020.tcenv; warn = uu___139_1020.warn; cache = uu___139_1020.cache; nolabels = uu___139_1020.nolabels; use_zfuel_name = uu___139_1020.use_zfuel_name; encode_non_total_function_typ = uu___139_1020.encode_non_total_function_typ; current_module_name = uu___139_1020.current_module_name}))))))


let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let uu___140_1033 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = uu___140_1033.depth; tcenv = uu___140_1033.tcenv; warn = uu___140_1033.warn; cache = uu___140_1033.cache; nolabels = uu___140_1033.nolabels; use_zfuel_name = uu___140_1033.use_zfuel_name; encode_non_total_function_typ = uu___140_1033.encode_non_total_function_typ; current_module_name = uu___140_1033.current_module_name}))))))


let new_term_constant_from_string : env_t  ->  FStar_Syntax_Syntax.bv  ->  Prims.string  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x str -> (

let ysym = (varops.mk_unique str)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let uu___141_1049 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = uu___141_1049.depth; tcenv = uu___141_1049.tcenv; warn = uu___141_1049.warn; cache = uu___141_1049.cache; nolabels = uu___141_1049.nolabels; use_zfuel_name = uu___141_1049.use_zfuel_name; encode_non_total_function_typ = uu___141_1049.encode_non_total_function_typ; current_module_name = uu___141_1049.current_module_name}))))))


let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (

let uu___142_1059 = env
in {bindings = (Binding_var (((x), (t))))::env.bindings; depth = uu___142_1059.depth; tcenv = uu___142_1059.tcenv; warn = uu___142_1059.warn; cache = uu___142_1059.cache; nolabels = uu___142_1059.nolabels; use_zfuel_name = uu___142_1059.use_zfuel_name; encode_non_total_function_typ = uu___142_1059.encode_non_total_function_typ; current_module_name = uu___142_1059.current_module_name}))


let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let aux = (fun a' -> (lookup_binding env (fun uu___115_1075 -> (match (uu___115_1075) with
| Binding_var (b, t) when (FStar_Syntax_Syntax.bv_eq b a') -> begin
Some (((b), (t)))
end
| uu____1083 -> begin
None
end))))
in (

let uu____1086 = (aux a)
in (match (uu____1086) with
| None -> begin
(

let a2 = (unmangle a)
in (

let uu____1093 = (aux a2)
in (match (uu____1093) with
| None -> begin
(

let uu____1099 = (

let uu____1100 = (FStar_Syntax_Print.bv_to_string a2)
in (

let uu____1101 = (print_env env)
in (FStar_Util.format2 "Bound term variable not found (after unmangling): %s in environment: %s" uu____1100 uu____1101)))
in (failwith uu____1099))
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
in (

let uu____1121 = (

let uu___143_1122 = env
in (

let uu____1123 = (

let uu____1125 = (

let uu____1126 = (

let uu____1133 = (

let uu____1135 = (FStar_SMTEncoding_Util.mkApp ((ftok), ([])))
in (FStar_All.pipe_left (fun _0_29 -> Some (_0_29)) uu____1135))
in ((x), (fname), (uu____1133), (None)))
in Binding_fvar (uu____1126))
in (uu____1125)::env.bindings)
in {bindings = uu____1123; depth = uu___143_1122.depth; tcenv = uu___143_1122.tcenv; warn = uu___143_1122.warn; cache = uu___143_1122.cache; nolabels = uu___143_1122.nolabels; use_zfuel_name = uu___143_1122.use_zfuel_name; encode_non_total_function_typ = uu___143_1122.encode_non_total_function_typ; current_module_name = uu___143_1122.current_module_name}))
in ((fname), (ftok), (uu____1121))))))


let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun uu___116_1157 -> (match (uu___116_1157) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some (((t1), (t2), (t3)))
end
| uu____1179 -> begin
None
end))))


let contains_name : env_t  ->  Prims.string  ->  Prims.bool = (fun env s -> (

let uu____1191 = (lookup_binding env (fun uu___117_1193 -> (match (uu___117_1193) with
| Binding_fvar (b, t1, t2, t3) when (b.FStar_Ident.str = s) -> begin
Some (())
end
| uu____1203 -> begin
None
end)))
in (FStar_All.pipe_right uu____1191 FStar_Option.isSome)))


let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun env a -> (

let uu____1216 = (try_lookup_lid env a)
in (match (uu____1216) with
| None -> begin
(

let uu____1233 = (

let uu____1234 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" uu____1234))
in (failwith uu____1233))
end
| Some (s) -> begin
s
end)))


let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (

let uu___144_1265 = env
in {bindings = (Binding_fvar (((x), (fname), (ftok), (None))))::env.bindings; depth = uu___144_1265.depth; tcenv = uu___144_1265.tcenv; warn = uu___144_1265.warn; cache = uu___144_1265.cache; nolabels = uu___144_1265.nolabels; use_zfuel_name = uu___144_1265.use_zfuel_name; encode_non_total_function_typ = uu___144_1265.encode_non_total_function_typ; current_module_name = uu___144_1265.current_module_name}))


let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (

let uu____1277 = (lookup_lid env x)
in (match (uu____1277) with
| (t1, t2, uu____1285) -> begin
(

let t3 = (

let uu____1291 = (

let uu____1295 = (

let uu____1297 = (FStar_SMTEncoding_Util.mkApp (("ZFuel"), ([])))
in (uu____1297)::[])
in ((f), (uu____1295)))
in (FStar_SMTEncoding_Util.mkApp uu____1291))
in (

let uu___145_1300 = env
in {bindings = (Binding_fvar (((x), (t1), (t2), (Some (t3)))))::env.bindings; depth = uu___145_1300.depth; tcenv = uu___145_1300.tcenv; warn = uu___145_1300.warn; cache = uu___145_1300.cache; nolabels = uu___145_1300.nolabels; use_zfuel_name = uu___145_1300.use_zfuel_name; encode_non_total_function_typ = uu___145_1300.encode_non_total_function_typ; current_module_name = uu___145_1300.current_module_name}))
end)))


let try_lookup_free_var : env_t  ->  FStar_Ident.lident  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env l -> (

let uu____1310 = (try_lookup_lid env l)
in (match (uu____1310) with
| None -> begin
None
end
| Some (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some (f) when env.use_zfuel_name -> begin
Some (f)
end
| uu____1337 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (uu____1342, (fuel)::[]) -> begin
(

let uu____1345 = (

let uu____1346 = (

let uu____1347 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right uu____1347 Prims.fst))
in (FStar_Util.starts_with uu____1346 "fuel"))
in (match (uu____1345) with
| true -> begin
(

let uu____1349 = (

let uu____1350 = (FStar_SMTEncoding_Util.mkFreeV ((name), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_ApplyTF uu____1350 fuel))
in (FStar_All.pipe_left (fun _0_30 -> Some (_0_30)) uu____1349))
end
| uu____1352 -> begin
Some (t)
end))
end
| uu____1353 -> begin
Some (t)
end)
end
| uu____1354 -> begin
None
end)
end)
end)))


let lookup_free_var = (fun env a -> (

let uu____1372 = (try_lookup_free_var env a.FStar_Syntax_Syntax.v)
in (match (uu____1372) with
| Some (t) -> begin
t
end
| None -> begin
(

let uu____1375 = (

let uu____1376 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" uu____1376))
in (failwith uu____1375))
end)))


let lookup_free_var_name = (fun env a -> (

let uu____1393 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (uu____1393) with
| (x, uu____1400, uu____1401) -> begin
x
end)))


let lookup_free_var_sym = (fun env a -> (

let uu____1425 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (uu____1425) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.freevars = uu____1446; FStar_SMTEncoding_Term.rng = uu____1447}) when env.use_zfuel_name -> begin
((g), (zf))
end
| uu____1455 -> begin
(match (sym) with
| None -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end
| Some (sym1) -> begin
(match (sym1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, (fuel)::[]) -> begin
((g), ((fuel)::[]))
end
| uu____1469 -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end)
end)
end)
end)))


let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun uu___118_1478 -> (match (uu___118_1478) with
| Binding_fvar (uu____1480, nm', tok, uu____1483) when (nm = nm') -> begin
tok
end
| uu____1488 -> begin
None
end))))


let mkForall_fuel' = (fun n1 uu____1505 -> (match (uu____1505) with
| (pats, vars, body) -> begin
(

let fallback = (fun uu____1521 -> (FStar_SMTEncoding_Util.mkForall ((pats), (vars), (body))))
in (

let uu____1524 = (FStar_Options.unthrottle_inductives ())
in (match (uu____1524) with
| true -> begin
(fallback ())
end
| uu____1525 -> begin
(

let uu____1526 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____1526) with
| (fsym, fterm) -> begin
(

let add_fuel1 = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Util.mkApp (("HasTypeFuel"), ((fterm)::args)))
end
| uu____1545 -> begin
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

let uu____1559 = (add_fuel1 guards)
in (FStar_SMTEncoding_Util.mk_and_l uu____1559))
end
| uu____1561 -> begin
(

let uu____1562 = (add_fuel1 ((guard)::[]))
in (FStar_All.pipe_right uu____1562 FStar_List.hd))
end)
in (FStar_SMTEncoding_Util.mkImp ((guard1), (body'))))
end
| uu____1565 -> begin
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
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) -> begin
true
end
| (FStar_Syntax_Syntax.Tm_fvar (fv)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let uu____1609 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____1609 FStar_Option.isNone))
end
| uu____1622 -> begin
false
end)))


let head_redex : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let uu____1629 = (

let uu____1630 = (FStar_Syntax_Util.un_uinst t)
in uu____1630.FStar_Syntax_Syntax.n)
in (match (uu____1629) with
| FStar_Syntax_Syntax.Tm_abs (uu____1633, uu____1634, Some (FStar_Util.Inr (l, flags))) -> begin
(((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid)) || (FStar_List.existsb (fun uu___119_1663 -> (match (uu___119_1663) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____1664 -> begin
false
end)) flags))
end
| FStar_Syntax_Syntax.Tm_abs (uu____1665, uu____1666, Some (FStar_Util.Inl (lc))) -> begin
(FStar_Syntax_Util.is_tot_or_gtot_lcomp lc)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____1693 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____1693 FStar_Option.isSome))
end
| uu____1706 -> begin
false
end)))


let whnf : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____1713 = (head_normal env t)
in (match (uu____1713) with
| true -> begin
t
end
| uu____1714 -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
end)))


let norm : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t))


let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____1724 = (

let uu____1725 = (FStar_Syntax_Syntax.null_binder t)
in (uu____1725)::[])
in (

let uu____1726 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Util.abs uu____1724 uu____1726 None))))


let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(

let uu____1753 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out uu____1753))
end
| s -> begin
(

let uu____1756 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Util.mk_ApplyTT out uu____1756))
end)) e)))


let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)))


let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun uu___120_1768 -> (match (uu___120_1768) with
| (FStar_SMTEncoding_Term.Var ("ApplyTT")) | (FStar_SMTEncoding_Term.Var ("ApplyTF")) -> begin
true
end
| uu____1769 -> begin
false
end))


let is_an_eta_expansion : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env vars body -> (

let rec check_partial_applications = (fun t xs -> (match (((t.FStar_SMTEncoding_Term.tm), (xs))) with
| (FStar_SMTEncoding_Term.App (app, (f)::({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.freevars = uu____1797; FStar_SMTEncoding_Term.rng = uu____1798})::[]), (x)::xs1) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(check_partial_applications f xs1)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), uu____1812) -> begin
(

let uu____1817 = (((FStar_List.length args) = (FStar_List.length xs)) && (FStar_List.forall2 (fun a v1 -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v1)
end
| uu____1827 -> begin
false
end)) args (FStar_List.rev xs)))
in (match (uu____1817) with
| true -> begin
(tok_of_name env f)
end
| uu____1829 -> begin
None
end))
end
| (uu____1830, []) -> begin
(

let fvs = (FStar_SMTEncoding_Term.free_variables t)
in (

let uu____1833 = (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (

let uu____1835 = (FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)
in (not (uu____1835))))))
in (match (uu____1833) with
| true -> begin
Some (t)
end
| uu____1837 -> begin
None
end)))
end
| uu____1838 -> begin
None
end))
in (check_partial_applications body (FStar_List.rev vars))))


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
| uu____1922 -> begin
false
end))


let encode_const : FStar_Const.sconst  ->  FStar_SMTEncoding_Term.term = (fun uu___121_1925 -> (match (uu___121_1925) with
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

let uu____1927 = (

let uu____1931 = (

let uu____1933 = (

let uu____1934 = (FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c))
in (FStar_SMTEncoding_Term.boxInt uu____1934))
in (uu____1933)::[])
in (("FStar.Char.Char"), (uu____1931)))
in (FStar_SMTEncoding_Util.mkApp uu____1927))
end
| FStar_Const.Const_int (i, None) -> begin
(

let uu____1942 = (FStar_SMTEncoding_Util.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt uu____1942))
end
| FStar_Const.Const_int (i, Some (uu____1944)) -> begin
(failwith "Machine integers should be desugared")
end
| FStar_Const.Const_string (bytes, uu____1953) -> begin
(

let uu____1956 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const uu____1956))
end
| FStar_Const.Const_range (r) -> begin
FStar_SMTEncoding_Term.mk_Range_const
end
| FStar_Const.Const_effect -> begin
FStar_SMTEncoding_Term.mk_Term_type
end
| c -> begin
(

let uu____1960 = (

let uu____1961 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" uu____1961))
in (failwith uu____1960))
end))


let as_function_typ : env_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (

let rec aux = (fun norm1 t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1980) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_refine (uu____1988) -> begin
(

let uu____1993 = (FStar_Syntax_Util.unrefine t1)
in (aux true uu____1993))
end
| uu____1994 -> begin
(match (norm1) with
| true -> begin
(

let uu____1995 = (whnf env t1)
in (aux false uu____1995))
end
| uu____1996 -> begin
(

let uu____1997 = (

let uu____1998 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (

let uu____1999 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" uu____1998 uu____1999)))
in (failwith uu____1997))
end)
end)))
in (aux true t0)))


let curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun k -> (

let k1 = (FStar_Syntax_Subst.compress k)
in (match (k1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| uu____2020 -> begin
(

let uu____2021 = (FStar_Syntax_Syntax.mk_Total k1)
in (([]), (uu____2021)))
end)))


let rec encode_binders : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> ((

let uu____2164 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____2164) with
| true -> begin
(

let uu____2165 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" uu____2165))
end
| uu____2166 -> begin
()
end));
(

let uu____2167 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____2203 b -> (match (uu____2203) with
| (vars, guards, env1, decls, names1) -> begin
(

let uu____2246 = (

let x = (unmangle (Prims.fst b))
in (

let uu____2255 = (gen_term_var env1 x)
in (match (uu____2255) with
| (xxsym, xx, env') -> begin
(

let uu____2269 = (

let uu____2272 = (norm env1 x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt uu____2272 env1 xx))
in (match (uu____2269) with
| (guard_x_t, decls') -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (guard_x_t), (env'), (decls'), (x))
end))
end)))
in (match (uu____2246) with
| (v1, g, env2, decls', n1) -> begin
(((v1)::vars), ((g)::guards), (env2), ((FStar_List.append decls decls')), ((n1)::names1))
end))
end)) (([]), ([]), (env), ([]), ([]))))
in (match (uu____2167) with
| (vars, guards, env1, decls, names1) -> begin
(((FStar_List.rev vars)), ((FStar_List.rev guards)), (env1), (decls), ((FStar_List.rev names1)))
end));
))
and encode_term_pred : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let uu____2360 = (encode_term t env)
in (match (uu____2360) with
| (t1, decls) -> begin
(

let uu____2367 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1)
in ((uu____2367), (decls)))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let uu____2375 = (encode_term t env)
in (match (uu____2375) with
| (t1, decls) -> begin
(match (fuel_opt) with
| None -> begin
(

let uu____2384 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t1)
in ((uu____2384), (decls)))
end
| Some (f) -> begin
(

let uu____2386 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1)
in ((uu____2386), (decls)))
end)
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let t0 = (FStar_Syntax_Subst.compress t)
in ((

let uu____2393 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____2393) with
| true -> begin
(

let uu____2394 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____2395 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____2396 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" uu____2394 uu____2395 uu____2396))))
end
| uu____2397 -> begin
()
end));
(match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(

let uu____2401 = (

let uu____2402 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____2403 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____2404 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____2405 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2402 uu____2403 uu____2404 uu____2405)))))
in (failwith uu____2401))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____2409 = (

let uu____2410 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" uu____2410))
in (failwith uu____2409))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, k, uu____2415) -> begin
(encode_term t1 env)
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____2445) -> begin
(encode_term t1 env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t1 = (lookup_term_var env x)
in ((t1), ([])))
end
| FStar_Syntax_Syntax.Tm_fvar (v1) -> begin
(

let uu____2454 = (lookup_free_var env v1.FStar_Syntax_Syntax.fv_name)
in ((uu____2454), ([])))
end
| FStar_Syntax_Syntax.Tm_type (uu____2460) -> begin
((FStar_SMTEncoding_Term.mk_Term_type), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____2463) -> begin
(encode_term t1 env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____2469 = (encode_const c)
in ((uu____2469), ([])))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let module_name = env.current_module_name
in (

let uu____2484 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____2484) with
| (binders1, res) -> begin
(

let uu____2491 = ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res))
in (match (uu____2491) with
| true -> begin
(

let uu____2494 = (encode_binders None binders1 env)
in (match (uu____2494) with
| (vars, guards, env', decls, uu____2509) -> begin
(

let fsym = (

let uu____2519 = (varops.fresh "f")
in ((uu____2519), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV fsym)
in (

let app = (mk_Apply f vars)
in (

let uu____2522 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post (

let uu___146_2526 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___146_2526.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___146_2526.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___146_2526.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___146_2526.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___146_2526.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___146_2526.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___146_2526.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___146_2526.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___146_2526.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___146_2526.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___146_2526.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___146_2526.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___146_2526.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___146_2526.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___146_2526.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___146_2526.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___146_2526.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___146_2526.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___146_2526.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___146_2526.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___146_2526.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___146_2526.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___146_2526.FStar_TypeChecker_Env.qname_and_index}) res)
in (match (uu____2522) with
| (pre_opt, res_t) -> begin
(

let uu____2533 = (encode_term_pred None res_t env' app)
in (match (uu____2533) with
| (res_pred, decls') -> begin
(

let uu____2540 = (match (pre_opt) with
| None -> begin
(

let uu____2547 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____2547), ([])))
end
| Some (pre) -> begin
(

let uu____2550 = (encode_formula pre env')
in (match (uu____2550) with
| (guard, decls0) -> begin
(

let uu____2558 = (FStar_SMTEncoding_Util.mk_and_l ((guard)::guards))
in ((uu____2558), (decls0)))
end))
end)
in (match (uu____2540) with
| (guards1, guard_decls) -> begin
(

let t_interp = (

let uu____2566 = (

let uu____2572 = (FStar_SMTEncoding_Util.mkImp ((guards1), (res_pred)))
in ((((app)::[])::[]), (vars), (uu____2572)))
in (FStar_SMTEncoding_Util.mkForall uu____2566))
in (

let cvars = (

let uu____2582 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right uu____2582 (FStar_List.filter (fun uu____2588 -> (match (uu____2588) with
| (x, uu____2592) -> begin
(x <> (Prims.fst fsym))
end)))))
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), ((fsym)::cvars), (t_interp)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____2603 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____2603) with
| Some (t', sorts, uu____2619) -> begin
(

let uu____2629 = (

let uu____2630 = (

let uu____2634 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((t'), (uu____2634)))
in (FStar_SMTEncoding_Util.mkApp uu____2630))
in ((uu____2629), ([])))
end
| None -> begin
(

let tsym = (

let uu____2650 = (

let uu____2651 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_arrow_" uu____2651))
in (varops.mk_unique uu____2650))
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let caption = (

let uu____2658 = (FStar_Options.log_queries ())
in (match (uu____2658) with
| true -> begin
(

let uu____2660 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in Some (uu____2660))
end
| uu____2661 -> begin
None
end))
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (caption)))
in (

let t1 = (

let uu____2666 = (

let uu____2670 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((tsym), (uu____2670)))
in (FStar_SMTEncoding_Util.mkApp uu____2666))
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t1 FStar_SMTEncoding_Term.mk_Term_type)
in (

let k_assumption = (

let a_name = (Prims.strcat "kinding_" tsym)
in (

let uu____2678 = (

let uu____2682 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((uu____2682), (Some (a_name)), (a_name)))
in FStar_SMTEncoding_Term.Assume (uu____2678)))
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t1)
in (

let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t1)
in (

let pre_typing = (

let a_name = (Prims.strcat "pre_typing_" tsym)
in (

let uu____2695 = (

let uu____2699 = (

let uu____2700 = (

let uu____2706 = (

let uu____2707 = (

let uu____2710 = (

let uu____2711 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____2711))
in ((f_has_t), (uu____2710)))
in (FStar_SMTEncoding_Util.mkImp uu____2707))
in ((((f_has_t)::[])::[]), ((fsym)::cvars), (uu____2706)))
in (mkForall_fuel uu____2700))
in ((uu____2699), (Some ("pre-typing for functions")), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in FStar_SMTEncoding_Term.Assume (uu____2695)))
in (

let t_interp1 = (

let a_name = (Prims.strcat "interpretation_" tsym)
in (

let uu____2724 = (

let uu____2728 = (

let uu____2729 = (

let uu____2735 = (FStar_SMTEncoding_Util.mkIff ((f_has_t_z), (t_interp)))
in ((((f_has_t_z)::[])::[]), ((fsym)::cvars), (uu____2735)))
in (FStar_SMTEncoding_Util.mkForall uu____2729))
in ((uu____2728), (Some (a_name)), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in FStar_SMTEncoding_Term.Assume (uu____2724)))
in (

let t_decls = (FStar_List.append ((tdecl)::decls) (FStar_List.append decls' (FStar_List.append guard_decls ((k_assumption)::(pre_typing)::(t_interp1)::[]))))
in ((FStar_Util.smap_add env.cache tkey_hash ((tsym), (cvar_sorts), (t_decls)));
((t1), (t_decls));
)))))))))))))
end))))))
end))
end))
end)))))
end))
end
| uu____2757 -> begin
(

let tsym = (varops.fresh "Non_total_Tm_arrow")
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let t1 = (FStar_SMTEncoding_Util.mkApp ((tsym), ([])))
in (

let t_kinding = (

let a_name = (Prims.strcat "non_total_function_typing_" tsym)
in (

let uu____2766 = (

let uu____2770 = (FStar_SMTEncoding_Term.mk_HasType t1 FStar_SMTEncoding_Term.mk_Term_type)
in ((uu____2770), (Some ("Typing for non-total arrows")), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in FStar_SMTEncoding_Term.Assume (uu____2766)))
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

let uu____2779 = (

let uu____2783 = (

let uu____2784 = (

let uu____2790 = (

let uu____2791 = (

let uu____2794 = (

let uu____2795 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____2795))
in ((f_has_t), (uu____2794)))
in (FStar_SMTEncoding_Util.mkImp uu____2791))
in ((((f_has_t)::[])::[]), ((fsym)::[]), (uu____2790)))
in (mkForall_fuel uu____2784))
in ((uu____2783), (Some (a_name)), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in FStar_SMTEncoding_Term.Assume (uu____2779)))
in ((t1), ((tdecl)::(t_kinding)::(t_interp)::[]))))))))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (uu____2809) -> begin
(

let uu____2814 = (

let uu____2817 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)
in (match (uu____2817) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.tk = uu____2822; FStar_Syntax_Syntax.pos = uu____2823; FStar_Syntax_Syntax.vars = uu____2824} -> begin
(

let uu____2831 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) f)
in (match (uu____2831) with
| (b, f1) -> begin
(

let uu____2845 = (

let uu____2846 = (FStar_List.hd b)
in (Prims.fst uu____2846))
in ((uu____2845), (f1)))
end))
end
| uu____2851 -> begin
(failwith "impossible")
end))
in (match (uu____2814) with
| (x, f) -> begin
(

let uu____2858 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (uu____2858) with
| (base_t, decls) -> begin
(

let uu____2865 = (gen_term_var env x)
in (match (uu____2865) with
| (x1, xtm, env') -> begin
(

let uu____2874 = (encode_formula f env')
in (match (uu____2874) with
| (refinement, decls') -> begin
(

let uu____2881 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____2881) with
| (fsym, fterm) -> begin
(

let tm_has_type_with_fuel = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in (

let encoding = (FStar_SMTEncoding_Util.mkAnd ((tm_has_type_with_fuel), (refinement)))
in (

let cvars = (

let uu____2892 = (

let uu____2894 = (FStar_SMTEncoding_Term.free_variables refinement)
in (

let uu____2898 = (FStar_SMTEncoding_Term.free_variables tm_has_type_with_fuel)
in (FStar_List.append uu____2894 uu____2898)))
in (FStar_Util.remove_dups FStar_SMTEncoding_Term.fv_eq uu____2892))
in (

let cvars1 = (FStar_All.pipe_right cvars (FStar_List.filter (fun uu____2914 -> (match (uu____2914) with
| (y, uu____2918) -> begin
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

let uu____2937 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____2937) with
| Some (t1, uu____2952, uu____2953) -> begin
(

let uu____2963 = (

let uu____2964 = (

let uu____2968 = (FStar_All.pipe_right cvars1 (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((t1), (uu____2968)))
in (FStar_SMTEncoding_Util.mkApp uu____2964))
in ((uu____2963), ([])))
end
| None -> begin
(

let module_name = env.current_module_name
in (

let tsym = (

let uu____2985 = (

let uu____2986 = (

let uu____2987 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "_Tm_refine_" uu____2987))
in (Prims.strcat module_name uu____2986))
in (varops.mk_unique uu____2985))
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars1)
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let t1 = (

let uu____2996 = (

let uu____3000 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars1)
in ((tsym), (uu____3000)))
in (FStar_SMTEncoding_Util.mkApp uu____2996))
in (

let x_has_t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t1)
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t1 FStar_SMTEncoding_Term.mk_Term_type)
in (

let t_haseq_base = (FStar_SMTEncoding_Term.mk_haseq base_t)
in (

let t_haseq_ref = (FStar_SMTEncoding_Term.mk_haseq t1)
in (

let t_haseq1 = (

let uu____3010 = (

let uu____3014 = (

let uu____3015 = (

let uu____3021 = (FStar_SMTEncoding_Util.mkIff ((t_haseq_ref), (t_haseq_base)))
in ((((t_haseq_ref)::[])::[]), (cvars1), (uu____3021)))
in (FStar_SMTEncoding_Util.mkForall uu____3015))
in ((uu____3014), (Some ((Prims.strcat "haseq for " tsym))), ((Prims.strcat "haseq" tsym))))
in FStar_SMTEncoding_Term.Assume (uu____3010))
in (

let t_kinding = (

let uu____3031 = (

let uu____3035 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars1), (t_has_kind)))
in ((uu____3035), (Some ("refinement kinding")), ((Prims.strcat "refinement_kinding_" tsym))))
in FStar_SMTEncoding_Term.Assume (uu____3031))
in (

let t_interp = (

let uu____3045 = (

let uu____3049 = (

let uu____3050 = (

let uu____3056 = (FStar_SMTEncoding_Util.mkIff ((x_has_t), (encoding)))
in ((((x_has_t)::[])::[]), ((ffv)::(xfv)::cvars1), (uu____3056)))
in (FStar_SMTEncoding_Util.mkForall uu____3050))
in (

let uu____3068 = (

let uu____3070 = (FStar_Syntax_Print.term_to_string t0)
in Some (uu____3070))
in ((uu____3049), (uu____3068), ((Prims.strcat "refinement_interpretation_" tsym)))))
in FStar_SMTEncoding_Term.Assume (uu____3045))
in (

let t_decls = (FStar_List.append decls (FStar_List.append decls' ((tdecl)::(t_kinding)::(t_interp)::(t_haseq1)::[])))
in ((FStar_Util.smap_add env.cache tkey_hash ((tsym), (cvar_sorts), (t_decls)));
((t1), (t_decls));
))))))))))))))
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

let uu____3098 = (FStar_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Util.mk_Term_uvar uu____3098))
in (

let uu____3102 = (encode_term_pred None k env ttm)
in (match (uu____3102) with
| (t_has_k, decls) -> begin
(

let d = (

let uu____3110 = (

let uu____3114 = (

let uu____3115 = (

let uu____3116 = (

let uu____3117 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____3117))
in (FStar_Util.format1 "uvar_typing_%s" uu____3116))
in (varops.mk_unique uu____3115))
in ((t_has_k), (Some ("Uvar typing")), (uu____3114)))
in FStar_SMTEncoding_Term.Assume (uu____3110))
in ((ttm), ((FStar_List.append decls ((d)::[])))))
end)))
end
| FStar_Syntax_Syntax.Tm_app (uu____3123) -> begin
(

let uu____3133 = (FStar_Syntax_Util.head_and_args t0)
in (match (uu____3133) with
| (head1, args_e) -> begin
(

let uu____3161 = (

let uu____3169 = (

let uu____3170 = (FStar_Syntax_Subst.compress head1)
in uu____3170.FStar_Syntax_Syntax.n)
in ((uu____3169), (args_e)))
in (match (uu____3161) with
| (uu____3180, uu____3181) when (head_redex env head1) -> begin
(

let uu____3192 = (whnf env t)
in (encode_term uu____3192 env))
end
| ((FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), (_)::((v1, _))::((v2, _))::[])) | ((FStar_Syntax_Syntax.Tm_fvar (fv), (_)::((v1, _))::((v2, _))::[])) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
(

let uu____3266 = (encode_term v1 env)
in (match (uu____3266) with
| (v11, decls1) -> begin
(

let uu____3273 = (encode_term v2 env)
in (match (uu____3273) with
| (v21, decls2) -> begin
(

let uu____3280 = (FStar_SMTEncoding_Util.mk_LexCons v11 v21)
in ((uu____3280), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), uu____3282) -> begin
(

let e0 = (

let uu____3294 = (FStar_List.hd args_e)
in (FStar_TypeChecker_Util.reify_body_with_arg env.tcenv head1 uu____3294))
in ((

let uu____3300 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____3300) with
| true -> begin
(

let uu____3301 = (FStar_Syntax_Print.term_to_string e0)
in (FStar_Util.print1 "Result of normalization %s\n" uu____3301))
end
| uu____3302 -> begin
()
end));
(

let e = (

let uu____3306 = (

let uu____3307 = (FStar_TypeChecker_Util.remove_reify e0)
in (

let uu____3308 = (FStar_List.tl args_e)
in (FStar_Syntax_Syntax.mk_Tm_app uu____3307 uu____3308)))
in (uu____3306 None t0.FStar_Syntax_Syntax.pos))
in (encode_term e env));
))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____3317)), ((arg, uu____3319))::[]) -> begin
(encode_term arg env)
end
| uu____3337 -> begin
(

let uu____3345 = (encode_args args_e env)
in (match (uu____3345) with
| (args, decls) -> begin
(

let encode_partial_app = (fun ht_opt -> (

let uu____3378 = (encode_term head1 env)
in (match (uu____3378) with
| (head2, decls') -> begin
(

let app_tm = (mk_Apply_args head2 args)
in (match (ht_opt) with
| None -> begin
((app_tm), ((FStar_List.append decls decls')))
end
| Some (formals, c) -> begin
(

let uu____3417 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (uu____3417) with
| (formals1, rest) -> begin
(

let subst1 = (FStar_List.map2 (fun uu____3459 uu____3460 -> (match (((uu____3459), (uu____3460))) with
| ((bv, uu____3474), (a, uu____3476)) -> begin
FStar_Syntax_Syntax.NT (((bv), (a)))
end)) formals1 args_e)
in (

let ty = (

let uu____3490 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right uu____3490 (FStar_Syntax_Subst.subst subst1)))
in (

let uu____3495 = (encode_term_pred None ty env app_tm)
in (match (uu____3495) with
| (has_type, decls'') -> begin
(

let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (

let e_typing = (

let uu____3505 = (

let uu____3509 = (FStar_SMTEncoding_Util.mkForall ((((has_type)::[])::[]), (cvars), (has_type)))
in (

let uu____3514 = (

let uu____3515 = (

let uu____3516 = (

let uu____3517 = (FStar_SMTEncoding_Term.hash_of_term app_tm)
in (FStar_Util.digest_of_string uu____3517))
in (Prims.strcat "partial_app_typing_" uu____3516))
in (varops.mk_unique uu____3515))
in ((uu____3509), (Some ("Partial app typing")), (uu____3514))))
in FStar_SMTEncoding_Term.Assume (uu____3505))
in ((app_tm), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' ((e_typing)::[]))))))))
end))))
end))
end))
end)))
in (

let encode_full_app = (fun fv -> (

let uu____3534 = (lookup_free_var_sym env fv)
in (match (uu____3534) with
| (fname, fuel_args) -> begin
(

let tm = (FStar_SMTEncoding_Util.mkApp' ((fname), ((FStar_List.append fuel_args args))))
in ((tm), (decls)))
end)))
in (

let head2 = (FStar_Syntax_Subst.compress head1)
in (

let head_type = (match (head2.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (x); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (x)) -> begin
Some (x.FStar_Syntax_Syntax.sort)
end
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(

let uu____3572 = (

let uu____3573 = (

let uu____3576 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____3576 Prims.fst))
in (FStar_All.pipe_right uu____3573 Prims.snd))
in Some (uu____3572))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____3595, (FStar_Util.Inl (t1), uu____3597), uu____3598) -> begin
Some (t1)
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____3636, (FStar_Util.Inr (c), uu____3638), uu____3639) -> begin
Some ((FStar_Syntax_Util.comp_result c))
end
| uu____3677 -> begin
None
end)
in (match (head_type) with
| None -> begin
(encode_partial_app None)
end
| Some (head_type1) -> begin
(

let head_type2 = (

let uu____3697 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type1)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine uu____3697))
in (

let uu____3698 = (curried_arrow_formals_comp head_type2)
in (match (uu____3698) with
| (formals, c) -> begin
(match (head2.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| uu____3723 -> begin
(match (((FStar_List.length formals) > (FStar_List.length args))) with
| true -> begin
(encode_partial_app (Some (((formals), (c)))))
end
| uu____3735 -> begin
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

let uu____3768 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____3768) with
| (bs1, body1, opening) -> begin
(

let fallback = (fun uu____3783 -> (

let f = (varops.fresh "Tm_abs")
in (

let decl = FStar_SMTEncoding_Term.DeclFun (((f), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Imprecise function encoding"))))
in (

let uu____3788 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in ((uu____3788), ((decl)::[]))))))
in (

let is_impure = (fun lc -> (match (lc) with
| FStar_Util.Inl (lc1) -> begin
(

let uu____3799 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1)
in (not (uu____3799)))
end
| FStar_Util.Inr (eff, uu____3801) -> begin
(

let uu____3807 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv eff)
in (FStar_All.pipe_right uu____3807 Prims.op_Negation))
end))
in (

let reify_comp_and_body = (fun env1 c body2 -> (

let reified_body = (FStar_TypeChecker_Util.reify_body env1.tcenv body2)
in (

let c1 = (match (c) with
| FStar_Util.Inl (lc) -> begin
(

let typ = (

let uu____3852 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_TypeChecker_Env.reify_comp (

let uu___147_3853 = env1.tcenv
in {FStar_TypeChecker_Env.solver = uu___147_3853.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___147_3853.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___147_3853.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___147_3853.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___147_3853.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___147_3853.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___147_3853.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___147_3853.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___147_3853.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___147_3853.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___147_3853.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___147_3853.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___147_3853.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___147_3853.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___147_3853.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___147_3853.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___147_3853.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___147_3853.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___147_3853.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___147_3853.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___147_3853.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___147_3853.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___147_3853.FStar_TypeChecker_Env.qname_and_index}) uu____3852 FStar_Syntax_Syntax.U_unknown))
in (

let uu____3854 = (

let uu____3855 = (FStar_Syntax_Syntax.mk_Total typ)
in (FStar_Syntax_Util.lcomp_of_comp uu____3855))
in FStar_Util.Inl (uu____3854)))
end
| FStar_Util.Inr (eff_name, uu____3862) -> begin
c
end)
in ((c1), (reified_body)))))
in (

let codomain_eff = (fun lc -> (match (lc) with
| FStar_Util.Inl (lc1) -> begin
(

let uu____3893 = (

let uu____3894 = (lc1.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening uu____3894))
in (FStar_All.pipe_right uu____3893 (fun _0_31 -> Some (_0_31))))
end
| FStar_Util.Inr (eff, flags) -> begin
(

let new_uvar1 = (fun uu____3906 -> (

let uu____3907 = (FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange [] FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right uu____3907 Prims.fst)))
in (match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid)) with
| true -> begin
(

let uu____3915 = (

let uu____3916 = (new_uvar1 ())
in (FStar_Syntax_Syntax.mk_Total uu____3916))
in (FStar_All.pipe_right uu____3915 (fun _0_32 -> Some (_0_32))))
end
| uu____3918 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid)) with
| true -> begin
(

let uu____3920 = (

let uu____3921 = (new_uvar1 ())
in (FStar_Syntax_Syntax.mk_GTotal uu____3921))
in (FStar_All.pipe_right uu____3920 (fun _0_33 -> Some (_0_33))))
end
| uu____3923 -> begin
None
end)
end))
end))
in (match (lopt) with
| None -> begin
((

let uu____3932 = (

let uu____3933 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)" uu____3933))
in (FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____3932));
(fallback ());
)
end
| Some (lc) -> begin
(

let lc1 = lc
in (

let uu____3948 = ((is_impure lc1) && (

let uu____3949 = (FStar_TypeChecker_Env.is_reifiable env.tcenv lc1)
in (not (uu____3949))))
in (match (uu____3948) with
| true -> begin
(fallback ())
end
| uu____3952 -> begin
(

let cache_size = (FStar_Util.smap_size env.cache)
in (

let uu____3959 = (encode_binders None bs1 env)
in (match (uu____3959) with
| (vars, guards, envbody, decls, uu____3974) -> begin
(

let uu____3981 = (

let uu____3989 = (FStar_TypeChecker_Env.is_reifiable env.tcenv lc1)
in (match (uu____3989) with
| true -> begin
(reify_comp_and_body envbody lc1 body1)
end
| uu____3997 -> begin
((lc1), (body1))
end))
in (match (uu____3981) with
| (lc2, body2) -> begin
(

let uu____4014 = (encode_term body2 envbody)
in (match (uu____4014) with
| (body3, decls') -> begin
(

let uu____4021 = (

let uu____4026 = (codomain_eff lc2)
in (match (uu____4026) with
| None -> begin
((None), ([]))
end
| Some (c) -> begin
(

let tfun = (FStar_Syntax_Util.arrow bs1 c)
in (

let uu____4038 = (encode_term tfun env)
in (match (uu____4038) with
| (t1, decls1) -> begin
((Some (t1)), (decls1))
end)))
end))
in (match (uu____4021) with
| (arrow_t_opt, decls'') -> begin
(

let key_body = (

let uu____4057 = (

let uu____4063 = (

let uu____4064 = (

let uu____4067 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____4067), (body3)))
in (FStar_SMTEncoding_Util.mkImp uu____4064))
in (([]), (vars), (uu____4063)))
in (FStar_SMTEncoding_Util.mkForall uu____4057))
in (

let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (

let cvars1 = (match (arrow_t_opt) with
| None -> begin
cvars
end
| Some (t1) -> begin
(

let uu____4075 = (

let uu____4077 = (FStar_SMTEncoding_Term.free_variables t1)
in (FStar_List.append uu____4077 cvars))
in (FStar_Util.remove_dups FStar_SMTEncoding_Term.fv_eq uu____4075))
end)
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), (cvars1), (key_body)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____4088 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____4088) with
| Some (t1, uu____4103, uu____4104) -> begin
(

let uu____4114 = (

let uu____4115 = (

let uu____4119 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars1)
in ((t1), (uu____4119)))
in (FStar_SMTEncoding_Util.mkApp uu____4115))
in ((uu____4114), ([])))
end
| None -> begin
(

let uu____4130 = (is_an_eta_expansion env vars body3)
in (match (uu____4130) with
| Some (t1) -> begin
(

let decls1 = (

let uu____4137 = (

let uu____4138 = (FStar_Util.smap_size env.cache)
in (uu____4138 = cache_size))
in (match (uu____4137) with
| true -> begin
[]
end
| uu____4145 -> begin
(FStar_List.append decls decls')
end))
in ((t1), (decls1)))
end
| None -> begin
(

let cvar_sorts = (FStar_List.map Prims.snd cvars1)
in (

let fsym = (

let module_name = env.current_module_name
in (

let fsym = (

let uu____4154 = (

let uu____4155 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_abs_" uu____4155))
in (varops.mk_unique uu____4154))
in (Prims.strcat module_name (Prims.strcat "_" fsym))))
in (

let fdecl = FStar_SMTEncoding_Term.DeclFun (((fsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let f = (

let uu____4160 = (

let uu____4164 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars1)
in ((fsym), (uu____4164)))
in (FStar_SMTEncoding_Util.mkApp uu____4160))
in (

let app = (mk_Apply f vars)
in (

let typing_f = (match (arrow_t_opt) with
| None -> begin
[]
end
| Some (t1) -> begin
(

let f_has_t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel None f t1)
in (

let a_name = (Prims.strcat "typing_" fsym)
in (

let uu____4176 = (

let uu____4177 = (

let uu____4181 = (FStar_SMTEncoding_Util.mkForall ((((f)::[])::[]), (cvars1), (f_has_t)))
in ((uu____4181), (Some (a_name)), (a_name)))
in FStar_SMTEncoding_Term.Assume (uu____4177))
in (uu____4176)::[])))
end)
in (

let interp_f = (

let a_name = (Prims.strcat "interpretation_" fsym)
in (

let uu____4189 = (

let uu____4193 = (

let uu____4194 = (

let uu____4200 = (FStar_SMTEncoding_Util.mkEq ((app), (body3)))
in ((((app)::[])::[]), ((FStar_List.append vars cvars1)), (uu____4200)))
in (FStar_SMTEncoding_Util.mkForall uu____4194))
in ((uu____4193), (Some (a_name)), (a_name)))
in FStar_SMTEncoding_Term.Assume (uu____4189)))
in (

let f_decls = (FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' (FStar_List.append ((fdecl)::typing_f) ((interp_f)::[])))))
in ((FStar_Util.smap_add env.cache tkey_hash ((fsym), (cvar_sorts), (f_decls)));
((f), (f_decls));
)))))))))
end))
end)))))))
end))
end))
end))
end)))
end)))
end)))))
end))
end
| FStar_Syntax_Syntax.Tm_let ((uu____4218, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____4219); FStar_Syntax_Syntax.lbunivs = uu____4220; FStar_Syntax_Syntax.lbtyp = uu____4221; FStar_Syntax_Syntax.lbeff = uu____4222; FStar_Syntax_Syntax.lbdef = uu____4223})::uu____4224), uu____4225) -> begin
(failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____4243; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____4245; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (uu____4261) -> begin
((FStar_Errors.diag t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts");
(

let e = (varops.fresh "let-rec")
in (

let decl_e = FStar_SMTEncoding_Term.DeclFun (((e), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let uu____4274 = (FStar_SMTEncoding_Util.mkFreeV ((e), (FStar_SMTEncoding_Term.Term_sort)))
in ((uu____4274), ((decl_e)::[])))));
)
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end);
)))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (

let uu____4316 = (encode_term e1 env)
in (match (uu____4316) with
| (ee1, decls1) -> begin
(

let uu____4323 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) e2)
in (match (uu____4323) with
| (xs, e21) -> begin
(

let uu____4337 = (FStar_List.hd xs)
in (match (uu____4337) with
| (x1, uu____4345) -> begin
(

let env' = (push_term_var env x1 ee1)
in (

let uu____4347 = (encode_body e21 env')
in (match (uu____4347) with
| (ee2, decls2) -> begin
((ee2), ((FStar_List.append decls1 decls2)))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (

let uu____4369 = (

let uu____4373 = (

let uu____4374 = ((FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown) None FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.null_bv uu____4374))
in (gen_term_var env uu____4373))
in (match (uu____4369) with
| (scrsym, scr', env1) -> begin
(

let uu____4388 = (encode_term e env1)
in (match (uu____4388) with
| (scr, decls) -> begin
(

let uu____4395 = (

let encode_branch = (fun b uu____4411 -> (match (uu____4411) with
| (else_case, decls1) -> begin
(

let uu____4422 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____4422) with
| (p, w, br) -> begin
(

let patterns = (encode_pat env1 p)
in (FStar_List.fold_right (fun uu____4452 uu____4453 -> (match (((uu____4452), (uu____4453))) with
| ((env0, pattern), (else_case1, decls2)) -> begin
(

let guard = (pattern.guard scr')
in (

let projections = (pattern.projections scr')
in (

let env2 = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env2 uu____4490 -> (match (uu____4490) with
| (x, t) -> begin
(push_term_var env2 x t)
end)) env1))
in (

let uu____4495 = (match (w) with
| None -> begin
((guard), ([]))
end
| Some (w1) -> begin
(

let uu____4510 = (encode_term w1 env2)
in (match (uu____4510) with
| (w2, decls21) -> begin
(

let uu____4518 = (

let uu____4519 = (

let uu____4522 = (

let uu____4523 = (

let uu____4526 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue)
in ((w2), (uu____4526)))
in (FStar_SMTEncoding_Util.mkEq uu____4523))
in ((guard), (uu____4522)))
in (FStar_SMTEncoding_Util.mkAnd uu____4519))
in ((uu____4518), (decls21)))
end))
end)
in (match (uu____4495) with
| (guard1, decls21) -> begin
(

let uu____4534 = (encode_br br env2)
in (match (uu____4534) with
| (br1, decls3) -> begin
(

let uu____4542 = (FStar_SMTEncoding_Util.mkITE ((guard1), (br1), (else_case1)))
in ((uu____4542), ((FStar_List.append decls2 (FStar_List.append decls21 decls3)))))
end))
end)))))
end)) patterns ((else_case), (decls1))))
end))
end))
in (FStar_List.fold_right encode_branch pats ((default_case), (decls))))
in (match (uu____4395) with
| (match_tm, decls1) -> begin
(

let uu____4554 = (FStar_SMTEncoding_Term.mkLet' (((((((scrsym), (FStar_SMTEncoding_Term.Term_sort))), (scr)))::[]), (match_tm)) FStar_Range.dummyRange)
in ((uu____4554), (decls1)))
end))
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| uu____4585 -> begin
(

let uu____4586 = (encode_one_pat env pat)
in (uu____4586)::[])
end))
and encode_one_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> ((

let uu____4598 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____4598) with
| true -> begin
(

let uu____4599 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" uu____4599))
end
| uu____4600 -> begin
()
end));
(

let uu____4601 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (uu____4601) with
| (vars, pat_term) -> begin
(

let uu____4611 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun uu____4634 v1 -> (match (uu____4634) with
| (env1, vars1) -> begin
(

let uu____4662 = (gen_term_var env1 v1)
in (match (uu____4662) with
| (xx, uu____4674, env2) -> begin
((env2), ((((v1), (((xx), (FStar_SMTEncoding_Term.Term_sort)))))::vars1))
end))
end)) ((env), ([]))))
in (match (uu____4611) with
| (env1, vars1) -> begin
(

let rec mk_guard = (fun pat1 scrutinee -> (match (pat1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (uu____4721) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_dot_term (_)) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____4729 = (

let uu____4732 = (encode_const c)
in ((scrutinee), (uu____4732)))
in (FStar_SMTEncoding_Util.mkEq uu____4729))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let is_f = (

let tc_name = (FStar_TypeChecker_Env.typ_of_datacon env1.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let uu____4751 = (FStar_TypeChecker_Env.datacons_of_typ env1.tcenv tc_name)
in (match (uu____4751) with
| (uu____4755, (uu____4756)::[]) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| uu____4758 -> begin
(mk_data_tester env1 f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
end)))
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____4779 -> (match (uu____4779) with
| (arg, uu____4785) -> begin
(

let proj = (primitive_projector_by_pos env1.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____4795 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_guard arg uu____4795)))
end))))
in (FStar_SMTEncoding_Util.mk_and_l ((is_f)::sub_term_guards))))
end))
in (

let rec mk_projections = (fun pat1 scrutinee -> (match (pat1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (uu____4814) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _)) | (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_constant (uu____4829) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let uu____4844 = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____4866 -> (match (uu____4866) with
| (arg, uu____4875) -> begin
(

let proj = (primitive_projector_by_pos env1.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____4885 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_projections arg uu____4885)))
end))))
in (FStar_All.pipe_right uu____4844 FStar_List.flatten))
end))
in (

let pat_term1 = (fun uu____4901 -> (encode_term pat_term env1))
in (

let pattern = {pat_vars = vars1; pat_term = pat_term1; guard = (mk_guard pat); projections = (mk_projections pat)}
in ((env1), (pattern))))))
end))
end));
))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (

let uu____4908 = (FStar_All.pipe_right l (FStar_List.fold_left (fun uu____4923 uu____4924 -> (match (((uu____4923), (uu____4924))) with
| ((tms, decls), (t, uu____4944)) -> begin
(

let uu____4955 = (encode_term t env)
in (match (uu____4955) with
| (t1, decls') -> begin
(((t1)::tms), ((FStar_List.append decls decls')))
end))
end)) (([]), ([]))))
in (match (uu____4908) with
| (l1, decls) -> begin
(((FStar_List.rev l1)), (decls))
end)))
and encode_function_type_as_formula : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun induction_on new_pats t env -> (

let list_elements1 = (fun e -> (

let uu____4993 = (FStar_Syntax_Util.list_elements e)
in (match (uu____4993) with
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

let uu____5011 = (

let uu____5021 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right uu____5021 FStar_Syntax_Util.head_and_args))
in (match (uu____5011) with
| (head1, args) -> begin
(

let uu____5052 = (

let uu____5060 = (

let uu____5061 = (FStar_Syntax_Util.un_uinst head1)
in uu____5061.FStar_Syntax_Syntax.n)
in ((uu____5060), (args)))
in (match (uu____5052) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((uu____5075, uu____5076))::((e, uu____5078))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpat_lid) -> begin
((e), (None))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, uu____5109))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatT_lid) -> begin
((e), (None))
end
| uu____5130 -> begin
(failwith "Unexpected pattern term")
end))
end)))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements1 p)
in (

let smt_pat_or = (fun t1 -> (

let uu____5163 = (

let uu____5173 = (FStar_Syntax_Util.unmeta t1)
in (FStar_All.pipe_right uu____5173 FStar_Syntax_Util.head_and_args))
in (match (uu____5163) with
| (head1, args) -> begin
(

let uu____5202 = (

let uu____5210 = (

let uu____5211 = (FStar_Syntax_Util.un_uinst head1)
in uu____5211.FStar_Syntax_Syntax.n)
in ((uu____5210), (args)))
in (match (uu____5202) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, uu____5224))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatOr_lid) -> begin
Some (e)
end
| uu____5244 -> begin
None
end))
end)))
in (match (elts) with
| (t1)::[] -> begin
(

let uu____5262 = (smt_pat_or t1)
in (match (uu____5262) with
| Some (e) -> begin
(

let uu____5278 = (list_elements1 e)
in (FStar_All.pipe_right uu____5278 (FStar_List.map (fun branch1 -> (

let uu____5295 = (list_elements1 branch1)
in (FStar_All.pipe_right uu____5295 (FStar_List.map one_pat)))))))
end
| uu____5309 -> begin
(

let uu____5313 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____5313)::[])
end))
end
| uu____5344 -> begin
(

let uu____5346 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____5346)::[])
end))))
in (

let uu____5377 = (

let uu____5393 = (

let uu____5394 = (FStar_Syntax_Subst.compress t)
in uu____5394.FStar_Syntax_Syntax.n)
in (match (uu____5393) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____5424 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____5424) with
| (binders1, c1) -> begin
(match (c1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____5459; FStar_Syntax_Syntax.effect_name = uu____5460; FStar_Syntax_Syntax.result_typ = uu____5461; FStar_Syntax_Syntax.effect_args = ((pre, uu____5463))::((post, uu____5465))::((pats, uu____5467))::[]; FStar_Syntax_Syntax.flags = uu____5468}) -> begin
(

let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (

let uu____5502 = (lemma_pats pats')
in ((binders1), (pre), (post), (uu____5502))))
end
| uu____5521 -> begin
(failwith "impos")
end)
end))
end
| uu____5537 -> begin
(failwith "Impos")
end))
in (match (uu____5377) with
| (binders, pre, post, patterns) -> begin
(

let uu____5581 = (encode_binders None binders env)
in (match (uu____5581) with
| (vars, guards, env1, decls, uu____5596) -> begin
(

let uu____5603 = (

let uu____5610 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch1 -> (

let uu____5641 = (

let uu____5646 = (FStar_All.pipe_right branch1 (FStar_List.map (fun uu____5662 -> (match (uu____5662) with
| (t1, uu____5669) -> begin
(encode_term t1 (

let uu___148_5672 = env1
in {bindings = uu___148_5672.bindings; depth = uu___148_5672.depth; tcenv = uu___148_5672.tcenv; warn = uu___148_5672.warn; cache = uu___148_5672.cache; nolabels = uu___148_5672.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___148_5672.encode_non_total_function_typ; current_module_name = uu___148_5672.current_module_name}))
end))))
in (FStar_All.pipe_right uu____5646 FStar_List.unzip))
in (match (uu____5641) with
| (pats, decls1) -> begin
((pats), (decls1))
end)))))
in (FStar_All.pipe_right uu____5610 FStar_List.unzip))
in (match (uu____5603) with
| (pats, decls') -> begin
(

let decls'1 = (FStar_List.flatten decls')
in (

let pats1 = (match (induction_on) with
| None -> begin
pats
end
| Some (e) -> begin
(match (vars) with
| [] -> begin
pats
end
| (l)::[] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (

let uu____5736 = (

let uu____5737 = (FStar_SMTEncoding_Util.mkFreeV l)
in (FStar_SMTEncoding_Util.mk_Precedes uu____5737 e))
in (uu____5736)::p))))
end
| uu____5738 -> begin
(

let rec aux = (fun tl1 vars1 -> (match (vars1) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (

let uu____5767 = (FStar_SMTEncoding_Util.mk_Precedes tl1 e)
in (uu____5767)::p))))
end
| ((x, FStar_SMTEncoding_Term.Term_sort))::vars2 -> begin
(

let uu____5775 = (

let uu____5776 = (FStar_SMTEncoding_Util.mkFreeV ((x), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Util.mk_LexCons uu____5776 tl1))
in (aux uu____5775 vars2))
end
| uu____5777 -> begin
pats
end))
in (

let uu____5781 = (FStar_SMTEncoding_Util.mkFreeV (("Prims.LexTop"), (FStar_SMTEncoding_Term.Term_sort)))
in (aux uu____5781 vars)))
end)
end)
in (

let env2 = (

let uu___149_5783 = env1
in {bindings = uu___149_5783.bindings; depth = uu___149_5783.depth; tcenv = uu___149_5783.tcenv; warn = uu___149_5783.warn; cache = uu___149_5783.cache; nolabels = true; use_zfuel_name = uu___149_5783.use_zfuel_name; encode_non_total_function_typ = uu___149_5783.encode_non_total_function_typ; current_module_name = uu___149_5783.current_module_name})
in (

let uu____5784 = (

let uu____5787 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula uu____5787 env2))
in (match (uu____5784) with
| (pre1, decls'') -> begin
(

let uu____5792 = (

let uu____5795 = (FStar_Syntax_Util.unmeta post)
in (encode_formula uu____5795 env2))
in (match (uu____5792) with
| (post1, decls''') -> begin
(

let decls1 = (FStar_List.append decls (FStar_List.append (FStar_List.flatten decls'1) (FStar_List.append decls'' decls''')))
in (

let uu____5802 = (

let uu____5803 = (

let uu____5809 = (

let uu____5810 = (

let uu____5813 = (FStar_SMTEncoding_Util.mk_and_l ((pre1)::guards))
in ((uu____5813), (post1)))
in (FStar_SMTEncoding_Util.mkImp uu____5810))
in ((pats1), (vars), (uu____5809)))
in (FStar_SMTEncoding_Util.mkForall uu____5803))
in ((uu____5802), (decls1))))
end))
end)))))
end))
end))
end))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (

let debug1 = (fun phi1 -> (

let uu____5826 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____5826) with
| true -> begin
(

let uu____5827 = (FStar_Syntax_Print.tag_of_term phi1)
in (

let uu____5828 = (FStar_Syntax_Print.term_to_string phi1)
in (FStar_Util.print2 "Formula (%s)  %s\n" uu____5827 uu____5828)))
end
| uu____5829 -> begin
()
end)))
in (

let enc = (fun f r l -> (

let uu____5855 = (FStar_Util.fold_map (fun decls x -> (

let uu____5868 = (encode_term (Prims.fst x) env)
in (match (uu____5868) with
| (t, decls') -> begin
(((FStar_List.append decls decls')), (t))
end))) [] l)
in (match (uu____5855) with
| (decls, args) -> begin
(

let uu____5885 = (

let uu___150_5886 = (f args)
in {FStar_SMTEncoding_Term.tm = uu___150_5886.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___150_5886.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____5885), (decls)))
end)))
in (

let const_op = (fun f r uu____5905 -> (

let uu____5908 = (f r)
in ((uu____5908), ([]))))
in (

let un_op = (fun f l -> (

let uu____5924 = (FStar_List.hd l)
in (FStar_All.pipe_left f uu____5924)))
in (

let bin_op = (fun f uu___122_5937 -> (match (uu___122_5937) with
| (t1)::(t2)::[] -> begin
(f ((t1), (t2)))
end
| uu____5945 -> begin
(failwith "Impossible")
end))
in (

let enc_prop_c = (fun f r l -> (

let uu____5972 = (FStar_Util.fold_map (fun decls uu____5981 -> (match (uu____5981) with
| (t, uu____5989) -> begin
(

let uu____5990 = (encode_formula t env)
in (match (uu____5990) with
| (phi1, decls') -> begin
(((FStar_List.append decls decls')), (phi1))
end))
end)) [] l)
in (match (uu____5972) with
| (decls, phis) -> begin
(

let uu____6007 = (

let uu___151_6008 = (f phis)
in {FStar_SMTEncoding_Term.tm = uu___151_6008.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___151_6008.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____6007), (decls)))
end)))
in (

let eq_op = (fun r uu___123_6024 -> (match (uu___123_6024) with
| ((_)::(e1)::(e2)::[]) | ((_)::(_)::(e1)::(e2)::[]) -> begin
(

let uu____6084 = (enc (bin_op FStar_SMTEncoding_Util.mkEq))
in (uu____6084 r ((e1)::(e2)::[])))
end
| l -> begin
(

let uu____6104 = (enc (bin_op FStar_SMTEncoding_Util.mkEq))
in (uu____6104 r l))
end))
in (

let mk_imp1 = (fun r uu___124_6123 -> (match (uu___124_6123) with
| ((lhs, uu____6127))::((rhs, uu____6129))::[] -> begin
(

let uu____6150 = (encode_formula rhs env)
in (match (uu____6150) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____6159) -> begin
((l1), (decls1))
end
| uu____6162 -> begin
(

let uu____6163 = (encode_formula lhs env)
in (match (uu____6163) with
| (l2, decls2) -> begin
(

let uu____6170 = (FStar_SMTEncoding_Term.mkImp ((l2), (l1)) r)
in ((uu____6170), ((FStar_List.append decls1 decls2))))
end))
end)
end))
end
| uu____6172 -> begin
(failwith "impossible")
end))
in (

let mk_ite = (fun r uu___125_6187 -> (match (uu___125_6187) with
| ((guard, uu____6191))::((_then, uu____6193))::((_else, uu____6195))::[] -> begin
(

let uu____6224 = (encode_formula guard env)
in (match (uu____6224) with
| (g, decls1) -> begin
(

let uu____6231 = (encode_formula _then env)
in (match (uu____6231) with
| (t, decls2) -> begin
(

let uu____6238 = (encode_formula _else env)
in (match (uu____6238) with
| (e, decls3) -> begin
(

let res = (FStar_SMTEncoding_Term.mkITE ((g), (t), (e)) r)
in ((res), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end))
end))
end
| uu____6247 -> begin
(failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (

let uu____6266 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f uu____6266)))
in (

let connectives = (

let uu____6278 = (

let uu____6287 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd))
in ((FStar_Syntax_Const.and_lid), (uu____6287)))
in (

let uu____6300 = (

let uu____6310 = (

let uu____6319 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr))
in ((FStar_Syntax_Const.or_lid), (uu____6319)))
in (

let uu____6332 = (

let uu____6342 = (

let uu____6352 = (

let uu____6361 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff))
in ((FStar_Syntax_Const.iff_lid), (uu____6361)))
in (

let uu____6374 = (

let uu____6384 = (

let uu____6394 = (

let uu____6403 = (enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot))
in ((FStar_Syntax_Const.not_lid), (uu____6403)))
in (uu____6394)::(((FStar_Syntax_Const.eq2_lid), (eq_op)))::(((FStar_Syntax_Const.eq3_lid), (eq_op)))::(((FStar_Syntax_Const.true_lid), ((const_op FStar_SMTEncoding_Term.mkTrue))))::(((FStar_Syntax_Const.false_lid), ((const_op FStar_SMTEncoding_Term.mkFalse))))::[])
in (((FStar_Syntax_Const.ite_lid), (mk_ite)))::uu____6384)
in (uu____6352)::uu____6374))
in (((FStar_Syntax_Const.imp_lid), (mk_imp1)))::uu____6342)
in (uu____6310)::uu____6332))
in (uu____6278)::uu____6300))
in (

let rec fallback = (fun phi1 -> (match (phi1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(

let uu____6565 = (encode_formula phi' env)
in (match (uu____6565) with
| (phi2, decls) -> begin
(

let uu____6572 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled (((phi2), (msg), (r)))) r)
in ((uu____6572), (decls)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (uu____6573) -> begin
(

let uu____6578 = (FStar_Syntax_Util.unmeta phi1)
in (encode_formula uu____6578 env))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(

let uu____6607 = (encode_match e pats FStar_SMTEncoding_Util.mkFalse env encode_formula)
in (match (uu____6607) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____6615; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____6617; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let uu____6633 = (encode_let x t1 e1 e2 env encode_formula)
in (match (uu____6633) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let head2 = (FStar_Syntax_Util.un_uinst head1)
in (match (((head2.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____6665)::((x, uu____6667))::((t, uu____6669))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.has_type_lid) -> begin
(

let uu____6703 = (encode_term x env)
in (match (uu____6703) with
| (x1, decls) -> begin
(

let uu____6710 = (encode_term t env)
in (match (uu____6710) with
| (t1, decls') -> begin
(

let uu____6717 = (FStar_SMTEncoding_Term.mk_HasType x1 t1)
in ((uu____6717), ((FStar_List.append decls decls'))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((r, uu____6721))::((msg, uu____6723))::((phi2, uu____6725))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.labeled_lid) -> begin
(

let uu____6759 = (

let uu____6762 = (

let uu____6763 = (FStar_Syntax_Subst.compress r)
in uu____6763.FStar_Syntax_Syntax.n)
in (

let uu____6766 = (

let uu____6767 = (FStar_Syntax_Subst.compress msg)
in uu____6767.FStar_Syntax_Syntax.n)
in ((uu____6762), (uu____6766))))
in (match (uu____6759) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____6774))) -> begin
(

let phi3 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((phi2), (FStar_Syntax_Syntax.Meta_labeled ((((FStar_Util.string_of_unicode s)), (r1), (false)))))))) None r1)
in (fallback phi3))
end
| uu____6790 -> begin
(fallback phi2)
end))
end
| uu____6793 when (head_redex env head2) -> begin
(

let uu____6801 = (whnf env phi1)
in (encode_formula uu____6801 env))
end
| uu____6802 -> begin
(

let uu____6810 = (encode_term phi1 env)
in (match (uu____6810) with
| (tt, decls) -> begin
(

let uu____6817 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___152_6818 = tt
in {FStar_SMTEncoding_Term.tm = uu___152_6818.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___152_6818.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi1.FStar_Syntax_Syntax.pos}))
in ((uu____6817), (decls)))
end))
end))
end
| uu____6821 -> begin
(

let uu____6822 = (encode_term phi1 env)
in (match (uu____6822) with
| (tt, decls) -> begin
(

let uu____6829 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___153_6830 = tt
in {FStar_SMTEncoding_Term.tm = uu___153_6830.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___153_6830.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi1.FStar_Syntax_Syntax.pos}))
in ((uu____6829), (decls)))
end))
end))
in (

let encode_q_body = (fun env1 bs ps body -> (

let uu____6857 = (encode_binders None bs env1)
in (match (uu____6857) with
| (vars, guards, env2, decls, uu____6879) -> begin
(

let uu____6886 = (

let uu____6893 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let uu____6916 = (

let uu____6921 = (FStar_All.pipe_right p (FStar_List.map (fun uu____6935 -> (match (uu____6935) with
| (t, uu____6941) -> begin
(encode_term t (

let uu___154_6942 = env2
in {bindings = uu___154_6942.bindings; depth = uu___154_6942.depth; tcenv = uu___154_6942.tcenv; warn = uu___154_6942.warn; cache = uu___154_6942.cache; nolabels = uu___154_6942.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___154_6942.encode_non_total_function_typ; current_module_name = uu___154_6942.current_module_name}))
end))))
in (FStar_All.pipe_right uu____6921 FStar_List.unzip))
in (match (uu____6916) with
| (p1, decls1) -> begin
((p1), ((FStar_List.flatten decls1)))
end)))))
in (FStar_All.pipe_right uu____6893 FStar_List.unzip))
in (match (uu____6886) with
| (pats, decls') -> begin
(

let uu____6994 = (encode_formula body env2)
in (match (uu____6994) with
| (body1, decls'') -> begin
(

let guards1 = (match (pats) with
| (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (gf), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____7013; FStar_SMTEncoding_Term.rng = uu____7014})::[])::[] when ((FStar_Ident.text_of_lid FStar_Syntax_Const.guard_free) = gf) -> begin
[]
end
| uu____7022 -> begin
guards
end)
in (

let uu____7025 = (FStar_SMTEncoding_Util.mk_and_l guards1)
in ((vars), (pats), (uu____7025), (body1), ((FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') decls''))))))
end))
end))
end)))
in ((debug1 phi);
(

let phi1 = (FStar_Syntax_Util.unascribe phi)
in (

let check_pattern_vars = (fun vars pats -> (

let pats1 = (FStar_All.pipe_right pats (FStar_List.map (fun uu____7059 -> (match (uu____7059) with
| (x, uu____7063) -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x)
end))))
in (match (pats1) with
| [] -> begin
()
end
| (hd1)::tl1 -> begin
(

let pat_vars = (

let uu____7069 = (FStar_Syntax_Free.names hd1)
in (FStar_List.fold_left (fun out x -> (

let uu____7075 = (FStar_Syntax_Free.names x)
in (FStar_Util.set_union out uu____7075))) uu____7069 tl1))
in (

let uu____7077 = (FStar_All.pipe_right vars (FStar_Util.find_opt (fun uu____7089 -> (match (uu____7089) with
| (b, uu____7093) -> begin
(

let uu____7094 = (FStar_Util.set_mem b pat_vars)
in (not (uu____7094)))
end))))
in (match (uu____7077) with
| None -> begin
()
end
| Some (x, uu____7098) -> begin
(

let pos = (FStar_List.fold_left (fun out t -> (FStar_Range.union_ranges out t.FStar_Syntax_Syntax.pos)) hd1.FStar_Syntax_Syntax.pos tl1)
in (

let uu____7108 = (

let uu____7109 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "SMT pattern misses at least one bound variable: %s" uu____7109))
in (FStar_Errors.warn pos uu____7108)))
end)))
end)))
in (

let uu____7110 = (FStar_Syntax_Util.destruct_typ_as_formula phi1)
in (match (uu____7110) with
| None -> begin
(fallback phi1)
end
| Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(

let uu____7116 = (FStar_All.pipe_right connectives (FStar_List.tryFind (fun uu____7152 -> (match (uu____7152) with
| (l, uu____7162) -> begin
(FStar_Ident.lid_equals op l)
end))))
in (match (uu____7116) with
| None -> begin
(fallback phi1)
end
| Some (uu____7185, f) -> begin
(f phi1.FStar_Syntax_Syntax.pos arms)
end))
end
| Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____7214 = (encode_q_body env vars pats body)
in (match (uu____7214) with
| (vars1, pats1, guard, body1, decls) -> begin
(

let tm = (

let uu____7240 = (

let uu____7246 = (FStar_SMTEncoding_Util.mkImp ((guard), (body1)))
in ((pats1), (vars1), (uu____7246)))
in (FStar_SMTEncoding_Term.mkForall uu____7240 phi1.FStar_Syntax_Syntax.pos))
in ((tm), (decls)))
end));
)
end
| Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____7258 = (encode_q_body env vars pats body)
in (match (uu____7258) with
| (vars1, pats1, guard, body1, decls) -> begin
(

let uu____7283 = (

let uu____7284 = (

let uu____7290 = (FStar_SMTEncoding_Util.mkAnd ((guard), (body1)))
in ((pats1), (vars1), (uu____7290)))
in (FStar_SMTEncoding_Term.mkExists uu____7284 phi1.FStar_Syntax_Syntax.pos))
in ((uu____7283), (decls)))
end));
)
end))));
)))))))))))))))

type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list); is : FStar_Ident.lident  ->  Prims.bool}


let prims : prims_t = (

let uu____7339 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____7339) with
| (asym, a) -> begin
(

let uu____7344 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____7344) with
| (xsym, x) -> begin
(

let uu____7349 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____7349) with
| (ysym, y) -> begin
(

let quant = (fun vars body x1 -> (

let xname_decl = (

let uu____7379 = (

let uu____7385 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in ((x1), (uu____7385), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (uu____7379))
in (

let xtok = (Prims.strcat x1 "@tok")
in (

let xtok_decl = FStar_SMTEncoding_Term.DeclFun (((xtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let xapp = (

let uu____7400 = (

let uu____7404 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((x1), (uu____7404)))
in (FStar_SMTEncoding_Util.mkApp uu____7400))
in (

let xtok1 = (FStar_SMTEncoding_Util.mkApp ((xtok), ([])))
in (

let xtok_app = (mk_Apply xtok1 vars)
in (

let uu____7412 = (

let uu____7414 = (

let uu____7416 = (

let uu____7418 = (

let uu____7419 = (

let uu____7423 = (

let uu____7424 = (

let uu____7430 = (FStar_SMTEncoding_Util.mkEq ((xapp), (body)))
in ((((xapp)::[])::[]), (vars), (uu____7430)))
in (FStar_SMTEncoding_Util.mkForall uu____7424))
in ((uu____7423), (None), ((Prims.strcat "primitive_" x1))))
in FStar_SMTEncoding_Term.Assume (uu____7419))
in (

let uu____7439 = (

let uu____7441 = (

let uu____7442 = (

let uu____7446 = (

let uu____7447 = (

let uu____7453 = (FStar_SMTEncoding_Util.mkEq ((xtok_app), (xapp)))
in ((((xtok_app)::[])::[]), (vars), (uu____7453)))
in (FStar_SMTEncoding_Util.mkForall uu____7447))
in ((uu____7446), (Some ("Name-token correspondence")), ((Prims.strcat "token_correspondence_" x1))))
in FStar_SMTEncoding_Term.Assume (uu____7442))
in (uu____7441)::[])
in (uu____7418)::uu____7439))
in (xtok_decl)::uu____7416)
in (xname_decl)::uu____7414)
in ((xtok1), (uu____7412))))))))))
in (

let axy = (((asym), (FStar_SMTEncoding_Term.Term_sort)))::(((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let xy = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let qx = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let prims1 = (

let uu____7502 = (

let uu____7510 = (

let uu____7516 = (

let uu____7517 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7517))
in (quant axy uu____7516))
in ((FStar_Syntax_Const.op_Eq), (uu____7510)))
in (

let uu____7523 = (

let uu____7532 = (

let uu____7540 = (

let uu____7546 = (

let uu____7547 = (

let uu____7548 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_SMTEncoding_Util.mkNot uu____7548))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7547))
in (quant axy uu____7546))
in ((FStar_Syntax_Const.op_notEq), (uu____7540)))
in (

let uu____7554 = (

let uu____7563 = (

let uu____7571 = (

let uu____7577 = (

let uu____7578 = (

let uu____7579 = (

let uu____7582 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7583 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7582), (uu____7583))))
in (FStar_SMTEncoding_Util.mkLT uu____7579))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7578))
in (quant xy uu____7577))
in ((FStar_Syntax_Const.op_LT), (uu____7571)))
in (

let uu____7589 = (

let uu____7598 = (

let uu____7606 = (

let uu____7612 = (

let uu____7613 = (

let uu____7614 = (

let uu____7617 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7618 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7617), (uu____7618))))
in (FStar_SMTEncoding_Util.mkLTE uu____7614))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7613))
in (quant xy uu____7612))
in ((FStar_Syntax_Const.op_LTE), (uu____7606)))
in (

let uu____7624 = (

let uu____7633 = (

let uu____7641 = (

let uu____7647 = (

let uu____7648 = (

let uu____7649 = (

let uu____7652 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7653 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7652), (uu____7653))))
in (FStar_SMTEncoding_Util.mkGT uu____7649))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7648))
in (quant xy uu____7647))
in ((FStar_Syntax_Const.op_GT), (uu____7641)))
in (

let uu____7659 = (

let uu____7668 = (

let uu____7676 = (

let uu____7682 = (

let uu____7683 = (

let uu____7684 = (

let uu____7687 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7688 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7687), (uu____7688))))
in (FStar_SMTEncoding_Util.mkGTE uu____7684))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7683))
in (quant xy uu____7682))
in ((FStar_Syntax_Const.op_GTE), (uu____7676)))
in (

let uu____7694 = (

let uu____7703 = (

let uu____7711 = (

let uu____7717 = (

let uu____7718 = (

let uu____7719 = (

let uu____7722 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7723 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7722), (uu____7723))))
in (FStar_SMTEncoding_Util.mkSub uu____7719))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7718))
in (quant xy uu____7717))
in ((FStar_Syntax_Const.op_Subtraction), (uu____7711)))
in (

let uu____7729 = (

let uu____7738 = (

let uu____7746 = (

let uu____7752 = (

let uu____7753 = (

let uu____7754 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Util.mkMinus uu____7754))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7753))
in (quant qx uu____7752))
in ((FStar_Syntax_Const.op_Minus), (uu____7746)))
in (

let uu____7760 = (

let uu____7769 = (

let uu____7777 = (

let uu____7783 = (

let uu____7784 = (

let uu____7785 = (

let uu____7788 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7789 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7788), (uu____7789))))
in (FStar_SMTEncoding_Util.mkAdd uu____7785))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7784))
in (quant xy uu____7783))
in ((FStar_Syntax_Const.op_Addition), (uu____7777)))
in (

let uu____7795 = (

let uu____7804 = (

let uu____7812 = (

let uu____7818 = (

let uu____7819 = (

let uu____7820 = (

let uu____7823 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7824 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7823), (uu____7824))))
in (FStar_SMTEncoding_Util.mkMul uu____7820))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7819))
in (quant xy uu____7818))
in ((FStar_Syntax_Const.op_Multiply), (uu____7812)))
in (

let uu____7830 = (

let uu____7839 = (

let uu____7847 = (

let uu____7853 = (

let uu____7854 = (

let uu____7855 = (

let uu____7858 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7859 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7858), (uu____7859))))
in (FStar_SMTEncoding_Util.mkDiv uu____7855))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7854))
in (quant xy uu____7853))
in ((FStar_Syntax_Const.op_Division), (uu____7847)))
in (

let uu____7865 = (

let uu____7874 = (

let uu____7882 = (

let uu____7888 = (

let uu____7889 = (

let uu____7890 = (

let uu____7893 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7894 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7893), (uu____7894))))
in (FStar_SMTEncoding_Util.mkMod uu____7890))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7889))
in (quant xy uu____7888))
in ((FStar_Syntax_Const.op_Modulus), (uu____7882)))
in (

let uu____7900 = (

let uu____7909 = (

let uu____7917 = (

let uu____7923 = (

let uu____7924 = (

let uu____7925 = (

let uu____7928 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____7929 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____7928), (uu____7929))))
in (FStar_SMTEncoding_Util.mkAnd uu____7925))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7924))
in (quant xy uu____7923))
in ((FStar_Syntax_Const.op_And), (uu____7917)))
in (

let uu____7935 = (

let uu____7944 = (

let uu____7952 = (

let uu____7958 = (

let uu____7959 = (

let uu____7960 = (

let uu____7963 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____7964 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____7963), (uu____7964))))
in (FStar_SMTEncoding_Util.mkOr uu____7960))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7959))
in (quant xy uu____7958))
in ((FStar_Syntax_Const.op_Or), (uu____7952)))
in (

let uu____7970 = (

let uu____7979 = (

let uu____7987 = (

let uu____7993 = (

let uu____7994 = (

let uu____7995 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Util.mkNot uu____7995))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7994))
in (quant qx uu____7993))
in ((FStar_Syntax_Const.op_Negation), (uu____7987)))
in (uu____7979)::[])
in (uu____7944)::uu____7970))
in (uu____7909)::uu____7935))
in (uu____7874)::uu____7900))
in (uu____7839)::uu____7865))
in (uu____7804)::uu____7830))
in (uu____7769)::uu____7795))
in (uu____7738)::uu____7760))
in (uu____7703)::uu____7729))
in (uu____7668)::uu____7694))
in (uu____7633)::uu____7659))
in (uu____7598)::uu____7624))
in (uu____7563)::uu____7589))
in (uu____7532)::uu____7554))
in (uu____7502)::uu____7523))
in (

let mk1 = (fun l v1 -> (

let uu____8123 = (

let uu____8128 = (FStar_All.pipe_right prims1 (FStar_List.find (fun uu____8160 -> (match (uu____8160) with
| (l', uu____8169) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right uu____8128 (FStar_Option.map (fun uu____8202 -> (match (uu____8202) with
| (uu____8213, b) -> begin
(b v1)
end)))))
in (FStar_All.pipe_right uu____8123 FStar_Option.get)))
in (

let is = (fun l -> (FStar_All.pipe_right prims1 (FStar_Util.for_some (fun uu____8254 -> (match (uu____8254) with
| (l', uu____8263) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk1; is = is})))))))
end))
end))
end))


let pretype_axiom : env_t  ->  FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun env tapp vars -> (

let uu____8289 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____8289) with
| (xxsym, xx) -> begin
(

let uu____8294 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____8294) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let tapp_hash = (FStar_SMTEncoding_Term.hash_of_term tapp)
in (

let module_name = env.current_module_name
in (

let uu____8302 = (

let uu____8306 = (

let uu____8307 = (

let uu____8313 = (

let uu____8314 = (

let uu____8317 = (

let uu____8318 = (

let uu____8321 = (FStar_SMTEncoding_Util.mkApp (("PreType"), ((xx)::[])))
in ((tapp), (uu____8321)))
in (FStar_SMTEncoding_Util.mkEq uu____8318))
in ((xx_has_type), (uu____8317)))
in (FStar_SMTEncoding_Util.mkImp uu____8314))
in ((((xx_has_type)::[])::[]), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars), (uu____8313)))
in (FStar_SMTEncoding_Util.mkForall uu____8307))
in (

let uu____8334 = (

let uu____8335 = (

let uu____8336 = (

let uu____8337 = (FStar_Util.digest_of_string tapp_hash)
in (Prims.strcat "_pretyping_" uu____8337))
in (Prims.strcat module_name uu____8336))
in (varops.mk_unique uu____8335))
in ((uu____8306), (Some ("pretyping")), (uu____8334))))
in FStar_SMTEncoding_Term.Assume (uu____8302)))))
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

let uu____8367 = (

let uu____8368 = (

let uu____8372 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in ((uu____8372), (Some ("unit typing")), ("unit_typing")))
in FStar_SMTEncoding_Term.Assume (uu____8368))
in (

let uu____8374 = (

let uu____8376 = (

let uu____8377 = (

let uu____8381 = (

let uu____8382 = (

let uu____8388 = (

let uu____8389 = (

let uu____8392 = (FStar_SMTEncoding_Util.mkEq ((x), (FStar_SMTEncoding_Term.mk_Term_unit)))
in ((typing_pred), (uu____8392)))
in (FStar_SMTEncoding_Util.mkImp uu____8389))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____8388)))
in (mkForall_fuel uu____8382))
in ((uu____8381), (Some ("unit inversion")), ("unit_inversion")))
in FStar_SMTEncoding_Term.Assume (uu____8377))
in (uu____8376)::[])
in (uu____8367)::uu____8374))))
in (

let mk_bool = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Bool_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____8420 = (

let uu____8421 = (

let uu____8425 = (

let uu____8426 = (

let uu____8432 = (

let uu____8435 = (

let uu____8437 = (FStar_SMTEncoding_Term.boxBool b)
in (uu____8437)::[])
in (uu____8435)::[])
in (

let uu____8440 = (

let uu____8441 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType uu____8441 tt))
in ((uu____8432), ((bb)::[]), (uu____8440))))
in (FStar_SMTEncoding_Util.mkForall uu____8426))
in ((uu____8425), (Some ("bool typing")), ("bool_typing")))
in FStar_SMTEncoding_Term.Assume (uu____8421))
in (

let uu____8452 = (

let uu____8454 = (

let uu____8455 = (

let uu____8459 = (

let uu____8460 = (

let uu____8466 = (

let uu____8467 = (

let uu____8470 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in ((typing_pred), (uu____8470)))
in (FStar_SMTEncoding_Util.mkImp uu____8467))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____8466)))
in (mkForall_fuel uu____8460))
in ((uu____8459), (Some ("bool inversion")), ("bool_inversion")))
in FStar_SMTEncoding_Term.Assume (uu____8455))
in (uu____8454)::[])
in (uu____8420)::uu____8452))))))
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

let uu____8504 = (

let uu____8505 = (

let uu____8509 = (

let uu____8511 = (

let uu____8513 = (

let uu____8515 = (FStar_SMTEncoding_Term.boxInt a)
in (

let uu____8516 = (

let uu____8518 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____8518)::[])
in (uu____8515)::uu____8516))
in (tt)::uu____8513)
in (tt)::uu____8511)
in (("Prims.Precedes"), (uu____8509)))
in (FStar_SMTEncoding_Util.mkApp uu____8505))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8504))
in (

let precedes_y_x = (

let uu____8521 = (FStar_SMTEncoding_Util.mkApp (("Precedes"), ((y)::(x)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8521))
in (

let uu____8523 = (

let uu____8524 = (

let uu____8528 = (

let uu____8529 = (

let uu____8535 = (

let uu____8538 = (

let uu____8540 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____8540)::[])
in (uu____8538)::[])
in (

let uu____8543 = (

let uu____8544 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType uu____8544 tt))
in ((uu____8535), ((bb)::[]), (uu____8543))))
in (FStar_SMTEncoding_Util.mkForall uu____8529))
in ((uu____8528), (Some ("int typing")), ("int_typing")))
in FStar_SMTEncoding_Term.Assume (uu____8524))
in (

let uu____8555 = (

let uu____8557 = (

let uu____8558 = (

let uu____8562 = (

let uu____8563 = (

let uu____8569 = (

let uu____8570 = (

let uu____8573 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in ((typing_pred), (uu____8573)))
in (FStar_SMTEncoding_Util.mkImp uu____8570))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____8569)))
in (mkForall_fuel uu____8563))
in ((uu____8562), (Some ("int inversion")), ("int_inversion")))
in FStar_SMTEncoding_Term.Assume (uu____8558))
in (

let uu____8586 = (

let uu____8588 = (

let uu____8589 = (

let uu____8593 = (

let uu____8594 = (

let uu____8600 = (

let uu____8601 = (

let uu____8604 = (

let uu____8605 = (

let uu____8607 = (

let uu____8609 = (

let uu____8611 = (

let uu____8612 = (

let uu____8615 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____8616 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____8615), (uu____8616))))
in (FStar_SMTEncoding_Util.mkGT uu____8612))
in (

let uu____8617 = (

let uu____8619 = (

let uu____8620 = (

let uu____8623 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____8624 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____8623), (uu____8624))))
in (FStar_SMTEncoding_Util.mkGTE uu____8620))
in (

let uu____8625 = (

let uu____8627 = (

let uu____8628 = (

let uu____8631 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____8632 = (FStar_SMTEncoding_Term.unboxInt x)
in ((uu____8631), (uu____8632))))
in (FStar_SMTEncoding_Util.mkLT uu____8628))
in (uu____8627)::[])
in (uu____8619)::uu____8625))
in (uu____8611)::uu____8617))
in (typing_pred_y)::uu____8609)
in (typing_pred)::uu____8607)
in (FStar_SMTEncoding_Util.mk_and_l uu____8605))
in ((uu____8604), (precedes_y_x)))
in (FStar_SMTEncoding_Util.mkImp uu____8601))
in ((((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[]), ((xx)::(yy)::[]), (uu____8600)))
in (mkForall_fuel uu____8594))
in ((uu____8593), (Some ("well-founded ordering on nat (alt)")), ("well-founded-ordering-on-nat")))
in FStar_SMTEncoding_Term.Assume (uu____8589))
in (uu____8588)::[])
in (uu____8557)::uu____8586))
in (uu____8523)::uu____8555)))))))))))
in (

let mk_str = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.String_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____8662 = (

let uu____8663 = (

let uu____8667 = (

let uu____8668 = (

let uu____8674 = (

let uu____8677 = (

let uu____8679 = (FStar_SMTEncoding_Term.boxString b)
in (uu____8679)::[])
in (uu____8677)::[])
in (

let uu____8682 = (

let uu____8683 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType uu____8683 tt))
in ((uu____8674), ((bb)::[]), (uu____8682))))
in (FStar_SMTEncoding_Util.mkForall uu____8668))
in ((uu____8667), (Some ("string typing")), ("string_typing")))
in FStar_SMTEncoding_Term.Assume (uu____8663))
in (

let uu____8694 = (

let uu____8696 = (

let uu____8697 = (

let uu____8701 = (

let uu____8702 = (

let uu____8708 = (

let uu____8709 = (

let uu____8712 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in ((typing_pred), (uu____8712)))
in (FStar_SMTEncoding_Util.mkImp uu____8709))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____8708)))
in (mkForall_fuel uu____8702))
in ((uu____8701), (Some ("string inversion")), ("string_inversion")))
in FStar_SMTEncoding_Term.Assume (uu____8697))
in (uu____8696)::[])
in (uu____8662)::uu____8694))))))
in (

let mk_ref1 = (fun env reft_name uu____8734 -> (

let r = (("r"), (FStar_SMTEncoding_Term.Ref_sort))
in (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let refa = (

let uu____8745 = (

let uu____8749 = (

let uu____8751 = (FStar_SMTEncoding_Util.mkFreeV aa)
in (uu____8751)::[])
in ((reft_name), (uu____8749)))
in (FStar_SMTEncoding_Util.mkApp uu____8745))
in (

let refb = (

let uu____8754 = (

let uu____8758 = (

let uu____8760 = (FStar_SMTEncoding_Util.mkFreeV bb)
in (uu____8760)::[])
in ((reft_name), (uu____8758)))
in (FStar_SMTEncoding_Util.mkApp uu____8754))
in (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (

let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (

let uu____8764 = (

let uu____8765 = (

let uu____8769 = (

let uu____8770 = (

let uu____8776 = (

let uu____8777 = (

let uu____8780 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in ((typing_pred), (uu____8780)))
in (FStar_SMTEncoding_Util.mkImp uu____8777))
in ((((typing_pred)::[])::[]), ((xx)::(aa)::[]), (uu____8776)))
in (mkForall_fuel uu____8770))
in ((uu____8769), (Some ("ref inversion")), ("ref_inversion")))
in FStar_SMTEncoding_Term.Assume (uu____8765))
in (

let uu____8795 = (

let uu____8797 = (

let uu____8798 = (

let uu____8802 = (

let uu____8803 = (

let uu____8809 = (

let uu____8810 = (

let uu____8813 = (FStar_SMTEncoding_Util.mkAnd ((typing_pred), (typing_pred_b)))
in (

let uu____8814 = (

let uu____8815 = (

let uu____8818 = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let uu____8819 = (FStar_SMTEncoding_Util.mkFreeV bb)
in ((uu____8818), (uu____8819))))
in (FStar_SMTEncoding_Util.mkEq uu____8815))
in ((uu____8813), (uu____8814))))
in (FStar_SMTEncoding_Util.mkImp uu____8810))
in ((((typing_pred)::(typing_pred_b)::[])::[]), ((xx)::(aa)::(bb)::[]), (uu____8809)))
in (mkForall_fuel' (Prims.parse_int "2") uu____8803))
in ((uu____8802), (Some ("ref typing is injective")), ("ref_injectivity")))
in FStar_SMTEncoding_Term.Assume (uu____8798))
in (uu____8797)::[])
in (uu____8764)::uu____8795))))))))))
in (

let mk_true_interp = (fun env nm true_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((true_tm)::[])))
in (FStar_SMTEncoding_Term.Assume (((valid), (Some ("True interpretation")), ("true_interp"))))::[]))
in (

let mk_false_interp = (fun env nm false_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((false_tm)::[])))
in (

let uu____8861 = (

let uu____8862 = (

let uu____8866 = (FStar_SMTEncoding_Util.mkIff ((FStar_SMTEncoding_Util.mkFalse), (valid)))
in ((uu____8866), (Some ("False interpretation")), ("false_interp")))
in FStar_SMTEncoding_Term.Assume (uu____8862))
in (uu____8861)::[])))
in (

let mk_and_interp = (fun env conj uu____8877 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let valid = (

let uu____8887 = (

let uu____8891 = (

let uu____8893 = (FStar_SMTEncoding_Util.mkApp ((conj), ((a)::(b)::[])))
in (uu____8893)::[])
in (("Valid"), (uu____8891)))
in (FStar_SMTEncoding_Util.mkApp uu____8887))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____8900 = (

let uu____8901 = (

let uu____8905 = (

let uu____8906 = (

let uu____8912 = (

let uu____8913 = (

let uu____8916 = (FStar_SMTEncoding_Util.mkAnd ((valid_a), (valid_b)))
in ((uu____8916), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____8913))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____8912)))
in (FStar_SMTEncoding_Util.mkForall uu____8906))
in ((uu____8905), (Some ("/\\ interpretation")), ("l_and-interp")))
in FStar_SMTEncoding_Term.Assume (uu____8901))
in (uu____8900)::[])))))))))
in (

let mk_or_interp = (fun env disj uu____8940 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let valid = (

let uu____8950 = (

let uu____8954 = (

let uu____8956 = (FStar_SMTEncoding_Util.mkApp ((disj), ((a)::(b)::[])))
in (uu____8956)::[])
in (("Valid"), (uu____8954)))
in (FStar_SMTEncoding_Util.mkApp uu____8950))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____8963 = (

let uu____8964 = (

let uu____8968 = (

let uu____8969 = (

let uu____8975 = (

let uu____8976 = (

let uu____8979 = (FStar_SMTEncoding_Util.mkOr ((valid_a), (valid_b)))
in ((uu____8979), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____8976))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____8975)))
in (FStar_SMTEncoding_Util.mkForall uu____8969))
in ((uu____8968), (Some ("\\/ interpretation")), ("l_or-interp")))
in FStar_SMTEncoding_Term.Assume (uu____8964))
in (uu____8963)::[])))))))))
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

let valid = (

let uu____9017 = (

let uu____9021 = (

let uu____9023 = (FStar_SMTEncoding_Util.mkApp ((eq2), ((a)::(x1)::(y1)::[])))
in (uu____9023)::[])
in (("Valid"), (uu____9021)))
in (FStar_SMTEncoding_Util.mkApp uu____9017))
in (

let uu____9026 = (

let uu____9027 = (

let uu____9031 = (

let uu____9032 = (

let uu____9038 = (

let uu____9039 = (

let uu____9042 = (FStar_SMTEncoding_Util.mkEq ((x1), (y1)))
in ((uu____9042), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9039))
in ((((valid)::[])::[]), ((aa)::(xx1)::(yy1)::[]), (uu____9038)))
in (FStar_SMTEncoding_Util.mkForall uu____9032))
in ((uu____9031), (Some ("Eq2 interpretation")), ("eq2-interp")))
in FStar_SMTEncoding_Term.Assume (uu____9027))
in (uu____9026)::[])))))))))
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

let valid = (

let uu____9086 = (

let uu____9090 = (

let uu____9092 = (FStar_SMTEncoding_Util.mkApp ((eq3), ((a)::(b)::(x1)::(y1)::[])))
in (uu____9092)::[])
in (("Valid"), (uu____9090)))
in (FStar_SMTEncoding_Util.mkApp uu____9086))
in (

let uu____9095 = (

let uu____9096 = (

let uu____9100 = (

let uu____9101 = (

let uu____9107 = (

let uu____9108 = (

let uu____9111 = (FStar_SMTEncoding_Util.mkEq ((x1), (y1)))
in ((uu____9111), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9108))
in ((((valid)::[])::[]), ((aa)::(bb)::(xx1)::(yy1)::[]), (uu____9107)))
in (FStar_SMTEncoding_Util.mkForall uu____9101))
in ((uu____9100), (Some ("Eq3 interpretation")), ("eq3-interp")))
in FStar_SMTEncoding_Term.Assume (uu____9096))
in (uu____9095)::[])))))))))))
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

let valid = (

let uu____9149 = (

let uu____9153 = (

let uu____9155 = (FStar_SMTEncoding_Util.mkApp ((imp), ((a)::(b)::[])))
in (uu____9155)::[])
in (("Valid"), (uu____9153)))
in (FStar_SMTEncoding_Util.mkApp uu____9149))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____9162 = (

let uu____9163 = (

let uu____9167 = (

let uu____9168 = (

let uu____9174 = (

let uu____9175 = (

let uu____9178 = (FStar_SMTEncoding_Util.mkImp ((valid_a), (valid_b)))
in ((uu____9178), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9175))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9174)))
in (FStar_SMTEncoding_Util.mkForall uu____9168))
in ((uu____9167), (Some ("==> interpretation")), ("l_imp-interp")))
in FStar_SMTEncoding_Term.Assume (uu____9163))
in (uu____9162)::[])))))))))
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

let valid = (

let uu____9212 = (

let uu____9216 = (

let uu____9218 = (FStar_SMTEncoding_Util.mkApp ((iff), ((a)::(b)::[])))
in (uu____9218)::[])
in (("Valid"), (uu____9216)))
in (FStar_SMTEncoding_Util.mkApp uu____9212))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____9225 = (

let uu____9226 = (

let uu____9230 = (

let uu____9231 = (

let uu____9237 = (

let uu____9238 = (

let uu____9241 = (FStar_SMTEncoding_Util.mkIff ((valid_a), (valid_b)))
in ((uu____9241), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9238))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9237)))
in (FStar_SMTEncoding_Util.mkForall uu____9231))
in ((uu____9230), (Some ("<==> interpretation")), ("l_iff-interp")))
in FStar_SMTEncoding_Term.Assume (uu____9226))
in (uu____9225)::[])))))))))
in (

let mk_not_interp = (fun env l_not tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let valid = (

let uu____9271 = (

let uu____9275 = (

let uu____9277 = (FStar_SMTEncoding_Util.mkApp ((l_not), ((a)::[])))
in (uu____9277)::[])
in (("Valid"), (uu____9275)))
in (FStar_SMTEncoding_Util.mkApp uu____9271))
in (

let not_valid_a = (

let uu____9281 = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9281))
in (

let uu____9283 = (

let uu____9284 = (

let uu____9288 = (

let uu____9289 = (

let uu____9295 = (FStar_SMTEncoding_Util.mkIff ((not_valid_a), (valid)))
in ((((valid)::[])::[]), ((aa)::[]), (uu____9295)))
in (FStar_SMTEncoding_Util.mkForall uu____9289))
in ((uu____9288), (Some ("not interpretation")), ("l_not-interp")))
in FStar_SMTEncoding_Term.Assume (uu____9284))
in (uu____9283)::[]))))))
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

let valid = (

let uu____9331 = (

let uu____9335 = (

let uu____9337 = (FStar_SMTEncoding_Util.mkApp ((for_all1), ((a)::(b)::[])))
in (uu____9337)::[])
in (("Valid"), (uu____9335)))
in (FStar_SMTEncoding_Util.mkApp uu____9331))
in (

let valid_b_x = (

let uu____9341 = (

let uu____9345 = (

let uu____9347 = (FStar_SMTEncoding_Util.mk_ApplyTT b x1)
in (uu____9347)::[])
in (("Valid"), (uu____9345)))
in (FStar_SMTEncoding_Util.mkApp uu____9341))
in (

let uu____9349 = (

let uu____9350 = (

let uu____9354 = (

let uu____9355 = (

let uu____9361 = (

let uu____9362 = (

let uu____9365 = (

let uu____9366 = (

let uu____9372 = (

let uu____9375 = (

let uu____9377 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in (uu____9377)::[])
in (uu____9375)::[])
in (

let uu____9380 = (

let uu____9381 = (

let uu____9384 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in ((uu____9384), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp uu____9381))
in ((uu____9372), ((xx1)::[]), (uu____9380))))
in (FStar_SMTEncoding_Util.mkForall uu____9366))
in ((uu____9365), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9362))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9361)))
in (FStar_SMTEncoding_Util.mkForall uu____9355))
in ((uu____9354), (Some ("forall interpretation")), ("forall-interp")))
in FStar_SMTEncoding_Term.Assume (uu____9350))
in (uu____9349)::[]))))))))))
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

let valid = (

let uu____9431 = (

let uu____9435 = (

let uu____9437 = (FStar_SMTEncoding_Util.mkApp ((for_some1), ((a)::(b)::[])))
in (uu____9437)::[])
in (("Valid"), (uu____9435)))
in (FStar_SMTEncoding_Util.mkApp uu____9431))
in (

let valid_b_x = (

let uu____9441 = (

let uu____9445 = (

let uu____9447 = (FStar_SMTEncoding_Util.mk_ApplyTT b x1)
in (uu____9447)::[])
in (("Valid"), (uu____9445)))
in (FStar_SMTEncoding_Util.mkApp uu____9441))
in (

let uu____9449 = (

let uu____9450 = (

let uu____9454 = (

let uu____9455 = (

let uu____9461 = (

let uu____9462 = (

let uu____9465 = (

let uu____9466 = (

let uu____9472 = (

let uu____9475 = (

let uu____9477 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in (uu____9477)::[])
in (uu____9475)::[])
in (

let uu____9480 = (

let uu____9481 = (

let uu____9484 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in ((uu____9484), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp uu____9481))
in ((uu____9472), ((xx1)::[]), (uu____9480))))
in (FStar_SMTEncoding_Util.mkExists uu____9466))
in ((uu____9465), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9462))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9461)))
in (FStar_SMTEncoding_Util.mkForall uu____9455))
in ((uu____9454), (Some ("exists interpretation")), ("exists-interp")))
in FStar_SMTEncoding_Term.Assume (uu____9450))
in (uu____9449)::[]))))))))))
in (

let mk_range_interp = (fun env range tt -> (

let range_ty = (FStar_SMTEncoding_Util.mkApp ((range), ([])))
in (

let uu____9520 = (

let uu____9521 = (

let uu____9525 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_ty)
in (

let uu____9526 = (varops.mk_unique "typing_range_const")
in ((uu____9525), (Some ("Range_const typing")), (uu____9526))))
in FStar_SMTEncoding_Term.Assume (uu____9521))
in (uu____9520)::[])))
in (

let prims1 = (((FStar_Syntax_Const.unit_lid), (mk_unit)))::(((FStar_Syntax_Const.bool_lid), (mk_bool)))::(((FStar_Syntax_Const.int_lid), (mk_int)))::(((FStar_Syntax_Const.string_lid), (mk_str)))::(((FStar_Syntax_Const.ref_lid), (mk_ref1)))::(((FStar_Syntax_Const.true_lid), (mk_true_interp)))::(((FStar_Syntax_Const.false_lid), (mk_false_interp)))::(((FStar_Syntax_Const.and_lid), (mk_and_interp)))::(((FStar_Syntax_Const.or_lid), (mk_or_interp)))::(((FStar_Syntax_Const.eq2_lid), (mk_eq2_interp)))::(((FStar_Syntax_Const.eq3_lid), (mk_eq3_interp)))::(((FStar_Syntax_Const.imp_lid), (mk_imp_interp)))::(((FStar_Syntax_Const.iff_lid), (mk_iff_interp)))::(((FStar_Syntax_Const.not_lid), (mk_not_interp)))::(((FStar_Syntax_Const.forall_lid), (mk_forall_interp)))::(((FStar_Syntax_Const.exists_lid), (mk_exists_interp)))::(((FStar_Syntax_Const.range_lid), (mk_range_interp)))::[]
in (fun env t s tt -> (

let uu____9788 = (FStar_Util.find_opt (fun uu____9806 -> (match (uu____9806) with
| (l, uu____9816) -> begin
(FStar_Ident.lid_equals l t)
end)) prims1)
in (match (uu____9788) with
| None -> begin
[]
end
| Some (uu____9838, f) -> begin
(f env s tt)
end)))))))))))))))))))))))))


let encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____9875 = (encode_function_type_as_formula None None t env)
in (match (uu____9875) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_SMTEncoding_Term.Assume (((form), (Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str))), ((Prims.strcat "lemma_" lid.FStar_Ident.str)))))::[]))
end))))


let encode_free_var : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env fv tt t_norm quals -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____9907 = ((

let uu____9908 = ((FStar_Syntax_Util.is_pure_or_ghost_function t_norm) || (FStar_TypeChecker_Env.is_reifiable_function env.tcenv t_norm))
in (FStar_All.pipe_left Prims.op_Negation uu____9908)) || (FStar_Syntax_Util.is_lemma t_norm))
in (match (uu____9907) with
| true -> begin
(

let uu____9912 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____9912) with
| (vname, vtok, env1) -> begin
(

let arg_sorts = (

let uu____9924 = (

let uu____9925 = (FStar_Syntax_Subst.compress t_norm)
in uu____9925.FStar_Syntax_Syntax.n)
in (match (uu____9924) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____9930) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun uu____9947 -> FStar_SMTEncoding_Term.Term_sort)))
end
| uu____9950 -> begin
[]
end))
in (

let d = FStar_SMTEncoding_Term.DeclFun (((vname), (arg_sorts), (FStar_SMTEncoding_Term.Term_sort), (Some ("Uninterpreted function symbol for impure function"))))
in (

let dd = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Uninterpreted name for impure function"))))
in (((d)::(dd)::[]), (env1)))))
end))
end
| uu____9958 -> begin
(

let uu____9959 = (prims.is lid)
in (match (uu____9959) with
| true -> begin
(

let vname = (varops.new_fvar lid)
in (

let uu____9964 = (prims.mk lid vname)
in (match (uu____9964) with
| (tok, definition) -> begin
(

let env1 = (push_free_var env lid vname (Some (tok)))
in ((definition), (env1)))
end)))
end
| uu____9977 -> begin
(

let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (

let uu____9979 = (

let uu____9985 = (curried_arrow_formals_comp t_norm)
in (match (uu____9985) with
| (args, comp) -> begin
(

let comp1 = (

let uu____9996 = (FStar_TypeChecker_Env.is_reifiable_comp env.tcenv comp)
in (match (uu____9996) with
| true -> begin
(

let uu____9997 = (FStar_TypeChecker_Env.reify_comp (

let uu___155_9998 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___155_9998.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___155_9998.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___155_9998.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___155_9998.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___155_9998.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___155_9998.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___155_9998.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___155_9998.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___155_9998.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___155_9998.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___155_9998.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___155_9998.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___155_9998.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___155_9998.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___155_9998.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___155_9998.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___155_9998.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___155_9998.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___155_9998.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___155_9998.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___155_9998.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___155_9998.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___155_9998.FStar_TypeChecker_Env.qname_and_index}) comp FStar_Syntax_Syntax.U_unknown)
in (FStar_Syntax_Syntax.mk_Total uu____9997))
end
| uu____9999 -> begin
comp
end))
in (match (encode_non_total_function_typ) with
| true -> begin
(

let uu____10005 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp1)
in ((args), (uu____10005)))
end
| uu____10012 -> begin
((args), (((None), ((FStar_Syntax_Util.comp_result comp1)))))
end))
end))
in (match (uu____9979) with
| (formals, (pre_opt, res_t)) -> begin
(

let uu____10032 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____10032) with
| (vname, vtok, env1) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
end
| uu____10045 -> begin
(FStar_SMTEncoding_Util.mkApp ((vtok), ([])))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun uu___126_10069 -> (match (uu___126_10069) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(

let uu____10072 = (FStar_Util.prefix vars)
in (match (uu____10072) with
| (uu____10083, (xxsym, uu____10085)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____10095 = (

let uu____10096 = (

let uu____10100 = (

let uu____10101 = (

let uu____10107 = (

let uu____10108 = (

let uu____10111 = (

let uu____10112 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____10112))
in ((vapp), (uu____10111)))
in (FStar_SMTEncoding_Util.mkEq uu____10108))
in ((((vapp)::[])::[]), (vars), (uu____10107)))
in (FStar_SMTEncoding_Util.mkForall uu____10101))
in ((uu____10100), (Some ("Discriminator equation")), ((Prims.strcat "disc_equation_" (escape d.FStar_Ident.str)))))
in FStar_SMTEncoding_Term.Assume (uu____10096))
in (uu____10095)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(

let uu____10123 = (FStar_Util.prefix vars)
in (match (uu____10123) with
| (uu____10134, (xxsym, uu____10136)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f1 = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (

let tp_name = (mk_term_projector_name d f1)
in (

let prim_app = (FStar_SMTEncoding_Util.mkApp ((tp_name), ((xx)::[])))
in (

let uu____10150 = (

let uu____10151 = (

let uu____10155 = (

let uu____10156 = (

let uu____10162 = (FStar_SMTEncoding_Util.mkEq ((vapp), (prim_app)))
in ((((vapp)::[])::[]), (vars), (uu____10162)))
in (FStar_SMTEncoding_Util.mkForall uu____10156))
in ((uu____10155), (Some ("Projector equation")), ((Prims.strcat "proj_equation_" tp_name))))
in FStar_SMTEncoding_Term.Assume (uu____10151))
in (uu____10150)::[])))))
end))
end
| uu____10171 -> begin
[]
end)))))
in (

let uu____10172 = (encode_binders None formals env1)
in (match (uu____10172) with
| (vars, guards, env', decls1, uu____10188) -> begin
(

let uu____10195 = (match (pre_opt) with
| None -> begin
(

let uu____10200 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____10200), (decls1)))
end
| Some (p) -> begin
(

let uu____10202 = (encode_formula p env')
in (match (uu____10202) with
| (g, ds) -> begin
(

let uu____10209 = (FStar_SMTEncoding_Util.mk_and_l ((g)::guards))
in ((uu____10209), ((FStar_List.append decls1 ds))))
end))
end)
in (match (uu____10195) with
| (guard, decls11) -> begin
(

let vtok_app = (mk_Apply vtok_tm vars)
in (

let vapp = (

let uu____10218 = (

let uu____10222 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((vname), (uu____10222)))
in (FStar_SMTEncoding_Util.mkApp uu____10218))
in (

let uu____10227 = (

let vname_decl = (

let uu____10232 = (

let uu____10238 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____10243 -> FStar_SMTEncoding_Term.Term_sort)))
in ((vname), (uu____10238), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (uu____10232))
in (

let uu____10248 = (

let env2 = (

let uu___156_10252 = env1
in {bindings = uu___156_10252.bindings; depth = uu___156_10252.depth; tcenv = uu___156_10252.tcenv; warn = uu___156_10252.warn; cache = uu___156_10252.cache; nolabels = uu___156_10252.nolabels; use_zfuel_name = uu___156_10252.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = uu___156_10252.current_module_name})
in (

let uu____10253 = (

let uu____10254 = (head_normal env2 tt)
in (not (uu____10254)))
in (match (uu____10253) with
| true -> begin
(encode_term_pred None tt env2 vtok_tm)
end
| uu____10257 -> begin
(encode_term_pred None t_norm env2 vtok_tm)
end)))
in (match (uu____10248) with
| (tok_typing, decls2) -> begin
(

let tok_typing1 = (match (formals) with
| (uu____10264)::uu____10265 -> begin
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

let uu____10288 = (

let uu____10294 = (FStar_SMTEncoding_Term.mk_NoHoist f tok_typing)
in ((((vtok_app_l)::[])::((vtok_app_r)::[])::[]), ((ff)::[]), (uu____10294)))
in (FStar_SMTEncoding_Util.mkForall uu____10288))
in FStar_SMTEncoding_Term.Assume (((guarded_tok_typing), (Some ("function token typing")), ((Prims.strcat "function_token_typing_" vname)))))))))
end
| uu____10308 -> begin
FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("function token typing")), ((Prims.strcat "function_token_typing_" vname))))
end)
in (

let uu____10310 = (match (formals) with
| [] -> begin
(

let uu____10319 = (

let uu____10320 = (

let uu____10322 = (FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left (fun _0_34 -> Some (_0_34)) uu____10322))
in (push_free_var env1 lid vname uu____10320))
in (((FStar_List.append decls2 ((tok_typing1)::[]))), (uu____10319)))
end
| uu____10325 -> begin
(

let vtok_decl = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let vtok_fresh = (

let uu____10330 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((vtok), (FStar_SMTEncoding_Term.Term_sort)) uu____10330))
in (

let name_tok_corr = (

let uu____10332 = (

let uu____10336 = (

let uu____10337 = (

let uu____10343 = (FStar_SMTEncoding_Util.mkEq ((vtok_app), (vapp)))
in ((((vtok_app)::[])::((vapp)::[])::[]), (vars), (uu____10343)))
in (FStar_SMTEncoding_Util.mkForall uu____10337))
in ((uu____10336), (Some ("Name-token correspondence")), ((Prims.strcat "token_correspondence_" vname))))
in FStar_SMTEncoding_Term.Assume (uu____10332))
in (((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing1)::[]))), (env1)))))
end)
in (match (uu____10310) with
| (tok_decl, env2) -> begin
(((vname_decl)::tok_decl), (env2))
end)))
end)))
in (match (uu____10227) with
| (decls2, env2) -> begin
(

let uu____10367 = (

let res_t1 = (FStar_Syntax_Subst.compress res_t)
in (

let uu____10372 = (encode_term res_t1 env')
in (match (uu____10372) with
| (encoded_res_t, decls) -> begin
(

let uu____10380 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in ((encoded_res_t), (uu____10380), (decls)))
end)))
in (match (uu____10367) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (

let uu____10388 = (

let uu____10392 = (

let uu____10393 = (

let uu____10399 = (FStar_SMTEncoding_Util.mkImp ((guard), (ty_pred)))
in ((((vapp)::[])::[]), (vars), (uu____10399)))
in (FStar_SMTEncoding_Util.mkForall uu____10393))
in ((uu____10392), (Some ("free var typing")), ((Prims.strcat "typing_" vname))))
in FStar_SMTEncoding_Term.Assume (uu____10388))
in (

let freshness = (

let uu____10408 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New))
in (match (uu____10408) with
| true -> begin
(

let uu____10411 = (

let uu____10412 = (

let uu____10418 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (

let uu____10424 = (varops.next_id ())
in ((vname), (uu____10418), (FStar_SMTEncoding_Term.Term_sort), (uu____10424))))
in (FStar_SMTEncoding_Term.fresh_constructor uu____10412))
in (

let uu____10426 = (

let uu____10428 = (pretype_axiom env2 vapp vars)
in (uu____10428)::[])
in (uu____10411)::uu____10426))
end
| uu____10429 -> begin
[]
end))
in (

let g = (

let uu____10432 = (

let uu____10434 = (

let uu____10436 = (

let uu____10438 = (

let uu____10440 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::uu____10440)
in (FStar_List.append freshness uu____10438))
in (FStar_List.append decls3 uu____10436))
in (FStar_List.append decls2 uu____10434))
in (FStar_List.append decls11 uu____10432))
in ((g), (env2)))))
end))
end))))
end))
end))))
end))
end)))
end))
end))))


let declare_top_level_let : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  ((Prims.string * FStar_SMTEncoding_Term.term Prims.option) * FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env x t t_norm -> (

let uu____10462 = (try_lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____10462) with
| None -> begin
(

let uu____10485 = (encode_free_var env x t t_norm [])
in (match (uu____10485) with
| (decls, env1) -> begin
(

let uu____10500 = (lookup_lid env1 x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____10500) with
| (n1, x', uu____10519) -> begin
((((n1), (x'))), (decls), (env1))
end))
end))
end
| Some (n1, x1, uu____10531) -> begin
((((n1), (x1))), ([]), (env))
end)))


let encode_top_level_val : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env lid t quals -> (

let tt = (norm env t)
in (

let uu____10564 = (encode_free_var env lid t tt quals)
in (match (uu____10564) with
| (decls, env1) -> begin
(

let uu____10575 = (FStar_Syntax_Util.is_smt_lemma t)
in (match (uu____10575) with
| true -> begin
(

let uu____10579 = (

let uu____10581 = (encode_smt_lemma env1 lid tt)
in (FStar_List.append decls uu____10581))
in ((uu____10579), (env1)))
end
| uu____10584 -> begin
((decls), (env1))
end))
end))))


let encode_top_level_vals : env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____10609 lb -> (match (uu____10609) with
| (decls, env1) -> begin
(

let uu____10621 = (

let uu____10625 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env1 uu____10625 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (uu____10621) with
| (decls', env2) -> begin
(((FStar_List.append decls decls')), (env2))
end))
end)) (([]), (env)))))


let is_tactic : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let fstar_tactics_tactic_lid = (FStar_Syntax_Const.p2l (("FStar")::("Tactics")::("tactic")::[]))
in (

let uu____10639 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____10639) with
| (hd1, args) -> begin
(

let uu____10665 = (

let uu____10666 = (FStar_Syntax_Util.un_uinst hd1)
in uu____10666.FStar_Syntax_Syntax.n)
in (match (uu____10665) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____10670, c) -> begin
(

let effect_name = (FStar_Syntax_Util.comp_effect_name c)
in (FStar_Util.starts_with "FStar.Tactics" effect_name.FStar_Ident.str))
end
| uu____10683 -> begin
false
end))
end))))


let encode_top_level_let : env_t  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env uu____10698 quals -> (match (uu____10698) with
| (is_rec, bindings) -> begin
(

let eta_expand1 = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let uu____10747 = (FStar_Util.first_N nbinders formals)
in (match (uu____10747) with
| (formals1, extra_formals) -> begin
(

let subst1 = (FStar_List.map2 (fun uu____10787 uu____10788 -> (match (((uu____10787), (uu____10788))) with
| ((formal, uu____10798), (binder, uu____10800)) -> begin
(

let uu____10805 = (

let uu____10810 = (FStar_Syntax_Syntax.bv_to_name binder)
in ((formal), (uu____10810)))
in FStar_Syntax_Syntax.NT (uu____10805))
end)) formals1 binders)
in (

let extra_formals1 = (

let uu____10815 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun uu____10829 -> (match (uu____10829) with
| (x, i) -> begin
(

let uu____10836 = (

let uu___157_10837 = x
in (

let uu____10838 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___157_10837.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___157_10837.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____10838}))
in ((uu____10836), (i)))
end))))
in (FStar_All.pipe_right uu____10815 FStar_Syntax_Util.name_binders))
in (

let body1 = (

let uu____10850 = (

let uu____10852 = (

let uu____10853 = (FStar_Syntax_Subst.subst subst1 t)
in uu____10853.FStar_Syntax_Syntax.n)
in (FStar_All.pipe_left (fun _0_35 -> Some (_0_35)) uu____10852))
in (

let uu____10857 = (

let uu____10858 = (FStar_Syntax_Subst.compress body)
in (

let uu____10859 = (

let uu____10860 = (FStar_Syntax_Util.args_of_binders extra_formals1)
in (FStar_All.pipe_left Prims.snd uu____10860))
in (FStar_Syntax_Syntax.extend_app_n uu____10858 uu____10859)))
in (uu____10857 uu____10850 body.FStar_Syntax_Syntax.pos)))
in (((FStar_List.append binders extra_formals1)), (body1)))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (

let get_result_type = (fun c -> (

let uu____10902 = (FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c)
in (match (uu____10902) with
| true -> begin
(FStar_TypeChecker_Env.reify_comp (

let uu___158_10903 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___158_10903.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___158_10903.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___158_10903.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___158_10903.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___158_10903.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___158_10903.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___158_10903.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___158_10903.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___158_10903.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___158_10903.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___158_10903.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___158_10903.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___158_10903.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___158_10903.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___158_10903.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___158_10903.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___158_10903.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___158_10903.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___158_10903.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___158_10903.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___158_10903.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___158_10903.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___158_10903.FStar_TypeChecker_Env.qname_and_index}) c FStar_Syntax_Syntax.U_unknown)
end
| uu____10904 -> begin
(FStar_Syntax_Util.comp_result c)
end)))
in (

let rec aux = (fun norm1 t_norm1 -> (

let uu____10924 = (FStar_Syntax_Util.abs_formals e)
in (match (uu____10924) with
| (binders, body, lopt) -> begin
(match (binders) with
| (uu____10973)::uu____10974 -> begin
(

let uu____10982 = (

let uu____10983 = (FStar_Syntax_Subst.compress t_norm1)
in uu____10983.FStar_Syntax_Syntax.n)
in (match (uu____10982) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____11010 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____11010) with
| (formals1, c1) -> begin
(

let nformals = (FStar_List.length formals1)
in (

let nbinders = (FStar_List.length binders)
in (

let tres = (get_result_type c1)
in (

let uu____11036 = ((nformals < nbinders) && (FStar_Syntax_Util.is_total_comp c1))
in (match (uu____11036) with
| true -> begin
(

let uu____11054 = (FStar_Util.first_N nformals binders)
in (match (uu____11054) with
| (bs0, rest) -> begin
(

let c2 = (

let subst1 = (FStar_List.map2 (fun uu____11100 uu____11101 -> (match (((uu____11100), (uu____11101))) with
| ((x, uu____11111), (b, uu____11113)) -> begin
(

let uu____11118 = (

let uu____11123 = (FStar_Syntax_Syntax.bv_to_name b)
in ((x), (uu____11123)))
in FStar_Syntax_Syntax.NT (uu____11118))
end)) formals1 bs0)
in (FStar_Syntax_Subst.subst_comp subst1 c1))
in (

let body1 = (FStar_Syntax_Util.abs rest body lopt)
in (

let uu____11125 = (

let uu____11136 = (get_result_type c2)
in ((bs0), (body1), (bs0), (uu____11136)))
in ((uu____11125), (false)))))
end))
end
| uu____11153 -> begin
(match ((nformals > nbinders)) with
| true -> begin
(

let uu____11171 = (eta_expand1 binders formals1 body tres)
in (match (uu____11171) with
| (binders1, body1) -> begin
((((binders1), (body1), (formals1), (tres))), (false))
end))
end
| uu____11217 -> begin
((((binders), (body), (formals1), (tres))), (false))
end)
end)))))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____11223) -> begin
(

let uu____11228 = (

let uu____11239 = (aux norm1 x.FStar_Syntax_Syntax.sort)
in (Prims.fst uu____11239))
in ((uu____11228), (true)))
end
| uu____11272 when (not (norm1)) -> begin
(

let t_norm2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm1)
in (aux true t_norm2))
end
| uu____11274 -> begin
(

let uu____11275 = (

let uu____11276 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____11277 = (FStar_Syntax_Print.term_to_string t_norm1)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str uu____11276 uu____11277)))
in (failwith uu____11275))
end))
end
| uu____11290 -> begin
(

let uu____11291 = (

let uu____11292 = (FStar_Syntax_Subst.compress t_norm1)
in uu____11292.FStar_Syntax_Syntax.n)
in (match (uu____11291) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____11319 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____11319) with
| (formals1, c1) -> begin
(

let tres = (get_result_type c1)
in (

let uu____11337 = (eta_expand1 [] formals1 e tres)
in (match (uu____11337) with
| (binders1, body1) -> begin
((((binders1), (body1), (formals1), (tres))), (false))
end)))
end))
end
| uu____11385 -> begin
(((([]), (e), ([]), (t_norm1))), (false))
end))
end)
end)))
in (aux false t_norm))))
in try
(match (()) with
| () -> begin
(

let uu____11413 = (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> ((FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))))
in (match (uu____11413) with
| true -> begin
(encode_top_level_vals env bindings quals)
end
| uu____11419 -> begin
(

let uu____11420 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____11461 lb -> (match (uu____11461) with
| (toks, typs, decls, env1) -> begin
((

let uu____11512 = (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp)
in (match (uu____11512) with
| true -> begin
(Prims.raise Let_rec_unencodeable)
end
| uu____11513 -> begin
()
end));
(

let t_norm = (whnf env1 lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____11515 = (

let uu____11523 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env1 uu____11523 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (uu____11515) with
| (tok, decl, env2) -> begin
(

let uu____11548 = (

let uu____11555 = (

let uu____11561 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in ((uu____11561), (tok)))
in (uu____11555)::toks)
in ((uu____11548), ((t_norm)::typs), ((decl)::decls), (env2)))
end)));
)
end)) (([]), ([]), ([]), (env))))
in (match (uu____11420) with
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
| uu____11663 -> begin
(match (curry) with
| true -> begin
(match (ftok) with
| Some (ftok1) -> begin
(mk_Apply ftok1 vars)
end
| None -> begin
(

let uu____11668 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply uu____11668 vars))
end)
end
| uu____11669 -> begin
(

let uu____11670 = (

let uu____11674 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (uu____11674)))
in (FStar_SMTEncoding_Util.mkApp uu____11670))
end)
end))
in (

let uu____11679 = ((FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___127_11681 -> (match (uu___127_11681) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| uu____11682 -> begin
false
end)))) || (FStar_All.pipe_right typs1 (FStar_Util.for_some (fun t -> (

let uu____11685 = ((FStar_Syntax_Util.is_pure_or_ghost_function t) || (FStar_TypeChecker_Env.is_reifiable_function env1.tcenv t))
in (FStar_All.pipe_left Prims.op_Negation uu____11685))))))
in (match (uu____11679) with
| true -> begin
((decls1), (env1))
end
| uu____11690 -> begin
(match ((not (is_rec))) with
| true -> begin
(match (((bindings), (typs1), (toks1))) with
| (({FStar_Syntax_Syntax.lbname = uu____11705; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____11707; FStar_Syntax_Syntax.lbeff = uu____11708; FStar_Syntax_Syntax.lbdef = e})::[], (t_norm)::[], ((flid_fv, (f, ftok)))::[]) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____11749 = (

let uu____11753 = (FStar_TypeChecker_Env.open_universes_in env1.tcenv uvs ((e)::(t_norm)::[]))
in (match (uu____11753) with
| (tcenv', uu____11764, e_t) -> begin
(

let uu____11768 = (match (e_t) with
| (e1)::(t_norm1)::[] -> begin
((e1), (t_norm1))
end
| uu____11775 -> begin
(failwith "Impossible")
end)
in (match (uu____11768) with
| (e1, t_norm1) -> begin
(((

let uu___161_11784 = env1
in {bindings = uu___161_11784.bindings; depth = uu___161_11784.depth; tcenv = tcenv'; warn = uu___161_11784.warn; cache = uu___161_11784.cache; nolabels = uu___161_11784.nolabels; use_zfuel_name = uu___161_11784.use_zfuel_name; encode_non_total_function_typ = uu___161_11784.encode_non_total_function_typ; current_module_name = uu___161_11784.current_module_name})), (e1), (t_norm1))
end))
end))
in (match (uu____11749) with
| (env', e1, t_norm1) -> begin
(

let uu____11791 = (destruct_bound_function flid t_norm1 e1)
in (match (uu____11791) with
| ((binders, body, uu____11803, uu____11804), curry) -> begin
((

let uu____11811 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____11811) with
| true -> begin
(

let uu____11812 = (FStar_Syntax_Print.binders_to_string ", " binders)
in (

let uu____11813 = (FStar_Syntax_Print.term_to_string body)
in (FStar_Util.print2 "Encoding let : binders=[%s], body=%s\n" uu____11812 uu____11813)))
end
| uu____11814 -> begin
()
end));
(

let uu____11815 = (encode_binders None binders env')
in (match (uu____11815) with
| (vars, guards, env'1, binder_decls, uu____11831) -> begin
(

let body1 = (

let uu____11839 = (FStar_TypeChecker_Env.is_reifiable_function env'1.tcenv t_norm1)
in (match (uu____11839) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env'1.tcenv body)
end
| uu____11840 -> begin
body
end))
in (

let app = (mk_app1 curry f ftok vars)
in (

let uu____11842 = (

let uu____11847 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic))
in (match (uu____11847) with
| true -> begin
(

let uu____11853 = (FStar_SMTEncoding_Term.mk_Valid app)
in (

let uu____11854 = (encode_formula body1 env'1)
in ((uu____11853), (uu____11854))))
end
| uu____11859 -> begin
(

let uu____11860 = (encode_term body1 env'1)
in ((app), (uu____11860)))
end))
in (match (uu____11842) with
| (app1, (body2, decls2)) -> begin
(

let eqn = (

let uu____11874 = (

let uu____11878 = (

let uu____11879 = (

let uu____11885 = (FStar_SMTEncoding_Util.mkEq ((app1), (body2)))
in ((((app1)::[])::[]), (vars), (uu____11885)))
in (FStar_SMTEncoding_Util.mkForall uu____11879))
in (

let uu____11891 = (

let uu____11893 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (uu____11893))
in ((uu____11878), (uu____11891), ((Prims.strcat "equation_" f)))))
in FStar_SMTEncoding_Term.Assume (uu____11874))
in (

let uu____11895 = (

let uu____11897 = (

let uu____11899 = (

let uu____11901 = (

let uu____11903 = (primitive_type_axioms env1.tcenv flid f app1)
in (FStar_List.append ((eqn)::[]) uu____11903))
in (FStar_List.append decls2 uu____11901))
in (FStar_List.append binder_decls uu____11899))
in (FStar_List.append decls1 uu____11897))
in ((uu____11895), (env1))))
end))))
end));
)
end))
end)))
end
| uu____11906 -> begin
(failwith "Impossible")
end)
end
| uu____11921 -> begin
(

let fuel = (

let uu____11925 = (varops.fresh "fuel")
in ((uu____11925), (FStar_SMTEncoding_Term.Fuel_sort)))
in (

let fuel_tm = (FStar_SMTEncoding_Util.mkFreeV fuel)
in (

let env0 = env1
in (

let uu____11928 = (FStar_All.pipe_right toks1 (FStar_List.fold_left (fun uu____11967 uu____11968 -> (match (((uu____11967), (uu____11968))) with
| ((gtoks, env2), (flid_fv, (f, ftok))) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let g = (

let uu____12050 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented")
in (varops.new_fvar uu____12050))
in (

let gtok = (

let uu____12052 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented_token")
in (varops.new_fvar uu____12052))
in (

let env3 = (

let uu____12054 = (

let uu____12056 = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::[])))
in (FStar_All.pipe_left (fun _0_36 -> Some (_0_36)) uu____12056))
in (push_free_var env2 flid gtok uu____12054))
in (((((flid), (f), (ftok), (g), (gtok)))::gtoks), (env3))))))
end)) (([]), (env1))))
in (match (uu____11928) with
| (gtoks, env2) -> begin
(

let gtoks1 = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env01 uu____12142 t_norm uu____12144 -> (match (((uu____12142), (uu____12144))) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = lbn; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____12171; FStar_Syntax_Syntax.lbeff = uu____12172; FStar_Syntax_Syntax.lbdef = e}) -> begin
(

let uu____12189 = (

let uu____12193 = (FStar_TypeChecker_Env.open_universes_in env2.tcenv uvs ((e)::(t_norm)::[]))
in (match (uu____12193) with
| (tcenv', uu____12208, e_t) -> begin
(

let uu____12212 = (match (e_t) with
| (e1)::(t_norm1)::[] -> begin
((e1), (t_norm1))
end
| uu____12219 -> begin
(failwith "Impossible")
end)
in (match (uu____12212) with
| (e1, t_norm1) -> begin
(((

let uu___162_12228 = env2
in {bindings = uu___162_12228.bindings; depth = uu___162_12228.depth; tcenv = tcenv'; warn = uu___162_12228.warn; cache = uu___162_12228.cache; nolabels = uu___162_12228.nolabels; use_zfuel_name = uu___162_12228.use_zfuel_name; encode_non_total_function_typ = uu___162_12228.encode_non_total_function_typ; current_module_name = uu___162_12228.current_module_name})), (e1), (t_norm1))
end))
end))
in (match (uu____12189) with
| (env', e1, t_norm1) -> begin
((

let uu____12238 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env01.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____12238) with
| true -> begin
(

let uu____12239 = (FStar_Syntax_Print.lbname_to_string lbn)
in (

let uu____12240 = (FStar_Syntax_Print.term_to_string t_norm1)
in (

let uu____12241 = (FStar_Syntax_Print.term_to_string e1)
in (FStar_Util.print3 "Encoding let rec %s : %s = %s\n" uu____12239 uu____12240 uu____12241))))
end
| uu____12242 -> begin
()
end));
(

let uu____12243 = (destruct_bound_function flid t_norm1 e1)
in (match (uu____12243) with
| ((binders, body, formals, tres), curry) -> begin
((

let uu____12265 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env01.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____12265) with
| true -> begin
(

let uu____12266 = (FStar_Syntax_Print.binders_to_string ", " binders)
in (

let uu____12267 = (FStar_Syntax_Print.term_to_string body)
in (

let uu____12268 = (FStar_Syntax_Print.binders_to_string ", " formals)
in (

let uu____12269 = (FStar_Syntax_Print.term_to_string tres)
in (FStar_Util.print4 "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n" uu____12266 uu____12267 uu____12268 uu____12269)))))
end
| uu____12270 -> begin
()
end));
(match (curry) with
| true -> begin
(failwith "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type")
end
| uu____12272 -> begin
()
end);
(

let uu____12273 = (encode_binders None binders env')
in (match (uu____12273) with
| (vars, guards, env'1, binder_decls, uu____12291) -> begin
(

let decl_g = (

let uu____12299 = (

let uu____12305 = (

let uu____12307 = (FStar_List.map Prims.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::uu____12307)
in ((g), (uu____12305), (FStar_SMTEncoding_Term.Term_sort), (Some ("Fuel-instrumented function name"))))
in FStar_SMTEncoding_Term.DeclFun (uu____12299))
in (

let env02 = (push_zfuel_name env01 flid g)
in (

let decl_g_tok = FStar_SMTEncoding_Term.DeclFun (((gtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Token for fuel-instrumented partial applications"))))
in (

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let app = (

let uu____12322 = (

let uu____12326 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (uu____12326)))
in (FStar_SMTEncoding_Util.mkApp uu____12322))
in (

let gsapp = (

let uu____12332 = (

let uu____12336 = (

let uu____12338 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (uu____12338)::vars_tm)
in ((g), (uu____12336)))
in (FStar_SMTEncoding_Util.mkApp uu____12332))
in (

let gmax = (

let uu____12342 = (

let uu____12346 = (

let uu____12348 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (uu____12348)::vars_tm)
in ((g), (uu____12346)))
in (FStar_SMTEncoding_Util.mkApp uu____12342))
in (

let body1 = (

let uu____12352 = (FStar_TypeChecker_Env.is_reifiable_function env'1.tcenv t_norm1)
in (match (uu____12352) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env'1.tcenv body)
end
| uu____12353 -> begin
body
end))
in (

let uu____12354 = (encode_term body1 env'1)
in (match (uu____12354) with
| (body_tm, decls2) -> begin
(

let eqn_g = (

let uu____12365 = (

let uu____12369 = (

let uu____12370 = (

let uu____12378 = (FStar_SMTEncoding_Util.mkEq ((gsapp), (body_tm)))
in ((((gsapp)::[])::[]), (Some ((Prims.parse_int "0"))), ((fuel)::vars), (uu____12378)))
in (FStar_SMTEncoding_Util.mkForall' uu____12370))
in (

let uu____12389 = (

let uu____12391 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (uu____12391))
in ((uu____12369), (uu____12389), ((Prims.strcat "equation_with_fuel_" g)))))
in FStar_SMTEncoding_Term.Assume (uu____12365))
in (

let eqn_f = (

let uu____12394 = (

let uu____12398 = (

let uu____12399 = (

let uu____12405 = (FStar_SMTEncoding_Util.mkEq ((app), (gmax)))
in ((((app)::[])::[]), (vars), (uu____12405)))
in (FStar_SMTEncoding_Util.mkForall uu____12399))
in ((uu____12398), (Some ("Correspondence of recursive function to instrumented version")), ((Prims.strcat "@fuel_correspondence_" g))))
in FStar_SMTEncoding_Term.Assume (uu____12394))
in (

let eqn_g' = (

let uu____12413 = (

let uu____12417 = (

let uu____12418 = (

let uu____12424 = (

let uu____12425 = (

let uu____12428 = (

let uu____12429 = (

let uu____12433 = (

let uu____12435 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "0"))
in (uu____12435)::vars_tm)
in ((g), (uu____12433)))
in (FStar_SMTEncoding_Util.mkApp uu____12429))
in ((gsapp), (uu____12428)))
in (FStar_SMTEncoding_Util.mkEq uu____12425))
in ((((gsapp)::[])::[]), ((fuel)::vars), (uu____12424)))
in (FStar_SMTEncoding_Util.mkForall uu____12418))
in ((uu____12417), (Some ("Fuel irrelevance")), ((Prims.strcat "@fuel_irrelevance_" g))))
in FStar_SMTEncoding_Term.Assume (uu____12413))
in (

let uu____12447 = (

let uu____12452 = (encode_binders None formals env02)
in (match (uu____12452) with
| (vars1, v_guards, env3, binder_decls1, uu____12469) -> begin
(

let vars_tm1 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars1)
in (

let gapp = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::vars_tm1)))
in (

let tok_corr = (

let tok_app = (

let uu____12484 = (FStar_SMTEncoding_Util.mkFreeV ((gtok), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply uu____12484 ((fuel)::vars1)))
in (

let uu____12487 = (

let uu____12491 = (

let uu____12492 = (

let uu____12498 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (gapp)))
in ((((tok_app)::[])::[]), ((fuel)::vars1), (uu____12498)))
in (FStar_SMTEncoding_Util.mkForall uu____12492))
in ((uu____12491), (Some ("Fuel token correspondence")), ((Prims.strcat "fuel_token_correspondence_" gtok))))
in FStar_SMTEncoding_Term.Assume (uu____12487)))
in (

let uu____12509 = (

let uu____12513 = (encode_term_pred None tres env3 gapp)
in (match (uu____12513) with
| (g_typing, d3) -> begin
(

let uu____12521 = (

let uu____12523 = (

let uu____12524 = (

let uu____12528 = (

let uu____12529 = (

let uu____12535 = (

let uu____12536 = (

let uu____12539 = (FStar_SMTEncoding_Util.mk_and_l v_guards)
in ((uu____12539), (g_typing)))
in (FStar_SMTEncoding_Util.mkImp uu____12536))
in ((((gapp)::[])::[]), ((fuel)::vars1), (uu____12535)))
in (FStar_SMTEncoding_Util.mkForall uu____12529))
in ((uu____12528), (Some ("Typing correspondence of token to term")), ((Prims.strcat "token_correspondence_" g))))
in FStar_SMTEncoding_Term.Assume (uu____12524))
in (uu____12523)::[])
in ((d3), (uu____12521)))
end))
in (match (uu____12509) with
| (aux_decls, typing_corr) -> begin
(((FStar_List.append binder_decls1 aux_decls)), ((FStar_List.append typing_corr ((tok_corr)::[]))))
end)))))
end))
in (match (uu____12447) with
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

let uu____12574 = (

let uu____12581 = (FStar_List.zip3 gtoks1 typs1 bindings)
in (FStar_List.fold_left (fun uu____12617 uu____12618 -> (match (((uu____12617), (uu____12618))) with
| ((decls2, eqns, env01), (gtok, ty, lb)) -> begin
(

let uu____12704 = (encode_one_binding env01 gtok ty lb)
in (match (uu____12704) with
| (decls', eqns', env02) -> begin
(((decls')::decls2), ((FStar_List.append eqns' eqns)), (env02))
end))
end)) (((decls1)::[]), ([]), (env0)) uu____12581))
in (match (uu____12574) with
| (decls2, eqns, env01) -> begin
(

let uu____12744 = (

let isDeclFun = (fun uu___128_12752 -> (match (uu___128_12752) with
| FStar_SMTEncoding_Term.DeclFun (uu____12753) -> begin
true
end
| uu____12759 -> begin
false
end))
in (

let uu____12760 = (FStar_All.pipe_right decls2 FStar_List.flatten)
in (FStar_All.pipe_right uu____12760 (FStar_List.partition isDeclFun))))
in (match (uu____12744) with
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

let uu____12787 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right uu____12787 (FStar_String.concat " and ")))
in (

let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in (((decl)::[]), (env))))
end))
end))


let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> ((

let uu____12820 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____12820) with
| true -> begin
(

let uu____12821 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") uu____12821))
end
| uu____12822 -> begin
()
end));
(

let nm = (

let uu____12824 = (FStar_Syntax_Util.lid_of_sigelt se)
in (match (uu____12824) with
| None -> begin
""
end
| Some (l) -> begin
l.FStar_Ident.str
end))
in (

let uu____12827 = (encode_sigelt' env se)
in (match (uu____12827) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(

let uu____12836 = (

let uu____12838 = (

let uu____12839 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (uu____12839))
in (uu____12838)::[])
in ((uu____12836), (e)))
end
| uu____12841 -> begin
(

let uu____12842 = (

let uu____12844 = (

let uu____12846 = (

let uu____12847 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____12847))
in (uu____12846)::g)
in (

let uu____12848 = (

let uu____12850 = (

let uu____12851 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____12851))
in (uu____12850)::[])
in (FStar_List.append uu____12844 uu____12848)))
in ((uu____12842), (e)))
end)
end)));
))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____12859) -> begin
(failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(

let uu____12868 = (

let uu____12869 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right uu____12869 Prims.op_Negation))
in (match (uu____12868) with
| true -> begin
(([]), (env))
end
| uu____12874 -> begin
(

let close_effect_params = (fun tm -> (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
tm
end
| uu____12889 -> begin
(

let uu____12890 = (

let uu____12893 = (

let uu____12894 = (

let uu____12909 = (FStar_All.pipe_left (fun _0_37 -> Some (_0_37)) (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[])))))
in ((ed.FStar_Syntax_Syntax.binders), (tm), (uu____12909)))
in FStar_Syntax_Syntax.Tm_abs (uu____12894))
in (FStar_Syntax_Syntax.mk uu____12893))
in (uu____12890 None tm.FStar_Syntax_Syntax.pos))
end))
in (

let encode_action = (fun env1 a -> (

let uu____12962 = (new_term_constant_and_tok_from_lid env1 a.FStar_Syntax_Syntax.action_name)
in (match (uu____12962) with
| (aname, atok, env2) -> begin
(

let uu____12972 = (FStar_Syntax_Util.arrow_formals_comp a.FStar_Syntax_Syntax.action_typ)
in (match (uu____12972) with
| (formals, uu____12982) -> begin
(

let uu____12989 = (

let uu____12992 = (close_effect_params a.FStar_Syntax_Syntax.action_defn)
in (encode_term uu____12992 env2))
in (match (uu____12989) with
| (tm, decls) -> begin
(

let a_decls = (

let uu____13000 = (

let uu____13001 = (

let uu____13007 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____13015 -> FStar_SMTEncoding_Term.Term_sort)))
in ((aname), (uu____13007), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action"))))
in FStar_SMTEncoding_Term.DeclFun (uu____13001))
in (uu____13000)::(FStar_SMTEncoding_Term.DeclFun (((atok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action token")))))::[])
in (

let uu____13022 = (

let aux = (fun uu____13051 uu____13052 -> (match (((uu____13051), (uu____13052))) with
| ((bv, uu____13079), (env3, acc_sorts, acc)) -> begin
(

let uu____13100 = (gen_term_var env3 bv)
in (match (uu____13100) with
| (xxsym, xx, env4) -> begin
((env4), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::acc_sorts), ((xx)::acc))
end))
end))
in (FStar_List.fold_right aux formals ((env2), ([]), ([]))))
in (match (uu____13022) with
| (uu____13138, xs_sorts, xs) -> begin
(

let app = (FStar_SMTEncoding_Util.mkApp ((aname), (xs)))
in (

let a_eq = (

let uu____13152 = (

let uu____13156 = (

let uu____13157 = (

let uu____13163 = (

let uu____13164 = (

let uu____13167 = (mk_Apply tm xs_sorts)
in ((app), (uu____13167)))
in (FStar_SMTEncoding_Util.mkEq uu____13164))
in ((((app)::[])::[]), (xs_sorts), (uu____13163)))
in (FStar_SMTEncoding_Util.mkForall uu____13157))
in ((uu____13156), (Some ("Action equality")), ((Prims.strcat aname "_equality"))))
in FStar_SMTEncoding_Term.Assume (uu____13152))
in (

let tok_correspondence = (

let tok_term = (FStar_SMTEncoding_Util.mkFreeV ((atok), (FStar_SMTEncoding_Term.Term_sort)))
in (

let tok_app = (mk_Apply tok_term xs_sorts)
in (

let uu____13179 = (

let uu____13183 = (

let uu____13184 = (

let uu____13190 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (app)))
in ((((tok_app)::[])::[]), (xs_sorts), (uu____13190)))
in (FStar_SMTEncoding_Util.mkForall uu____13184))
in ((uu____13183), (Some ("Action token correspondence")), ((Prims.strcat aname "_token_correspondence"))))
in FStar_SMTEncoding_Term.Assume (uu____13179))))
in ((env2), ((FStar_List.append decls (FStar_List.append a_decls ((a_eq)::(tok_correspondence)::[]))))))))
end)))
end))
end))
end)))
in (

let uu____13200 = (FStar_Util.fold_map encode_action env ed.FStar_Syntax_Syntax.actions)
in (match (uu____13200) with
| (env1, decls2) -> begin
(((FStar_List.flatten decls2)), (env1))
end))))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____13216, uu____13217, uu____13218) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid) -> begin
(

let uu____13221 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____13221) with
| (tname, ttok, env1) -> begin
(([]), (env1))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____13232, t, quals) -> begin
(

let will_encode_definition = (

let uu____13238 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___129_13240 -> (match (uu___129_13240) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Irreducible) -> begin
true
end
| uu____13243 -> begin
false
end))))
in (not (uu____13238)))
in (match (will_encode_definition) with
| true -> begin
(([]), (env))
end
| uu____13247 -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____13249 = (encode_top_level_val env fv t quals)
in (match (uu____13249) with
| (decls, env1) -> begin
(

let tname = lid.FStar_Ident.str
in (

let tsym = (FStar_SMTEncoding_Util.mkFreeV ((tname), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____13261 = (

let uu____13263 = (primitive_type_axioms env1.tcenv lid tname tsym)
in (FStar_List.append decls uu____13263))
in ((uu____13261), (env1)))))
end)))
end))
end
| FStar_Syntax_Syntax.Sig_assume (l, f, uu____13268) -> begin
(

let uu____13271 = (encode_formula f env)
in (match (uu____13271) with
| (f1, decls) -> begin
(

let g = (

let uu____13280 = (

let uu____13281 = (

let uu____13285 = (

let uu____13287 = (

let uu____13288 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" uu____13288))
in Some (uu____13287))
in (

let uu____13289 = (varops.mk_unique (Prims.strcat "assumption_" l.FStar_Ident.str))
in ((f1), (uu____13285), (uu____13289))))
in FStar_SMTEncoding_Term.Assume (uu____13281))
in (uu____13280)::[])
in (((FStar_List.append decls g)), (env)))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____13293, quals, uu____13295) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) -> begin
(

let uu____13303 = (FStar_Util.fold_map (fun env1 lb -> (

let lid = (

let uu____13310 = (

let uu____13315 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____13315.FStar_Syntax_Syntax.fv_name)
in uu____13310.FStar_Syntax_Syntax.v)
in (

let uu____13319 = (

let uu____13320 = (FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone uu____13320))
in (match (uu____13319) with
| true -> begin
(

let val_decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals))); FStar_Syntax_Syntax.sigrng = se.FStar_Syntax_Syntax.sigrng}
in (

let uu____13339 = (encode_sigelt' env1 val_decl)
in (match (uu____13339) with
| (decls, env2) -> begin
((env2), (decls))
end)))
end
| uu____13346 -> begin
((env1), ([]))
end)))) env (Prims.snd lbs))
in (match (uu____13303) with
| (env1, decls) -> begin
(((FStar_List.flatten decls)), (env1))
end))
end
| FStar_Syntax_Syntax.Sig_let ((uu____13356, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t1); FStar_Syntax_Syntax.lbunivs = uu____13358; FStar_Syntax_Syntax.lbtyp = uu____13359; FStar_Syntax_Syntax.lbeff = uu____13360; FStar_Syntax_Syntax.lbdef = uu____13361})::[]), uu____13362, uu____13363, uu____13364) when (FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid) -> begin
(

let uu____13380 = (new_term_constant_and_tok_from_lid env b2t1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____13380) with
| (tname, ttok, env1) -> begin
(

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let valid_b2t_x = (

let uu____13398 = (

let uu____13402 = (

let uu____13404 = (FStar_SMTEncoding_Util.mkApp (("Prims.b2t"), ((x)::[])))
in (uu____13404)::[])
in (("Valid"), (uu____13402)))
in (FStar_SMTEncoding_Util.mkApp uu____13398))
in (

let decls = (

let uu____13409 = (

let uu____13411 = (

let uu____13412 = (

let uu____13416 = (

let uu____13417 = (

let uu____13423 = (

let uu____13424 = (

let uu____13427 = (FStar_SMTEncoding_Util.mkApp (("BoxBool_proj_0"), ((x)::[])))
in ((valid_b2t_x), (uu____13427)))
in (FStar_SMTEncoding_Util.mkEq uu____13424))
in ((((valid_b2t_x)::[])::[]), ((xx)::[]), (uu____13423)))
in (FStar_SMTEncoding_Util.mkForall uu____13417))
in ((uu____13416), (Some ("b2t def")), ("b2t_def")))
in FStar_SMTEncoding_Term.Assume (uu____13412))
in (uu____13411)::[])
in (FStar_SMTEncoding_Term.DeclFun (((tname), ((FStar_SMTEncoding_Term.Term_sort)::[]), (FStar_SMTEncoding_Term.Term_sort), (None))))::uu____13409)
in ((decls), (env1))))))
end))
end
| FStar_Syntax_Syntax.Sig_let (uu____13444, uu____13445, quals, uu____13447) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___130_13455 -> (match (uu___130_13455) with
| FStar_Syntax_Syntax.Discriminator (uu____13456) -> begin
true
end
| uu____13457 -> begin
false
end)))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let (uu____13459, lids, quals, uu____13462) when ((FStar_All.pipe_right lids (FStar_Util.for_some (fun l -> (

let uu____13471 = (

let uu____13472 = (FStar_List.hd l.FStar_Ident.ns)
in uu____13472.FStar_Ident.idText)
in (uu____13471 = "Prims"))))) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___131_13474 -> (match (uu___131_13474) with
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
true
end
| uu____13475 -> begin
false
end))))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____13478, quals, uu____13480) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___132_13492 -> (match (uu___132_13492) with
| FStar_Syntax_Syntax.Projector (uu____13493) -> begin
true
end
| uu____13496 -> begin
false
end)))) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____13503 = (try_lookup_free_var env l)
in (match (uu____13503) with
| Some (uu____13507) -> begin
(([]), (env))
end
| None -> begin
(

let se1 = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l)}
in (encode_sigelt env se1))
end))))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), uu____13516, quals, uu____13518) -> begin
(encode_top_level_let env ((is_rec), (bindings)) quals)
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____13532, uu____13533) -> begin
(

let uu____13540 = (encode_signature env ses)
in (match (uu____13540) with
| (g, env1) -> begin
(

let uu____13550 = (FStar_All.pipe_right g (FStar_List.partition (fun uu___133_13560 -> (match (uu___133_13560) with
| FStar_SMTEncoding_Term.Assume (uu____13561, Some ("inversion axiom"), uu____13562) -> begin
false
end
| uu____13564 -> begin
true
end))))
in (match (uu____13550) with
| (g', inversions) -> begin
(

let uu____13573 = (FStar_All.pipe_right g' (FStar_List.partition (fun uu___134_13583 -> (match (uu___134_13583) with
| FStar_SMTEncoding_Term.DeclFun (uu____13584) -> begin
true
end
| uu____13590 -> begin
false
end))))
in (match (uu____13573) with
| (decls, rest) -> begin
(((FStar_List.append decls (FStar_List.append rest inversions))), (env1))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, uu____13601, tps, k, uu____13604, datas, quals) -> begin
(

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___135_13615 -> (match (uu___135_13615) with
| (FStar_Syntax_Syntax.Logic) | (FStar_Syntax_Syntax.Assumption) -> begin
true
end
| uu____13616 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> (match (is_logical) with
| true -> begin
(

let uu____13623 = c
in (match (uu____13623) with
| (name, args, uu____13627, uu____13628, uu____13629) -> begin
(

let uu____13632 = (

let uu____13633 = (

let uu____13639 = (FStar_All.pipe_right args (FStar_List.map (fun uu____13646 -> (match (uu____13646) with
| (uu____13650, sort, uu____13652) -> begin
sort
end))))
in ((name), (uu____13639), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (uu____13633))
in (uu____13632)::[])
end))
end
| uu____13655 -> begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end))
in (

let inversion_axioms = (fun tapp vars -> (

let uu____13670 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (

let uu____13673 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right uu____13673 FStar_Option.isNone)))))
in (match (uu____13670) with
| true -> begin
[]
end
| uu____13689 -> begin
(

let uu____13690 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____13690) with
| (xxsym, xx) -> begin
(

let uu____13696 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun uu____13707 l -> (match (uu____13707) with
| (out, decls) -> begin
(

let uu____13719 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (uu____13719) with
| (uu____13725, data_t) -> begin
(

let uu____13727 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (uu____13727) with
| (args, res) -> begin
(

let indices = (

let uu____13756 = (

let uu____13757 = (FStar_Syntax_Subst.compress res)
in uu____13757.FStar_Syntax_Syntax.n)
in (match (uu____13756) with
| FStar_Syntax_Syntax.Tm_app (uu____13765, indices) -> begin
indices
end
| uu____13781 -> begin
[]
end))
in (

let env1 = (FStar_All.pipe_right args (FStar_List.fold_left (fun env1 uu____13793 -> (match (uu____13793) with
| (x, uu____13797) -> begin
(

let uu____13798 = (

let uu____13799 = (

let uu____13803 = (mk_term_projector_name l x)
in ((uu____13803), ((xx)::[])))
in (FStar_SMTEncoding_Util.mkApp uu____13799))
in (push_term_var env1 x uu____13798))
end)) env))
in (

let uu____13805 = (encode_args indices env1)
in (match (uu____13805) with
| (indices1, decls') -> begin
((match (((FStar_List.length indices1) <> (FStar_List.length vars))) with
| true -> begin
(failwith "Impossible")
end
| uu____13823 -> begin
()
end);
(

let eqs = (

let uu____13825 = (FStar_List.map2 (fun v1 a -> (

let uu____13833 = (

let uu____13836 = (FStar_SMTEncoding_Util.mkFreeV v1)
in ((uu____13836), (a)))
in (FStar_SMTEncoding_Util.mkEq uu____13833))) vars indices1)
in (FStar_All.pipe_right uu____13825 FStar_SMTEncoding_Util.mk_and_l))
in (

let uu____13838 = (

let uu____13839 = (

let uu____13842 = (

let uu____13843 = (

let uu____13846 = (mk_data_tester env1 l xx)
in ((uu____13846), (eqs)))
in (FStar_SMTEncoding_Util.mkAnd uu____13843))
in ((out), (uu____13842)))
in (FStar_SMTEncoding_Util.mkOr uu____13839))
in ((uu____13838), ((FStar_List.append decls decls')))));
)
end))))
end))
end))
end)) ((FStar_SMTEncoding_Util.mkFalse), ([]))))
in (match (uu____13696) with
| (data_ax, decls) -> begin
(

let uu____13854 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____13854) with
| (ffsym, ff) -> begin
(

let fuel_guarded_inversion = (

let xx_has_type_sfuel = (match (((FStar_List.length datas) > (Prims.parse_int "1"))) with
| true -> begin
(

let uu____13865 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((ff)::[])))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel uu____13865 xx tapp))
end
| uu____13867 -> begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end)
in (

let uu____13868 = (

let uu____13872 = (

let uu____13873 = (

let uu____13879 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (

let uu____13887 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_sfuel), (data_ax)))
in ((((xx_has_type_sfuel)::[])::[]), (uu____13879), (uu____13887))))
in (FStar_SMTEncoding_Util.mkForall uu____13873))
in (

let uu____13895 = (varops.mk_unique (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str))
in ((uu____13872), (Some ("inversion axiom")), (uu____13895))))
in FStar_SMTEncoding_Term.Assume (uu____13868)))
in (

let pattern_guarded_inversion = (

let uu____13899 = ((contains_name env "Prims.inversion") && ((FStar_List.length datas) > (Prims.parse_int "1")))
in (match (uu____13899) with
| true -> begin
(

let xx_has_type_fuel = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let pattern_guard = (FStar_SMTEncoding_Util.mkApp (("Prims.inversion"), ((tapp)::[])))
in (

let uu____13907 = (

let uu____13908 = (

let uu____13912 = (

let uu____13913 = (

let uu____13919 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (

let uu____13927 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_fuel), (data_ax)))
in ((((xx_has_type_fuel)::(pattern_guard)::[])::[]), (uu____13919), (uu____13927))))
in (FStar_SMTEncoding_Util.mkForall uu____13913))
in (

let uu____13935 = (varops.mk_unique (Prims.strcat "pattern_guarded_inversion_" t.FStar_Ident.str))
in ((uu____13912), (Some ("inversion axiom")), (uu____13935))))
in FStar_SMTEncoding_Term.Assume (uu____13908))
in (uu____13907)::[])))
end
| uu____13937 -> begin
[]
end))
in (FStar_List.append decls (FStar_List.append ((fuel_guarded_inversion)::[]) pattern_guarded_inversion))))
end))
end))
end))
end)))
in (

let uu____13938 = (

let uu____13946 = (

let uu____13947 = (FStar_Syntax_Subst.compress k)
in uu____13947.FStar_Syntax_Syntax.n)
in (match (uu____13946) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
(((FStar_List.append tps formals)), ((FStar_Syntax_Util.comp_result kres)))
end
| uu____13976 -> begin
((tps), (k))
end))
in (match (uu____13938) with
| (formals, res) -> begin
(

let uu____13991 = (FStar_Syntax_Subst.open_term formals res)
in (match (uu____13991) with
| (formals1, res1) -> begin
(

let uu____13998 = (encode_binders None formals1 env)
in (match (uu____13998) with
| (vars, guards, env', binder_decls, uu____14013) -> begin
(

let uu____14020 = (new_term_constant_and_tok_from_lid env t)
in (match (uu____14020) with
| (tname, ttok, env1) -> begin
(

let ttok_tm = (FStar_SMTEncoding_Util.mkApp ((ttok), ([])))
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let tapp = (

let uu____14033 = (

let uu____14037 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((tname), (uu____14037)))
in (FStar_SMTEncoding_Util.mkApp uu____14033))
in (

let uu____14042 = (

let tname_decl = (

let uu____14048 = (

let uu____14049 = (FStar_All.pipe_right vars (FStar_List.map (fun uu____14064 -> (match (uu____14064) with
| (n1, s) -> begin
(((Prims.strcat tname n1)), (s), (false))
end))))
in (

let uu____14072 = (varops.next_id ())
in ((tname), (uu____14049), (FStar_SMTEncoding_Term.Term_sort), (uu____14072), (false))))
in (constructor_or_logic_type_decl uu____14048))
in (

let uu____14077 = (match (vars) with
| [] -> begin
(

let uu____14084 = (

let uu____14085 = (

let uu____14087 = (FStar_SMTEncoding_Util.mkApp ((tname), ([])))
in (FStar_All.pipe_left (fun _0_38 -> Some (_0_38)) uu____14087))
in (push_free_var env1 t tname uu____14085))
in (([]), (uu____14084)))
end
| uu____14091 -> begin
(

let ttok_decl = FStar_SMTEncoding_Term.DeclFun (((ttok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("token"))))
in (

let ttok_fresh = (

let uu____14097 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ttok), (FStar_SMTEncoding_Term.Term_sort)) uu____14097))
in (

let ttok_app = (mk_Apply ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (

let uu____14106 = (

let uu____14110 = (

let uu____14111 = (

let uu____14119 = (FStar_SMTEncoding_Util.mkEq ((ttok_app), (tapp)))
in ((pats), (None), (vars), (uu____14119)))
in (FStar_SMTEncoding_Util.mkForall' uu____14111))
in ((uu____14110), (Some ("name-token correspondence")), ((Prims.strcat "token_correspondence_" ttok))))
in FStar_SMTEncoding_Term.Assume (uu____14106))
in (((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[]), (env1)))))))
end)
in (match (uu____14077) with
| (tok_decls, env2) -> begin
(((FStar_List.append tname_decl tok_decls)), (env2))
end)))
in (match (uu____14042) with
| (decls, env2) -> begin
(

let kindingAx = (

let uu____14142 = (encode_term_pred None res1 env' tapp)
in (match (uu____14142) with
| (k1, decls1) -> begin
(

let karr = (match (((FStar_List.length formals1) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____14156 = (

let uu____14157 = (

let uu____14161 = (

let uu____14162 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____14162))
in ((uu____14161), (Some ("kinding")), ((Prims.strcat "pre_kinding_" ttok))))
in FStar_SMTEncoding_Term.Assume (uu____14157))
in (uu____14156)::[])
end
| uu____14164 -> begin
[]
end)
in (

let uu____14165 = (

let uu____14167 = (

let uu____14169 = (

let uu____14170 = (

let uu____14174 = (

let uu____14175 = (

let uu____14181 = (FStar_SMTEncoding_Util.mkImp ((guard), (k1)))
in ((((tapp)::[])::[]), (vars), (uu____14181)))
in (FStar_SMTEncoding_Util.mkForall uu____14175))
in ((uu____14174), (None), ((Prims.strcat "kinding_" ttok))))
in FStar_SMTEncoding_Term.Assume (uu____14170))
in (uu____14169)::[])
in (FStar_List.append karr uu____14167))
in (FStar_List.append decls1 uu____14165)))
end))
in (

let aux = (

let uu____14190 = (

let uu____14192 = (inversion_axioms tapp vars)
in (

let uu____14194 = (

let uu____14196 = (pretype_axiom env2 tapp vars)
in (uu____14196)::[])
in (FStar_List.append uu____14192 uu____14194)))
in (FStar_List.append kindingAx uu____14190))
in (

let g = (FStar_List.append decls (FStar_List.append binder_decls aux))
in ((g), (env2)))))
end)))))
end))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____14201, uu____14202, uu____14203, uu____14204, uu____14205, uu____14206) when (FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____14213, t, uu____14215, n_tps, quals, uu____14218) -> begin
(

let uu____14223 = (new_term_constant_and_tok_from_lid env d)
in (match (uu____14223) with
| (ddconstrsym, ddtok, env1) -> begin
(

let ddtok_tm = (FStar_SMTEncoding_Util.mkApp ((ddtok), ([])))
in (

let uu____14234 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____14234) with
| (formals, t_res) -> begin
(

let uu____14256 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____14256) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (

let uu____14265 = (encode_binders (Some (fuel_tm)) formals env1)
in (match (uu____14265) with
| (vars, guards, env', binder_decls, names1) -> begin
(

let fields = (FStar_All.pipe_right names1 (FStar_List.mapi (fun n1 x -> (

let projectible = true
in (

let uu____14303 = (mk_term_projector_name d x)
in ((uu____14303), (FStar_SMTEncoding_Term.Term_sort), (projectible)))))))
in (

let datacons = (

let uu____14305 = (

let uu____14315 = (varops.next_id ())
in ((ddconstrsym), (fields), (FStar_SMTEncoding_Term.Term_sort), (uu____14315), (true)))
in (FStar_All.pipe_right uu____14305 FStar_SMTEncoding_Term.constructor_to_decl))
in (

let app = (mk_Apply ddtok_tm vars)
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (

let uu____14337 = (encode_term_pred None t env1 ddtok_tm)
in (match (uu____14337) with
| (tok_typing, decls3) -> begin
(

let tok_typing1 = (match (fields) with
| (uu____14345)::uu____14346 -> begin
(

let ff = (("ty"), (FStar_SMTEncoding_Term.Term_sort))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV ff)
in (

let vtok_app_l = (mk_Apply ddtok_tm ((ff)::[]))
in (

let vtok_app_r = (mk_Apply f ((((ddtok), (FStar_SMTEncoding_Term.Term_sort)))::[]))
in (

let uu____14371 = (

let uu____14377 = (FStar_SMTEncoding_Term.mk_NoHoist f tok_typing)
in ((((vtok_app_l)::[])::((vtok_app_r)::[])::[]), ((ff)::[]), (uu____14377)))
in (FStar_SMTEncoding_Util.mkForall uu____14371))))))
end
| uu____14390 -> begin
tok_typing
end)
in (

let uu____14395 = (encode_binders (Some (fuel_tm)) formals env1)
in (match (uu____14395) with
| (vars', guards', env'', decls_formals, uu____14410) -> begin
(

let uu____14417 = (

let xvars1 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars')
in (

let dapp1 = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars1)))
in (encode_term_pred (Some (fuel_tm)) t_res env'' dapp1)))
in (match (uu____14417) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_SMTEncoding_Util.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| uu____14436 -> begin
(

let uu____14440 = (

let uu____14441 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ddtok), (FStar_SMTEncoding_Term.Term_sort)) uu____14441))
in (uu____14440)::[])
end)
in (

let encode_elim = (fun uu____14448 -> (

let uu____14449 = (FStar_Syntax_Util.head_and_args t_res)
in (match (uu____14449) with
| (head1, args) -> begin
(

let uu____14478 = (

let uu____14479 = (FStar_Syntax_Subst.compress head1)
in uu____14479.FStar_Syntax_Syntax.n)
in (match (uu____14478) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let uu____14497 = (encode_args args env')
in (match (uu____14497) with
| (encoded_args, arg_decls) -> begin
(

let guards_for_parameter = (fun arg xv -> (

let fv1 = (match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv1) -> begin
fv1
end
| uu____14523 -> begin
(failwith "Impossible: parameter must be a variable")
end)
in (

let guards1 = (FStar_All.pipe_right guards (FStar_List.collect (fun g -> (

let uu____14531 = (

let uu____14532 = (FStar_SMTEncoding_Term.free_variables g)
in (FStar_List.contains fv1 uu____14532))
in (match (uu____14531) with
| true -> begin
(

let uu____14539 = (FStar_SMTEncoding_Term.subst g fv1 xv)
in (uu____14539)::[])
end
| uu____14540 -> begin
[]
end)))))
in (FStar_SMTEncoding_Util.mk_and_l guards1))))
in (

let uu____14541 = (FStar_List.fold_left (fun uu____14554 arg -> (match (uu____14554) with
| (env2, arg_vars, eqns_or_guards, i) -> begin
(

let uu____14576 = (

let uu____14580 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in (gen_term_var env2 uu____14580))
in (match (uu____14576) with
| (uu____14587, xv, env3) -> begin
(

let eqns = (match ((i < n_tps)) with
| true -> begin
(

let uu____14593 = (guards_for_parameter arg xv)
in (uu____14593)::eqns_or_guards)
end
| uu____14594 -> begin
(

let uu____14595 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (uu____14595)::eqns_or_guards)
end)
in ((env3), ((xv)::arg_vars), (eqns), ((i + (Prims.parse_int "1")))))
end))
end)) ((env'), ([]), ([]), ((Prims.parse_int "0"))) encoded_args)
in (match (uu____14541) with
| (uu____14603, arg_vars, elim_eqns_or_guards, uu____14606) -> begin
(

let arg_vars1 = (FStar_List.rev arg_vars)
in (

let ty = (FStar_SMTEncoding_Util.mkApp ((encoded_head), (arg_vars1)))
in (

let xvars1 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp1 = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars1)))
in (

let ty_pred = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp1 ty)
in (

let arg_binders = (FStar_List.map FStar_SMTEncoding_Term.fv_of_term arg_vars1)
in (

let typing_inversion = (

let uu____14625 = (

let uu____14629 = (

let uu____14630 = (

let uu____14636 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____14642 = (

let uu____14643 = (

let uu____14646 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append elim_eqns_or_guards guards))
in ((ty_pred), (uu____14646)))
in (FStar_SMTEncoding_Util.mkImp uu____14643))
in ((((ty_pred)::[])::[]), (uu____14636), (uu____14642))))
in (FStar_SMTEncoding_Util.mkForall uu____14630))
in ((uu____14629), (Some ("data constructor typing elim")), ((Prims.strcat "data_elim_" ddconstrsym))))
in FStar_SMTEncoding_Term.Assume (uu____14625))
in (

let subterm_ordering = (match ((FStar_Ident.lid_equals d FStar_Syntax_Const.lextop_lid)) with
| true -> begin
(

let x = (

let uu____14659 = (varops.fresh "x")
in ((uu____14659), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (

let uu____14661 = (

let uu____14665 = (

let uu____14666 = (

let uu____14672 = (

let uu____14675 = (

let uu____14677 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in (uu____14677)::[])
in (uu____14675)::[])
in (

let uu____14680 = (

let uu____14681 = (

let uu____14684 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (

let uu____14685 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in ((uu____14684), (uu____14685))))
in (FStar_SMTEncoding_Util.mkImp uu____14681))
in ((uu____14672), ((x)::[]), (uu____14680))))
in (FStar_SMTEncoding_Util.mkForall uu____14666))
in (

let uu____14695 = (varops.mk_unique "lextop")
in ((uu____14665), (Some ("lextop is top")), (uu____14695))))
in FStar_SMTEncoding_Term.Assume (uu____14661))))
end
| uu____14697 -> begin
(

let prec = (

let uu____14700 = (FStar_All.pipe_right vars (FStar_List.mapi (fun i v1 -> (match ((i < n_tps)) with
| true -> begin
[]
end
| uu____14714 -> begin
(

let uu____14715 = (

let uu____14716 = (FStar_SMTEncoding_Util.mkFreeV v1)
in (FStar_SMTEncoding_Util.mk_Precedes uu____14716 dapp1))
in (uu____14715)::[])
end))))
in (FStar_All.pipe_right uu____14700 FStar_List.flatten))
in (

let uu____14720 = (

let uu____14724 = (

let uu____14725 = (

let uu____14731 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____14737 = (

let uu____14738 = (

let uu____14741 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (uu____14741)))
in (FStar_SMTEncoding_Util.mkImp uu____14738))
in ((((ty_pred)::[])::[]), (uu____14731), (uu____14737))))
in (FStar_SMTEncoding_Util.mkForall uu____14725))
in ((uu____14724), (Some ("subterm ordering")), ((Prims.strcat "subterm_ordering_" ddconstrsym))))
in FStar_SMTEncoding_Term.Assume (uu____14720)))
end)
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end)))
end)))
end
| uu____14751 -> begin
((

let uu____14753 = (

let uu____14754 = (FStar_Syntax_Print.lid_to_string d)
in (

let uu____14755 = (FStar_Syntax_Print.term_to_string head1)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" uu____14754 uu____14755)))
in (FStar_Errors.warn se.FStar_Syntax_Syntax.sigrng uu____14753));
(([]), ([]));
)
end))
end)))
in (

let uu____14758 = (encode_elim ())
in (match (uu____14758) with
| (decls2, elim) -> begin
(

let g = (

let uu____14770 = (

let uu____14772 = (

let uu____14774 = (

let uu____14776 = (

let uu____14778 = (

let uu____14779 = (

let uu____14785 = (

let uu____14787 = (

let uu____14788 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" uu____14788))
in Some (uu____14787))
in ((ddtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (uu____14785)))
in FStar_SMTEncoding_Term.DeclFun (uu____14779))
in (uu____14778)::[])
in (

let uu____14791 = (

let uu____14793 = (

let uu____14795 = (

let uu____14797 = (

let uu____14799 = (

let uu____14801 = (

let uu____14803 = (

let uu____14804 = (

let uu____14808 = (

let uu____14809 = (

let uu____14815 = (FStar_SMTEncoding_Util.mkEq ((app), (dapp)))
in ((((app)::[])::[]), (vars), (uu____14815)))
in (FStar_SMTEncoding_Util.mkForall uu____14809))
in ((uu____14808), (Some ("equality for proxy")), ((Prims.strcat "equality_tok_" ddtok))))
in FStar_SMTEncoding_Term.Assume (uu____14804))
in (

let uu____14822 = (

let uu____14824 = (

let uu____14825 = (

let uu____14829 = (

let uu____14830 = (

let uu____14836 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) vars')
in (

let uu____14842 = (FStar_SMTEncoding_Util.mkImp ((guard'), (ty_pred')))
in ((((ty_pred')::[])::[]), (uu____14836), (uu____14842))))
in (FStar_SMTEncoding_Util.mkForall uu____14830))
in ((uu____14829), (Some ("data constructor typing intro")), ((Prims.strcat "data_typing_intro_" ddtok))))
in FStar_SMTEncoding_Term.Assume (uu____14825))
in (uu____14824)::[])
in (uu____14803)::uu____14822))
in (FStar_SMTEncoding_Term.Assume (((tok_typing1), (Some ("typing for data constructor proxy")), ((Prims.strcat "typing_tok_" ddtok)))))::uu____14801)
in (FStar_List.append uu____14799 elim))
in (FStar_List.append decls_pred uu____14797))
in (FStar_List.append decls_formals uu____14795))
in (FStar_List.append proxy_fresh uu____14793))
in (FStar_List.append uu____14776 uu____14791)))
in (FStar_List.append decls3 uu____14774))
in (FStar_List.append decls2 uu____14772))
in (FStar_List.append binder_decls uu____14770))
in (((FStar_List.append datacons g)), (env1)))
end)))))
end))
end)))
end))))))))
end)))
end))
end)))
end))
end))
and encode_signature : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun uu____14863 se -> (match (uu____14863) with
| (g, env1) -> begin
(

let uu____14875 = (encode_sigelt env1 se)
in (match (uu____14875) with
| (g', env2) -> begin
(((FStar_List.append g g')), (env2))
end))
end)) (([]), (env)))))


let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env bindings -> (

let encode_binding = (fun b uu____14911 -> (match (uu____14911) with
| (i, decls, env1) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (uu____14929) -> begin
(((i + (Prims.parse_int "1"))), ([]), (env1))
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env1.tcenv x.FStar_Syntax_Syntax.sort)
in ((

let uu____14934 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____14934) with
| true -> begin
(

let uu____14935 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____14936 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____14937 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" uu____14935 uu____14936 uu____14937))))
end
| uu____14938 -> begin
()
end));
(

let uu____14939 = (encode_term t1 env1)
in (match (uu____14939) with
| (t, decls') -> begin
(

let t_hash = (FStar_SMTEncoding_Term.hash_of_term t)
in (

let uu____14949 = (

let uu____14953 = (

let uu____14954 = (

let uu____14955 = (FStar_Util.digest_of_string t_hash)
in (Prims.strcat uu____14955 (Prims.strcat "_" (Prims.string_of_int i))))
in (Prims.strcat "x_" uu____14954))
in (new_term_constant_from_string env1 x uu____14953))
in (match (uu____14949) with
| (xxsym, xx, env') -> begin
(

let t2 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel None xx t)
in (

let caption = (

let uu____14966 = (FStar_Options.log_queries ())
in (match (uu____14966) with
| true -> begin
(

let uu____14968 = (

let uu____14969 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____14970 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____14971 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" uu____14969 uu____14970 uu____14971))))
in Some (uu____14968))
end
| uu____14972 -> begin
None
end))
in (

let ax = (

let a_name = (Prims.strcat "binder_" xxsym)
in FStar_SMTEncoding_Term.Assume (((t2), (Some (a_name)), (a_name))))
in (

let g = (FStar_List.append ((FStar_SMTEncoding_Term.DeclFun (((xxsym), ([]), (FStar_SMTEncoding_Term.Term_sort), (caption))))::[]) (FStar_List.append decls' ((ax)::[])))
in (((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))))))
end)))
end));
))
end
| FStar_TypeChecker_Env.Binding_lid (x, (uu____14982, t)) -> begin
(

let t_norm = (whnf env1 t)
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____14991 = (encode_free_var env1 fv t t_norm [])
in (match (uu____14991) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))))
end
| (FStar_TypeChecker_Env.Binding_sig_inst (_, se, _)) | (FStar_TypeChecker_Env.Binding_sig (_, se)) -> begin
(

let uu____15010 = (encode_sigelt env1 se)
in (match (uu____15010) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))
end)
end))
in (

let uu____15020 = (FStar_List.fold_right encode_binding bindings (((Prims.parse_int "0")), ([]), (env)))
in (match (uu____15020) with
| (uu____15032, decls, env1) -> begin
((decls), (env1))
end))))


let encode_labels = (fun labs -> (

let prefix1 = (FStar_All.pipe_right labs (FStar_List.map (fun uu____15077 -> (match (uu____15077) with
| (l, uu____15084, uu____15085) -> begin
FStar_SMTEncoding_Term.DeclFun ((((Prims.fst l)), ([]), (FStar_SMTEncoding_Term.Bool_sort), (None)))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun uu____15106 -> (match (uu____15106) with
| (l, uu____15114, uu____15115) -> begin
(

let uu____15120 = (FStar_All.pipe_left (fun _0_39 -> FStar_SMTEncoding_Term.Echo (_0_39)) (Prims.fst l))
in (

let uu____15121 = (

let uu____15123 = (

let uu____15124 = (FStar_SMTEncoding_Util.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (uu____15124))
in (uu____15123)::[])
in (uu____15120)::uu____15121))
end))))
in ((prefix1), (suffix)))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (

let uu____15135 = (

let uu____15137 = (

let uu____15138 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (

let uu____15150 = (

let uu____15151 = (FStar_TypeChecker_Env.current_module tcenv)
in (FStar_All.pipe_right uu____15151 FStar_Ident.string_of_lid))
in {bindings = []; depth = (Prims.parse_int "0"); tcenv = tcenv; warn = true; cache = uu____15138; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true; current_module_name = uu____15150}))
in (uu____15137)::[])
in (FStar_ST.write last_env uu____15135)))


let get_env : FStar_Ident.lident  ->  FStar_TypeChecker_Env.env  ->  env_t = (fun cmn tcenv -> (

let uu____15161 = (FStar_ST.read last_env)
in (match (uu____15161) with
| [] -> begin
(failwith "No env; call init first!")
end
| (e)::uu____15167 -> begin
(

let uu___163_15169 = e
in (

let uu____15170 = (FStar_Ident.string_of_lid cmn)
in {bindings = uu___163_15169.bindings; depth = uu___163_15169.depth; tcenv = tcenv; warn = uu___163_15169.warn; cache = uu___163_15169.cache; nolabels = uu___163_15169.nolabels; use_zfuel_name = uu___163_15169.use_zfuel_name; encode_non_total_function_typ = uu___163_15169.encode_non_total_function_typ; current_module_name = uu____15170}))
end)))


let set_env : env_t  ->  Prims.unit = (fun env -> (

let uu____15174 = (FStar_ST.read last_env)
in (match (uu____15174) with
| [] -> begin
(failwith "Empty env stack")
end
| (uu____15179)::tl1 -> begin
(FStar_ST.write last_env ((env)::tl1))
end)))


let push_env : Prims.unit  ->  Prims.unit = (fun uu____15187 -> (

let uu____15188 = (FStar_ST.read last_env)
in (match (uu____15188) with
| [] -> begin
(failwith "Empty env stack")
end
| (hd1)::tl1 -> begin
(

let refs = (FStar_Util.smap_copy hd1.cache)
in (

let top = (

let uu___164_15209 = hd1
in {bindings = uu___164_15209.bindings; depth = uu___164_15209.depth; tcenv = uu___164_15209.tcenv; warn = uu___164_15209.warn; cache = refs; nolabels = uu___164_15209.nolabels; use_zfuel_name = uu___164_15209.use_zfuel_name; encode_non_total_function_typ = uu___164_15209.encode_non_total_function_typ; current_module_name = uu___164_15209.current_module_name})
in (FStar_ST.write last_env ((top)::(hd1)::tl1))))
end)))


let pop_env : Prims.unit  ->  Prims.unit = (fun uu____15215 -> (

let uu____15216 = (FStar_ST.read last_env)
in (match (uu____15216) with
| [] -> begin
(failwith "Popping an empty stack")
end
| (uu____15221)::tl1 -> begin
(FStar_ST.write last_env tl1)
end)))


let mark_env : Prims.unit  ->  Prims.unit = (fun uu____15229 -> (push_env ()))


let reset_mark_env : Prims.unit  ->  Prims.unit = (fun uu____15232 -> (pop_env ()))


let commit_mark_env : Prims.unit  ->  Prims.unit = (fun uu____15235 -> (

let uu____15236 = (FStar_ST.read last_env)
in (match (uu____15236) with
| (hd1)::(uu____15242)::tl1 -> begin
(FStar_ST.write last_env ((hd1)::tl1))
end
| uu____15248 -> begin
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

let uu____15293 = (FStar_Options.log_queries ())
in (match (uu____15293) with
| true -> begin
(

let uu____15295 = (

let uu____15296 = (

let uu____15297 = (

let uu____15298 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.map FStar_Syntax_Print.lid_to_string))
in (FStar_All.pipe_right uu____15298 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " uu____15297))
in FStar_SMTEncoding_Term.Caption (uu____15296))
in (uu____15295)::decls)
end
| uu____15303 -> begin
decls
end)))
in (

let env = (

let uu____15305 = (FStar_TypeChecker_Env.current_module tcenv)
in (get_env uu____15305 tcenv))
in (

let uu____15306 = (encode_sigelt env se)
in (match (uu____15306) with
| (decls, env1) -> begin
((set_env env1);
(

let uu____15312 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 uu____15312));
)
end)))))


let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____15321 -> begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in ((

let uu____15323 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____15323) with
| true -> begin
(

let uu____15324 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) Prims.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name uu____15324))
end
| uu____15327 -> begin
()
end));
(

let env = (get_env modul.FStar_Syntax_Syntax.name tcenv)
in (

let uu____15329 = (encode_signature (

let uu___165_15333 = env
in {bindings = uu___165_15333.bindings; depth = uu___165_15333.depth; tcenv = uu___165_15333.tcenv; warn = false; cache = uu___165_15333.cache; nolabels = uu___165_15333.nolabels; use_zfuel_name = uu___165_15333.use_zfuel_name; encode_non_total_function_typ = uu___165_15333.encode_non_total_function_typ; current_module_name = uu___165_15333.current_module_name}) modul.FStar_Syntax_Syntax.exports)
in (match (uu____15329) with
| (decls, env1) -> begin
(

let caption = (fun decls1 -> (

let uu____15345 = (FStar_Options.log_queries ())
in (match (uu____15345) with
| true -> begin
(

let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::decls1) ((FStar_SMTEncoding_Term.Caption ((Prims.strcat "End " msg)))::[])))
end
| uu____15348 -> begin
decls1
end)))
in ((set_env (

let uu___166_15350 = env1
in {bindings = uu___166_15350.bindings; depth = uu___166_15350.depth; tcenv = uu___166_15350.tcenv; warn = true; cache = uu___166_15350.cache; nolabels = uu___166_15350.nolabels; use_zfuel_name = uu___166_15350.use_zfuel_name; encode_non_total_function_typ = uu___166_15350.encode_non_total_function_typ; current_module_name = uu___166_15350.current_module_name}));
(

let uu____15352 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____15352) with
| true -> begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end
| uu____15353 -> begin
()
end));
(

let decls1 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls1));
))
end)));
)))


let encode_query : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_ErrorReporting.label Prims.list * FStar_SMTEncoding_Term.decl * FStar_SMTEncoding_Term.decl Prims.list) = (fun use_env_msg tcenv q -> ((

let uu____15387 = (

let uu____15388 = (FStar_TypeChecker_Env.current_module tcenv)
in uu____15388.FStar_Ident.str)
in (FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name uu____15387));
(

let env = (

let uu____15390 = (FStar_TypeChecker_Env.current_module tcenv)
in (get_env uu____15390 tcenv))
in (

let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (

let uu____15397 = (

let rec aux = (fun bindings1 -> (match (bindings1) with
| (FStar_TypeChecker_Env.Binding_var (x))::rest -> begin
(

let uu____15418 = (aux rest)
in (match (uu____15418) with
| (out, rest1) -> begin
(

let t = (

let uu____15436 = (FStar_Syntax_Util.destruct_typ_as_formula x.FStar_Syntax_Syntax.sort)
in (match (uu____15436) with
| Some (uu____15440) -> begin
(

let uu____15441 = (FStar_Syntax_Syntax.new_bv None FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.refine uu____15441 x.FStar_Syntax_Syntax.sort))
end
| uu____15442 -> begin
x.FStar_Syntax_Syntax.sort
end))
in (

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
in (

let uu____15445 = (

let uu____15447 = (FStar_Syntax_Syntax.mk_binder (

let uu___167_15448 = x
in {FStar_Syntax_Syntax.ppname = uu___167_15448.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___167_15448.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in (uu____15447)::out)
in ((uu____15445), (rest1)))))
end))
end
| uu____15451 -> begin
(([]), (bindings1))
end))
in (

let uu____15455 = (aux bindings)
in (match (uu____15455) with
| (closing, bindings1) -> begin
(

let uu____15469 = (FStar_Syntax_Util.close_forall_no_univs (FStar_List.rev closing) q)
in ((uu____15469), (bindings1)))
end)))
in (match (uu____15397) with
| (q1, bindings1) -> begin
(

let uu____15482 = (

let uu____15485 = (FStar_List.filter (fun uu___136_15487 -> (match (uu___136_15487) with
| FStar_TypeChecker_Env.Binding_sig (uu____15488) -> begin
false
end
| uu____15492 -> begin
true
end)) bindings1)
in (encode_env_bindings env uu____15485))
in (match (uu____15482) with
| (env_decls, env1) -> begin
((

let uu____15503 = (((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTQuery"))))
in (match (uu____15503) with
| true -> begin
(

let uu____15504 = (FStar_Syntax_Print.term_to_string q1)
in (FStar_Util.print1 "Encoding query formula: %s\n" uu____15504))
end
| uu____15505 -> begin
()
end));
(

let uu____15506 = (encode_formula q1 env1)
in (match (uu____15506) with
| (phi, qdecls) -> begin
(

let uu____15518 = (

let uu____15521 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg uu____15521 phi))
in (match (uu____15518) with
| (labels, phi1) -> begin
(

let uu____15531 = (encode_labels labels)
in (match (uu____15531) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append env_decls (FStar_List.append label_prefix qdecls))
in (

let qry = (

let uu____15552 = (

let uu____15556 = (FStar_SMTEncoding_Util.mkNot phi1)
in (

let uu____15557 = (varops.mk_unique "@query")
in ((uu____15556), (Some ("query")), (uu____15557))))
in FStar_SMTEncoding_Term.Assume (uu____15552))
in (

let suffix = (

let uu____15561 = (

let uu____15563 = (

let uu____15565 = (FStar_Options.print_z3_statistics ())
in (match (uu____15565) with
| true -> begin
(FStar_SMTEncoding_Term.PrintStats)::[]
end
| uu____15567 -> begin
[]
end))
in (FStar_List.append uu____15563 ((FStar_SMTEncoding_Term.Echo ("Done!"))::[])))
in (FStar_List.append label_suffix uu____15561))
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

let uu____15577 = (FStar_TypeChecker_Env.current_module tcenv)
in (get_env uu____15577 tcenv))
in ((FStar_SMTEncoding_Z3.push "query");
(

let uu____15579 = (encode_formula q env)
in (match (uu____15579) with
| (f, uu____15583) -> begin
((FStar_SMTEncoding_Z3.pop "query");
(match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____15585) -> begin
true
end
| uu____15588 -> begin
false
end);
)
end));
)))




