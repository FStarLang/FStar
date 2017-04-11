
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


let vargs = (fun args -> (FStar_List.filter (fun uu___111_74 -> (match (uu___111_74) with
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

let uu___135_140 = a
in (

let uu____141 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = uu____141; FStar_Syntax_Syntax.index = uu___135_140.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___135_140.FStar_Syntax_Syntax.sort}))
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

let uu___136_780 = x
in (

let uu____781 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = uu____781; FStar_Syntax_Syntax.index = uu___136_780.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___136_780.FStar_Syntax_Syntax.sort})))

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

let uu____952 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun uu___112_956 -> (match (uu___112_956) with
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

let uu___137_1020 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = (env.depth + (Prims.parse_int "1")); tcenv = uu___137_1020.tcenv; warn = uu___137_1020.warn; cache = uu___137_1020.cache; nolabels = uu___137_1020.nolabels; use_zfuel_name = uu___137_1020.use_zfuel_name; encode_non_total_function_typ = uu___137_1020.encode_non_total_function_typ; current_module_name = uu___137_1020.current_module_name}))))))


let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let uu___138_1033 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = uu___138_1033.depth; tcenv = uu___138_1033.tcenv; warn = uu___138_1033.warn; cache = uu___138_1033.cache; nolabels = uu___138_1033.nolabels; use_zfuel_name = uu___138_1033.use_zfuel_name; encode_non_total_function_typ = uu___138_1033.encode_non_total_function_typ; current_module_name = uu___138_1033.current_module_name}))))))


let new_term_constant_from_string : env_t  ->  FStar_Syntax_Syntax.bv  ->  Prims.string  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x str -> (

let ysym = (varops.mk_unique str)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let uu___139_1049 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = uu___139_1049.depth; tcenv = uu___139_1049.tcenv; warn = uu___139_1049.warn; cache = uu___139_1049.cache; nolabels = uu___139_1049.nolabels; use_zfuel_name = uu___139_1049.use_zfuel_name; encode_non_total_function_typ = uu___139_1049.encode_non_total_function_typ; current_module_name = uu___139_1049.current_module_name}))))))


let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (

let uu___140_1059 = env
in {bindings = (Binding_var (((x), (t))))::env.bindings; depth = uu___140_1059.depth; tcenv = uu___140_1059.tcenv; warn = uu___140_1059.warn; cache = uu___140_1059.cache; nolabels = uu___140_1059.nolabels; use_zfuel_name = uu___140_1059.use_zfuel_name; encode_non_total_function_typ = uu___140_1059.encode_non_total_function_typ; current_module_name = uu___140_1059.current_module_name}))


let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let aux = (fun a' -> (lookup_binding env (fun uu___113_1075 -> (match (uu___113_1075) with
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

let uu___141_1122 = env
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
in {bindings = uu____1123; depth = uu___141_1122.depth; tcenv = uu___141_1122.tcenv; warn = uu___141_1122.warn; cache = uu___141_1122.cache; nolabels = uu___141_1122.nolabels; use_zfuel_name = uu___141_1122.use_zfuel_name; encode_non_total_function_typ = uu___141_1122.encode_non_total_function_typ; current_module_name = uu___141_1122.current_module_name}))
in ((fname), (ftok), (uu____1121))))))


let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun uu___114_1157 -> (match (uu___114_1157) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some (((t1), (t2), (t3)))
end
| uu____1179 -> begin
None
end))))


let contains_name : env_t  ->  Prims.string  ->  Prims.bool = (fun env s -> (

let uu____1191 = (lookup_binding env (fun uu___115_1193 -> (match (uu___115_1193) with
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

let uu___142_1265 = env
in {bindings = (Binding_fvar (((x), (fname), (ftok), (None))))::env.bindings; depth = uu___142_1265.depth; tcenv = uu___142_1265.tcenv; warn = uu___142_1265.warn; cache = uu___142_1265.cache; nolabels = uu___142_1265.nolabels; use_zfuel_name = uu___142_1265.use_zfuel_name; encode_non_total_function_typ = uu___142_1265.encode_non_total_function_typ; current_module_name = uu___142_1265.current_module_name}))


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

let uu___143_1300 = env
in {bindings = (Binding_fvar (((x), (t1), (t2), (Some (t3)))))::env.bindings; depth = uu___143_1300.depth; tcenv = uu___143_1300.tcenv; warn = uu___143_1300.warn; cache = uu___143_1300.cache; nolabels = uu___143_1300.nolabels; use_zfuel_name = uu___143_1300.use_zfuel_name; encode_non_total_function_typ = uu___143_1300.encode_non_total_function_typ; current_module_name = uu___143_1300.current_module_name}))
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


let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun uu___116_1478 -> (match (uu___116_1478) with
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
(((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid)) || (FStar_List.existsb (fun uu___117_1663 -> (match (uu___117_1663) with
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


let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun uu___118_1768 -> (match (uu___118_1768) with
| (FStar_SMTEncoding_Term.Var ("ApplyTT")) | (FStar_SMTEncoding_Term.Var ("ApplyTF")) -> begin
true
end
| uu____1769 -> begin
false
end))


let is_an_eta_expansion : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env vars body -> (

let rec aux = (fun t xs -> (match (((t.FStar_SMTEncoding_Term.tm), (xs))) with
| (FStar_SMTEncoding_Term.App (app, (f)::({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.freevars = uu____1797; FStar_SMTEncoding_Term.rng = uu____1798})::[]), (x)::xs1) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(aux f xs1)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), uu____1812) -> begin
(

let uu____1817 = (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v1 -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v1)
end
| uu____1827 -> begin
false
end)) args vars))
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
in (aux body (FStar_List.rev vars))))


let reify_body : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let tm = (FStar_Syntax_Util.mk_reify t)
in (

let tm' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env tm)
in ((

let uu____1853 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____1853) with
| true -> begin
(

let uu____1854 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____1855 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print2 "Reified body %s \nto %s\n" uu____1854 uu____1855)))
end
| uu____1856 -> begin
()
end));
tm';
))))


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
| uu____1937 -> begin
false
end))


let encode_const : FStar_Const.sconst  ->  FStar_SMTEncoding_Term.term = (fun uu___119_1940 -> (match (uu___119_1940) with
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

let uu____1942 = (

let uu____1946 = (

let uu____1948 = (

let uu____1949 = (FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c))
in (FStar_SMTEncoding_Term.boxInt uu____1949))
in (uu____1948)::[])
in (("FStar.Char.Char"), (uu____1946)))
in (FStar_SMTEncoding_Util.mkApp uu____1942))
end
| FStar_Const.Const_int (i, None) -> begin
(

let uu____1957 = (FStar_SMTEncoding_Util.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt uu____1957))
end
| FStar_Const.Const_int (i, Some (uu____1959)) -> begin
(failwith "Machine integers should be desugared")
end
| FStar_Const.Const_string (bytes, uu____1968) -> begin
(

let uu____1971 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const uu____1971))
end
| FStar_Const.Const_range (r) -> begin
FStar_SMTEncoding_Term.mk_Range_const
end
| FStar_Const.Const_effect -> begin
FStar_SMTEncoding_Term.mk_Term_type
end
| c -> begin
(

let uu____1975 = (

let uu____1976 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" uu____1976))
in (failwith uu____1975))
end))


let as_function_typ : env_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (

let rec aux = (fun norm1 t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1995) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_refine (uu____2003) -> begin
(

let uu____2008 = (FStar_Syntax_Util.unrefine t1)
in (aux true uu____2008))
end
| uu____2009 -> begin
(match (norm1) with
| true -> begin
(

let uu____2010 = (whnf env t1)
in (aux false uu____2010))
end
| uu____2011 -> begin
(

let uu____2012 = (

let uu____2013 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (

let uu____2014 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" uu____2013 uu____2014)))
in (failwith uu____2012))
end)
end)))
in (aux true t0)))


let curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun k -> (

let k1 = (FStar_Syntax_Subst.compress k)
in (match (k1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| uu____2035 -> begin
(

let uu____2036 = (FStar_Syntax_Syntax.mk_Total k1)
in (([]), (uu____2036)))
end)))


let rec encode_binders : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> ((

let uu____2179 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____2179) with
| true -> begin
(

let uu____2180 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" uu____2180))
end
| uu____2181 -> begin
()
end));
(

let uu____2182 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____2218 b -> (match (uu____2218) with
| (vars, guards, env1, decls, names1) -> begin
(

let uu____2261 = (

let x = (unmangle (Prims.fst b))
in (

let uu____2270 = (gen_term_var env1 x)
in (match (uu____2270) with
| (xxsym, xx, env') -> begin
(

let uu____2284 = (

let uu____2287 = (norm env1 x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt uu____2287 env1 xx))
in (match (uu____2284) with
| (guard_x_t, decls') -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (guard_x_t), (env'), (decls'), (x))
end))
end)))
in (match (uu____2261) with
| (v1, g, env2, decls', n1) -> begin
(((v1)::vars), ((g)::guards), (env2), ((FStar_List.append decls decls')), ((n1)::names1))
end))
end)) (([]), ([]), (env), ([]), ([]))))
in (match (uu____2182) with
| (vars, guards, env1, decls, names1) -> begin
(((FStar_List.rev vars)), ((FStar_List.rev guards)), (env1), (decls), ((FStar_List.rev names1)))
end));
))
and encode_term_pred : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let uu____2375 = (encode_term t env)
in (match (uu____2375) with
| (t1, decls) -> begin
(

let uu____2382 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1)
in ((uu____2382), (decls)))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let uu____2390 = (encode_term t env)
in (match (uu____2390) with
| (t1, decls) -> begin
(match (fuel_opt) with
| None -> begin
(

let uu____2399 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t1)
in ((uu____2399), (decls)))
end
| Some (f) -> begin
(

let uu____2401 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1)
in ((uu____2401), (decls)))
end)
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let t0 = (FStar_Syntax_Subst.compress t)
in ((

let uu____2408 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____2408) with
| true -> begin
(

let uu____2409 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____2410 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____2411 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" uu____2409 uu____2410 uu____2411))))
end
| uu____2412 -> begin
()
end));
(match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(

let uu____2416 = (

let uu____2417 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____2418 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____2419 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____2420 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2417 uu____2418 uu____2419 uu____2420)))))
in (failwith uu____2416))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____2424 = (

let uu____2425 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" uu____2425))
in (failwith uu____2424))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, k, uu____2430) -> begin
(encode_term t1 env)
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____2460) -> begin
(encode_term t1 env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t1 = (lookup_term_var env x)
in ((t1), ([])))
end
| FStar_Syntax_Syntax.Tm_fvar (v1) -> begin
(

let uu____2469 = (lookup_free_var env v1.FStar_Syntax_Syntax.fv_name)
in ((uu____2469), ([])))
end
| FStar_Syntax_Syntax.Tm_type (uu____2475) -> begin
((FStar_SMTEncoding_Term.mk_Term_type), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____2478) -> begin
(encode_term t1 env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____2484 = (encode_const c)
in ((uu____2484), ([])))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let module_name = env.current_module_name
in (

let uu____2499 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____2499) with
| (binders1, res) -> begin
(

let uu____2506 = ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res))
in (match (uu____2506) with
| true -> begin
(

let uu____2509 = (encode_binders None binders1 env)
in (match (uu____2509) with
| (vars, guards, env', decls, uu____2524) -> begin
(

let fsym = (

let uu____2534 = (varops.fresh "f")
in ((uu____2534), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV fsym)
in (

let app = (mk_Apply f vars)
in (

let uu____2537 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post (

let uu___144_2541 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___144_2541.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___144_2541.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___144_2541.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___144_2541.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___144_2541.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___144_2541.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___144_2541.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___144_2541.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___144_2541.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___144_2541.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___144_2541.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___144_2541.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___144_2541.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___144_2541.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___144_2541.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___144_2541.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___144_2541.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___144_2541.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___144_2541.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___144_2541.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___144_2541.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___144_2541.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___144_2541.FStar_TypeChecker_Env.qname_and_index}) res)
in (match (uu____2537) with
| (pre_opt, res_t) -> begin
(

let uu____2548 = (encode_term_pred None res_t env' app)
in (match (uu____2548) with
| (res_pred, decls') -> begin
(

let uu____2555 = (match (pre_opt) with
| None -> begin
(

let uu____2562 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____2562), ([])))
end
| Some (pre) -> begin
(

let uu____2565 = (encode_formula pre env')
in (match (uu____2565) with
| (guard, decls0) -> begin
(

let uu____2573 = (FStar_SMTEncoding_Util.mk_and_l ((guard)::guards))
in ((uu____2573), (decls0)))
end))
end)
in (match (uu____2555) with
| (guards1, guard_decls) -> begin
(

let t_interp = (

let uu____2581 = (

let uu____2587 = (FStar_SMTEncoding_Util.mkImp ((guards1), (res_pred)))
in ((((app)::[])::[]), (vars), (uu____2587)))
in (FStar_SMTEncoding_Util.mkForall uu____2581))
in (

let cvars = (

let uu____2597 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right uu____2597 (FStar_List.filter (fun uu____2603 -> (match (uu____2603) with
| (x, uu____2607) -> begin
(x <> (Prims.fst fsym))
end)))))
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), ((fsym)::cvars), (t_interp)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____2618 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____2618) with
| Some (t', sorts, uu____2634) -> begin
(

let uu____2644 = (

let uu____2645 = (

let uu____2649 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((t'), (uu____2649)))
in (FStar_SMTEncoding_Util.mkApp uu____2645))
in ((uu____2644), ([])))
end
| None -> begin
(

let tsym = (

let uu____2665 = (

let uu____2666 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_arrow_" uu____2666))
in (varops.mk_unique uu____2665))
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let caption = (

let uu____2673 = (FStar_Options.log_queries ())
in (match (uu____2673) with
| true -> begin
(

let uu____2675 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in Some (uu____2675))
end
| uu____2676 -> begin
None
end))
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (caption)))
in (

let t1 = (

let uu____2681 = (

let uu____2685 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((tsym), (uu____2685)))
in (FStar_SMTEncoding_Util.mkApp uu____2681))
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t1 FStar_SMTEncoding_Term.mk_Term_type)
in (

let k_assumption = (

let a_name = (Prims.strcat "kinding_" tsym)
in (

let uu____2693 = (

let uu____2697 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((uu____2697), (Some (a_name)), (a_name)))
in FStar_SMTEncoding_Term.Assume (uu____2693)))
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t1)
in (

let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t1)
in (

let pre_typing = (

let a_name = (Prims.strcat "pre_typing_" tsym)
in (

let uu____2710 = (

let uu____2714 = (

let uu____2715 = (

let uu____2721 = (

let uu____2722 = (

let uu____2725 = (

let uu____2726 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____2726))
in ((f_has_t), (uu____2725)))
in (FStar_SMTEncoding_Util.mkImp uu____2722))
in ((((f_has_t)::[])::[]), ((fsym)::cvars), (uu____2721)))
in (mkForall_fuel uu____2715))
in ((uu____2714), (Some ("pre-typing for functions")), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in FStar_SMTEncoding_Term.Assume (uu____2710)))
in (

let t_interp1 = (

let a_name = (Prims.strcat "interpretation_" tsym)
in (

let uu____2739 = (

let uu____2743 = (

let uu____2744 = (

let uu____2750 = (FStar_SMTEncoding_Util.mkIff ((f_has_t_z), (t_interp)))
in ((((f_has_t_z)::[])::[]), ((fsym)::cvars), (uu____2750)))
in (FStar_SMTEncoding_Util.mkForall uu____2744))
in ((uu____2743), (Some (a_name)), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in FStar_SMTEncoding_Term.Assume (uu____2739)))
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
| uu____2772 -> begin
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

let uu____2781 = (

let uu____2785 = (FStar_SMTEncoding_Term.mk_HasType t1 FStar_SMTEncoding_Term.mk_Term_type)
in ((uu____2785), (Some ("Typing for non-total arrows")), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in FStar_SMTEncoding_Term.Assume (uu____2781)))
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

let uu____2794 = (

let uu____2798 = (

let uu____2799 = (

let uu____2805 = (

let uu____2806 = (

let uu____2809 = (

let uu____2810 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____2810))
in ((f_has_t), (uu____2809)))
in (FStar_SMTEncoding_Util.mkImp uu____2806))
in ((((f_has_t)::[])::[]), ((fsym)::[]), (uu____2805)))
in (mkForall_fuel uu____2799))
in ((uu____2798), (Some (a_name)), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in FStar_SMTEncoding_Term.Assume (uu____2794)))
in ((t1), ((tdecl)::(t_kinding)::(t_interp)::[]))))))))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (uu____2824) -> begin
(

let uu____2829 = (

let uu____2832 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)
in (match (uu____2832) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.tk = uu____2837; FStar_Syntax_Syntax.pos = uu____2838; FStar_Syntax_Syntax.vars = uu____2839} -> begin
(

let uu____2846 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) f)
in (match (uu____2846) with
| (b, f1) -> begin
(

let uu____2860 = (

let uu____2861 = (FStar_List.hd b)
in (Prims.fst uu____2861))
in ((uu____2860), (f1)))
end))
end
| uu____2866 -> begin
(failwith "impossible")
end))
in (match (uu____2829) with
| (x, f) -> begin
(

let uu____2873 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (uu____2873) with
| (base_t, decls) -> begin
(

let uu____2880 = (gen_term_var env x)
in (match (uu____2880) with
| (x1, xtm, env') -> begin
(

let uu____2889 = (encode_formula f env')
in (match (uu____2889) with
| (refinement, decls') -> begin
(

let uu____2896 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____2896) with
| (fsym, fterm) -> begin
(

let tm_has_type_with_fuel = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in (

let encoding = (FStar_SMTEncoding_Util.mkAnd ((tm_has_type_with_fuel), (refinement)))
in (

let cvars = (

let uu____2907 = (

let uu____2909 = (FStar_SMTEncoding_Term.free_variables refinement)
in (

let uu____2913 = (FStar_SMTEncoding_Term.free_variables tm_has_type_with_fuel)
in (FStar_List.append uu____2909 uu____2913)))
in (FStar_Util.remove_dups FStar_SMTEncoding_Term.fv_eq uu____2907))
in (

let cvars1 = (FStar_All.pipe_right cvars (FStar_List.filter (fun uu____2929 -> (match (uu____2929) with
| (y, uu____2933) -> begin
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

let uu____2952 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____2952) with
| Some (t1, uu____2967, uu____2968) -> begin
(

let uu____2978 = (

let uu____2979 = (

let uu____2983 = (FStar_All.pipe_right cvars1 (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((t1), (uu____2983)))
in (FStar_SMTEncoding_Util.mkApp uu____2979))
in ((uu____2978), ([])))
end
| None -> begin
(

let module_name = env.current_module_name
in (

let tsym = (

let uu____3000 = (

let uu____3001 = (

let uu____3002 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "_Tm_refine_" uu____3002))
in (Prims.strcat module_name uu____3001))
in (varops.mk_unique uu____3000))
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars1)
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let t1 = (

let uu____3011 = (

let uu____3015 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars1)
in ((tsym), (uu____3015)))
in (FStar_SMTEncoding_Util.mkApp uu____3011))
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

let uu____3025 = (

let uu____3029 = (

let uu____3030 = (

let uu____3036 = (FStar_SMTEncoding_Util.mkIff ((t_haseq_ref), (t_haseq_base)))
in ((((t_haseq_ref)::[])::[]), (cvars1), (uu____3036)))
in (FStar_SMTEncoding_Util.mkForall uu____3030))
in ((uu____3029), (Some ((Prims.strcat "haseq for " tsym))), ((Prims.strcat "haseq" tsym))))
in FStar_SMTEncoding_Term.Assume (uu____3025))
in (

let t_kinding = (

let uu____3046 = (

let uu____3050 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars1), (t_has_kind)))
in ((uu____3050), (Some ("refinement kinding")), ((Prims.strcat "refinement_kinding_" tsym))))
in FStar_SMTEncoding_Term.Assume (uu____3046))
in (

let t_interp = (

let uu____3060 = (

let uu____3064 = (

let uu____3065 = (

let uu____3071 = (FStar_SMTEncoding_Util.mkIff ((x_has_t), (encoding)))
in ((((x_has_t)::[])::[]), ((ffv)::(xfv)::cvars1), (uu____3071)))
in (FStar_SMTEncoding_Util.mkForall uu____3065))
in (

let uu____3083 = (

let uu____3085 = (FStar_Syntax_Print.term_to_string t0)
in Some (uu____3085))
in ((uu____3064), (uu____3083), ((Prims.strcat "refinement_interpretation_" tsym)))))
in FStar_SMTEncoding_Term.Assume (uu____3060))
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

let uu____3113 = (FStar_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Util.mk_Term_uvar uu____3113))
in (

let uu____3117 = (encode_term_pred None k env ttm)
in (match (uu____3117) with
| (t_has_k, decls) -> begin
(

let d = (

let uu____3125 = (

let uu____3129 = (

let uu____3130 = (

let uu____3131 = (

let uu____3132 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____3132))
in (FStar_Util.format1 "uvar_typing_%s" uu____3131))
in (varops.mk_unique uu____3130))
in ((t_has_k), (Some ("Uvar typing")), (uu____3129)))
in FStar_SMTEncoding_Term.Assume (uu____3125))
in ((ttm), ((FStar_List.append decls ((d)::[])))))
end)))
end
| FStar_Syntax_Syntax.Tm_app (uu____3138) -> begin
(

let uu____3148 = (FStar_Syntax_Util.head_and_args t0)
in (match (uu____3148) with
| (head1, args_e) -> begin
(

let uu____3176 = (

let uu____3184 = (

let uu____3185 = (FStar_Syntax_Subst.compress head1)
in uu____3185.FStar_Syntax_Syntax.n)
in ((uu____3184), (args_e)))
in (match (uu____3176) with
| (uu____3195, uu____3196) when (head_redex env head1) -> begin
(

let uu____3207 = (whnf env t)
in (encode_term uu____3207 env))
end
| ((FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), (_)::((v1, _))::((v2, _))::[])) | ((FStar_Syntax_Syntax.Tm_fvar (fv), (_)::((v1, _))::((v2, _))::[])) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
(

let uu____3281 = (encode_term v1 env)
in (match (uu____3281) with
| (v11, decls1) -> begin
(

let uu____3288 = (encode_term v2 env)
in (match (uu____3288) with
| (v21, decls2) -> begin
(

let uu____3295 = (FStar_SMTEncoding_Util.mk_LexCons v11 v21)
in ((uu____3295), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), uu____3297) -> begin
(

let e0 = (

let uu____3311 = (

let uu____3314 = (

let uu____3315 = (

let uu____3325 = (

let uu____3331 = (FStar_List.hd args_e)
in (uu____3331)::[])
in ((head1), (uu____3325)))
in FStar_Syntax_Syntax.Tm_app (uu____3315))
in (FStar_Syntax_Syntax.mk uu____3314))
in (uu____3311 None head1.FStar_Syntax_Syntax.pos))
in ((

let uu____3364 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____3364) with
| true -> begin
(

let uu____3365 = (FStar_Syntax_Print.term_to_string e0)
in (FStar_Util.print1 "Trying to normalize %s\n" uu____3365))
end
| uu____3366 -> begin
()
end));
(

let e01 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env.tcenv e0)
in ((

let uu____3369 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____3369) with
| true -> begin
(

let uu____3370 = (FStar_Syntax_Print.term_to_string e01)
in (FStar_Util.print1 "Result of normalization %s\n" uu____3370))
end
| uu____3371 -> begin
()
end));
(

let e02 = (

let uu____3373 = (

let uu____3374 = (

let uu____3375 = (FStar_Syntax_Subst.compress e01)
in uu____3375.FStar_Syntax_Syntax.n)
in (match (uu____3374) with
| FStar_Syntax_Syntax.Tm_app (uu____3378) -> begin
false
end
| uu____3388 -> begin
true
end))
in (match (uu____3373) with
| true -> begin
e01
end
| uu____3389 -> begin
(

let uu____3390 = (FStar_Syntax_Util.head_and_args e01)
in (match (uu____3390) with
| (head2, args) -> begin
(

let uu____3416 = (

let uu____3417 = (

let uu____3418 = (FStar_Syntax_Subst.compress head2)
in uu____3418.FStar_Syntax_Syntax.n)
in (match (uu____3417) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) -> begin
true
end
| uu____3421 -> begin
false
end))
in (match (uu____3416) with
| true -> begin
(match (args) with
| (x)::[] -> begin
(Prims.fst x)
end
| uu____3437 -> begin
(failwith "Impossible : Reify applied to multiple arguments after normalization.")
end)
end
| uu____3443 -> begin
e01
end))
end))
end))
in (

let e = (match (args_e) with
| (uu____3445)::[] -> begin
e02
end
| uu____3458 -> begin
(

let uu____3464 = (

let uu____3467 = (

let uu____3468 = (

let uu____3478 = (FStar_List.tl args_e)
in ((e02), (uu____3478)))
in FStar_Syntax_Syntax.Tm_app (uu____3468))
in (FStar_Syntax_Syntax.mk uu____3467))
in (uu____3464 None t0.FStar_Syntax_Syntax.pos))
end)
in (encode_term e env)));
));
))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____3501)), ((arg, uu____3503))::[]) -> begin
(encode_term arg env)
end
| uu____3521 -> begin
(

let uu____3529 = (encode_args args_e env)
in (match (uu____3529) with
| (args, decls) -> begin
(

let encode_partial_app = (fun ht_opt -> (

let uu____3562 = (encode_term head1 env)
in (match (uu____3562) with
| (head2, decls') -> begin
(

let app_tm = (mk_Apply_args head2 args)
in (match (ht_opt) with
| None -> begin
((app_tm), ((FStar_List.append decls decls')))
end
| Some (formals, c) -> begin
(

let uu____3601 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (uu____3601) with
| (formals1, rest) -> begin
(

let subst1 = (FStar_List.map2 (fun uu____3643 uu____3644 -> (match (((uu____3643), (uu____3644))) with
| ((bv, uu____3658), (a, uu____3660)) -> begin
FStar_Syntax_Syntax.NT (((bv), (a)))
end)) formals1 args_e)
in (

let ty = (

let uu____3674 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right uu____3674 (FStar_Syntax_Subst.subst subst1)))
in (

let uu____3679 = (encode_term_pred None ty env app_tm)
in (match (uu____3679) with
| (has_type, decls'') -> begin
(

let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (

let e_typing = (

let uu____3689 = (

let uu____3693 = (FStar_SMTEncoding_Util.mkForall ((((has_type)::[])::[]), (cvars), (has_type)))
in (

let uu____3698 = (

let uu____3699 = (

let uu____3700 = (

let uu____3701 = (FStar_SMTEncoding_Term.hash_of_term app_tm)
in (FStar_Util.digest_of_string uu____3701))
in (Prims.strcat "partial_app_typing_" uu____3700))
in (varops.mk_unique uu____3699))
in ((uu____3693), (Some ("Partial app typing")), (uu____3698))))
in FStar_SMTEncoding_Term.Assume (uu____3689))
in ((app_tm), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' ((e_typing)::[]))))))))
end))))
end))
end))
end)))
in (

let encode_full_app = (fun fv -> (

let uu____3718 = (lookup_free_var_sym env fv)
in (match (uu____3718) with
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

let uu____3756 = (

let uu____3757 = (

let uu____3760 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____3760 Prims.fst))
in (FStar_All.pipe_right uu____3757 Prims.snd))
in Some (uu____3756))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____3779, (FStar_Util.Inl (t1), uu____3781), uu____3782) -> begin
Some (t1)
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____3820, (FStar_Util.Inr (c), uu____3822), uu____3823) -> begin
Some ((FStar_Syntax_Util.comp_result c))
end
| uu____3861 -> begin
None
end)
in (match (head_type) with
| None -> begin
(encode_partial_app None)
end
| Some (head_type1) -> begin
(

let head_type2 = (

let uu____3881 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type1)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine uu____3881))
in (

let uu____3882 = (curried_arrow_formals_comp head_type2)
in (match (uu____3882) with
| (formals, c) -> begin
(match (head2.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| uu____3907 -> begin
(match (((FStar_List.length formals) > (FStar_List.length args))) with
| true -> begin
(encode_partial_app (Some (((formals), (c)))))
end
| uu____3919 -> begin
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

let uu____3952 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____3952) with
| (bs1, body1, opening) -> begin
(

let fallback = (fun uu____3967 -> (

let f = (varops.fresh "Tm_abs")
in (

let decl = FStar_SMTEncoding_Term.DeclFun (((f), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Imprecise function encoding"))))
in (

let uu____3972 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in ((uu____3972), ((decl)::[]))))))
in (

let is_impure = (fun lc -> (match (lc) with
| FStar_Util.Inl (lc1) -> begin
(

let uu____3983 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1)
in (not (uu____3983)))
end
| FStar_Util.Inr (eff, uu____3985) -> begin
(

let uu____3991 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv eff)
in (FStar_All.pipe_right uu____3991 Prims.op_Negation))
end))
in (

let reify_comp_and_body = (fun env1 c body2 -> (

let reified_body = (reify_body env1.tcenv body2)
in (

let c1 = (match (c) with
| FStar_Util.Inl (lc) -> begin
(

let typ = (

let uu____4036 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_TypeChecker_Env.reify_comp (

let uu___145_4037 = env1.tcenv
in {FStar_TypeChecker_Env.solver = uu___145_4037.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___145_4037.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___145_4037.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___145_4037.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___145_4037.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___145_4037.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___145_4037.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___145_4037.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___145_4037.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___145_4037.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___145_4037.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___145_4037.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___145_4037.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___145_4037.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___145_4037.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___145_4037.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___145_4037.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___145_4037.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___145_4037.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___145_4037.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___145_4037.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___145_4037.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___145_4037.FStar_TypeChecker_Env.qname_and_index}) uu____4036 FStar_Syntax_Syntax.U_unknown))
in (

let uu____4038 = (

let uu____4039 = (FStar_Syntax_Syntax.mk_Total typ)
in (FStar_Syntax_Util.lcomp_of_comp uu____4039))
in FStar_Util.Inl (uu____4038)))
end
| FStar_Util.Inr (eff_name, uu____4046) -> begin
c
end)
in ((c1), (reified_body)))))
in (

let codomain_eff = (fun lc -> (match (lc) with
| FStar_Util.Inl (lc1) -> begin
(

let uu____4077 = (

let uu____4078 = (lc1.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening uu____4078))
in (FStar_All.pipe_right uu____4077 (fun _0_31 -> Some (_0_31))))
end
| FStar_Util.Inr (eff, flags) -> begin
(

let new_uvar1 = (fun uu____4090 -> (

let uu____4091 = (FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange [] FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right uu____4091 Prims.fst)))
in (match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid)) with
| true -> begin
(

let uu____4099 = (

let uu____4100 = (new_uvar1 ())
in (FStar_Syntax_Syntax.mk_Total uu____4100))
in (FStar_All.pipe_right uu____4099 (fun _0_32 -> Some (_0_32))))
end
| uu____4102 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid)) with
| true -> begin
(

let uu____4104 = (

let uu____4105 = (new_uvar1 ())
in (FStar_Syntax_Syntax.mk_GTotal uu____4105))
in (FStar_All.pipe_right uu____4104 (fun _0_33 -> Some (_0_33))))
end
| uu____4107 -> begin
None
end)
end))
end))
in (match (lopt) with
| None -> begin
((

let uu____4116 = (

let uu____4117 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)" uu____4117))
in (FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____4116));
(fallback ());
)
end
| Some (lc) -> begin
(

let lc1 = lc
in (

let uu____4132 = ((is_impure lc1) && (

let uu____4133 = (FStar_TypeChecker_Env.is_reifiable env.tcenv lc1)
in (not (uu____4133))))
in (match (uu____4132) with
| true -> begin
(fallback ())
end
| uu____4136 -> begin
(

let cache_size = (FStar_Util.smap_size env.cache)
in (

let uu____4143 = (encode_binders None bs1 env)
in (match (uu____4143) with
| (vars, guards, envbody, decls, uu____4158) -> begin
(

let uu____4165 = (

let uu____4173 = (FStar_TypeChecker_Env.is_reifiable env.tcenv lc1)
in (match (uu____4173) with
| true -> begin
(reify_comp_and_body envbody lc1 body1)
end
| uu____4181 -> begin
((lc1), (body1))
end))
in (match (uu____4165) with
| (lc2, body2) -> begin
(

let uu____4198 = (encode_term body2 envbody)
in (match (uu____4198) with
| (body3, decls') -> begin
(

let uu____4205 = (

let uu____4210 = (codomain_eff lc2)
in (match (uu____4210) with
| None -> begin
((None), ([]))
end
| Some (c) -> begin
(

let tfun = (FStar_Syntax_Util.arrow bs1 c)
in (

let uu____4222 = (encode_term tfun env)
in (match (uu____4222) with
| (t1, decls1) -> begin
((Some (t1)), (decls1))
end)))
end))
in (match (uu____4205) with
| (arrow_t_opt, decls'') -> begin
(

let key_body = (

let uu____4241 = (

let uu____4247 = (

let uu____4248 = (

let uu____4251 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____4251), (body3)))
in (FStar_SMTEncoding_Util.mkImp uu____4248))
in (([]), (vars), (uu____4247)))
in (FStar_SMTEncoding_Util.mkForall uu____4241))
in (

let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (

let cvars1 = (match (arrow_t_opt) with
| None -> begin
cvars
end
| Some (t1) -> begin
(

let uu____4259 = (

let uu____4261 = (FStar_SMTEncoding_Term.free_variables t1)
in (FStar_List.append uu____4261 cvars))
in (FStar_Util.remove_dups FStar_SMTEncoding_Term.fv_eq uu____4259))
end)
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), (cvars1), (key_body)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____4272 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____4272) with
| Some (t1, uu____4287, uu____4288) -> begin
(

let uu____4298 = (

let uu____4299 = (

let uu____4303 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars1)
in ((t1), (uu____4303)))
in (FStar_SMTEncoding_Util.mkApp uu____4299))
in ((uu____4298), ([])))
end
| None -> begin
(

let uu____4314 = (is_an_eta_expansion env vars body3)
in (match (uu____4314) with
| Some (t1) -> begin
(

let decls1 = (

let uu____4321 = (

let uu____4322 = (FStar_Util.smap_size env.cache)
in (uu____4322 = cache_size))
in (match (uu____4321) with
| true -> begin
[]
end
| uu____4329 -> begin
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

let uu____4338 = (

let uu____4339 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_abs_" uu____4339))
in (varops.mk_unique uu____4338))
in (Prims.strcat module_name (Prims.strcat "_" fsym))))
in (

let fdecl = FStar_SMTEncoding_Term.DeclFun (((fsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let f = (

let uu____4344 = (

let uu____4348 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars1)
in ((fsym), (uu____4348)))
in (FStar_SMTEncoding_Util.mkApp uu____4344))
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

let uu____4360 = (

let uu____4361 = (

let uu____4365 = (FStar_SMTEncoding_Util.mkForall ((((f)::[])::[]), (cvars1), (f_has_t)))
in ((uu____4365), (Some (a_name)), (a_name)))
in FStar_SMTEncoding_Term.Assume (uu____4361))
in (uu____4360)::[])))
end)
in (

let interp_f = (

let a_name = (Prims.strcat "interpretation_" fsym)
in (

let uu____4373 = (

let uu____4377 = (

let uu____4378 = (

let uu____4384 = (FStar_SMTEncoding_Util.mkEq ((app), (body3)))
in ((((app)::[])::[]), ((FStar_List.append vars cvars1)), (uu____4384)))
in (FStar_SMTEncoding_Util.mkForall uu____4378))
in ((uu____4377), (Some (a_name)), (a_name)))
in FStar_SMTEncoding_Term.Assume (uu____4373)))
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
| FStar_Syntax_Syntax.Tm_let ((uu____4402, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____4403); FStar_Syntax_Syntax.lbunivs = uu____4404; FStar_Syntax_Syntax.lbtyp = uu____4405; FStar_Syntax_Syntax.lbeff = uu____4406; FStar_Syntax_Syntax.lbdef = uu____4407})::uu____4408), uu____4409) -> begin
(failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____4427; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____4429; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (uu____4445) -> begin
((FStar_Errors.diag t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts");
(

let e = (varops.fresh "let-rec")
in (

let decl_e = FStar_SMTEncoding_Term.DeclFun (((e), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let uu____4458 = (FStar_SMTEncoding_Util.mkFreeV ((e), (FStar_SMTEncoding_Term.Term_sort)))
in ((uu____4458), ((decl_e)::[])))));
)
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end);
)))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (

let uu____4500 = (encode_term e1 env)
in (match (uu____4500) with
| (ee1, decls1) -> begin
(

let uu____4507 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) e2)
in (match (uu____4507) with
| (xs, e21) -> begin
(

let uu____4521 = (FStar_List.hd xs)
in (match (uu____4521) with
| (x1, uu____4529) -> begin
(

let env' = (push_term_var env x1 ee1)
in (

let uu____4531 = (encode_body e21 env')
in (match (uu____4531) with
| (ee2, decls2) -> begin
((ee2), ((FStar_List.append decls1 decls2)))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (

let uu____4553 = (

let uu____4557 = (

let uu____4558 = ((FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown) None FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.null_bv uu____4558))
in (gen_term_var env uu____4557))
in (match (uu____4553) with
| (scrsym, scr', env1) -> begin
(

let uu____4572 = (encode_term e env1)
in (match (uu____4572) with
| (scr, decls) -> begin
(

let uu____4579 = (

let encode_branch = (fun b uu____4595 -> (match (uu____4595) with
| (else_case, decls1) -> begin
(

let uu____4606 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____4606) with
| (p, w, br) -> begin
(

let patterns = (encode_pat env1 p)
in (FStar_List.fold_right (fun uu____4636 uu____4637 -> (match (((uu____4636), (uu____4637))) with
| ((env0, pattern), (else_case1, decls2)) -> begin
(

let guard = (pattern.guard scr')
in (

let projections = (pattern.projections scr')
in (

let env2 = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env2 uu____4674 -> (match (uu____4674) with
| (x, t) -> begin
(push_term_var env2 x t)
end)) env1))
in (

let uu____4679 = (match (w) with
| None -> begin
((guard), ([]))
end
| Some (w1) -> begin
(

let uu____4694 = (encode_term w1 env2)
in (match (uu____4694) with
| (w2, decls21) -> begin
(

let uu____4702 = (

let uu____4703 = (

let uu____4706 = (

let uu____4707 = (

let uu____4710 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue)
in ((w2), (uu____4710)))
in (FStar_SMTEncoding_Util.mkEq uu____4707))
in ((guard), (uu____4706)))
in (FStar_SMTEncoding_Util.mkAnd uu____4703))
in ((uu____4702), (decls21)))
end))
end)
in (match (uu____4679) with
| (guard1, decls21) -> begin
(

let uu____4718 = (encode_br br env2)
in (match (uu____4718) with
| (br1, decls3) -> begin
(

let uu____4726 = (FStar_SMTEncoding_Util.mkITE ((guard1), (br1), (else_case1)))
in ((uu____4726), ((FStar_List.append decls2 (FStar_List.append decls21 decls3)))))
end))
end)))))
end)) patterns ((else_case), (decls1))))
end))
end))
in (FStar_List.fold_right encode_branch pats ((default_case), (decls))))
in (match (uu____4579) with
| (match_tm, decls1) -> begin
(

let uu____4738 = (FStar_SMTEncoding_Term.mkLet' (((((((scrsym), (FStar_SMTEncoding_Term.Term_sort))), (scr)))::[]), (match_tm)) FStar_Range.dummyRange)
in ((uu____4738), (decls1)))
end))
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| uu____4769 -> begin
(

let uu____4770 = (encode_one_pat env pat)
in (uu____4770)::[])
end))
and encode_one_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> ((

let uu____4782 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____4782) with
| true -> begin
(

let uu____4783 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" uu____4783))
end
| uu____4784 -> begin
()
end));
(

let uu____4785 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (uu____4785) with
| (vars, pat_term) -> begin
(

let uu____4795 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun uu____4818 v1 -> (match (uu____4818) with
| (env1, vars1) -> begin
(

let uu____4846 = (gen_term_var env1 v1)
in (match (uu____4846) with
| (xx, uu____4858, env2) -> begin
((env2), ((((v1), (((xx), (FStar_SMTEncoding_Term.Term_sort)))))::vars1))
end))
end)) ((env), ([]))))
in (match (uu____4795) with
| (env1, vars1) -> begin
(

let rec mk_guard = (fun pat1 scrutinee -> (match (pat1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (uu____4905) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_dot_term (_)) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____4913 = (

let uu____4916 = (encode_const c)
in ((scrutinee), (uu____4916)))
in (FStar_SMTEncoding_Util.mkEq uu____4913))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let is_f = (

let tc_name = (FStar_TypeChecker_Env.typ_of_datacon env1.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let uu____4935 = (FStar_TypeChecker_Env.datacons_of_typ env1.tcenv tc_name)
in (match (uu____4935) with
| (uu____4939, (uu____4940)::[]) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| uu____4942 -> begin
(mk_data_tester env1 f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
end)))
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____4963 -> (match (uu____4963) with
| (arg, uu____4969) -> begin
(

let proj = (primitive_projector_by_pos env1.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____4979 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_guard arg uu____4979)))
end))))
in (FStar_SMTEncoding_Util.mk_and_l ((is_f)::sub_term_guards))))
end))
in (

let rec mk_projections = (fun pat1 scrutinee -> (match (pat1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (uu____4998) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _)) | (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_constant (uu____5013) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let uu____5028 = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____5050 -> (match (uu____5050) with
| (arg, uu____5059) -> begin
(

let proj = (primitive_projector_by_pos env1.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____5069 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_projections arg uu____5069)))
end))))
in (FStar_All.pipe_right uu____5028 FStar_List.flatten))
end))
in (

let pat_term1 = (fun uu____5085 -> (encode_term pat_term env1))
in (

let pattern = {pat_vars = vars1; pat_term = pat_term1; guard = (mk_guard pat); projections = (mk_projections pat)}
in ((env1), (pattern))))))
end))
end));
))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (

let uu____5092 = (FStar_All.pipe_right l (FStar_List.fold_left (fun uu____5107 uu____5108 -> (match (((uu____5107), (uu____5108))) with
| ((tms, decls), (t, uu____5128)) -> begin
(

let uu____5139 = (encode_term t env)
in (match (uu____5139) with
| (t1, decls') -> begin
(((t1)::tms), ((FStar_List.append decls decls')))
end))
end)) (([]), ([]))))
in (match (uu____5092) with
| (l1, decls) -> begin
(((FStar_List.rev l1)), (decls))
end)))
and encode_function_type_as_formula : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun induction_on new_pats t env -> (

let list_elements1 = (fun e -> (

let uu____5177 = (FStar_Syntax_Util.list_elements e)
in (match (uu____5177) with
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

let uu____5195 = (

let uu____5205 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right uu____5205 FStar_Syntax_Util.head_and_args))
in (match (uu____5195) with
| (head1, args) -> begin
(

let uu____5236 = (

let uu____5244 = (

let uu____5245 = (FStar_Syntax_Util.un_uinst head1)
in uu____5245.FStar_Syntax_Syntax.n)
in ((uu____5244), (args)))
in (match (uu____5236) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((uu____5259, uu____5260))::((e, uu____5262))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpat_lid) -> begin
((e), (None))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, uu____5293))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatT_lid) -> begin
((e), (None))
end
| uu____5314 -> begin
(failwith "Unexpected pattern term")
end))
end)))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements1 p)
in (

let smt_pat_or = (fun t1 -> (

let uu____5347 = (

let uu____5357 = (FStar_Syntax_Util.unmeta t1)
in (FStar_All.pipe_right uu____5357 FStar_Syntax_Util.head_and_args))
in (match (uu____5347) with
| (head1, args) -> begin
(

let uu____5386 = (

let uu____5394 = (

let uu____5395 = (FStar_Syntax_Util.un_uinst head1)
in uu____5395.FStar_Syntax_Syntax.n)
in ((uu____5394), (args)))
in (match (uu____5386) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, uu____5408))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatOr_lid) -> begin
Some (e)
end
| uu____5428 -> begin
None
end))
end)))
in (match (elts) with
| (t1)::[] -> begin
(

let uu____5446 = (smt_pat_or t1)
in (match (uu____5446) with
| Some (e) -> begin
(

let uu____5462 = (list_elements1 e)
in (FStar_All.pipe_right uu____5462 (FStar_List.map (fun branch1 -> (

let uu____5479 = (list_elements1 branch1)
in (FStar_All.pipe_right uu____5479 (FStar_List.map one_pat)))))))
end
| uu____5493 -> begin
(

let uu____5497 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____5497)::[])
end))
end
| uu____5528 -> begin
(

let uu____5530 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____5530)::[])
end))))
in (

let uu____5561 = (

let uu____5577 = (

let uu____5578 = (FStar_Syntax_Subst.compress t)
in uu____5578.FStar_Syntax_Syntax.n)
in (match (uu____5577) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____5608 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____5608) with
| (binders1, c1) -> begin
(match (c1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____5643; FStar_Syntax_Syntax.effect_name = uu____5644; FStar_Syntax_Syntax.result_typ = uu____5645; FStar_Syntax_Syntax.effect_args = ((pre, uu____5647))::((post, uu____5649))::((pats, uu____5651))::[]; FStar_Syntax_Syntax.flags = uu____5652}) -> begin
(

let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (

let uu____5686 = (lemma_pats pats')
in ((binders1), (pre), (post), (uu____5686))))
end
| uu____5705 -> begin
(failwith "impos")
end)
end))
end
| uu____5721 -> begin
(failwith "Impos")
end))
in (match (uu____5561) with
| (binders, pre, post, patterns) -> begin
(

let uu____5765 = (encode_binders None binders env)
in (match (uu____5765) with
| (vars, guards, env1, decls, uu____5780) -> begin
(

let uu____5787 = (

let uu____5794 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch1 -> (

let uu____5825 = (

let uu____5830 = (FStar_All.pipe_right branch1 (FStar_List.map (fun uu____5846 -> (match (uu____5846) with
| (t1, uu____5853) -> begin
(encode_term t1 (

let uu___146_5856 = env1
in {bindings = uu___146_5856.bindings; depth = uu___146_5856.depth; tcenv = uu___146_5856.tcenv; warn = uu___146_5856.warn; cache = uu___146_5856.cache; nolabels = uu___146_5856.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___146_5856.encode_non_total_function_typ; current_module_name = uu___146_5856.current_module_name}))
end))))
in (FStar_All.pipe_right uu____5830 FStar_List.unzip))
in (match (uu____5825) with
| (pats, decls1) -> begin
((pats), (decls1))
end)))))
in (FStar_All.pipe_right uu____5794 FStar_List.unzip))
in (match (uu____5787) with
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

let uu____5920 = (

let uu____5921 = (FStar_SMTEncoding_Util.mkFreeV l)
in (FStar_SMTEncoding_Util.mk_Precedes uu____5921 e))
in (uu____5920)::p))))
end
| uu____5922 -> begin
(

let rec aux = (fun tl1 vars1 -> (match (vars1) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (

let uu____5951 = (FStar_SMTEncoding_Util.mk_Precedes tl1 e)
in (uu____5951)::p))))
end
| ((x, FStar_SMTEncoding_Term.Term_sort))::vars2 -> begin
(

let uu____5959 = (

let uu____5960 = (FStar_SMTEncoding_Util.mkFreeV ((x), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Util.mk_LexCons uu____5960 tl1))
in (aux uu____5959 vars2))
end
| uu____5961 -> begin
pats
end))
in (

let uu____5965 = (FStar_SMTEncoding_Util.mkFreeV (("Prims.LexTop"), (FStar_SMTEncoding_Term.Term_sort)))
in (aux uu____5965 vars)))
end)
end)
in (

let env2 = (

let uu___147_5967 = env1
in {bindings = uu___147_5967.bindings; depth = uu___147_5967.depth; tcenv = uu___147_5967.tcenv; warn = uu___147_5967.warn; cache = uu___147_5967.cache; nolabels = true; use_zfuel_name = uu___147_5967.use_zfuel_name; encode_non_total_function_typ = uu___147_5967.encode_non_total_function_typ; current_module_name = uu___147_5967.current_module_name})
in (

let uu____5968 = (

let uu____5971 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula uu____5971 env2))
in (match (uu____5968) with
| (pre1, decls'') -> begin
(

let uu____5976 = (

let uu____5979 = (FStar_Syntax_Util.unmeta post)
in (encode_formula uu____5979 env2))
in (match (uu____5976) with
| (post1, decls''') -> begin
(

let decls1 = (FStar_List.append decls (FStar_List.append (FStar_List.flatten decls'1) (FStar_List.append decls'' decls''')))
in (

let uu____5986 = (

let uu____5987 = (

let uu____5993 = (

let uu____5994 = (

let uu____5997 = (FStar_SMTEncoding_Util.mk_and_l ((pre1)::guards))
in ((uu____5997), (post1)))
in (FStar_SMTEncoding_Util.mkImp uu____5994))
in ((pats1), (vars), (uu____5993)))
in (FStar_SMTEncoding_Util.mkForall uu____5987))
in ((uu____5986), (decls1))))
end))
end)))))
end))
end))
end))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (

let debug1 = (fun phi1 -> (

let uu____6010 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____6010) with
| true -> begin
(

let uu____6011 = (FStar_Syntax_Print.tag_of_term phi1)
in (

let uu____6012 = (FStar_Syntax_Print.term_to_string phi1)
in (FStar_Util.print2 "Formula (%s)  %s\n" uu____6011 uu____6012)))
end
| uu____6013 -> begin
()
end)))
in (

let enc = (fun f r l -> (

let uu____6039 = (FStar_Util.fold_map (fun decls x -> (

let uu____6052 = (encode_term (Prims.fst x) env)
in (match (uu____6052) with
| (t, decls') -> begin
(((FStar_List.append decls decls')), (t))
end))) [] l)
in (match (uu____6039) with
| (decls, args) -> begin
(

let uu____6069 = (

let uu___148_6070 = (f args)
in {FStar_SMTEncoding_Term.tm = uu___148_6070.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___148_6070.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____6069), (decls)))
end)))
in (

let const_op = (fun f r uu____6089 -> (

let uu____6092 = (f r)
in ((uu____6092), ([]))))
in (

let un_op = (fun f l -> (

let uu____6108 = (FStar_List.hd l)
in (FStar_All.pipe_left f uu____6108)))
in (

let bin_op = (fun f uu___120_6121 -> (match (uu___120_6121) with
| (t1)::(t2)::[] -> begin
(f ((t1), (t2)))
end
| uu____6129 -> begin
(failwith "Impossible")
end))
in (

let enc_prop_c = (fun f r l -> (

let uu____6156 = (FStar_Util.fold_map (fun decls uu____6165 -> (match (uu____6165) with
| (t, uu____6173) -> begin
(

let uu____6174 = (encode_formula t env)
in (match (uu____6174) with
| (phi1, decls') -> begin
(((FStar_List.append decls decls')), (phi1))
end))
end)) [] l)
in (match (uu____6156) with
| (decls, phis) -> begin
(

let uu____6191 = (

let uu___149_6192 = (f phis)
in {FStar_SMTEncoding_Term.tm = uu___149_6192.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___149_6192.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____6191), (decls)))
end)))
in (

let eq_op = (fun r uu___121_6208 -> (match (uu___121_6208) with
| ((_)::(e1)::(e2)::[]) | ((_)::(_)::(e1)::(e2)::[]) -> begin
(

let uu____6268 = (enc (bin_op FStar_SMTEncoding_Util.mkEq))
in (uu____6268 r ((e1)::(e2)::[])))
end
| l -> begin
(

let uu____6288 = (enc (bin_op FStar_SMTEncoding_Util.mkEq))
in (uu____6288 r l))
end))
in (

let mk_imp1 = (fun r uu___122_6307 -> (match (uu___122_6307) with
| ((lhs, uu____6311))::((rhs, uu____6313))::[] -> begin
(

let uu____6334 = (encode_formula rhs env)
in (match (uu____6334) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____6343) -> begin
((l1), (decls1))
end
| uu____6346 -> begin
(

let uu____6347 = (encode_formula lhs env)
in (match (uu____6347) with
| (l2, decls2) -> begin
(

let uu____6354 = (FStar_SMTEncoding_Term.mkImp ((l2), (l1)) r)
in ((uu____6354), ((FStar_List.append decls1 decls2))))
end))
end)
end))
end
| uu____6356 -> begin
(failwith "impossible")
end))
in (

let mk_ite = (fun r uu___123_6371 -> (match (uu___123_6371) with
| ((guard, uu____6375))::((_then, uu____6377))::((_else, uu____6379))::[] -> begin
(

let uu____6408 = (encode_formula guard env)
in (match (uu____6408) with
| (g, decls1) -> begin
(

let uu____6415 = (encode_formula _then env)
in (match (uu____6415) with
| (t, decls2) -> begin
(

let uu____6422 = (encode_formula _else env)
in (match (uu____6422) with
| (e, decls3) -> begin
(

let res = (FStar_SMTEncoding_Term.mkITE ((g), (t), (e)) r)
in ((res), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end))
end))
end
| uu____6431 -> begin
(failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (

let uu____6450 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f uu____6450)))
in (

let connectives = (

let uu____6462 = (

let uu____6471 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd))
in ((FStar_Syntax_Const.and_lid), (uu____6471)))
in (

let uu____6484 = (

let uu____6494 = (

let uu____6503 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr))
in ((FStar_Syntax_Const.or_lid), (uu____6503)))
in (

let uu____6516 = (

let uu____6526 = (

let uu____6536 = (

let uu____6545 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff))
in ((FStar_Syntax_Const.iff_lid), (uu____6545)))
in (

let uu____6558 = (

let uu____6568 = (

let uu____6578 = (

let uu____6587 = (enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot))
in ((FStar_Syntax_Const.not_lid), (uu____6587)))
in (uu____6578)::(((FStar_Syntax_Const.eq2_lid), (eq_op)))::(((FStar_Syntax_Const.eq3_lid), (eq_op)))::(((FStar_Syntax_Const.true_lid), ((const_op FStar_SMTEncoding_Term.mkTrue))))::(((FStar_Syntax_Const.false_lid), ((const_op FStar_SMTEncoding_Term.mkFalse))))::[])
in (((FStar_Syntax_Const.ite_lid), (mk_ite)))::uu____6568)
in (uu____6536)::uu____6558))
in (((FStar_Syntax_Const.imp_lid), (mk_imp1)))::uu____6526)
in (uu____6494)::uu____6516))
in (uu____6462)::uu____6484))
in (

let rec fallback = (fun phi1 -> (match (phi1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(

let uu____6749 = (encode_formula phi' env)
in (match (uu____6749) with
| (phi2, decls) -> begin
(

let uu____6756 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled (((phi2), (msg), (r)))) r)
in ((uu____6756), (decls)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (uu____6757) -> begin
(

let uu____6762 = (FStar_Syntax_Util.unmeta phi1)
in (encode_formula uu____6762 env))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(

let uu____6791 = (encode_match e pats FStar_SMTEncoding_Util.mkFalse env encode_formula)
in (match (uu____6791) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____6799; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____6801; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let uu____6817 = (encode_let x t1 e1 e2 env encode_formula)
in (match (uu____6817) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let head2 = (FStar_Syntax_Util.un_uinst head1)
in (match (((head2.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____6849)::((x, uu____6851))::((t, uu____6853))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.has_type_lid) -> begin
(

let uu____6887 = (encode_term x env)
in (match (uu____6887) with
| (x1, decls) -> begin
(

let uu____6894 = (encode_term t env)
in (match (uu____6894) with
| (t1, decls') -> begin
(

let uu____6901 = (FStar_SMTEncoding_Term.mk_HasType x1 t1)
in ((uu____6901), ((FStar_List.append decls decls'))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((r, uu____6905))::((msg, uu____6907))::((phi2, uu____6909))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.labeled_lid) -> begin
(

let uu____6943 = (

let uu____6946 = (

let uu____6947 = (FStar_Syntax_Subst.compress r)
in uu____6947.FStar_Syntax_Syntax.n)
in (

let uu____6950 = (

let uu____6951 = (FStar_Syntax_Subst.compress msg)
in uu____6951.FStar_Syntax_Syntax.n)
in ((uu____6946), (uu____6950))))
in (match (uu____6943) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____6958))) -> begin
(

let phi3 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((phi2), (FStar_Syntax_Syntax.Meta_labeled ((((FStar_Util.string_of_unicode s)), (r1), (false)))))))) None r1)
in (fallback phi3))
end
| uu____6974 -> begin
(fallback phi2)
end))
end
| uu____6977 when (head_redex env head2) -> begin
(

let uu____6985 = (whnf env phi1)
in (encode_formula uu____6985 env))
end
| uu____6986 -> begin
(

let uu____6994 = (encode_term phi1 env)
in (match (uu____6994) with
| (tt, decls) -> begin
(

let uu____7001 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___150_7002 = tt
in {FStar_SMTEncoding_Term.tm = uu___150_7002.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___150_7002.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi1.FStar_Syntax_Syntax.pos}))
in ((uu____7001), (decls)))
end))
end))
end
| uu____7005 -> begin
(

let uu____7006 = (encode_term phi1 env)
in (match (uu____7006) with
| (tt, decls) -> begin
(

let uu____7013 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___151_7014 = tt
in {FStar_SMTEncoding_Term.tm = uu___151_7014.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___151_7014.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi1.FStar_Syntax_Syntax.pos}))
in ((uu____7013), (decls)))
end))
end))
in (

let encode_q_body = (fun env1 bs ps body -> (

let uu____7041 = (encode_binders None bs env1)
in (match (uu____7041) with
| (vars, guards, env2, decls, uu____7063) -> begin
(

let uu____7070 = (

let uu____7077 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let uu____7100 = (

let uu____7105 = (FStar_All.pipe_right p (FStar_List.map (fun uu____7119 -> (match (uu____7119) with
| (t, uu____7125) -> begin
(encode_term t (

let uu___152_7126 = env2
in {bindings = uu___152_7126.bindings; depth = uu___152_7126.depth; tcenv = uu___152_7126.tcenv; warn = uu___152_7126.warn; cache = uu___152_7126.cache; nolabels = uu___152_7126.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___152_7126.encode_non_total_function_typ; current_module_name = uu___152_7126.current_module_name}))
end))))
in (FStar_All.pipe_right uu____7105 FStar_List.unzip))
in (match (uu____7100) with
| (p1, decls1) -> begin
((p1), ((FStar_List.flatten decls1)))
end)))))
in (FStar_All.pipe_right uu____7077 FStar_List.unzip))
in (match (uu____7070) with
| (pats, decls') -> begin
(

let uu____7178 = (encode_formula body env2)
in (match (uu____7178) with
| (body1, decls'') -> begin
(

let guards1 = (match (pats) with
| (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (gf), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____7197; FStar_SMTEncoding_Term.rng = uu____7198})::[])::[] when ((FStar_Ident.text_of_lid FStar_Syntax_Const.guard_free) = gf) -> begin
[]
end
| uu____7206 -> begin
guards
end)
in (

let uu____7209 = (FStar_SMTEncoding_Util.mk_and_l guards1)
in ((vars), (pats), (uu____7209), (body1), ((FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') decls''))))))
end))
end))
end)))
in ((debug1 phi);
(

let phi1 = (FStar_Syntax_Util.unascribe phi)
in (

let check_pattern_vars = (fun vars pats -> (

let pats1 = (FStar_All.pipe_right pats (FStar_List.map (fun uu____7243 -> (match (uu____7243) with
| (x, uu____7247) -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x)
end))))
in (match (pats1) with
| [] -> begin
()
end
| (hd1)::tl1 -> begin
(

let pat_vars = (

let uu____7253 = (FStar_Syntax_Free.names hd1)
in (FStar_List.fold_left (fun out x -> (

let uu____7259 = (FStar_Syntax_Free.names x)
in (FStar_Util.set_union out uu____7259))) uu____7253 tl1))
in (

let uu____7261 = (FStar_All.pipe_right vars (FStar_Util.find_opt (fun uu____7273 -> (match (uu____7273) with
| (b, uu____7277) -> begin
(

let uu____7278 = (FStar_Util.set_mem b pat_vars)
in (not (uu____7278)))
end))))
in (match (uu____7261) with
| None -> begin
()
end
| Some (x, uu____7282) -> begin
(

let pos = (FStar_List.fold_left (fun out t -> (FStar_Range.union_ranges out t.FStar_Syntax_Syntax.pos)) hd1.FStar_Syntax_Syntax.pos tl1)
in (

let uu____7292 = (

let uu____7293 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "SMT pattern misses at least one bound variable: %s" uu____7293))
in (FStar_Errors.warn pos uu____7292)))
end)))
end)))
in (

let uu____7294 = (FStar_Syntax_Util.destruct_typ_as_formula phi1)
in (match (uu____7294) with
| None -> begin
(fallback phi1)
end
| Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(

let uu____7300 = (FStar_All.pipe_right connectives (FStar_List.tryFind (fun uu____7336 -> (match (uu____7336) with
| (l, uu____7346) -> begin
(FStar_Ident.lid_equals op l)
end))))
in (match (uu____7300) with
| None -> begin
(fallback phi1)
end
| Some (uu____7369, f) -> begin
(f phi1.FStar_Syntax_Syntax.pos arms)
end))
end
| Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____7398 = (encode_q_body env vars pats body)
in (match (uu____7398) with
| (vars1, pats1, guard, body1, decls) -> begin
(

let tm = (

let uu____7424 = (

let uu____7430 = (FStar_SMTEncoding_Util.mkImp ((guard), (body1)))
in ((pats1), (vars1), (uu____7430)))
in (FStar_SMTEncoding_Term.mkForall uu____7424 phi1.FStar_Syntax_Syntax.pos))
in ((tm), (decls)))
end));
)
end
| Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____7442 = (encode_q_body env vars pats body)
in (match (uu____7442) with
| (vars1, pats1, guard, body1, decls) -> begin
(

let uu____7467 = (

let uu____7468 = (

let uu____7474 = (FStar_SMTEncoding_Util.mkAnd ((guard), (body1)))
in ((pats1), (vars1), (uu____7474)))
in (FStar_SMTEncoding_Term.mkExists uu____7468 phi1.FStar_Syntax_Syntax.pos))
in ((uu____7467), (decls)))
end));
)
end))));
)))))))))))))))

type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list); is : FStar_Ident.lident  ->  Prims.bool}


let prims : prims_t = (

let uu____7523 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____7523) with
| (asym, a) -> begin
(

let uu____7528 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____7528) with
| (xsym, x) -> begin
(

let uu____7533 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____7533) with
| (ysym, y) -> begin
(

let quant = (fun vars body x1 -> (

let xname_decl = (

let uu____7563 = (

let uu____7569 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in ((x1), (uu____7569), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (uu____7563))
in (

let xtok = (Prims.strcat x1 "@tok")
in (

let xtok_decl = FStar_SMTEncoding_Term.DeclFun (((xtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let xapp = (

let uu____7584 = (

let uu____7588 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((x1), (uu____7588)))
in (FStar_SMTEncoding_Util.mkApp uu____7584))
in (

let xtok1 = (FStar_SMTEncoding_Util.mkApp ((xtok), ([])))
in (

let xtok_app = (mk_Apply xtok1 vars)
in (

let uu____7596 = (

let uu____7598 = (

let uu____7600 = (

let uu____7602 = (

let uu____7603 = (

let uu____7607 = (

let uu____7608 = (

let uu____7614 = (FStar_SMTEncoding_Util.mkEq ((xapp), (body)))
in ((((xapp)::[])::[]), (vars), (uu____7614)))
in (FStar_SMTEncoding_Util.mkForall uu____7608))
in ((uu____7607), (None), ((Prims.strcat "primitive_" x1))))
in FStar_SMTEncoding_Term.Assume (uu____7603))
in (

let uu____7623 = (

let uu____7625 = (

let uu____7626 = (

let uu____7630 = (

let uu____7631 = (

let uu____7637 = (FStar_SMTEncoding_Util.mkEq ((xtok_app), (xapp)))
in ((((xtok_app)::[])::[]), (vars), (uu____7637)))
in (FStar_SMTEncoding_Util.mkForall uu____7631))
in ((uu____7630), (Some ("Name-token correspondence")), ((Prims.strcat "token_correspondence_" x1))))
in FStar_SMTEncoding_Term.Assume (uu____7626))
in (uu____7625)::[])
in (uu____7602)::uu____7623))
in (xtok_decl)::uu____7600)
in (xname_decl)::uu____7598)
in ((xtok1), (uu____7596))))))))))
in (

let axy = (((asym), (FStar_SMTEncoding_Term.Term_sort)))::(((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let xy = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let qx = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let prims1 = (

let uu____7686 = (

let uu____7694 = (

let uu____7700 = (

let uu____7701 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7701))
in (quant axy uu____7700))
in ((FStar_Syntax_Const.op_Eq), (uu____7694)))
in (

let uu____7707 = (

let uu____7716 = (

let uu____7724 = (

let uu____7730 = (

let uu____7731 = (

let uu____7732 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_SMTEncoding_Util.mkNot uu____7732))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7731))
in (quant axy uu____7730))
in ((FStar_Syntax_Const.op_notEq), (uu____7724)))
in (

let uu____7738 = (

let uu____7747 = (

let uu____7755 = (

let uu____7761 = (

let uu____7762 = (

let uu____7763 = (

let uu____7766 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7767 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7766), (uu____7767))))
in (FStar_SMTEncoding_Util.mkLT uu____7763))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7762))
in (quant xy uu____7761))
in ((FStar_Syntax_Const.op_LT), (uu____7755)))
in (

let uu____7773 = (

let uu____7782 = (

let uu____7790 = (

let uu____7796 = (

let uu____7797 = (

let uu____7798 = (

let uu____7801 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7802 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7801), (uu____7802))))
in (FStar_SMTEncoding_Util.mkLTE uu____7798))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7797))
in (quant xy uu____7796))
in ((FStar_Syntax_Const.op_LTE), (uu____7790)))
in (

let uu____7808 = (

let uu____7817 = (

let uu____7825 = (

let uu____7831 = (

let uu____7832 = (

let uu____7833 = (

let uu____7836 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7837 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7836), (uu____7837))))
in (FStar_SMTEncoding_Util.mkGT uu____7833))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7832))
in (quant xy uu____7831))
in ((FStar_Syntax_Const.op_GT), (uu____7825)))
in (

let uu____7843 = (

let uu____7852 = (

let uu____7860 = (

let uu____7866 = (

let uu____7867 = (

let uu____7868 = (

let uu____7871 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7872 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7871), (uu____7872))))
in (FStar_SMTEncoding_Util.mkGTE uu____7868))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7867))
in (quant xy uu____7866))
in ((FStar_Syntax_Const.op_GTE), (uu____7860)))
in (

let uu____7878 = (

let uu____7887 = (

let uu____7895 = (

let uu____7901 = (

let uu____7902 = (

let uu____7903 = (

let uu____7906 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7907 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7906), (uu____7907))))
in (FStar_SMTEncoding_Util.mkSub uu____7903))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7902))
in (quant xy uu____7901))
in ((FStar_Syntax_Const.op_Subtraction), (uu____7895)))
in (

let uu____7913 = (

let uu____7922 = (

let uu____7930 = (

let uu____7936 = (

let uu____7937 = (

let uu____7938 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Util.mkMinus uu____7938))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7937))
in (quant qx uu____7936))
in ((FStar_Syntax_Const.op_Minus), (uu____7930)))
in (

let uu____7944 = (

let uu____7953 = (

let uu____7961 = (

let uu____7967 = (

let uu____7968 = (

let uu____7969 = (

let uu____7972 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7973 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7972), (uu____7973))))
in (FStar_SMTEncoding_Util.mkAdd uu____7969))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7968))
in (quant xy uu____7967))
in ((FStar_Syntax_Const.op_Addition), (uu____7961)))
in (

let uu____7979 = (

let uu____7988 = (

let uu____7996 = (

let uu____8002 = (

let uu____8003 = (

let uu____8004 = (

let uu____8007 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____8008 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____8007), (uu____8008))))
in (FStar_SMTEncoding_Util.mkMul uu____8004))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____8003))
in (quant xy uu____8002))
in ((FStar_Syntax_Const.op_Multiply), (uu____7996)))
in (

let uu____8014 = (

let uu____8023 = (

let uu____8031 = (

let uu____8037 = (

let uu____8038 = (

let uu____8039 = (

let uu____8042 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____8043 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____8042), (uu____8043))))
in (FStar_SMTEncoding_Util.mkDiv uu____8039))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____8038))
in (quant xy uu____8037))
in ((FStar_Syntax_Const.op_Division), (uu____8031)))
in (

let uu____8049 = (

let uu____8058 = (

let uu____8066 = (

let uu____8072 = (

let uu____8073 = (

let uu____8074 = (

let uu____8077 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____8078 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____8077), (uu____8078))))
in (FStar_SMTEncoding_Util.mkMod uu____8074))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____8073))
in (quant xy uu____8072))
in ((FStar_Syntax_Const.op_Modulus), (uu____8066)))
in (

let uu____8084 = (

let uu____8093 = (

let uu____8101 = (

let uu____8107 = (

let uu____8108 = (

let uu____8109 = (

let uu____8112 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____8113 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____8112), (uu____8113))))
in (FStar_SMTEncoding_Util.mkAnd uu____8109))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____8108))
in (quant xy uu____8107))
in ((FStar_Syntax_Const.op_And), (uu____8101)))
in (

let uu____8119 = (

let uu____8128 = (

let uu____8136 = (

let uu____8142 = (

let uu____8143 = (

let uu____8144 = (

let uu____8147 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____8148 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____8147), (uu____8148))))
in (FStar_SMTEncoding_Util.mkOr uu____8144))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____8143))
in (quant xy uu____8142))
in ((FStar_Syntax_Const.op_Or), (uu____8136)))
in (

let uu____8154 = (

let uu____8163 = (

let uu____8171 = (

let uu____8177 = (

let uu____8178 = (

let uu____8179 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Util.mkNot uu____8179))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____8178))
in (quant qx uu____8177))
in ((FStar_Syntax_Const.op_Negation), (uu____8171)))
in (uu____8163)::[])
in (uu____8128)::uu____8154))
in (uu____8093)::uu____8119))
in (uu____8058)::uu____8084))
in (uu____8023)::uu____8049))
in (uu____7988)::uu____8014))
in (uu____7953)::uu____7979))
in (uu____7922)::uu____7944))
in (uu____7887)::uu____7913))
in (uu____7852)::uu____7878))
in (uu____7817)::uu____7843))
in (uu____7782)::uu____7808))
in (uu____7747)::uu____7773))
in (uu____7716)::uu____7738))
in (uu____7686)::uu____7707))
in (

let mk1 = (fun l v1 -> (

let uu____8307 = (

let uu____8312 = (FStar_All.pipe_right prims1 (FStar_List.find (fun uu____8344 -> (match (uu____8344) with
| (l', uu____8353) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right uu____8312 (FStar_Option.map (fun uu____8386 -> (match (uu____8386) with
| (uu____8397, b) -> begin
(b v1)
end)))))
in (FStar_All.pipe_right uu____8307 FStar_Option.get)))
in (

let is = (fun l -> (FStar_All.pipe_right prims1 (FStar_Util.for_some (fun uu____8438 -> (match (uu____8438) with
| (l', uu____8447) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk1; is = is})))))))
end))
end))
end))


let pretype_axiom : env_t  ->  FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun env tapp vars -> (

let uu____8473 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____8473) with
| (xxsym, xx) -> begin
(

let uu____8478 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____8478) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let tapp_hash = (FStar_SMTEncoding_Term.hash_of_term tapp)
in (

let module_name = env.current_module_name
in (

let uu____8486 = (

let uu____8490 = (

let uu____8491 = (

let uu____8497 = (

let uu____8498 = (

let uu____8501 = (

let uu____8502 = (

let uu____8505 = (FStar_SMTEncoding_Util.mkApp (("PreType"), ((xx)::[])))
in ((tapp), (uu____8505)))
in (FStar_SMTEncoding_Util.mkEq uu____8502))
in ((xx_has_type), (uu____8501)))
in (FStar_SMTEncoding_Util.mkImp uu____8498))
in ((((xx_has_type)::[])::[]), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars), (uu____8497)))
in (FStar_SMTEncoding_Util.mkForall uu____8491))
in (

let uu____8518 = (

let uu____8519 = (

let uu____8520 = (

let uu____8521 = (FStar_Util.digest_of_string tapp_hash)
in (Prims.strcat "_pretyping_" uu____8521))
in (Prims.strcat module_name uu____8520))
in (varops.mk_unique uu____8519))
in ((uu____8490), (Some ("pretyping")), (uu____8518))))
in FStar_SMTEncoding_Term.Assume (uu____8486)))))
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

let uu____8551 = (

let uu____8552 = (

let uu____8556 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in ((uu____8556), (Some ("unit typing")), ("unit_typing")))
in FStar_SMTEncoding_Term.Assume (uu____8552))
in (

let uu____8558 = (

let uu____8560 = (

let uu____8561 = (

let uu____8565 = (

let uu____8566 = (

let uu____8572 = (

let uu____8573 = (

let uu____8576 = (FStar_SMTEncoding_Util.mkEq ((x), (FStar_SMTEncoding_Term.mk_Term_unit)))
in ((typing_pred), (uu____8576)))
in (FStar_SMTEncoding_Util.mkImp uu____8573))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____8572)))
in (mkForall_fuel uu____8566))
in ((uu____8565), (Some ("unit inversion")), ("unit_inversion")))
in FStar_SMTEncoding_Term.Assume (uu____8561))
in (uu____8560)::[])
in (uu____8551)::uu____8558))))
in (

let mk_bool = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Bool_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____8604 = (

let uu____8605 = (

let uu____8609 = (

let uu____8610 = (

let uu____8616 = (

let uu____8619 = (

let uu____8621 = (FStar_SMTEncoding_Term.boxBool b)
in (uu____8621)::[])
in (uu____8619)::[])
in (

let uu____8624 = (

let uu____8625 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType uu____8625 tt))
in ((uu____8616), ((bb)::[]), (uu____8624))))
in (FStar_SMTEncoding_Util.mkForall uu____8610))
in ((uu____8609), (Some ("bool typing")), ("bool_typing")))
in FStar_SMTEncoding_Term.Assume (uu____8605))
in (

let uu____8636 = (

let uu____8638 = (

let uu____8639 = (

let uu____8643 = (

let uu____8644 = (

let uu____8650 = (

let uu____8651 = (

let uu____8654 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in ((typing_pred), (uu____8654)))
in (FStar_SMTEncoding_Util.mkImp uu____8651))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____8650)))
in (mkForall_fuel uu____8644))
in ((uu____8643), (Some ("bool inversion")), ("bool_inversion")))
in FStar_SMTEncoding_Term.Assume (uu____8639))
in (uu____8638)::[])
in (uu____8604)::uu____8636))))))
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

let uu____8688 = (

let uu____8689 = (

let uu____8693 = (

let uu____8695 = (

let uu____8697 = (

let uu____8699 = (FStar_SMTEncoding_Term.boxInt a)
in (

let uu____8700 = (

let uu____8702 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____8702)::[])
in (uu____8699)::uu____8700))
in (tt)::uu____8697)
in (tt)::uu____8695)
in (("Prims.Precedes"), (uu____8693)))
in (FStar_SMTEncoding_Util.mkApp uu____8689))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8688))
in (

let precedes_y_x = (

let uu____8705 = (FStar_SMTEncoding_Util.mkApp (("Precedes"), ((y)::(x)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8705))
in (

let uu____8707 = (

let uu____8708 = (

let uu____8712 = (

let uu____8713 = (

let uu____8719 = (

let uu____8722 = (

let uu____8724 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____8724)::[])
in (uu____8722)::[])
in (

let uu____8727 = (

let uu____8728 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType uu____8728 tt))
in ((uu____8719), ((bb)::[]), (uu____8727))))
in (FStar_SMTEncoding_Util.mkForall uu____8713))
in ((uu____8712), (Some ("int typing")), ("int_typing")))
in FStar_SMTEncoding_Term.Assume (uu____8708))
in (

let uu____8739 = (

let uu____8741 = (

let uu____8742 = (

let uu____8746 = (

let uu____8747 = (

let uu____8753 = (

let uu____8754 = (

let uu____8757 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in ((typing_pred), (uu____8757)))
in (FStar_SMTEncoding_Util.mkImp uu____8754))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____8753)))
in (mkForall_fuel uu____8747))
in ((uu____8746), (Some ("int inversion")), ("int_inversion")))
in FStar_SMTEncoding_Term.Assume (uu____8742))
in (

let uu____8770 = (

let uu____8772 = (

let uu____8773 = (

let uu____8777 = (

let uu____8778 = (

let uu____8784 = (

let uu____8785 = (

let uu____8788 = (

let uu____8789 = (

let uu____8791 = (

let uu____8793 = (

let uu____8795 = (

let uu____8796 = (

let uu____8799 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____8800 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____8799), (uu____8800))))
in (FStar_SMTEncoding_Util.mkGT uu____8796))
in (

let uu____8801 = (

let uu____8803 = (

let uu____8804 = (

let uu____8807 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____8808 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____8807), (uu____8808))))
in (FStar_SMTEncoding_Util.mkGTE uu____8804))
in (

let uu____8809 = (

let uu____8811 = (

let uu____8812 = (

let uu____8815 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____8816 = (FStar_SMTEncoding_Term.unboxInt x)
in ((uu____8815), (uu____8816))))
in (FStar_SMTEncoding_Util.mkLT uu____8812))
in (uu____8811)::[])
in (uu____8803)::uu____8809))
in (uu____8795)::uu____8801))
in (typing_pred_y)::uu____8793)
in (typing_pred)::uu____8791)
in (FStar_SMTEncoding_Util.mk_and_l uu____8789))
in ((uu____8788), (precedes_y_x)))
in (FStar_SMTEncoding_Util.mkImp uu____8785))
in ((((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[]), ((xx)::(yy)::[]), (uu____8784)))
in (mkForall_fuel uu____8778))
in ((uu____8777), (Some ("well-founded ordering on nat (alt)")), ("well-founded-ordering-on-nat")))
in FStar_SMTEncoding_Term.Assume (uu____8773))
in (uu____8772)::[])
in (uu____8741)::uu____8770))
in (uu____8707)::uu____8739)))))))))))
in (

let mk_str = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.String_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____8846 = (

let uu____8847 = (

let uu____8851 = (

let uu____8852 = (

let uu____8858 = (

let uu____8861 = (

let uu____8863 = (FStar_SMTEncoding_Term.boxString b)
in (uu____8863)::[])
in (uu____8861)::[])
in (

let uu____8866 = (

let uu____8867 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType uu____8867 tt))
in ((uu____8858), ((bb)::[]), (uu____8866))))
in (FStar_SMTEncoding_Util.mkForall uu____8852))
in ((uu____8851), (Some ("string typing")), ("string_typing")))
in FStar_SMTEncoding_Term.Assume (uu____8847))
in (

let uu____8878 = (

let uu____8880 = (

let uu____8881 = (

let uu____8885 = (

let uu____8886 = (

let uu____8892 = (

let uu____8893 = (

let uu____8896 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in ((typing_pred), (uu____8896)))
in (FStar_SMTEncoding_Util.mkImp uu____8893))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____8892)))
in (mkForall_fuel uu____8886))
in ((uu____8885), (Some ("string inversion")), ("string_inversion")))
in FStar_SMTEncoding_Term.Assume (uu____8881))
in (uu____8880)::[])
in (uu____8846)::uu____8878))))))
in (

let mk_ref1 = (fun env reft_name uu____8918 -> (

let r = (("r"), (FStar_SMTEncoding_Term.Ref_sort))
in (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let refa = (

let uu____8929 = (

let uu____8933 = (

let uu____8935 = (FStar_SMTEncoding_Util.mkFreeV aa)
in (uu____8935)::[])
in ((reft_name), (uu____8933)))
in (FStar_SMTEncoding_Util.mkApp uu____8929))
in (

let refb = (

let uu____8938 = (

let uu____8942 = (

let uu____8944 = (FStar_SMTEncoding_Util.mkFreeV bb)
in (uu____8944)::[])
in ((reft_name), (uu____8942)))
in (FStar_SMTEncoding_Util.mkApp uu____8938))
in (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (

let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (

let uu____8948 = (

let uu____8949 = (

let uu____8953 = (

let uu____8954 = (

let uu____8960 = (

let uu____8961 = (

let uu____8964 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in ((typing_pred), (uu____8964)))
in (FStar_SMTEncoding_Util.mkImp uu____8961))
in ((((typing_pred)::[])::[]), ((xx)::(aa)::[]), (uu____8960)))
in (mkForall_fuel uu____8954))
in ((uu____8953), (Some ("ref inversion")), ("ref_inversion")))
in FStar_SMTEncoding_Term.Assume (uu____8949))
in (

let uu____8979 = (

let uu____8981 = (

let uu____8982 = (

let uu____8986 = (

let uu____8987 = (

let uu____8993 = (

let uu____8994 = (

let uu____8997 = (FStar_SMTEncoding_Util.mkAnd ((typing_pred), (typing_pred_b)))
in (

let uu____8998 = (

let uu____8999 = (

let uu____9002 = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let uu____9003 = (FStar_SMTEncoding_Util.mkFreeV bb)
in ((uu____9002), (uu____9003))))
in (FStar_SMTEncoding_Util.mkEq uu____8999))
in ((uu____8997), (uu____8998))))
in (FStar_SMTEncoding_Util.mkImp uu____8994))
in ((((typing_pred)::(typing_pred_b)::[])::[]), ((xx)::(aa)::(bb)::[]), (uu____8993)))
in (mkForall_fuel' (Prims.parse_int "2") uu____8987))
in ((uu____8986), (Some ("ref typing is injective")), ("ref_injectivity")))
in FStar_SMTEncoding_Term.Assume (uu____8982))
in (uu____8981)::[])
in (uu____8948)::uu____8979))))))))))
in (

let mk_true_interp = (fun env nm true_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((true_tm)::[])))
in (FStar_SMTEncoding_Term.Assume (((valid), (Some ("True interpretation")), ("true_interp"))))::[]))
in (

let mk_false_interp = (fun env nm false_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((false_tm)::[])))
in (

let uu____9045 = (

let uu____9046 = (

let uu____9050 = (FStar_SMTEncoding_Util.mkIff ((FStar_SMTEncoding_Util.mkFalse), (valid)))
in ((uu____9050), (Some ("False interpretation")), ("false_interp")))
in FStar_SMTEncoding_Term.Assume (uu____9046))
in (uu____9045)::[])))
in (

let mk_and_interp = (fun env conj uu____9061 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let valid = (

let uu____9071 = (

let uu____9075 = (

let uu____9077 = (FStar_SMTEncoding_Util.mkApp ((conj), ((a)::(b)::[])))
in (uu____9077)::[])
in (("Valid"), (uu____9075)))
in (FStar_SMTEncoding_Util.mkApp uu____9071))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____9084 = (

let uu____9085 = (

let uu____9089 = (

let uu____9090 = (

let uu____9096 = (

let uu____9097 = (

let uu____9100 = (FStar_SMTEncoding_Util.mkAnd ((valid_a), (valid_b)))
in ((uu____9100), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9097))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9096)))
in (FStar_SMTEncoding_Util.mkForall uu____9090))
in ((uu____9089), (Some ("/\\ interpretation")), ("l_and-interp")))
in FStar_SMTEncoding_Term.Assume (uu____9085))
in (uu____9084)::[])))))))))
in (

let mk_or_interp = (fun env disj uu____9124 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let valid = (

let uu____9134 = (

let uu____9138 = (

let uu____9140 = (FStar_SMTEncoding_Util.mkApp ((disj), ((a)::(b)::[])))
in (uu____9140)::[])
in (("Valid"), (uu____9138)))
in (FStar_SMTEncoding_Util.mkApp uu____9134))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____9147 = (

let uu____9148 = (

let uu____9152 = (

let uu____9153 = (

let uu____9159 = (

let uu____9160 = (

let uu____9163 = (FStar_SMTEncoding_Util.mkOr ((valid_a), (valid_b)))
in ((uu____9163), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9160))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9159)))
in (FStar_SMTEncoding_Util.mkForall uu____9153))
in ((uu____9152), (Some ("\\/ interpretation")), ("l_or-interp")))
in FStar_SMTEncoding_Term.Assume (uu____9148))
in (uu____9147)::[])))))))))
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

let uu____9201 = (

let uu____9205 = (

let uu____9207 = (FStar_SMTEncoding_Util.mkApp ((eq2), ((a)::(x1)::(y1)::[])))
in (uu____9207)::[])
in (("Valid"), (uu____9205)))
in (FStar_SMTEncoding_Util.mkApp uu____9201))
in (

let uu____9210 = (

let uu____9211 = (

let uu____9215 = (

let uu____9216 = (

let uu____9222 = (

let uu____9223 = (

let uu____9226 = (FStar_SMTEncoding_Util.mkEq ((x1), (y1)))
in ((uu____9226), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9223))
in ((((valid)::[])::[]), ((aa)::(xx1)::(yy1)::[]), (uu____9222)))
in (FStar_SMTEncoding_Util.mkForall uu____9216))
in ((uu____9215), (Some ("Eq2 interpretation")), ("eq2-interp")))
in FStar_SMTEncoding_Term.Assume (uu____9211))
in (uu____9210)::[])))))))))
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

let uu____9270 = (

let uu____9274 = (

let uu____9276 = (FStar_SMTEncoding_Util.mkApp ((eq3), ((a)::(b)::(x1)::(y1)::[])))
in (uu____9276)::[])
in (("Valid"), (uu____9274)))
in (FStar_SMTEncoding_Util.mkApp uu____9270))
in (

let uu____9279 = (

let uu____9280 = (

let uu____9284 = (

let uu____9285 = (

let uu____9291 = (

let uu____9292 = (

let uu____9295 = (FStar_SMTEncoding_Util.mkEq ((x1), (y1)))
in ((uu____9295), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9292))
in ((((valid)::[])::[]), ((aa)::(bb)::(xx1)::(yy1)::[]), (uu____9291)))
in (FStar_SMTEncoding_Util.mkForall uu____9285))
in ((uu____9284), (Some ("Eq3 interpretation")), ("eq3-interp")))
in FStar_SMTEncoding_Term.Assume (uu____9280))
in (uu____9279)::[])))))))))))
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

let uu____9333 = (

let uu____9337 = (

let uu____9339 = (FStar_SMTEncoding_Util.mkApp ((imp), ((a)::(b)::[])))
in (uu____9339)::[])
in (("Valid"), (uu____9337)))
in (FStar_SMTEncoding_Util.mkApp uu____9333))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____9346 = (

let uu____9347 = (

let uu____9351 = (

let uu____9352 = (

let uu____9358 = (

let uu____9359 = (

let uu____9362 = (FStar_SMTEncoding_Util.mkImp ((valid_a), (valid_b)))
in ((uu____9362), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9359))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9358)))
in (FStar_SMTEncoding_Util.mkForall uu____9352))
in ((uu____9351), (Some ("==> interpretation")), ("l_imp-interp")))
in FStar_SMTEncoding_Term.Assume (uu____9347))
in (uu____9346)::[])))))))))
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

let uu____9396 = (

let uu____9400 = (

let uu____9402 = (FStar_SMTEncoding_Util.mkApp ((iff), ((a)::(b)::[])))
in (uu____9402)::[])
in (("Valid"), (uu____9400)))
in (FStar_SMTEncoding_Util.mkApp uu____9396))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____9409 = (

let uu____9410 = (

let uu____9414 = (

let uu____9415 = (

let uu____9421 = (

let uu____9422 = (

let uu____9425 = (FStar_SMTEncoding_Util.mkIff ((valid_a), (valid_b)))
in ((uu____9425), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9422))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9421)))
in (FStar_SMTEncoding_Util.mkForall uu____9415))
in ((uu____9414), (Some ("<==> interpretation")), ("l_iff-interp")))
in FStar_SMTEncoding_Term.Assume (uu____9410))
in (uu____9409)::[])))))))))
in (

let mk_not_interp = (fun env l_not tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let valid = (

let uu____9455 = (

let uu____9459 = (

let uu____9461 = (FStar_SMTEncoding_Util.mkApp ((l_not), ((a)::[])))
in (uu____9461)::[])
in (("Valid"), (uu____9459)))
in (FStar_SMTEncoding_Util.mkApp uu____9455))
in (

let not_valid_a = (

let uu____9465 = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9465))
in (

let uu____9467 = (

let uu____9468 = (

let uu____9472 = (

let uu____9473 = (

let uu____9479 = (FStar_SMTEncoding_Util.mkIff ((not_valid_a), (valid)))
in ((((valid)::[])::[]), ((aa)::[]), (uu____9479)))
in (FStar_SMTEncoding_Util.mkForall uu____9473))
in ((uu____9472), (Some ("not interpretation")), ("l_not-interp")))
in FStar_SMTEncoding_Term.Assume (uu____9468))
in (uu____9467)::[]))))))
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

let uu____9515 = (

let uu____9519 = (

let uu____9521 = (FStar_SMTEncoding_Util.mkApp ((for_all1), ((a)::(b)::[])))
in (uu____9521)::[])
in (("Valid"), (uu____9519)))
in (FStar_SMTEncoding_Util.mkApp uu____9515))
in (

let valid_b_x = (

let uu____9525 = (

let uu____9529 = (

let uu____9531 = (FStar_SMTEncoding_Util.mk_ApplyTT b x1)
in (uu____9531)::[])
in (("Valid"), (uu____9529)))
in (FStar_SMTEncoding_Util.mkApp uu____9525))
in (

let uu____9533 = (

let uu____9534 = (

let uu____9538 = (

let uu____9539 = (

let uu____9545 = (

let uu____9546 = (

let uu____9549 = (

let uu____9550 = (

let uu____9556 = (

let uu____9559 = (

let uu____9561 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in (uu____9561)::[])
in (uu____9559)::[])
in (

let uu____9564 = (

let uu____9565 = (

let uu____9568 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in ((uu____9568), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp uu____9565))
in ((uu____9556), ((xx1)::[]), (uu____9564))))
in (FStar_SMTEncoding_Util.mkForall uu____9550))
in ((uu____9549), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9546))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9545)))
in (FStar_SMTEncoding_Util.mkForall uu____9539))
in ((uu____9538), (Some ("forall interpretation")), ("forall-interp")))
in FStar_SMTEncoding_Term.Assume (uu____9534))
in (uu____9533)::[]))))))))))
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

let uu____9615 = (

let uu____9619 = (

let uu____9621 = (FStar_SMTEncoding_Util.mkApp ((for_some1), ((a)::(b)::[])))
in (uu____9621)::[])
in (("Valid"), (uu____9619)))
in (FStar_SMTEncoding_Util.mkApp uu____9615))
in (

let valid_b_x = (

let uu____9625 = (

let uu____9629 = (

let uu____9631 = (FStar_SMTEncoding_Util.mk_ApplyTT b x1)
in (uu____9631)::[])
in (("Valid"), (uu____9629)))
in (FStar_SMTEncoding_Util.mkApp uu____9625))
in (

let uu____9633 = (

let uu____9634 = (

let uu____9638 = (

let uu____9639 = (

let uu____9645 = (

let uu____9646 = (

let uu____9649 = (

let uu____9650 = (

let uu____9656 = (

let uu____9659 = (

let uu____9661 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in (uu____9661)::[])
in (uu____9659)::[])
in (

let uu____9664 = (

let uu____9665 = (

let uu____9668 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in ((uu____9668), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp uu____9665))
in ((uu____9656), ((xx1)::[]), (uu____9664))))
in (FStar_SMTEncoding_Util.mkExists uu____9650))
in ((uu____9649), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9646))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9645)))
in (FStar_SMTEncoding_Util.mkForall uu____9639))
in ((uu____9638), (Some ("exists interpretation")), ("exists-interp")))
in FStar_SMTEncoding_Term.Assume (uu____9634))
in (uu____9633)::[]))))))))))
in (

let mk_range_interp = (fun env range tt -> (

let range_ty = (FStar_SMTEncoding_Util.mkApp ((range), ([])))
in (

let uu____9704 = (

let uu____9705 = (

let uu____9709 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_ty)
in (

let uu____9710 = (varops.mk_unique "typing_range_const")
in ((uu____9709), (Some ("Range_const typing")), (uu____9710))))
in FStar_SMTEncoding_Term.Assume (uu____9705))
in (uu____9704)::[])))
in (

let prims1 = (((FStar_Syntax_Const.unit_lid), (mk_unit)))::(((FStar_Syntax_Const.bool_lid), (mk_bool)))::(((FStar_Syntax_Const.int_lid), (mk_int)))::(((FStar_Syntax_Const.string_lid), (mk_str)))::(((FStar_Syntax_Const.ref_lid), (mk_ref1)))::(((FStar_Syntax_Const.true_lid), (mk_true_interp)))::(((FStar_Syntax_Const.false_lid), (mk_false_interp)))::(((FStar_Syntax_Const.and_lid), (mk_and_interp)))::(((FStar_Syntax_Const.or_lid), (mk_or_interp)))::(((FStar_Syntax_Const.eq2_lid), (mk_eq2_interp)))::(((FStar_Syntax_Const.eq3_lid), (mk_eq3_interp)))::(((FStar_Syntax_Const.imp_lid), (mk_imp_interp)))::(((FStar_Syntax_Const.iff_lid), (mk_iff_interp)))::(((FStar_Syntax_Const.not_lid), (mk_not_interp)))::(((FStar_Syntax_Const.forall_lid), (mk_forall_interp)))::(((FStar_Syntax_Const.exists_lid), (mk_exists_interp)))::(((FStar_Syntax_Const.range_lid), (mk_range_interp)))::[]
in (fun env t s tt -> (

let uu____9972 = (FStar_Util.find_opt (fun uu____9990 -> (match (uu____9990) with
| (l, uu____10000) -> begin
(FStar_Ident.lid_equals l t)
end)) prims1)
in (match (uu____9972) with
| None -> begin
[]
end
| Some (uu____10022, f) -> begin
(f env s tt)
end)))))))))))))))))))))))))


let encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____10059 = (encode_function_type_as_formula None None t env)
in (match (uu____10059) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_SMTEncoding_Term.Assume (((form), (Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str))), ((Prims.strcat "lemma_" lid.FStar_Ident.str)))))::[]))
end))))


let encode_free_var : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env fv tt t_norm quals -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____10091 = ((

let uu____10092 = ((FStar_Syntax_Util.is_pure_or_ghost_function t_norm) || (FStar_TypeChecker_Env.is_reifiable_function env.tcenv t_norm))
in (FStar_All.pipe_left Prims.op_Negation uu____10092)) || (FStar_Syntax_Util.is_lemma t_norm))
in (match (uu____10091) with
| true -> begin
(

let uu____10096 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____10096) with
| (vname, vtok, env1) -> begin
(

let arg_sorts = (

let uu____10108 = (

let uu____10109 = (FStar_Syntax_Subst.compress t_norm)
in uu____10109.FStar_Syntax_Syntax.n)
in (match (uu____10108) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____10114) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun uu____10131 -> FStar_SMTEncoding_Term.Term_sort)))
end
| uu____10134 -> begin
[]
end))
in (

let d = FStar_SMTEncoding_Term.DeclFun (((vname), (arg_sorts), (FStar_SMTEncoding_Term.Term_sort), (Some ("Uninterpreted function symbol for impure function"))))
in (

let dd = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Uninterpreted name for impure function"))))
in (((d)::(dd)::[]), (env1)))))
end))
end
| uu____10142 -> begin
(

let uu____10143 = (prims.is lid)
in (match (uu____10143) with
| true -> begin
(

let vname = (varops.new_fvar lid)
in (

let uu____10148 = (prims.mk lid vname)
in (match (uu____10148) with
| (tok, definition) -> begin
(

let env1 = (push_free_var env lid vname (Some (tok)))
in ((definition), (env1)))
end)))
end
| uu____10161 -> begin
(

let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (

let uu____10163 = (

let uu____10169 = (curried_arrow_formals_comp t_norm)
in (match (uu____10169) with
| (args, comp) -> begin
(

let comp1 = (

let uu____10180 = (FStar_TypeChecker_Env.is_reifiable_comp env.tcenv comp)
in (match (uu____10180) with
| true -> begin
(

let uu____10181 = (FStar_TypeChecker_Env.reify_comp (

let uu___153_10182 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___153_10182.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___153_10182.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___153_10182.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___153_10182.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___153_10182.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___153_10182.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___153_10182.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___153_10182.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___153_10182.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___153_10182.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___153_10182.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___153_10182.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___153_10182.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___153_10182.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___153_10182.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___153_10182.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___153_10182.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___153_10182.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___153_10182.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___153_10182.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___153_10182.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___153_10182.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___153_10182.FStar_TypeChecker_Env.qname_and_index}) comp FStar_Syntax_Syntax.U_unknown)
in (FStar_Syntax_Syntax.mk_Total uu____10181))
end
| uu____10183 -> begin
comp
end))
in (match (encode_non_total_function_typ) with
| true -> begin
(

let uu____10189 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp1)
in ((args), (uu____10189)))
end
| uu____10196 -> begin
((args), (((None), ((FStar_Syntax_Util.comp_result comp1)))))
end))
end))
in (match (uu____10163) with
| (formals, (pre_opt, res_t)) -> begin
(

let uu____10216 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____10216) with
| (vname, vtok, env1) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
end
| uu____10229 -> begin
(FStar_SMTEncoding_Util.mkApp ((vtok), ([])))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun uu___124_10253 -> (match (uu___124_10253) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(

let uu____10256 = (FStar_Util.prefix vars)
in (match (uu____10256) with
| (uu____10267, (xxsym, uu____10269)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____10279 = (

let uu____10280 = (

let uu____10284 = (

let uu____10285 = (

let uu____10291 = (

let uu____10292 = (

let uu____10295 = (

let uu____10296 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____10296))
in ((vapp), (uu____10295)))
in (FStar_SMTEncoding_Util.mkEq uu____10292))
in ((((vapp)::[])::[]), (vars), (uu____10291)))
in (FStar_SMTEncoding_Util.mkForall uu____10285))
in ((uu____10284), (Some ("Discriminator equation")), ((Prims.strcat "disc_equation_" (escape d.FStar_Ident.str)))))
in FStar_SMTEncoding_Term.Assume (uu____10280))
in (uu____10279)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(

let uu____10307 = (FStar_Util.prefix vars)
in (match (uu____10307) with
| (uu____10318, (xxsym, uu____10320)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f1 = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (

let tp_name = (mk_term_projector_name d f1)
in (

let prim_app = (FStar_SMTEncoding_Util.mkApp ((tp_name), ((xx)::[])))
in (

let uu____10334 = (

let uu____10335 = (

let uu____10339 = (

let uu____10340 = (

let uu____10346 = (FStar_SMTEncoding_Util.mkEq ((vapp), (prim_app)))
in ((((vapp)::[])::[]), (vars), (uu____10346)))
in (FStar_SMTEncoding_Util.mkForall uu____10340))
in ((uu____10339), (Some ("Projector equation")), ((Prims.strcat "proj_equation_" tp_name))))
in FStar_SMTEncoding_Term.Assume (uu____10335))
in (uu____10334)::[])))))
end))
end
| uu____10355 -> begin
[]
end)))))
in (

let uu____10356 = (encode_binders None formals env1)
in (match (uu____10356) with
| (vars, guards, env', decls1, uu____10372) -> begin
(

let uu____10379 = (match (pre_opt) with
| None -> begin
(

let uu____10384 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____10384), (decls1)))
end
| Some (p) -> begin
(

let uu____10386 = (encode_formula p env')
in (match (uu____10386) with
| (g, ds) -> begin
(

let uu____10393 = (FStar_SMTEncoding_Util.mk_and_l ((g)::guards))
in ((uu____10393), ((FStar_List.append decls1 ds))))
end))
end)
in (match (uu____10379) with
| (guard, decls11) -> begin
(

let vtok_app = (mk_Apply vtok_tm vars)
in (

let vapp = (

let uu____10402 = (

let uu____10406 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((vname), (uu____10406)))
in (FStar_SMTEncoding_Util.mkApp uu____10402))
in (

let uu____10411 = (

let vname_decl = (

let uu____10416 = (

let uu____10422 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____10427 -> FStar_SMTEncoding_Term.Term_sort)))
in ((vname), (uu____10422), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (uu____10416))
in (

let uu____10432 = (

let env2 = (

let uu___154_10436 = env1
in {bindings = uu___154_10436.bindings; depth = uu___154_10436.depth; tcenv = uu___154_10436.tcenv; warn = uu___154_10436.warn; cache = uu___154_10436.cache; nolabels = uu___154_10436.nolabels; use_zfuel_name = uu___154_10436.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = uu___154_10436.current_module_name})
in (

let uu____10437 = (

let uu____10438 = (head_normal env2 tt)
in (not (uu____10438)))
in (match (uu____10437) with
| true -> begin
(encode_term_pred None tt env2 vtok_tm)
end
| uu____10441 -> begin
(encode_term_pred None t_norm env2 vtok_tm)
end)))
in (match (uu____10432) with
| (tok_typing, decls2) -> begin
(

let tok_typing1 = (match (formals) with
| (uu____10448)::uu____10449 -> begin
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

let uu____10472 = (

let uu____10478 = (FStar_SMTEncoding_Term.mk_NoHoist f tok_typing)
in ((((vtok_app_l)::[])::((vtok_app_r)::[])::[]), ((ff)::[]), (uu____10478)))
in (FStar_SMTEncoding_Util.mkForall uu____10472))
in FStar_SMTEncoding_Term.Assume (((guarded_tok_typing), (Some ("function token typing")), ((Prims.strcat "function_token_typing_" vname)))))))))
end
| uu____10492 -> begin
FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("function token typing")), ((Prims.strcat "function_token_typing_" vname))))
end)
in (

let uu____10494 = (match (formals) with
| [] -> begin
(

let uu____10503 = (

let uu____10504 = (

let uu____10506 = (FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left (fun _0_34 -> Some (_0_34)) uu____10506))
in (push_free_var env1 lid vname uu____10504))
in (((FStar_List.append decls2 ((tok_typing1)::[]))), (uu____10503)))
end
| uu____10509 -> begin
(

let vtok_decl = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let vtok_fresh = (

let uu____10514 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((vtok), (FStar_SMTEncoding_Term.Term_sort)) uu____10514))
in (

let name_tok_corr = (

let uu____10516 = (

let uu____10520 = (

let uu____10521 = (

let uu____10527 = (FStar_SMTEncoding_Util.mkEq ((vtok_app), (vapp)))
in ((((vtok_app)::[])::((vapp)::[])::[]), (vars), (uu____10527)))
in (FStar_SMTEncoding_Util.mkForall uu____10521))
in ((uu____10520), (Some ("Name-token correspondence")), ((Prims.strcat "token_correspondence_" vname))))
in FStar_SMTEncoding_Term.Assume (uu____10516))
in (((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing1)::[]))), (env1)))))
end)
in (match (uu____10494) with
| (tok_decl, env2) -> begin
(((vname_decl)::tok_decl), (env2))
end)))
end)))
in (match (uu____10411) with
| (decls2, env2) -> begin
(

let uu____10551 = (

let res_t1 = (FStar_Syntax_Subst.compress res_t)
in (

let uu____10556 = (encode_term res_t1 env')
in (match (uu____10556) with
| (encoded_res_t, decls) -> begin
(

let uu____10564 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in ((encoded_res_t), (uu____10564), (decls)))
end)))
in (match (uu____10551) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (

let uu____10572 = (

let uu____10576 = (

let uu____10577 = (

let uu____10583 = (FStar_SMTEncoding_Util.mkImp ((guard), (ty_pred)))
in ((((vapp)::[])::[]), (vars), (uu____10583)))
in (FStar_SMTEncoding_Util.mkForall uu____10577))
in ((uu____10576), (Some ("free var typing")), ((Prims.strcat "typing_" vname))))
in FStar_SMTEncoding_Term.Assume (uu____10572))
in (

let freshness = (

let uu____10592 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New))
in (match (uu____10592) with
| true -> begin
(

let uu____10595 = (

let uu____10596 = (

let uu____10602 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (

let uu____10608 = (varops.next_id ())
in ((vname), (uu____10602), (FStar_SMTEncoding_Term.Term_sort), (uu____10608))))
in (FStar_SMTEncoding_Term.fresh_constructor uu____10596))
in (

let uu____10610 = (

let uu____10612 = (pretype_axiom env2 vapp vars)
in (uu____10612)::[])
in (uu____10595)::uu____10610))
end
| uu____10613 -> begin
[]
end))
in (

let g = (

let uu____10616 = (

let uu____10618 = (

let uu____10620 = (

let uu____10622 = (

let uu____10624 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::uu____10624)
in (FStar_List.append freshness uu____10622))
in (FStar_List.append decls3 uu____10620))
in (FStar_List.append decls2 uu____10618))
in (FStar_List.append decls11 uu____10616))
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

let uu____10646 = (try_lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____10646) with
| None -> begin
(

let uu____10669 = (encode_free_var env x t t_norm [])
in (match (uu____10669) with
| (decls, env1) -> begin
(

let uu____10684 = (lookup_lid env1 x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____10684) with
| (n1, x', uu____10703) -> begin
((((n1), (x'))), (decls), (env1))
end))
end))
end
| Some (n1, x1, uu____10715) -> begin
((((n1), (x1))), ([]), (env))
end)))


let encode_top_level_val : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env lid t quals -> (

let tt = (norm env t)
in (

let uu____10748 = (encode_free_var env lid t tt quals)
in (match (uu____10748) with
| (decls, env1) -> begin
(

let uu____10759 = (FStar_Syntax_Util.is_smt_lemma t)
in (match (uu____10759) with
| true -> begin
(

let uu____10763 = (

let uu____10765 = (encode_smt_lemma env1 lid tt)
in (FStar_List.append decls uu____10765))
in ((uu____10763), (env1)))
end
| uu____10768 -> begin
((decls), (env1))
end))
end))))


let encode_top_level_vals : env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____10793 lb -> (match (uu____10793) with
| (decls, env1) -> begin
(

let uu____10805 = (

let uu____10809 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env1 uu____10809 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (uu____10805) with
| (decls', env2) -> begin
(((FStar_List.append decls decls')), (env2))
end))
end)) (([]), (env)))))


let is_tactic : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let fstar_tactics_tactic_lid = (FStar_Syntax_Const.p2l (("FStar")::("Tactics")::("tactic")::[]))
in (

let uu____10823 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____10823) with
| (hd1, args) -> begin
(

let uu____10849 = (

let uu____10850 = (FStar_Syntax_Util.un_uinst hd1)
in uu____10850.FStar_Syntax_Syntax.n)
in (match (uu____10849) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____10854, c) -> begin
(

let effect_name = (FStar_Syntax_Util.comp_effect_name c)
in (FStar_Util.starts_with "FStar.Tactics" effect_name.FStar_Ident.str))
end
| uu____10867 -> begin
false
end))
end))))


let encode_top_level_let : env_t  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env uu____10882 quals -> (match (uu____10882) with
| (is_rec, bindings) -> begin
(

let eta_expand1 = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let uu____10931 = (FStar_Util.first_N nbinders formals)
in (match (uu____10931) with
| (formals1, extra_formals) -> begin
(

let subst1 = (FStar_List.map2 (fun uu____10971 uu____10972 -> (match (((uu____10971), (uu____10972))) with
| ((formal, uu____10982), (binder, uu____10984)) -> begin
(

let uu____10989 = (

let uu____10994 = (FStar_Syntax_Syntax.bv_to_name binder)
in ((formal), (uu____10994)))
in FStar_Syntax_Syntax.NT (uu____10989))
end)) formals1 binders)
in (

let extra_formals1 = (

let uu____10999 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun uu____11013 -> (match (uu____11013) with
| (x, i) -> begin
(

let uu____11020 = (

let uu___155_11021 = x
in (

let uu____11022 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___155_11021.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___155_11021.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____11022}))
in ((uu____11020), (i)))
end))))
in (FStar_All.pipe_right uu____10999 FStar_Syntax_Util.name_binders))
in (

let body1 = (

let uu____11034 = (

let uu____11036 = (

let uu____11037 = (FStar_Syntax_Subst.subst subst1 t)
in uu____11037.FStar_Syntax_Syntax.n)
in (FStar_All.pipe_left (fun _0_35 -> Some (_0_35)) uu____11036))
in (

let uu____11041 = (

let uu____11042 = (FStar_Syntax_Subst.compress body)
in (

let uu____11043 = (

let uu____11044 = (FStar_Syntax_Util.args_of_binders extra_formals1)
in (FStar_All.pipe_left Prims.snd uu____11044))
in (FStar_Syntax_Syntax.extend_app_n uu____11042 uu____11043)))
in (uu____11041 uu____11034 body.FStar_Syntax_Syntax.pos)))
in (((FStar_List.append binders extra_formals1)), (body1)))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (

let get_result_type = (fun c -> (

let uu____11086 = (FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c)
in (match (uu____11086) with
| true -> begin
(FStar_TypeChecker_Env.reify_comp (

let uu___156_11087 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___156_11087.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___156_11087.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___156_11087.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___156_11087.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___156_11087.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___156_11087.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___156_11087.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___156_11087.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___156_11087.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___156_11087.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___156_11087.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___156_11087.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___156_11087.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___156_11087.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___156_11087.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___156_11087.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___156_11087.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___156_11087.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___156_11087.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___156_11087.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___156_11087.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___156_11087.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___156_11087.FStar_TypeChecker_Env.qname_and_index}) c FStar_Syntax_Syntax.U_unknown)
end
| uu____11088 -> begin
(FStar_Syntax_Util.comp_result c)
end)))
in (

let rec aux = (fun norm1 t_norm1 -> (

let uu____11108 = (FStar_Syntax_Util.abs_formals e)
in (match (uu____11108) with
| (binders, body, lopt) -> begin
(match (binders) with
| (uu____11157)::uu____11158 -> begin
(

let uu____11166 = (

let uu____11167 = (FStar_Syntax_Subst.compress t_norm1)
in uu____11167.FStar_Syntax_Syntax.n)
in (match (uu____11166) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____11194 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____11194) with
| (formals1, c1) -> begin
(

let nformals = (FStar_List.length formals1)
in (

let nbinders = (FStar_List.length binders)
in (

let tres = (get_result_type c1)
in (

let uu____11220 = ((nformals < nbinders) && (FStar_Syntax_Util.is_total_comp c1))
in (match (uu____11220) with
| true -> begin
(

let uu____11238 = (FStar_Util.first_N nformals binders)
in (match (uu____11238) with
| (bs0, rest) -> begin
(

let c2 = (

let subst1 = (FStar_List.map2 (fun uu____11284 uu____11285 -> (match (((uu____11284), (uu____11285))) with
| ((x, uu____11295), (b, uu____11297)) -> begin
(

let uu____11302 = (

let uu____11307 = (FStar_Syntax_Syntax.bv_to_name b)
in ((x), (uu____11307)))
in FStar_Syntax_Syntax.NT (uu____11302))
end)) formals1 bs0)
in (FStar_Syntax_Subst.subst_comp subst1 c1))
in (

let body1 = (FStar_Syntax_Util.abs rest body lopt)
in (

let uu____11309 = (

let uu____11320 = (get_result_type c2)
in ((bs0), (body1), (bs0), (uu____11320)))
in ((uu____11309), (false)))))
end))
end
| uu____11337 -> begin
(match ((nformals > nbinders)) with
| true -> begin
(

let uu____11355 = (eta_expand1 binders formals1 body tres)
in (match (uu____11355) with
| (binders1, body1) -> begin
((((binders1), (body1), (formals1), (tres))), (false))
end))
end
| uu____11401 -> begin
((((binders), (body), (formals1), (tres))), (false))
end)
end)))))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____11407) -> begin
(

let uu____11412 = (

let uu____11423 = (aux norm1 x.FStar_Syntax_Syntax.sort)
in (Prims.fst uu____11423))
in ((uu____11412), (true)))
end
| uu____11456 when (not (norm1)) -> begin
(

let t_norm2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm1)
in (aux true t_norm2))
end
| uu____11458 -> begin
(

let uu____11459 = (

let uu____11460 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____11461 = (FStar_Syntax_Print.term_to_string t_norm1)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str uu____11460 uu____11461)))
in (failwith uu____11459))
end))
end
| uu____11474 -> begin
(

let uu____11475 = (

let uu____11476 = (FStar_Syntax_Subst.compress t_norm1)
in uu____11476.FStar_Syntax_Syntax.n)
in (match (uu____11475) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____11503 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____11503) with
| (formals1, c1) -> begin
(

let tres = (get_result_type c1)
in (

let uu____11521 = (eta_expand1 [] formals1 e tres)
in (match (uu____11521) with
| (binders1, body1) -> begin
((((binders1), (body1), (formals1), (tres))), (false))
end)))
end))
end
| uu____11569 -> begin
(((([]), (e), ([]), (t_norm1))), (false))
end))
end)
end)))
in (aux false t_norm))))
in try
(match (()) with
| () -> begin
(

let uu____11597 = (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> ((FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))))
in (match (uu____11597) with
| true -> begin
(encode_top_level_vals env bindings quals)
end
| uu____11603 -> begin
(

let uu____11604 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____11645 lb -> (match (uu____11645) with
| (toks, typs, decls, env1) -> begin
((

let uu____11696 = (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp)
in (match (uu____11696) with
| true -> begin
(Prims.raise Let_rec_unencodeable)
end
| uu____11697 -> begin
()
end));
(

let t_norm = (whnf env1 lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____11699 = (

let uu____11707 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env1 uu____11707 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (uu____11699) with
| (tok, decl, env2) -> begin
(

let uu____11732 = (

let uu____11739 = (

let uu____11745 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in ((uu____11745), (tok)))
in (uu____11739)::toks)
in ((uu____11732), ((t_norm)::typs), ((decl)::decls), (env2)))
end)));
)
end)) (([]), ([]), ([]), (env))))
in (match (uu____11604) with
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
| uu____11847 -> begin
(match (curry) with
| true -> begin
(match (ftok) with
| Some (ftok1) -> begin
(mk_Apply ftok1 vars)
end
| None -> begin
(

let uu____11852 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply uu____11852 vars))
end)
end
| uu____11853 -> begin
(

let uu____11854 = (

let uu____11858 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (uu____11858)))
in (FStar_SMTEncoding_Util.mkApp uu____11854))
end)
end))
in (

let uu____11863 = ((FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___125_11865 -> (match (uu___125_11865) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| uu____11866 -> begin
false
end)))) || (FStar_All.pipe_right typs1 (FStar_Util.for_some (fun t -> (

let uu____11869 = ((FStar_Syntax_Util.is_pure_or_ghost_function t) || (FStar_TypeChecker_Env.is_reifiable_function env1.tcenv t))
in (FStar_All.pipe_left Prims.op_Negation uu____11869))))))
in (match (uu____11863) with
| true -> begin
((decls1), (env1))
end
| uu____11874 -> begin
(match ((not (is_rec))) with
| true -> begin
(match (((bindings), (typs1), (toks1))) with
| (({FStar_Syntax_Syntax.lbname = uu____11889; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____11891; FStar_Syntax_Syntax.lbeff = uu____11892; FStar_Syntax_Syntax.lbdef = e})::[], (t_norm)::[], ((flid_fv, (f, ftok)))::[]) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____11933 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____11933) with
| (univ_subst, univ_vars1) -> begin
(

let env' = (

let uu___159_11948 = env1
in (

let uu____11949 = (FStar_TypeChecker_Env.push_univ_vars env1.tcenv univ_vars1)
in {bindings = uu___159_11948.bindings; depth = uu___159_11948.depth; tcenv = uu____11949; warn = uu___159_11948.warn; cache = uu___159_11948.cache; nolabels = uu___159_11948.nolabels; use_zfuel_name = uu___159_11948.use_zfuel_name; encode_non_total_function_typ = uu___159_11948.encode_non_total_function_typ; current_module_name = uu___159_11948.current_module_name}))
in (

let t_norm1 = (FStar_Syntax_Subst.subst univ_subst t_norm)
in (

let e1 = (

let uu____11952 = (FStar_Syntax_Subst.subst univ_subst e)
in (FStar_Syntax_Subst.compress uu____11952))
in (

let uu____11953 = (destruct_bound_function flid t_norm1 e1)
in (match (uu____11953) with
| ((binders, body, uu____11965, uu____11966), curry) -> begin
((

let uu____11973 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____11973) with
| true -> begin
(

let uu____11974 = (FStar_Syntax_Print.binders_to_string ", " binders)
in (

let uu____11975 = (FStar_Syntax_Print.term_to_string body)
in (FStar_Util.print2 "Encoding let : binders=[%s], body=%s\n" uu____11974 uu____11975)))
end
| uu____11976 -> begin
()
end));
(

let uu____11977 = (encode_binders None binders env')
in (match (uu____11977) with
| (vars, guards, env'1, binder_decls, uu____11993) -> begin
(

let body1 = (

let uu____12001 = (FStar_TypeChecker_Env.is_reifiable_function env'1.tcenv t_norm1)
in (match (uu____12001) with
| true -> begin
(reify_body env'1.tcenv body)
end
| uu____12002 -> begin
body
end))
in (

let app = (mk_app1 curry f ftok vars)
in (

let uu____12004 = (

let uu____12009 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic))
in (match (uu____12009) with
| true -> begin
(

let uu____12015 = (FStar_SMTEncoding_Term.mk_Valid app)
in (

let uu____12016 = (encode_formula body1 env'1)
in ((uu____12015), (uu____12016))))
end
| uu____12021 -> begin
(

let uu____12022 = (encode_term body1 env'1)
in ((app), (uu____12022)))
end))
in (match (uu____12004) with
| (app1, (body2, decls2)) -> begin
(

let eqn = (

let uu____12036 = (

let uu____12040 = (

let uu____12041 = (

let uu____12047 = (FStar_SMTEncoding_Util.mkEq ((app1), (body2)))
in ((((app1)::[])::[]), (vars), (uu____12047)))
in (FStar_SMTEncoding_Util.mkForall uu____12041))
in (

let uu____12053 = (

let uu____12055 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (uu____12055))
in ((uu____12040), (uu____12053), ((Prims.strcat "equation_" f)))))
in FStar_SMTEncoding_Term.Assume (uu____12036))
in (

let uu____12057 = (

let uu____12059 = (

let uu____12061 = (

let uu____12063 = (

let uu____12065 = (primitive_type_axioms env1.tcenv flid f app1)
in (FStar_List.append ((eqn)::[]) uu____12065))
in (FStar_List.append decls2 uu____12063))
in (FStar_List.append binder_decls uu____12061))
in (FStar_List.append decls1 uu____12059))
in ((uu____12057), (env1))))
end))))
end));
)
end)))))
end)))
end
| uu____12068 -> begin
(failwith "Impossible")
end)
end
| uu____12083 -> begin
(

let fuel = (

let uu____12087 = (varops.fresh "fuel")
in ((uu____12087), (FStar_SMTEncoding_Term.Fuel_sort)))
in (

let fuel_tm = (FStar_SMTEncoding_Util.mkFreeV fuel)
in (

let env0 = env1
in (

let uu____12090 = (FStar_All.pipe_right toks1 (FStar_List.fold_left (fun uu____12129 uu____12130 -> (match (((uu____12129), (uu____12130))) with
| ((gtoks, env2), (flid_fv, (f, ftok))) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let g = (

let uu____12212 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented")
in (varops.new_fvar uu____12212))
in (

let gtok = (

let uu____12214 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented_token")
in (varops.new_fvar uu____12214))
in (

let env3 = (

let uu____12216 = (

let uu____12218 = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::[])))
in (FStar_All.pipe_left (fun _0_36 -> Some (_0_36)) uu____12218))
in (push_free_var env2 flid gtok uu____12216))
in (((((flid), (f), (ftok), (g), (gtok)))::gtoks), (env3))))))
end)) (([]), (env1))))
in (match (uu____12090) with
| (gtoks, env2) -> begin
(

let gtoks1 = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env01 uu____12302 t_norm uu____12304 -> (match (((uu____12302), (uu____12304))) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = lbn; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____12329; FStar_Syntax_Syntax.lbeff = uu____12330; FStar_Syntax_Syntax.lbdef = e}) -> begin
(

let uu____12347 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____12347) with
| (univ_subst, univ_vars1) -> begin
(

let env' = (

let uu___160_12364 = env2
in (

let uu____12365 = (FStar_TypeChecker_Env.push_univ_vars env2.tcenv univ_vars1)
in {bindings = uu___160_12364.bindings; depth = uu___160_12364.depth; tcenv = uu____12365; warn = uu___160_12364.warn; cache = uu___160_12364.cache; nolabels = uu___160_12364.nolabels; use_zfuel_name = uu___160_12364.use_zfuel_name; encode_non_total_function_typ = uu___160_12364.encode_non_total_function_typ; current_module_name = uu___160_12364.current_module_name}))
in (

let t_norm1 = (FStar_Syntax_Subst.subst univ_subst t_norm)
in (

let e1 = (FStar_Syntax_Subst.subst univ_subst e)
in ((

let uu____12369 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env01.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____12369) with
| true -> begin
(

let uu____12370 = (FStar_Syntax_Print.lbname_to_string lbn)
in (

let uu____12371 = (FStar_Syntax_Print.term_to_string t_norm1)
in (

let uu____12372 = (FStar_Syntax_Print.term_to_string e1)
in (FStar_Util.print3 "Encoding let rec %s : %s = %s\n" uu____12370 uu____12371 uu____12372))))
end
| uu____12373 -> begin
()
end));
(

let uu____12374 = (destruct_bound_function flid t_norm1 e1)
in (match (uu____12374) with
| ((binders, body, formals, tres), curry) -> begin
((

let uu____12396 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env01.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____12396) with
| true -> begin
(

let uu____12397 = (FStar_Syntax_Print.binders_to_string ", " binders)
in (

let uu____12398 = (FStar_Syntax_Print.term_to_string body)
in (

let uu____12399 = (FStar_Syntax_Print.binders_to_string ", " formals)
in (

let uu____12400 = (FStar_Syntax_Print.term_to_string tres)
in (FStar_Util.print4 "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n" uu____12397 uu____12398 uu____12399 uu____12400)))))
end
| uu____12401 -> begin
()
end));
(match (curry) with
| true -> begin
(failwith "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type")
end
| uu____12403 -> begin
()
end);
(

let uu____12404 = (encode_binders None binders env')
in (match (uu____12404) with
| (vars, guards, env'1, binder_decls, uu____12422) -> begin
(

let decl_g = (

let uu____12430 = (

let uu____12436 = (

let uu____12438 = (FStar_List.map Prims.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::uu____12438)
in ((g), (uu____12436), (FStar_SMTEncoding_Term.Term_sort), (Some ("Fuel-instrumented function name"))))
in FStar_SMTEncoding_Term.DeclFun (uu____12430))
in (

let env02 = (push_zfuel_name env01 flid g)
in (

let decl_g_tok = FStar_SMTEncoding_Term.DeclFun (((gtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Token for fuel-instrumented partial applications"))))
in (

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let app = (

let uu____12453 = (

let uu____12457 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (uu____12457)))
in (FStar_SMTEncoding_Util.mkApp uu____12453))
in (

let gsapp = (

let uu____12463 = (

let uu____12467 = (

let uu____12469 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (uu____12469)::vars_tm)
in ((g), (uu____12467)))
in (FStar_SMTEncoding_Util.mkApp uu____12463))
in (

let gmax = (

let uu____12473 = (

let uu____12477 = (

let uu____12479 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (uu____12479)::vars_tm)
in ((g), (uu____12477)))
in (FStar_SMTEncoding_Util.mkApp uu____12473))
in (

let body1 = (

let uu____12483 = (FStar_TypeChecker_Env.is_reifiable_function env'1.tcenv t_norm1)
in (match (uu____12483) with
| true -> begin
(reify_body env'1.tcenv body)
end
| uu____12484 -> begin
body
end))
in (

let uu____12485 = (encode_term body1 env'1)
in (match (uu____12485) with
| (body_tm, decls2) -> begin
(

let eqn_g = (

let uu____12496 = (

let uu____12500 = (

let uu____12501 = (

let uu____12509 = (FStar_SMTEncoding_Util.mkEq ((gsapp), (body_tm)))
in ((((gsapp)::[])::[]), (Some ((Prims.parse_int "0"))), ((fuel)::vars), (uu____12509)))
in (FStar_SMTEncoding_Util.mkForall' uu____12501))
in (

let uu____12520 = (

let uu____12522 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (uu____12522))
in ((uu____12500), (uu____12520), ((Prims.strcat "equation_with_fuel_" g)))))
in FStar_SMTEncoding_Term.Assume (uu____12496))
in (

let eqn_f = (

let uu____12525 = (

let uu____12529 = (

let uu____12530 = (

let uu____12536 = (FStar_SMTEncoding_Util.mkEq ((app), (gmax)))
in ((((app)::[])::[]), (vars), (uu____12536)))
in (FStar_SMTEncoding_Util.mkForall uu____12530))
in ((uu____12529), (Some ("Correspondence of recursive function to instrumented version")), ((Prims.strcat "fuel_correspondence_" g))))
in FStar_SMTEncoding_Term.Assume (uu____12525))
in (

let eqn_g' = (

let uu____12544 = (

let uu____12548 = (

let uu____12549 = (

let uu____12555 = (

let uu____12556 = (

let uu____12559 = (

let uu____12560 = (

let uu____12564 = (

let uu____12566 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "0"))
in (uu____12566)::vars_tm)
in ((g), (uu____12564)))
in (FStar_SMTEncoding_Util.mkApp uu____12560))
in ((gsapp), (uu____12559)))
in (FStar_SMTEncoding_Util.mkEq uu____12556))
in ((((gsapp)::[])::[]), ((fuel)::vars), (uu____12555)))
in (FStar_SMTEncoding_Util.mkForall uu____12549))
in ((uu____12548), (Some ("Fuel irrelevance")), ((Prims.strcat "fuel_irrelevance_" g))))
in FStar_SMTEncoding_Term.Assume (uu____12544))
in (

let uu____12578 = (

let uu____12583 = (encode_binders None formals env02)
in (match (uu____12583) with
| (vars1, v_guards, env3, binder_decls1, uu____12600) -> begin
(

let vars_tm1 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars1)
in (

let gapp = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::vars_tm1)))
in (

let tok_corr = (

let tok_app = (

let uu____12615 = (FStar_SMTEncoding_Util.mkFreeV ((gtok), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply uu____12615 ((fuel)::vars1)))
in (

let uu____12618 = (

let uu____12622 = (

let uu____12623 = (

let uu____12629 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (gapp)))
in ((((tok_app)::[])::[]), ((fuel)::vars1), (uu____12629)))
in (FStar_SMTEncoding_Util.mkForall uu____12623))
in ((uu____12622), (Some ("Fuel token correspondence")), ((Prims.strcat "fuel_token_correspondence_" gtok))))
in FStar_SMTEncoding_Term.Assume (uu____12618)))
in (

let uu____12640 = (

let uu____12644 = (encode_term_pred None tres env3 gapp)
in (match (uu____12644) with
| (g_typing, d3) -> begin
(

let uu____12652 = (

let uu____12654 = (

let uu____12655 = (

let uu____12659 = (

let uu____12660 = (

let uu____12666 = (

let uu____12667 = (

let uu____12670 = (FStar_SMTEncoding_Util.mk_and_l v_guards)
in ((uu____12670), (g_typing)))
in (FStar_SMTEncoding_Util.mkImp uu____12667))
in ((((gapp)::[])::[]), ((fuel)::vars1), (uu____12666)))
in (FStar_SMTEncoding_Util.mkForall uu____12660))
in ((uu____12659), (Some ("Typing correspondence of token to term")), ((Prims.strcat "token_correspondence_" g))))
in FStar_SMTEncoding_Term.Assume (uu____12655))
in (uu____12654)::[])
in ((d3), (uu____12652)))
end))
in (match (uu____12640) with
| (aux_decls, typing_corr) -> begin
(((FStar_List.append binder_decls1 aux_decls)), ((FStar_List.append typing_corr ((tok_corr)::[]))))
end)))))
end))
in (match (uu____12578) with
| (aux_decls, g_typing) -> begin
(((FStar_List.append binder_decls (FStar_List.append decls2 (FStar_List.append aux_decls ((decl_g)::(decl_g_tok)::[]))))), ((FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing)), (env02))
end)))))
end))))))))))
end));
)
end));
))))
end))
end))
in (

let uu____12705 = (

let uu____12712 = (FStar_List.zip3 gtoks1 typs1 bindings)
in (FStar_List.fold_left (fun uu____12744 uu____12745 -> (match (((uu____12744), (uu____12745))) with
| ((decls2, eqns, env01), (gtok, ty, lb)) -> begin
(

let uu____12821 = (encode_one_binding env01 gtok ty lb)
in (match (uu____12821) with
| (decls', eqns', env02) -> begin
(((decls')::decls2), ((FStar_List.append eqns' eqns)), (env02))
end))
end)) (((decls1)::[]), ([]), (env0)) uu____12712))
in (match (uu____12705) with
| (decls2, eqns, env01) -> begin
(

let uu____12861 = (

let isDeclFun = (fun uu___126_12869 -> (match (uu___126_12869) with
| FStar_SMTEncoding_Term.DeclFun (uu____12870) -> begin
true
end
| uu____12876 -> begin
false
end))
in (

let uu____12877 = (FStar_All.pipe_right decls2 FStar_List.flatten)
in (FStar_All.pipe_right uu____12877 (FStar_List.partition isDeclFun))))
in (match (uu____12861) with
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

let uu____12904 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right uu____12904 (FStar_String.concat " and ")))
in (

let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in (((decl)::[]), (env))))
end))
end))


let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> ((

let uu____12937 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____12937) with
| true -> begin
(

let uu____12938 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") uu____12938))
end
| uu____12939 -> begin
()
end));
(

let nm = (

let uu____12941 = (FStar_Syntax_Util.lid_of_sigelt se)
in (match (uu____12941) with
| None -> begin
""
end
| Some (l) -> begin
l.FStar_Ident.str
end))
in (

let uu____12944 = (encode_sigelt' env se)
in (match (uu____12944) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(

let uu____12953 = (

let uu____12955 = (

let uu____12956 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (uu____12956))
in (uu____12955)::[])
in ((uu____12953), (e)))
end
| uu____12958 -> begin
(

let uu____12959 = (

let uu____12961 = (

let uu____12963 = (

let uu____12964 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____12964))
in (uu____12963)::g)
in (

let uu____12965 = (

let uu____12967 = (

let uu____12968 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____12968))
in (uu____12967)::[])
in (FStar_List.append uu____12961 uu____12965)))
in ((uu____12959), (e)))
end)
end)));
))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____12976) -> begin
(failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(

let uu____12985 = (

let uu____12986 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right uu____12986 Prims.op_Negation))
in (match (uu____12985) with
| true -> begin
(([]), (env))
end
| uu____12991 -> begin
(

let close_effect_params = (fun tm -> (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
tm
end
| uu____13006 -> begin
(

let uu____13007 = (

let uu____13010 = (

let uu____13011 = (

let uu____13026 = (FStar_All.pipe_left (fun _0_37 -> Some (_0_37)) (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[])))))
in ((ed.FStar_Syntax_Syntax.binders), (tm), (uu____13026)))
in FStar_Syntax_Syntax.Tm_abs (uu____13011))
in (FStar_Syntax_Syntax.mk uu____13010))
in (uu____13007 None tm.FStar_Syntax_Syntax.pos))
end))
in (

let encode_action = (fun env1 a -> (

let uu____13079 = (new_term_constant_and_tok_from_lid env1 a.FStar_Syntax_Syntax.action_name)
in (match (uu____13079) with
| (aname, atok, env2) -> begin
(

let uu____13089 = (FStar_Syntax_Util.arrow_formals_comp a.FStar_Syntax_Syntax.action_typ)
in (match (uu____13089) with
| (formals, uu____13099) -> begin
(

let uu____13106 = (

let uu____13109 = (close_effect_params a.FStar_Syntax_Syntax.action_defn)
in (encode_term uu____13109 env2))
in (match (uu____13106) with
| (tm, decls) -> begin
(

let a_decls = (

let uu____13117 = (

let uu____13118 = (

let uu____13124 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____13132 -> FStar_SMTEncoding_Term.Term_sort)))
in ((aname), (uu____13124), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action"))))
in FStar_SMTEncoding_Term.DeclFun (uu____13118))
in (uu____13117)::(FStar_SMTEncoding_Term.DeclFun (((atok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action token")))))::[])
in (

let uu____13139 = (

let aux = (fun uu____13168 uu____13169 -> (match (((uu____13168), (uu____13169))) with
| ((bv, uu____13196), (env3, acc_sorts, acc)) -> begin
(

let uu____13217 = (gen_term_var env3 bv)
in (match (uu____13217) with
| (xxsym, xx, env4) -> begin
((env4), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::acc_sorts), ((xx)::acc))
end))
end))
in (FStar_List.fold_right aux formals ((env2), ([]), ([]))))
in (match (uu____13139) with
| (uu____13255, xs_sorts, xs) -> begin
(

let app = (FStar_SMTEncoding_Util.mkApp ((aname), (xs)))
in (

let a_eq = (

let uu____13269 = (

let uu____13273 = (

let uu____13274 = (

let uu____13280 = (

let uu____13281 = (

let uu____13284 = (mk_Apply tm xs_sorts)
in ((app), (uu____13284)))
in (FStar_SMTEncoding_Util.mkEq uu____13281))
in ((((app)::[])::[]), (xs_sorts), (uu____13280)))
in (FStar_SMTEncoding_Util.mkForall uu____13274))
in ((uu____13273), (Some ("Action equality")), ((Prims.strcat aname "_equality"))))
in FStar_SMTEncoding_Term.Assume (uu____13269))
in (

let tok_correspondence = (

let tok_term = (FStar_SMTEncoding_Util.mkFreeV ((atok), (FStar_SMTEncoding_Term.Term_sort)))
in (

let tok_app = (mk_Apply tok_term xs_sorts)
in (

let uu____13296 = (

let uu____13300 = (

let uu____13301 = (

let uu____13307 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (app)))
in ((((tok_app)::[])::[]), (xs_sorts), (uu____13307)))
in (FStar_SMTEncoding_Util.mkForall uu____13301))
in ((uu____13300), (Some ("Action token correspondence")), ((Prims.strcat aname "_token_correspondence"))))
in FStar_SMTEncoding_Term.Assume (uu____13296))))
in ((env2), ((FStar_List.append decls (FStar_List.append a_decls ((a_eq)::(tok_correspondence)::[]))))))))
end)))
end))
end))
end)))
in (

let uu____13317 = (FStar_Util.fold_map encode_action env ed.FStar_Syntax_Syntax.actions)
in (match (uu____13317) with
| (env1, decls2) -> begin
(((FStar_List.flatten decls2)), (env1))
end))))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____13333, uu____13334, uu____13335) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid) -> begin
(

let uu____13338 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____13338) with
| (tname, ttok, env1) -> begin
(([]), (env1))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____13349, t, quals) -> begin
(

let will_encode_definition = (

let uu____13355 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___127_13357 -> (match (uu___127_13357) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Irreducible) -> begin
true
end
| uu____13360 -> begin
false
end))))
in (not (uu____13355)))
in (match (will_encode_definition) with
| true -> begin
(([]), (env))
end
| uu____13364 -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____13366 = (encode_top_level_val env fv t quals)
in (match (uu____13366) with
| (decls, env1) -> begin
(

let tname = lid.FStar_Ident.str
in (

let tsym = (FStar_SMTEncoding_Util.mkFreeV ((tname), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____13378 = (

let uu____13380 = (primitive_type_axioms env1.tcenv lid tname tsym)
in (FStar_List.append decls uu____13380))
in ((uu____13378), (env1)))))
end)))
end))
end
| FStar_Syntax_Syntax.Sig_assume (l, f, uu____13385) -> begin
(

let uu____13388 = (encode_formula f env)
in (match (uu____13388) with
| (f1, decls) -> begin
(

let g = (

let uu____13397 = (

let uu____13398 = (

let uu____13402 = (

let uu____13404 = (

let uu____13405 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" uu____13405))
in Some (uu____13404))
in (

let uu____13406 = (varops.mk_unique (Prims.strcat "assumption_" l.FStar_Ident.str))
in ((f1), (uu____13402), (uu____13406))))
in FStar_SMTEncoding_Term.Assume (uu____13398))
in (uu____13397)::[])
in (((FStar_List.append decls g)), (env)))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____13410, quals, uu____13412) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) -> begin
(

let uu____13420 = (FStar_Util.fold_map (fun env1 lb -> (

let lid = (

let uu____13427 = (

let uu____13432 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____13432.FStar_Syntax_Syntax.fv_name)
in uu____13427.FStar_Syntax_Syntax.v)
in (

let uu____13436 = (

let uu____13437 = (FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone uu____13437))
in (match (uu____13436) with
| true -> begin
(

let val_decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals))); FStar_Syntax_Syntax.sigrng = se.FStar_Syntax_Syntax.sigrng}
in (

let uu____13456 = (encode_sigelt' env1 val_decl)
in (match (uu____13456) with
| (decls, env2) -> begin
((env2), (decls))
end)))
end
| uu____13463 -> begin
((env1), ([]))
end)))) env (Prims.snd lbs))
in (match (uu____13420) with
| (env1, decls) -> begin
(((FStar_List.flatten decls)), (env1))
end))
end
| FStar_Syntax_Syntax.Sig_let ((uu____13473, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t1); FStar_Syntax_Syntax.lbunivs = uu____13475; FStar_Syntax_Syntax.lbtyp = uu____13476; FStar_Syntax_Syntax.lbeff = uu____13477; FStar_Syntax_Syntax.lbdef = uu____13478})::[]), uu____13479, uu____13480, uu____13481) when (FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid) -> begin
(

let uu____13497 = (new_term_constant_and_tok_from_lid env b2t1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____13497) with
| (tname, ttok, env1) -> begin
(

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let valid_b2t_x = (

let uu____13515 = (

let uu____13519 = (

let uu____13521 = (FStar_SMTEncoding_Util.mkApp (("Prims.b2t"), ((x)::[])))
in (uu____13521)::[])
in (("Valid"), (uu____13519)))
in (FStar_SMTEncoding_Util.mkApp uu____13515))
in (

let decls = (

let uu____13526 = (

let uu____13528 = (

let uu____13529 = (

let uu____13533 = (

let uu____13534 = (

let uu____13540 = (

let uu____13541 = (

let uu____13544 = (FStar_SMTEncoding_Util.mkApp (("BoxBool_proj_0"), ((x)::[])))
in ((valid_b2t_x), (uu____13544)))
in (FStar_SMTEncoding_Util.mkEq uu____13541))
in ((((valid_b2t_x)::[])::[]), ((xx)::[]), (uu____13540)))
in (FStar_SMTEncoding_Util.mkForall uu____13534))
in ((uu____13533), (Some ("b2t def")), ("b2t_def")))
in FStar_SMTEncoding_Term.Assume (uu____13529))
in (uu____13528)::[])
in (FStar_SMTEncoding_Term.DeclFun (((tname), ((FStar_SMTEncoding_Term.Term_sort)::[]), (FStar_SMTEncoding_Term.Term_sort), (None))))::uu____13526)
in ((decls), (env1))))))
end))
end
| FStar_Syntax_Syntax.Sig_let (uu____13561, uu____13562, quals, uu____13564) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___128_13572 -> (match (uu___128_13572) with
| FStar_Syntax_Syntax.Discriminator (uu____13573) -> begin
true
end
| uu____13574 -> begin
false
end)))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let (uu____13576, lids, quals, uu____13579) when ((FStar_All.pipe_right lids (FStar_Util.for_some (fun l -> (

let uu____13588 = (

let uu____13589 = (FStar_List.hd l.FStar_Ident.ns)
in uu____13589.FStar_Ident.idText)
in (uu____13588 = "Prims"))))) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___129_13591 -> (match (uu___129_13591) with
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
true
end
| uu____13592 -> begin
false
end))))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____13595, quals, uu____13597) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___130_13609 -> (match (uu___130_13609) with
| FStar_Syntax_Syntax.Projector (uu____13610) -> begin
true
end
| uu____13613 -> begin
false
end)))) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____13620 = (try_lookup_free_var env l)
in (match (uu____13620) with
| Some (uu____13624) -> begin
(([]), (env))
end
| None -> begin
(

let se1 = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l)}
in (encode_sigelt env se1))
end))))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), uu____13633, quals, uu____13635) -> begin
(encode_top_level_let env ((is_rec), (bindings)) quals)
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____13649, uu____13650) -> begin
(

let uu____13657 = (encode_signature env ses)
in (match (uu____13657) with
| (g, env1) -> begin
(

let uu____13667 = (FStar_All.pipe_right g (FStar_List.partition (fun uu___131_13677 -> (match (uu___131_13677) with
| FStar_SMTEncoding_Term.Assume (uu____13678, Some ("inversion axiom"), uu____13679) -> begin
false
end
| uu____13681 -> begin
true
end))))
in (match (uu____13667) with
| (g', inversions) -> begin
(

let uu____13690 = (FStar_All.pipe_right g' (FStar_List.partition (fun uu___132_13700 -> (match (uu___132_13700) with
| FStar_SMTEncoding_Term.DeclFun (uu____13701) -> begin
true
end
| uu____13707 -> begin
false
end))))
in (match (uu____13690) with
| (decls, rest) -> begin
(((FStar_List.append decls (FStar_List.append rest inversions))), (env1))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, uu____13718, tps, k, uu____13721, datas, quals) -> begin
(

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___133_13732 -> (match (uu___133_13732) with
| (FStar_Syntax_Syntax.Logic) | (FStar_Syntax_Syntax.Assumption) -> begin
true
end
| uu____13733 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> (match (is_logical) with
| true -> begin
(

let uu____13740 = c
in (match (uu____13740) with
| (name, args, uu____13744, uu____13745, uu____13746) -> begin
(

let uu____13749 = (

let uu____13750 = (

let uu____13756 = (FStar_All.pipe_right args (FStar_List.map (fun uu____13763 -> (match (uu____13763) with
| (uu____13767, sort, uu____13769) -> begin
sort
end))))
in ((name), (uu____13756), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (uu____13750))
in (uu____13749)::[])
end))
end
| uu____13772 -> begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end))
in (

let inversion_axioms = (fun tapp vars -> (

let uu____13787 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (

let uu____13790 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right uu____13790 FStar_Option.isNone)))))
in (match (uu____13787) with
| true -> begin
[]
end
| uu____13806 -> begin
(

let uu____13807 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____13807) with
| (xxsym, xx) -> begin
(

let uu____13813 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun uu____13824 l -> (match (uu____13824) with
| (out, decls) -> begin
(

let uu____13836 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (uu____13836) with
| (uu____13842, data_t) -> begin
(

let uu____13844 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (uu____13844) with
| (args, res) -> begin
(

let indices = (

let uu____13873 = (

let uu____13874 = (FStar_Syntax_Subst.compress res)
in uu____13874.FStar_Syntax_Syntax.n)
in (match (uu____13873) with
| FStar_Syntax_Syntax.Tm_app (uu____13882, indices) -> begin
indices
end
| uu____13898 -> begin
[]
end))
in (

let env1 = (FStar_All.pipe_right args (FStar_List.fold_left (fun env1 uu____13910 -> (match (uu____13910) with
| (x, uu____13914) -> begin
(

let uu____13915 = (

let uu____13916 = (

let uu____13920 = (mk_term_projector_name l x)
in ((uu____13920), ((xx)::[])))
in (FStar_SMTEncoding_Util.mkApp uu____13916))
in (push_term_var env1 x uu____13915))
end)) env))
in (

let uu____13922 = (encode_args indices env1)
in (match (uu____13922) with
| (indices1, decls') -> begin
((match (((FStar_List.length indices1) <> (FStar_List.length vars))) with
| true -> begin
(failwith "Impossible")
end
| uu____13940 -> begin
()
end);
(

let eqs = (

let uu____13942 = (FStar_List.map2 (fun v1 a -> (

let uu____13950 = (

let uu____13953 = (FStar_SMTEncoding_Util.mkFreeV v1)
in ((uu____13953), (a)))
in (FStar_SMTEncoding_Util.mkEq uu____13950))) vars indices1)
in (FStar_All.pipe_right uu____13942 FStar_SMTEncoding_Util.mk_and_l))
in (

let uu____13955 = (

let uu____13956 = (

let uu____13959 = (

let uu____13960 = (

let uu____13963 = (mk_data_tester env1 l xx)
in ((uu____13963), (eqs)))
in (FStar_SMTEncoding_Util.mkAnd uu____13960))
in ((out), (uu____13959)))
in (FStar_SMTEncoding_Util.mkOr uu____13956))
in ((uu____13955), ((FStar_List.append decls decls')))));
)
end))))
end))
end))
end)) ((FStar_SMTEncoding_Util.mkFalse), ([]))))
in (match (uu____13813) with
| (data_ax, decls) -> begin
(

let uu____13971 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____13971) with
| (ffsym, ff) -> begin
(

let fuel_guarded_inversion = (

let xx_has_type_sfuel = (match (((FStar_List.length datas) > (Prims.parse_int "1"))) with
| true -> begin
(

let uu____13982 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((ff)::[])))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel uu____13982 xx tapp))
end
| uu____13984 -> begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end)
in (

let uu____13985 = (

let uu____13989 = (

let uu____13990 = (

let uu____13996 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (

let uu____14004 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_sfuel), (data_ax)))
in ((((xx_has_type_sfuel)::[])::[]), (uu____13996), (uu____14004))))
in (FStar_SMTEncoding_Util.mkForall uu____13990))
in (

let uu____14012 = (varops.mk_unique (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str))
in ((uu____13989), (Some ("inversion axiom")), (uu____14012))))
in FStar_SMTEncoding_Term.Assume (uu____13985)))
in (

let pattern_guarded_inversion = (

let uu____14016 = ((contains_name env "Prims.inversion") && ((FStar_List.length datas) > (Prims.parse_int "1")))
in (match (uu____14016) with
| true -> begin
(

let xx_has_type_fuel = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let pattern_guard = (FStar_SMTEncoding_Util.mkApp (("Prims.inversion"), ((tapp)::[])))
in (

let uu____14024 = (

let uu____14025 = (

let uu____14029 = (

let uu____14030 = (

let uu____14036 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (

let uu____14044 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_fuel), (data_ax)))
in ((((xx_has_type_fuel)::(pattern_guard)::[])::[]), (uu____14036), (uu____14044))))
in (FStar_SMTEncoding_Util.mkForall uu____14030))
in (

let uu____14052 = (varops.mk_unique (Prims.strcat "pattern_guarded_inversion_" t.FStar_Ident.str))
in ((uu____14029), (Some ("inversion axiom")), (uu____14052))))
in FStar_SMTEncoding_Term.Assume (uu____14025))
in (uu____14024)::[])))
end
| uu____14054 -> begin
[]
end))
in (FStar_List.append decls (FStar_List.append ((fuel_guarded_inversion)::[]) pattern_guarded_inversion))))
end))
end))
end))
end)))
in (

let uu____14055 = (

let uu____14063 = (

let uu____14064 = (FStar_Syntax_Subst.compress k)
in uu____14064.FStar_Syntax_Syntax.n)
in (match (uu____14063) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
(((FStar_List.append tps formals)), ((FStar_Syntax_Util.comp_result kres)))
end
| uu____14093 -> begin
((tps), (k))
end))
in (match (uu____14055) with
| (formals, res) -> begin
(

let uu____14108 = (FStar_Syntax_Subst.open_term formals res)
in (match (uu____14108) with
| (formals1, res1) -> begin
(

let uu____14115 = (encode_binders None formals1 env)
in (match (uu____14115) with
| (vars, guards, env', binder_decls, uu____14130) -> begin
(

let uu____14137 = (new_term_constant_and_tok_from_lid env t)
in (match (uu____14137) with
| (tname, ttok, env1) -> begin
(

let ttok_tm = (FStar_SMTEncoding_Util.mkApp ((ttok), ([])))
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let tapp = (

let uu____14150 = (

let uu____14154 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((tname), (uu____14154)))
in (FStar_SMTEncoding_Util.mkApp uu____14150))
in (

let uu____14159 = (

let tname_decl = (

let uu____14165 = (

let uu____14166 = (FStar_All.pipe_right vars (FStar_List.map (fun uu____14181 -> (match (uu____14181) with
| (n1, s) -> begin
(((Prims.strcat tname n1)), (s), (false))
end))))
in (

let uu____14189 = (varops.next_id ())
in ((tname), (uu____14166), (FStar_SMTEncoding_Term.Term_sort), (uu____14189), (false))))
in (constructor_or_logic_type_decl uu____14165))
in (

let uu____14194 = (match (vars) with
| [] -> begin
(

let uu____14201 = (

let uu____14202 = (

let uu____14204 = (FStar_SMTEncoding_Util.mkApp ((tname), ([])))
in (FStar_All.pipe_left (fun _0_38 -> Some (_0_38)) uu____14204))
in (push_free_var env1 t tname uu____14202))
in (([]), (uu____14201)))
end
| uu____14208 -> begin
(

let ttok_decl = FStar_SMTEncoding_Term.DeclFun (((ttok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("token"))))
in (

let ttok_fresh = (

let uu____14214 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ttok), (FStar_SMTEncoding_Term.Term_sort)) uu____14214))
in (

let ttok_app = (mk_Apply ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (

let uu____14223 = (

let uu____14227 = (

let uu____14228 = (

let uu____14236 = (FStar_SMTEncoding_Util.mkEq ((ttok_app), (tapp)))
in ((pats), (None), (vars), (uu____14236)))
in (FStar_SMTEncoding_Util.mkForall' uu____14228))
in ((uu____14227), (Some ("name-token correspondence")), ((Prims.strcat "token_correspondence_" ttok))))
in FStar_SMTEncoding_Term.Assume (uu____14223))
in (((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[]), (env1)))))))
end)
in (match (uu____14194) with
| (tok_decls, env2) -> begin
(((FStar_List.append tname_decl tok_decls)), (env2))
end)))
in (match (uu____14159) with
| (decls, env2) -> begin
(

let kindingAx = (

let uu____14259 = (encode_term_pred None res1 env' tapp)
in (match (uu____14259) with
| (k1, decls1) -> begin
(

let karr = (match (((FStar_List.length formals1) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____14273 = (

let uu____14274 = (

let uu____14278 = (

let uu____14279 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____14279))
in ((uu____14278), (Some ("kinding")), ((Prims.strcat "pre_kinding_" ttok))))
in FStar_SMTEncoding_Term.Assume (uu____14274))
in (uu____14273)::[])
end
| uu____14281 -> begin
[]
end)
in (

let uu____14282 = (

let uu____14284 = (

let uu____14286 = (

let uu____14287 = (

let uu____14291 = (

let uu____14292 = (

let uu____14298 = (FStar_SMTEncoding_Util.mkImp ((guard), (k1)))
in ((((tapp)::[])::[]), (vars), (uu____14298)))
in (FStar_SMTEncoding_Util.mkForall uu____14292))
in ((uu____14291), (None), ((Prims.strcat "kinding_" ttok))))
in FStar_SMTEncoding_Term.Assume (uu____14287))
in (uu____14286)::[])
in (FStar_List.append karr uu____14284))
in (FStar_List.append decls1 uu____14282)))
end))
in (

let aux = (

let uu____14307 = (

let uu____14309 = (inversion_axioms tapp vars)
in (

let uu____14311 = (

let uu____14313 = (pretype_axiom env2 tapp vars)
in (uu____14313)::[])
in (FStar_List.append uu____14309 uu____14311)))
in (FStar_List.append kindingAx uu____14307))
in (

let g = (FStar_List.append decls (FStar_List.append binder_decls aux))
in ((g), (env2)))))
end)))))
end))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____14318, uu____14319, uu____14320, uu____14321, uu____14322, uu____14323) when (FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____14330, t, uu____14332, n_tps, quals, uu____14335) -> begin
(

let uu____14340 = (new_term_constant_and_tok_from_lid env d)
in (match (uu____14340) with
| (ddconstrsym, ddtok, env1) -> begin
(

let ddtok_tm = (FStar_SMTEncoding_Util.mkApp ((ddtok), ([])))
in (

let uu____14351 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____14351) with
| (formals, t_res) -> begin
(

let uu____14373 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____14373) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (

let uu____14382 = (encode_binders (Some (fuel_tm)) formals env1)
in (match (uu____14382) with
| (vars, guards, env', binder_decls, names1) -> begin
(

let fields = (FStar_All.pipe_right names1 (FStar_List.mapi (fun n1 x -> (

let projectible = true
in (

let uu____14420 = (mk_term_projector_name d x)
in ((uu____14420), (FStar_SMTEncoding_Term.Term_sort), (projectible)))))))
in (

let datacons = (

let uu____14422 = (

let uu____14432 = (varops.next_id ())
in ((ddconstrsym), (fields), (FStar_SMTEncoding_Term.Term_sort), (uu____14432), (true)))
in (FStar_All.pipe_right uu____14422 FStar_SMTEncoding_Term.constructor_to_decl))
in (

let app = (mk_Apply ddtok_tm vars)
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (

let uu____14454 = (encode_term_pred None t env1 ddtok_tm)
in (match (uu____14454) with
| (tok_typing, decls3) -> begin
(

let tok_typing1 = (match (fields) with
| (uu____14462)::uu____14463 -> begin
(

let ff = (("ty"), (FStar_SMTEncoding_Term.Term_sort))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV ff)
in (

let vtok_app_l = (mk_Apply ddtok_tm ((ff)::[]))
in (

let vtok_app_r = (mk_Apply f ((((ddtok), (FStar_SMTEncoding_Term.Term_sort)))::[]))
in (

let uu____14488 = (

let uu____14494 = (FStar_SMTEncoding_Term.mk_NoHoist f tok_typing)
in ((((vtok_app_l)::[])::((vtok_app_r)::[])::[]), ((ff)::[]), (uu____14494)))
in (FStar_SMTEncoding_Util.mkForall uu____14488))))))
end
| uu____14507 -> begin
tok_typing
end)
in (

let uu____14512 = (encode_binders (Some (fuel_tm)) formals env1)
in (match (uu____14512) with
| (vars', guards', env'', decls_formals, uu____14527) -> begin
(

let uu____14534 = (

let xvars1 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars')
in (

let dapp1 = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars1)))
in (encode_term_pred (Some (fuel_tm)) t_res env'' dapp1)))
in (match (uu____14534) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_SMTEncoding_Util.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| uu____14553 -> begin
(

let uu____14557 = (

let uu____14558 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ddtok), (FStar_SMTEncoding_Term.Term_sort)) uu____14558))
in (uu____14557)::[])
end)
in (

let encode_elim = (fun uu____14565 -> (

let uu____14566 = (FStar_Syntax_Util.head_and_args t_res)
in (match (uu____14566) with
| (head1, args) -> begin
(

let uu____14595 = (

let uu____14596 = (FStar_Syntax_Subst.compress head1)
in uu____14596.FStar_Syntax_Syntax.n)
in (match (uu____14595) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let uu____14614 = (encode_args args env')
in (match (uu____14614) with
| (encoded_args, arg_decls) -> begin
(

let guards_for_parameter = (fun arg xv -> (

let fv1 = (match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv1) -> begin
fv1
end
| uu____14640 -> begin
(failwith "Impossible: parameter must be a variable")
end)
in (

let guards1 = (FStar_All.pipe_right guards (FStar_List.collect (fun g -> (

let uu____14648 = (

let uu____14649 = (FStar_SMTEncoding_Term.free_variables g)
in (FStar_List.contains fv1 uu____14649))
in (match (uu____14648) with
| true -> begin
(

let uu____14656 = (FStar_SMTEncoding_Term.subst g fv1 xv)
in (uu____14656)::[])
end
| uu____14657 -> begin
[]
end)))))
in (FStar_SMTEncoding_Util.mk_and_l guards1))))
in (

let uu____14658 = (FStar_List.fold_left (fun uu____14671 arg -> (match (uu____14671) with
| (env2, arg_vars, eqns_or_guards, i) -> begin
(

let uu____14693 = (

let uu____14697 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in (gen_term_var env2 uu____14697))
in (match (uu____14693) with
| (uu____14704, xv, env3) -> begin
(

let eqns = (match ((i < n_tps)) with
| true -> begin
(

let uu____14710 = (guards_for_parameter arg xv)
in (uu____14710)::eqns_or_guards)
end
| uu____14711 -> begin
(

let uu____14712 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (uu____14712)::eqns_or_guards)
end)
in ((env3), ((xv)::arg_vars), (eqns), ((i + (Prims.parse_int "1")))))
end))
end)) ((env'), ([]), ([]), ((Prims.parse_int "0"))) encoded_args)
in (match (uu____14658) with
| (uu____14720, arg_vars, elim_eqns_or_guards, uu____14723) -> begin
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

let uu____14742 = (

let uu____14746 = (

let uu____14747 = (

let uu____14753 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____14759 = (

let uu____14760 = (

let uu____14763 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append elim_eqns_or_guards guards))
in ((ty_pred), (uu____14763)))
in (FStar_SMTEncoding_Util.mkImp uu____14760))
in ((((ty_pred)::[])::[]), (uu____14753), (uu____14759))))
in (FStar_SMTEncoding_Util.mkForall uu____14747))
in ((uu____14746), (Some ("data constructor typing elim")), ((Prims.strcat "data_elim_" ddconstrsym))))
in FStar_SMTEncoding_Term.Assume (uu____14742))
in (

let subterm_ordering = (match ((FStar_Ident.lid_equals d FStar_Syntax_Const.lextop_lid)) with
| true -> begin
(

let x = (

let uu____14776 = (varops.fresh "x")
in ((uu____14776), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (

let uu____14778 = (

let uu____14782 = (

let uu____14783 = (

let uu____14789 = (

let uu____14792 = (

let uu____14794 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in (uu____14794)::[])
in (uu____14792)::[])
in (

let uu____14797 = (

let uu____14798 = (

let uu____14801 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (

let uu____14802 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in ((uu____14801), (uu____14802))))
in (FStar_SMTEncoding_Util.mkImp uu____14798))
in ((uu____14789), ((x)::[]), (uu____14797))))
in (FStar_SMTEncoding_Util.mkForall uu____14783))
in (

let uu____14812 = (varops.mk_unique "lextop")
in ((uu____14782), (Some ("lextop is top")), (uu____14812))))
in FStar_SMTEncoding_Term.Assume (uu____14778))))
end
| uu____14814 -> begin
(

let prec = (

let uu____14817 = (FStar_All.pipe_right vars (FStar_List.mapi (fun i v1 -> (match ((i < n_tps)) with
| true -> begin
[]
end
| uu____14831 -> begin
(

let uu____14832 = (

let uu____14833 = (FStar_SMTEncoding_Util.mkFreeV v1)
in (FStar_SMTEncoding_Util.mk_Precedes uu____14833 dapp1))
in (uu____14832)::[])
end))))
in (FStar_All.pipe_right uu____14817 FStar_List.flatten))
in (

let uu____14837 = (

let uu____14841 = (

let uu____14842 = (

let uu____14848 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____14854 = (

let uu____14855 = (

let uu____14858 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (uu____14858)))
in (FStar_SMTEncoding_Util.mkImp uu____14855))
in ((((ty_pred)::[])::[]), (uu____14848), (uu____14854))))
in (FStar_SMTEncoding_Util.mkForall uu____14842))
in ((uu____14841), (Some ("subterm ordering")), ((Prims.strcat "subterm_ordering_" ddconstrsym))))
in FStar_SMTEncoding_Term.Assume (uu____14837)))
end)
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end)))
end)))
end
| uu____14868 -> begin
((

let uu____14870 = (

let uu____14871 = (FStar_Syntax_Print.lid_to_string d)
in (

let uu____14872 = (FStar_Syntax_Print.term_to_string head1)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" uu____14871 uu____14872)))
in (FStar_Errors.warn se.FStar_Syntax_Syntax.sigrng uu____14870));
(([]), ([]));
)
end))
end)))
in (

let uu____14875 = (encode_elim ())
in (match (uu____14875) with
| (decls2, elim) -> begin
(

let g = (

let uu____14887 = (

let uu____14889 = (

let uu____14891 = (

let uu____14893 = (

let uu____14895 = (

let uu____14896 = (

let uu____14902 = (

let uu____14904 = (

let uu____14905 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" uu____14905))
in Some (uu____14904))
in ((ddtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (uu____14902)))
in FStar_SMTEncoding_Term.DeclFun (uu____14896))
in (uu____14895)::[])
in (

let uu____14908 = (

let uu____14910 = (

let uu____14912 = (

let uu____14914 = (

let uu____14916 = (

let uu____14918 = (

let uu____14920 = (

let uu____14921 = (

let uu____14925 = (

let uu____14926 = (

let uu____14932 = (FStar_SMTEncoding_Util.mkEq ((app), (dapp)))
in ((((app)::[])::[]), (vars), (uu____14932)))
in (FStar_SMTEncoding_Util.mkForall uu____14926))
in ((uu____14925), (Some ("equality for proxy")), ((Prims.strcat "equality_tok_" ddtok))))
in FStar_SMTEncoding_Term.Assume (uu____14921))
in (

let uu____14939 = (

let uu____14941 = (

let uu____14942 = (

let uu____14946 = (

let uu____14947 = (

let uu____14953 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) vars')
in (

let uu____14959 = (FStar_SMTEncoding_Util.mkImp ((guard'), (ty_pred')))
in ((((ty_pred')::[])::[]), (uu____14953), (uu____14959))))
in (FStar_SMTEncoding_Util.mkForall uu____14947))
in ((uu____14946), (Some ("data constructor typing intro")), ((Prims.strcat "data_typing_intro_" ddtok))))
in FStar_SMTEncoding_Term.Assume (uu____14942))
in (uu____14941)::[])
in (uu____14920)::uu____14939))
in (FStar_SMTEncoding_Term.Assume (((tok_typing1), (Some ("typing for data constructor proxy")), ((Prims.strcat "typing_tok_" ddtok)))))::uu____14918)
in (FStar_List.append uu____14916 elim))
in (FStar_List.append decls_pred uu____14914))
in (FStar_List.append decls_formals uu____14912))
in (FStar_List.append proxy_fresh uu____14910))
in (FStar_List.append uu____14893 uu____14908)))
in (FStar_List.append decls3 uu____14891))
in (FStar_List.append decls2 uu____14889))
in (FStar_List.append binder_decls uu____14887))
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
and encode_signature : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun uu____14980 se -> (match (uu____14980) with
| (g, env1) -> begin
(

let uu____14992 = (encode_sigelt env1 se)
in (match (uu____14992) with
| (g', env2) -> begin
(((FStar_List.append g g')), (env2))
end))
end)) (([]), (env)))))


let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env bindings -> (

let encode_binding = (fun b uu____15028 -> (match (uu____15028) with
| (i, decls, env1) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (uu____15046) -> begin
(((i + (Prims.parse_int "1"))), ([]), (env1))
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env1.tcenv x.FStar_Syntax_Syntax.sort)
in ((

let uu____15051 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____15051) with
| true -> begin
(

let uu____15052 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____15053 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____15054 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" uu____15052 uu____15053 uu____15054))))
end
| uu____15055 -> begin
()
end));
(

let uu____15056 = (encode_term t1 env1)
in (match (uu____15056) with
| (t, decls') -> begin
(

let t_hash = (FStar_SMTEncoding_Term.hash_of_term t)
in (

let uu____15066 = (

let uu____15070 = (

let uu____15071 = (

let uu____15072 = (FStar_Util.digest_of_string t_hash)
in (Prims.strcat uu____15072 (Prims.strcat "_" (Prims.string_of_int i))))
in (Prims.strcat "x_" uu____15071))
in (new_term_constant_from_string env1 x uu____15070))
in (match (uu____15066) with
| (xxsym, xx, env') -> begin
(

let t2 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel None xx t)
in (

let caption = (

let uu____15083 = (FStar_Options.log_queries ())
in (match (uu____15083) with
| true -> begin
(

let uu____15085 = (

let uu____15086 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____15087 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____15088 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" uu____15086 uu____15087 uu____15088))))
in Some (uu____15085))
end
| uu____15089 -> begin
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
| FStar_TypeChecker_Env.Binding_lid (x, (uu____15099, t)) -> begin
(

let t_norm = (whnf env1 t)
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____15108 = (encode_free_var env1 fv t t_norm [])
in (match (uu____15108) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))))
end
| (FStar_TypeChecker_Env.Binding_sig_inst (_, se, _)) | (FStar_TypeChecker_Env.Binding_sig (_, se)) -> begin
(

let uu____15127 = (encode_sigelt env1 se)
in (match (uu____15127) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))
end)
end))
in (

let uu____15137 = (FStar_List.fold_right encode_binding bindings (((Prims.parse_int "0")), ([]), (env)))
in (match (uu____15137) with
| (uu____15149, decls, env1) -> begin
((decls), (env1))
end))))


let encode_labels = (fun labs -> (

let prefix1 = (FStar_All.pipe_right labs (FStar_List.map (fun uu____15194 -> (match (uu____15194) with
| (l, uu____15201, uu____15202) -> begin
FStar_SMTEncoding_Term.DeclFun ((((Prims.fst l)), ([]), (FStar_SMTEncoding_Term.Bool_sort), (None)))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun uu____15223 -> (match (uu____15223) with
| (l, uu____15231, uu____15232) -> begin
(

let uu____15237 = (FStar_All.pipe_left (fun _0_39 -> FStar_SMTEncoding_Term.Echo (_0_39)) (Prims.fst l))
in (

let uu____15238 = (

let uu____15240 = (

let uu____15241 = (FStar_SMTEncoding_Util.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (uu____15241))
in (uu____15240)::[])
in (uu____15237)::uu____15238))
end))))
in ((prefix1), (suffix)))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (

let uu____15252 = (

let uu____15254 = (

let uu____15255 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (

let uu____15267 = (

let uu____15268 = (FStar_TypeChecker_Env.current_module tcenv)
in (FStar_All.pipe_right uu____15268 FStar_Ident.string_of_lid))
in {bindings = []; depth = (Prims.parse_int "0"); tcenv = tcenv; warn = true; cache = uu____15255; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true; current_module_name = uu____15267}))
in (uu____15254)::[])
in (FStar_ST.write last_env uu____15252)))


let get_env : FStar_Ident.lident  ->  FStar_TypeChecker_Env.env  ->  env_t = (fun cmn tcenv -> (

let uu____15278 = (FStar_ST.read last_env)
in (match (uu____15278) with
| [] -> begin
(failwith "No env; call init first!")
end
| (e)::uu____15284 -> begin
(

let uu___161_15286 = e
in (

let uu____15287 = (FStar_Ident.string_of_lid cmn)
in {bindings = uu___161_15286.bindings; depth = uu___161_15286.depth; tcenv = tcenv; warn = uu___161_15286.warn; cache = uu___161_15286.cache; nolabels = uu___161_15286.nolabels; use_zfuel_name = uu___161_15286.use_zfuel_name; encode_non_total_function_typ = uu___161_15286.encode_non_total_function_typ; current_module_name = uu____15287}))
end)))


let set_env : env_t  ->  Prims.unit = (fun env -> (

let uu____15291 = (FStar_ST.read last_env)
in (match (uu____15291) with
| [] -> begin
(failwith "Empty env stack")
end
| (uu____15296)::tl1 -> begin
(FStar_ST.write last_env ((env)::tl1))
end)))


let push_env : Prims.unit  ->  Prims.unit = (fun uu____15304 -> (

let uu____15305 = (FStar_ST.read last_env)
in (match (uu____15305) with
| [] -> begin
(failwith "Empty env stack")
end
| (hd1)::tl1 -> begin
(

let refs = (FStar_Util.smap_copy hd1.cache)
in (

let top = (

let uu___162_15326 = hd1
in {bindings = uu___162_15326.bindings; depth = uu___162_15326.depth; tcenv = uu___162_15326.tcenv; warn = uu___162_15326.warn; cache = refs; nolabels = uu___162_15326.nolabels; use_zfuel_name = uu___162_15326.use_zfuel_name; encode_non_total_function_typ = uu___162_15326.encode_non_total_function_typ; current_module_name = uu___162_15326.current_module_name})
in (FStar_ST.write last_env ((top)::(hd1)::tl1))))
end)))


let pop_env : Prims.unit  ->  Prims.unit = (fun uu____15332 -> (

let uu____15333 = (FStar_ST.read last_env)
in (match (uu____15333) with
| [] -> begin
(failwith "Popping an empty stack")
end
| (uu____15338)::tl1 -> begin
(FStar_ST.write last_env tl1)
end)))


let mark_env : Prims.unit  ->  Prims.unit = (fun uu____15346 -> (push_env ()))


let reset_mark_env : Prims.unit  ->  Prims.unit = (fun uu____15349 -> (pop_env ()))


let commit_mark_env : Prims.unit  ->  Prims.unit = (fun uu____15352 -> (

let uu____15353 = (FStar_ST.read last_env)
in (match (uu____15353) with
| (hd1)::(uu____15359)::tl1 -> begin
(FStar_ST.write last_env ((hd1)::tl1))
end
| uu____15365 -> begin
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

let uu____15410 = (FStar_Options.log_queries ())
in (match (uu____15410) with
| true -> begin
(

let uu____15412 = (

let uu____15413 = (

let uu____15414 = (

let uu____15415 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.map FStar_Syntax_Print.lid_to_string))
in (FStar_All.pipe_right uu____15415 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " uu____15414))
in FStar_SMTEncoding_Term.Caption (uu____15413))
in (uu____15412)::decls)
end
| uu____15420 -> begin
decls
end)))
in (

let env = (

let uu____15422 = (FStar_TypeChecker_Env.current_module tcenv)
in (get_env uu____15422 tcenv))
in (

let uu____15423 = (encode_sigelt env se)
in (match (uu____15423) with
| (decls, env1) -> begin
((set_env env1);
(

let uu____15429 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 uu____15429));
)
end)))))


let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____15438 -> begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in ((

let uu____15440 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____15440) with
| true -> begin
(

let uu____15441 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) Prims.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name uu____15441))
end
| uu____15444 -> begin
()
end));
(

let env = (get_env modul.FStar_Syntax_Syntax.name tcenv)
in (

let uu____15446 = (encode_signature (

let uu___163_15450 = env
in {bindings = uu___163_15450.bindings; depth = uu___163_15450.depth; tcenv = uu___163_15450.tcenv; warn = false; cache = uu___163_15450.cache; nolabels = uu___163_15450.nolabels; use_zfuel_name = uu___163_15450.use_zfuel_name; encode_non_total_function_typ = uu___163_15450.encode_non_total_function_typ; current_module_name = uu___163_15450.current_module_name}) modul.FStar_Syntax_Syntax.exports)
in (match (uu____15446) with
| (decls, env1) -> begin
(

let caption = (fun decls1 -> (

let uu____15462 = (FStar_Options.log_queries ())
in (match (uu____15462) with
| true -> begin
(

let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::decls1) ((FStar_SMTEncoding_Term.Caption ((Prims.strcat "End " msg)))::[])))
end
| uu____15465 -> begin
decls1
end)))
in ((set_env (

let uu___164_15467 = env1
in {bindings = uu___164_15467.bindings; depth = uu___164_15467.depth; tcenv = uu___164_15467.tcenv; warn = true; cache = uu___164_15467.cache; nolabels = uu___164_15467.nolabels; use_zfuel_name = uu___164_15467.use_zfuel_name; encode_non_total_function_typ = uu___164_15467.encode_non_total_function_typ; current_module_name = uu___164_15467.current_module_name}));
(

let uu____15469 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____15469) with
| true -> begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end
| uu____15470 -> begin
()
end));
(

let decls1 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls1));
))
end)));
)))


let encode_query : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_ErrorReporting.label Prims.list * FStar_SMTEncoding_Term.decl * FStar_SMTEncoding_Term.decl Prims.list) = (fun use_env_msg tcenv q -> ((

let uu____15504 = (

let uu____15505 = (FStar_TypeChecker_Env.current_module tcenv)
in uu____15505.FStar_Ident.str)
in (FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name uu____15504));
(

let env = (

let uu____15507 = (FStar_TypeChecker_Env.current_module tcenv)
in (get_env uu____15507 tcenv))
in (

let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (

let uu____15514 = (

let rec aux = (fun bindings1 -> (match (bindings1) with
| (FStar_TypeChecker_Env.Binding_var (x))::rest -> begin
(

let uu____15535 = (aux rest)
in (match (uu____15535) with
| (out, rest1) -> begin
(

let t = (

let uu____15553 = (FStar_Syntax_Util.destruct_typ_as_formula x.FStar_Syntax_Syntax.sort)
in (match (uu____15553) with
| Some (uu____15557) -> begin
(

let uu____15558 = (FStar_Syntax_Syntax.new_bv None FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.refine uu____15558 x.FStar_Syntax_Syntax.sort))
end
| uu____15559 -> begin
x.FStar_Syntax_Syntax.sort
end))
in (

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
in (

let uu____15562 = (

let uu____15564 = (FStar_Syntax_Syntax.mk_binder (

let uu___165_15565 = x
in {FStar_Syntax_Syntax.ppname = uu___165_15565.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___165_15565.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in (uu____15564)::out)
in ((uu____15562), (rest1)))))
end))
end
| uu____15568 -> begin
(([]), (bindings1))
end))
in (

let uu____15572 = (aux bindings)
in (match (uu____15572) with
| (closing, bindings1) -> begin
(

let uu____15586 = (FStar_Syntax_Util.close_forall_no_univs (FStar_List.rev closing) q)
in ((uu____15586), (bindings1)))
end)))
in (match (uu____15514) with
| (q1, bindings1) -> begin
(

let uu____15599 = (

let uu____15602 = (FStar_List.filter (fun uu___134_15604 -> (match (uu___134_15604) with
| FStar_TypeChecker_Env.Binding_sig (uu____15605) -> begin
false
end
| uu____15609 -> begin
true
end)) bindings1)
in (encode_env_bindings env uu____15602))
in (match (uu____15599) with
| (env_decls, env1) -> begin
((

let uu____15620 = (((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTQuery"))))
in (match (uu____15620) with
| true -> begin
(

let uu____15621 = (FStar_Syntax_Print.term_to_string q1)
in (FStar_Util.print1 "Encoding query formula: %s\n" uu____15621))
end
| uu____15622 -> begin
()
end));
(

let uu____15623 = (encode_formula q1 env1)
in (match (uu____15623) with
| (phi, qdecls) -> begin
(

let uu____15635 = (

let uu____15638 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg uu____15638 phi))
in (match (uu____15635) with
| (labels, phi1) -> begin
(

let uu____15648 = (encode_labels labels)
in (match (uu____15648) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append env_decls (FStar_List.append label_prefix qdecls))
in (

let qry = (

let uu____15669 = (

let uu____15673 = (FStar_SMTEncoding_Util.mkNot phi1)
in (

let uu____15674 = (varops.mk_unique "@query")
in ((uu____15673), (Some ("query")), (uu____15674))))
in FStar_SMTEncoding_Term.Assume (uu____15669))
in (

let suffix = (

let uu____15678 = (

let uu____15680 = (

let uu____15682 = (FStar_Options.print_z3_statistics ())
in (match (uu____15682) with
| true -> begin
(FStar_SMTEncoding_Term.PrintStats)::[]
end
| uu____15684 -> begin
[]
end))
in (FStar_List.append uu____15680 ((FStar_SMTEncoding_Term.Echo ("Done!"))::[])))
in (FStar_List.append label_suffix uu____15678))
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

let uu____15694 = (FStar_TypeChecker_Env.current_module tcenv)
in (get_env uu____15694 tcenv))
in ((FStar_SMTEncoding_Z3.push "query");
(

let uu____15696 = (encode_formula q env)
in (match (uu____15696) with
| (f, uu____15700) -> begin
((FStar_SMTEncoding_Z3.pop "query");
(match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____15702) -> begin
true
end
| uu____15705 -> begin
false
end);
)
end));
)))




