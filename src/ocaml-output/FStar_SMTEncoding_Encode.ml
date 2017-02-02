
open Prims

let add_fuel = (fun x tl -> (

let uu____16 = (FStar_Options.unthrottle_inductives ())
in (match (uu____16) with
| true -> begin
tl
end
| uu____18 -> begin
(x)::tl
end)))


let withenv = (fun c uu____39 -> (match (uu____39) with
| (a, b) -> begin
((a), (b), (c))
end))


let vargs = (fun args -> (FStar_List.filter (fun uu___109_74 -> (match (uu___109_74) with
| (FStar_Util.Inl (uu____79), uu____80) -> begin
false
end
| uu____83 -> begin
true
end)) args))


let subst_lcomp_opt = (fun s l -> (match (l) with
| Some (FStar_Util.Inl (l)) -> begin
(

let uu____114 = (

let uu____117 = (

let uu____118 = (

let uu____121 = (l.FStar_Syntax_Syntax.comp ())
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

let a = (

let uu___134_140 = a
in (

let uu____141 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = uu____141; FStar_Syntax_Syntax.index = uu___134_140.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___134_140.FStar_Syntax_Syntax.sort}))
in (

let uu____142 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str a.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (FStar_All.pipe_left escape uu____142))))


let primitive_projector_by_pos : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (

let fail = (fun uu____155 -> (

let uu____156 = (

let uu____157 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" uu____157 lid.FStar_Ident.str))
in (failwith uu____156)))
in (

let uu____158 = (FStar_TypeChecker_Env.lookup_datacon env lid)
in (match (uu____158) with
| (uu____161, t) -> begin
(

let uu____163 = (

let uu____164 = (FStar_Syntax_Subst.compress t)
in uu____164.FStar_Syntax_Syntax.n)
in (match (uu____163) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____179 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____179) with
| (binders, uu____183) -> begin
(match (((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders)))) with
| true -> begin
(fail ())
end
| uu____188 -> begin
(

let b = (FStar_List.nth binders i)
in (mk_term_projector_name lid (Prims.fst b)))
end)
end))
end
| uu____194 -> begin
(fail ())
end))
end))))


let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (

let uu____201 = (

let uu____202 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str uu____202))
in (FStar_All.pipe_left escape uu____201)))


let mk_term_projector : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun lid a -> (

let uu____209 = (

let uu____212 = (mk_term_projector_name lid a)
in ((uu____212), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Util.mkFreeV uu____209)))


let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_SMTEncoding_Term.term = (fun lid i -> (

let uu____219 = (

let uu____222 = (mk_term_projector_name_by_pos lid i)
in ((uu____222), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Util.mkFreeV uu____219)))


let mk_data_tester = (fun env l x -> (FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x))

type varops_t =
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; mark : Prims.unit  ->  Prims.unit; reset_mark : Prims.unit  ->  Prims.unit; commit_mark : Prims.unit  ->  Prims.unit; new_var : FStar_Ident.ident  ->  Prims.int  ->  Prims.string; new_fvar : FStar_Ident.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_SMTEncoding_Term.term; next_id : Prims.unit  ->  Prims.int; mk_unique : Prims.string  ->  Prims.string}


let varops : varops_t = (

let initial_ctr = (Prims.parse_int "100")
in (

let ctr = (FStar_Util.mk_ref initial_ctr)
in (

let new_scope = (fun uu____412 -> (

let uu____413 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (

let uu____415 = (FStar_Util.smap_create (Prims.parse_int "100"))
in ((uu____413), (uu____415)))))
in (

let scopes = (

let uu____426 = (

let uu____432 = (new_scope ())
in (uu____432)::[])
in (FStar_Util.mk_ref uu____426))
in (

let mk_unique = (fun y -> (

let y = (escape y)
in (

let y = (

let uu____457 = (

let uu____459 = (FStar_ST.read scopes)
in (FStar_Util.find_map uu____459 (fun uu____476 -> (match (uu____476) with
| (names, uu____483) -> begin
(FStar_Util.smap_try_find names y)
end))))
in (match (uu____457) with
| None -> begin
y
end
| Some (uu____488) -> begin
((FStar_Util.incr ctr);
(

let uu____493 = (

let uu____494 = (

let uu____495 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int uu____495))
in (Prims.strcat "__" uu____494))
in (Prims.strcat y uu____493));
)
end))
in (

let top_scope = (

let uu____500 = (

let uu____505 = (FStar_ST.read scopes)
in (FStar_List.hd uu____505))
in (FStar_All.pipe_left Prims.fst uu____500))
in ((FStar_Util.smap_add top_scope y true);
y;
)))))
in (

let new_var = (fun pp rn -> (

let uu____537 = (

let uu____538 = (

let uu____539 = (FStar_Util.string_of_int rn)
in (Prims.strcat "__" uu____539))
in (Prims.strcat pp.FStar_Ident.idText uu____538))
in (FStar_All.pipe_left mk_unique uu____537)))
in (

let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (

let next_id = (fun uu____547 -> ((FStar_Util.incr ctr);
(FStar_ST.read ctr);
))
in (

let fresh = (fun pfx -> (

let uu____558 = (

let uu____559 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int uu____559))
in (FStar_Util.format2 "%s_%s" pfx uu____558)))
in (

let string_const = (fun s -> (

let uu____564 = (

let uu____566 = (FStar_ST.read scopes)
in (FStar_Util.find_map uu____566 (fun uu____583 -> (match (uu____583) with
| (uu____589, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))
in (match (uu____564) with
| Some (f) -> begin
f
end
| None -> begin
(

let id = (next_id ())
in (

let f = (

let uu____598 = (FStar_SMTEncoding_Util.mk_String_const id)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____598))
in (

let top_scope = (

let uu____601 = (

let uu____606 = (FStar_ST.read scopes)
in (FStar_List.hd uu____606))
in (FStar_All.pipe_left Prims.snd uu____601))
in ((FStar_Util.smap_add top_scope s f);
f;
))))
end)))
in (

let push = (fun uu____634 -> (

let uu____635 = (

let uu____641 = (new_scope ())
in (

let uu____646 = (FStar_ST.read scopes)
in (uu____641)::uu____646))
in (FStar_ST.write scopes uu____635)))
in (

let pop = (fun uu____673 -> (

let uu____674 = (

let uu____680 = (FStar_ST.read scopes)
in (FStar_List.tl uu____680))
in (FStar_ST.write scopes uu____674)))
in (

let mark = (fun uu____707 -> (push ()))
in (

let reset_mark = (fun uu____711 -> (pop ()))
in (

let commit_mark = (fun uu____715 -> (

let uu____716 = (FStar_ST.read scopes)
in (match (uu____716) with
| ((hd1, hd2))::((next1, next2))::tl -> begin
((FStar_Util.smap_fold hd1 (fun key value v -> (FStar_Util.smap_add next1 key value)) ());
(FStar_Util.smap_fold hd2 (fun key value v -> (FStar_Util.smap_add next2 key value)) ());
(FStar_ST.write scopes ((((next1), (next2)))::tl));
)
end
| uu____776 -> begin
(failwith "Impossible")
end)))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id; mk_unique = mk_unique})))))))))))))))


let unmangle : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv = (fun x -> (

let uu___135_785 = x
in (

let uu____786 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = uu____786; FStar_Syntax_Syntax.index = uu___135_785.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___135_785.FStar_Syntax_Syntax.sort})))

type binding =
| Binding_var of (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term)
| Binding_fvar of (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option)


let uu___is_Binding_var : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Binding_var (_0) -> begin
true
end
| uu____807 -> begin
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
| uu____831 -> begin
false
end))


let __proj__Binding_fvar__item___0 : binding  ->  (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun projectee -> (match (projectee) with
| Binding_fvar (_0) -> begin
_0
end))


let binder_of_eithervar = (fun v -> ((v), (None)))

type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_TypeChecker_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_SMTEncoding_Term.sort Prims.list * FStar_SMTEncoding_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}


let print_env : env_t  ->  Prims.string = (fun e -> (

let uu____950 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun uu___110_954 -> (match (uu___110_954) with
| Binding_var (x, uu____956) -> begin
(FStar_Syntax_Print.bv_to_string x)
end
| Binding_fvar (l, uu____958, uu____959, uu____960) -> begin
(FStar_Syntax_Print.lid_to_string l)
end))))
in (FStar_All.pipe_right uu____950 (FStar_String.concat ", "))))


let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))


let caption_t : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.string Prims.option = (fun env t -> (

let uu____993 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____993) with
| true -> begin
(

let uu____995 = (FStar_Syntax_Print.term_to_string t)
in Some (uu____995))
end
| uu____996 -> begin
None
end)))


let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (

let xsym = (varops.fresh x)
in (

let uu____1006 = (FStar_SMTEncoding_Util.mkFreeV ((xsym), (s)))
in ((xsym), (uu____1006)))))


let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (

let uu____1017 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" uu____1017))
in (

let y = (FStar_SMTEncoding_Util.mkFreeV ((ysym), (FStar_SMTEncoding_Term.Term_sort)))
in ((ysym), (y), ((

let uu___136_1019 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = (env.depth + (Prims.parse_int "1")); tcenv = uu___136_1019.tcenv; warn = uu___136_1019.warn; cache = uu___136_1019.cache; nolabels = uu___136_1019.nolabels; use_zfuel_name = uu___136_1019.use_zfuel_name; encode_non_total_function_typ = uu___136_1019.encode_non_total_function_typ}))))))


let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let uu___137_1032 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = uu___137_1032.depth; tcenv = uu___137_1032.tcenv; warn = uu___137_1032.warn; cache = uu___137_1032.cache; nolabels = uu___137_1032.nolabels; use_zfuel_name = uu___137_1032.use_zfuel_name; encode_non_total_function_typ = uu___137_1032.encode_non_total_function_typ}))))))


let new_term_constant_from_string : env_t  ->  FStar_Syntax_Syntax.bv  ->  Prims.string  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x str -> (

let ysym = (varops.mk_unique str)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let uu___138_1048 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = uu___138_1048.depth; tcenv = uu___138_1048.tcenv; warn = uu___138_1048.warn; cache = uu___138_1048.cache; nolabels = uu___138_1048.nolabels; use_zfuel_name = uu___138_1048.use_zfuel_name; encode_non_total_function_typ = uu___138_1048.encode_non_total_function_typ}))))))


let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (

let uu___139_1058 = env
in {bindings = (Binding_var (((x), (t))))::env.bindings; depth = uu___139_1058.depth; tcenv = uu___139_1058.tcenv; warn = uu___139_1058.warn; cache = uu___139_1058.cache; nolabels = uu___139_1058.nolabels; use_zfuel_name = uu___139_1058.use_zfuel_name; encode_non_total_function_typ = uu___139_1058.encode_non_total_function_typ}))


let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let aux = (fun a' -> (lookup_binding env (fun uu___111_1074 -> (match (uu___111_1074) with
| Binding_var (b, t) when (FStar_Syntax_Syntax.bv_eq b a') -> begin
Some (((b), (t)))
end
| uu____1082 -> begin
None
end))))
in (

let uu____1085 = (aux a)
in (match (uu____1085) with
| None -> begin
(

let a = (unmangle a)
in (

let uu____1092 = (aux a)
in (match (uu____1092) with
| None -> begin
(

let uu____1098 = (

let uu____1099 = (FStar_Syntax_Print.bv_to_string a)
in (FStar_Util.format1 "Bound term variable not found (after unmangling): %s" uu____1099))
in (failwith uu____1098))
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

let uu____1119 = (

let uu___140_1120 = env
in (

let uu____1121 = (

let uu____1123 = (

let uu____1124 = (

let uu____1131 = (

let uu____1133 = (FStar_SMTEncoding_Util.mkApp ((ftok), ([])))
in (FStar_All.pipe_left (fun _0_29 -> Some (_0_29)) uu____1133))
in ((x), (fname), (uu____1131), (None)))
in Binding_fvar (uu____1124))
in (uu____1123)::env.bindings)
in {bindings = uu____1121; depth = uu___140_1120.depth; tcenv = uu___140_1120.tcenv; warn = uu___140_1120.warn; cache = uu___140_1120.cache; nolabels = uu___140_1120.nolabels; use_zfuel_name = uu___140_1120.use_zfuel_name; encode_non_total_function_typ = uu___140_1120.encode_non_total_function_typ}))
in ((fname), (ftok), (uu____1119))))))


let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun uu___112_1155 -> (match (uu___112_1155) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some (((t1), (t2), (t3)))
end
| uu____1177 -> begin
None
end))))


let contains_name : env_t  ->  Prims.string  ->  Prims.bool = (fun env s -> (

let uu____1189 = (lookup_binding env (fun uu___113_1191 -> (match (uu___113_1191) with
| Binding_fvar (b, t1, t2, t3) when (b.FStar_Ident.str = s) -> begin
Some (())
end
| uu____1201 -> begin
None
end)))
in (FStar_All.pipe_right uu____1189 FStar_Option.isSome)))


let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun env a -> (

let uu____1214 = (try_lookup_lid env a)
in (match (uu____1214) with
| None -> begin
(

let uu____1231 = (

let uu____1232 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" uu____1232))
in (failwith uu____1231))
end
| Some (s) -> begin
s
end)))


let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (

let uu___141_1263 = env
in {bindings = (Binding_fvar (((x), (fname), (ftok), (None))))::env.bindings; depth = uu___141_1263.depth; tcenv = uu___141_1263.tcenv; warn = uu___141_1263.warn; cache = uu___141_1263.cache; nolabels = uu___141_1263.nolabels; use_zfuel_name = uu___141_1263.use_zfuel_name; encode_non_total_function_typ = uu___141_1263.encode_non_total_function_typ}))


let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (

let uu____1275 = (lookup_lid env x)
in (match (uu____1275) with
| (t1, t2, uu____1283) -> begin
(

let t3 = (

let uu____1289 = (

let uu____1293 = (

let uu____1295 = (FStar_SMTEncoding_Util.mkApp (("ZFuel"), ([])))
in (uu____1295)::[])
in ((f), (uu____1293)))
in (FStar_SMTEncoding_Util.mkApp uu____1289))
in (

let uu___142_1298 = env
in {bindings = (Binding_fvar (((x), (t1), (t2), (Some (t3)))))::env.bindings; depth = uu___142_1298.depth; tcenv = uu___142_1298.tcenv; warn = uu___142_1298.warn; cache = uu___142_1298.cache; nolabels = uu___142_1298.nolabels; use_zfuel_name = uu___142_1298.use_zfuel_name; encode_non_total_function_typ = uu___142_1298.encode_non_total_function_typ}))
end)))


let try_lookup_free_var : env_t  ->  FStar_Ident.lident  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env l -> (

let uu____1308 = (try_lookup_lid env l)
in (match (uu____1308) with
| None -> begin
None
end
| Some (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some (f) when env.use_zfuel_name -> begin
Some (f)
end
| uu____1335 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (uu____1340, (fuel)::[]) -> begin
(

let uu____1343 = (

let uu____1344 = (

let uu____1345 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right uu____1345 Prims.fst))
in (FStar_Util.starts_with uu____1344 "fuel"))
in (match (uu____1343) with
| true -> begin
(

let uu____1347 = (

let uu____1348 = (FStar_SMTEncoding_Util.mkFreeV ((name), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_ApplyTF uu____1348 fuel))
in (FStar_All.pipe_left (fun _0_30 -> Some (_0_30)) uu____1347))
end
| uu____1350 -> begin
Some (t)
end))
end
| uu____1351 -> begin
Some (t)
end)
end
| uu____1352 -> begin
None
end)
end)
end)))


let lookup_free_var = (fun env a -> (

let uu____1370 = (try_lookup_free_var env a.FStar_Syntax_Syntax.v)
in (match (uu____1370) with
| Some (t) -> begin
t
end
| None -> begin
(

let uu____1373 = (

let uu____1374 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" uu____1374))
in (failwith uu____1373))
end)))


let lookup_free_var_name = (fun env a -> (

let uu____1391 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (uu____1391) with
| (x, uu____1398, uu____1399) -> begin
x
end)))


let lookup_free_var_sym = (fun env a -> (

let uu____1423 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (uu____1423) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.freevars = uu____1444; FStar_SMTEncoding_Term.rng = uu____1445}) when env.use_zfuel_name -> begin
((g), (zf))
end
| uu____1453 -> begin
(match (sym) with
| None -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end
| Some (sym) -> begin
(match (sym.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, (fuel)::[]) -> begin
((g), ((fuel)::[]))
end
| uu____1467 -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end)
end)
end)
end)))


let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun uu___114_1476 -> (match (uu___114_1476) with
| Binding_fvar (uu____1478, nm', tok, uu____1481) when (nm = nm') -> begin
tok
end
| uu____1486 -> begin
None
end))))


let mkForall_fuel' = (fun n uu____1503 -> (match (uu____1503) with
| (pats, vars, body) -> begin
(

let fallback = (fun uu____1519 -> (FStar_SMTEncoding_Util.mkForall ((pats), (vars), (body))))
in (

let uu____1522 = (FStar_Options.unthrottle_inductives ())
in (match (uu____1522) with
| true -> begin
(fallback ())
end
| uu____1523 -> begin
(

let uu____1524 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____1524) with
| (fsym, fterm) -> begin
(

let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Util.mkApp (("HasTypeFuel"), ((fterm)::args)))
end
| uu____1543 -> begin
p
end)))))
in (

let pats = (FStar_List.map add_fuel pats)
in (

let body = (match (body.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (guard)::(body')::[]) -> begin
(

let guard = (match (guard.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, guards) -> begin
(

let uu____1557 = (add_fuel guards)
in (FStar_SMTEncoding_Util.mk_and_l uu____1557))
end
| uu____1559 -> begin
(

let uu____1560 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right uu____1560 FStar_List.hd))
end)
in (FStar_SMTEncoding_Util.mkImp ((guard), (body'))))
end
| uu____1563 -> begin
body
end)
in (

let vars = (((fsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars
in (FStar_SMTEncoding_Util.mkForall ((pats), (vars), (body)))))))
end))
end)))
end))


let mkForall_fuel : (FStar_SMTEncoding_Term.pat Prims.list Prims.list * FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (mkForall_fuel' (Prims.parse_int "1"))


let head_normal : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let t = (FStar_Syntax_Util.unmeta t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) -> begin
true
end
| (FStar_Syntax_Syntax.Tm_fvar (fv)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let uu____1607 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____1607 FStar_Option.isNone))
end
| uu____1620 -> begin
false
end)))


let head_redex : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let uu____1627 = (

let uu____1628 = (FStar_Syntax_Util.un_uinst t)
in uu____1628.FStar_Syntax_Syntax.n)
in (match (uu____1627) with
| FStar_Syntax_Syntax.Tm_abs (uu____1631, uu____1632, Some (FStar_Util.Inr (l, flags))) -> begin
(((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid)) || (FStar_List.existsb (fun uu___115_1661 -> (match (uu___115_1661) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____1662 -> begin
false
end)) flags))
end
| FStar_Syntax_Syntax.Tm_abs (uu____1663, uu____1664, Some (FStar_Util.Inl (lc))) -> begin
(FStar_Syntax_Util.is_tot_or_gtot_lcomp lc)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____1691 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____1691 FStar_Option.isSome))
end
| uu____1704 -> begin
false
end)))


let whnf : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____1711 = (head_normal env t)
in (match (uu____1711) with
| true -> begin
t
end
| uu____1712 -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
end)))


let norm : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t))


let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____1722 = (

let uu____1726 = (FStar_Syntax_Syntax.null_binder t)
in (uu____1726)::[])
in (

let uu____1727 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Util.abs uu____1722 uu____1727 None))))


let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(

let uu____1754 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out uu____1754))
end
| s -> begin
(

let uu____1757 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Util.mk_ApplyTT out uu____1757))
end)) e)))


let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)))


let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun uu___116_1769 -> (match (uu___116_1769) with
| (FStar_SMTEncoding_Term.Var ("ApplyTT")) | (FStar_SMTEncoding_Term.Var ("ApplyTF")) -> begin
true
end
| uu____1770 -> begin
false
end))


let is_eta : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env vars t -> (

let rec aux = (fun t xs -> (match (((t.FStar_SMTEncoding_Term.tm), (xs))) with
| (FStar_SMTEncoding_Term.App (app, (f)::({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.freevars = uu____1798; FStar_SMTEncoding_Term.rng = uu____1799})::[]), (x)::xs) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), uu____1813) -> begin
(

let uu____1818 = (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v)
end
| uu____1828 -> begin
false
end)) args vars))
in (match (uu____1818) with
| true -> begin
(tok_of_name env f)
end
| uu____1830 -> begin
None
end))
end
| (uu____1831, []) -> begin
(

let fvs = (FStar_SMTEncoding_Term.free_variables t)
in (

let uu____1834 = (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (

let uu____1836 = (FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)
in (not (uu____1836))))))
in (match (uu____1834) with
| true -> begin
Some (t)
end
| uu____1838 -> begin
None
end)))
end
| uu____1839 -> begin
None
end))
in (aux t (FStar_List.rev vars))))


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
| uu____1923 -> begin
false
end))


let encode_const : FStar_Const.sconst  ->  FStar_SMTEncoding_Term.term = (fun uu___117_1926 -> (match (uu___117_1926) with
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

let uu____1928 = (

let uu____1932 = (

let uu____1934 = (

let uu____1935 = (FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c))
in (FStar_SMTEncoding_Term.boxInt uu____1935))
in (uu____1934)::[])
in (("FStar.Char.Char"), (uu____1932)))
in (FStar_SMTEncoding_Util.mkApp uu____1928))
end
| FStar_Const.Const_int (i, None) -> begin
(

let uu____1943 = (FStar_SMTEncoding_Util.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt uu____1943))
end
| FStar_Const.Const_int (i, Some (uu____1945)) -> begin
(failwith "Machine integers should be desugared")
end
| FStar_Const.Const_string (bytes, uu____1954) -> begin
(

let uu____1957 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const uu____1957))
end
| FStar_Const.Const_range (r) -> begin
FStar_SMTEncoding_Term.mk_Range_const
end
| FStar_Const.Const_effect -> begin
FStar_SMTEncoding_Term.mk_Term_type
end
| c -> begin
(

let uu____1961 = (

let uu____1962 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" uu____1962))
in (failwith uu____1961))
end))


let as_function_typ : env_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (

let rec aux = (fun norm t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1981) -> begin
t
end
| FStar_Syntax_Syntax.Tm_refine (uu____1989) -> begin
(

let uu____1994 = (FStar_Syntax_Util.unrefine t)
in (aux true uu____1994))
end
| uu____1995 -> begin
(match (norm) with
| true -> begin
(

let uu____1996 = (whnf env t)
in (aux false uu____1996))
end
| uu____1997 -> begin
(

let uu____1998 = (

let uu____1999 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (

let uu____2000 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" uu____1999 uu____2000)))
in (failwith uu____1998))
end)
end)))
in (aux true t0)))


let curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun k -> (

let k = (FStar_Syntax_Subst.compress k)
in (match (k.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| uu____2021 -> begin
(

let uu____2022 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (uu____2022)))
end)))


let rec encode_binders : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> ((

let uu____2165 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____2165) with
| true -> begin
(

let uu____2166 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" uu____2166))
end
| uu____2167 -> begin
()
end));
(

let uu____2168 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____2204 b -> (match (uu____2204) with
| (vars, guards, env, decls, names) -> begin
(

let uu____2247 = (

let x = (unmangle (Prims.fst b))
in (

let uu____2256 = (gen_term_var env x)
in (match (uu____2256) with
| (xxsym, xx, env') -> begin
(

let uu____2270 = (

let uu____2273 = (norm env x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt uu____2273 env xx))
in (match (uu____2270) with
| (guard_x_t, decls') -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (guard_x_t), (env'), (decls'), (x))
end))
end)))
in (match (uu____2247) with
| (v, g, env, decls', n) -> begin
(((v)::vars), ((g)::guards), (env), ((FStar_List.append decls decls')), ((n)::names))
end))
end)) (([]), ([]), (env), ([]), ([]))))
in (match (uu____2168) with
| (vars, guards, env, decls, names) -> begin
(((FStar_List.rev vars)), ((FStar_List.rev guards)), (env), (decls), ((FStar_List.rev names)))
end));
))
and encode_term_pred : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let uu____2361 = (encode_term t env)
in (match (uu____2361) with
| (t, decls) -> begin
(

let uu____2368 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t)
in ((uu____2368), (decls)))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let uu____2376 = (encode_term t env)
in (match (uu____2376) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(

let uu____2385 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t)
in ((uu____2385), (decls)))
end
| Some (f) -> begin
(

let uu____2387 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t)
in ((uu____2387), (decls)))
end)
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let t0 = (FStar_Syntax_Subst.compress t)
in ((

let uu____2394 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____2394) with
| true -> begin
(

let uu____2395 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____2396 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____2397 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" uu____2395 uu____2396 uu____2397))))
end
| uu____2398 -> begin
()
end));
(match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(

let uu____2402 = (

let uu____2403 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____2404 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____2405 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____2406 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2403 uu____2404 uu____2405 uu____2406)))))
in (failwith uu____2402))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____2410 = (

let uu____2411 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" uu____2411))
in (failwith uu____2410))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, k, uu____2416) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____2436) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t = (lookup_term_var env x)
in ((t), ([])))
end
| FStar_Syntax_Syntax.Tm_fvar (v) -> begin
(

let uu____2445 = (lookup_free_var env v.FStar_Syntax_Syntax.fv_name)
in ((uu____2445), ([])))
end
| FStar_Syntax_Syntax.Tm_type (uu____2451) -> begin
((FStar_SMTEncoding_Term.mk_Term_type), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t, uu____2454) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____2460 = (encode_const c)
in ((uu____2460), ([])))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____2474 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____2474) with
| (binders, res) -> begin
(

let uu____2481 = ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res))
in (match (uu____2481) with
| true -> begin
(

let uu____2484 = (encode_binders None binders env)
in (match (uu____2484) with
| (vars, guards, env', decls, uu____2499) -> begin
(

let fsym = (

let uu____2509 = (varops.fresh "f")
in ((uu____2509), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV fsym)
in (

let app = (mk_Apply f vars)
in (

let uu____2512 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post (

let uu___143_2516 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___143_2516.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___143_2516.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___143_2516.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___143_2516.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___143_2516.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___143_2516.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___143_2516.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___143_2516.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___143_2516.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___143_2516.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___143_2516.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___143_2516.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___143_2516.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___143_2516.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___143_2516.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___143_2516.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___143_2516.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___143_2516.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___143_2516.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___143_2516.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___143_2516.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___143_2516.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___143_2516.FStar_TypeChecker_Env.qname_and_index}) res)
in (match (uu____2512) with
| (pre_opt, res_t) -> begin
(

let uu____2523 = (encode_term_pred None res_t env' app)
in (match (uu____2523) with
| (res_pred, decls') -> begin
(

let uu____2530 = (match (pre_opt) with
| None -> begin
(

let uu____2537 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____2537), ([])))
end
| Some (pre) -> begin
(

let uu____2540 = (encode_formula pre env')
in (match (uu____2540) with
| (guard, decls0) -> begin
(

let uu____2548 = (FStar_SMTEncoding_Util.mk_and_l ((guard)::guards))
in ((uu____2548), (decls0)))
end))
end)
in (match (uu____2530) with
| (guards, guard_decls) -> begin
(

let t_interp = (

let uu____2556 = (

let uu____2562 = (FStar_SMTEncoding_Util.mkImp ((guards), (res_pred)))
in ((((app)::[])::[]), (vars), (uu____2562)))
in (FStar_SMTEncoding_Util.mkForall uu____2556))
in (

let cvars = (

let uu____2572 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right uu____2572 (FStar_List.filter (fun uu____2578 -> (match (uu____2578) with
| (x, uu____2582) -> begin
(x <> (Prims.fst fsym))
end)))))
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), ((fsym)::cvars), (t_interp)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____2593 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____2593) with
| Some (t', sorts, uu____2609) -> begin
(

let uu____2619 = (

let uu____2620 = (

let uu____2624 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((t'), (uu____2624)))
in (FStar_SMTEncoding_Util.mkApp uu____2620))
in ((uu____2619), ([])))
end
| None -> begin
(

let tsym = (

let uu____2640 = (

let uu____2641 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_arrow_" uu____2641))
in (varops.mk_unique uu____2640))
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let caption = (

let uu____2648 = (FStar_Options.log_queries ())
in (match (uu____2648) with
| true -> begin
(

let uu____2650 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in Some (uu____2650))
end
| uu____2651 -> begin
None
end))
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (caption)))
in (

let t = (

let uu____2656 = (

let uu____2660 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((tsym), (uu____2660)))
in (FStar_SMTEncoding_Util.mkApp uu____2656))
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let k_assumption = (

let a_name = Some ((Prims.strcat "kinding_" tsym))
in (

let uu____2669 = (

let uu____2674 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((uu____2674), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (uu____2669)))
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t)
in (

let pre_typing = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in (

let uu____2689 = (

let uu____2694 = (

let uu____2695 = (

let uu____2701 = (

let uu____2702 = (

let uu____2705 = (

let uu____2706 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____2706))
in ((f_has_t), (uu____2705)))
in (FStar_SMTEncoding_Util.mkImp uu____2702))
in ((((f_has_t)::[])::[]), ((fsym)::cvars), (uu____2701)))
in (mkForall_fuel uu____2695))
in ((uu____2694), (Some ("pre-typing for functions")), (a_name)))
in FStar_SMTEncoding_Term.Assume (uu____2689)))
in (

let t_interp = (

let a_name = Some ((Prims.strcat "interpretation_" tsym))
in (

let uu____2721 = (

let uu____2726 = (

let uu____2727 = (

let uu____2733 = (FStar_SMTEncoding_Util.mkIff ((f_has_t_z), (t_interp)))
in ((((f_has_t_z)::[])::[]), ((fsym)::cvars), (uu____2733)))
in (FStar_SMTEncoding_Util.mkForall uu____2727))
in ((uu____2726), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (uu____2721)))
in (

let t_decls = (FStar_List.append ((tdecl)::decls) (FStar_List.append decls' (FStar_List.append guard_decls ((k_assumption)::(pre_typing)::(t_interp)::[]))))
in ((FStar_Util.smap_add env.cache tkey_hash ((tsym), (cvar_sorts), (t_decls)));
((t), (t_decls));
)))))))))))))
end))))))
end))
end))
end)))))
end))
end
| uu____2756 -> begin
(

let tsym = (varops.fresh "Non_total_Tm_arrow")
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let t = (FStar_SMTEncoding_Util.mkApp ((tsym), ([])))
in (

let t_kinding = (

let a_name = Some ((Prims.strcat "non_total_function_typing_" tsym))
in (

let uu____2766 = (

let uu____2771 = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in ((uu____2771), (Some ("Typing for non-total arrows")), (a_name)))
in FStar_SMTEncoding_Term.Assume (uu____2766)))
in (

let fsym = (("f"), (FStar_SMTEncoding_Term.Term_sort))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV fsym)
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let t_interp = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in (

let uu____2782 = (

let uu____2787 = (

let uu____2788 = (

let uu____2794 = (

let uu____2795 = (

let uu____2798 = (

let uu____2799 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____2799))
in ((f_has_t), (uu____2798)))
in (FStar_SMTEncoding_Util.mkImp uu____2795))
in ((((f_has_t)::[])::[]), ((fsym)::[]), (uu____2794)))
in (mkForall_fuel uu____2788))
in ((uu____2787), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (uu____2782)))
in ((t), ((tdecl)::(t_kinding)::(t_interp)::[]))))))))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_refine (uu____2814) -> begin
(

let uu____2819 = (

let uu____2822 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)
in (match (uu____2822) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.tk = uu____2827; FStar_Syntax_Syntax.pos = uu____2828; FStar_Syntax_Syntax.vars = uu____2829} -> begin
(

let uu____2836 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) f)
in (match (uu____2836) with
| (b, f) -> begin
(

let uu____2850 = (

let uu____2851 = (FStar_List.hd b)
in (Prims.fst uu____2851))
in ((uu____2850), (f)))
end))
end
| uu____2856 -> begin
(failwith "impossible")
end))
in (match (uu____2819) with
| (x, f) -> begin
(

let uu____2863 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (uu____2863) with
| (base_t, decls) -> begin
(

let uu____2870 = (gen_term_var env x)
in (match (uu____2870) with
| (x, xtm, env') -> begin
(

let uu____2879 = (encode_formula f env')
in (match (uu____2879) with
| (refinement, decls') -> begin
(

let uu____2886 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____2886) with
| (fsym, fterm) -> begin
(

let encoding = (

let uu____2894 = (

let uu____2897 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in ((uu____2897), (refinement)))
in (FStar_SMTEncoding_Util.mkAnd uu____2894))
in (

let cvars = (

let uu____2902 = (FStar_SMTEncoding_Term.free_variables encoding)
in (FStar_All.pipe_right uu____2902 (FStar_List.filter (fun uu____2908 -> (match (uu____2908) with
| (y, uu____2912) -> begin
((y <> x) && (y <> fsym))
end)))))
in (

let xfv = ((x), (FStar_SMTEncoding_Term.Term_sort))
in (

let ffv = ((fsym), (FStar_SMTEncoding_Term.Fuel_sort))
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), ((ffv)::(xfv)::cvars), (encoding)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____2931 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____2931) with
| Some (t, uu____2946, uu____2947) -> begin
(

let uu____2957 = (

let uu____2958 = (

let uu____2962 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((t), (uu____2962)))
in (FStar_SMTEncoding_Util.mkApp uu____2958))
in ((uu____2957), ([])))
end
| None -> begin
(

let tsym = (

let uu____2978 = (

let uu____2979 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_refine_" uu____2979))
in (varops.mk_unique uu____2978))
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let t = (

let uu____2988 = (

let uu____2992 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((tsym), (uu____2992)))
in (FStar_SMTEncoding_Util.mkApp uu____2988))
in (

let x_has_t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let t_haseq_base = (FStar_SMTEncoding_Term.mk_haseq base_t)
in (

let t_haseq_ref = (FStar_SMTEncoding_Term.mk_haseq t)
in (

let t_haseq = (

let uu____3002 = (

let uu____3007 = (

let uu____3008 = (

let uu____3014 = (FStar_SMTEncoding_Util.mkIff ((t_haseq_ref), (t_haseq_base)))
in ((((t_haseq_ref)::[])::[]), (cvars), (uu____3014)))
in (FStar_SMTEncoding_Util.mkForall uu____3008))
in ((uu____3007), (Some ((Prims.strcat "haseq for " tsym))), (Some ((Prims.strcat "haseq" tsym)))))
in FStar_SMTEncoding_Term.Assume (uu____3002))
in (

let t_kinding = (

let uu____3025 = (

let uu____3030 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((uu____3030), (Some ("refinement kinding")), (Some ((Prims.strcat "refinement_kinding_" tsym)))))
in FStar_SMTEncoding_Term.Assume (uu____3025))
in (

let t_interp = (

let uu____3041 = (

let uu____3046 = (

let uu____3047 = (

let uu____3053 = (FStar_SMTEncoding_Util.mkIff ((x_has_t), (encoding)))
in ((((x_has_t)::[])::[]), ((ffv)::(xfv)::cvars), (uu____3053)))
in (FStar_SMTEncoding_Util.mkForall uu____3047))
in (

let uu____3065 = (

let uu____3067 = (FStar_Syntax_Print.term_to_string t0)
in Some (uu____3067))
in ((uu____3046), (uu____3065), (Some ((Prims.strcat "refinement_interpretation_" tsym))))))
in FStar_SMTEncoding_Term.Assume (uu____3041))
in (

let t_decls = (FStar_List.append decls (FStar_List.append decls' ((tdecl)::(t_kinding)::(t_interp)::(t_haseq)::[])))
in ((FStar_Util.smap_add env.cache tkey_hash ((tsym), (cvar_sorts), (t_decls)));
((t), (t_decls));
)))))))))))))
end))))))))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
(

let ttm = (

let uu____3096 = (FStar_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Util.mk_Term_uvar uu____3096))
in (

let uu____3100 = (encode_term_pred None k env ttm)
in (match (uu____3100) with
| (t_has_k, decls) -> begin
(

let d = (

let uu____3108 = (

let uu____3113 = (

let uu____3115 = (

let uu____3116 = (

let uu____3117 = (

let uu____3118 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____3118))
in (FStar_Util.format1 "uvar_typing_%s" uu____3117))
in (varops.mk_unique uu____3116))
in Some (uu____3115))
in ((t_has_k), (Some ("Uvar typing")), (uu____3113)))
in FStar_SMTEncoding_Term.Assume (uu____3108))
in ((ttm), ((FStar_List.append decls ((d)::[])))))
end)))
end
| FStar_Syntax_Syntax.Tm_app (uu____3125) -> begin
(

let uu____3135 = (FStar_Syntax_Util.head_and_args t0)
in (match (uu____3135) with
| (head, args_e) -> begin
(

let uu____3163 = (

let uu____3171 = (

let uu____3172 = (FStar_Syntax_Subst.compress head)
in uu____3172.FStar_Syntax_Syntax.n)
in ((uu____3171), (args_e)))
in (match (uu____3163) with
| (uu____3182, uu____3183) when (head_redex env head) -> begin
(

let uu____3194 = (whnf env t)
in (encode_term uu____3194 env))
end
| ((FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), (_)::((v1, _))::((v2, _))::[])) | ((FStar_Syntax_Syntax.Tm_fvar (fv), (_)::((v1, _))::((v2, _))::[])) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
(

let uu____3268 = (encode_term v1 env)
in (match (uu____3268) with
| (v1, decls1) -> begin
(

let uu____3275 = (encode_term v2 env)
in (match (uu____3275) with
| (v2, decls2) -> begin
(

let uu____3282 = (FStar_SMTEncoding_Util.mk_LexCons v1 v2)
in ((uu____3282), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), uu____3284) -> begin
(

let e0 = (

let uu____3298 = (

let uu____3301 = (

let uu____3302 = (

let uu____3312 = (

let uu____3318 = (FStar_List.hd args_e)
in (uu____3318)::[])
in ((head), (uu____3312)))
in FStar_Syntax_Syntax.Tm_app (uu____3302))
in (FStar_Syntax_Syntax.mk uu____3301))
in (uu____3298 None head.FStar_Syntax_Syntax.pos))
in ((

let uu____3351 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____3351) with
| true -> begin
(

let uu____3352 = (FStar_Syntax_Print.term_to_string e0)
in (FStar_Util.print1 "Trying to normalize %s\n" uu____3352))
end
| uu____3353 -> begin
()
end));
(

let e0 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env.tcenv e0)
in ((

let uu____3356 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____3356) with
| true -> begin
(

let uu____3357 = (FStar_Syntax_Print.term_to_string e0)
in (FStar_Util.print1 "Result of normalization %s\n" uu____3357))
end
| uu____3358 -> begin
()
end));
(

let e0 = (

let uu____3360 = (

let uu____3361 = (

let uu____3362 = (FStar_Syntax_Subst.compress e0)
in uu____3362.FStar_Syntax_Syntax.n)
in (match (uu____3361) with
| FStar_Syntax_Syntax.Tm_app (uu____3365) -> begin
false
end
| uu____3375 -> begin
true
end))
in (match (uu____3360) with
| true -> begin
e0
end
| uu____3376 -> begin
(

let uu____3377 = (FStar_Syntax_Util.head_and_args e0)
in (match (uu____3377) with
| (head, args) -> begin
(

let uu____3403 = (

let uu____3404 = (

let uu____3405 = (FStar_Syntax_Subst.compress head)
in uu____3405.FStar_Syntax_Syntax.n)
in (match (uu____3404) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) -> begin
true
end
| uu____3408 -> begin
false
end))
in (match (uu____3403) with
| true -> begin
(match (args) with
| (x)::[] -> begin
(Prims.fst x)
end
| uu____3424 -> begin
(failwith "Impossible : Reify applied to multiple arguments after normalization.")
end)
end
| uu____3430 -> begin
e0
end))
end))
end))
in (

let e = (match (args_e) with
| (uu____3432)::[] -> begin
e0
end
| uu____3445 -> begin
(

let uu____3451 = (

let uu____3454 = (

let uu____3455 = (

let uu____3465 = (FStar_List.tl args_e)
in ((e0), (uu____3465)))
in FStar_Syntax_Syntax.Tm_app (uu____3455))
in (FStar_Syntax_Syntax.mk uu____3454))
in (uu____3451 None t0.FStar_Syntax_Syntax.pos))
end)
in (encode_term e env)));
));
))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____3488)), ((arg, uu____3490))::[]) -> begin
(encode_term arg env)
end
| uu____3508 -> begin
(

let uu____3516 = (encode_args args_e env)
in (match (uu____3516) with
| (args, decls) -> begin
(

let encode_partial_app = (fun ht_opt -> (

let uu____3549 = (encode_term head env)
in (match (uu____3549) with
| (head, decls') -> begin
(

let app_tm = (mk_Apply_args head args)
in (match (ht_opt) with
| None -> begin
((app_tm), ((FStar_List.append decls decls')))
end
| Some (formals, c) -> begin
(

let uu____3588 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (uu____3588) with
| (formals, rest) -> begin
(

let subst = (FStar_List.map2 (fun uu____3630 uu____3631 -> (match (((uu____3630), (uu____3631))) with
| ((bv, uu____3645), (a, uu____3647)) -> begin
FStar_Syntax_Syntax.NT (((bv), (a)))
end)) formals args_e)
in (

let ty = (

let uu____3661 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right uu____3661 (FStar_Syntax_Subst.subst subst)))
in (

let uu____3666 = (encode_term_pred None ty env app_tm)
in (match (uu____3666) with
| (has_type, decls'') -> begin
(

let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (

let e_typing = (

let uu____3676 = (

let uu____3681 = (FStar_SMTEncoding_Util.mkForall ((((has_type)::[])::[]), (cvars), (has_type)))
in (

let uu____3686 = (

let uu____3688 = (

let uu____3689 = (

let uu____3690 = (

let uu____3691 = (FStar_SMTEncoding_Term.hash_of_term app_tm)
in (FStar_Util.digest_of_string uu____3691))
in (Prims.strcat "partial_app_typing_" uu____3690))
in (varops.mk_unique uu____3689))
in Some (uu____3688))
in ((uu____3681), (Some ("Partial app typing")), (uu____3686))))
in FStar_SMTEncoding_Term.Assume (uu____3676))
in ((app_tm), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' ((e_typing)::[]))))))))
end))))
end))
end))
end)))
in (

let encode_full_app = (fun fv -> (

let uu____3709 = (lookup_free_var_sym env fv)
in (match (uu____3709) with
| (fname, fuel_args) -> begin
(

let tm = (FStar_SMTEncoding_Util.mkApp' ((fname), ((FStar_List.append fuel_args args))))
in ((tm), (decls)))
end)))
in (

let head = (FStar_Syntax_Subst.compress head)
in (

let head_type = (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (x); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (x)) -> begin
Some (x.FStar_Syntax_Syntax.sort)
end
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(

let uu____3747 = (

let uu____3748 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____3748 Prims.snd))
in Some (uu____3747))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____3757, FStar_Util.Inl (t), uu____3759) -> begin
Some (t)
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____3780, FStar_Util.Inr (c), uu____3782) -> begin
Some ((FStar_Syntax_Util.comp_result c))
end
| uu____3803 -> begin
None
end)
in (match (head_type) with
| None -> begin
(encode_partial_app None)
end
| Some (head_type) -> begin
(

let head_type = (

let uu____3823 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine uu____3823))
in (

let uu____3824 = (curried_arrow_formals_comp head_type)
in (match (uu____3824) with
| (formals, c) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| uu____3849 -> begin
(match (((FStar_List.length formals) > (FStar_List.length args))) with
| true -> begin
(encode_partial_app (Some (((formals), (c)))))
end
| uu____3861 -> begin
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

let uu____3894 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____3894) with
| (bs, body, opening) -> begin
(

let fallback = (fun uu____3909 -> (

let f = (varops.fresh "Tm_abs")
in (

let decl = FStar_SMTEncoding_Term.DeclFun (((f), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Imprecise function encoding"))))
in (

let uu____3914 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in ((uu____3914), ((decl)::[]))))))
in (

let is_impure = (fun uu___118_3924 -> (match (uu___118_3924) with
| FStar_Util.Inl (lc) -> begin
(

let uu____3934 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)
in (not (uu____3934)))
end
| FStar_Util.Inr (eff, uu____3936) -> begin
(

let uu____3942 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv eff)
in (FStar_All.pipe_right uu____3942 Prims.op_Negation))
end))
in (

let codomain_eff = (fun lc -> (match (lc) with
| FStar_Util.Inl (lc) -> begin
(

let uu____3963 = (

let uu____3964 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening uu____3964))
in (FStar_All.pipe_right uu____3963 (fun _0_31 -> Some (_0_31))))
end
| FStar_Util.Inr (eff, flags) -> begin
(

let new_uvar = (fun uu____3976 -> (

let uu____3977 = (FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange [] FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right uu____3977 Prims.fst)))
in (match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid)) with
| true -> begin
(

let uu____3985 = (

let uu____3986 = (new_uvar ())
in (FStar_Syntax_Syntax.mk_Total uu____3986))
in (FStar_All.pipe_right uu____3985 (fun _0_32 -> Some (_0_32))))
end
| uu____3988 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid)) with
| true -> begin
(

let uu____3990 = (

let uu____3991 = (new_uvar ())
in (FStar_Syntax_Syntax.mk_GTotal uu____3991))
in (FStar_All.pipe_right uu____3990 (fun _0_33 -> Some (_0_33))))
end
| uu____3993 -> begin
None
end)
end))
end))
in (match (lopt) with
| None -> begin
((

let uu____4002 = (

let uu____4003 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)" uu____4003))
in (FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____4002));
(fallback ());
)
end
| Some (lc) -> begin
(

let uu____4015 = (is_impure lc)
in (match (uu____4015) with
| true -> begin
(fallback ())
end
| uu____4018 -> begin
(

let uu____4019 = (encode_binders None bs env)
in (match (uu____4019) with
| (vars, guards, envbody, decls, uu____4034) -> begin
(

let uu____4041 = (encode_term body envbody)
in (match (uu____4041) with
| (body, decls') -> begin
(

let key_body = (

let uu____4049 = (

let uu____4055 = (

let uu____4056 = (

let uu____4059 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____4059), (body)))
in (FStar_SMTEncoding_Util.mkImp uu____4056))
in (([]), (vars), (uu____4055)))
in (FStar_SMTEncoding_Util.mkForall uu____4049))
in (

let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), (cvars), (key_body)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____4070 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____4070) with
| Some (t, uu____4085, uu____4086) -> begin
(

let uu____4096 = (

let uu____4097 = (

let uu____4101 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((t), (uu____4101)))
in (FStar_SMTEncoding_Util.mkApp uu____4097))
in ((uu____4096), ([])))
end
| None -> begin
(

let uu____4112 = (is_eta env vars body)
in (match (uu____4112) with
| Some (t) -> begin
((t), ([]))
end
| None -> begin
(

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let fsym = (

let uu____4123 = (

let uu____4124 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_abs_" uu____4124))
in (varops.mk_unique uu____4123))
in (

let fdecl = FStar_SMTEncoding_Term.DeclFun (((fsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let f = (

let uu____4129 = (

let uu____4133 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((fsym), (uu____4133)))
in (FStar_SMTEncoding_Util.mkApp uu____4129))
in (

let app = (mk_Apply f vars)
in (

let typing_f = (

let uu____4141 = (codomain_eff lc)
in (match (uu____4141) with
| None -> begin
[]
end
| Some (c) -> begin
(

let tfun = (FStar_Syntax_Util.arrow bs c)
in (

let uu____4148 = (encode_term_pred None tfun env f)
in (match (uu____4148) with
| (f_has_t, decls'') -> begin
(

let a_name = Some ((Prims.strcat "typing_" fsym))
in (

let uu____4156 = (

let uu____4158 = (

let uu____4159 = (

let uu____4164 = (FStar_SMTEncoding_Util.mkForall ((((f)::[])::[]), (cvars), (f_has_t)))
in ((uu____4164), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (uu____4159))
in (uu____4158)::[])
in (FStar_List.append decls'' uu____4156)))
end)))
end))
in (

let interp_f = (

let a_name = Some ((Prims.strcat "interpretation_" fsym))
in (

let uu____4174 = (

let uu____4179 = (

let uu____4180 = (

let uu____4186 = (FStar_SMTEncoding_Util.mkEq ((app), (body)))
in ((((app)::[])::[]), ((FStar_List.append vars cvars)), (uu____4186)))
in (FStar_SMTEncoding_Util.mkForall uu____4180))
in ((uu____4179), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (uu____4174)))
in (

let f_decls = (FStar_List.append decls (FStar_List.append decls' (FStar_List.append ((fdecl)::typing_f) ((interp_f)::[]))))
in ((FStar_Util.smap_add env.cache tkey_hash ((fsym), (cvar_sorts), (f_decls)));
((f), (f_decls));
)))))))))
end))
end))))))
end))
end))
end))
end))))
end))
end
| FStar_Syntax_Syntax.Tm_let ((uu____4205, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____4206); FStar_Syntax_Syntax.lbunivs = uu____4207; FStar_Syntax_Syntax.lbtyp = uu____4208; FStar_Syntax_Syntax.lbeff = uu____4209; FStar_Syntax_Syntax.lbdef = uu____4210})::uu____4211), uu____4212) -> begin
(failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____4230; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____4232; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (uu____4248) -> begin
((FStar_Errors.diag t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts");
(

let e = (varops.fresh "let-rec")
in (

let decl_e = FStar_SMTEncoding_Term.DeclFun (((e), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let uu____4261 = (FStar_SMTEncoding_Util.mkFreeV ((e), (FStar_SMTEncoding_Term.Term_sort)))
in ((uu____4261), ((decl_e)::[])))));
)
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end);
)))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (

let uu____4303 = (encode_term e1 env)
in (match (uu____4303) with
| (ee1, decls1) -> begin
(

let uu____4310 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) e2)
in (match (uu____4310) with
| (xs, e2) -> begin
(

let uu____4324 = (FStar_List.hd xs)
in (match (uu____4324) with
| (x, uu____4332) -> begin
(

let env' = (push_term_var env x ee1)
in (

let uu____4334 = (encode_body e2 env')
in (match (uu____4334) with
| (ee2, decls2) -> begin
((ee2), ((FStar_List.append decls1 decls2)))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (

let uu____4356 = (encode_term e env)
in (match (uu____4356) with
| (scr, decls) -> begin
(

let uu____4363 = (FStar_List.fold_right (fun b uu____4371 -> (match (uu____4371) with
| (else_case, decls) -> begin
(

let uu____4382 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____4382) with
| (p, w, br) -> begin
(

let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun uu____4412 uu____4413 -> (match (((uu____4412), (uu____4413))) with
| ((env0, pattern), (else_case, decls)) -> begin
(

let guard = (pattern.guard scr)
in (

let projections = (pattern.projections scr)
in (

let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env uu____4450 -> (match (uu____4450) with
| (x, t) -> begin
(push_term_var env x t)
end)) env))
in (

let uu____4455 = (match (w) with
| None -> begin
((guard), ([]))
end
| Some (w) -> begin
(

let uu____4470 = (encode_term w env)
in (match (uu____4470) with
| (w, decls2) -> begin
(

let uu____4478 = (

let uu____4479 = (

let uu____4482 = (

let uu____4483 = (

let uu____4486 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue)
in ((w), (uu____4486)))
in (FStar_SMTEncoding_Util.mkEq uu____4483))
in ((guard), (uu____4482)))
in (FStar_SMTEncoding_Util.mkAnd uu____4479))
in ((uu____4478), (decls2)))
end))
end)
in (match (uu____4455) with
| (guard, decls2) -> begin
(

let uu____4494 = (encode_br br env)
in (match (uu____4494) with
| (br, decls3) -> begin
(

let uu____4502 = (FStar_SMTEncoding_Util.mkITE ((guard), (br), (else_case)))
in ((uu____4502), ((FStar_List.append decls (FStar_List.append decls2 decls3)))))
end))
end)))))
end)) patterns ((else_case), (decls))))
end))
end)) pats ((default_case), (decls)))
in (match (uu____4363) with
| (match_tm, decls) -> begin
((match_tm), (decls))
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| uu____4526 -> begin
(

let uu____4527 = (encode_one_pat env pat)
in (uu____4527)::[])
end))
and encode_one_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> ((

let uu____4539 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____4539) with
| true -> begin
(

let uu____4540 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" uu____4540))
end
| uu____4541 -> begin
()
end));
(

let uu____4542 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (uu____4542) with
| (vars, pat_term) -> begin
(

let uu____4552 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun uu____4575 v -> (match (uu____4575) with
| (env, vars) -> begin
(

let uu____4603 = (gen_term_var env v)
in (match (uu____4603) with
| (xx, uu____4615, env) -> begin
((env), ((((v), (((xx), (FStar_SMTEncoding_Term.Term_sort)))))::vars))
end))
end)) ((env), ([]))))
in (match (uu____4552) with
| (env, vars) -> begin
(

let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (uu____4662) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_dot_term (_)) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____4670 = (

let uu____4673 = (encode_const c)
in ((scrutinee), (uu____4673)))
in (FStar_SMTEncoding_Util.mkEq uu____4670))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let is_f = (mk_data_tester env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____4704 -> (match (uu____4704) with
| (arg, uu____4710) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____4720 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_guard arg uu____4720)))
end))))
in (FStar_SMTEncoding_Util.mk_and_l ((is_f)::sub_term_guards))))
end))
in (

let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (uu____4739) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _)) | (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_constant (uu____4754) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let uu____4769 = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____4791 -> (match (uu____4791) with
| (arg, uu____4800) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____4810 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_projections arg uu____4810)))
end))))
in (FStar_All.pipe_right uu____4769 FStar_List.flatten))
end))
in (

let pat_term = (fun uu____4826 -> (encode_term pat_term env))
in (

let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in ((env), (pattern))))))
end))
end));
))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (

let uu____4833 = (FStar_All.pipe_right l (FStar_List.fold_left (fun uu____4848 uu____4849 -> (match (((uu____4848), (uu____4849))) with
| ((tms, decls), (t, uu____4869)) -> begin
(

let uu____4880 = (encode_term t env)
in (match (uu____4880) with
| (t, decls') -> begin
(((t)::tms), ((FStar_List.append decls decls')))
end))
end)) (([]), ([]))))
in (match (uu____4833) with
| (l, decls) -> begin
(((FStar_List.rev l)), (decls))
end)))
and encode_function_type_as_formula : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun induction_on new_pats t env -> (

let list_elements = (fun e -> (

let uu____4918 = (FStar_Syntax_Util.list_elements e)
in (match (uu____4918) with
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

let uu____4936 = (

let uu____4946 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right uu____4946 FStar_Syntax_Util.head_and_args))
in (match (uu____4936) with
| (head, args) -> begin
(

let uu____4977 = (

let uu____4985 = (

let uu____4986 = (FStar_Syntax_Util.un_uinst head)
in uu____4986.FStar_Syntax_Syntax.n)
in ((uu____4985), (args)))
in (match (uu____4977) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((uu____5000, uu____5001))::((e, uu____5003))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpat_lid) -> begin
((e), (None))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, uu____5034))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatT_lid) -> begin
((e), (None))
end
| uu____5055 -> begin
(failwith "Unexpected pattern term")
end))
end)))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements p)
in (

let smt_pat_or = (fun t -> (

let uu____5088 = (

let uu____5098 = (FStar_Syntax_Util.unmeta t)
in (FStar_All.pipe_right uu____5098 FStar_Syntax_Util.head_and_args))
in (match (uu____5088) with
| (head, args) -> begin
(

let uu____5127 = (

let uu____5135 = (

let uu____5136 = (FStar_Syntax_Util.un_uinst head)
in uu____5136.FStar_Syntax_Syntax.n)
in ((uu____5135), (args)))
in (match (uu____5127) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, uu____5149))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatOr_lid) -> begin
Some (e)
end
| uu____5169 -> begin
None
end))
end)))
in (match (elts) with
| (t)::[] -> begin
(

let uu____5187 = (smt_pat_or t)
in (match (uu____5187) with
| Some (e) -> begin
(

let uu____5203 = (list_elements e)
in (FStar_All.pipe_right uu____5203 (FStar_List.map (fun branch -> (

let uu____5220 = (list_elements branch)
in (FStar_All.pipe_right uu____5220 (FStar_List.map one_pat)))))))
end
| uu____5234 -> begin
(

let uu____5238 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____5238)::[])
end))
end
| uu____5269 -> begin
(

let uu____5271 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____5271)::[])
end))))
in (

let uu____5302 = (

let uu____5318 = (

let uu____5319 = (FStar_Syntax_Subst.compress t)
in uu____5319.FStar_Syntax_Syntax.n)
in (match (uu____5318) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____5349 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____5349) with
| (binders, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____5384; FStar_Syntax_Syntax.effect_name = uu____5385; FStar_Syntax_Syntax.result_typ = uu____5386; FStar_Syntax_Syntax.effect_args = ((pre, uu____5388))::((post, uu____5390))::((pats, uu____5392))::[]; FStar_Syntax_Syntax.flags = uu____5393}) -> begin
(

let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (

let uu____5427 = (lemma_pats pats')
in ((binders), (pre), (post), (uu____5427))))
end
| uu____5446 -> begin
(failwith "impos")
end)
end))
end
| uu____5462 -> begin
(failwith "Impos")
end))
in (match (uu____5302) with
| (binders, pre, post, patterns) -> begin
(

let uu____5506 = (encode_binders None binders env)
in (match (uu____5506) with
| (vars, guards, env, decls, uu____5521) -> begin
(

let uu____5528 = (

let uu____5535 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (

let uu____5566 = (

let uu____5571 = (FStar_All.pipe_right branch (FStar_List.map (fun uu____5587 -> (match (uu____5587) with
| (t, uu____5594) -> begin
(encode_term t (

let uu___144_5597 = env
in {bindings = uu___144_5597.bindings; depth = uu___144_5597.depth; tcenv = uu___144_5597.tcenv; warn = uu___144_5597.warn; cache = uu___144_5597.cache; nolabels = uu___144_5597.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___144_5597.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right uu____5571 FStar_List.unzip))
in (match (uu____5566) with
| (pats, decls) -> begin
((pats), (decls))
end)))))
in (FStar_All.pipe_right uu____5535 FStar_List.unzip))
in (match (uu____5528) with
| (pats, decls') -> begin
(

let decls' = (FStar_List.flatten decls')
in (

let pats = (match (induction_on) with
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

let uu____5661 = (

let uu____5662 = (FStar_SMTEncoding_Util.mkFreeV l)
in (FStar_SMTEncoding_Util.mk_Precedes uu____5662 e))
in (uu____5661)::p))))
end
| uu____5663 -> begin
(

let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (

let uu____5692 = (FStar_SMTEncoding_Util.mk_Precedes tl e)
in (uu____5692)::p))))
end
| ((x, FStar_SMTEncoding_Term.Term_sort))::vars -> begin
(

let uu____5700 = (

let uu____5701 = (FStar_SMTEncoding_Util.mkFreeV ((x), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Util.mk_LexCons uu____5701 tl))
in (aux uu____5700 vars))
end
| uu____5702 -> begin
pats
end))
in (

let uu____5706 = (FStar_SMTEncoding_Util.mkFreeV (("Prims.LexTop"), (FStar_SMTEncoding_Term.Term_sort)))
in (aux uu____5706 vars)))
end)
end)
in (

let env = (

let uu___145_5708 = env
in {bindings = uu___145_5708.bindings; depth = uu___145_5708.depth; tcenv = uu___145_5708.tcenv; warn = uu___145_5708.warn; cache = uu___145_5708.cache; nolabels = true; use_zfuel_name = uu___145_5708.use_zfuel_name; encode_non_total_function_typ = uu___145_5708.encode_non_total_function_typ})
in (

let uu____5709 = (

let uu____5712 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula uu____5712 env))
in (match (uu____5709) with
| (pre, decls'') -> begin
(

let uu____5717 = (

let uu____5720 = (FStar_Syntax_Util.unmeta post)
in (encode_formula uu____5720 env))
in (match (uu____5717) with
| (post, decls''') -> begin
(

let decls = (FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') (FStar_List.append decls'' decls''')))
in (

let uu____5727 = (

let uu____5728 = (

let uu____5734 = (

let uu____5735 = (

let uu____5738 = (FStar_SMTEncoding_Util.mk_and_l ((pre)::guards))
in ((uu____5738), (post)))
in (FStar_SMTEncoding_Util.mkImp uu____5735))
in ((pats), (vars), (uu____5734)))
in (FStar_SMTEncoding_Util.mkForall uu____5728))
in ((uu____5727), (decls))))
end))
end)))))
end))
end))
end))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (

let debug = (fun phi -> (

let uu____5751 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____5751) with
| true -> begin
(

let uu____5752 = (FStar_Syntax_Print.tag_of_term phi)
in (

let uu____5753 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print2 "Formula (%s)  %s\n" uu____5752 uu____5753)))
end
| uu____5754 -> begin
()
end)))
in (

let enc = (fun f r l -> (

let uu____5780 = (FStar_Util.fold_map (fun decls x -> (

let uu____5793 = (encode_term (Prims.fst x) env)
in (match (uu____5793) with
| (t, decls') -> begin
(((FStar_List.append decls decls')), (t))
end))) [] l)
in (match (uu____5780) with
| (decls, args) -> begin
(

let uu____5810 = (

let uu___146_5811 = (f args)
in {FStar_SMTEncoding_Term.tm = uu___146_5811.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___146_5811.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____5810), (decls)))
end)))
in (

let const_op = (fun f r uu____5830 -> (

let uu____5833 = (f r)
in ((uu____5833), ([]))))
in (

let un_op = (fun f l -> (

let uu____5849 = (FStar_List.hd l)
in (FStar_All.pipe_left f uu____5849)))
in (

let bin_op = (fun f uu___119_5862 -> (match (uu___119_5862) with
| (t1)::(t2)::[] -> begin
(f ((t1), (t2)))
end
| uu____5870 -> begin
(failwith "Impossible")
end))
in (

let enc_prop_c = (fun f r l -> (

let uu____5897 = (FStar_Util.fold_map (fun decls uu____5906 -> (match (uu____5906) with
| (t, uu____5914) -> begin
(

let uu____5915 = (encode_formula t env)
in (match (uu____5915) with
| (phi, decls') -> begin
(((FStar_List.append decls decls')), (phi))
end))
end)) [] l)
in (match (uu____5897) with
| (decls, phis) -> begin
(

let uu____5932 = (

let uu___147_5933 = (f phis)
in {FStar_SMTEncoding_Term.tm = uu___147_5933.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___147_5933.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____5932), (decls)))
end)))
in (

let eq_op = (fun r uu___120_5949 -> (match (uu___120_5949) with
| ((_)::(e1)::(e2)::[]) | ((_)::(_)::(e1)::(e2)::[]) -> begin
(

let uu____6009 = (enc (bin_op FStar_SMTEncoding_Util.mkEq))
in (uu____6009 r ((e1)::(e2)::[])))
end
| l -> begin
(

let uu____6029 = (enc (bin_op FStar_SMTEncoding_Util.mkEq))
in (uu____6029 r l))
end))
in (

let mk_imp = (fun r uu___121_6048 -> (match (uu___121_6048) with
| ((lhs, uu____6052))::((rhs, uu____6054))::[] -> begin
(

let uu____6075 = (encode_formula rhs env)
in (match (uu____6075) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____6084) -> begin
((l1), (decls1))
end
| uu____6087 -> begin
(

let uu____6088 = (encode_formula lhs env)
in (match (uu____6088) with
| (l2, decls2) -> begin
(

let uu____6095 = (FStar_SMTEncoding_Term.mkImp ((l2), (l1)) r)
in ((uu____6095), ((FStar_List.append decls1 decls2))))
end))
end)
end))
end
| uu____6097 -> begin
(failwith "impossible")
end))
in (

let mk_ite = (fun r uu___122_6112 -> (match (uu___122_6112) with
| ((guard, uu____6116))::((_then, uu____6118))::((_else, uu____6120))::[] -> begin
(

let uu____6149 = (encode_formula guard env)
in (match (uu____6149) with
| (g, decls1) -> begin
(

let uu____6156 = (encode_formula _then env)
in (match (uu____6156) with
| (t, decls2) -> begin
(

let uu____6163 = (encode_formula _else env)
in (match (uu____6163) with
| (e, decls3) -> begin
(

let res = (FStar_SMTEncoding_Term.mkITE ((g), (t), (e)) r)
in ((res), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end))
end))
end
| uu____6172 -> begin
(failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (

let uu____6191 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f uu____6191)))
in (

let connectives = (

let uu____6203 = (

let uu____6212 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd))
in ((FStar_Syntax_Const.and_lid), (uu____6212)))
in (

let uu____6225 = (

let uu____6235 = (

let uu____6244 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr))
in ((FStar_Syntax_Const.or_lid), (uu____6244)))
in (

let uu____6257 = (

let uu____6267 = (

let uu____6277 = (

let uu____6286 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff))
in ((FStar_Syntax_Const.iff_lid), (uu____6286)))
in (

let uu____6299 = (

let uu____6309 = (

let uu____6319 = (

let uu____6328 = (enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot))
in ((FStar_Syntax_Const.not_lid), (uu____6328)))
in (uu____6319)::(((FStar_Syntax_Const.eq2_lid), (eq_op)))::(((FStar_Syntax_Const.eq3_lid), (eq_op)))::(((FStar_Syntax_Const.true_lid), ((const_op FStar_SMTEncoding_Term.mkTrue))))::(((FStar_Syntax_Const.false_lid), ((const_op FStar_SMTEncoding_Term.mkFalse))))::[])
in (((FStar_Syntax_Const.ite_lid), (mk_ite)))::uu____6309)
in (uu____6277)::uu____6299))
in (((FStar_Syntax_Const.imp_lid), (mk_imp)))::uu____6267)
in (uu____6235)::uu____6257))
in (uu____6203)::uu____6225))
in (

let rec fallback = (fun phi -> (match (phi.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(

let uu____6490 = (encode_formula phi' env)
in (match (uu____6490) with
| (phi, decls) -> begin
(

let uu____6497 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled (((phi), (msg), (r)))) r)
in ((uu____6497), (decls)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (uu____6498) -> begin
(

let uu____6503 = (FStar_Syntax_Util.unmeta phi)
in (encode_formula uu____6503 env))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(

let uu____6532 = (encode_match e pats FStar_SMTEncoding_Util.mkFalse env encode_formula)
in (match (uu____6532) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____6540; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____6542; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let uu____6558 = (encode_let x t1 e1 e2 env encode_formula)
in (match (uu____6558) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let head = (FStar_Syntax_Util.un_uinst head)
in (match (((head.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____6590)::((x, uu____6592))::((t, uu____6594))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.has_type_lid) -> begin
(

let uu____6628 = (encode_term x env)
in (match (uu____6628) with
| (x, decls) -> begin
(

let uu____6635 = (encode_term t env)
in (match (uu____6635) with
| (t, decls') -> begin
(

let uu____6642 = (FStar_SMTEncoding_Term.mk_HasType x t)
in ((uu____6642), ((FStar_List.append decls decls'))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((r, uu____6646))::((msg, uu____6648))::((phi, uu____6650))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.labeled_lid) -> begin
(

let uu____6684 = (

let uu____6687 = (

let uu____6688 = (FStar_Syntax_Subst.compress r)
in uu____6688.FStar_Syntax_Syntax.n)
in (

let uu____6691 = (

let uu____6692 = (FStar_Syntax_Subst.compress msg)
in uu____6692.FStar_Syntax_Syntax.n)
in ((uu____6687), (uu____6691))))
in (match (uu____6684) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____6699))) -> begin
(

let phi = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((phi), (FStar_Syntax_Syntax.Meta_labeled ((((FStar_Util.string_of_unicode s)), (r), (false)))))))) None r)
in (fallback phi))
end
| uu____6715 -> begin
(fallback phi)
end))
end
| uu____6718 when (head_redex env head) -> begin
(

let uu____6726 = (whnf env phi)
in (encode_formula uu____6726 env))
end
| uu____6727 -> begin
(

let uu____6735 = (encode_term phi env)
in (match (uu____6735) with
| (tt, decls) -> begin
(

let uu____6742 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___148_6743 = tt
in {FStar_SMTEncoding_Term.tm = uu___148_6743.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___148_6743.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi.FStar_Syntax_Syntax.pos}))
in ((uu____6742), (decls)))
end))
end))
end
| uu____6746 -> begin
(

let uu____6747 = (encode_term phi env)
in (match (uu____6747) with
| (tt, decls) -> begin
(

let uu____6754 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___149_6755 = tt
in {FStar_SMTEncoding_Term.tm = uu___149_6755.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___149_6755.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi.FStar_Syntax_Syntax.pos}))
in ((uu____6754), (decls)))
end))
end))
in (

let encode_q_body = (fun env bs ps body -> (

let uu____6782 = (encode_binders None bs env)
in (match (uu____6782) with
| (vars, guards, env, decls, uu____6804) -> begin
(

let uu____6811 = (

let uu____6818 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let uu____6841 = (

let uu____6846 = (FStar_All.pipe_right p (FStar_List.map (fun uu____6860 -> (match (uu____6860) with
| (t, uu____6866) -> begin
(encode_term t (

let uu___150_6867 = env
in {bindings = uu___150_6867.bindings; depth = uu___150_6867.depth; tcenv = uu___150_6867.tcenv; warn = uu___150_6867.warn; cache = uu___150_6867.cache; nolabels = uu___150_6867.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___150_6867.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right uu____6846 FStar_List.unzip))
in (match (uu____6841) with
| (p, decls) -> begin
((p), ((FStar_List.flatten decls)))
end)))))
in (FStar_All.pipe_right uu____6818 FStar_List.unzip))
in (match (uu____6811) with
| (pats, decls') -> begin
(

let uu____6919 = (encode_formula body env)
in (match (uu____6919) with
| (body, decls'') -> begin
(

let guards = (match (pats) with
| (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (gf), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____6938; FStar_SMTEncoding_Term.rng = uu____6939})::[])::[] when ((FStar_Ident.text_of_lid FStar_Syntax_Const.guard_free) = gf) -> begin
[]
end
| uu____6947 -> begin
guards
end)
in (

let uu____6950 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((vars), (pats), (uu____6950), (body), ((FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') decls''))))))
end))
end))
end)))
in ((debug phi);
(

let phi = (FStar_Syntax_Util.unascribe phi)
in (

let check_pattern_vars = (fun vars pats -> (

let pats = (FStar_All.pipe_right pats (FStar_List.map (fun uu____6984 -> (match (uu____6984) with
| (x, uu____6988) -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x)
end))))
in (match (pats) with
| [] -> begin
()
end
| (hd)::tl -> begin
(

let pat_vars = (

let uu____6994 = (FStar_Syntax_Free.names hd)
in (FStar_List.fold_left (fun out x -> (

let uu____7000 = (FStar_Syntax_Free.names x)
in (FStar_Util.set_union out uu____7000))) uu____6994 tl))
in (

let uu____7002 = (FStar_All.pipe_right vars (FStar_Util.find_opt (fun uu____7014 -> (match (uu____7014) with
| (b, uu____7018) -> begin
(

let uu____7019 = (FStar_Util.set_mem b pat_vars)
in (not (uu____7019)))
end))))
in (match (uu____7002) with
| None -> begin
()
end
| Some (x, uu____7023) -> begin
(

let pos = (FStar_List.fold_left (fun out t -> (FStar_Range.union_ranges out t.FStar_Syntax_Syntax.pos)) hd.FStar_Syntax_Syntax.pos tl)
in (

let uu____7033 = (

let uu____7034 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "SMT pattern misses at least one bound variable: %s" uu____7034))
in (FStar_Errors.warn pos uu____7033)))
end)))
end)))
in (

let uu____7035 = (FStar_Syntax_Util.destruct_typ_as_formula phi)
in (match (uu____7035) with
| None -> begin
(fallback phi)
end
| Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(

let uu____7041 = (FStar_All.pipe_right connectives (FStar_List.tryFind (fun uu____7077 -> (match (uu____7077) with
| (l, uu____7087) -> begin
(FStar_Ident.lid_equals op l)
end))))
in (match (uu____7041) with
| None -> begin
(fallback phi)
end
| Some (uu____7110, f) -> begin
(f phi.FStar_Syntax_Syntax.pos arms)
end))
end
| Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____7139 = (encode_q_body env vars pats body)
in (match (uu____7139) with
| (vars, pats, guard, body, decls) -> begin
(

let tm = (

let uu____7165 = (

let uu____7171 = (FStar_SMTEncoding_Util.mkImp ((guard), (body)))
in ((pats), (vars), (uu____7171)))
in (FStar_SMTEncoding_Term.mkForall uu____7165 phi.FStar_Syntax_Syntax.pos))
in ((tm), (decls)))
end));
)
end
| Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____7183 = (encode_q_body env vars pats body)
in (match (uu____7183) with
| (vars, pats, guard, body, decls) -> begin
(

let uu____7208 = (

let uu____7209 = (

let uu____7215 = (FStar_SMTEncoding_Util.mkAnd ((guard), (body)))
in ((pats), (vars), (uu____7215)))
in (FStar_SMTEncoding_Term.mkExists uu____7209 phi.FStar_Syntax_Syntax.pos))
in ((uu____7208), (decls)))
end));
)
end))));
)))))))))))))))

type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list); is : FStar_Ident.lident  ->  Prims.bool}


let prims : prims_t = (

let uu____7264 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____7264) with
| (asym, a) -> begin
(

let uu____7269 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____7269) with
| (xsym, x) -> begin
(

let uu____7274 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____7274) with
| (ysym, y) -> begin
(

let quant = (fun vars body x -> (

let xname_decl = (

let uu____7304 = (

let uu____7310 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in ((x), (uu____7310), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (uu____7304))
in (

let xtok = (Prims.strcat x "@tok")
in (

let xtok_decl = FStar_SMTEncoding_Term.DeclFun (((xtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let xapp = (

let uu____7325 = (

let uu____7329 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((x), (uu____7329)))
in (FStar_SMTEncoding_Util.mkApp uu____7325))
in (

let xtok = (FStar_SMTEncoding_Util.mkApp ((xtok), ([])))
in (

let xtok_app = (mk_Apply xtok vars)
in (

let uu____7337 = (

let uu____7339 = (

let uu____7341 = (

let uu____7343 = (

let uu____7344 = (

let uu____7349 = (

let uu____7350 = (

let uu____7356 = (FStar_SMTEncoding_Util.mkEq ((xapp), (body)))
in ((((xapp)::[])::[]), (vars), (uu____7356)))
in (FStar_SMTEncoding_Util.mkForall uu____7350))
in ((uu____7349), (None), (Some ((Prims.strcat "primitive_" x)))))
in FStar_SMTEncoding_Term.Assume (uu____7344))
in (

let uu____7366 = (

let uu____7368 = (

let uu____7369 = (

let uu____7374 = (

let uu____7375 = (

let uu____7381 = (FStar_SMTEncoding_Util.mkEq ((xtok_app), (xapp)))
in ((((xtok_app)::[])::[]), (vars), (uu____7381)))
in (FStar_SMTEncoding_Util.mkForall uu____7375))
in ((uu____7374), (Some ("Name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" x)))))
in FStar_SMTEncoding_Term.Assume (uu____7369))
in (uu____7368)::[])
in (uu____7343)::uu____7366))
in (xtok_decl)::uu____7341)
in (xname_decl)::uu____7339)
in ((xtok), (uu____7337))))))))))
in (

let axy = (((asym), (FStar_SMTEncoding_Term.Term_sort)))::(((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let xy = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let qx = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let prims = (

let uu____7431 = (

let uu____7439 = (

let uu____7445 = (

let uu____7446 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7446))
in (quant axy uu____7445))
in ((FStar_Syntax_Const.op_Eq), (uu____7439)))
in (

let uu____7452 = (

let uu____7461 = (

let uu____7469 = (

let uu____7475 = (

let uu____7476 = (

let uu____7477 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_SMTEncoding_Util.mkNot uu____7477))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7476))
in (quant axy uu____7475))
in ((FStar_Syntax_Const.op_notEq), (uu____7469)))
in (

let uu____7483 = (

let uu____7492 = (

let uu____7500 = (

let uu____7506 = (

let uu____7507 = (

let uu____7508 = (

let uu____7511 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7512 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7511), (uu____7512))))
in (FStar_SMTEncoding_Util.mkLT uu____7508))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7507))
in (quant xy uu____7506))
in ((FStar_Syntax_Const.op_LT), (uu____7500)))
in (

let uu____7518 = (

let uu____7527 = (

let uu____7535 = (

let uu____7541 = (

let uu____7542 = (

let uu____7543 = (

let uu____7546 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7547 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7546), (uu____7547))))
in (FStar_SMTEncoding_Util.mkLTE uu____7543))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7542))
in (quant xy uu____7541))
in ((FStar_Syntax_Const.op_LTE), (uu____7535)))
in (

let uu____7553 = (

let uu____7562 = (

let uu____7570 = (

let uu____7576 = (

let uu____7577 = (

let uu____7578 = (

let uu____7581 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7582 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7581), (uu____7582))))
in (FStar_SMTEncoding_Util.mkGT uu____7578))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7577))
in (quant xy uu____7576))
in ((FStar_Syntax_Const.op_GT), (uu____7570)))
in (

let uu____7588 = (

let uu____7597 = (

let uu____7605 = (

let uu____7611 = (

let uu____7612 = (

let uu____7613 = (

let uu____7616 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7617 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7616), (uu____7617))))
in (FStar_SMTEncoding_Util.mkGTE uu____7613))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7612))
in (quant xy uu____7611))
in ((FStar_Syntax_Const.op_GTE), (uu____7605)))
in (

let uu____7623 = (

let uu____7632 = (

let uu____7640 = (

let uu____7646 = (

let uu____7647 = (

let uu____7648 = (

let uu____7651 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7652 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7651), (uu____7652))))
in (FStar_SMTEncoding_Util.mkSub uu____7648))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7647))
in (quant xy uu____7646))
in ((FStar_Syntax_Const.op_Subtraction), (uu____7640)))
in (

let uu____7658 = (

let uu____7667 = (

let uu____7675 = (

let uu____7681 = (

let uu____7682 = (

let uu____7683 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Util.mkMinus uu____7683))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7682))
in (quant qx uu____7681))
in ((FStar_Syntax_Const.op_Minus), (uu____7675)))
in (

let uu____7689 = (

let uu____7698 = (

let uu____7706 = (

let uu____7712 = (

let uu____7713 = (

let uu____7714 = (

let uu____7717 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7718 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7717), (uu____7718))))
in (FStar_SMTEncoding_Util.mkAdd uu____7714))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7713))
in (quant xy uu____7712))
in ((FStar_Syntax_Const.op_Addition), (uu____7706)))
in (

let uu____7724 = (

let uu____7733 = (

let uu____7741 = (

let uu____7747 = (

let uu____7748 = (

let uu____7749 = (

let uu____7752 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7753 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7752), (uu____7753))))
in (FStar_SMTEncoding_Util.mkMul uu____7749))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7748))
in (quant xy uu____7747))
in ((FStar_Syntax_Const.op_Multiply), (uu____7741)))
in (

let uu____7759 = (

let uu____7768 = (

let uu____7776 = (

let uu____7782 = (

let uu____7783 = (

let uu____7784 = (

let uu____7787 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7788 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7787), (uu____7788))))
in (FStar_SMTEncoding_Util.mkDiv uu____7784))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7783))
in (quant xy uu____7782))
in ((FStar_Syntax_Const.op_Division), (uu____7776)))
in (

let uu____7794 = (

let uu____7803 = (

let uu____7811 = (

let uu____7817 = (

let uu____7818 = (

let uu____7819 = (

let uu____7822 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7823 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7822), (uu____7823))))
in (FStar_SMTEncoding_Util.mkMod uu____7819))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7818))
in (quant xy uu____7817))
in ((FStar_Syntax_Const.op_Modulus), (uu____7811)))
in (

let uu____7829 = (

let uu____7838 = (

let uu____7846 = (

let uu____7852 = (

let uu____7853 = (

let uu____7854 = (

let uu____7857 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____7858 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____7857), (uu____7858))))
in (FStar_SMTEncoding_Util.mkAnd uu____7854))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7853))
in (quant xy uu____7852))
in ((FStar_Syntax_Const.op_And), (uu____7846)))
in (

let uu____7864 = (

let uu____7873 = (

let uu____7881 = (

let uu____7887 = (

let uu____7888 = (

let uu____7889 = (

let uu____7892 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____7893 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____7892), (uu____7893))))
in (FStar_SMTEncoding_Util.mkOr uu____7889))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7888))
in (quant xy uu____7887))
in ((FStar_Syntax_Const.op_Or), (uu____7881)))
in (

let uu____7899 = (

let uu____7908 = (

let uu____7916 = (

let uu____7922 = (

let uu____7923 = (

let uu____7924 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Util.mkNot uu____7924))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7923))
in (quant qx uu____7922))
in ((FStar_Syntax_Const.op_Negation), (uu____7916)))
in (uu____7908)::[])
in (uu____7873)::uu____7899))
in (uu____7838)::uu____7864))
in (uu____7803)::uu____7829))
in (uu____7768)::uu____7794))
in (uu____7733)::uu____7759))
in (uu____7698)::uu____7724))
in (uu____7667)::uu____7689))
in (uu____7632)::uu____7658))
in (uu____7597)::uu____7623))
in (uu____7562)::uu____7588))
in (uu____7527)::uu____7553))
in (uu____7492)::uu____7518))
in (uu____7461)::uu____7483))
in (uu____7431)::uu____7452))
in (

let mk = (fun l v -> (

let uu____8052 = (

let uu____8057 = (FStar_All.pipe_right prims (FStar_List.find (fun uu____8089 -> (match (uu____8089) with
| (l', uu____8098) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right uu____8057 (FStar_Option.map (fun uu____8131 -> (match (uu____8131) with
| (uu____8142, b) -> begin
(b v)
end)))))
in (FStar_All.pipe_right uu____8052 FStar_Option.get)))
in (

let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun uu____8183 -> (match (uu____8183) with
| (l', uu____8192) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is})))))))
end))
end))
end))


let pretype_axiom : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun tapp vars -> (

let uu____8215 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____8215) with
| (xxsym, xx) -> begin
(

let uu____8220 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____8220) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let tapp_hash = (FStar_SMTEncoding_Term.hash_of_term tapp)
in (

let uu____8227 = (

let uu____8232 = (

let uu____8233 = (

let uu____8239 = (

let uu____8240 = (

let uu____8243 = (

let uu____8244 = (

let uu____8247 = (FStar_SMTEncoding_Util.mkApp (("PreType"), ((xx)::[])))
in ((tapp), (uu____8247)))
in (FStar_SMTEncoding_Util.mkEq uu____8244))
in ((xx_has_type), (uu____8243)))
in (FStar_SMTEncoding_Util.mkImp uu____8240))
in ((((xx_has_type)::[])::[]), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars), (uu____8239)))
in (FStar_SMTEncoding_Util.mkForall uu____8233))
in (

let uu____8260 = (

let uu____8262 = (

let uu____8263 = (

let uu____8264 = (FStar_Util.digest_of_string tapp_hash)
in (Prims.strcat "pretyping_" uu____8264))
in (varops.mk_unique uu____8263))
in Some (uu____8262))
in ((uu____8232), (Some ("pretyping")), (uu____8260))))
in FStar_SMTEncoding_Term.Assume (uu____8227))))
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

let uu____8295 = (

let uu____8296 = (

let uu____8301 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in ((uu____8301), (Some ("unit typing")), (Some ("unit_typing"))))
in FStar_SMTEncoding_Term.Assume (uu____8296))
in (

let uu____8304 = (

let uu____8306 = (

let uu____8307 = (

let uu____8312 = (

let uu____8313 = (

let uu____8319 = (

let uu____8320 = (

let uu____8323 = (FStar_SMTEncoding_Util.mkEq ((x), (FStar_SMTEncoding_Term.mk_Term_unit)))
in ((typing_pred), (uu____8323)))
in (FStar_SMTEncoding_Util.mkImp uu____8320))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____8319)))
in (mkForall_fuel uu____8313))
in ((uu____8312), (Some ("unit inversion")), (Some ("unit_inversion"))))
in FStar_SMTEncoding_Term.Assume (uu____8307))
in (uu____8306)::[])
in (uu____8295)::uu____8304))))
in (

let mk_bool = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Bool_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____8352 = (

let uu____8353 = (

let uu____8358 = (

let uu____8359 = (

let uu____8365 = (

let uu____8368 = (

let uu____8370 = (FStar_SMTEncoding_Term.boxBool b)
in (uu____8370)::[])
in (uu____8368)::[])
in (

let uu____8373 = (

let uu____8374 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType uu____8374 tt))
in ((uu____8365), ((bb)::[]), (uu____8373))))
in (FStar_SMTEncoding_Util.mkForall uu____8359))
in ((uu____8358), (Some ("bool typing")), (Some ("bool_typing"))))
in FStar_SMTEncoding_Term.Assume (uu____8353))
in (

let uu____8386 = (

let uu____8388 = (

let uu____8389 = (

let uu____8394 = (

let uu____8395 = (

let uu____8401 = (

let uu____8402 = (

let uu____8405 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in ((typing_pred), (uu____8405)))
in (FStar_SMTEncoding_Util.mkImp uu____8402))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____8401)))
in (mkForall_fuel uu____8395))
in ((uu____8394), (Some ("bool inversion")), (Some ("bool_inversion"))))
in FStar_SMTEncoding_Term.Assume (uu____8389))
in (uu____8388)::[])
in (uu____8352)::uu____8386))))))
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

let uu____8440 = (

let uu____8441 = (

let uu____8445 = (

let uu____8447 = (

let uu____8449 = (

let uu____8451 = (FStar_SMTEncoding_Term.boxInt a)
in (

let uu____8452 = (

let uu____8454 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____8454)::[])
in (uu____8451)::uu____8452))
in (tt)::uu____8449)
in (tt)::uu____8447)
in (("Prims.Precedes"), (uu____8445)))
in (FStar_SMTEncoding_Util.mkApp uu____8441))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8440))
in (

let precedes_y_x = (

let uu____8457 = (FStar_SMTEncoding_Util.mkApp (("Precedes"), ((y)::(x)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8457))
in (

let uu____8459 = (

let uu____8460 = (

let uu____8465 = (

let uu____8466 = (

let uu____8472 = (

let uu____8475 = (

let uu____8477 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____8477)::[])
in (uu____8475)::[])
in (

let uu____8480 = (

let uu____8481 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType uu____8481 tt))
in ((uu____8472), ((bb)::[]), (uu____8480))))
in (FStar_SMTEncoding_Util.mkForall uu____8466))
in ((uu____8465), (Some ("int typing")), (Some ("int_typing"))))
in FStar_SMTEncoding_Term.Assume (uu____8460))
in (

let uu____8493 = (

let uu____8495 = (

let uu____8496 = (

let uu____8501 = (

let uu____8502 = (

let uu____8508 = (

let uu____8509 = (

let uu____8512 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in ((typing_pred), (uu____8512)))
in (FStar_SMTEncoding_Util.mkImp uu____8509))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____8508)))
in (mkForall_fuel uu____8502))
in ((uu____8501), (Some ("int inversion")), (Some ("int_inversion"))))
in FStar_SMTEncoding_Term.Assume (uu____8496))
in (

let uu____8526 = (

let uu____8528 = (

let uu____8529 = (

let uu____8534 = (

let uu____8535 = (

let uu____8541 = (

let uu____8542 = (

let uu____8545 = (

let uu____8546 = (

let uu____8548 = (

let uu____8550 = (

let uu____8552 = (

let uu____8553 = (

let uu____8556 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____8557 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____8556), (uu____8557))))
in (FStar_SMTEncoding_Util.mkGT uu____8553))
in (

let uu____8558 = (

let uu____8560 = (

let uu____8561 = (

let uu____8564 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____8565 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____8564), (uu____8565))))
in (FStar_SMTEncoding_Util.mkGTE uu____8561))
in (

let uu____8566 = (

let uu____8568 = (

let uu____8569 = (

let uu____8572 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____8573 = (FStar_SMTEncoding_Term.unboxInt x)
in ((uu____8572), (uu____8573))))
in (FStar_SMTEncoding_Util.mkLT uu____8569))
in (uu____8568)::[])
in (uu____8560)::uu____8566))
in (uu____8552)::uu____8558))
in (typing_pred_y)::uu____8550)
in (typing_pred)::uu____8548)
in (FStar_SMTEncoding_Util.mk_and_l uu____8546))
in ((uu____8545), (precedes_y_x)))
in (FStar_SMTEncoding_Util.mkImp uu____8542))
in ((((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[]), ((xx)::(yy)::[]), (uu____8541)))
in (mkForall_fuel uu____8535))
in ((uu____8534), (Some ("well-founded ordering on nat (alt)")), (Some ("well-founded-ordering-on-nat"))))
in FStar_SMTEncoding_Term.Assume (uu____8529))
in (uu____8528)::[])
in (uu____8495)::uu____8526))
in (uu____8459)::uu____8493)))))))))))
in (

let mk_str = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.String_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____8604 = (

let uu____8605 = (

let uu____8610 = (

let uu____8611 = (

let uu____8617 = (

let uu____8620 = (

let uu____8622 = (FStar_SMTEncoding_Term.boxString b)
in (uu____8622)::[])
in (uu____8620)::[])
in (

let uu____8625 = (

let uu____8626 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType uu____8626 tt))
in ((uu____8617), ((bb)::[]), (uu____8625))))
in (FStar_SMTEncoding_Util.mkForall uu____8611))
in ((uu____8610), (Some ("string typing")), (Some ("string_typing"))))
in FStar_SMTEncoding_Term.Assume (uu____8605))
in (

let uu____8638 = (

let uu____8640 = (

let uu____8641 = (

let uu____8646 = (

let uu____8647 = (

let uu____8653 = (

let uu____8654 = (

let uu____8657 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in ((typing_pred), (uu____8657)))
in (FStar_SMTEncoding_Util.mkImp uu____8654))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____8653)))
in (mkForall_fuel uu____8647))
in ((uu____8646), (Some ("string inversion")), (Some ("string_inversion"))))
in FStar_SMTEncoding_Term.Assume (uu____8641))
in (uu____8640)::[])
in (uu____8604)::uu____8638))))))
in (

let mk_ref = (fun env reft_name uu____8680 -> (

let r = (("r"), (FStar_SMTEncoding_Term.Ref_sort))
in (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let refa = (

let uu____8691 = (

let uu____8695 = (

let uu____8697 = (FStar_SMTEncoding_Util.mkFreeV aa)
in (uu____8697)::[])
in ((reft_name), (uu____8695)))
in (FStar_SMTEncoding_Util.mkApp uu____8691))
in (

let refb = (

let uu____8700 = (

let uu____8704 = (

let uu____8706 = (FStar_SMTEncoding_Util.mkFreeV bb)
in (uu____8706)::[])
in ((reft_name), (uu____8704)))
in (FStar_SMTEncoding_Util.mkApp uu____8700))
in (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (

let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (

let uu____8710 = (

let uu____8711 = (

let uu____8716 = (

let uu____8717 = (

let uu____8723 = (

let uu____8724 = (

let uu____8727 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in ((typing_pred), (uu____8727)))
in (FStar_SMTEncoding_Util.mkImp uu____8724))
in ((((typing_pred)::[])::[]), ((xx)::(aa)::[]), (uu____8723)))
in (mkForall_fuel uu____8717))
in ((uu____8716), (Some ("ref inversion")), (Some ("ref_inversion"))))
in FStar_SMTEncoding_Term.Assume (uu____8711))
in (

let uu____8743 = (

let uu____8745 = (

let uu____8746 = (

let uu____8751 = (

let uu____8752 = (

let uu____8758 = (

let uu____8759 = (

let uu____8762 = (FStar_SMTEncoding_Util.mkAnd ((typing_pred), (typing_pred_b)))
in (

let uu____8763 = (

let uu____8764 = (

let uu____8767 = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let uu____8768 = (FStar_SMTEncoding_Util.mkFreeV bb)
in ((uu____8767), (uu____8768))))
in (FStar_SMTEncoding_Util.mkEq uu____8764))
in ((uu____8762), (uu____8763))))
in (FStar_SMTEncoding_Util.mkImp uu____8759))
in ((((typing_pred)::(typing_pred_b)::[])::[]), ((xx)::(aa)::(bb)::[]), (uu____8758)))
in (mkForall_fuel' (Prims.parse_int "2") uu____8752))
in ((uu____8751), (Some ("ref typing is injective")), (Some ("ref_injectivity"))))
in FStar_SMTEncoding_Term.Assume (uu____8746))
in (uu____8745)::[])
in (uu____8710)::uu____8743))))))))))
in (

let mk_true_interp = (fun env nm true_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((true_tm)::[])))
in (FStar_SMTEncoding_Term.Assume (((valid), (Some ("True interpretation")), (Some ("true_interp")))))::[]))
in (

let mk_false_interp = (fun env nm false_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((false_tm)::[])))
in (

let uu____8812 = (

let uu____8813 = (

let uu____8818 = (FStar_SMTEncoding_Util.mkIff ((FStar_SMTEncoding_Util.mkFalse), (valid)))
in ((uu____8818), (Some ("False interpretation")), (Some ("false_interp"))))
in FStar_SMTEncoding_Term.Assume (uu____8813))
in (uu____8812)::[])))
in (

let mk_and_interp = (fun env conj uu____8830 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let valid = (

let uu____8840 = (

let uu____8844 = (

let uu____8846 = (FStar_SMTEncoding_Util.mkApp ((conj), ((a)::(b)::[])))
in (uu____8846)::[])
in (("Valid"), (uu____8844)))
in (FStar_SMTEncoding_Util.mkApp uu____8840))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____8853 = (

let uu____8854 = (

let uu____8859 = (

let uu____8860 = (

let uu____8866 = (

let uu____8867 = (

let uu____8870 = (FStar_SMTEncoding_Util.mkAnd ((valid_a), (valid_b)))
in ((uu____8870), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____8867))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____8866)))
in (FStar_SMTEncoding_Util.mkForall uu____8860))
in ((uu____8859), (Some ("/\\ interpretation")), (Some ("l_and-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____8854))
in (uu____8853)::[])))))))))
in (

let mk_or_interp = (fun env disj uu____8895 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let valid = (

let uu____8905 = (

let uu____8909 = (

let uu____8911 = (FStar_SMTEncoding_Util.mkApp ((disj), ((a)::(b)::[])))
in (uu____8911)::[])
in (("Valid"), (uu____8909)))
in (FStar_SMTEncoding_Util.mkApp uu____8905))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____8918 = (

let uu____8919 = (

let uu____8924 = (

let uu____8925 = (

let uu____8931 = (

let uu____8932 = (

let uu____8935 = (FStar_SMTEncoding_Util.mkOr ((valid_a), (valid_b)))
in ((uu____8935), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____8932))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____8931)))
in (FStar_SMTEncoding_Util.mkForall uu____8925))
in ((uu____8924), (Some ("\\/ interpretation")), (Some ("l_or-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____8919))
in (uu____8918)::[])))))))))
in (

let mk_eq2_interp = (fun env eq2 tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let yy = (("y"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let y = (FStar_SMTEncoding_Util.mkFreeV yy)
in (

let valid = (

let uu____8974 = (

let uu____8978 = (

let uu____8980 = (FStar_SMTEncoding_Util.mkApp ((eq2), ((a)::(x)::(y)::[])))
in (uu____8980)::[])
in (("Valid"), (uu____8978)))
in (FStar_SMTEncoding_Util.mkApp uu____8974))
in (

let uu____8983 = (

let uu____8984 = (

let uu____8989 = (

let uu____8990 = (

let uu____8996 = (

let uu____8997 = (

let uu____9000 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in ((uu____9000), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____8997))
in ((((valid)::[])::[]), ((aa)::(xx)::(yy)::[]), (uu____8996)))
in (FStar_SMTEncoding_Util.mkForall uu____8990))
in ((uu____8989), (Some ("Eq2 interpretation")), (Some ("eq2-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____8984))
in (uu____8983)::[])))))))))
in (

let mk_eq3_interp = (fun env eq3 tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let yy = (("y"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let y = (FStar_SMTEncoding_Util.mkFreeV yy)
in (

let valid = (

let uu____9045 = (

let uu____9049 = (

let uu____9051 = (FStar_SMTEncoding_Util.mkApp ((eq3), ((a)::(b)::(x)::(y)::[])))
in (uu____9051)::[])
in (("Valid"), (uu____9049)))
in (FStar_SMTEncoding_Util.mkApp uu____9045))
in (

let uu____9054 = (

let uu____9055 = (

let uu____9060 = (

let uu____9061 = (

let uu____9067 = (

let uu____9068 = (

let uu____9071 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in ((uu____9071), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9068))
in ((((valid)::[])::[]), ((aa)::(bb)::(xx)::(yy)::[]), (uu____9067)))
in (FStar_SMTEncoding_Util.mkForall uu____9061))
in ((uu____9060), (Some ("Eq3 interpretation")), (Some ("eq3-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9055))
in (uu____9054)::[])))))))))))
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

let uu____9110 = (

let uu____9114 = (

let uu____9116 = (FStar_SMTEncoding_Util.mkApp ((imp), ((a)::(b)::[])))
in (uu____9116)::[])
in (("Valid"), (uu____9114)))
in (FStar_SMTEncoding_Util.mkApp uu____9110))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____9123 = (

let uu____9124 = (

let uu____9129 = (

let uu____9130 = (

let uu____9136 = (

let uu____9137 = (

let uu____9140 = (FStar_SMTEncoding_Util.mkImp ((valid_a), (valid_b)))
in ((uu____9140), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9137))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9136)))
in (FStar_SMTEncoding_Util.mkForall uu____9130))
in ((uu____9129), (Some ("==> interpretation")), (Some ("l_imp-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9124))
in (uu____9123)::[])))))))))
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

let uu____9175 = (

let uu____9179 = (

let uu____9181 = (FStar_SMTEncoding_Util.mkApp ((iff), ((a)::(b)::[])))
in (uu____9181)::[])
in (("Valid"), (uu____9179)))
in (FStar_SMTEncoding_Util.mkApp uu____9175))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____9188 = (

let uu____9189 = (

let uu____9194 = (

let uu____9195 = (

let uu____9201 = (

let uu____9202 = (

let uu____9205 = (FStar_SMTEncoding_Util.mkIff ((valid_a), (valid_b)))
in ((uu____9205), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9202))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9201)))
in (FStar_SMTEncoding_Util.mkForall uu____9195))
in ((uu____9194), (Some ("<==> interpretation")), (Some ("l_iff-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9189))
in (uu____9188)::[])))))))))
in (

let mk_not_interp = (fun env l_not tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let valid = (

let uu____9236 = (

let uu____9240 = (

let uu____9242 = (FStar_SMTEncoding_Util.mkApp ((l_not), ((a)::[])))
in (uu____9242)::[])
in (("Valid"), (uu____9240)))
in (FStar_SMTEncoding_Util.mkApp uu____9236))
in (

let not_valid_a = (

let uu____9246 = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9246))
in (

let uu____9248 = (

let uu____9249 = (

let uu____9254 = (

let uu____9255 = (

let uu____9261 = (FStar_SMTEncoding_Util.mkIff ((not_valid_a), (valid)))
in ((((valid)::[])::[]), ((aa)::[]), (uu____9261)))
in (FStar_SMTEncoding_Util.mkForall uu____9255))
in ((uu____9254), (Some ("not interpretation")), (Some ("l_not-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9249))
in (uu____9248)::[]))))))
in (

let mk_forall_interp = (fun env for_all tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let valid = (

let uu____9298 = (

let uu____9302 = (

let uu____9304 = (FStar_SMTEncoding_Util.mkApp ((for_all), ((a)::(b)::[])))
in (uu____9304)::[])
in (("Valid"), (uu____9302)))
in (FStar_SMTEncoding_Util.mkApp uu____9298))
in (

let valid_b_x = (

let uu____9308 = (

let uu____9312 = (

let uu____9314 = (FStar_SMTEncoding_Util.mk_ApplyTT b x)
in (uu____9314)::[])
in (("Valid"), (uu____9312)))
in (FStar_SMTEncoding_Util.mkApp uu____9308))
in (

let uu____9316 = (

let uu____9317 = (

let uu____9322 = (

let uu____9323 = (

let uu____9329 = (

let uu____9330 = (

let uu____9333 = (

let uu____9334 = (

let uu____9340 = (

let uu____9343 = (

let uu____9345 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (uu____9345)::[])
in (uu____9343)::[])
in (

let uu____9348 = (

let uu____9349 = (

let uu____9352 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((uu____9352), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp uu____9349))
in ((uu____9340), ((xx)::[]), (uu____9348))))
in (FStar_SMTEncoding_Util.mkForall uu____9334))
in ((uu____9333), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9330))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9329)))
in (FStar_SMTEncoding_Util.mkForall uu____9323))
in ((uu____9322), (Some ("forall interpretation")), (Some ("forall-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9317))
in (uu____9316)::[]))))))))))
in (

let mk_exists_interp = (fun env for_some tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let valid = (

let uu____9400 = (

let uu____9404 = (

let uu____9406 = (FStar_SMTEncoding_Util.mkApp ((for_some), ((a)::(b)::[])))
in (uu____9406)::[])
in (("Valid"), (uu____9404)))
in (FStar_SMTEncoding_Util.mkApp uu____9400))
in (

let valid_b_x = (

let uu____9410 = (

let uu____9414 = (

let uu____9416 = (FStar_SMTEncoding_Util.mk_ApplyTT b x)
in (uu____9416)::[])
in (("Valid"), (uu____9414)))
in (FStar_SMTEncoding_Util.mkApp uu____9410))
in (

let uu____9418 = (

let uu____9419 = (

let uu____9424 = (

let uu____9425 = (

let uu____9431 = (

let uu____9432 = (

let uu____9435 = (

let uu____9436 = (

let uu____9442 = (

let uu____9445 = (

let uu____9447 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (uu____9447)::[])
in (uu____9445)::[])
in (

let uu____9450 = (

let uu____9451 = (

let uu____9454 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((uu____9454), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp uu____9451))
in ((uu____9442), ((xx)::[]), (uu____9450))))
in (FStar_SMTEncoding_Util.mkExists uu____9436))
in ((uu____9435), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9432))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9431)))
in (FStar_SMTEncoding_Util.mkForall uu____9425))
in ((uu____9424), (Some ("exists interpretation")), (Some ("exists-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9419))
in (uu____9418)::[]))))))))))
in (

let mk_range_interp = (fun env range tt -> (

let range_ty = (FStar_SMTEncoding_Util.mkApp ((range), ([])))
in (

let uu____9491 = (

let uu____9492 = (

let uu____9497 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_ty)
in (

let uu____9498 = (

let uu____9500 = (varops.mk_unique "typing_range_const")
in Some (uu____9500))
in ((uu____9497), (Some ("Range_const typing")), (uu____9498))))
in FStar_SMTEncoding_Term.Assume (uu____9492))
in (uu____9491)::[])))
in (

let prims = (((FStar_Syntax_Const.unit_lid), (mk_unit)))::(((FStar_Syntax_Const.bool_lid), (mk_bool)))::(((FStar_Syntax_Const.int_lid), (mk_int)))::(((FStar_Syntax_Const.string_lid), (mk_str)))::(((FStar_Syntax_Const.ref_lid), (mk_ref)))::(((FStar_Syntax_Const.true_lid), (mk_true_interp)))::(((FStar_Syntax_Const.false_lid), (mk_false_interp)))::(((FStar_Syntax_Const.and_lid), (mk_and_interp)))::(((FStar_Syntax_Const.or_lid), (mk_or_interp)))::(((FStar_Syntax_Const.eq2_lid), (mk_eq2_interp)))::(((FStar_Syntax_Const.eq3_lid), (mk_eq3_interp)))::(((FStar_Syntax_Const.imp_lid), (mk_imp_interp)))::(((FStar_Syntax_Const.iff_lid), (mk_iff_interp)))::(((FStar_Syntax_Const.not_lid), (mk_not_interp)))::(((FStar_Syntax_Const.forall_lid), (mk_forall_interp)))::(((FStar_Syntax_Const.exists_lid), (mk_exists_interp)))::(((FStar_Syntax_Const.range_lid), (mk_range_interp)))::[]
in (fun env t s tt -> (

let uu____9763 = (FStar_Util.find_opt (fun uu____9781 -> (match (uu____9781) with
| (l, uu____9791) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)
in (match (uu____9763) with
| None -> begin
[]
end
| Some (uu____9813, f) -> begin
(f env s tt)
end)))))))))))))))))))))))))


let encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____9850 = (encode_function_type_as_formula None None t env)
in (match (uu____9850) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_SMTEncoding_Term.Assume (((form), (Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str))), (Some ((Prims.strcat "lemma_" lid.FStar_Ident.str))))))::[]))
end))))


let encode_free_var : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env fv tt t_norm quals -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____9883 = ((

let uu____9884 = (FStar_Syntax_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation uu____9884)) || (FStar_Syntax_Util.is_lemma t_norm))
in (match (uu____9883) with
| true -> begin
(

let uu____9888 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____9888) with
| (vname, vtok, env) -> begin
(

let arg_sorts = (

let uu____9900 = (

let uu____9901 = (FStar_Syntax_Subst.compress t_norm)
in uu____9901.FStar_Syntax_Syntax.n)
in (match (uu____9900) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____9906) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun uu____9923 -> FStar_SMTEncoding_Term.Term_sort)))
end
| uu____9926 -> begin
[]
end))
in (

let d = FStar_SMTEncoding_Term.DeclFun (((vname), (arg_sorts), (FStar_SMTEncoding_Term.Term_sort), (Some ("Uninterpreted function symbol for impure function"))))
in (

let dd = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Uninterpreted name for impure function"))))
in (((d)::(dd)::[]), (env)))))
end))
end
| uu____9934 -> begin
(

let uu____9935 = (prims.is lid)
in (match (uu____9935) with
| true -> begin
(

let vname = (varops.new_fvar lid)
in (

let uu____9940 = (prims.mk lid vname)
in (match (uu____9940) with
| (tok, definition) -> begin
(

let env = (push_free_var env lid vname (Some (tok)))
in ((definition), (env)))
end)))
end
| uu____9953 -> begin
(

let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (

let uu____9955 = (

let uu____9961 = (curried_arrow_formals_comp t_norm)
in (match (uu____9961) with
| (args, comp) -> begin
(match (encode_non_total_function_typ) with
| true -> begin
(

let uu____9976 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in ((args), (uu____9976)))
end
| uu____9983 -> begin
((args), (((None), ((FStar_Syntax_Util.comp_result comp)))))
end)
end))
in (match (uu____9955) with
| (formals, (pre_opt, res_t)) -> begin
(

let uu____10003 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____10003) with
| (vname, vtok, env) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
end
| uu____10016 -> begin
(FStar_SMTEncoding_Util.mkApp ((vtok), ([])))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun uu___123_10040 -> (match (uu___123_10040) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(

let uu____10043 = (FStar_Util.prefix vars)
in (match (uu____10043) with
| (uu____10054, (xxsym, uu____10056)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____10066 = (

let uu____10067 = (

let uu____10072 = (

let uu____10073 = (

let uu____10079 = (

let uu____10080 = (

let uu____10083 = (

let uu____10084 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____10084))
in ((vapp), (uu____10083)))
in (FStar_SMTEncoding_Util.mkEq uu____10080))
in ((((vapp)::[])::[]), (vars), (uu____10079)))
in (FStar_SMTEncoding_Util.mkForall uu____10073))
in ((uu____10072), (Some ("Discriminator equation")), (Some ((Prims.strcat "disc_equation_" (escape d.FStar_Ident.str))))))
in FStar_SMTEncoding_Term.Assume (uu____10067))
in (uu____10066)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(

let uu____10096 = (FStar_Util.prefix vars)
in (match (uu____10096) with
| (uu____10107, (xxsym, uu____10109)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (

let tp_name = (mk_term_projector_name d f)
in (

let prim_app = (FStar_SMTEncoding_Util.mkApp ((tp_name), ((xx)::[])))
in (

let uu____10123 = (

let uu____10124 = (

let uu____10129 = (

let uu____10130 = (

let uu____10136 = (FStar_SMTEncoding_Util.mkEq ((vapp), (prim_app)))
in ((((vapp)::[])::[]), (vars), (uu____10136)))
in (FStar_SMTEncoding_Util.mkForall uu____10130))
in ((uu____10129), (Some ("Projector equation")), (Some ((Prims.strcat "proj_equation_" tp_name)))))
in FStar_SMTEncoding_Term.Assume (uu____10124))
in (uu____10123)::[])))))
end))
end
| uu____10146 -> begin
[]
end)))))
in (

let uu____10147 = (encode_binders None formals env)
in (match (uu____10147) with
| (vars, guards, env', decls1, uu____10163) -> begin
(

let uu____10170 = (match (pre_opt) with
| None -> begin
(

let uu____10175 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____10175), (decls1)))
end
| Some (p) -> begin
(

let uu____10177 = (encode_formula p env')
in (match (uu____10177) with
| (g, ds) -> begin
(

let uu____10184 = (FStar_SMTEncoding_Util.mk_and_l ((g)::guards))
in ((uu____10184), ((FStar_List.append decls1 ds))))
end))
end)
in (match (uu____10170) with
| (guard, decls1) -> begin
(

let vtok_app = (mk_Apply vtok_tm vars)
in (

let vapp = (

let uu____10193 = (

let uu____10197 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((vname), (uu____10197)))
in (FStar_SMTEncoding_Util.mkApp uu____10193))
in (

let uu____10202 = (

let vname_decl = (

let uu____10207 = (

let uu____10213 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____10218 -> FStar_SMTEncoding_Term.Term_sort)))
in ((vname), (uu____10213), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (uu____10207))
in (

let uu____10223 = (

let env = (

let uu___151_10227 = env
in {bindings = uu___151_10227.bindings; depth = uu___151_10227.depth; tcenv = uu___151_10227.tcenv; warn = uu___151_10227.warn; cache = uu___151_10227.cache; nolabels = uu___151_10227.nolabels; use_zfuel_name = uu___151_10227.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in (

let uu____10228 = (

let uu____10229 = (head_normal env tt)
in (not (uu____10229)))
in (match (uu____10228) with
| true -> begin
(encode_term_pred None tt env vtok_tm)
end
| uu____10232 -> begin
(encode_term_pred None t_norm env vtok_tm)
end)))
in (match (uu____10223) with
| (tok_typing, decls2) -> begin
(

let tok_typing = FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("function token typing")), (Some ((Prims.strcat "function_token_typing_" vname)))))
in (

let uu____10241 = (match (formals) with
| [] -> begin
(

let uu____10250 = (

let uu____10251 = (

let uu____10253 = (FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left (fun _0_34 -> Some (_0_34)) uu____10253))
in (push_free_var env lid vname uu____10251))
in (((FStar_List.append decls2 ((tok_typing)::[]))), (uu____10250)))
end
| uu____10256 -> begin
(

let vtok_decl = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let vtok_fresh = (

let uu____10261 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((vtok), (FStar_SMTEncoding_Term.Term_sort)) uu____10261))
in (

let name_tok_corr = (

let uu____10263 = (

let uu____10268 = (

let uu____10269 = (

let uu____10275 = (FStar_SMTEncoding_Util.mkEq ((vtok_app), (vapp)))
in ((((vtok_app)::[])::((vapp)::[])::[]), (vars), (uu____10275)))
in (FStar_SMTEncoding_Util.mkForall uu____10269))
in ((uu____10268), (Some ("Name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" vname)))))
in FStar_SMTEncoding_Term.Assume (uu____10263))
in (((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[]))), (env)))))
end)
in (match (uu____10241) with
| (tok_decl, env) -> begin
(((vname_decl)::tok_decl), (env))
end)))
end)))
in (match (uu____10202) with
| (decls2, env) -> begin
(

let uu____10300 = (

let res_t = (FStar_Syntax_Subst.compress res_t)
in (

let uu____10305 = (encode_term res_t env')
in (match (uu____10305) with
| (encoded_res_t, decls) -> begin
(

let uu____10313 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in ((encoded_res_t), (uu____10313), (decls)))
end)))
in (match (uu____10300) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (

let uu____10321 = (

let uu____10326 = (

let uu____10327 = (

let uu____10333 = (FStar_SMTEncoding_Util.mkImp ((guard), (ty_pred)))
in ((((vapp)::[])::[]), (vars), (uu____10333)))
in (FStar_SMTEncoding_Util.mkForall uu____10327))
in ((uu____10326), (Some ("free var typing")), (Some ((Prims.strcat "typing_" vname)))))
in FStar_SMTEncoding_Term.Assume (uu____10321))
in (

let freshness = (

let uu____10343 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New))
in (match (uu____10343) with
| true -> begin
(

let uu____10346 = (

let uu____10347 = (

let uu____10353 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (

let uu____10359 = (varops.next_id ())
in ((vname), (uu____10353), (FStar_SMTEncoding_Term.Term_sort), (uu____10359))))
in (FStar_SMTEncoding_Term.fresh_constructor uu____10347))
in (

let uu____10361 = (

let uu____10363 = (pretype_axiom vapp vars)
in (uu____10363)::[])
in (uu____10346)::uu____10361))
end
| uu____10364 -> begin
[]
end))
in (

let g = (

let uu____10367 = (

let uu____10369 = (

let uu____10371 = (

let uu____10373 = (

let uu____10375 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::uu____10375)
in (FStar_List.append freshness uu____10373))
in (FStar_List.append decls3 uu____10371))
in (FStar_List.append decls2 uu____10369))
in (FStar_List.append decls1 uu____10367))
in ((g), (env)))))
end))
end))))
end))
end))))
end))
end)))
end))
end))))


let declare_top_level_let : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  ((Prims.string * FStar_SMTEncoding_Term.term Prims.option) * FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env x t t_norm -> (

let uu____10397 = (try_lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____10397) with
| None -> begin
(

let uu____10420 = (encode_free_var env x t t_norm [])
in (match (uu____10420) with
| (decls, env) -> begin
(

let uu____10435 = (lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____10435) with
| (n, x', uu____10454) -> begin
((((n), (x'))), (decls), (env))
end))
end))
end
| Some (n, x, uu____10466) -> begin
((((n), (x))), ([]), (env))
end)))


let encode_top_level_val : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env lid t quals -> (

let tt = (norm env t)
in (

let uu____10499 = (encode_free_var env lid t tt quals)
in (match (uu____10499) with
| (decls, env) -> begin
(

let uu____10510 = (FStar_Syntax_Util.is_smt_lemma t)
in (match (uu____10510) with
| true -> begin
(

let uu____10514 = (

let uu____10516 = (encode_smt_lemma env lid tt)
in (FStar_List.append decls uu____10516))
in ((uu____10514), (env)))
end
| uu____10519 -> begin
((decls), (env))
end))
end))))


let encode_top_level_vals : env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____10544 lb -> (match (uu____10544) with
| (decls, env) -> begin
(

let uu____10556 = (

let uu____10560 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env uu____10560 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (uu____10556) with
| (decls', env) -> begin
(((FStar_List.append decls decls')), (env))
end))
end)) (([]), (env)))))


let encode_top_level_let : env_t  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env uu____10584 quals -> (match (uu____10584) with
| (is_rec, bindings) -> begin
(

let eta_expand = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let uu____10633 = (FStar_Util.first_N nbinders formals)
in (match (uu____10633) with
| (formals, extra_formals) -> begin
(

let subst = (FStar_List.map2 (fun uu____10673 uu____10674 -> (match (((uu____10673), (uu____10674))) with
| ((formal, uu____10684), (binder, uu____10686)) -> begin
(

let uu____10691 = (

let uu____10696 = (FStar_Syntax_Syntax.bv_to_name binder)
in ((formal), (uu____10696)))
in FStar_Syntax_Syntax.NT (uu____10691))
end)) formals binders)
in (

let extra_formals = (

let uu____10701 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun uu____10715 -> (match (uu____10715) with
| (x, i) -> begin
(

let uu____10722 = (

let uu___152_10723 = x
in (

let uu____10724 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___152_10723.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___152_10723.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____10724}))
in ((uu____10722), (i)))
end))))
in (FStar_All.pipe_right uu____10701 FStar_Syntax_Util.name_binders))
in (

let body = (

let uu____10736 = (

let uu____10738 = (

let uu____10739 = (FStar_Syntax_Subst.subst subst t)
in uu____10739.FStar_Syntax_Syntax.n)
in (FStar_All.pipe_left (fun _0_35 -> Some (_0_35)) uu____10738))
in (

let uu____10743 = (

let uu____10744 = (FStar_Syntax_Subst.compress body)
in (

let uu____10745 = (

let uu____10746 = (FStar_Syntax_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd uu____10746))
in (FStar_Syntax_Syntax.extend_app_n uu____10744 uu____10745)))
in (uu____10743 uu____10736 body.FStar_Syntax_Syntax.pos)))
in (((FStar_List.append binders extra_formals)), (body)))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (

let rec aux = (fun norm t_norm -> (

let uu____10805 = (FStar_Syntax_Util.abs_formals e)
in (match (uu____10805) with
| (binders, body, lopt) -> begin
(match (binders) with
| (uu____10858)::uu____10859 -> begin
(

let uu____10867 = (

let uu____10868 = (FStar_Syntax_Subst.compress t_norm)
in uu____10868.FStar_Syntax_Syntax.n)
in (match (uu____10867) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____10897 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____10897) with
| (formals, c) -> begin
(

let nformals = (FStar_List.length formals)
in (

let nbinders = (FStar_List.length binders)
in (

let tres = (FStar_Syntax_Util.comp_result c)
in (

let uu____10927 = ((nformals < nbinders) && (FStar_Syntax_Util.is_total_comp c))
in (match (uu____10927) with
| true -> begin
(

let uu____10947 = (FStar_Util.first_N nformals binders)
in (match (uu____10947) with
| (bs0, rest) -> begin
(

let c = (

let subst = (FStar_List.map2 (fun uu____10995 uu____10996 -> (match (((uu____10995), (uu____10996))) with
| ((b, uu____11006), (x, uu____11008)) -> begin
(

let uu____11013 = (

let uu____11018 = (FStar_Syntax_Syntax.bv_to_name x)
in ((b), (uu____11018)))
in FStar_Syntax_Syntax.NT (uu____11013))
end)) bs0 formals)
in (FStar_Syntax_Subst.subst_comp subst c))
in (

let body = (FStar_Syntax_Util.abs rest body lopt)
in ((((bs0), (body), (bs0), ((FStar_Syntax_Util.comp_result c)))), (false))))
end))
end
| uu____11040 -> begin
(match ((nformals > nbinders)) with
| true -> begin
(

let uu____11060 = (eta_expand binders formals body tres)
in (match (uu____11060) with
| (binders, body) -> begin
((((binders), (body), (formals), (tres))), (false))
end))
end
| uu____11112 -> begin
((((binders), (body), (formals), (tres))), (false))
end)
end)))))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____11122) -> begin
(

let uu____11127 = (

let uu____11140 = (aux norm x.FStar_Syntax_Syntax.sort)
in (Prims.fst uu____11140))
in ((uu____11127), (true)))
end
| uu____11179 when (not (norm)) -> begin
(

let t_norm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm)
in (aux true t_norm))
end
| uu____11181 -> begin
(

let uu____11182 = (

let uu____11183 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____11184 = (FStar_Syntax_Print.term_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str uu____11183 uu____11184)))
in (failwith uu____11182))
end))
end
| uu____11199 -> begin
(

let uu____11200 = (

let uu____11201 = (FStar_Syntax_Subst.compress t_norm)
in uu____11201.FStar_Syntax_Syntax.n)
in (match (uu____11200) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____11230 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____11230) with
| (formals, c) -> begin
(

let tres = (FStar_Syntax_Util.comp_result c)
in (

let uu____11252 = (eta_expand [] formals e tres)
in (match (uu____11252) with
| (binders, body) -> begin
((((binders), (body), (formals), (tres))), (false))
end)))
end))
end
| uu____11306 -> begin
(((([]), (e), ([]), (t_norm))), (false))
end))
end)
end)))
in (aux false t_norm)))
in try
(match (()) with
| () -> begin
(

let uu____11334 = (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp))))
in (match (uu____11334) with
| true -> begin
(encode_top_level_vals env bindings quals)
end
| uu____11340 -> begin
(

let uu____11341 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____11382 lb -> (match (uu____11382) with
| (toks, typs, decls, env) -> begin
((

let uu____11433 = (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp)
in (match (uu____11433) with
| true -> begin
(Prims.raise Let_rec_unencodeable)
end
| uu____11434 -> begin
()
end));
(

let t_norm = (whnf env lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____11436 = (

let uu____11444 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env uu____11444 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (uu____11436) with
| (tok, decl, env) -> begin
(

let uu____11469 = (

let uu____11476 = (

let uu____11482 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in ((uu____11482), (tok)))
in (uu____11476)::toks)
in ((uu____11469), ((t_norm)::typs), ((decl)::decls), (env)))
end)));
)
end)) (([]), ([]), ([]), (env))))
in (match (uu____11341) with
| (toks, typs, decls, env) -> begin
(

let toks = (FStar_List.rev toks)
in (

let decls = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (

let typs = (FStar_List.rev typs)
in (

let mk_app = (fun curry f ftok vars -> (match (vars) with
| [] -> begin
(FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
end
| uu____11584 -> begin
(match (curry) with
| true -> begin
(match (ftok) with
| Some (ftok) -> begin
(mk_Apply ftok vars)
end
| None -> begin
(

let uu____11589 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply uu____11589 vars))
end)
end
| uu____11590 -> begin
(

let uu____11591 = (

let uu____11595 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (uu____11595)))
in (FStar_SMTEncoding_Util.mkApp uu____11591))
end)
end))
in (

let uu____11600 = ((FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___124_11602 -> (match (uu___124_11602) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| uu____11603 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> (

let uu____11606 = (FStar_Syntax_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation uu____11606))))))
in (match (uu____11600) with
| true -> begin
((decls), (env))
end
| uu____11611 -> begin
(match ((not (is_rec))) with
| true -> begin
(match (((bindings), (typs), (toks))) with
| (({FStar_Syntax_Syntax.lbname = uu____11626; FStar_Syntax_Syntax.lbunivs = uu____11627; FStar_Syntax_Syntax.lbtyp = uu____11628; FStar_Syntax_Syntax.lbeff = uu____11629; FStar_Syntax_Syntax.lbdef = e})::[], (t_norm)::[], ((flid_fv, (f, ftok)))::[]) -> begin
(

let e = (FStar_Syntax_Subst.compress e)
in (

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____11671 = (destruct_bound_function flid t_norm e)
in (match (uu____11671) with
| ((binders, body, uu____11683, uu____11684), curry) -> begin
(

let uu____11690 = (encode_binders None binders env)
in (match (uu____11690) with
| (vars, guards, env', binder_decls, uu____11706) -> begin
(

let app = (mk_app curry f ftok vars)
in (

let uu____11714 = (

let uu____11719 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic))
in (match (uu____11719) with
| true -> begin
(

let uu____11725 = (FStar_SMTEncoding_Term.mk_Valid app)
in (

let uu____11726 = (encode_formula body env')
in ((uu____11725), (uu____11726))))
end
| uu____11731 -> begin
(

let uu____11732 = (encode_term body env')
in ((app), (uu____11732)))
end))
in (match (uu____11714) with
| (app, (body, decls2)) -> begin
(

let eqn = (

let uu____11746 = (

let uu____11751 = (

let uu____11752 = (

let uu____11758 = (FStar_SMTEncoding_Util.mkEq ((app), (body)))
in ((((app)::[])::[]), (vars), (uu____11758)))
in (FStar_SMTEncoding_Util.mkForall uu____11752))
in (

let uu____11764 = (

let uu____11766 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (uu____11766))
in ((uu____11751), (uu____11764), (Some ((Prims.strcat "equation_" f))))))
in FStar_SMTEncoding_Term.Assume (uu____11746))
in (

let uu____11769 = (

let uu____11771 = (

let uu____11773 = (

let uu____11775 = (

let uu____11777 = (primitive_type_axioms env.tcenv flid f app)
in (FStar_List.append ((eqn)::[]) uu____11777))
in (FStar_List.append decls2 uu____11775))
in (FStar_List.append binder_decls uu____11773))
in (FStar_List.append decls uu____11771))
in ((uu____11769), (env))))
end)))
end))
end))))
end
| uu____11780 -> begin
(failwith "Impossible")
end)
end
| uu____11795 -> begin
(

let fuel = (

let uu____11799 = (varops.fresh "fuel")
in ((uu____11799), (FStar_SMTEncoding_Term.Fuel_sort)))
in (

let fuel_tm = (FStar_SMTEncoding_Util.mkFreeV fuel)
in (

let env0 = env
in (

let uu____11802 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun uu____11841 uu____11842 -> (match (((uu____11841), (uu____11842))) with
| ((gtoks, env), (flid_fv, (f, ftok))) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let g = (

let uu____11924 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented")
in (varops.new_fvar uu____11924))
in (

let gtok = (

let uu____11926 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented_token")
in (varops.new_fvar uu____11926))
in (

let env = (

let uu____11928 = (

let uu____11930 = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::[])))
in (FStar_All.pipe_left (fun _0_36 -> Some (_0_36)) uu____11930))
in (push_free_var env flid gtok uu____11928))
in (((((flid), (f), (ftok), (g), (gtok)))::gtoks), (env))))))
end)) (([]), (env))))
in (match (uu____11802) with
| (gtoks, env) -> begin
(

let gtoks = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env0 uu____12014 t_norm uu____12016 -> (match (((uu____12014), (uu____12016))) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = lbn; FStar_Syntax_Syntax.lbunivs = uu____12040; FStar_Syntax_Syntax.lbtyp = uu____12041; FStar_Syntax_Syntax.lbeff = uu____12042; FStar_Syntax_Syntax.lbdef = e}) -> begin
((

let uu____12060 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____12060) with
| true -> begin
(

let uu____12061 = (FStar_Syntax_Print.lbname_to_string lbn)
in (

let uu____12062 = (FStar_Syntax_Print.term_to_string t_norm)
in (

let uu____12063 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print3 "Encoding let rec %s : %s = %s\n" uu____12061 uu____12062 uu____12063))))
end
| uu____12064 -> begin
()
end));
(

let uu____12065 = (destruct_bound_function flid t_norm e)
in (match (uu____12065) with
| ((binders, body, formals, tres), curry) -> begin
((

let uu____12087 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____12087) with
| true -> begin
(

let uu____12088 = (FStar_Syntax_Print.binders_to_string ", " binders)
in (

let uu____12089 = (FStar_Syntax_Print.term_to_string body)
in (FStar_Util.print2 "Encoding let rec: binders=[%s], body=%s\n" uu____12088 uu____12089)))
end
| uu____12090 -> begin
()
end));
(match (curry) with
| true -> begin
(failwith "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type")
end
| uu____12092 -> begin
()
end);
(

let uu____12093 = (encode_binders None binders env)
in (match (uu____12093) with
| (vars, guards, env', binder_decls, uu____12111) -> begin
(

let decl_g = (

let uu____12119 = (

let uu____12125 = (

let uu____12127 = (FStar_List.map Prims.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::uu____12127)
in ((g), (uu____12125), (FStar_SMTEncoding_Term.Term_sort), (Some ("Fuel-instrumented function name"))))
in FStar_SMTEncoding_Term.DeclFun (uu____12119))
in (

let env0 = (push_zfuel_name env0 flid g)
in (

let decl_g_tok = FStar_SMTEncoding_Term.DeclFun (((gtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Token for fuel-instrumented partial applications"))))
in (

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let app = (

let uu____12142 = (

let uu____12146 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (uu____12146)))
in (FStar_SMTEncoding_Util.mkApp uu____12142))
in (

let gsapp = (

let uu____12152 = (

let uu____12156 = (

let uu____12158 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (uu____12158)::vars_tm)
in ((g), (uu____12156)))
in (FStar_SMTEncoding_Util.mkApp uu____12152))
in (

let gmax = (

let uu____12162 = (

let uu____12166 = (

let uu____12168 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (uu____12168)::vars_tm)
in ((g), (uu____12166)))
in (FStar_SMTEncoding_Util.mkApp uu____12162))
in (

let uu____12171 = (encode_term body env')
in (match (uu____12171) with
| (body_tm, decls2) -> begin
(

let eqn_g = (

let uu____12182 = (

let uu____12187 = (

let uu____12188 = (

let uu____12196 = (FStar_SMTEncoding_Util.mkEq ((gsapp), (body_tm)))
in ((((gsapp)::[])::[]), (Some ((Prims.parse_int "0"))), ((fuel)::vars), (uu____12196)))
in (FStar_SMTEncoding_Util.mkForall' uu____12188))
in (

let uu____12207 = (

let uu____12209 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (uu____12209))
in ((uu____12187), (uu____12207), (Some ((Prims.strcat "equation_with_fuel_" g))))))
in FStar_SMTEncoding_Term.Assume (uu____12182))
in (

let eqn_f = (

let uu____12213 = (

let uu____12218 = (

let uu____12219 = (

let uu____12225 = (FStar_SMTEncoding_Util.mkEq ((app), (gmax)))
in ((((app)::[])::[]), (vars), (uu____12225)))
in (FStar_SMTEncoding_Util.mkForall uu____12219))
in ((uu____12218), (Some ("Correspondence of recursive function to instrumented version")), (Some ((Prims.strcat "fuel_correspondence_" g)))))
in FStar_SMTEncoding_Term.Assume (uu____12213))
in (

let eqn_g' = (

let uu____12234 = (

let uu____12239 = (

let uu____12240 = (

let uu____12246 = (

let uu____12247 = (

let uu____12250 = (

let uu____12251 = (

let uu____12255 = (

let uu____12257 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "0"))
in (uu____12257)::vars_tm)
in ((g), (uu____12255)))
in (FStar_SMTEncoding_Util.mkApp uu____12251))
in ((gsapp), (uu____12250)))
in (FStar_SMTEncoding_Util.mkEq uu____12247))
in ((((gsapp)::[])::[]), ((fuel)::vars), (uu____12246)))
in (FStar_SMTEncoding_Util.mkForall uu____12240))
in ((uu____12239), (Some ("Fuel irrelevance")), (Some ((Prims.strcat "fuel_irrelevance_" g)))))
in FStar_SMTEncoding_Term.Assume (uu____12234))
in (

let uu____12270 = (

let uu____12275 = (encode_binders None formals env0)
in (match (uu____12275) with
| (vars, v_guards, env, binder_decls, uu____12292) -> begin
(

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let gapp = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::vars_tm)))
in (

let tok_corr = (

let tok_app = (

let uu____12307 = (FStar_SMTEncoding_Util.mkFreeV ((gtok), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply uu____12307 ((fuel)::vars)))
in (

let uu____12310 = (

let uu____12315 = (

let uu____12316 = (

let uu____12322 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (gapp)))
in ((((tok_app)::[])::[]), ((fuel)::vars), (uu____12322)))
in (FStar_SMTEncoding_Util.mkForall uu____12316))
in ((uu____12315), (Some ("Fuel token correspondence")), (Some ((Prims.strcat "fuel_token_correspondence_" gtok)))))
in FStar_SMTEncoding_Term.Assume (uu____12310)))
in (

let uu____12334 = (

let uu____12338 = (encode_term_pred None tres env gapp)
in (match (uu____12338) with
| (g_typing, d3) -> begin
(

let uu____12346 = (

let uu____12348 = (

let uu____12349 = (

let uu____12354 = (

let uu____12355 = (

let uu____12361 = (

let uu____12362 = (

let uu____12365 = (FStar_SMTEncoding_Util.mk_and_l v_guards)
in ((uu____12365), (g_typing)))
in (FStar_SMTEncoding_Util.mkImp uu____12362))
in ((((gapp)::[])::[]), ((fuel)::vars), (uu____12361)))
in (FStar_SMTEncoding_Util.mkForall uu____12355))
in ((uu____12354), (Some ("Typing correspondence of token to term")), (Some ((Prims.strcat "token_correspondence_" g)))))
in FStar_SMTEncoding_Term.Assume (uu____12349))
in (uu____12348)::[])
in ((d3), (uu____12346)))
end))
in (match (uu____12334) with
| (aux_decls, typing_corr) -> begin
(((FStar_List.append binder_decls aux_decls)), ((FStar_List.append typing_corr ((tok_corr)::[]))))
end)))))
end))
in (match (uu____12270) with
| (aux_decls, g_typing) -> begin
(((FStar_List.append binder_decls (FStar_List.append decls2 (FStar_List.append aux_decls ((decl_g)::(decl_g_tok)::[]))))), ((FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing)), (env0))
end)))))
end)))))))))
end));
)
end));
)
end))
in (

let uu____12401 = (

let uu____12408 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun uu____12440 uu____12441 -> (match (((uu____12440), (uu____12441))) with
| ((decls, eqns, env0), (gtok, ty, lb)) -> begin
(

let uu____12517 = (encode_one_binding env0 gtok ty lb)
in (match (uu____12517) with
| (decls', eqns', env0) -> begin
(((decls')::decls), ((FStar_List.append eqns' eqns)), (env0))
end))
end)) (((decls)::[]), ([]), (env0)) uu____12408))
in (match (uu____12401) with
| (decls, eqns, env0) -> begin
(

let uu____12557 = (

let uu____12562 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right uu____12562 (FStar_List.partition (fun uu___125_12572 -> (match (uu___125_12572) with
| FStar_SMTEncoding_Term.DeclFun (uu____12573) -> begin
true
end
| uu____12579 -> begin
false
end)))))
in (match (uu____12557) with
| (prefix_decls, rest) -> begin
(

let eqns = (FStar_List.rev eqns)
in (((FStar_List.append prefix_decls (FStar_List.append rest eqns))), (env0)))
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

let uu____12597 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right uu____12597 (FStar_String.concat " and ")))
in (

let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in (((decl)::[]), (env))))
end))
end))


let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> ((

let uu____12630 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____12630) with
| true -> begin
(

let uu____12631 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") uu____12631))
end
| uu____12632 -> begin
()
end));
(

let nm = (

let uu____12634 = (FStar_Syntax_Util.lid_of_sigelt se)
in (match (uu____12634) with
| None -> begin
""
end
| Some (l) -> begin
l.FStar_Ident.str
end))
in (

let uu____12637 = (encode_sigelt' env se)
in (match (uu____12637) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(

let uu____12646 = (

let uu____12648 = (

let uu____12649 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (uu____12649))
in (uu____12648)::[])
in ((uu____12646), (e)))
end
| uu____12651 -> begin
(

let uu____12652 = (

let uu____12654 = (

let uu____12656 = (

let uu____12657 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____12657))
in (uu____12656)::g)
in (

let uu____12658 = (

let uu____12660 = (

let uu____12661 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____12661))
in (uu____12660)::[])
in (FStar_List.append uu____12654 uu____12658)))
in ((uu____12652), (e)))
end)
end)));
))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____12669) -> begin
(failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, uu____12680) -> begin
(

let uu____12681 = (

let uu____12682 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right uu____12682 Prims.op_Negation))
in (match (uu____12681) with
| true -> begin
(([]), (env))
end
| uu____12687 -> begin
(

let close_effect_params = (fun tm -> (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
tm
end
| uu____12702 -> begin
(

let uu____12703 = (

let uu____12706 = (

let uu____12707 = (

let uu____12722 = (FStar_All.pipe_left (fun _0_37 -> Some (_0_37)) (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[])))))
in ((ed.FStar_Syntax_Syntax.binders), (tm), (uu____12722)))
in FStar_Syntax_Syntax.Tm_abs (uu____12707))
in (FStar_Syntax_Syntax.mk uu____12706))
in (uu____12703 None tm.FStar_Syntax_Syntax.pos))
end))
in (

let encode_action = (fun env a -> (

let uu____12775 = (new_term_constant_and_tok_from_lid env a.FStar_Syntax_Syntax.action_name)
in (match (uu____12775) with
| (aname, atok, env) -> begin
(

let uu____12785 = (FStar_Syntax_Util.arrow_formals_comp a.FStar_Syntax_Syntax.action_typ)
in (match (uu____12785) with
| (formals, uu____12795) -> begin
(

let uu____12802 = (

let uu____12805 = (close_effect_params a.FStar_Syntax_Syntax.action_defn)
in (encode_term uu____12805 env))
in (match (uu____12802) with
| (tm, decls) -> begin
(

let a_decls = (

let uu____12813 = (

let uu____12814 = (

let uu____12820 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____12828 -> FStar_SMTEncoding_Term.Term_sort)))
in ((aname), (uu____12820), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action"))))
in FStar_SMTEncoding_Term.DeclFun (uu____12814))
in (uu____12813)::(FStar_SMTEncoding_Term.DeclFun (((atok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action token")))))::[])
in (

let uu____12835 = (

let uu____12842 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____12862 -> (match (uu____12862) with
| (bv, uu____12870) -> begin
(

let uu____12871 = (gen_term_var env bv)
in (match (uu____12871) with
| (xxsym, xx, uu____12881) -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (xx))
end))
end))))
in (FStar_All.pipe_right uu____12842 FStar_List.split))
in (match (uu____12835) with
| (xs_sorts, xs) -> begin
(

let app = (

let uu____12911 = (

let uu____12915 = (

let uu____12917 = (FStar_SMTEncoding_Util.mkApp ((aname), (xs)))
in (uu____12917)::[])
in (("Reify"), (uu____12915)))
in (FStar_SMTEncoding_Util.mkApp uu____12911))
in (

let a_eq = (

let uu____12921 = (

let uu____12926 = (

let uu____12927 = (

let uu____12933 = (

let uu____12934 = (

let uu____12937 = (mk_Apply tm xs_sorts)
in ((app), (uu____12937)))
in (FStar_SMTEncoding_Util.mkEq uu____12934))
in ((((app)::[])::[]), (xs_sorts), (uu____12933)))
in (FStar_SMTEncoding_Util.mkForall uu____12927))
in ((uu____12926), (Some ("Action equality")), (Some ((Prims.strcat aname "_equality")))))
in FStar_SMTEncoding_Term.Assume (uu____12921))
in (

let tok_correspondence = (

let tok_term = (FStar_SMTEncoding_Util.mkFreeV ((atok), (FStar_SMTEncoding_Term.Term_sort)))
in (

let tok_app = (mk_Apply tok_term xs_sorts)
in (

let uu____12950 = (

let uu____12955 = (

let uu____12956 = (

let uu____12962 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (app)))
in ((((tok_app)::[])::[]), (xs_sorts), (uu____12962)))
in (FStar_SMTEncoding_Util.mkForall uu____12956))
in ((uu____12955), (Some ("Action token correspondence")), (Some ((Prims.strcat aname "_token_correspondence")))))
in FStar_SMTEncoding_Term.Assume (uu____12950))))
in ((env), ((FStar_List.append decls (FStar_List.append a_decls ((a_eq)::(tok_correspondence)::[]))))))))
end)))
end))
end))
end)))
in (

let uu____12973 = (FStar_Util.fold_map encode_action env ed.FStar_Syntax_Syntax.actions)
in (match (uu____12973) with
| (env, decls2) -> begin
(((FStar_List.flatten decls2)), (env))
end))))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____12989, uu____12990, uu____12991, uu____12992) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid) -> begin
(

let uu____12995 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____12995) with
| (tname, ttok, env) -> begin
(([]), (env))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____13006, t, quals, uu____13009) -> begin
(

let will_encode_definition = (

let uu____13013 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___126_13015 -> (match (uu___126_13015) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Irreducible) -> begin
true
end
| uu____13018 -> begin
false
end))))
in (not (uu____13013)))
in (match (will_encode_definition) with
| true -> begin
(([]), (env))
end
| uu____13022 -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____13024 = (encode_top_level_val env fv t quals)
in (match (uu____13024) with
| (decls, env) -> begin
(

let tname = lid.FStar_Ident.str
in (

let tsym = (FStar_SMTEncoding_Util.mkFreeV ((tname), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____13036 = (

let uu____13038 = (primitive_type_axioms env.tcenv lid tname tsym)
in (FStar_List.append decls uu____13038))
in ((uu____13036), (env)))))
end)))
end))
end
| FStar_Syntax_Syntax.Sig_assume (l, f, uu____13043, uu____13044) -> begin
(

let uu____13047 = (encode_formula f env)
in (match (uu____13047) with
| (f, decls) -> begin
(

let g = (

let uu____13056 = (

let uu____13057 = (

let uu____13062 = (

let uu____13064 = (

let uu____13065 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" uu____13065))
in Some (uu____13064))
in (

let uu____13066 = (

let uu____13068 = (varops.mk_unique (Prims.strcat "assumption_" l.FStar_Ident.str))
in Some (uu____13068))
in ((f), (uu____13062), (uu____13066))))
in FStar_SMTEncoding_Term.Assume (uu____13057))
in (uu____13056)::[])
in (((FStar_List.append decls g)), (env)))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, uu____13074, quals, uu____13076) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) -> begin
(

let uu____13084 = (FStar_Util.fold_map (fun env lb -> (

let lid = (

let uu____13091 = (

let uu____13096 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____13096.FStar_Syntax_Syntax.fv_name)
in uu____13091.FStar_Syntax_Syntax.v)
in (

let uu____13100 = (

let uu____13101 = (FStar_TypeChecker_Env.try_lookup_val_decl env.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone uu____13101))
in (match (uu____13100) with
| true -> begin
(

let val_decl = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), (r)))
in (

let uu____13120 = (encode_sigelt' env val_decl)
in (match (uu____13120) with
| (decls, env) -> begin
((env), (decls))
end)))
end
| uu____13127 -> begin
((env), ([]))
end)))) env (Prims.snd lbs))
in (match (uu____13084) with
| (env, decls) -> begin
(((FStar_List.flatten decls)), (env))
end))
end
| FStar_Syntax_Syntax.Sig_let ((uu____13137, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t); FStar_Syntax_Syntax.lbunivs = uu____13139; FStar_Syntax_Syntax.lbtyp = uu____13140; FStar_Syntax_Syntax.lbeff = uu____13141; FStar_Syntax_Syntax.lbdef = uu____13142})::[]), uu____13143, uu____13144, uu____13145, uu____13146) when (FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Syntax_Const.b2t_lid) -> begin
(

let uu____13162 = (new_term_constant_and_tok_from_lid env b2t.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____13162) with
| (tname, ttok, env) -> begin
(

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let valid_b2t_x = (

let uu____13180 = (

let uu____13184 = (

let uu____13186 = (FStar_SMTEncoding_Util.mkApp (("Prims.b2t"), ((x)::[])))
in (uu____13186)::[])
in (("Valid"), (uu____13184)))
in (FStar_SMTEncoding_Util.mkApp uu____13180))
in (

let decls = (

let uu____13191 = (

let uu____13193 = (

let uu____13194 = (

let uu____13199 = (

let uu____13200 = (

let uu____13206 = (

let uu____13207 = (

let uu____13210 = (FStar_SMTEncoding_Util.mkApp (("BoxBool_proj_0"), ((x)::[])))
in ((valid_b2t_x), (uu____13210)))
in (FStar_SMTEncoding_Util.mkEq uu____13207))
in ((((valid_b2t_x)::[])::[]), ((xx)::[]), (uu____13206)))
in (FStar_SMTEncoding_Util.mkForall uu____13200))
in ((uu____13199), (Some ("b2t def")), (Some ("b2t_def"))))
in FStar_SMTEncoding_Term.Assume (uu____13194))
in (uu____13193)::[])
in (FStar_SMTEncoding_Term.DeclFun (((tname), ((FStar_SMTEncoding_Term.Term_sort)::[]), (FStar_SMTEncoding_Term.Term_sort), (None))))::uu____13191)
in ((decls), (env))))))
end))
end
| FStar_Syntax_Syntax.Sig_let (uu____13228, uu____13229, uu____13230, quals, uu____13232) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___127_13240 -> (match (uu___127_13240) with
| FStar_Syntax_Syntax.Discriminator (uu____13241) -> begin
true
end
| uu____13242 -> begin
false
end)))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let (uu____13244, uu____13245, lids, quals, uu____13248) when ((FStar_All.pipe_right lids (FStar_Util.for_some (fun l -> (

let uu____13257 = (

let uu____13258 = (FStar_List.hd l.FStar_Ident.ns)
in uu____13258.FStar_Ident.idText)
in (uu____13257 = "Prims"))))) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___128_13260 -> (match (uu___128_13260) with
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
true
end
| uu____13261 -> begin
false
end))))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____13264, uu____13265, quals, uu____13267) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___129_13279 -> (match (uu___129_13279) with
| FStar_Syntax_Syntax.Projector (uu____13280) -> begin
true
end
| uu____13283 -> begin
false
end)))) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____13290 = (try_lookup_free_var env l)
in (match (uu____13290) with
| Some (uu____13294) -> begin
(([]), (env))
end
| None -> begin
(

let se = FStar_Syntax_Syntax.Sig_declare_typ (((l), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), ((FStar_Ident.range_of_lid l))))
in (encode_sigelt env se))
end))))
end
| FStar_Syntax_Syntax.Sig_let ((uu____13301, (lb)::[]), uu____13303, uu____13304, quals, uu____13306) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) -> begin
(

let uu____13318 = (

let uu____13319 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef)
in uu____13319.FStar_Syntax_Syntax.n)
in (match (uu____13318) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____13326) -> begin
(

let body = (FStar_Syntax_Util.mk_reify body)
in (

let tm = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None))))) None lb.FStar_Syntax_Syntax.lbdef.FStar_Syntax_Syntax.pos)
in (

let tm' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env.tcenv tm)
in (

let lb_typ = (

let uu____13383 = (FStar_Syntax_Util.arrow_formals_comp lb.FStar_Syntax_Syntax.lbtyp)
in (match (uu____13383) with
| (formals, comp) -> begin
(

let reified_typ = (FStar_TypeChecker_Util.reify_comp (

let uu___155_13400 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___155_13400.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___155_13400.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___155_13400.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___155_13400.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___155_13400.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___155_13400.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___155_13400.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___155_13400.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___155_13400.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___155_13400.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___155_13400.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___155_13400.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___155_13400.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___155_13400.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___155_13400.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___155_13400.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___155_13400.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___155_13400.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___155_13400.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___155_13400.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___155_13400.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___155_13400.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___155_13400.FStar_TypeChecker_Env.qname_and_index}) (FStar_Syntax_Util.lcomp_of_comp comp) FStar_Syntax_Syntax.U_unknown)
in (

let uu____13401 = (FStar_Syntax_Syntax.mk_Total reified_typ)
in (FStar_Syntax_Util.arrow formals uu____13401)))
end))
in (

let lb = (

let uu___156_13405 = lb
in {FStar_Syntax_Syntax.lbname = uu___156_13405.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___156_13405.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lb_typ; FStar_Syntax_Syntax.lbeff = uu___156_13405.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = tm'})
in ((

let uu____13407 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____13407) with
| true -> begin
(

let uu____13408 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____13409 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____13410 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print3 "%s: Reified %s\nto %s\n" uu____13408 uu____13409 uu____13410))))
end
| uu____13411 -> begin
()
end));
(encode_top_level_let env ((false), ((lb)::[])) quals);
))))))
end
| uu____13413 -> begin
(([]), (env))
end))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), uu____13417, uu____13418, quals, uu____13420) -> begin
(encode_top_level_let env ((is_rec), (bindings)) quals)
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____13434, uu____13435, uu____13436) -> begin
(

let uu____13443 = (encode_signature env ses)
in (match (uu____13443) with
| (g, env) -> begin
(

let uu____13453 = (FStar_All.pipe_right g (FStar_List.partition (fun uu___130_13463 -> (match (uu___130_13463) with
| FStar_SMTEncoding_Term.Assume (uu____13464, Some ("inversion axiom"), uu____13465) -> begin
false
end
| uu____13469 -> begin
true
end))))
in (match (uu____13453) with
| (g', inversions) -> begin
(

let uu____13478 = (FStar_All.pipe_right g' (FStar_List.partition (fun uu___131_13488 -> (match (uu___131_13488) with
| FStar_SMTEncoding_Term.DeclFun (uu____13489) -> begin
true
end
| uu____13495 -> begin
false
end))))
in (match (uu____13478) with
| (decls, rest) -> begin
(((FStar_List.append decls (FStar_List.append rest inversions))), (env))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, uu____13506, tps, k, uu____13509, datas, quals, uu____13512) -> begin
(

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___132_13521 -> (match (uu___132_13521) with
| (FStar_Syntax_Syntax.Logic) | (FStar_Syntax_Syntax.Assumption) -> begin
true
end
| uu____13522 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> (match (is_logical) with
| true -> begin
(

let uu____13545 = c
in (match (uu____13545) with
| (name, args, uu____13557, uu____13558, uu____13559) -> begin
(

let uu____13566 = (

let uu____13567 = (

let uu____13573 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in ((name), (uu____13573), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (uu____13567))
in (uu____13566)::[])
end))
end
| uu____13583 -> begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end))
in (

let inversion_axioms = (fun tapp vars -> (

let uu____13598 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (

let uu____13601 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right uu____13601 FStar_Option.isNone)))))
in (match (uu____13598) with
| true -> begin
[]
end
| uu____13611 -> begin
(

let uu____13612 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____13612) with
| (xxsym, xx) -> begin
(

let uu____13618 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun uu____13629 l -> (match (uu____13629) with
| (out, decls) -> begin
(

let uu____13641 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (uu____13641) with
| (uu____13647, data_t) -> begin
(

let uu____13649 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (uu____13649) with
| (args, res) -> begin
(

let indices = (

let uu____13678 = (

let uu____13679 = (FStar_Syntax_Subst.compress res)
in uu____13679.FStar_Syntax_Syntax.n)
in (match (uu____13678) with
| FStar_Syntax_Syntax.Tm_app (uu____13687, indices) -> begin
indices
end
| uu____13703 -> begin
[]
end))
in (

let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env uu____13715 -> (match (uu____13715) with
| (x, uu____13719) -> begin
(

let uu____13720 = (

let uu____13721 = (

let uu____13725 = (mk_term_projector_name l x)
in ((uu____13725), ((xx)::[])))
in (FStar_SMTEncoding_Util.mkApp uu____13721))
in (push_term_var env x uu____13720))
end)) env))
in (

let uu____13727 = (encode_args indices env)
in (match (uu____13727) with
| (indices, decls') -> begin
((match (((FStar_List.length indices) <> (FStar_List.length vars))) with
| true -> begin
(failwith "Impossible")
end
| uu____13745 -> begin
()
end);
(

let eqs = (

let uu____13747 = (FStar_List.map2 (fun v a -> (

let uu____13755 = (

let uu____13758 = (FStar_SMTEncoding_Util.mkFreeV v)
in ((uu____13758), (a)))
in (FStar_SMTEncoding_Util.mkEq uu____13755))) vars indices)
in (FStar_All.pipe_right uu____13747 FStar_SMTEncoding_Util.mk_and_l))
in (

let uu____13760 = (

let uu____13761 = (

let uu____13764 = (

let uu____13765 = (

let uu____13768 = (mk_data_tester env l xx)
in ((uu____13768), (eqs)))
in (FStar_SMTEncoding_Util.mkAnd uu____13765))
in ((out), (uu____13764)))
in (FStar_SMTEncoding_Util.mkOr uu____13761))
in ((uu____13760), ((FStar_List.append decls decls')))));
)
end))))
end))
end))
end)) ((FStar_SMTEncoding_Util.mkFalse), ([]))))
in (match (uu____13618) with
| (data_ax, decls) -> begin
(

let uu____13776 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____13776) with
| (ffsym, ff) -> begin
(

let fuel_guarded_inversion = (

let xx_has_type_sfuel = (match (((FStar_List.length datas) > (Prims.parse_int "1"))) with
| true -> begin
(

let uu____13787 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((ff)::[])))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel uu____13787 xx tapp))
end
| uu____13789 -> begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end)
in (

let uu____13790 = (

let uu____13795 = (

let uu____13796 = (

let uu____13802 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (

let uu____13810 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_sfuel), (data_ax)))
in ((((xx_has_type_sfuel)::[])::[]), (uu____13802), (uu____13810))))
in (FStar_SMTEncoding_Util.mkForall uu____13796))
in (

let uu____13818 = (

let uu____13820 = (varops.mk_unique (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str))
in Some (uu____13820))
in ((uu____13795), (Some ("inversion axiom")), (uu____13818))))
in FStar_SMTEncoding_Term.Assume (uu____13790)))
in (

let pattern_guarded_inversion = (

let uu____13825 = ((contains_name env "Prims.inversion") && ((FStar_List.length datas) > (Prims.parse_int "1")))
in (match (uu____13825) with
| true -> begin
(

let xx_has_type_fuel = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let pattern_guard = (FStar_SMTEncoding_Util.mkApp (("Prims.inversion"), ((tapp)::[])))
in (

let uu____13833 = (

let uu____13834 = (

let uu____13839 = (

let uu____13840 = (

let uu____13846 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (

let uu____13854 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_fuel), (data_ax)))
in ((((xx_has_type_fuel)::(pattern_guard)::[])::[]), (uu____13846), (uu____13854))))
in (FStar_SMTEncoding_Util.mkForall uu____13840))
in (

let uu____13862 = (

let uu____13864 = (varops.mk_unique (Prims.strcat "pattern_guarded_inversion_" t.FStar_Ident.str))
in Some (uu____13864))
in ((uu____13839), (Some ("inversion axiom")), (uu____13862))))
in FStar_SMTEncoding_Term.Assume (uu____13834))
in (uu____13833)::[])))
end
| uu____13867 -> begin
[]
end))
in (FStar_List.append decls (FStar_List.append ((fuel_guarded_inversion)::[]) pattern_guarded_inversion))))
end))
end))
end))
end)))
in (

let uu____13868 = (

let uu____13876 = (

let uu____13877 = (FStar_Syntax_Subst.compress k)
in uu____13877.FStar_Syntax_Syntax.n)
in (match (uu____13876) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
(((FStar_List.append tps formals)), ((FStar_Syntax_Util.comp_result kres)))
end
| uu____13906 -> begin
((tps), (k))
end))
in (match (uu____13868) with
| (formals, res) -> begin
(

let uu____13921 = (FStar_Syntax_Subst.open_term formals res)
in (match (uu____13921) with
| (formals, res) -> begin
(

let uu____13928 = (encode_binders None formals env)
in (match (uu____13928) with
| (vars, guards, env', binder_decls, uu____13943) -> begin
(

let uu____13950 = (new_term_constant_and_tok_from_lid env t)
in (match (uu____13950) with
| (tname, ttok, env) -> begin
(

let ttok_tm = (FStar_SMTEncoding_Util.mkApp ((ttok), ([])))
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let tapp = (

let uu____13963 = (

let uu____13967 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((tname), (uu____13967)))
in (FStar_SMTEncoding_Util.mkApp uu____13963))
in (

let uu____13972 = (

let tname_decl = (

let uu____13978 = (

let uu____13987 = (FStar_All.pipe_right vars (FStar_List.map (fun uu____13999 -> (match (uu____13999) with
| (n, s) -> begin
(((Prims.strcat tname n)), (s))
end))))
in (

let uu____14006 = (varops.next_id ())
in ((tname), (uu____13987), (FStar_SMTEncoding_Term.Term_sort), (uu____14006), (false))))
in (constructor_or_logic_type_decl uu____13978))
in (

let uu____14010 = (match (vars) with
| [] -> begin
(

let uu____14017 = (

let uu____14018 = (

let uu____14020 = (FStar_SMTEncoding_Util.mkApp ((tname), ([])))
in (FStar_All.pipe_left (fun _0_38 -> Some (_0_38)) uu____14020))
in (push_free_var env t tname uu____14018))
in (([]), (uu____14017)))
end
| uu____14024 -> begin
(

let ttok_decl = FStar_SMTEncoding_Term.DeclFun (((ttok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("token"))))
in (

let ttok_fresh = (

let uu____14030 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ttok), (FStar_SMTEncoding_Term.Term_sort)) uu____14030))
in (

let ttok_app = (mk_Apply ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (

let uu____14039 = (

let uu____14044 = (

let uu____14045 = (

let uu____14053 = (FStar_SMTEncoding_Util.mkEq ((ttok_app), (tapp)))
in ((pats), (None), (vars), (uu____14053)))
in (FStar_SMTEncoding_Util.mkForall' uu____14045))
in ((uu____14044), (Some ("name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" ttok)))))
in FStar_SMTEncoding_Term.Assume (uu____14039))
in (((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[]), (env)))))))
end)
in (match (uu____14010) with
| (tok_decls, env) -> begin
(((FStar_List.append tname_decl tok_decls)), (env))
end)))
in (match (uu____13972) with
| (decls, env) -> begin
(

let kindingAx = (

let uu____14077 = (encode_term_pred None res env' tapp)
in (match (uu____14077) with
| (k, decls) -> begin
(

let karr = (match (((FStar_List.length formals) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____14091 = (

let uu____14092 = (

let uu____14097 = (

let uu____14098 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____14098))
in ((uu____14097), (Some ("kinding")), (Some ((Prims.strcat "pre_kinding_" ttok)))))
in FStar_SMTEncoding_Term.Assume (uu____14092))
in (uu____14091)::[])
end
| uu____14101 -> begin
[]
end)
in (

let uu____14102 = (

let uu____14104 = (

let uu____14106 = (

let uu____14107 = (

let uu____14112 = (

let uu____14113 = (

let uu____14119 = (FStar_SMTEncoding_Util.mkImp ((guard), (k)))
in ((((tapp)::[])::[]), (vars), (uu____14119)))
in (FStar_SMTEncoding_Util.mkForall uu____14113))
in ((uu____14112), (None), (Some ((Prims.strcat "kinding_" ttok)))))
in FStar_SMTEncoding_Term.Assume (uu____14107))
in (uu____14106)::[])
in (FStar_List.append karr uu____14104))
in (FStar_List.append decls uu____14102)))
end))
in (

let aux = (

let uu____14129 = (

let uu____14131 = (inversion_axioms tapp vars)
in (

let uu____14133 = (

let uu____14135 = (pretype_axiom tapp vars)
in (uu____14135)::[])
in (FStar_List.append uu____14131 uu____14133)))
in (FStar_List.append kindingAx uu____14129))
in (

let g = (FStar_List.append decls (FStar_List.append binder_decls aux))
in ((g), (env)))))
end)))))
end))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____14140, uu____14141, uu____14142, uu____14143, uu____14144, uu____14145, uu____14146) when (FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____14153, t, uu____14155, n_tps, quals, uu____14158, drange) -> begin
(

let uu____14164 = (new_term_constant_and_tok_from_lid env d)
in (match (uu____14164) with
| (ddconstrsym, ddtok, env) -> begin
(

let ddtok_tm = (FStar_SMTEncoding_Util.mkApp ((ddtok), ([])))
in (

let uu____14175 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____14175) with
| (formals, t_res) -> begin
(

let uu____14197 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____14197) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (

let uu____14206 = (encode_binders (Some (fuel_tm)) formals env)
in (match (uu____14206) with
| (vars, guards, env', binder_decls, names) -> begin
(

let projectors = (FStar_All.pipe_right names (FStar_List.map (fun x -> (

let uu____14239 = (mk_term_projector_name d x)
in ((uu____14239), (FStar_SMTEncoding_Term.Term_sort))))))
in (

let datacons = (

let uu____14241 = (

let uu____14250 = (varops.next_id ())
in ((ddconstrsym), (projectors), (FStar_SMTEncoding_Term.Term_sort), (uu____14250), (true)))
in (FStar_All.pipe_right uu____14241 FStar_SMTEncoding_Term.constructor_to_decl))
in (

let app = (mk_Apply ddtok_tm vars)
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (

let uu____14270 = (encode_term_pred None t env ddtok_tm)
in (match (uu____14270) with
| (tok_typing, decls3) -> begin
(

let uu____14277 = (encode_binders (Some (fuel_tm)) formals env)
in (match (uu____14277) with
| (vars', guards', env'', decls_formals, uu____14292) -> begin
(

let uu____14299 = (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars')
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (encode_term_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (uu____14299) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_SMTEncoding_Util.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| uu____14318 -> begin
(

let uu____14322 = (

let uu____14323 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ddtok), (FStar_SMTEncoding_Term.Term_sort)) uu____14323))
in (uu____14322)::[])
end)
in (

let encode_elim = (fun uu____14330 -> (

let uu____14331 = (FStar_Syntax_Util.head_and_args t_res)
in (match (uu____14331) with
| (head, args) -> begin
(

let uu____14360 = (

let uu____14361 = (FStar_Syntax_Subst.compress head)
in uu____14361.FStar_Syntax_Syntax.n)
in (match (uu____14360) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let uu____14379 = (encode_args args env')
in (match (uu____14379) with
| (encoded_args, arg_decls) -> begin
(

let uu____14390 = (FStar_List.fold_left (fun uu____14401 arg -> (match (uu____14401) with
| (env, arg_vars, eqns) -> begin
(

let uu____14420 = (

let uu____14424 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in (gen_term_var env uu____14424))
in (match (uu____14420) with
| (uu____14430, xv, env) -> begin
(

let uu____14433 = (

let uu____14435 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (uu____14435)::eqns)
in ((env), ((xv)::arg_vars), (uu____14433)))
end))
end)) ((env'), ([]), ([])) encoded_args)
in (match (uu____14390) with
| (uu____14443, arg_vars, eqns) -> begin
(

let arg_vars = (FStar_List.rev arg_vars)
in (

let ty = (FStar_SMTEncoding_Util.mkApp ((encoded_head), (arg_vars)))
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (

let ty_pred = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp ty)
in (

let arg_binders = (FStar_List.map FStar_SMTEncoding_Term.fv_of_term arg_vars)
in (

let typing_inversion = (

let uu____14464 = (

let uu____14469 = (

let uu____14470 = (

let uu____14476 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____14482 = (

let uu____14483 = (

let uu____14486 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append eqns guards))
in ((ty_pred), (uu____14486)))
in (FStar_SMTEncoding_Util.mkImp uu____14483))
in ((((ty_pred)::[])::[]), (uu____14476), (uu____14482))))
in (FStar_SMTEncoding_Util.mkForall uu____14470))
in ((uu____14469), (Some ("data constructor typing elim")), (Some ((Prims.strcat "data_elim_" ddconstrsym)))))
in FStar_SMTEncoding_Term.Assume (uu____14464))
in (

let subterm_ordering = (match ((FStar_Ident.lid_equals d FStar_Syntax_Const.lextop_lid)) with
| true -> begin
(

let x = (

let uu____14500 = (varops.fresh "x")
in ((uu____14500), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (

let uu____14502 = (

let uu____14507 = (

let uu____14508 = (

let uu____14514 = (

let uu____14517 = (

let uu____14519 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp)
in (uu____14519)::[])
in (uu____14517)::[])
in (

let uu____14522 = (

let uu____14523 = (

let uu____14526 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (

let uu____14527 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp)
in ((uu____14526), (uu____14527))))
in (FStar_SMTEncoding_Util.mkImp uu____14523))
in ((uu____14514), ((x)::[]), (uu____14522))))
in (FStar_SMTEncoding_Util.mkForall uu____14508))
in (

let uu____14537 = (

let uu____14539 = (varops.mk_unique "lextop")
in Some (uu____14539))
in ((uu____14507), (Some ("lextop is top")), (uu____14537))))
in FStar_SMTEncoding_Term.Assume (uu____14502))))
end
| uu____14542 -> begin
(

let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
[]
end
| FStar_SMTEncoding_Term.Term_sort -> begin
(

let uu____14553 = (

let uu____14554 = (FStar_SMTEncoding_Util.mkFreeV v)
in (FStar_SMTEncoding_Util.mk_Precedes uu____14554 dapp))
in (uu____14553)::[])
end
| uu____14555 -> begin
(failwith "unexpected sort")
end))))
in (

let uu____14557 = (

let uu____14562 = (

let uu____14563 = (

let uu____14569 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____14575 = (

let uu____14576 = (

let uu____14579 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (uu____14579)))
in (FStar_SMTEncoding_Util.mkImp uu____14576))
in ((((ty_pred)::[])::[]), (uu____14569), (uu____14575))))
in (FStar_SMTEncoding_Util.mkForall uu____14563))
in ((uu____14562), (Some ("subterm ordering")), (Some ((Prims.strcat "subterm_ordering_" ddconstrsym)))))
in FStar_SMTEncoding_Term.Assume (uu____14557)))
end)
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end))
end)))
end
| uu____14590 -> begin
((

let uu____14592 = (

let uu____14593 = (FStar_Syntax_Print.lid_to_string d)
in (

let uu____14594 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" uu____14593 uu____14594)))
in (FStar_Errors.warn drange uu____14592));
(([]), ([]));
)
end))
end)))
in (

let uu____14597 = (encode_elim ())
in (match (uu____14597) with
| (decls2, elim) -> begin
(

let g = (

let uu____14609 = (

let uu____14611 = (

let uu____14613 = (

let uu____14615 = (

let uu____14617 = (

let uu____14618 = (

let uu____14624 = (

let uu____14626 = (

let uu____14627 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" uu____14627))
in Some (uu____14626))
in ((ddtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (uu____14624)))
in FStar_SMTEncoding_Term.DeclFun (uu____14618))
in (uu____14617)::[])
in (

let uu____14630 = (

let uu____14632 = (

let uu____14634 = (

let uu____14636 = (

let uu____14638 = (

let uu____14640 = (

let uu____14642 = (

let uu____14643 = (

let uu____14648 = (

let uu____14649 = (

let uu____14655 = (FStar_SMTEncoding_Util.mkEq ((app), (dapp)))
in ((((app)::[])::[]), (vars), (uu____14655)))
in (FStar_SMTEncoding_Util.mkForall uu____14649))
in ((uu____14648), (Some ("equality for proxy")), (Some ((Prims.strcat "equality_tok_" ddtok)))))
in FStar_SMTEncoding_Term.Assume (uu____14643))
in (

let uu____14663 = (

let uu____14665 = (

let uu____14666 = (

let uu____14671 = (

let uu____14672 = (

let uu____14678 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) vars')
in (

let uu____14684 = (FStar_SMTEncoding_Util.mkImp ((guard'), (ty_pred')))
in ((((ty_pred')::[])::[]), (uu____14678), (uu____14684))))
in (FStar_SMTEncoding_Util.mkForall uu____14672))
in ((uu____14671), (Some ("data constructor typing intro")), (Some ((Prims.strcat "data_typing_intro_" ddtok)))))
in FStar_SMTEncoding_Term.Assume (uu____14666))
in (uu____14665)::[])
in (uu____14642)::uu____14663))
in (FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("typing for data constructor proxy")), (Some ((Prims.strcat "typing_tok_" ddtok))))))::uu____14640)
in (FStar_List.append uu____14638 elim))
in (FStar_List.append decls_pred uu____14636))
in (FStar_List.append decls_formals uu____14634))
in (FStar_List.append proxy_fresh uu____14632))
in (FStar_List.append uu____14615 uu____14630)))
in (FStar_List.append decls3 uu____14613))
in (FStar_List.append decls2 uu____14611))
in (FStar_List.append binder_decls uu____14609))
in (((FStar_List.append datacons g)), (env)))
end)))))
end))
end))
end))))))))
end)))
end))
end)))
end))
end))
and encode_signature : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun uu____14707 se -> (match (uu____14707) with
| (g, env) -> begin
(

let uu____14719 = (encode_sigelt env se)
in (match (uu____14719) with
| (g', env) -> begin
(((FStar_List.append g g')), (env))
end))
end)) (([]), (env)))))


let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env bindings -> (

let encode_binding = (fun b uu____14755 -> (match (uu____14755) with
| (i, decls, env) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (uu____14773) -> begin
(((i + (Prims.parse_int "1"))), ([]), (env))
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in ((

let uu____14778 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____14778) with
| true -> begin
(

let uu____14779 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____14780 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____14781 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" uu____14779 uu____14780 uu____14781))))
end
| uu____14782 -> begin
()
end));
(

let uu____14783 = (encode_term t1 env)
in (match (uu____14783) with
| (t, decls') -> begin
(

let t_hash = (FStar_SMTEncoding_Term.hash_of_term t)
in (

let uu____14793 = (

let uu____14797 = (

let uu____14798 = (

let uu____14799 = (FStar_Util.digest_of_string t_hash)
in (

let uu____14800 = (

let uu____14801 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" uu____14801))
in (Prims.strcat uu____14799 uu____14800)))
in (Prims.strcat "x_" uu____14798))
in (new_term_constant_from_string env x uu____14797))
in (match (uu____14793) with
| (xxsym, xx, env') -> begin
(

let t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel None xx t)
in (

let caption = (

let uu____14812 = (FStar_Options.log_queries ())
in (match (uu____14812) with
| true -> begin
(

let uu____14814 = (

let uu____14815 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____14816 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____14817 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" uu____14815 uu____14816 uu____14817))))
in Some (uu____14814))
end
| uu____14818 -> begin
None
end))
in (

let ax = (

let a_name = Some ((Prims.strcat "binder_" xxsym))
in FStar_SMTEncoding_Term.Assume (((t), (a_name), (a_name))))
in (

let g = (FStar_List.append ((FStar_SMTEncoding_Term.DeclFun (((xxsym), ([]), (FStar_SMTEncoding_Term.Term_sort), (caption))))::[]) (FStar_List.append decls' ((ax)::[])))
in (((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))))))
end)))
end));
))
end
| FStar_TypeChecker_Env.Binding_lid (x, (uu____14830, t)) -> begin
(

let t_norm = (whnf env t)
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____14839 = (encode_free_var env fv t t_norm [])
in (match (uu____14839) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))))
end
| (FStar_TypeChecker_Env.Binding_sig_inst (_, se, _)) | (FStar_TypeChecker_Env.Binding_sig (_, se)) -> begin
(

let uu____14858 = (encode_sigelt env se)
in (match (uu____14858) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))
end)
end))
in (

let uu____14868 = (FStar_List.fold_right encode_binding bindings (((Prims.parse_int "0")), ([]), (env)))
in (match (uu____14868) with
| (uu____14880, decls, env) -> begin
((decls), (env))
end))))


let encode_labels = (fun labs -> (

let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun uu____14925 -> (match (uu____14925) with
| (l, uu____14932, uu____14933) -> begin
FStar_SMTEncoding_Term.DeclFun ((((Prims.fst l)), ([]), (FStar_SMTEncoding_Term.Bool_sort), (None)))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun uu____14954 -> (match (uu____14954) with
| (l, uu____14962, uu____14963) -> begin
(

let uu____14968 = (FStar_All.pipe_left (fun _0_39 -> FStar_SMTEncoding_Term.Echo (_0_39)) (Prims.fst l))
in (

let uu____14969 = (

let uu____14971 = (

let uu____14972 = (FStar_SMTEncoding_Util.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (uu____14972))
in (uu____14971)::[])
in (uu____14968)::uu____14969))
end))))
in ((prefix), (suffix)))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (

let uu____14983 = (

let uu____14985 = (

let uu____14986 = (FStar_Util.smap_create (Prims.parse_int "100"))
in {bindings = []; depth = (Prims.parse_int "0"); tcenv = tcenv; warn = true; cache = uu____14986; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (uu____14985)::[])
in (FStar_ST.write last_env uu____14983)))


let get_env : FStar_TypeChecker_Env.env  ->  env_t = (fun tcenv -> (

let uu____15004 = (FStar_ST.read last_env)
in (match (uu____15004) with
| [] -> begin
(failwith "No env; call init first!")
end
| (e)::uu____15010 -> begin
(

let uu___157_15012 = e
in {bindings = uu___157_15012.bindings; depth = uu___157_15012.depth; tcenv = tcenv; warn = uu___157_15012.warn; cache = uu___157_15012.cache; nolabels = uu___157_15012.nolabels; use_zfuel_name = uu___157_15012.use_zfuel_name; encode_non_total_function_typ = uu___157_15012.encode_non_total_function_typ})
end)))


let set_env : env_t  ->  Prims.unit = (fun env -> (

let uu____15016 = (FStar_ST.read last_env)
in (match (uu____15016) with
| [] -> begin
(failwith "Empty env stack")
end
| (uu____15021)::tl -> begin
(FStar_ST.write last_env ((env)::tl))
end)))


let push_env : Prims.unit  ->  Prims.unit = (fun uu____15029 -> (

let uu____15030 = (FStar_ST.read last_env)
in (match (uu____15030) with
| [] -> begin
(failwith "Empty env stack")
end
| (hd)::tl -> begin
(

let refs = (FStar_Util.smap_copy hd.cache)
in (

let top = (

let uu___158_15051 = hd
in {bindings = uu___158_15051.bindings; depth = uu___158_15051.depth; tcenv = uu___158_15051.tcenv; warn = uu___158_15051.warn; cache = refs; nolabels = uu___158_15051.nolabels; use_zfuel_name = uu___158_15051.use_zfuel_name; encode_non_total_function_typ = uu___158_15051.encode_non_total_function_typ})
in (FStar_ST.write last_env ((top)::(hd)::tl))))
end)))


let pop_env : Prims.unit  ->  Prims.unit = (fun uu____15057 -> (

let uu____15058 = (FStar_ST.read last_env)
in (match (uu____15058) with
| [] -> begin
(failwith "Popping an empty stack")
end
| (uu____15063)::tl -> begin
(FStar_ST.write last_env tl)
end)))


let mark_env : Prims.unit  ->  Prims.unit = (fun uu____15071 -> (push_env ()))


let reset_mark_env : Prims.unit  ->  Prims.unit = (fun uu____15074 -> (pop_env ()))


let commit_mark_env : Prims.unit  ->  Prims.unit = (fun uu____15077 -> (

let uu____15078 = (FStar_ST.read last_env)
in (match (uu____15078) with
| (hd)::(uu____15084)::tl -> begin
(FStar_ST.write last_env ((hd)::tl))
end
| uu____15090 -> begin
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

let uu____15135 = (FStar_Options.log_queries ())
in (match (uu____15135) with
| true -> begin
(

let uu____15137 = (

let uu____15138 = (

let uu____15139 = (

let uu____15140 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.map FStar_Syntax_Print.lid_to_string))
in (FStar_All.pipe_right uu____15140 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " uu____15139))
in FStar_SMTEncoding_Term.Caption (uu____15138))
in (uu____15137)::decls)
end
| uu____15145 -> begin
decls
end)))
in (

let env = (get_env tcenv)
in (

let uu____15147 = (encode_sigelt env se)
in (match (uu____15147) with
| (decls, env) -> begin
((set_env env);
(

let uu____15153 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 uu____15153));
)
end)))))


let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____15162 -> begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in ((

let uu____15164 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____15164) with
| true -> begin
(

let uu____15165 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name uu____15165))
end
| uu____15168 -> begin
()
end));
(

let env = (get_env tcenv)
in (

let uu____15170 = (encode_signature (

let uu___159_15174 = env
in {bindings = uu___159_15174.bindings; depth = uu___159_15174.depth; tcenv = uu___159_15174.tcenv; warn = false; cache = uu___159_15174.cache; nolabels = uu___159_15174.nolabels; use_zfuel_name = uu___159_15174.use_zfuel_name; encode_non_total_function_typ = uu___159_15174.encode_non_total_function_typ}) modul.FStar_Syntax_Syntax.exports)
in (match (uu____15170) with
| (decls, env) -> begin
(

let caption = (fun decls -> (

let uu____15186 = (FStar_Options.log_queries ())
in (match (uu____15186) with
| true -> begin
(

let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::decls) ((FStar_SMTEncoding_Term.Caption ((Prims.strcat "End " msg)))::[])))
end
| uu____15189 -> begin
decls
end)))
in ((set_env (

let uu___160_15191 = env
in {bindings = uu___160_15191.bindings; depth = uu___160_15191.depth; tcenv = uu___160_15191.tcenv; warn = true; cache = uu___160_15191.cache; nolabels = uu___160_15191.nolabels; use_zfuel_name = uu___160_15191.use_zfuel_name; encode_non_total_function_typ = uu___160_15191.encode_non_total_function_typ}));
(

let uu____15193 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____15193) with
| true -> begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end
| uu____15194 -> begin
()
end));
(

let decls = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls));
))
end)));
)))


let encode_query : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_ErrorReporting.label Prims.list * FStar_SMTEncoding_Term.decl * FStar_SMTEncoding_Term.decl Prims.list) = (fun use_env_msg tcenv q -> ((

let uu____15228 = (

let uu____15229 = (FStar_TypeChecker_Env.current_module tcenv)
in uu____15229.FStar_Ident.str)
in (FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name uu____15228));
(

let env = (get_env tcenv)
in (

let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (

let uu____15237 = (

let rec aux = (fun bindings -> (match (bindings) with
| (FStar_TypeChecker_Env.Binding_var (x))::rest -> begin
(

let uu____15258 = (aux rest)
in (match (uu____15258) with
| (out, rest) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (

let uu____15274 = (

let uu____15276 = (FStar_Syntax_Syntax.mk_binder (

let uu___161_15277 = x
in {FStar_Syntax_Syntax.ppname = uu___161_15277.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___161_15277.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (uu____15276)::out)
in ((uu____15274), (rest))))
end))
end
| uu____15280 -> begin
(([]), (bindings))
end))
in (

let uu____15284 = (aux bindings)
in (match (uu____15284) with
| (closing, bindings) -> begin
(

let uu____15298 = (FStar_Syntax_Util.close_forall (FStar_List.rev closing) q)
in ((uu____15298), (bindings)))
end)))
in (match (uu____15237) with
| (q, bindings) -> begin
(

let uu____15311 = (

let uu____15314 = (FStar_List.filter (fun uu___133_15316 -> (match (uu___133_15316) with
| FStar_TypeChecker_Env.Binding_sig (uu____15317) -> begin
false
end
| uu____15321 -> begin
true
end)) bindings)
in (encode_env_bindings env uu____15314))
in (match (uu____15311) with
| (env_decls, env) -> begin
((

let uu____15332 = (((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTQuery"))))
in (match (uu____15332) with
| true -> begin
(

let uu____15333 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" uu____15333))
end
| uu____15334 -> begin
()
end));
(

let uu____15335 = (encode_formula q env)
in (match (uu____15335) with
| (phi, qdecls) -> begin
(

let uu____15347 = (

let uu____15350 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg uu____15350 phi))
in (match (uu____15347) with
| (labels, phi) -> begin
(

let uu____15360 = (encode_labels labels)
in (match (uu____15360) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append env_decls (FStar_List.append label_prefix qdecls))
in (

let qry = (

let uu____15381 = (

let uu____15386 = (FStar_SMTEncoding_Util.mkNot phi)
in (

let uu____15387 = (

let uu____15389 = (varops.mk_unique "@query")
in Some (uu____15389))
in ((uu____15386), (Some ("query")), (uu____15387))))
in FStar_SMTEncoding_Term.Assume (uu____15381))
in (

let suffix = (

let uu____15394 = (

let uu____15396 = (

let uu____15398 = (FStar_Options.print_z3_statistics ())
in (match (uu____15398) with
| true -> begin
(FStar_SMTEncoding_Term.PrintStats)::[]
end
| uu____15400 -> begin
[]
end))
in (FStar_List.append uu____15396 ((FStar_SMTEncoding_Term.Echo ("Done!"))::[])))
in (FStar_List.append label_suffix uu____15394))
in ((query_prelude), (labels), (qry), (suffix)))))
end))
end))
end));
)
end))
end))));
))


let is_trivial : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun tcenv q -> (

let env = (get_env tcenv)
in ((FStar_SMTEncoding_Z3.push "query");
(

let uu____15411 = (encode_formula q env)
in (match (uu____15411) with
| (f, uu____15415) -> begin
((FStar_SMTEncoding_Z3.pop "query");
(match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____15417) -> begin
true
end
| uu____15420 -> begin
false
end);
)
end));
)))




