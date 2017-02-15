
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

let a2 = (unmangle a)
in (

let uu____1092 = (aux a2)
in (match (uu____1092) with
| None -> begin
(

let uu____1098 = (

let uu____1099 = (FStar_Syntax_Print.bv_to_string a2)
in (

let uu____1100 = (print_env env)
in (FStar_Util.format2 "Bound term variable not found (after unmangling): %s in environment: %s" uu____1099 uu____1100)))
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

let uu____1120 = (

let uu___140_1121 = env
in (

let uu____1122 = (

let uu____1124 = (

let uu____1125 = (

let uu____1132 = (

let uu____1134 = (FStar_SMTEncoding_Util.mkApp ((ftok), ([])))
in (FStar_All.pipe_left (fun _0_29 -> Some (_0_29)) uu____1134))
in ((x), (fname), (uu____1132), (None)))
in Binding_fvar (uu____1125))
in (uu____1124)::env.bindings)
in {bindings = uu____1122; depth = uu___140_1121.depth; tcenv = uu___140_1121.tcenv; warn = uu___140_1121.warn; cache = uu___140_1121.cache; nolabels = uu___140_1121.nolabels; use_zfuel_name = uu___140_1121.use_zfuel_name; encode_non_total_function_typ = uu___140_1121.encode_non_total_function_typ}))
in ((fname), (ftok), (uu____1120))))))


let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun uu___112_1156 -> (match (uu___112_1156) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some (((t1), (t2), (t3)))
end
| uu____1178 -> begin
None
end))))


let contains_name : env_t  ->  Prims.string  ->  Prims.bool = (fun env s -> (

let uu____1190 = (lookup_binding env (fun uu___113_1192 -> (match (uu___113_1192) with
| Binding_fvar (b, t1, t2, t3) when (b.FStar_Ident.str = s) -> begin
Some (())
end
| uu____1202 -> begin
None
end)))
in (FStar_All.pipe_right uu____1190 FStar_Option.isSome)))


let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun env a -> (

let uu____1215 = (try_lookup_lid env a)
in (match (uu____1215) with
| None -> begin
(

let uu____1232 = (

let uu____1233 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" uu____1233))
in (failwith uu____1232))
end
| Some (s) -> begin
s
end)))


let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (

let uu___141_1264 = env
in {bindings = (Binding_fvar (((x), (fname), (ftok), (None))))::env.bindings; depth = uu___141_1264.depth; tcenv = uu___141_1264.tcenv; warn = uu___141_1264.warn; cache = uu___141_1264.cache; nolabels = uu___141_1264.nolabels; use_zfuel_name = uu___141_1264.use_zfuel_name; encode_non_total_function_typ = uu___141_1264.encode_non_total_function_typ}))


let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (

let uu____1276 = (lookup_lid env x)
in (match (uu____1276) with
| (t1, t2, uu____1284) -> begin
(

let t3 = (

let uu____1290 = (

let uu____1294 = (

let uu____1296 = (FStar_SMTEncoding_Util.mkApp (("ZFuel"), ([])))
in (uu____1296)::[])
in ((f), (uu____1294)))
in (FStar_SMTEncoding_Util.mkApp uu____1290))
in (

let uu___142_1299 = env
in {bindings = (Binding_fvar (((x), (t1), (t2), (Some (t3)))))::env.bindings; depth = uu___142_1299.depth; tcenv = uu___142_1299.tcenv; warn = uu___142_1299.warn; cache = uu___142_1299.cache; nolabels = uu___142_1299.nolabels; use_zfuel_name = uu___142_1299.use_zfuel_name; encode_non_total_function_typ = uu___142_1299.encode_non_total_function_typ}))
end)))


let try_lookup_free_var : env_t  ->  FStar_Ident.lident  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env l -> (

let uu____1309 = (try_lookup_lid env l)
in (match (uu____1309) with
| None -> begin
None
end
| Some (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some (f) when env.use_zfuel_name -> begin
Some (f)
end
| uu____1336 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (uu____1341, (fuel)::[]) -> begin
(

let uu____1344 = (

let uu____1345 = (

let uu____1346 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right uu____1346 Prims.fst))
in (FStar_Util.starts_with uu____1345 "fuel"))
in (match (uu____1344) with
| true -> begin
(

let uu____1348 = (

let uu____1349 = (FStar_SMTEncoding_Util.mkFreeV ((name), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_ApplyTF uu____1349 fuel))
in (FStar_All.pipe_left (fun _0_30 -> Some (_0_30)) uu____1348))
end
| uu____1351 -> begin
Some (t)
end))
end
| uu____1352 -> begin
Some (t)
end)
end
| uu____1353 -> begin
None
end)
end)
end)))


let lookup_free_var = (fun env a -> (

let uu____1371 = (try_lookup_free_var env a.FStar_Syntax_Syntax.v)
in (match (uu____1371) with
| Some (t) -> begin
t
end
| None -> begin
(

let uu____1374 = (

let uu____1375 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" uu____1375))
in (failwith uu____1374))
end)))


let lookup_free_var_name = (fun env a -> (

let uu____1392 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (uu____1392) with
| (x, uu____1399, uu____1400) -> begin
x
end)))


let lookup_free_var_sym = (fun env a -> (

let uu____1424 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (uu____1424) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.freevars = uu____1445; FStar_SMTEncoding_Term.rng = uu____1446}) when env.use_zfuel_name -> begin
((g), (zf))
end
| uu____1454 -> begin
(match (sym) with
| None -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end
| Some (sym) -> begin
(match (sym.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, (fuel)::[]) -> begin
((g), ((fuel)::[]))
end
| uu____1468 -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end)
end)
end)
end)))


let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun uu___114_1477 -> (match (uu___114_1477) with
| Binding_fvar (uu____1479, nm', tok, uu____1482) when (nm = nm') -> begin
tok
end
| uu____1487 -> begin
None
end))))


let mkForall_fuel' = (fun n uu____1504 -> (match (uu____1504) with
| (pats, vars, body) -> begin
(

let fallback = (fun uu____1520 -> (FStar_SMTEncoding_Util.mkForall ((pats), (vars), (body))))
in (

let uu____1523 = (FStar_Options.unthrottle_inductives ())
in (match (uu____1523) with
| true -> begin
(fallback ())
end
| uu____1524 -> begin
(

let uu____1525 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____1525) with
| (fsym, fterm) -> begin
(

let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Util.mkApp (("HasTypeFuel"), ((fterm)::args)))
end
| uu____1544 -> begin
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

let uu____1558 = (add_fuel guards)
in (FStar_SMTEncoding_Util.mk_and_l uu____1558))
end
| uu____1560 -> begin
(

let uu____1561 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right uu____1561 FStar_List.hd))
end)
in (FStar_SMTEncoding_Util.mkImp ((guard), (body'))))
end
| uu____1564 -> begin
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

let uu____1608 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____1608 FStar_Option.isNone))
end
| uu____1621 -> begin
false
end)))


let head_redex : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let uu____1628 = (

let uu____1629 = (FStar_Syntax_Util.un_uinst t)
in uu____1629.FStar_Syntax_Syntax.n)
in (match (uu____1628) with
| FStar_Syntax_Syntax.Tm_abs (uu____1632, uu____1633, Some (FStar_Util.Inr (l, flags))) -> begin
(((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid)) || (FStar_List.existsb (fun uu___115_1662 -> (match (uu___115_1662) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____1663 -> begin
false
end)) flags))
end
| FStar_Syntax_Syntax.Tm_abs (uu____1664, uu____1665, Some (FStar_Util.Inl (lc))) -> begin
(FStar_Syntax_Util.is_tot_or_gtot_lcomp lc)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____1692 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____1692 FStar_Option.isSome))
end
| uu____1705 -> begin
false
end)))


let whnf : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____1712 = (head_normal env t)
in (match (uu____1712) with
| true -> begin
t
end
| uu____1713 -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
end)))


let norm : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t))


let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____1723 = (

let uu____1727 = (FStar_Syntax_Syntax.null_binder t)
in (uu____1727)::[])
in (

let uu____1728 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Util.abs uu____1723 uu____1728 None))))


let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(

let uu____1755 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out uu____1755))
end
| s -> begin
(

let uu____1758 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Util.mk_ApplyTT out uu____1758))
end)) e)))


let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)))


let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun uu___116_1770 -> (match (uu___116_1770) with
| (FStar_SMTEncoding_Term.Var ("ApplyTT")) | (FStar_SMTEncoding_Term.Var ("ApplyTF")) -> begin
true
end
| uu____1771 -> begin
false
end))


let is_eta : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env vars t -> (

let rec aux = (fun t xs -> (match (((t.FStar_SMTEncoding_Term.tm), (xs))) with
| (FStar_SMTEncoding_Term.App (app, (f)::({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.freevars = uu____1799; FStar_SMTEncoding_Term.rng = uu____1800})::[]), (x)::xs) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), uu____1814) -> begin
(

let uu____1819 = (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v)
end
| uu____1829 -> begin
false
end)) args vars))
in (match (uu____1819) with
| true -> begin
(tok_of_name env f)
end
| uu____1831 -> begin
None
end))
end
| (uu____1832, []) -> begin
(

let fvs = (FStar_SMTEncoding_Term.free_variables t)
in (

let uu____1835 = (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (

let uu____1837 = (FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)
in (not (uu____1837))))))
in (match (uu____1835) with
| true -> begin
Some (t)
end
| uu____1839 -> begin
None
end)))
end
| uu____1840 -> begin
None
end))
in (aux t (FStar_List.rev vars))))


let is_reifiable_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env effect_lid -> (

let quals = (FStar_TypeChecker_Env.lookup_effect_quals env effect_lid)
in (FStar_List.contains FStar_Syntax_Syntax.Reifiable quals)))


let is_reifiable : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.lcomp, FStar_Syntax_Syntax.residual_comp) FStar_Util.either  ->  Prims.bool = (fun env c -> (

let effect_lid = (match (c) with
| FStar_Util.Inl (lc) -> begin
lc.FStar_Syntax_Syntax.eff_name
end
| FStar_Util.Inr (eff_name, uu____1865) -> begin
eff_name
end)
in (is_reifiable_effect env effect_lid)))


let is_reifiable_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.bool = (fun env c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) -> begin
(is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name)
end
| uu____1878 -> begin
false
end))


let is_reifiable_function : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let uu____1885 = (

let uu____1886 = (FStar_Syntax_Subst.compress t)
in uu____1886.FStar_Syntax_Syntax.n)
in (match (uu____1885) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1889, c) -> begin
(is_reifiable_comp env c)
end
| uu____1901 -> begin
false
end)))


let reify_body : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let tm = (FStar_Syntax_Util.mk_reify t)
in (

let tm' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env tm)
in ((

let uu____1913 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____1913) with
| true -> begin
(

let uu____1914 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____1915 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print2 "Reified body %s \nto %s\n" uu____1914 uu____1915)))
end
| uu____1916 -> begin
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
| uu____1997 -> begin
false
end))


let encode_const : FStar_Const.sconst  ->  FStar_SMTEncoding_Term.term = (fun uu___117_2000 -> (match (uu___117_2000) with
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

let uu____2002 = (

let uu____2006 = (

let uu____2008 = (

let uu____2009 = (FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c))
in (FStar_SMTEncoding_Term.boxInt uu____2009))
in (uu____2008)::[])
in (("FStar.Char.Char"), (uu____2006)))
in (FStar_SMTEncoding_Util.mkApp uu____2002))
end
| FStar_Const.Const_int (i, None) -> begin
(

let uu____2017 = (FStar_SMTEncoding_Util.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt uu____2017))
end
| FStar_Const.Const_int (i, Some (uu____2019)) -> begin
(failwith "Machine integers should be desugared")
end
| FStar_Const.Const_string (bytes, uu____2028) -> begin
(

let uu____2031 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const uu____2031))
end
| FStar_Const.Const_range (r) -> begin
FStar_SMTEncoding_Term.mk_Range_const
end
| FStar_Const.Const_effect -> begin
FStar_SMTEncoding_Term.mk_Term_type
end
| c -> begin
(

let uu____2035 = (

let uu____2036 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" uu____2036))
in (failwith uu____2035))
end))


let as_function_typ : env_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (

let rec aux = (fun norm t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____2055) -> begin
t
end
| FStar_Syntax_Syntax.Tm_refine (uu____2063) -> begin
(

let uu____2068 = (FStar_Syntax_Util.unrefine t)
in (aux true uu____2068))
end
| uu____2069 -> begin
(match (norm) with
| true -> begin
(

let uu____2070 = (whnf env t)
in (aux false uu____2070))
end
| uu____2071 -> begin
(

let uu____2072 = (

let uu____2073 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (

let uu____2074 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" uu____2073 uu____2074)))
in (failwith uu____2072))
end)
end)))
in (aux true t0)))


let curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun k -> (

let k = (FStar_Syntax_Subst.compress k)
in (match (k.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| uu____2095 -> begin
(

let uu____2096 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (uu____2096)))
end)))


let rec encode_binders : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> ((

let uu____2239 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____2239) with
| true -> begin
(

let uu____2240 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" uu____2240))
end
| uu____2241 -> begin
()
end));
(

let uu____2242 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____2278 b -> (match (uu____2278) with
| (vars, guards, env, decls, names) -> begin
(

let uu____2321 = (

let x = (unmangle (Prims.fst b))
in (

let uu____2330 = (gen_term_var env x)
in (match (uu____2330) with
| (xxsym, xx, env') -> begin
(

let uu____2344 = (

let uu____2347 = (norm env x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt uu____2347 env xx))
in (match (uu____2344) with
| (guard_x_t, decls') -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (guard_x_t), (env'), (decls'), (x))
end))
end)))
in (match (uu____2321) with
| (v, g, env, decls', n) -> begin
(((v)::vars), ((g)::guards), (env), ((FStar_List.append decls decls')), ((n)::names))
end))
end)) (([]), ([]), (env), ([]), ([]))))
in (match (uu____2242) with
| (vars, guards, env, decls, names) -> begin
(((FStar_List.rev vars)), ((FStar_List.rev guards)), (env), (decls), ((FStar_List.rev names)))
end));
))
and encode_term_pred : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let uu____2435 = (encode_term t env)
in (match (uu____2435) with
| (t, decls) -> begin
(

let uu____2442 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t)
in ((uu____2442), (decls)))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let uu____2450 = (encode_term t env)
in (match (uu____2450) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(

let uu____2459 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t)
in ((uu____2459), (decls)))
end
| Some (f) -> begin
(

let uu____2461 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t)
in ((uu____2461), (decls)))
end)
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let t0 = (FStar_Syntax_Subst.compress t)
in ((

let uu____2468 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____2468) with
| true -> begin
(

let uu____2469 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____2470 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____2471 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" uu____2469 uu____2470 uu____2471))))
end
| uu____2472 -> begin
()
end));
(match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(

let uu____2476 = (

let uu____2477 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____2478 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____2479 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____2480 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2477 uu____2478 uu____2479 uu____2480)))))
in (failwith uu____2476))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____2484 = (

let uu____2485 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" uu____2485))
in (failwith uu____2484))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, k, uu____2490) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____2510) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t = (lookup_term_var env x)
in ((t), ([])))
end
| FStar_Syntax_Syntax.Tm_fvar (v) -> begin
(

let uu____2519 = (lookup_free_var env v.FStar_Syntax_Syntax.fv_name)
in ((uu____2519), ([])))
end
| FStar_Syntax_Syntax.Tm_type (uu____2525) -> begin
((FStar_SMTEncoding_Term.mk_Term_type), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t, uu____2528) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____2534 = (encode_const c)
in ((uu____2534), ([])))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____2548 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____2548) with
| (binders, res) -> begin
(

let uu____2555 = ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res))
in (match (uu____2555) with
| true -> begin
(

let uu____2558 = (encode_binders None binders env)
in (match (uu____2558) with
| (vars, guards, env', decls, uu____2573) -> begin
(

let fsym = (

let uu____2583 = (varops.fresh "f")
in ((uu____2583), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV fsym)
in (

let app = (mk_Apply f vars)
in (

let uu____2586 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post (

let uu___143_2590 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___143_2590.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___143_2590.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___143_2590.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___143_2590.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___143_2590.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___143_2590.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___143_2590.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___143_2590.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___143_2590.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___143_2590.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___143_2590.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___143_2590.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___143_2590.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___143_2590.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___143_2590.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___143_2590.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___143_2590.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___143_2590.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___143_2590.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___143_2590.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___143_2590.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___143_2590.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___143_2590.FStar_TypeChecker_Env.qname_and_index}) res)
in (match (uu____2586) with
| (pre_opt, res_t) -> begin
(

let uu____2597 = (encode_term_pred None res_t env' app)
in (match (uu____2597) with
| (res_pred, decls') -> begin
(

let uu____2604 = (match (pre_opt) with
| None -> begin
(

let uu____2611 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____2611), ([])))
end
| Some (pre) -> begin
(

let uu____2614 = (encode_formula pre env')
in (match (uu____2614) with
| (guard, decls0) -> begin
(

let uu____2622 = (FStar_SMTEncoding_Util.mk_and_l ((guard)::guards))
in ((uu____2622), (decls0)))
end))
end)
in (match (uu____2604) with
| (guards, guard_decls) -> begin
(

let t_interp = (

let uu____2630 = (

let uu____2636 = (FStar_SMTEncoding_Util.mkImp ((guards), (res_pred)))
in ((((app)::[])::[]), (vars), (uu____2636)))
in (FStar_SMTEncoding_Util.mkForall uu____2630))
in (

let cvars = (

let uu____2646 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right uu____2646 (FStar_List.filter (fun uu____2652 -> (match (uu____2652) with
| (x, uu____2656) -> begin
(x <> (Prims.fst fsym))
end)))))
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), ((fsym)::cvars), (t_interp)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____2667 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____2667) with
| Some (t', sorts, uu____2683) -> begin
(

let uu____2693 = (

let uu____2694 = (

let uu____2698 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((t'), (uu____2698)))
in (FStar_SMTEncoding_Util.mkApp uu____2694))
in ((uu____2693), ([])))
end
| None -> begin
(

let tsym = (

let uu____2714 = (

let uu____2715 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_arrow_" uu____2715))
in (varops.mk_unique uu____2714))
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let caption = (

let uu____2722 = (FStar_Options.log_queries ())
in (match (uu____2722) with
| true -> begin
(

let uu____2724 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in Some (uu____2724))
end
| uu____2725 -> begin
None
end))
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (caption)))
in (

let t = (

let uu____2730 = (

let uu____2734 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((tsym), (uu____2734)))
in (FStar_SMTEncoding_Util.mkApp uu____2730))
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let k_assumption = (

let a_name = Some ((Prims.strcat "kinding_" tsym))
in (

let uu____2743 = (

let uu____2748 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((uu____2748), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (uu____2743)))
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t)
in (

let pre_typing = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in (

let uu____2763 = (

let uu____2768 = (

let uu____2769 = (

let uu____2775 = (

let uu____2776 = (

let uu____2779 = (

let uu____2780 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____2780))
in ((f_has_t), (uu____2779)))
in (FStar_SMTEncoding_Util.mkImp uu____2776))
in ((((f_has_t)::[])::[]), ((fsym)::cvars), (uu____2775)))
in (mkForall_fuel uu____2769))
in ((uu____2768), (Some ("pre-typing for functions")), (a_name)))
in FStar_SMTEncoding_Term.Assume (uu____2763)))
in (

let t_interp = (

let a_name = Some ((Prims.strcat "interpretation_" tsym))
in (

let uu____2795 = (

let uu____2800 = (

let uu____2801 = (

let uu____2807 = (FStar_SMTEncoding_Util.mkIff ((f_has_t_z), (t_interp)))
in ((((f_has_t_z)::[])::[]), ((fsym)::cvars), (uu____2807)))
in (FStar_SMTEncoding_Util.mkForall uu____2801))
in ((uu____2800), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (uu____2795)))
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
| uu____2830 -> begin
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

let uu____2840 = (

let uu____2845 = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in ((uu____2845), (Some ("Typing for non-total arrows")), (a_name)))
in FStar_SMTEncoding_Term.Assume (uu____2840)))
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

let uu____2856 = (

let uu____2861 = (

let uu____2862 = (

let uu____2868 = (

let uu____2869 = (

let uu____2872 = (

let uu____2873 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____2873))
in ((f_has_t), (uu____2872)))
in (FStar_SMTEncoding_Util.mkImp uu____2869))
in ((((f_has_t)::[])::[]), ((fsym)::[]), (uu____2868)))
in (mkForall_fuel uu____2862))
in ((uu____2861), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (uu____2856)))
in ((t), ((tdecl)::(t_kinding)::(t_interp)::[]))))))))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_refine (uu____2888) -> begin
(

let uu____2893 = (

let uu____2896 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)
in (match (uu____2896) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.tk = uu____2901; FStar_Syntax_Syntax.pos = uu____2902; FStar_Syntax_Syntax.vars = uu____2903} -> begin
(

let uu____2910 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) f)
in (match (uu____2910) with
| (b, f) -> begin
(

let uu____2924 = (

let uu____2925 = (FStar_List.hd b)
in (Prims.fst uu____2925))
in ((uu____2924), (f)))
end))
end
| uu____2930 -> begin
(failwith "impossible")
end))
in (match (uu____2893) with
| (x, f) -> begin
(

let uu____2937 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (uu____2937) with
| (base_t, decls) -> begin
(

let uu____2944 = (gen_term_var env x)
in (match (uu____2944) with
| (x, xtm, env') -> begin
(

let uu____2953 = (encode_formula f env')
in (match (uu____2953) with
| (refinement, decls') -> begin
(

let uu____2960 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____2960) with
| (fsym, fterm) -> begin
(

let encoding = (

let uu____2968 = (

let uu____2971 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in ((uu____2971), (refinement)))
in (FStar_SMTEncoding_Util.mkAnd uu____2968))
in (

let cvars = (

let uu____2976 = (FStar_SMTEncoding_Term.free_variables encoding)
in (FStar_All.pipe_right uu____2976 (FStar_List.filter (fun uu____2982 -> (match (uu____2982) with
| (y, uu____2986) -> begin
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

let uu____3005 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____3005) with
| Some (t, uu____3020, uu____3021) -> begin
(

let uu____3031 = (

let uu____3032 = (

let uu____3036 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((t), (uu____3036)))
in (FStar_SMTEncoding_Util.mkApp uu____3032))
in ((uu____3031), ([])))
end
| None -> begin
(

let tsym = (

let uu____3052 = (

let uu____3053 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_refine_" uu____3053))
in (varops.mk_unique uu____3052))
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let t = (

let uu____3062 = (

let uu____3066 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((tsym), (uu____3066)))
in (FStar_SMTEncoding_Util.mkApp uu____3062))
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

let uu____3076 = (

let uu____3081 = (

let uu____3082 = (

let uu____3088 = (FStar_SMTEncoding_Util.mkIff ((t_haseq_ref), (t_haseq_base)))
in ((((t_haseq_ref)::[])::[]), (cvars), (uu____3088)))
in (FStar_SMTEncoding_Util.mkForall uu____3082))
in ((uu____3081), (Some ((Prims.strcat "haseq for " tsym))), (Some ((Prims.strcat "haseq" tsym)))))
in FStar_SMTEncoding_Term.Assume (uu____3076))
in (

let t_kinding = (

let uu____3099 = (

let uu____3104 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((uu____3104), (Some ("refinement kinding")), (Some ((Prims.strcat "refinement_kinding_" tsym)))))
in FStar_SMTEncoding_Term.Assume (uu____3099))
in (

let t_interp = (

let uu____3115 = (

let uu____3120 = (

let uu____3121 = (

let uu____3127 = (FStar_SMTEncoding_Util.mkIff ((x_has_t), (encoding)))
in ((((x_has_t)::[])::[]), ((ffv)::(xfv)::cvars), (uu____3127)))
in (FStar_SMTEncoding_Util.mkForall uu____3121))
in (

let uu____3139 = (

let uu____3141 = (FStar_Syntax_Print.term_to_string t0)
in Some (uu____3141))
in ((uu____3120), (uu____3139), (Some ((Prims.strcat "refinement_interpretation_" tsym))))))
in FStar_SMTEncoding_Term.Assume (uu____3115))
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

let uu____3170 = (FStar_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Util.mk_Term_uvar uu____3170))
in (

let uu____3174 = (encode_term_pred None k env ttm)
in (match (uu____3174) with
| (t_has_k, decls) -> begin
(

let d = (

let uu____3182 = (

let uu____3187 = (

let uu____3189 = (

let uu____3190 = (

let uu____3191 = (

let uu____3192 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____3192))
in (FStar_Util.format1 "uvar_typing_%s" uu____3191))
in (varops.mk_unique uu____3190))
in Some (uu____3189))
in ((t_has_k), (Some ("Uvar typing")), (uu____3187)))
in FStar_SMTEncoding_Term.Assume (uu____3182))
in ((ttm), ((FStar_List.append decls ((d)::[])))))
end)))
end
| FStar_Syntax_Syntax.Tm_app (uu____3199) -> begin
(

let uu____3209 = (FStar_Syntax_Util.head_and_args t0)
in (match (uu____3209) with
| (head, args_e) -> begin
(

let uu____3237 = (

let uu____3245 = (

let uu____3246 = (FStar_Syntax_Subst.compress head)
in uu____3246.FStar_Syntax_Syntax.n)
in ((uu____3245), (args_e)))
in (match (uu____3237) with
| (uu____3256, uu____3257) when (head_redex env head) -> begin
(

let uu____3268 = (whnf env t)
in (encode_term uu____3268 env))
end
| ((FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), (_)::((v1, _))::((v2, _))::[])) | ((FStar_Syntax_Syntax.Tm_fvar (fv), (_)::((v1, _))::((v2, _))::[])) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
(

let uu____3342 = (encode_term v1 env)
in (match (uu____3342) with
| (v1, decls1) -> begin
(

let uu____3349 = (encode_term v2 env)
in (match (uu____3349) with
| (v2, decls2) -> begin
(

let uu____3356 = (FStar_SMTEncoding_Util.mk_LexCons v1 v2)
in ((uu____3356), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), uu____3358) -> begin
(

let e0 = (

let uu____3372 = (

let uu____3375 = (

let uu____3376 = (

let uu____3386 = (

let uu____3392 = (FStar_List.hd args_e)
in (uu____3392)::[])
in ((head), (uu____3386)))
in FStar_Syntax_Syntax.Tm_app (uu____3376))
in (FStar_Syntax_Syntax.mk uu____3375))
in (uu____3372 None head.FStar_Syntax_Syntax.pos))
in ((

let uu____3425 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____3425) with
| true -> begin
(

let uu____3426 = (FStar_Syntax_Print.term_to_string e0)
in (FStar_Util.print1 "Trying to normalize %s\n" uu____3426))
end
| uu____3427 -> begin
()
end));
(

let e0 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env.tcenv e0)
in ((

let uu____3430 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____3430) with
| true -> begin
(

let uu____3431 = (FStar_Syntax_Print.term_to_string e0)
in (FStar_Util.print1 "Result of normalization %s\n" uu____3431))
end
| uu____3432 -> begin
()
end));
(

let e0 = (

let uu____3434 = (

let uu____3435 = (

let uu____3436 = (FStar_Syntax_Subst.compress e0)
in uu____3436.FStar_Syntax_Syntax.n)
in (match (uu____3435) with
| FStar_Syntax_Syntax.Tm_app (uu____3439) -> begin
false
end
| uu____3449 -> begin
true
end))
in (match (uu____3434) with
| true -> begin
e0
end
| uu____3450 -> begin
(

let uu____3451 = (FStar_Syntax_Util.head_and_args e0)
in (match (uu____3451) with
| (head, args) -> begin
(

let uu____3477 = (

let uu____3478 = (

let uu____3479 = (FStar_Syntax_Subst.compress head)
in uu____3479.FStar_Syntax_Syntax.n)
in (match (uu____3478) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) -> begin
true
end
| uu____3482 -> begin
false
end))
in (match (uu____3477) with
| true -> begin
(match (args) with
| (x)::[] -> begin
(Prims.fst x)
end
| uu____3498 -> begin
(failwith "Impossible : Reify applied to multiple arguments after normalization.")
end)
end
| uu____3504 -> begin
e0
end))
end))
end))
in (

let e = (match (args_e) with
| (uu____3506)::[] -> begin
e0
end
| uu____3519 -> begin
(

let uu____3525 = (

let uu____3528 = (

let uu____3529 = (

let uu____3539 = (FStar_List.tl args_e)
in ((e0), (uu____3539)))
in FStar_Syntax_Syntax.Tm_app (uu____3529))
in (FStar_Syntax_Syntax.mk uu____3528))
in (uu____3525 None t0.FStar_Syntax_Syntax.pos))
end)
in (encode_term e env)));
));
))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____3562)), ((arg, uu____3564))::[]) -> begin
(encode_term arg env)
end
| uu____3582 -> begin
(

let uu____3590 = (encode_args args_e env)
in (match (uu____3590) with
| (args, decls) -> begin
(

let encode_partial_app = (fun ht_opt -> (

let uu____3623 = (encode_term head env)
in (match (uu____3623) with
| (head, decls') -> begin
(

let app_tm = (mk_Apply_args head args)
in (match (ht_opt) with
| None -> begin
((app_tm), ((FStar_List.append decls decls')))
end
| Some (formals, c) -> begin
(

let uu____3662 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (uu____3662) with
| (formals, rest) -> begin
(

let subst = (FStar_List.map2 (fun uu____3704 uu____3705 -> (match (((uu____3704), (uu____3705))) with
| ((bv, uu____3719), (a, uu____3721)) -> begin
FStar_Syntax_Syntax.NT (((bv), (a)))
end)) formals args_e)
in (

let ty = (

let uu____3735 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right uu____3735 (FStar_Syntax_Subst.subst subst)))
in (

let uu____3740 = (encode_term_pred None ty env app_tm)
in (match (uu____3740) with
| (has_type, decls'') -> begin
(

let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (

let e_typing = (

let uu____3750 = (

let uu____3755 = (FStar_SMTEncoding_Util.mkForall ((((has_type)::[])::[]), (cvars), (has_type)))
in (

let uu____3760 = (

let uu____3762 = (

let uu____3763 = (

let uu____3764 = (

let uu____3765 = (FStar_SMTEncoding_Term.hash_of_term app_tm)
in (FStar_Util.digest_of_string uu____3765))
in (Prims.strcat "partial_app_typing_" uu____3764))
in (varops.mk_unique uu____3763))
in Some (uu____3762))
in ((uu____3755), (Some ("Partial app typing")), (uu____3760))))
in FStar_SMTEncoding_Term.Assume (uu____3750))
in ((app_tm), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' ((e_typing)::[]))))))))
end))))
end))
end))
end)))
in (

let encode_full_app = (fun fv -> (

let uu____3783 = (lookup_free_var_sym env fv)
in (match (uu____3783) with
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

let uu____3821 = (

let uu____3822 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____3822 Prims.snd))
in Some (uu____3821))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____3831, FStar_Util.Inl (t), uu____3833) -> begin
Some (t)
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____3854, FStar_Util.Inr (c), uu____3856) -> begin
Some ((FStar_Syntax_Util.comp_result c))
end
| uu____3877 -> begin
None
end)
in (match (head_type) with
| None -> begin
(encode_partial_app None)
end
| Some (head_type) -> begin
(

let head_type = (

let uu____3897 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine uu____3897))
in (

let uu____3898 = (curried_arrow_formals_comp head_type)
in (match (uu____3898) with
| (formals, c) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| uu____3923 -> begin
(match (((FStar_List.length formals) > (FStar_List.length args))) with
| true -> begin
(encode_partial_app (Some (((formals), (c)))))
end
| uu____3935 -> begin
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

let uu____3968 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____3968) with
| (bs, body, opening) -> begin
(

let fallback = (fun uu____3983 -> (

let f = (varops.fresh "Tm_abs")
in (

let decl = FStar_SMTEncoding_Term.DeclFun (((f), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Imprecise function encoding"))))
in (

let uu____3988 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in ((uu____3988), ((decl)::[]))))))
in (

let is_impure = (fun uu___118_3998 -> (match (uu___118_3998) with
| FStar_Util.Inl (lc) -> begin
(

let uu____4008 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)
in (not (uu____4008)))
end
| FStar_Util.Inr (eff, uu____4010) -> begin
(

let uu____4016 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv eff)
in (FStar_All.pipe_right uu____4016 Prims.op_Negation))
end))
in (

let reify_comp_and_body = (fun env c body -> (

let reified_body = (reify_body env.tcenv body)
in (

let c = (match (c) with
| FStar_Util.Inl (lc) -> begin
(

let typ = (FStar_TypeChecker_Util.reify_comp (

let uu___144_4061 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___144_4061.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___144_4061.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___144_4061.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___144_4061.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___144_4061.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___144_4061.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___144_4061.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___144_4061.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___144_4061.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___144_4061.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___144_4061.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___144_4061.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___144_4061.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___144_4061.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___144_4061.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___144_4061.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___144_4061.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___144_4061.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___144_4061.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___144_4061.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___144_4061.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___144_4061.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___144_4061.FStar_TypeChecker_Env.qname_and_index}) lc FStar_Syntax_Syntax.U_unknown)
in (

let uu____4062 = (

let uu____4063 = (FStar_Syntax_Syntax.mk_Total typ)
in (FStar_Syntax_Util.lcomp_of_comp uu____4063))
in FStar_Util.Inl (uu____4062)))
end
| FStar_Util.Inr (eff_name, uu____4070) -> begin
c
end)
in ((c), (reified_body)))))
in (

let codomain_eff = (fun lc -> (match (lc) with
| FStar_Util.Inl (lc) -> begin
(

let uu____4101 = (

let uu____4102 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening uu____4102))
in (FStar_All.pipe_right uu____4101 (fun _0_31 -> Some (_0_31))))
end
| FStar_Util.Inr (eff, flags) -> begin
(

let new_uvar = (fun uu____4114 -> (

let uu____4115 = (FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange [] FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right uu____4115 Prims.fst)))
in (match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid)) with
| true -> begin
(

let uu____4123 = (

let uu____4124 = (new_uvar ())
in (FStar_Syntax_Syntax.mk_Total uu____4124))
in (FStar_All.pipe_right uu____4123 (fun _0_32 -> Some (_0_32))))
end
| uu____4126 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid)) with
| true -> begin
(

let uu____4128 = (

let uu____4129 = (new_uvar ())
in (FStar_Syntax_Syntax.mk_GTotal uu____4129))
in (FStar_All.pipe_right uu____4128 (fun _0_33 -> Some (_0_33))))
end
| uu____4131 -> begin
None
end)
end))
end))
in (match (lopt) with
| None -> begin
((

let uu____4140 = (

let uu____4141 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)" uu____4141))
in (FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____4140));
(fallback ());
)
end
| Some (lc) -> begin
(

let uu____4153 = ((is_impure lc) && (

let uu____4154 = (is_reifiable env.tcenv lc)
in (not (uu____4154))))
in (match (uu____4153) with
| true -> begin
(fallback ())
end
| uu____4157 -> begin
(

let uu____4158 = (encode_binders None bs env)
in (match (uu____4158) with
| (vars, guards, envbody, decls, uu____4173) -> begin
(

let uu____4180 = (

let uu____4188 = (is_reifiable env.tcenv lc)
in (match (uu____4188) with
| true -> begin
(reify_comp_and_body envbody lc body)
end
| uu____4196 -> begin
((lc), (body))
end))
in (match (uu____4180) with
| (lc, body) -> begin
(

let uu____4216 = (encode_term body envbody)
in (match (uu____4216) with
| (body, decls') -> begin
(

let key_body = (

let uu____4224 = (

let uu____4230 = (

let uu____4231 = (

let uu____4234 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____4234), (body)))
in (FStar_SMTEncoding_Util.mkImp uu____4231))
in (([]), (vars), (uu____4230)))
in (FStar_SMTEncoding_Util.mkForall uu____4224))
in (

let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), (cvars), (key_body)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____4245 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____4245) with
| Some (t, uu____4260, uu____4261) -> begin
(

let uu____4271 = (

let uu____4272 = (

let uu____4276 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((t), (uu____4276)))
in (FStar_SMTEncoding_Util.mkApp uu____4272))
in ((uu____4271), ([])))
end
| None -> begin
(

let uu____4287 = (is_eta env vars body)
in (match (uu____4287) with
| Some (t) -> begin
((t), ([]))
end
| None -> begin
(

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let fsym = (

let uu____4298 = (

let uu____4299 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_abs_" uu____4299))
in (varops.mk_unique uu____4298))
in (

let fdecl = FStar_SMTEncoding_Term.DeclFun (((fsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let f = (

let uu____4304 = (

let uu____4308 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((fsym), (uu____4308)))
in (FStar_SMTEncoding_Util.mkApp uu____4304))
in (

let app = (mk_Apply f vars)
in (

let typing_f = (

let uu____4316 = (codomain_eff lc)
in (match (uu____4316) with
| None -> begin
[]
end
| Some (c) -> begin
(

let tfun = (FStar_Syntax_Util.arrow bs c)
in (

let uu____4323 = (encode_term_pred None tfun env f)
in (match (uu____4323) with
| (f_has_t, decls'') -> begin
(

let a_name = Some ((Prims.strcat "typing_" fsym))
in (

let uu____4331 = (

let uu____4333 = (

let uu____4334 = (

let uu____4339 = (FStar_SMTEncoding_Util.mkForall ((((f)::[])::[]), (cvars), (f_has_t)))
in ((uu____4339), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (uu____4334))
in (uu____4333)::[])
in (FStar_List.append decls'' uu____4331)))
end)))
end))
in (

let interp_f = (

let a_name = Some ((Prims.strcat "interpretation_" fsym))
in (

let uu____4349 = (

let uu____4354 = (

let uu____4355 = (

let uu____4361 = (FStar_SMTEncoding_Util.mkEq ((app), (body)))
in ((((app)::[])::[]), ((FStar_List.append vars cvars)), (uu____4361)))
in (FStar_SMTEncoding_Util.mkForall uu____4355))
in ((uu____4354), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (uu____4349)))
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
end))
end)))))
end))
end
| FStar_Syntax_Syntax.Tm_let ((uu____4380, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____4381); FStar_Syntax_Syntax.lbunivs = uu____4382; FStar_Syntax_Syntax.lbtyp = uu____4383; FStar_Syntax_Syntax.lbeff = uu____4384; FStar_Syntax_Syntax.lbdef = uu____4385})::uu____4386), uu____4387) -> begin
(failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____4405; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____4407; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (uu____4423) -> begin
((FStar_Errors.diag t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts");
(

let e = (varops.fresh "let-rec")
in (

let decl_e = FStar_SMTEncoding_Term.DeclFun (((e), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let uu____4436 = (FStar_SMTEncoding_Util.mkFreeV ((e), (FStar_SMTEncoding_Term.Term_sort)))
in ((uu____4436), ((decl_e)::[])))));
)
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end);
)))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (

let uu____4478 = (encode_term e1 env)
in (match (uu____4478) with
| (ee1, decls1) -> begin
(

let uu____4485 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) e2)
in (match (uu____4485) with
| (xs, e2) -> begin
(

let uu____4499 = (FStar_List.hd xs)
in (match (uu____4499) with
| (x, uu____4507) -> begin
(

let env' = (push_term_var env x ee1)
in (

let uu____4509 = (encode_body e2 env')
in (match (uu____4509) with
| (ee2, decls2) -> begin
((ee2), ((FStar_List.append decls1 decls2)))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (

let uu____4531 = (

let uu____4535 = (

let uu____4536 = ((FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown) None FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.null_bv uu____4536))
in (gen_term_var env uu____4535))
in (match (uu____4531) with
| (scrsym, scr', env) -> begin
(

let uu____4550 = (encode_term e env)
in (match (uu____4550) with
| (scr, decls) -> begin
(

let uu____4557 = (

let encode_branch = (fun b uu____4573 -> (match (uu____4573) with
| (else_case, decls) -> begin
(

let uu____4584 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____4584) with
| (p, w, br) -> begin
(

let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun uu____4614 uu____4615 -> (match (((uu____4614), (uu____4615))) with
| ((env0, pattern), (else_case, decls)) -> begin
(

let guard = (pattern.guard scr')
in (

let projections = (pattern.projections scr')
in (

let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env uu____4652 -> (match (uu____4652) with
| (x, t) -> begin
(push_term_var env x t)
end)) env))
in (

let uu____4657 = (match (w) with
| None -> begin
((guard), ([]))
end
| Some (w) -> begin
(

let uu____4672 = (encode_term w env)
in (match (uu____4672) with
| (w, decls2) -> begin
(

let uu____4680 = (

let uu____4681 = (

let uu____4684 = (

let uu____4685 = (

let uu____4688 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue)
in ((w), (uu____4688)))
in (FStar_SMTEncoding_Util.mkEq uu____4685))
in ((guard), (uu____4684)))
in (FStar_SMTEncoding_Util.mkAnd uu____4681))
in ((uu____4680), (decls2)))
end))
end)
in (match (uu____4657) with
| (guard, decls2) -> begin
(

let uu____4696 = (encode_br br env)
in (match (uu____4696) with
| (br, decls3) -> begin
(

let uu____4704 = (FStar_SMTEncoding_Util.mkITE ((guard), (br), (else_case)))
in ((uu____4704), ((FStar_List.append decls (FStar_List.append decls2 decls3)))))
end))
end)))))
end)) patterns ((else_case), (decls))))
end))
end))
in (FStar_List.fold_right encode_branch pats ((default_case), (decls))))
in (match (uu____4557) with
| (match_tm, decls) -> begin
(

let uu____4716 = (FStar_SMTEncoding_Term.mkLet' (((((((scrsym), (FStar_SMTEncoding_Term.Term_sort))), (scr)))::[]), (match_tm)) FStar_Range.dummyRange)
in ((uu____4716), (decls)))
end))
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| uu____4747 -> begin
(

let uu____4748 = (encode_one_pat env pat)
in (uu____4748)::[])
end))
and encode_one_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> ((

let uu____4760 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____4760) with
| true -> begin
(

let uu____4761 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" uu____4761))
end
| uu____4762 -> begin
()
end));
(

let uu____4763 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (uu____4763) with
| (vars, pat_term) -> begin
(

let uu____4773 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun uu____4796 v -> (match (uu____4796) with
| (env, vars) -> begin
(

let uu____4824 = (gen_term_var env v)
in (match (uu____4824) with
| (xx, uu____4836, env) -> begin
((env), ((((v), (((xx), (FStar_SMTEncoding_Term.Term_sort)))))::vars))
end))
end)) ((env), ([]))))
in (match (uu____4773) with
| (env, vars) -> begin
(

let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (uu____4883) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_dot_term (_)) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____4891 = (

let uu____4894 = (encode_const c)
in ((scrutinee), (uu____4894)))
in (FStar_SMTEncoding_Util.mkEq uu____4891))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let is_f = (

let tc_name = (FStar_TypeChecker_Env.typ_of_datacon env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let uu____4913 = (FStar_TypeChecker_Env.datacons_of_typ env.tcenv tc_name)
in (match (uu____4913) with
| (uu____4917, (uu____4918)::[]) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| uu____4920 -> begin
(mk_data_tester env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
end)))
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____4941 -> (match (uu____4941) with
| (arg, uu____4947) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____4957 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_guard arg uu____4957)))
end))))
in (FStar_SMTEncoding_Util.mk_and_l ((is_f)::sub_term_guards))))
end))
in (

let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (uu____4976) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _)) | (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_constant (uu____4991) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let uu____5006 = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____5028 -> (match (uu____5028) with
| (arg, uu____5037) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____5047 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_projections arg uu____5047)))
end))))
in (FStar_All.pipe_right uu____5006 FStar_List.flatten))
end))
in (

let pat_term = (fun uu____5063 -> (encode_term pat_term env))
in (

let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in ((env), (pattern))))))
end))
end));
))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (

let uu____5070 = (FStar_All.pipe_right l (FStar_List.fold_left (fun uu____5085 uu____5086 -> (match (((uu____5085), (uu____5086))) with
| ((tms, decls), (t, uu____5106)) -> begin
(

let uu____5117 = (encode_term t env)
in (match (uu____5117) with
| (t, decls') -> begin
(((t)::tms), ((FStar_List.append decls decls')))
end))
end)) (([]), ([]))))
in (match (uu____5070) with
| (l, decls) -> begin
(((FStar_List.rev l)), (decls))
end)))
and encode_function_type_as_formula : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun induction_on new_pats t env -> (

let list_elements = (fun e -> (

let uu____5155 = (FStar_Syntax_Util.list_elements e)
in (match (uu____5155) with
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

let uu____5173 = (

let uu____5183 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right uu____5183 FStar_Syntax_Util.head_and_args))
in (match (uu____5173) with
| (head, args) -> begin
(

let uu____5214 = (

let uu____5222 = (

let uu____5223 = (FStar_Syntax_Util.un_uinst head)
in uu____5223.FStar_Syntax_Syntax.n)
in ((uu____5222), (args)))
in (match (uu____5214) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((uu____5237, uu____5238))::((e, uu____5240))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpat_lid) -> begin
((e), (None))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, uu____5271))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatT_lid) -> begin
((e), (None))
end
| uu____5292 -> begin
(failwith "Unexpected pattern term")
end))
end)))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements p)
in (

let smt_pat_or = (fun t -> (

let uu____5325 = (

let uu____5335 = (FStar_Syntax_Util.unmeta t)
in (FStar_All.pipe_right uu____5335 FStar_Syntax_Util.head_and_args))
in (match (uu____5325) with
| (head, args) -> begin
(

let uu____5364 = (

let uu____5372 = (

let uu____5373 = (FStar_Syntax_Util.un_uinst head)
in uu____5373.FStar_Syntax_Syntax.n)
in ((uu____5372), (args)))
in (match (uu____5364) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, uu____5386))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatOr_lid) -> begin
Some (e)
end
| uu____5406 -> begin
None
end))
end)))
in (match (elts) with
| (t)::[] -> begin
(

let uu____5424 = (smt_pat_or t)
in (match (uu____5424) with
| Some (e) -> begin
(

let uu____5440 = (list_elements e)
in (FStar_All.pipe_right uu____5440 (FStar_List.map (fun branch -> (

let uu____5457 = (list_elements branch)
in (FStar_All.pipe_right uu____5457 (FStar_List.map one_pat)))))))
end
| uu____5471 -> begin
(

let uu____5475 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____5475)::[])
end))
end
| uu____5506 -> begin
(

let uu____5508 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____5508)::[])
end))))
in (

let uu____5539 = (

let uu____5555 = (

let uu____5556 = (FStar_Syntax_Subst.compress t)
in uu____5556.FStar_Syntax_Syntax.n)
in (match (uu____5555) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____5586 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____5586) with
| (binders, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____5621; FStar_Syntax_Syntax.effect_name = uu____5622; FStar_Syntax_Syntax.result_typ = uu____5623; FStar_Syntax_Syntax.effect_args = ((pre, uu____5625))::((post, uu____5627))::((pats, uu____5629))::[]; FStar_Syntax_Syntax.flags = uu____5630}) -> begin
(

let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (

let uu____5664 = (lemma_pats pats')
in ((binders), (pre), (post), (uu____5664))))
end
| uu____5683 -> begin
(failwith "impos")
end)
end))
end
| uu____5699 -> begin
(failwith "Impos")
end))
in (match (uu____5539) with
| (binders, pre, post, patterns) -> begin
(

let uu____5743 = (encode_binders None binders env)
in (match (uu____5743) with
| (vars, guards, env, decls, uu____5758) -> begin
(

let uu____5765 = (

let uu____5772 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (

let uu____5803 = (

let uu____5808 = (FStar_All.pipe_right branch (FStar_List.map (fun uu____5824 -> (match (uu____5824) with
| (t, uu____5831) -> begin
(encode_term t (

let uu___145_5834 = env
in {bindings = uu___145_5834.bindings; depth = uu___145_5834.depth; tcenv = uu___145_5834.tcenv; warn = uu___145_5834.warn; cache = uu___145_5834.cache; nolabels = uu___145_5834.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___145_5834.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right uu____5808 FStar_List.unzip))
in (match (uu____5803) with
| (pats, decls) -> begin
((pats), (decls))
end)))))
in (FStar_All.pipe_right uu____5772 FStar_List.unzip))
in (match (uu____5765) with
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

let uu____5898 = (

let uu____5899 = (FStar_SMTEncoding_Util.mkFreeV l)
in (FStar_SMTEncoding_Util.mk_Precedes uu____5899 e))
in (uu____5898)::p))))
end
| uu____5900 -> begin
(

let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (

let uu____5929 = (FStar_SMTEncoding_Util.mk_Precedes tl e)
in (uu____5929)::p))))
end
| ((x, FStar_SMTEncoding_Term.Term_sort))::vars -> begin
(

let uu____5937 = (

let uu____5938 = (FStar_SMTEncoding_Util.mkFreeV ((x), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Util.mk_LexCons uu____5938 tl))
in (aux uu____5937 vars))
end
| uu____5939 -> begin
pats
end))
in (

let uu____5943 = (FStar_SMTEncoding_Util.mkFreeV (("Prims.LexTop"), (FStar_SMTEncoding_Term.Term_sort)))
in (aux uu____5943 vars)))
end)
end)
in (

let env = (

let uu___146_5945 = env
in {bindings = uu___146_5945.bindings; depth = uu___146_5945.depth; tcenv = uu___146_5945.tcenv; warn = uu___146_5945.warn; cache = uu___146_5945.cache; nolabels = true; use_zfuel_name = uu___146_5945.use_zfuel_name; encode_non_total_function_typ = uu___146_5945.encode_non_total_function_typ})
in (

let uu____5946 = (

let uu____5949 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula uu____5949 env))
in (match (uu____5946) with
| (pre, decls'') -> begin
(

let uu____5954 = (

let uu____5957 = (FStar_Syntax_Util.unmeta post)
in (encode_formula uu____5957 env))
in (match (uu____5954) with
| (post, decls''') -> begin
(

let decls = (FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') (FStar_List.append decls'' decls''')))
in (

let uu____5964 = (

let uu____5965 = (

let uu____5971 = (

let uu____5972 = (

let uu____5975 = (FStar_SMTEncoding_Util.mk_and_l ((pre)::guards))
in ((uu____5975), (post)))
in (FStar_SMTEncoding_Util.mkImp uu____5972))
in ((pats), (vars), (uu____5971)))
in (FStar_SMTEncoding_Util.mkForall uu____5965))
in ((uu____5964), (decls))))
end))
end)))))
end))
end))
end))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (

let debug = (fun phi -> (

let uu____5988 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____5988) with
| true -> begin
(

let uu____5989 = (FStar_Syntax_Print.tag_of_term phi)
in (

let uu____5990 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print2 "Formula (%s)  %s\n" uu____5989 uu____5990)))
end
| uu____5991 -> begin
()
end)))
in (

let enc = (fun f r l -> (

let uu____6017 = (FStar_Util.fold_map (fun decls x -> (

let uu____6030 = (encode_term (Prims.fst x) env)
in (match (uu____6030) with
| (t, decls') -> begin
(((FStar_List.append decls decls')), (t))
end))) [] l)
in (match (uu____6017) with
| (decls, args) -> begin
(

let uu____6047 = (

let uu___147_6048 = (f args)
in {FStar_SMTEncoding_Term.tm = uu___147_6048.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___147_6048.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____6047), (decls)))
end)))
in (

let const_op = (fun f r uu____6067 -> (

let uu____6070 = (f r)
in ((uu____6070), ([]))))
in (

let un_op = (fun f l -> (

let uu____6086 = (FStar_List.hd l)
in (FStar_All.pipe_left f uu____6086)))
in (

let bin_op = (fun f uu___119_6099 -> (match (uu___119_6099) with
| (t1)::(t2)::[] -> begin
(f ((t1), (t2)))
end
| uu____6107 -> begin
(failwith "Impossible")
end))
in (

let enc_prop_c = (fun f r l -> (

let uu____6134 = (FStar_Util.fold_map (fun decls uu____6143 -> (match (uu____6143) with
| (t, uu____6151) -> begin
(

let uu____6152 = (encode_formula t env)
in (match (uu____6152) with
| (phi, decls') -> begin
(((FStar_List.append decls decls')), (phi))
end))
end)) [] l)
in (match (uu____6134) with
| (decls, phis) -> begin
(

let uu____6169 = (

let uu___148_6170 = (f phis)
in {FStar_SMTEncoding_Term.tm = uu___148_6170.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___148_6170.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____6169), (decls)))
end)))
in (

let eq_op = (fun r uu___120_6186 -> (match (uu___120_6186) with
| ((_)::(e1)::(e2)::[]) | ((_)::(_)::(e1)::(e2)::[]) -> begin
(

let uu____6246 = (enc (bin_op FStar_SMTEncoding_Util.mkEq))
in (uu____6246 r ((e1)::(e2)::[])))
end
| l -> begin
(

let uu____6266 = (enc (bin_op FStar_SMTEncoding_Util.mkEq))
in (uu____6266 r l))
end))
in (

let mk_imp = (fun r uu___121_6285 -> (match (uu___121_6285) with
| ((lhs, uu____6289))::((rhs, uu____6291))::[] -> begin
(

let uu____6312 = (encode_formula rhs env)
in (match (uu____6312) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____6321) -> begin
((l1), (decls1))
end
| uu____6324 -> begin
(

let uu____6325 = (encode_formula lhs env)
in (match (uu____6325) with
| (l2, decls2) -> begin
(

let uu____6332 = (FStar_SMTEncoding_Term.mkImp ((l2), (l1)) r)
in ((uu____6332), ((FStar_List.append decls1 decls2))))
end))
end)
end))
end
| uu____6334 -> begin
(failwith "impossible")
end))
in (

let mk_ite = (fun r uu___122_6349 -> (match (uu___122_6349) with
| ((guard, uu____6353))::((_then, uu____6355))::((_else, uu____6357))::[] -> begin
(

let uu____6386 = (encode_formula guard env)
in (match (uu____6386) with
| (g, decls1) -> begin
(

let uu____6393 = (encode_formula _then env)
in (match (uu____6393) with
| (t, decls2) -> begin
(

let uu____6400 = (encode_formula _else env)
in (match (uu____6400) with
| (e, decls3) -> begin
(

let res = (FStar_SMTEncoding_Term.mkITE ((g), (t), (e)) r)
in ((res), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end))
end))
end
| uu____6409 -> begin
(failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (

let uu____6428 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f uu____6428)))
in (

let connectives = (

let uu____6440 = (

let uu____6449 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd))
in ((FStar_Syntax_Const.and_lid), (uu____6449)))
in (

let uu____6462 = (

let uu____6472 = (

let uu____6481 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr))
in ((FStar_Syntax_Const.or_lid), (uu____6481)))
in (

let uu____6494 = (

let uu____6504 = (

let uu____6514 = (

let uu____6523 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff))
in ((FStar_Syntax_Const.iff_lid), (uu____6523)))
in (

let uu____6536 = (

let uu____6546 = (

let uu____6556 = (

let uu____6565 = (enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot))
in ((FStar_Syntax_Const.not_lid), (uu____6565)))
in (uu____6556)::(((FStar_Syntax_Const.eq2_lid), (eq_op)))::(((FStar_Syntax_Const.eq3_lid), (eq_op)))::(((FStar_Syntax_Const.true_lid), ((const_op FStar_SMTEncoding_Term.mkTrue))))::(((FStar_Syntax_Const.false_lid), ((const_op FStar_SMTEncoding_Term.mkFalse))))::[])
in (((FStar_Syntax_Const.ite_lid), (mk_ite)))::uu____6546)
in (uu____6514)::uu____6536))
in (((FStar_Syntax_Const.imp_lid), (mk_imp)))::uu____6504)
in (uu____6472)::uu____6494))
in (uu____6440)::uu____6462))
in (

let rec fallback = (fun phi -> (match (phi.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(

let uu____6727 = (encode_formula phi' env)
in (match (uu____6727) with
| (phi, decls) -> begin
(

let uu____6734 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled (((phi), (msg), (r)))) r)
in ((uu____6734), (decls)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (uu____6735) -> begin
(

let uu____6740 = (FStar_Syntax_Util.unmeta phi)
in (encode_formula uu____6740 env))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(

let uu____6769 = (encode_match e pats FStar_SMTEncoding_Util.mkFalse env encode_formula)
in (match (uu____6769) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____6777; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____6779; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let uu____6795 = (encode_let x t1 e1 e2 env encode_formula)
in (match (uu____6795) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let head = (FStar_Syntax_Util.un_uinst head)
in (match (((head.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____6827)::((x, uu____6829))::((t, uu____6831))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.has_type_lid) -> begin
(

let uu____6865 = (encode_term x env)
in (match (uu____6865) with
| (x, decls) -> begin
(

let uu____6872 = (encode_term t env)
in (match (uu____6872) with
| (t, decls') -> begin
(

let uu____6879 = (FStar_SMTEncoding_Term.mk_HasType x t)
in ((uu____6879), ((FStar_List.append decls decls'))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((r, uu____6883))::((msg, uu____6885))::((phi, uu____6887))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.labeled_lid) -> begin
(

let uu____6921 = (

let uu____6924 = (

let uu____6925 = (FStar_Syntax_Subst.compress r)
in uu____6925.FStar_Syntax_Syntax.n)
in (

let uu____6928 = (

let uu____6929 = (FStar_Syntax_Subst.compress msg)
in uu____6929.FStar_Syntax_Syntax.n)
in ((uu____6924), (uu____6928))))
in (match (uu____6921) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____6936))) -> begin
(

let phi = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((phi), (FStar_Syntax_Syntax.Meta_labeled ((((FStar_Util.string_of_unicode s)), (r), (false)))))))) None r)
in (fallback phi))
end
| uu____6952 -> begin
(fallback phi)
end))
end
| uu____6955 when (head_redex env head) -> begin
(

let uu____6963 = (whnf env phi)
in (encode_formula uu____6963 env))
end
| uu____6964 -> begin
(

let uu____6972 = (encode_term phi env)
in (match (uu____6972) with
| (tt, decls) -> begin
(

let uu____6979 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___149_6980 = tt
in {FStar_SMTEncoding_Term.tm = uu___149_6980.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___149_6980.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi.FStar_Syntax_Syntax.pos}))
in ((uu____6979), (decls)))
end))
end))
end
| uu____6983 -> begin
(

let uu____6984 = (encode_term phi env)
in (match (uu____6984) with
| (tt, decls) -> begin
(

let uu____6991 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___150_6992 = tt
in {FStar_SMTEncoding_Term.tm = uu___150_6992.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___150_6992.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi.FStar_Syntax_Syntax.pos}))
in ((uu____6991), (decls)))
end))
end))
in (

let encode_q_body = (fun env bs ps body -> (

let uu____7019 = (encode_binders None bs env)
in (match (uu____7019) with
| (vars, guards, env, decls, uu____7041) -> begin
(

let uu____7048 = (

let uu____7055 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let uu____7078 = (

let uu____7083 = (FStar_All.pipe_right p (FStar_List.map (fun uu____7097 -> (match (uu____7097) with
| (t, uu____7103) -> begin
(encode_term t (

let uu___151_7104 = env
in {bindings = uu___151_7104.bindings; depth = uu___151_7104.depth; tcenv = uu___151_7104.tcenv; warn = uu___151_7104.warn; cache = uu___151_7104.cache; nolabels = uu___151_7104.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___151_7104.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right uu____7083 FStar_List.unzip))
in (match (uu____7078) with
| (p, decls) -> begin
((p), ((FStar_List.flatten decls)))
end)))))
in (FStar_All.pipe_right uu____7055 FStar_List.unzip))
in (match (uu____7048) with
| (pats, decls') -> begin
(

let uu____7156 = (encode_formula body env)
in (match (uu____7156) with
| (body, decls'') -> begin
(

let guards = (match (pats) with
| (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (gf), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____7175; FStar_SMTEncoding_Term.rng = uu____7176})::[])::[] when ((FStar_Ident.text_of_lid FStar_Syntax_Const.guard_free) = gf) -> begin
[]
end
| uu____7184 -> begin
guards
end)
in (

let uu____7187 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((vars), (pats), (uu____7187), (body), ((FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') decls''))))))
end))
end))
end)))
in ((debug phi);
(

let phi = (FStar_Syntax_Util.unascribe phi)
in (

let check_pattern_vars = (fun vars pats -> (

let pats = (FStar_All.pipe_right pats (FStar_List.map (fun uu____7221 -> (match (uu____7221) with
| (x, uu____7225) -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x)
end))))
in (match (pats) with
| [] -> begin
()
end
| (hd)::tl -> begin
(

let pat_vars = (

let uu____7231 = (FStar_Syntax_Free.names hd)
in (FStar_List.fold_left (fun out x -> (

let uu____7237 = (FStar_Syntax_Free.names x)
in (FStar_Util.set_union out uu____7237))) uu____7231 tl))
in (

let uu____7239 = (FStar_All.pipe_right vars (FStar_Util.find_opt (fun uu____7251 -> (match (uu____7251) with
| (b, uu____7255) -> begin
(

let uu____7256 = (FStar_Util.set_mem b pat_vars)
in (not (uu____7256)))
end))))
in (match (uu____7239) with
| None -> begin
()
end
| Some (x, uu____7260) -> begin
(

let pos = (FStar_List.fold_left (fun out t -> (FStar_Range.union_ranges out t.FStar_Syntax_Syntax.pos)) hd.FStar_Syntax_Syntax.pos tl)
in (

let uu____7270 = (

let uu____7271 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "SMT pattern misses at least one bound variable: %s" uu____7271))
in (FStar_Errors.warn pos uu____7270)))
end)))
end)))
in (

let uu____7272 = (FStar_Syntax_Util.destruct_typ_as_formula phi)
in (match (uu____7272) with
| None -> begin
(fallback phi)
end
| Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(

let uu____7278 = (FStar_All.pipe_right connectives (FStar_List.tryFind (fun uu____7314 -> (match (uu____7314) with
| (l, uu____7324) -> begin
(FStar_Ident.lid_equals op l)
end))))
in (match (uu____7278) with
| None -> begin
(fallback phi)
end
| Some (uu____7347, f) -> begin
(f phi.FStar_Syntax_Syntax.pos arms)
end))
end
| Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____7376 = (encode_q_body env vars pats body)
in (match (uu____7376) with
| (vars, pats, guard, body, decls) -> begin
(

let tm = (

let uu____7402 = (

let uu____7408 = (FStar_SMTEncoding_Util.mkImp ((guard), (body)))
in ((pats), (vars), (uu____7408)))
in (FStar_SMTEncoding_Term.mkForall uu____7402 phi.FStar_Syntax_Syntax.pos))
in ((tm), (decls)))
end));
)
end
| Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____7420 = (encode_q_body env vars pats body)
in (match (uu____7420) with
| (vars, pats, guard, body, decls) -> begin
(

let uu____7445 = (

let uu____7446 = (

let uu____7452 = (FStar_SMTEncoding_Util.mkAnd ((guard), (body)))
in ((pats), (vars), (uu____7452)))
in (FStar_SMTEncoding_Term.mkExists uu____7446 phi.FStar_Syntax_Syntax.pos))
in ((uu____7445), (decls)))
end));
)
end))));
)))))))))))))))

type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list); is : FStar_Ident.lident  ->  Prims.bool}


let prims : prims_t = (

let uu____7501 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____7501) with
| (asym, a) -> begin
(

let uu____7506 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____7506) with
| (xsym, x) -> begin
(

let uu____7511 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____7511) with
| (ysym, y) -> begin
(

let quant = (fun vars body x -> (

let xname_decl = (

let uu____7541 = (

let uu____7547 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in ((x), (uu____7547), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (uu____7541))
in (

let xtok = (Prims.strcat x "@tok")
in (

let xtok_decl = FStar_SMTEncoding_Term.DeclFun (((xtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let xapp = (

let uu____7562 = (

let uu____7566 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((x), (uu____7566)))
in (FStar_SMTEncoding_Util.mkApp uu____7562))
in (

let xtok = (FStar_SMTEncoding_Util.mkApp ((xtok), ([])))
in (

let xtok_app = (mk_Apply xtok vars)
in (

let uu____7574 = (

let uu____7576 = (

let uu____7578 = (

let uu____7580 = (

let uu____7581 = (

let uu____7586 = (

let uu____7587 = (

let uu____7593 = (FStar_SMTEncoding_Util.mkEq ((xapp), (body)))
in ((((xapp)::[])::[]), (vars), (uu____7593)))
in (FStar_SMTEncoding_Util.mkForall uu____7587))
in ((uu____7586), (None), (Some ((Prims.strcat "primitive_" x)))))
in FStar_SMTEncoding_Term.Assume (uu____7581))
in (

let uu____7603 = (

let uu____7605 = (

let uu____7606 = (

let uu____7611 = (

let uu____7612 = (

let uu____7618 = (FStar_SMTEncoding_Util.mkEq ((xtok_app), (xapp)))
in ((((xtok_app)::[])::[]), (vars), (uu____7618)))
in (FStar_SMTEncoding_Util.mkForall uu____7612))
in ((uu____7611), (Some ("Name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" x)))))
in FStar_SMTEncoding_Term.Assume (uu____7606))
in (uu____7605)::[])
in (uu____7580)::uu____7603))
in (xtok_decl)::uu____7578)
in (xname_decl)::uu____7576)
in ((xtok), (uu____7574))))))))))
in (

let axy = (((asym), (FStar_SMTEncoding_Term.Term_sort)))::(((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let xy = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let qx = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let prims = (

let uu____7668 = (

let uu____7676 = (

let uu____7682 = (

let uu____7683 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7683))
in (quant axy uu____7682))
in ((FStar_Syntax_Const.op_Eq), (uu____7676)))
in (

let uu____7689 = (

let uu____7698 = (

let uu____7706 = (

let uu____7712 = (

let uu____7713 = (

let uu____7714 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_SMTEncoding_Util.mkNot uu____7714))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7713))
in (quant axy uu____7712))
in ((FStar_Syntax_Const.op_notEq), (uu____7706)))
in (

let uu____7720 = (

let uu____7729 = (

let uu____7737 = (

let uu____7743 = (

let uu____7744 = (

let uu____7745 = (

let uu____7748 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7749 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7748), (uu____7749))))
in (FStar_SMTEncoding_Util.mkLT uu____7745))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7744))
in (quant xy uu____7743))
in ((FStar_Syntax_Const.op_LT), (uu____7737)))
in (

let uu____7755 = (

let uu____7764 = (

let uu____7772 = (

let uu____7778 = (

let uu____7779 = (

let uu____7780 = (

let uu____7783 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7784 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7783), (uu____7784))))
in (FStar_SMTEncoding_Util.mkLTE uu____7780))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7779))
in (quant xy uu____7778))
in ((FStar_Syntax_Const.op_LTE), (uu____7772)))
in (

let uu____7790 = (

let uu____7799 = (

let uu____7807 = (

let uu____7813 = (

let uu____7814 = (

let uu____7815 = (

let uu____7818 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7819 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7818), (uu____7819))))
in (FStar_SMTEncoding_Util.mkGT uu____7815))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7814))
in (quant xy uu____7813))
in ((FStar_Syntax_Const.op_GT), (uu____7807)))
in (

let uu____7825 = (

let uu____7834 = (

let uu____7842 = (

let uu____7848 = (

let uu____7849 = (

let uu____7850 = (

let uu____7853 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7854 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7853), (uu____7854))))
in (FStar_SMTEncoding_Util.mkGTE uu____7850))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7849))
in (quant xy uu____7848))
in ((FStar_Syntax_Const.op_GTE), (uu____7842)))
in (

let uu____7860 = (

let uu____7869 = (

let uu____7877 = (

let uu____7883 = (

let uu____7884 = (

let uu____7885 = (

let uu____7888 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7889 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7888), (uu____7889))))
in (FStar_SMTEncoding_Util.mkSub uu____7885))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7884))
in (quant xy uu____7883))
in ((FStar_Syntax_Const.op_Subtraction), (uu____7877)))
in (

let uu____7895 = (

let uu____7904 = (

let uu____7912 = (

let uu____7918 = (

let uu____7919 = (

let uu____7920 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Util.mkMinus uu____7920))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7919))
in (quant qx uu____7918))
in ((FStar_Syntax_Const.op_Minus), (uu____7912)))
in (

let uu____7926 = (

let uu____7935 = (

let uu____7943 = (

let uu____7949 = (

let uu____7950 = (

let uu____7951 = (

let uu____7954 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7955 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7954), (uu____7955))))
in (FStar_SMTEncoding_Util.mkAdd uu____7951))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7950))
in (quant xy uu____7949))
in ((FStar_Syntax_Const.op_Addition), (uu____7943)))
in (

let uu____7961 = (

let uu____7970 = (

let uu____7978 = (

let uu____7984 = (

let uu____7985 = (

let uu____7986 = (

let uu____7989 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7990 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7989), (uu____7990))))
in (FStar_SMTEncoding_Util.mkMul uu____7986))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7985))
in (quant xy uu____7984))
in ((FStar_Syntax_Const.op_Multiply), (uu____7978)))
in (

let uu____7996 = (

let uu____8005 = (

let uu____8013 = (

let uu____8019 = (

let uu____8020 = (

let uu____8021 = (

let uu____8024 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____8025 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____8024), (uu____8025))))
in (FStar_SMTEncoding_Util.mkDiv uu____8021))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____8020))
in (quant xy uu____8019))
in ((FStar_Syntax_Const.op_Division), (uu____8013)))
in (

let uu____8031 = (

let uu____8040 = (

let uu____8048 = (

let uu____8054 = (

let uu____8055 = (

let uu____8056 = (

let uu____8059 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____8060 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____8059), (uu____8060))))
in (FStar_SMTEncoding_Util.mkMod uu____8056))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____8055))
in (quant xy uu____8054))
in ((FStar_Syntax_Const.op_Modulus), (uu____8048)))
in (

let uu____8066 = (

let uu____8075 = (

let uu____8083 = (

let uu____8089 = (

let uu____8090 = (

let uu____8091 = (

let uu____8094 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____8095 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____8094), (uu____8095))))
in (FStar_SMTEncoding_Util.mkAnd uu____8091))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____8090))
in (quant xy uu____8089))
in ((FStar_Syntax_Const.op_And), (uu____8083)))
in (

let uu____8101 = (

let uu____8110 = (

let uu____8118 = (

let uu____8124 = (

let uu____8125 = (

let uu____8126 = (

let uu____8129 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____8130 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____8129), (uu____8130))))
in (FStar_SMTEncoding_Util.mkOr uu____8126))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____8125))
in (quant xy uu____8124))
in ((FStar_Syntax_Const.op_Or), (uu____8118)))
in (

let uu____8136 = (

let uu____8145 = (

let uu____8153 = (

let uu____8159 = (

let uu____8160 = (

let uu____8161 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Util.mkNot uu____8161))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____8160))
in (quant qx uu____8159))
in ((FStar_Syntax_Const.op_Negation), (uu____8153)))
in (uu____8145)::[])
in (uu____8110)::uu____8136))
in (uu____8075)::uu____8101))
in (uu____8040)::uu____8066))
in (uu____8005)::uu____8031))
in (uu____7970)::uu____7996))
in (uu____7935)::uu____7961))
in (uu____7904)::uu____7926))
in (uu____7869)::uu____7895))
in (uu____7834)::uu____7860))
in (uu____7799)::uu____7825))
in (uu____7764)::uu____7790))
in (uu____7729)::uu____7755))
in (uu____7698)::uu____7720))
in (uu____7668)::uu____7689))
in (

let mk = (fun l v -> (

let uu____8289 = (

let uu____8294 = (FStar_All.pipe_right prims (FStar_List.find (fun uu____8326 -> (match (uu____8326) with
| (l', uu____8335) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right uu____8294 (FStar_Option.map (fun uu____8368 -> (match (uu____8368) with
| (uu____8379, b) -> begin
(b v)
end)))))
in (FStar_All.pipe_right uu____8289 FStar_Option.get)))
in (

let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun uu____8420 -> (match (uu____8420) with
| (l', uu____8429) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is})))))))
end))
end))
end))


let pretype_axiom : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun tapp vars -> (

let uu____8452 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____8452) with
| (xxsym, xx) -> begin
(

let uu____8457 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____8457) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let tapp_hash = (FStar_SMTEncoding_Term.hash_of_term tapp)
in (

let uu____8464 = (

let uu____8469 = (

let uu____8470 = (

let uu____8476 = (

let uu____8477 = (

let uu____8480 = (

let uu____8481 = (

let uu____8484 = (FStar_SMTEncoding_Util.mkApp (("PreType"), ((xx)::[])))
in ((tapp), (uu____8484)))
in (FStar_SMTEncoding_Util.mkEq uu____8481))
in ((xx_has_type), (uu____8480)))
in (FStar_SMTEncoding_Util.mkImp uu____8477))
in ((((xx_has_type)::[])::[]), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars), (uu____8476)))
in (FStar_SMTEncoding_Util.mkForall uu____8470))
in (

let uu____8497 = (

let uu____8499 = (

let uu____8500 = (

let uu____8501 = (FStar_Util.digest_of_string tapp_hash)
in (Prims.strcat "pretyping_" uu____8501))
in (varops.mk_unique uu____8500))
in Some (uu____8499))
in ((uu____8469), (Some ("pretyping")), (uu____8497))))
in FStar_SMTEncoding_Term.Assume (uu____8464))))
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

let uu____8532 = (

let uu____8533 = (

let uu____8538 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in ((uu____8538), (Some ("unit typing")), (Some ("unit_typing"))))
in FStar_SMTEncoding_Term.Assume (uu____8533))
in (

let uu____8541 = (

let uu____8543 = (

let uu____8544 = (

let uu____8549 = (

let uu____8550 = (

let uu____8556 = (

let uu____8557 = (

let uu____8560 = (FStar_SMTEncoding_Util.mkEq ((x), (FStar_SMTEncoding_Term.mk_Term_unit)))
in ((typing_pred), (uu____8560)))
in (FStar_SMTEncoding_Util.mkImp uu____8557))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____8556)))
in (mkForall_fuel uu____8550))
in ((uu____8549), (Some ("unit inversion")), (Some ("unit_inversion"))))
in FStar_SMTEncoding_Term.Assume (uu____8544))
in (uu____8543)::[])
in (uu____8532)::uu____8541))))
in (

let mk_bool = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Bool_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____8589 = (

let uu____8590 = (

let uu____8595 = (

let uu____8596 = (

let uu____8602 = (

let uu____8605 = (

let uu____8607 = (FStar_SMTEncoding_Term.boxBool b)
in (uu____8607)::[])
in (uu____8605)::[])
in (

let uu____8610 = (

let uu____8611 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType uu____8611 tt))
in ((uu____8602), ((bb)::[]), (uu____8610))))
in (FStar_SMTEncoding_Util.mkForall uu____8596))
in ((uu____8595), (Some ("bool typing")), (Some ("bool_typing"))))
in FStar_SMTEncoding_Term.Assume (uu____8590))
in (

let uu____8623 = (

let uu____8625 = (

let uu____8626 = (

let uu____8631 = (

let uu____8632 = (

let uu____8638 = (

let uu____8639 = (

let uu____8642 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in ((typing_pred), (uu____8642)))
in (FStar_SMTEncoding_Util.mkImp uu____8639))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____8638)))
in (mkForall_fuel uu____8632))
in ((uu____8631), (Some ("bool inversion")), (Some ("bool_inversion"))))
in FStar_SMTEncoding_Term.Assume (uu____8626))
in (uu____8625)::[])
in (uu____8589)::uu____8623))))))
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

let uu____8677 = (

let uu____8678 = (

let uu____8682 = (

let uu____8684 = (

let uu____8686 = (

let uu____8688 = (FStar_SMTEncoding_Term.boxInt a)
in (

let uu____8689 = (

let uu____8691 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____8691)::[])
in (uu____8688)::uu____8689))
in (tt)::uu____8686)
in (tt)::uu____8684)
in (("Prims.Precedes"), (uu____8682)))
in (FStar_SMTEncoding_Util.mkApp uu____8678))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8677))
in (

let precedes_y_x = (

let uu____8694 = (FStar_SMTEncoding_Util.mkApp (("Precedes"), ((y)::(x)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8694))
in (

let uu____8696 = (

let uu____8697 = (

let uu____8702 = (

let uu____8703 = (

let uu____8709 = (

let uu____8712 = (

let uu____8714 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____8714)::[])
in (uu____8712)::[])
in (

let uu____8717 = (

let uu____8718 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType uu____8718 tt))
in ((uu____8709), ((bb)::[]), (uu____8717))))
in (FStar_SMTEncoding_Util.mkForall uu____8703))
in ((uu____8702), (Some ("int typing")), (Some ("int_typing"))))
in FStar_SMTEncoding_Term.Assume (uu____8697))
in (

let uu____8730 = (

let uu____8732 = (

let uu____8733 = (

let uu____8738 = (

let uu____8739 = (

let uu____8745 = (

let uu____8746 = (

let uu____8749 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in ((typing_pred), (uu____8749)))
in (FStar_SMTEncoding_Util.mkImp uu____8746))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____8745)))
in (mkForall_fuel uu____8739))
in ((uu____8738), (Some ("int inversion")), (Some ("int_inversion"))))
in FStar_SMTEncoding_Term.Assume (uu____8733))
in (

let uu____8763 = (

let uu____8765 = (

let uu____8766 = (

let uu____8771 = (

let uu____8772 = (

let uu____8778 = (

let uu____8779 = (

let uu____8782 = (

let uu____8783 = (

let uu____8785 = (

let uu____8787 = (

let uu____8789 = (

let uu____8790 = (

let uu____8793 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____8794 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____8793), (uu____8794))))
in (FStar_SMTEncoding_Util.mkGT uu____8790))
in (

let uu____8795 = (

let uu____8797 = (

let uu____8798 = (

let uu____8801 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____8802 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____8801), (uu____8802))))
in (FStar_SMTEncoding_Util.mkGTE uu____8798))
in (

let uu____8803 = (

let uu____8805 = (

let uu____8806 = (

let uu____8809 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____8810 = (FStar_SMTEncoding_Term.unboxInt x)
in ((uu____8809), (uu____8810))))
in (FStar_SMTEncoding_Util.mkLT uu____8806))
in (uu____8805)::[])
in (uu____8797)::uu____8803))
in (uu____8789)::uu____8795))
in (typing_pred_y)::uu____8787)
in (typing_pred)::uu____8785)
in (FStar_SMTEncoding_Util.mk_and_l uu____8783))
in ((uu____8782), (precedes_y_x)))
in (FStar_SMTEncoding_Util.mkImp uu____8779))
in ((((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[]), ((xx)::(yy)::[]), (uu____8778)))
in (mkForall_fuel uu____8772))
in ((uu____8771), (Some ("well-founded ordering on nat (alt)")), (Some ("well-founded-ordering-on-nat"))))
in FStar_SMTEncoding_Term.Assume (uu____8766))
in (uu____8765)::[])
in (uu____8732)::uu____8763))
in (uu____8696)::uu____8730)))))))))))
in (

let mk_str = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.String_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____8841 = (

let uu____8842 = (

let uu____8847 = (

let uu____8848 = (

let uu____8854 = (

let uu____8857 = (

let uu____8859 = (FStar_SMTEncoding_Term.boxString b)
in (uu____8859)::[])
in (uu____8857)::[])
in (

let uu____8862 = (

let uu____8863 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType uu____8863 tt))
in ((uu____8854), ((bb)::[]), (uu____8862))))
in (FStar_SMTEncoding_Util.mkForall uu____8848))
in ((uu____8847), (Some ("string typing")), (Some ("string_typing"))))
in FStar_SMTEncoding_Term.Assume (uu____8842))
in (

let uu____8875 = (

let uu____8877 = (

let uu____8878 = (

let uu____8883 = (

let uu____8884 = (

let uu____8890 = (

let uu____8891 = (

let uu____8894 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in ((typing_pred), (uu____8894)))
in (FStar_SMTEncoding_Util.mkImp uu____8891))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____8890)))
in (mkForall_fuel uu____8884))
in ((uu____8883), (Some ("string inversion")), (Some ("string_inversion"))))
in FStar_SMTEncoding_Term.Assume (uu____8878))
in (uu____8877)::[])
in (uu____8841)::uu____8875))))))
in (

let mk_ref = (fun env reft_name uu____8917 -> (

let r = (("r"), (FStar_SMTEncoding_Term.Ref_sort))
in (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let refa = (

let uu____8928 = (

let uu____8932 = (

let uu____8934 = (FStar_SMTEncoding_Util.mkFreeV aa)
in (uu____8934)::[])
in ((reft_name), (uu____8932)))
in (FStar_SMTEncoding_Util.mkApp uu____8928))
in (

let refb = (

let uu____8937 = (

let uu____8941 = (

let uu____8943 = (FStar_SMTEncoding_Util.mkFreeV bb)
in (uu____8943)::[])
in ((reft_name), (uu____8941)))
in (FStar_SMTEncoding_Util.mkApp uu____8937))
in (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (

let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (

let uu____8947 = (

let uu____8948 = (

let uu____8953 = (

let uu____8954 = (

let uu____8960 = (

let uu____8961 = (

let uu____8964 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in ((typing_pred), (uu____8964)))
in (FStar_SMTEncoding_Util.mkImp uu____8961))
in ((((typing_pred)::[])::[]), ((xx)::(aa)::[]), (uu____8960)))
in (mkForall_fuel uu____8954))
in ((uu____8953), (Some ("ref inversion")), (Some ("ref_inversion"))))
in FStar_SMTEncoding_Term.Assume (uu____8948))
in (

let uu____8980 = (

let uu____8982 = (

let uu____8983 = (

let uu____8988 = (

let uu____8989 = (

let uu____8995 = (

let uu____8996 = (

let uu____8999 = (FStar_SMTEncoding_Util.mkAnd ((typing_pred), (typing_pred_b)))
in (

let uu____9000 = (

let uu____9001 = (

let uu____9004 = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let uu____9005 = (FStar_SMTEncoding_Util.mkFreeV bb)
in ((uu____9004), (uu____9005))))
in (FStar_SMTEncoding_Util.mkEq uu____9001))
in ((uu____8999), (uu____9000))))
in (FStar_SMTEncoding_Util.mkImp uu____8996))
in ((((typing_pred)::(typing_pred_b)::[])::[]), ((xx)::(aa)::(bb)::[]), (uu____8995)))
in (mkForall_fuel' (Prims.parse_int "2") uu____8989))
in ((uu____8988), (Some ("ref typing is injective")), (Some ("ref_injectivity"))))
in FStar_SMTEncoding_Term.Assume (uu____8983))
in (uu____8982)::[])
in (uu____8947)::uu____8980))))))))))
in (

let mk_true_interp = (fun env nm true_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((true_tm)::[])))
in (FStar_SMTEncoding_Term.Assume (((valid), (Some ("True interpretation")), (Some ("true_interp")))))::[]))
in (

let mk_false_interp = (fun env nm false_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((false_tm)::[])))
in (

let uu____9049 = (

let uu____9050 = (

let uu____9055 = (FStar_SMTEncoding_Util.mkIff ((FStar_SMTEncoding_Util.mkFalse), (valid)))
in ((uu____9055), (Some ("False interpretation")), (Some ("false_interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9050))
in (uu____9049)::[])))
in (

let mk_and_interp = (fun env conj uu____9067 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let valid = (

let uu____9077 = (

let uu____9081 = (

let uu____9083 = (FStar_SMTEncoding_Util.mkApp ((conj), ((a)::(b)::[])))
in (uu____9083)::[])
in (("Valid"), (uu____9081)))
in (FStar_SMTEncoding_Util.mkApp uu____9077))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____9090 = (

let uu____9091 = (

let uu____9096 = (

let uu____9097 = (

let uu____9103 = (

let uu____9104 = (

let uu____9107 = (FStar_SMTEncoding_Util.mkAnd ((valid_a), (valid_b)))
in ((uu____9107), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9104))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9103)))
in (FStar_SMTEncoding_Util.mkForall uu____9097))
in ((uu____9096), (Some ("/\\ interpretation")), (Some ("l_and-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9091))
in (uu____9090)::[])))))))))
in (

let mk_or_interp = (fun env disj uu____9132 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let valid = (

let uu____9142 = (

let uu____9146 = (

let uu____9148 = (FStar_SMTEncoding_Util.mkApp ((disj), ((a)::(b)::[])))
in (uu____9148)::[])
in (("Valid"), (uu____9146)))
in (FStar_SMTEncoding_Util.mkApp uu____9142))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____9155 = (

let uu____9156 = (

let uu____9161 = (

let uu____9162 = (

let uu____9168 = (

let uu____9169 = (

let uu____9172 = (FStar_SMTEncoding_Util.mkOr ((valid_a), (valid_b)))
in ((uu____9172), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9169))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9168)))
in (FStar_SMTEncoding_Util.mkForall uu____9162))
in ((uu____9161), (Some ("\\/ interpretation")), (Some ("l_or-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9156))
in (uu____9155)::[])))))))))
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

let uu____9211 = (

let uu____9215 = (

let uu____9217 = (FStar_SMTEncoding_Util.mkApp ((eq2), ((a)::(x)::(y)::[])))
in (uu____9217)::[])
in (("Valid"), (uu____9215)))
in (FStar_SMTEncoding_Util.mkApp uu____9211))
in (

let uu____9220 = (

let uu____9221 = (

let uu____9226 = (

let uu____9227 = (

let uu____9233 = (

let uu____9234 = (

let uu____9237 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in ((uu____9237), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9234))
in ((((valid)::[])::[]), ((aa)::(xx)::(yy)::[]), (uu____9233)))
in (FStar_SMTEncoding_Util.mkForall uu____9227))
in ((uu____9226), (Some ("Eq2 interpretation")), (Some ("eq2-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9221))
in (uu____9220)::[])))))))))
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

let uu____9282 = (

let uu____9286 = (

let uu____9288 = (FStar_SMTEncoding_Util.mkApp ((eq3), ((a)::(b)::(x)::(y)::[])))
in (uu____9288)::[])
in (("Valid"), (uu____9286)))
in (FStar_SMTEncoding_Util.mkApp uu____9282))
in (

let uu____9291 = (

let uu____9292 = (

let uu____9297 = (

let uu____9298 = (

let uu____9304 = (

let uu____9305 = (

let uu____9308 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in ((uu____9308), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9305))
in ((((valid)::[])::[]), ((aa)::(bb)::(xx)::(yy)::[]), (uu____9304)))
in (FStar_SMTEncoding_Util.mkForall uu____9298))
in ((uu____9297), (Some ("Eq3 interpretation")), (Some ("eq3-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9292))
in (uu____9291)::[])))))))))))
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

let uu____9347 = (

let uu____9351 = (

let uu____9353 = (FStar_SMTEncoding_Util.mkApp ((imp), ((a)::(b)::[])))
in (uu____9353)::[])
in (("Valid"), (uu____9351)))
in (FStar_SMTEncoding_Util.mkApp uu____9347))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____9360 = (

let uu____9361 = (

let uu____9366 = (

let uu____9367 = (

let uu____9373 = (

let uu____9374 = (

let uu____9377 = (FStar_SMTEncoding_Util.mkImp ((valid_a), (valid_b)))
in ((uu____9377), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9374))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9373)))
in (FStar_SMTEncoding_Util.mkForall uu____9367))
in ((uu____9366), (Some ("==> interpretation")), (Some ("l_imp-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9361))
in (uu____9360)::[])))))))))
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

let uu____9412 = (

let uu____9416 = (

let uu____9418 = (FStar_SMTEncoding_Util.mkApp ((iff), ((a)::(b)::[])))
in (uu____9418)::[])
in (("Valid"), (uu____9416)))
in (FStar_SMTEncoding_Util.mkApp uu____9412))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____9425 = (

let uu____9426 = (

let uu____9431 = (

let uu____9432 = (

let uu____9438 = (

let uu____9439 = (

let uu____9442 = (FStar_SMTEncoding_Util.mkIff ((valid_a), (valid_b)))
in ((uu____9442), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9439))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9438)))
in (FStar_SMTEncoding_Util.mkForall uu____9432))
in ((uu____9431), (Some ("<==> interpretation")), (Some ("l_iff-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9426))
in (uu____9425)::[])))))))))
in (

let mk_not_interp = (fun env l_not tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let valid = (

let uu____9473 = (

let uu____9477 = (

let uu____9479 = (FStar_SMTEncoding_Util.mkApp ((l_not), ((a)::[])))
in (uu____9479)::[])
in (("Valid"), (uu____9477)))
in (FStar_SMTEncoding_Util.mkApp uu____9473))
in (

let not_valid_a = (

let uu____9483 = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9483))
in (

let uu____9485 = (

let uu____9486 = (

let uu____9491 = (

let uu____9492 = (

let uu____9498 = (FStar_SMTEncoding_Util.mkIff ((not_valid_a), (valid)))
in ((((valid)::[])::[]), ((aa)::[]), (uu____9498)))
in (FStar_SMTEncoding_Util.mkForall uu____9492))
in ((uu____9491), (Some ("not interpretation")), (Some ("l_not-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9486))
in (uu____9485)::[]))))))
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

let uu____9535 = (

let uu____9539 = (

let uu____9541 = (FStar_SMTEncoding_Util.mkApp ((for_all), ((a)::(b)::[])))
in (uu____9541)::[])
in (("Valid"), (uu____9539)))
in (FStar_SMTEncoding_Util.mkApp uu____9535))
in (

let valid_b_x = (

let uu____9545 = (

let uu____9549 = (

let uu____9551 = (FStar_SMTEncoding_Util.mk_ApplyTT b x)
in (uu____9551)::[])
in (("Valid"), (uu____9549)))
in (FStar_SMTEncoding_Util.mkApp uu____9545))
in (

let uu____9553 = (

let uu____9554 = (

let uu____9559 = (

let uu____9560 = (

let uu____9566 = (

let uu____9567 = (

let uu____9570 = (

let uu____9571 = (

let uu____9577 = (

let uu____9580 = (

let uu____9582 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (uu____9582)::[])
in (uu____9580)::[])
in (

let uu____9585 = (

let uu____9586 = (

let uu____9589 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((uu____9589), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp uu____9586))
in ((uu____9577), ((xx)::[]), (uu____9585))))
in (FStar_SMTEncoding_Util.mkForall uu____9571))
in ((uu____9570), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9567))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9566)))
in (FStar_SMTEncoding_Util.mkForall uu____9560))
in ((uu____9559), (Some ("forall interpretation")), (Some ("forall-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9554))
in (uu____9553)::[]))))))))))
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

let uu____9637 = (

let uu____9641 = (

let uu____9643 = (FStar_SMTEncoding_Util.mkApp ((for_some), ((a)::(b)::[])))
in (uu____9643)::[])
in (("Valid"), (uu____9641)))
in (FStar_SMTEncoding_Util.mkApp uu____9637))
in (

let valid_b_x = (

let uu____9647 = (

let uu____9651 = (

let uu____9653 = (FStar_SMTEncoding_Util.mk_ApplyTT b x)
in (uu____9653)::[])
in (("Valid"), (uu____9651)))
in (FStar_SMTEncoding_Util.mkApp uu____9647))
in (

let uu____9655 = (

let uu____9656 = (

let uu____9661 = (

let uu____9662 = (

let uu____9668 = (

let uu____9669 = (

let uu____9672 = (

let uu____9673 = (

let uu____9679 = (

let uu____9682 = (

let uu____9684 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (uu____9684)::[])
in (uu____9682)::[])
in (

let uu____9687 = (

let uu____9688 = (

let uu____9691 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((uu____9691), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp uu____9688))
in ((uu____9679), ((xx)::[]), (uu____9687))))
in (FStar_SMTEncoding_Util.mkExists uu____9673))
in ((uu____9672), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9669))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9668)))
in (FStar_SMTEncoding_Util.mkForall uu____9662))
in ((uu____9661), (Some ("exists interpretation")), (Some ("exists-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9656))
in (uu____9655)::[]))))))))))
in (

let mk_range_interp = (fun env range tt -> (

let range_ty = (FStar_SMTEncoding_Util.mkApp ((range), ([])))
in (

let uu____9728 = (

let uu____9729 = (

let uu____9734 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_ty)
in (

let uu____9735 = (

let uu____9737 = (varops.mk_unique "typing_range_const")
in Some (uu____9737))
in ((uu____9734), (Some ("Range_const typing")), (uu____9735))))
in FStar_SMTEncoding_Term.Assume (uu____9729))
in (uu____9728)::[])))
in (

let prims = (((FStar_Syntax_Const.unit_lid), (mk_unit)))::(((FStar_Syntax_Const.bool_lid), (mk_bool)))::(((FStar_Syntax_Const.int_lid), (mk_int)))::(((FStar_Syntax_Const.string_lid), (mk_str)))::(((FStar_Syntax_Const.ref_lid), (mk_ref)))::(((FStar_Syntax_Const.true_lid), (mk_true_interp)))::(((FStar_Syntax_Const.false_lid), (mk_false_interp)))::(((FStar_Syntax_Const.and_lid), (mk_and_interp)))::(((FStar_Syntax_Const.or_lid), (mk_or_interp)))::(((FStar_Syntax_Const.eq2_lid), (mk_eq2_interp)))::(((FStar_Syntax_Const.eq3_lid), (mk_eq3_interp)))::(((FStar_Syntax_Const.imp_lid), (mk_imp_interp)))::(((FStar_Syntax_Const.iff_lid), (mk_iff_interp)))::(((FStar_Syntax_Const.not_lid), (mk_not_interp)))::(((FStar_Syntax_Const.forall_lid), (mk_forall_interp)))::(((FStar_Syntax_Const.exists_lid), (mk_exists_interp)))::(((FStar_Syntax_Const.range_lid), (mk_range_interp)))::[]
in (fun env t s tt -> (

let uu____10000 = (FStar_Util.find_opt (fun uu____10018 -> (match (uu____10018) with
| (l, uu____10028) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)
in (match (uu____10000) with
| None -> begin
[]
end
| Some (uu____10050, f) -> begin
(f env s tt)
end)))))))))))))))))))))))))


let encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____10087 = (encode_function_type_as_formula None None t env)
in (match (uu____10087) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_SMTEncoding_Term.Assume (((form), (Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str))), (Some ((Prims.strcat "lemma_" lid.FStar_Ident.str))))))::[]))
end))))


let encode_free_var : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env fv tt t_norm quals -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____10120 = ((

let uu____10121 = ((FStar_Syntax_Util.is_pure_or_ghost_function t_norm) || (is_reifiable_function env.tcenv t_norm))
in (FStar_All.pipe_left Prims.op_Negation uu____10121)) || (FStar_Syntax_Util.is_lemma t_norm))
in (match (uu____10120) with
| true -> begin
(

let uu____10125 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____10125) with
| (vname, vtok, env) -> begin
(

let arg_sorts = (

let uu____10137 = (

let uu____10138 = (FStar_Syntax_Subst.compress t_norm)
in uu____10138.FStar_Syntax_Syntax.n)
in (match (uu____10137) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____10143) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun uu____10160 -> FStar_SMTEncoding_Term.Term_sort)))
end
| uu____10163 -> begin
[]
end))
in (

let d = FStar_SMTEncoding_Term.DeclFun (((vname), (arg_sorts), (FStar_SMTEncoding_Term.Term_sort), (Some ("Uninterpreted function symbol for impure function"))))
in (

let dd = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Uninterpreted name for impure function"))))
in (((d)::(dd)::[]), (env)))))
end))
end
| uu____10171 -> begin
(

let uu____10172 = (prims.is lid)
in (match (uu____10172) with
| true -> begin
(

let vname = (varops.new_fvar lid)
in (

let uu____10177 = (prims.mk lid vname)
in (match (uu____10177) with
| (tok, definition) -> begin
(

let env = (push_free_var env lid vname (Some (tok)))
in ((definition), (env)))
end)))
end
| uu____10190 -> begin
(

let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (

let uu____10192 = (

let uu____10198 = (curried_arrow_formals_comp t_norm)
in (match (uu____10198) with
| (args, comp) -> begin
(

let comp = (

let uu____10209 = (is_reifiable_comp env.tcenv comp)
in (match (uu____10209) with
| true -> begin
(

let uu____10210 = (FStar_TypeChecker_Util.reify_comp (

let uu___152_10211 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___152_10211.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___152_10211.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___152_10211.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___152_10211.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___152_10211.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___152_10211.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___152_10211.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___152_10211.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___152_10211.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___152_10211.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___152_10211.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___152_10211.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___152_10211.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___152_10211.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___152_10211.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___152_10211.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___152_10211.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___152_10211.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___152_10211.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___152_10211.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___152_10211.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___152_10211.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___152_10211.FStar_TypeChecker_Env.qname_and_index}) (FStar_Syntax_Util.lcomp_of_comp comp) FStar_Syntax_Syntax.U_unknown)
in (FStar_Syntax_Syntax.mk_Total uu____10210))
end
| uu____10212 -> begin
comp
end))
in (match (encode_non_total_function_typ) with
| true -> begin
(

let uu____10218 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in ((args), (uu____10218)))
end
| uu____10225 -> begin
((args), (((None), ((FStar_Syntax_Util.comp_result comp)))))
end))
end))
in (match (uu____10192) with
| (formals, (pre_opt, res_t)) -> begin
(

let uu____10245 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____10245) with
| (vname, vtok, env) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
end
| uu____10258 -> begin
(FStar_SMTEncoding_Util.mkApp ((vtok), ([])))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun uu___123_10282 -> (match (uu___123_10282) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(

let uu____10285 = (FStar_Util.prefix vars)
in (match (uu____10285) with
| (uu____10296, (xxsym, uu____10298)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____10308 = (

let uu____10309 = (

let uu____10314 = (

let uu____10315 = (

let uu____10321 = (

let uu____10322 = (

let uu____10325 = (

let uu____10326 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____10326))
in ((vapp), (uu____10325)))
in (FStar_SMTEncoding_Util.mkEq uu____10322))
in ((((vapp)::[])::[]), (vars), (uu____10321)))
in (FStar_SMTEncoding_Util.mkForall uu____10315))
in ((uu____10314), (Some ("Discriminator equation")), (Some ((Prims.strcat "disc_equation_" (escape d.FStar_Ident.str))))))
in FStar_SMTEncoding_Term.Assume (uu____10309))
in (uu____10308)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(

let uu____10338 = (FStar_Util.prefix vars)
in (match (uu____10338) with
| (uu____10349, (xxsym, uu____10351)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (

let tp_name = (mk_term_projector_name d f)
in (

let prim_app = (FStar_SMTEncoding_Util.mkApp ((tp_name), ((xx)::[])))
in (

let uu____10365 = (

let uu____10366 = (

let uu____10371 = (

let uu____10372 = (

let uu____10378 = (FStar_SMTEncoding_Util.mkEq ((vapp), (prim_app)))
in ((((vapp)::[])::[]), (vars), (uu____10378)))
in (FStar_SMTEncoding_Util.mkForall uu____10372))
in ((uu____10371), (Some ("Projector equation")), (Some ((Prims.strcat "proj_equation_" tp_name)))))
in FStar_SMTEncoding_Term.Assume (uu____10366))
in (uu____10365)::[])))))
end))
end
| uu____10388 -> begin
[]
end)))))
in (

let uu____10389 = (encode_binders None formals env)
in (match (uu____10389) with
| (vars, guards, env', decls1, uu____10405) -> begin
(

let uu____10412 = (match (pre_opt) with
| None -> begin
(

let uu____10417 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____10417), (decls1)))
end
| Some (p) -> begin
(

let uu____10419 = (encode_formula p env')
in (match (uu____10419) with
| (g, ds) -> begin
(

let uu____10426 = (FStar_SMTEncoding_Util.mk_and_l ((g)::guards))
in ((uu____10426), ((FStar_List.append decls1 ds))))
end))
end)
in (match (uu____10412) with
| (guard, decls1) -> begin
(

let vtok_app = (mk_Apply vtok_tm vars)
in (

let vapp = (

let uu____10435 = (

let uu____10439 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((vname), (uu____10439)))
in (FStar_SMTEncoding_Util.mkApp uu____10435))
in (

let uu____10444 = (

let vname_decl = (

let uu____10449 = (

let uu____10455 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____10460 -> FStar_SMTEncoding_Term.Term_sort)))
in ((vname), (uu____10455), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (uu____10449))
in (

let uu____10465 = (

let env = (

let uu___153_10469 = env
in {bindings = uu___153_10469.bindings; depth = uu___153_10469.depth; tcenv = uu___153_10469.tcenv; warn = uu___153_10469.warn; cache = uu___153_10469.cache; nolabels = uu___153_10469.nolabels; use_zfuel_name = uu___153_10469.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in (

let uu____10470 = (

let uu____10471 = (head_normal env tt)
in (not (uu____10471)))
in (match (uu____10470) with
| true -> begin
(encode_term_pred None tt env vtok_tm)
end
| uu____10474 -> begin
(encode_term_pred None t_norm env vtok_tm)
end)))
in (match (uu____10465) with
| (tok_typing, decls2) -> begin
(

let tok_typing = FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("function token typing")), (Some ((Prims.strcat "function_token_typing_" vname)))))
in (

let uu____10483 = (match (formals) with
| [] -> begin
(

let uu____10492 = (

let uu____10493 = (

let uu____10495 = (FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left (fun _0_34 -> Some (_0_34)) uu____10495))
in (push_free_var env lid vname uu____10493))
in (((FStar_List.append decls2 ((tok_typing)::[]))), (uu____10492)))
end
| uu____10498 -> begin
(

let vtok_decl = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let vtok_fresh = (

let uu____10503 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((vtok), (FStar_SMTEncoding_Term.Term_sort)) uu____10503))
in (

let name_tok_corr = (

let uu____10505 = (

let uu____10510 = (

let uu____10511 = (

let uu____10517 = (FStar_SMTEncoding_Util.mkEq ((vtok_app), (vapp)))
in ((((vtok_app)::[])::((vapp)::[])::[]), (vars), (uu____10517)))
in (FStar_SMTEncoding_Util.mkForall uu____10511))
in ((uu____10510), (Some ("Name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" vname)))))
in FStar_SMTEncoding_Term.Assume (uu____10505))
in (((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[]))), (env)))))
end)
in (match (uu____10483) with
| (tok_decl, env) -> begin
(((vname_decl)::tok_decl), (env))
end)))
end)))
in (match (uu____10444) with
| (decls2, env) -> begin
(

let uu____10542 = (

let res_t = (FStar_Syntax_Subst.compress res_t)
in (

let uu____10547 = (encode_term res_t env')
in (match (uu____10547) with
| (encoded_res_t, decls) -> begin
(

let uu____10555 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in ((encoded_res_t), (uu____10555), (decls)))
end)))
in (match (uu____10542) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (

let uu____10563 = (

let uu____10568 = (

let uu____10569 = (

let uu____10575 = (FStar_SMTEncoding_Util.mkImp ((guard), (ty_pred)))
in ((((vapp)::[])::[]), (vars), (uu____10575)))
in (FStar_SMTEncoding_Util.mkForall uu____10569))
in ((uu____10568), (Some ("free var typing")), (Some ((Prims.strcat "typing_" vname)))))
in FStar_SMTEncoding_Term.Assume (uu____10563))
in (

let freshness = (

let uu____10585 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New))
in (match (uu____10585) with
| true -> begin
(

let uu____10588 = (

let uu____10589 = (

let uu____10595 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (

let uu____10601 = (varops.next_id ())
in ((vname), (uu____10595), (FStar_SMTEncoding_Term.Term_sort), (uu____10601))))
in (FStar_SMTEncoding_Term.fresh_constructor uu____10589))
in (

let uu____10603 = (

let uu____10605 = (pretype_axiom vapp vars)
in (uu____10605)::[])
in (uu____10588)::uu____10603))
end
| uu____10606 -> begin
[]
end))
in (

let g = (

let uu____10609 = (

let uu____10611 = (

let uu____10613 = (

let uu____10615 = (

let uu____10617 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::uu____10617)
in (FStar_List.append freshness uu____10615))
in (FStar_List.append decls3 uu____10613))
in (FStar_List.append decls2 uu____10611))
in (FStar_List.append decls1 uu____10609))
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

let uu____10639 = (try_lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____10639) with
| None -> begin
(

let uu____10662 = (encode_free_var env x t t_norm [])
in (match (uu____10662) with
| (decls, env) -> begin
(

let uu____10677 = (lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____10677) with
| (n, x', uu____10696) -> begin
((((n), (x'))), (decls), (env))
end))
end))
end
| Some (n, x, uu____10708) -> begin
((((n), (x))), ([]), (env))
end)))


let encode_top_level_val : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env lid t quals -> (

let tt = (norm env t)
in (

let uu____10741 = (encode_free_var env lid t tt quals)
in (match (uu____10741) with
| (decls, env) -> begin
(

let uu____10752 = (FStar_Syntax_Util.is_smt_lemma t)
in (match (uu____10752) with
| true -> begin
(

let uu____10756 = (

let uu____10758 = (encode_smt_lemma env lid tt)
in (FStar_List.append decls uu____10758))
in ((uu____10756), (env)))
end
| uu____10761 -> begin
((decls), (env))
end))
end))))


let encode_top_level_vals : env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____10786 lb -> (match (uu____10786) with
| (decls, env) -> begin
(

let uu____10798 = (

let uu____10802 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env uu____10802 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (uu____10798) with
| (decls', env) -> begin
(((FStar_List.append decls decls')), (env))
end))
end)) (([]), (env)))))


let encode_top_level_let : env_t  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env uu____10826 quals -> (match (uu____10826) with
| (is_rec, bindings) -> begin
(

let eta_expand = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let uu____10875 = (FStar_Util.first_N nbinders formals)
in (match (uu____10875) with
| (formals, extra_formals) -> begin
(

let subst = (FStar_List.map2 (fun uu____10915 uu____10916 -> (match (((uu____10915), (uu____10916))) with
| ((formal, uu____10926), (binder, uu____10928)) -> begin
(

let uu____10933 = (

let uu____10938 = (FStar_Syntax_Syntax.bv_to_name binder)
in ((formal), (uu____10938)))
in FStar_Syntax_Syntax.NT (uu____10933))
end)) formals binders)
in (

let extra_formals = (

let uu____10943 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun uu____10957 -> (match (uu____10957) with
| (x, i) -> begin
(

let uu____10964 = (

let uu___154_10965 = x
in (

let uu____10966 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___154_10965.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___154_10965.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____10966}))
in ((uu____10964), (i)))
end))))
in (FStar_All.pipe_right uu____10943 FStar_Syntax_Util.name_binders))
in (

let body = (

let uu____10978 = (

let uu____10980 = (

let uu____10981 = (FStar_Syntax_Subst.subst subst t)
in uu____10981.FStar_Syntax_Syntax.n)
in (FStar_All.pipe_left (fun _0_35 -> Some (_0_35)) uu____10980))
in (

let uu____10985 = (

let uu____10986 = (FStar_Syntax_Subst.compress body)
in (

let uu____10987 = (

let uu____10988 = (FStar_Syntax_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd uu____10988))
in (FStar_Syntax_Syntax.extend_app_n uu____10986 uu____10987)))
in (uu____10985 uu____10978 body.FStar_Syntax_Syntax.pos)))
in (((FStar_List.append binders extra_formals)), (body)))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (

let rec aux = (fun norm t_norm -> (

let uu____11045 = (FStar_Syntax_Util.abs_formals e)
in (match (uu____11045) with
| (binders, body, lopt) -> begin
(match (binders) with
| (uu____11094)::uu____11095 -> begin
(

let uu____11103 = (

let uu____11104 = (FStar_Syntax_Subst.compress t_norm)
in uu____11104.FStar_Syntax_Syntax.n)
in (match (uu____11103) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____11131 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____11131) with
| (formals, c) -> begin
(

let nformals = (FStar_List.length formals)
in (

let nbinders = (FStar_List.length binders)
in (

let get_result_type = (fun c -> (

let uu____11160 = (is_reifiable_comp env.tcenv c)
in (match (uu____11160) with
| true -> begin
(FStar_TypeChecker_Util.reify_comp (

let uu___155_11161 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___155_11161.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___155_11161.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___155_11161.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___155_11161.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___155_11161.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___155_11161.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___155_11161.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___155_11161.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___155_11161.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___155_11161.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___155_11161.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___155_11161.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___155_11161.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___155_11161.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___155_11161.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___155_11161.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___155_11161.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___155_11161.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___155_11161.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___155_11161.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___155_11161.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___155_11161.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___155_11161.FStar_TypeChecker_Env.qname_and_index}) (FStar_Syntax_Util.lcomp_of_comp c) FStar_Syntax_Syntax.U_unknown)
end
| uu____11162 -> begin
(FStar_Syntax_Util.comp_result c)
end)))
in (

let tres = (get_result_type c)
in (

let uu____11164 = ((nformals < nbinders) && (FStar_Syntax_Util.is_total_comp c))
in (match (uu____11164) with
| true -> begin
(

let uu____11182 = (FStar_Util.first_N nformals binders)
in (match (uu____11182) with
| (bs0, rest) -> begin
(

let c = (

let subst = (FStar_List.map2 (fun uu____11228 uu____11229 -> (match (((uu____11228), (uu____11229))) with
| ((x, uu____11239), (b, uu____11241)) -> begin
(

let uu____11246 = (

let uu____11251 = (FStar_Syntax_Syntax.bv_to_name b)
in ((x), (uu____11251)))
in FStar_Syntax_Syntax.NT (uu____11246))
end)) formals bs0)
in (FStar_Syntax_Subst.subst_comp subst c))
in (

let body = (FStar_Syntax_Util.abs rest body lopt)
in (

let uu____11253 = (

let uu____11264 = (get_result_type c)
in ((bs0), (body), (bs0), (uu____11264)))
in ((uu____11253), (false)))))
end))
end
| uu____11281 -> begin
(match ((nformals > nbinders)) with
| true -> begin
(

let uu____11299 = (eta_expand binders formals body tres)
in (match (uu____11299) with
| (binders, body) -> begin
((((binders), (body), (formals), (tres))), (false))
end))
end
| uu____11345 -> begin
((((binders), (body), (formals), (tres))), (false))
end)
end))))))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____11351) -> begin
(

let uu____11356 = (

let uu____11367 = (aux norm x.FStar_Syntax_Syntax.sort)
in (Prims.fst uu____11367))
in ((uu____11356), (true)))
end
| uu____11400 when (not (norm)) -> begin
(

let t_norm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm)
in (aux true t_norm))
end
| uu____11402 -> begin
(

let uu____11403 = (

let uu____11404 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____11405 = (FStar_Syntax_Print.term_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str uu____11404 uu____11405)))
in (failwith uu____11403))
end))
end
| uu____11418 -> begin
(

let uu____11419 = (

let uu____11420 = (FStar_Syntax_Subst.compress t_norm)
in uu____11420.FStar_Syntax_Syntax.n)
in (match (uu____11419) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____11447 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____11447) with
| (formals, c) -> begin
(

let tres = (FStar_Syntax_Util.comp_result c)
in (

let uu____11467 = (eta_expand [] formals e tres)
in (match (uu____11467) with
| (binders, body) -> begin
((((binders), (body), (formals), (tres))), (false))
end)))
end))
end
| uu____11519 -> begin
(((([]), (e), ([]), (t_norm))), (false))
end))
end)
end)))
in (aux false t_norm)))
in try
(match (()) with
| () -> begin
(

let uu____11547 = (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp))))
in (match (uu____11547) with
| true -> begin
(encode_top_level_vals env bindings quals)
end
| uu____11553 -> begin
(

let uu____11554 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____11595 lb -> (match (uu____11595) with
| (toks, typs, decls, env) -> begin
((

let uu____11646 = (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp)
in (match (uu____11646) with
| true -> begin
(Prims.raise Let_rec_unencodeable)
end
| uu____11647 -> begin
()
end));
(

let t_norm = (whnf env lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____11649 = (

let uu____11657 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env uu____11657 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (uu____11649) with
| (tok, decl, env) -> begin
(

let uu____11682 = (

let uu____11689 = (

let uu____11695 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in ((uu____11695), (tok)))
in (uu____11689)::toks)
in ((uu____11682), ((t_norm)::typs), ((decl)::decls), (env)))
end)));
)
end)) (([]), ([]), ([]), (env))))
in (match (uu____11554) with
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
| uu____11797 -> begin
(match (curry) with
| true -> begin
(match (ftok) with
| Some (ftok) -> begin
(mk_Apply ftok vars)
end
| None -> begin
(

let uu____11802 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply uu____11802 vars))
end)
end
| uu____11803 -> begin
(

let uu____11804 = (

let uu____11808 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (uu____11808)))
in (FStar_SMTEncoding_Util.mkApp uu____11804))
end)
end))
in (

let uu____11813 = ((FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___124_11815 -> (match (uu___124_11815) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| uu____11816 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> (

let uu____11819 = ((FStar_Syntax_Util.is_pure_or_ghost_function t) || (is_reifiable_function env.tcenv t))
in (FStar_All.pipe_left Prims.op_Negation uu____11819))))))
in (match (uu____11813) with
| true -> begin
((decls), (env))
end
| uu____11824 -> begin
(match ((not (is_rec))) with
| true -> begin
(match (((bindings), (typs), (toks))) with
| (({FStar_Syntax_Syntax.lbname = uu____11839; FStar_Syntax_Syntax.lbunivs = uu____11840; FStar_Syntax_Syntax.lbtyp = uu____11841; FStar_Syntax_Syntax.lbeff = uu____11842; FStar_Syntax_Syntax.lbdef = e})::[], (t_norm)::[], ((flid_fv, (f, ftok)))::[]) -> begin
(

let e = (FStar_Syntax_Subst.compress e)
in (

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____11884 = (destruct_bound_function flid t_norm e)
in (match (uu____11884) with
| ((binders, body, uu____11896, uu____11897), curry) -> begin
((

let uu____11904 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____11904) with
| true -> begin
(

let uu____11905 = (FStar_Syntax_Print.binders_to_string ", " binders)
in (

let uu____11906 = (FStar_Syntax_Print.term_to_string body)
in (FStar_Util.print2 "Encoding let : binders=[%s], body=%s\n" uu____11905 uu____11906)))
end
| uu____11907 -> begin
()
end));
(

let uu____11908 = (encode_binders None binders env)
in (match (uu____11908) with
| (vars, guards, env', binder_decls, uu____11924) -> begin
(

let body = (

let uu____11932 = (is_reifiable_function env'.tcenv t_norm)
in (match (uu____11932) with
| true -> begin
(reify_body env'.tcenv body)
end
| uu____11933 -> begin
body
end))
in (

let app = (mk_app curry f ftok vars)
in (

let uu____11935 = (

let uu____11940 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic))
in (match (uu____11940) with
| true -> begin
(

let uu____11946 = (FStar_SMTEncoding_Term.mk_Valid app)
in (

let uu____11947 = (encode_formula body env')
in ((uu____11946), (uu____11947))))
end
| uu____11952 -> begin
(

let uu____11953 = (encode_term body env')
in ((app), (uu____11953)))
end))
in (match (uu____11935) with
| (app, (body, decls2)) -> begin
(

let eqn = (

let uu____11967 = (

let uu____11972 = (

let uu____11973 = (

let uu____11979 = (FStar_SMTEncoding_Util.mkEq ((app), (body)))
in ((((app)::[])::[]), (vars), (uu____11979)))
in (FStar_SMTEncoding_Util.mkForall uu____11973))
in (

let uu____11985 = (

let uu____11987 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (uu____11987))
in ((uu____11972), (uu____11985), (Some ((Prims.strcat "equation_" f))))))
in FStar_SMTEncoding_Term.Assume (uu____11967))
in (

let uu____11990 = (

let uu____11992 = (

let uu____11994 = (

let uu____11996 = (

let uu____11998 = (primitive_type_axioms env.tcenv flid f app)
in (FStar_List.append ((eqn)::[]) uu____11998))
in (FStar_List.append decls2 uu____11996))
in (FStar_List.append binder_decls uu____11994))
in (FStar_List.append decls uu____11992))
in ((uu____11990), (env))))
end))))
end));
)
end))))
end
| uu____12001 -> begin
(failwith "Impossible")
end)
end
| uu____12016 -> begin
(

let fuel = (

let uu____12020 = (varops.fresh "fuel")
in ((uu____12020), (FStar_SMTEncoding_Term.Fuel_sort)))
in (

let fuel_tm = (FStar_SMTEncoding_Util.mkFreeV fuel)
in (

let env0 = env
in (

let uu____12023 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun uu____12062 uu____12063 -> (match (((uu____12062), (uu____12063))) with
| ((gtoks, env), (flid_fv, (f, ftok))) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let g = (

let uu____12145 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented")
in (varops.new_fvar uu____12145))
in (

let gtok = (

let uu____12147 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented_token")
in (varops.new_fvar uu____12147))
in (

let env = (

let uu____12149 = (

let uu____12151 = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::[])))
in (FStar_All.pipe_left (fun _0_36 -> Some (_0_36)) uu____12151))
in (push_free_var env flid gtok uu____12149))
in (((((flid), (f), (ftok), (g), (gtok)))::gtoks), (env))))))
end)) (([]), (env))))
in (match (uu____12023) with
| (gtoks, env) -> begin
(

let gtoks = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env0 uu____12235 t_norm uu____12237 -> (match (((uu____12235), (uu____12237))) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = lbn; FStar_Syntax_Syntax.lbunivs = uu____12261; FStar_Syntax_Syntax.lbtyp = uu____12262; FStar_Syntax_Syntax.lbeff = uu____12263; FStar_Syntax_Syntax.lbdef = e}) -> begin
((

let uu____12281 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____12281) with
| true -> begin
(

let uu____12282 = (FStar_Syntax_Print.lbname_to_string lbn)
in (

let uu____12283 = (FStar_Syntax_Print.term_to_string t_norm)
in (

let uu____12284 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print3 "Encoding let rec %s : %s = %s\n" uu____12282 uu____12283 uu____12284))))
end
| uu____12285 -> begin
()
end));
(

let uu____12286 = (destruct_bound_function flid t_norm e)
in (match (uu____12286) with
| ((binders, body, formals, tres), curry) -> begin
((

let uu____12308 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____12308) with
| true -> begin
(

let uu____12309 = (FStar_Syntax_Print.binders_to_string ", " binders)
in (

let uu____12310 = (FStar_Syntax_Print.term_to_string body)
in (

let uu____12311 = (FStar_Syntax_Print.binders_to_string ", " formals)
in (

let uu____12312 = (FStar_Syntax_Print.term_to_string tres)
in (FStar_Util.print4 "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n" uu____12309 uu____12310 uu____12311 uu____12312)))))
end
| uu____12313 -> begin
()
end));
(match (curry) with
| true -> begin
(failwith "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type")
end
| uu____12315 -> begin
()
end);
(

let uu____12316 = (encode_binders None binders env)
in (match (uu____12316) with
| (vars, guards, env', binder_decls, uu____12334) -> begin
(

let decl_g = (

let uu____12342 = (

let uu____12348 = (

let uu____12350 = (FStar_List.map Prims.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::uu____12350)
in ((g), (uu____12348), (FStar_SMTEncoding_Term.Term_sort), (Some ("Fuel-instrumented function name"))))
in FStar_SMTEncoding_Term.DeclFun (uu____12342))
in (

let env0 = (push_zfuel_name env0 flid g)
in (

let decl_g_tok = FStar_SMTEncoding_Term.DeclFun (((gtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Token for fuel-instrumented partial applications"))))
in (

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let app = (

let uu____12365 = (

let uu____12369 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (uu____12369)))
in (FStar_SMTEncoding_Util.mkApp uu____12365))
in (

let gsapp = (

let uu____12375 = (

let uu____12379 = (

let uu____12381 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (uu____12381)::vars_tm)
in ((g), (uu____12379)))
in (FStar_SMTEncoding_Util.mkApp uu____12375))
in (

let gmax = (

let uu____12385 = (

let uu____12389 = (

let uu____12391 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (uu____12391)::vars_tm)
in ((g), (uu____12389)))
in (FStar_SMTEncoding_Util.mkApp uu____12385))
in (

let body = (

let uu____12395 = (is_reifiable_function env'.tcenv t_norm)
in (match (uu____12395) with
| true -> begin
(reify_body env'.tcenv body)
end
| uu____12396 -> begin
body
end))
in (

let uu____12397 = (encode_term body env')
in (match (uu____12397) with
| (body_tm, decls2) -> begin
(

let eqn_g = (

let uu____12408 = (

let uu____12413 = (

let uu____12414 = (

let uu____12422 = (FStar_SMTEncoding_Util.mkEq ((gsapp), (body_tm)))
in ((((gsapp)::[])::[]), (Some ((Prims.parse_int "0"))), ((fuel)::vars), (uu____12422)))
in (FStar_SMTEncoding_Util.mkForall' uu____12414))
in (

let uu____12433 = (

let uu____12435 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (uu____12435))
in ((uu____12413), (uu____12433), (Some ((Prims.strcat "equation_with_fuel_" g))))))
in FStar_SMTEncoding_Term.Assume (uu____12408))
in (

let eqn_f = (

let uu____12439 = (

let uu____12444 = (

let uu____12445 = (

let uu____12451 = (FStar_SMTEncoding_Util.mkEq ((app), (gmax)))
in ((((app)::[])::[]), (vars), (uu____12451)))
in (FStar_SMTEncoding_Util.mkForall uu____12445))
in ((uu____12444), (Some ("Correspondence of recursive function to instrumented version")), (Some ((Prims.strcat "fuel_correspondence_" g)))))
in FStar_SMTEncoding_Term.Assume (uu____12439))
in (

let eqn_g' = (

let uu____12460 = (

let uu____12465 = (

let uu____12466 = (

let uu____12472 = (

let uu____12473 = (

let uu____12476 = (

let uu____12477 = (

let uu____12481 = (

let uu____12483 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "0"))
in (uu____12483)::vars_tm)
in ((g), (uu____12481)))
in (FStar_SMTEncoding_Util.mkApp uu____12477))
in ((gsapp), (uu____12476)))
in (FStar_SMTEncoding_Util.mkEq uu____12473))
in ((((gsapp)::[])::[]), ((fuel)::vars), (uu____12472)))
in (FStar_SMTEncoding_Util.mkForall uu____12466))
in ((uu____12465), (Some ("Fuel irrelevance")), (Some ((Prims.strcat "fuel_irrelevance_" g)))))
in FStar_SMTEncoding_Term.Assume (uu____12460))
in (

let uu____12496 = (

let uu____12501 = (encode_binders None formals env0)
in (match (uu____12501) with
| (vars, v_guards, env, binder_decls, uu____12518) -> begin
(

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let gapp = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::vars_tm)))
in (

let tok_corr = (

let tok_app = (

let uu____12533 = (FStar_SMTEncoding_Util.mkFreeV ((gtok), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply uu____12533 ((fuel)::vars)))
in (

let uu____12536 = (

let uu____12541 = (

let uu____12542 = (

let uu____12548 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (gapp)))
in ((((tok_app)::[])::[]), ((fuel)::vars), (uu____12548)))
in (FStar_SMTEncoding_Util.mkForall uu____12542))
in ((uu____12541), (Some ("Fuel token correspondence")), (Some ((Prims.strcat "fuel_token_correspondence_" gtok)))))
in FStar_SMTEncoding_Term.Assume (uu____12536)))
in (

let uu____12560 = (

let uu____12564 = (encode_term_pred None tres env gapp)
in (match (uu____12564) with
| (g_typing, d3) -> begin
(

let uu____12572 = (

let uu____12574 = (

let uu____12575 = (

let uu____12580 = (

let uu____12581 = (

let uu____12587 = (

let uu____12588 = (

let uu____12591 = (FStar_SMTEncoding_Util.mk_and_l v_guards)
in ((uu____12591), (g_typing)))
in (FStar_SMTEncoding_Util.mkImp uu____12588))
in ((((gapp)::[])::[]), ((fuel)::vars), (uu____12587)))
in (FStar_SMTEncoding_Util.mkForall uu____12581))
in ((uu____12580), (Some ("Typing correspondence of token to term")), (Some ((Prims.strcat "token_correspondence_" g)))))
in FStar_SMTEncoding_Term.Assume (uu____12575))
in (uu____12574)::[])
in ((d3), (uu____12572)))
end))
in (match (uu____12560) with
| (aux_decls, typing_corr) -> begin
(((FStar_List.append binder_decls aux_decls)), ((FStar_List.append typing_corr ((tok_corr)::[]))))
end)))))
end))
in (match (uu____12496) with
| (aux_decls, g_typing) -> begin
(((FStar_List.append binder_decls (FStar_List.append decls2 (FStar_List.append aux_decls ((decl_g)::(decl_g_tok)::[]))))), ((FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing)), (env0))
end)))))
end))))))))))
end));
)
end));
)
end))
in (

let uu____12627 = (

let uu____12634 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun uu____12666 uu____12667 -> (match (((uu____12666), (uu____12667))) with
| ((decls, eqns, env0), (gtok, ty, lb)) -> begin
(

let uu____12743 = (encode_one_binding env0 gtok ty lb)
in (match (uu____12743) with
| (decls', eqns', env0) -> begin
(((decls')::decls), ((FStar_List.append eqns' eqns)), (env0))
end))
end)) (((decls)::[]), ([]), (env0)) uu____12634))
in (match (uu____12627) with
| (decls, eqns, env0) -> begin
(

let uu____12783 = (

let uu____12788 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right uu____12788 (FStar_List.partition (fun uu___125_12798 -> (match (uu___125_12798) with
| FStar_SMTEncoding_Term.DeclFun (uu____12799) -> begin
true
end
| uu____12805 -> begin
false
end)))))
in (match (uu____12783) with
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

let uu____12823 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right uu____12823 (FStar_String.concat " and ")))
in (

let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in (((decl)::[]), (env))))
end))
end))


let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> ((

let uu____12856 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____12856) with
| true -> begin
(

let uu____12857 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") uu____12857))
end
| uu____12858 -> begin
()
end));
(

let nm = (

let uu____12860 = (FStar_Syntax_Util.lid_of_sigelt se)
in (match (uu____12860) with
| None -> begin
""
end
| Some (l) -> begin
l.FStar_Ident.str
end))
in (

let uu____12863 = (encode_sigelt' env se)
in (match (uu____12863) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(

let uu____12872 = (

let uu____12874 = (

let uu____12875 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (uu____12875))
in (uu____12874)::[])
in ((uu____12872), (e)))
end
| uu____12877 -> begin
(

let uu____12878 = (

let uu____12880 = (

let uu____12882 = (

let uu____12883 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____12883))
in (uu____12882)::g)
in (

let uu____12884 = (

let uu____12886 = (

let uu____12887 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____12887))
in (uu____12886)::[])
in (FStar_List.append uu____12880 uu____12884)))
in ((uu____12878), (e)))
end)
end)));
))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____12895) -> begin
(failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, uu____12906) -> begin
(

let uu____12907 = (

let uu____12908 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right uu____12908 Prims.op_Negation))
in (match (uu____12907) with
| true -> begin
(([]), (env))
end
| uu____12913 -> begin
(

let close_effect_params = (fun tm -> (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
tm
end
| uu____12928 -> begin
(

let uu____12929 = (

let uu____12932 = (

let uu____12933 = (

let uu____12948 = (FStar_All.pipe_left (fun _0_37 -> Some (_0_37)) (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[])))))
in ((ed.FStar_Syntax_Syntax.binders), (tm), (uu____12948)))
in FStar_Syntax_Syntax.Tm_abs (uu____12933))
in (FStar_Syntax_Syntax.mk uu____12932))
in (uu____12929 None tm.FStar_Syntax_Syntax.pos))
end))
in (

let encode_action = (fun env a -> (

let uu____13001 = (new_term_constant_and_tok_from_lid env a.FStar_Syntax_Syntax.action_name)
in (match (uu____13001) with
| (aname, atok, env) -> begin
(

let uu____13011 = (FStar_Syntax_Util.arrow_formals_comp a.FStar_Syntax_Syntax.action_typ)
in (match (uu____13011) with
| (formals, uu____13021) -> begin
(

let uu____13028 = (

let uu____13031 = (close_effect_params a.FStar_Syntax_Syntax.action_defn)
in (encode_term uu____13031 env))
in (match (uu____13028) with
| (tm, decls) -> begin
(

let a_decls = (

let uu____13039 = (

let uu____13040 = (

let uu____13046 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____13054 -> FStar_SMTEncoding_Term.Term_sort)))
in ((aname), (uu____13046), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action"))))
in FStar_SMTEncoding_Term.DeclFun (uu____13040))
in (uu____13039)::(FStar_SMTEncoding_Term.DeclFun (((atok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action token")))))::[])
in (

let uu____13061 = (

let aux = (fun uu____13090 uu____13091 -> (match (((uu____13090), (uu____13091))) with
| ((bv, uu____13118), (env, acc_sorts, acc)) -> begin
(

let uu____13139 = (gen_term_var env bv)
in (match (uu____13139) with
| (xxsym, xx, env) -> begin
((env), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::acc_sorts), ((xx)::acc))
end))
end))
in (FStar_List.fold_right aux formals ((env), ([]), ([]))))
in (match (uu____13061) with
| (uu____13177, xs_sorts, xs) -> begin
(

let app = (FStar_SMTEncoding_Util.mkApp ((aname), (xs)))
in (

let a_eq = (

let uu____13191 = (

let uu____13196 = (

let uu____13197 = (

let uu____13203 = (

let uu____13204 = (

let uu____13207 = (mk_Apply tm xs_sorts)
in ((app), (uu____13207)))
in (FStar_SMTEncoding_Util.mkEq uu____13204))
in ((((app)::[])::[]), (xs_sorts), (uu____13203)))
in (FStar_SMTEncoding_Util.mkForall uu____13197))
in ((uu____13196), (Some ("Action equality")), (Some ((Prims.strcat aname "_equality")))))
in FStar_SMTEncoding_Term.Assume (uu____13191))
in (

let tok_correspondence = (

let tok_term = (FStar_SMTEncoding_Util.mkFreeV ((atok), (FStar_SMTEncoding_Term.Term_sort)))
in (

let tok_app = (mk_Apply tok_term xs_sorts)
in (

let uu____13220 = (

let uu____13225 = (

let uu____13226 = (

let uu____13232 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (app)))
in ((((tok_app)::[])::[]), (xs_sorts), (uu____13232)))
in (FStar_SMTEncoding_Util.mkForall uu____13226))
in ((uu____13225), (Some ("Action token correspondence")), (Some ((Prims.strcat aname "_token_correspondence")))))
in FStar_SMTEncoding_Term.Assume (uu____13220))))
in ((env), ((FStar_List.append decls (FStar_List.append a_decls ((a_eq)::(tok_correspondence)::[]))))))))
end)))
end))
end))
end)))
in (

let uu____13243 = (FStar_Util.fold_map encode_action env ed.FStar_Syntax_Syntax.actions)
in (match (uu____13243) with
| (env, decls2) -> begin
(((FStar_List.flatten decls2)), (env))
end))))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____13259, uu____13260, uu____13261, uu____13262) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid) -> begin
(

let uu____13265 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____13265) with
| (tname, ttok, env) -> begin
(([]), (env))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____13276, t, quals, uu____13279) -> begin
(

let will_encode_definition = (

let uu____13283 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___126_13285 -> (match (uu___126_13285) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Irreducible) -> begin
true
end
| uu____13288 -> begin
false
end))))
in (not (uu____13283)))
in (match (will_encode_definition) with
| true -> begin
(([]), (env))
end
| uu____13292 -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____13294 = (encode_top_level_val env fv t quals)
in (match (uu____13294) with
| (decls, env) -> begin
(

let tname = lid.FStar_Ident.str
in (

let tsym = (FStar_SMTEncoding_Util.mkFreeV ((tname), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____13306 = (

let uu____13308 = (primitive_type_axioms env.tcenv lid tname tsym)
in (FStar_List.append decls uu____13308))
in ((uu____13306), (env)))))
end)))
end))
end
| FStar_Syntax_Syntax.Sig_assume (l, f, uu____13313, uu____13314) -> begin
(

let uu____13317 = (encode_formula f env)
in (match (uu____13317) with
| (f, decls) -> begin
(

let g = (

let uu____13326 = (

let uu____13327 = (

let uu____13332 = (

let uu____13334 = (

let uu____13335 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" uu____13335))
in Some (uu____13334))
in (

let uu____13336 = (

let uu____13338 = (varops.mk_unique (Prims.strcat "assumption_" l.FStar_Ident.str))
in Some (uu____13338))
in ((f), (uu____13332), (uu____13336))))
in FStar_SMTEncoding_Term.Assume (uu____13327))
in (uu____13326)::[])
in (((FStar_List.append decls g)), (env)))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, uu____13344, quals, uu____13346) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) -> begin
(

let uu____13354 = (FStar_Util.fold_map (fun env lb -> (

let lid = (

let uu____13361 = (

let uu____13366 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____13366.FStar_Syntax_Syntax.fv_name)
in uu____13361.FStar_Syntax_Syntax.v)
in (

let uu____13370 = (

let uu____13371 = (FStar_TypeChecker_Env.try_lookup_val_decl env.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone uu____13371))
in (match (uu____13370) with
| true -> begin
(

let val_decl = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), (r)))
in (

let uu____13390 = (encode_sigelt' env val_decl)
in (match (uu____13390) with
| (decls, env) -> begin
((env), (decls))
end)))
end
| uu____13397 -> begin
((env), ([]))
end)))) env (Prims.snd lbs))
in (match (uu____13354) with
| (env, decls) -> begin
(((FStar_List.flatten decls)), (env))
end))
end
| FStar_Syntax_Syntax.Sig_let ((uu____13407, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t); FStar_Syntax_Syntax.lbunivs = uu____13409; FStar_Syntax_Syntax.lbtyp = uu____13410; FStar_Syntax_Syntax.lbeff = uu____13411; FStar_Syntax_Syntax.lbdef = uu____13412})::[]), uu____13413, uu____13414, uu____13415, uu____13416) when (FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Syntax_Const.b2t_lid) -> begin
(

let uu____13432 = (new_term_constant_and_tok_from_lid env b2t.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____13432) with
| (tname, ttok, env) -> begin
(

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let valid_b2t_x = (

let uu____13450 = (

let uu____13454 = (

let uu____13456 = (FStar_SMTEncoding_Util.mkApp (("Prims.b2t"), ((x)::[])))
in (uu____13456)::[])
in (("Valid"), (uu____13454)))
in (FStar_SMTEncoding_Util.mkApp uu____13450))
in (

let decls = (

let uu____13461 = (

let uu____13463 = (

let uu____13464 = (

let uu____13469 = (

let uu____13470 = (

let uu____13476 = (

let uu____13477 = (

let uu____13480 = (FStar_SMTEncoding_Util.mkApp (("BoxBool_proj_0"), ((x)::[])))
in ((valid_b2t_x), (uu____13480)))
in (FStar_SMTEncoding_Util.mkEq uu____13477))
in ((((valid_b2t_x)::[])::[]), ((xx)::[]), (uu____13476)))
in (FStar_SMTEncoding_Util.mkForall uu____13470))
in ((uu____13469), (Some ("b2t def")), (Some ("b2t_def"))))
in FStar_SMTEncoding_Term.Assume (uu____13464))
in (uu____13463)::[])
in (FStar_SMTEncoding_Term.DeclFun (((tname), ((FStar_SMTEncoding_Term.Term_sort)::[]), (FStar_SMTEncoding_Term.Term_sort), (None))))::uu____13461)
in ((decls), (env))))))
end))
end
| FStar_Syntax_Syntax.Sig_let (uu____13498, uu____13499, uu____13500, quals, uu____13502) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___127_13510 -> (match (uu___127_13510) with
| FStar_Syntax_Syntax.Discriminator (uu____13511) -> begin
true
end
| uu____13512 -> begin
false
end)))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let (uu____13514, uu____13515, lids, quals, uu____13518) when ((FStar_All.pipe_right lids (FStar_Util.for_some (fun l -> (

let uu____13527 = (

let uu____13528 = (FStar_List.hd l.FStar_Ident.ns)
in uu____13528.FStar_Ident.idText)
in (uu____13527 = "Prims"))))) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___128_13530 -> (match (uu___128_13530) with
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
true
end
| uu____13531 -> begin
false
end))))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____13534, uu____13535, quals, uu____13537) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___129_13549 -> (match (uu___129_13549) with
| FStar_Syntax_Syntax.Projector (uu____13550) -> begin
true
end
| uu____13553 -> begin
false
end)))) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____13560 = (try_lookup_free_var env l)
in (match (uu____13560) with
| Some (uu____13564) -> begin
(([]), (env))
end
| None -> begin
(

let se = FStar_Syntax_Syntax.Sig_declare_typ (((l), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), ((FStar_Ident.range_of_lid l))))
in (encode_sigelt env se))
end))))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), uu____13573, uu____13574, quals, uu____13576) -> begin
(encode_top_level_let env ((is_rec), (bindings)) quals)
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____13590, uu____13591, uu____13592) -> begin
(

let uu____13599 = (encode_signature env ses)
in (match (uu____13599) with
| (g, env) -> begin
(

let uu____13609 = (FStar_All.pipe_right g (FStar_List.partition (fun uu___130_13619 -> (match (uu___130_13619) with
| FStar_SMTEncoding_Term.Assume (uu____13620, Some ("inversion axiom"), uu____13621) -> begin
false
end
| uu____13625 -> begin
true
end))))
in (match (uu____13609) with
| (g', inversions) -> begin
(

let uu____13634 = (FStar_All.pipe_right g' (FStar_List.partition (fun uu___131_13644 -> (match (uu___131_13644) with
| FStar_SMTEncoding_Term.DeclFun (uu____13645) -> begin
true
end
| uu____13651 -> begin
false
end))))
in (match (uu____13634) with
| (decls, rest) -> begin
(((FStar_List.append decls (FStar_List.append rest inversions))), (env))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, uu____13662, tps, k, uu____13665, datas, quals, uu____13668) -> begin
(

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___132_13677 -> (match (uu___132_13677) with
| (FStar_Syntax_Syntax.Logic) | (FStar_Syntax_Syntax.Assumption) -> begin
true
end
| uu____13678 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> (match (is_logical) with
| true -> begin
(

let uu____13701 = c
in (match (uu____13701) with
| (name, args, uu____13713, uu____13714, uu____13715) -> begin
(

let uu____13722 = (

let uu____13723 = (

let uu____13729 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in ((name), (uu____13729), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (uu____13723))
in (uu____13722)::[])
end))
end
| uu____13739 -> begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end))
in (

let inversion_axioms = (fun tapp vars -> (

let uu____13754 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (

let uu____13757 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right uu____13757 FStar_Option.isNone)))))
in (match (uu____13754) with
| true -> begin
[]
end
| uu____13767 -> begin
(

let uu____13768 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____13768) with
| (xxsym, xx) -> begin
(

let uu____13774 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun uu____13785 l -> (match (uu____13785) with
| (out, decls) -> begin
(

let uu____13797 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (uu____13797) with
| (uu____13803, data_t) -> begin
(

let uu____13805 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (uu____13805) with
| (args, res) -> begin
(

let indices = (

let uu____13834 = (

let uu____13835 = (FStar_Syntax_Subst.compress res)
in uu____13835.FStar_Syntax_Syntax.n)
in (match (uu____13834) with
| FStar_Syntax_Syntax.Tm_app (uu____13843, indices) -> begin
indices
end
| uu____13859 -> begin
[]
end))
in (

let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env uu____13871 -> (match (uu____13871) with
| (x, uu____13875) -> begin
(

let uu____13876 = (

let uu____13877 = (

let uu____13881 = (mk_term_projector_name l x)
in ((uu____13881), ((xx)::[])))
in (FStar_SMTEncoding_Util.mkApp uu____13877))
in (push_term_var env x uu____13876))
end)) env))
in (

let uu____13883 = (encode_args indices env)
in (match (uu____13883) with
| (indices, decls') -> begin
((match (((FStar_List.length indices) <> (FStar_List.length vars))) with
| true -> begin
(failwith "Impossible")
end
| uu____13901 -> begin
()
end);
(

let eqs = (

let uu____13903 = (FStar_List.map2 (fun v a -> (

let uu____13911 = (

let uu____13914 = (FStar_SMTEncoding_Util.mkFreeV v)
in ((uu____13914), (a)))
in (FStar_SMTEncoding_Util.mkEq uu____13911))) vars indices)
in (FStar_All.pipe_right uu____13903 FStar_SMTEncoding_Util.mk_and_l))
in (

let uu____13916 = (

let uu____13917 = (

let uu____13920 = (

let uu____13921 = (

let uu____13924 = (mk_data_tester env l xx)
in ((uu____13924), (eqs)))
in (FStar_SMTEncoding_Util.mkAnd uu____13921))
in ((out), (uu____13920)))
in (FStar_SMTEncoding_Util.mkOr uu____13917))
in ((uu____13916), ((FStar_List.append decls decls')))));
)
end))))
end))
end))
end)) ((FStar_SMTEncoding_Util.mkFalse), ([]))))
in (match (uu____13774) with
| (data_ax, decls) -> begin
(

let uu____13932 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____13932) with
| (ffsym, ff) -> begin
(

let fuel_guarded_inversion = (

let xx_has_type_sfuel = (match (((FStar_List.length datas) > (Prims.parse_int "1"))) with
| true -> begin
(

let uu____13943 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((ff)::[])))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel uu____13943 xx tapp))
end
| uu____13945 -> begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end)
in (

let uu____13946 = (

let uu____13951 = (

let uu____13952 = (

let uu____13958 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (

let uu____13966 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_sfuel), (data_ax)))
in ((((xx_has_type_sfuel)::[])::[]), (uu____13958), (uu____13966))))
in (FStar_SMTEncoding_Util.mkForall uu____13952))
in (

let uu____13974 = (

let uu____13976 = (varops.mk_unique (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str))
in Some (uu____13976))
in ((uu____13951), (Some ("inversion axiom")), (uu____13974))))
in FStar_SMTEncoding_Term.Assume (uu____13946)))
in (

let pattern_guarded_inversion = (

let uu____13981 = ((contains_name env "Prims.inversion") && ((FStar_List.length datas) > (Prims.parse_int "1")))
in (match (uu____13981) with
| true -> begin
(

let xx_has_type_fuel = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let pattern_guard = (FStar_SMTEncoding_Util.mkApp (("Prims.inversion"), ((tapp)::[])))
in (

let uu____13989 = (

let uu____13990 = (

let uu____13995 = (

let uu____13996 = (

let uu____14002 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (

let uu____14010 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_fuel), (data_ax)))
in ((((xx_has_type_fuel)::(pattern_guard)::[])::[]), (uu____14002), (uu____14010))))
in (FStar_SMTEncoding_Util.mkForall uu____13996))
in (

let uu____14018 = (

let uu____14020 = (varops.mk_unique (Prims.strcat "pattern_guarded_inversion_" t.FStar_Ident.str))
in Some (uu____14020))
in ((uu____13995), (Some ("inversion axiom")), (uu____14018))))
in FStar_SMTEncoding_Term.Assume (uu____13990))
in (uu____13989)::[])))
end
| uu____14023 -> begin
[]
end))
in (FStar_List.append decls (FStar_List.append ((fuel_guarded_inversion)::[]) pattern_guarded_inversion))))
end))
end))
end))
end)))
in (

let uu____14024 = (

let uu____14032 = (

let uu____14033 = (FStar_Syntax_Subst.compress k)
in uu____14033.FStar_Syntax_Syntax.n)
in (match (uu____14032) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
(((FStar_List.append tps formals)), ((FStar_Syntax_Util.comp_result kres)))
end
| uu____14062 -> begin
((tps), (k))
end))
in (match (uu____14024) with
| (formals, res) -> begin
(

let uu____14077 = (FStar_Syntax_Subst.open_term formals res)
in (match (uu____14077) with
| (formals, res) -> begin
(

let uu____14084 = (encode_binders None formals env)
in (match (uu____14084) with
| (vars, guards, env', binder_decls, uu____14099) -> begin
(

let uu____14106 = (new_term_constant_and_tok_from_lid env t)
in (match (uu____14106) with
| (tname, ttok, env) -> begin
(

let ttok_tm = (FStar_SMTEncoding_Util.mkApp ((ttok), ([])))
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let tapp = (

let uu____14119 = (

let uu____14123 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((tname), (uu____14123)))
in (FStar_SMTEncoding_Util.mkApp uu____14119))
in (

let uu____14128 = (

let tname_decl = (

let uu____14134 = (

let uu____14143 = (FStar_All.pipe_right vars (FStar_List.map (fun uu____14155 -> (match (uu____14155) with
| (n, s) -> begin
(((Prims.strcat tname n)), (s))
end))))
in (

let uu____14162 = (varops.next_id ())
in ((tname), (uu____14143), (FStar_SMTEncoding_Term.Term_sort), (uu____14162), (false))))
in (constructor_or_logic_type_decl uu____14134))
in (

let uu____14166 = (match (vars) with
| [] -> begin
(

let uu____14173 = (

let uu____14174 = (

let uu____14176 = (FStar_SMTEncoding_Util.mkApp ((tname), ([])))
in (FStar_All.pipe_left (fun _0_38 -> Some (_0_38)) uu____14176))
in (push_free_var env t tname uu____14174))
in (([]), (uu____14173)))
end
| uu____14180 -> begin
(

let ttok_decl = FStar_SMTEncoding_Term.DeclFun (((ttok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("token"))))
in (

let ttok_fresh = (

let uu____14186 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ttok), (FStar_SMTEncoding_Term.Term_sort)) uu____14186))
in (

let ttok_app = (mk_Apply ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (

let uu____14195 = (

let uu____14200 = (

let uu____14201 = (

let uu____14209 = (FStar_SMTEncoding_Util.mkEq ((ttok_app), (tapp)))
in ((pats), (None), (vars), (uu____14209)))
in (FStar_SMTEncoding_Util.mkForall' uu____14201))
in ((uu____14200), (Some ("name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" ttok)))))
in FStar_SMTEncoding_Term.Assume (uu____14195))
in (((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[]), (env)))))))
end)
in (match (uu____14166) with
| (tok_decls, env) -> begin
(((FStar_List.append tname_decl tok_decls)), (env))
end)))
in (match (uu____14128) with
| (decls, env) -> begin
(

let kindingAx = (

let uu____14233 = (encode_term_pred None res env' tapp)
in (match (uu____14233) with
| (k, decls) -> begin
(

let karr = (match (((FStar_List.length formals) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____14247 = (

let uu____14248 = (

let uu____14253 = (

let uu____14254 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____14254))
in ((uu____14253), (Some ("kinding")), (Some ((Prims.strcat "pre_kinding_" ttok)))))
in FStar_SMTEncoding_Term.Assume (uu____14248))
in (uu____14247)::[])
end
| uu____14257 -> begin
[]
end)
in (

let uu____14258 = (

let uu____14260 = (

let uu____14262 = (

let uu____14263 = (

let uu____14268 = (

let uu____14269 = (

let uu____14275 = (FStar_SMTEncoding_Util.mkImp ((guard), (k)))
in ((((tapp)::[])::[]), (vars), (uu____14275)))
in (FStar_SMTEncoding_Util.mkForall uu____14269))
in ((uu____14268), (None), (Some ((Prims.strcat "kinding_" ttok)))))
in FStar_SMTEncoding_Term.Assume (uu____14263))
in (uu____14262)::[])
in (FStar_List.append karr uu____14260))
in (FStar_List.append decls uu____14258)))
end))
in (

let aux = (

let uu____14285 = (

let uu____14287 = (inversion_axioms tapp vars)
in (

let uu____14289 = (

let uu____14291 = (pretype_axiom tapp vars)
in (uu____14291)::[])
in (FStar_List.append uu____14287 uu____14289)))
in (FStar_List.append kindingAx uu____14285))
in (

let g = (FStar_List.append decls (FStar_List.append binder_decls aux))
in ((g), (env)))))
end)))))
end))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____14296, uu____14297, uu____14298, uu____14299, uu____14300, uu____14301, uu____14302) when (FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____14309, t, uu____14311, n_tps, quals, uu____14314, drange) -> begin
(

let uu____14320 = (new_term_constant_and_tok_from_lid env d)
in (match (uu____14320) with
| (ddconstrsym, ddtok, env) -> begin
(

let ddtok_tm = (FStar_SMTEncoding_Util.mkApp ((ddtok), ([])))
in (

let uu____14331 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____14331) with
| (formals, t_res) -> begin
(

let uu____14353 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____14353) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (

let uu____14362 = (encode_binders (Some (fuel_tm)) formals env)
in (match (uu____14362) with
| (vars, guards, env', binder_decls, names) -> begin
(

let projectors = (FStar_All.pipe_right names (FStar_List.map (fun x -> (

let uu____14395 = (mk_term_projector_name d x)
in ((uu____14395), (FStar_SMTEncoding_Term.Term_sort))))))
in (

let datacons = (

let uu____14397 = (

let uu____14406 = (varops.next_id ())
in ((ddconstrsym), (projectors), (FStar_SMTEncoding_Term.Term_sort), (uu____14406), (true)))
in (FStar_All.pipe_right uu____14397 FStar_SMTEncoding_Term.constructor_to_decl))
in (

let app = (mk_Apply ddtok_tm vars)
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (

let uu____14426 = (encode_term_pred None t env ddtok_tm)
in (match (uu____14426) with
| (tok_typing, decls3) -> begin
(

let uu____14433 = (encode_binders (Some (fuel_tm)) formals env)
in (match (uu____14433) with
| (vars', guards', env'', decls_formals, uu____14448) -> begin
(

let uu____14455 = (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars')
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (encode_term_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (uu____14455) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_SMTEncoding_Util.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| uu____14474 -> begin
(

let uu____14478 = (

let uu____14479 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ddtok), (FStar_SMTEncoding_Term.Term_sort)) uu____14479))
in (uu____14478)::[])
end)
in (

let encode_elim = (fun uu____14486 -> (

let uu____14487 = (FStar_Syntax_Util.head_and_args t_res)
in (match (uu____14487) with
| (head, args) -> begin
(

let uu____14516 = (

let uu____14517 = (FStar_Syntax_Subst.compress head)
in uu____14517.FStar_Syntax_Syntax.n)
in (match (uu____14516) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let uu____14535 = (encode_args args env')
in (match (uu____14535) with
| (encoded_args, arg_decls) -> begin
(

let uu____14546 = (FStar_List.fold_left (fun uu____14557 arg -> (match (uu____14557) with
| (env, arg_vars, eqns) -> begin
(

let uu____14576 = (

let uu____14580 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in (gen_term_var env uu____14580))
in (match (uu____14576) with
| (uu____14586, xv, env) -> begin
(

let uu____14589 = (

let uu____14591 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (uu____14591)::eqns)
in ((env), ((xv)::arg_vars), (uu____14589)))
end))
end)) ((env'), ([]), ([])) encoded_args)
in (match (uu____14546) with
| (uu____14599, arg_vars, eqns) -> begin
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

let uu____14620 = (

let uu____14625 = (

let uu____14626 = (

let uu____14632 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____14638 = (

let uu____14639 = (

let uu____14642 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append eqns guards))
in ((ty_pred), (uu____14642)))
in (FStar_SMTEncoding_Util.mkImp uu____14639))
in ((((ty_pred)::[])::[]), (uu____14632), (uu____14638))))
in (FStar_SMTEncoding_Util.mkForall uu____14626))
in ((uu____14625), (Some ("data constructor typing elim")), (Some ((Prims.strcat "data_elim_" ddconstrsym)))))
in FStar_SMTEncoding_Term.Assume (uu____14620))
in (

let subterm_ordering = (match ((FStar_Ident.lid_equals d FStar_Syntax_Const.lextop_lid)) with
| true -> begin
(

let x = (

let uu____14656 = (varops.fresh "x")
in ((uu____14656), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (

let uu____14658 = (

let uu____14663 = (

let uu____14664 = (

let uu____14670 = (

let uu____14673 = (

let uu____14675 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp)
in (uu____14675)::[])
in (uu____14673)::[])
in (

let uu____14678 = (

let uu____14679 = (

let uu____14682 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (

let uu____14683 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp)
in ((uu____14682), (uu____14683))))
in (FStar_SMTEncoding_Util.mkImp uu____14679))
in ((uu____14670), ((x)::[]), (uu____14678))))
in (FStar_SMTEncoding_Util.mkForall uu____14664))
in (

let uu____14693 = (

let uu____14695 = (varops.mk_unique "lextop")
in Some (uu____14695))
in ((uu____14663), (Some ("lextop is top")), (uu____14693))))
in FStar_SMTEncoding_Term.Assume (uu____14658))))
end
| uu____14698 -> begin
(

let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
[]
end
| FStar_SMTEncoding_Term.Term_sort -> begin
(

let uu____14709 = (

let uu____14710 = (FStar_SMTEncoding_Util.mkFreeV v)
in (FStar_SMTEncoding_Util.mk_Precedes uu____14710 dapp))
in (uu____14709)::[])
end
| uu____14711 -> begin
(failwith "unexpected sort")
end))))
in (

let uu____14713 = (

let uu____14718 = (

let uu____14719 = (

let uu____14725 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____14731 = (

let uu____14732 = (

let uu____14735 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (uu____14735)))
in (FStar_SMTEncoding_Util.mkImp uu____14732))
in ((((ty_pred)::[])::[]), (uu____14725), (uu____14731))))
in (FStar_SMTEncoding_Util.mkForall uu____14719))
in ((uu____14718), (Some ("subterm ordering")), (Some ((Prims.strcat "subterm_ordering_" ddconstrsym)))))
in FStar_SMTEncoding_Term.Assume (uu____14713)))
end)
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end))
end)))
end
| uu____14746 -> begin
((

let uu____14748 = (

let uu____14749 = (FStar_Syntax_Print.lid_to_string d)
in (

let uu____14750 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" uu____14749 uu____14750)))
in (FStar_Errors.warn drange uu____14748));
(([]), ([]));
)
end))
end)))
in (

let uu____14753 = (encode_elim ())
in (match (uu____14753) with
| (decls2, elim) -> begin
(

let g = (

let uu____14765 = (

let uu____14767 = (

let uu____14769 = (

let uu____14771 = (

let uu____14773 = (

let uu____14774 = (

let uu____14780 = (

let uu____14782 = (

let uu____14783 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" uu____14783))
in Some (uu____14782))
in ((ddtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (uu____14780)))
in FStar_SMTEncoding_Term.DeclFun (uu____14774))
in (uu____14773)::[])
in (

let uu____14786 = (

let uu____14788 = (

let uu____14790 = (

let uu____14792 = (

let uu____14794 = (

let uu____14796 = (

let uu____14798 = (

let uu____14799 = (

let uu____14804 = (

let uu____14805 = (

let uu____14811 = (FStar_SMTEncoding_Util.mkEq ((app), (dapp)))
in ((((app)::[])::[]), (vars), (uu____14811)))
in (FStar_SMTEncoding_Util.mkForall uu____14805))
in ((uu____14804), (Some ("equality for proxy")), (Some ((Prims.strcat "equality_tok_" ddtok)))))
in FStar_SMTEncoding_Term.Assume (uu____14799))
in (

let uu____14819 = (

let uu____14821 = (

let uu____14822 = (

let uu____14827 = (

let uu____14828 = (

let uu____14834 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) vars')
in (

let uu____14840 = (FStar_SMTEncoding_Util.mkImp ((guard'), (ty_pred')))
in ((((ty_pred')::[])::[]), (uu____14834), (uu____14840))))
in (FStar_SMTEncoding_Util.mkForall uu____14828))
in ((uu____14827), (Some ("data constructor typing intro")), (Some ((Prims.strcat "data_typing_intro_" ddtok)))))
in FStar_SMTEncoding_Term.Assume (uu____14822))
in (uu____14821)::[])
in (uu____14798)::uu____14819))
in (FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("typing for data constructor proxy")), (Some ((Prims.strcat "typing_tok_" ddtok))))))::uu____14796)
in (FStar_List.append uu____14794 elim))
in (FStar_List.append decls_pred uu____14792))
in (FStar_List.append decls_formals uu____14790))
in (FStar_List.append proxy_fresh uu____14788))
in (FStar_List.append uu____14771 uu____14786)))
in (FStar_List.append decls3 uu____14769))
in (FStar_List.append decls2 uu____14767))
in (FStar_List.append binder_decls uu____14765))
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
and encode_signature : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun uu____14863 se -> (match (uu____14863) with
| (g, env) -> begin
(

let uu____14875 = (encode_sigelt env se)
in (match (uu____14875) with
| (g', env) -> begin
(((FStar_List.append g g')), (env))
end))
end)) (([]), (env)))))


let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env bindings -> (

let encode_binding = (fun b uu____14911 -> (match (uu____14911) with
| (i, decls, env) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (uu____14929) -> begin
(((i + (Prims.parse_int "1"))), ([]), (env))
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in ((

let uu____14934 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
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

let uu____14939 = (encode_term t1 env)
in (match (uu____14939) with
| (t, decls') -> begin
(

let t_hash = (FStar_SMTEncoding_Term.hash_of_term t)
in (

let uu____14949 = (

let uu____14953 = (

let uu____14954 = (

let uu____14955 = (FStar_Util.digest_of_string t_hash)
in (

let uu____14956 = (

let uu____14957 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" uu____14957))
in (Prims.strcat uu____14955 uu____14956)))
in (Prims.strcat "x_" uu____14954))
in (new_term_constant_from_string env x uu____14953))
in (match (uu____14949) with
| (xxsym, xx, env') -> begin
(

let t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel None xx t)
in (

let caption = (

let uu____14968 = (FStar_Options.log_queries ())
in (match (uu____14968) with
| true -> begin
(

let uu____14970 = (

let uu____14971 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____14972 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____14973 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" uu____14971 uu____14972 uu____14973))))
in Some (uu____14970))
end
| uu____14974 -> begin
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
| FStar_TypeChecker_Env.Binding_lid (x, (uu____14986, t)) -> begin
(

let t_norm = (whnf env t)
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____14995 = (encode_free_var env fv t t_norm [])
in (match (uu____14995) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))))
end
| (FStar_TypeChecker_Env.Binding_sig_inst (_, se, _)) | (FStar_TypeChecker_Env.Binding_sig (_, se)) -> begin
(

let uu____15014 = (encode_sigelt env se)
in (match (uu____15014) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))
end)
end))
in (

let uu____15024 = (FStar_List.fold_right encode_binding bindings (((Prims.parse_int "0")), ([]), (env)))
in (match (uu____15024) with
| (uu____15036, decls, env) -> begin
((decls), (env))
end))))


let encode_labels = (fun labs -> (

let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun uu____15081 -> (match (uu____15081) with
| (l, uu____15088, uu____15089) -> begin
FStar_SMTEncoding_Term.DeclFun ((((Prims.fst l)), ([]), (FStar_SMTEncoding_Term.Bool_sort), (None)))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun uu____15110 -> (match (uu____15110) with
| (l, uu____15118, uu____15119) -> begin
(

let uu____15124 = (FStar_All.pipe_left (fun _0_39 -> FStar_SMTEncoding_Term.Echo (_0_39)) (Prims.fst l))
in (

let uu____15125 = (

let uu____15127 = (

let uu____15128 = (FStar_SMTEncoding_Util.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (uu____15128))
in (uu____15127)::[])
in (uu____15124)::uu____15125))
end))))
in ((prefix), (suffix)))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (

let uu____15139 = (

let uu____15141 = (

let uu____15142 = (FStar_Util.smap_create (Prims.parse_int "100"))
in {bindings = []; depth = (Prims.parse_int "0"); tcenv = tcenv; warn = true; cache = uu____15142; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (uu____15141)::[])
in (FStar_ST.write last_env uu____15139)))


let get_env : FStar_TypeChecker_Env.env  ->  env_t = (fun tcenv -> (

let uu____15160 = (FStar_ST.read last_env)
in (match (uu____15160) with
| [] -> begin
(failwith "No env; call init first!")
end
| (e)::uu____15166 -> begin
(

let uu___158_15168 = e
in {bindings = uu___158_15168.bindings; depth = uu___158_15168.depth; tcenv = tcenv; warn = uu___158_15168.warn; cache = uu___158_15168.cache; nolabels = uu___158_15168.nolabels; use_zfuel_name = uu___158_15168.use_zfuel_name; encode_non_total_function_typ = uu___158_15168.encode_non_total_function_typ})
end)))


let set_env : env_t  ->  Prims.unit = (fun env -> (

let uu____15172 = (FStar_ST.read last_env)
in (match (uu____15172) with
| [] -> begin
(failwith "Empty env stack")
end
| (uu____15177)::tl -> begin
(FStar_ST.write last_env ((env)::tl))
end)))


let push_env : Prims.unit  ->  Prims.unit = (fun uu____15185 -> (

let uu____15186 = (FStar_ST.read last_env)
in (match (uu____15186) with
| [] -> begin
(failwith "Empty env stack")
end
| (hd)::tl -> begin
(

let refs = (FStar_Util.smap_copy hd.cache)
in (

let top = (

let uu___159_15207 = hd
in {bindings = uu___159_15207.bindings; depth = uu___159_15207.depth; tcenv = uu___159_15207.tcenv; warn = uu___159_15207.warn; cache = refs; nolabels = uu___159_15207.nolabels; use_zfuel_name = uu___159_15207.use_zfuel_name; encode_non_total_function_typ = uu___159_15207.encode_non_total_function_typ})
in (FStar_ST.write last_env ((top)::(hd)::tl))))
end)))


let pop_env : Prims.unit  ->  Prims.unit = (fun uu____15213 -> (

let uu____15214 = (FStar_ST.read last_env)
in (match (uu____15214) with
| [] -> begin
(failwith "Popping an empty stack")
end
| (uu____15219)::tl -> begin
(FStar_ST.write last_env tl)
end)))


let mark_env : Prims.unit  ->  Prims.unit = (fun uu____15227 -> (push_env ()))


let reset_mark_env : Prims.unit  ->  Prims.unit = (fun uu____15230 -> (pop_env ()))


let commit_mark_env : Prims.unit  ->  Prims.unit = (fun uu____15233 -> (

let uu____15234 = (FStar_ST.read last_env)
in (match (uu____15234) with
| (hd)::(uu____15240)::tl -> begin
(FStar_ST.write last_env ((hd)::tl))
end
| uu____15246 -> begin
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

let uu____15291 = (FStar_Options.log_queries ())
in (match (uu____15291) with
| true -> begin
(

let uu____15293 = (

let uu____15294 = (

let uu____15295 = (

let uu____15296 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.map FStar_Syntax_Print.lid_to_string))
in (FStar_All.pipe_right uu____15296 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " uu____15295))
in FStar_SMTEncoding_Term.Caption (uu____15294))
in (uu____15293)::decls)
end
| uu____15301 -> begin
decls
end)))
in (

let env = (get_env tcenv)
in (

let uu____15303 = (encode_sigelt env se)
in (match (uu____15303) with
| (decls, env) -> begin
((set_env env);
(

let uu____15309 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 uu____15309));
)
end)))))


let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____15318 -> begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in ((

let uu____15320 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____15320) with
| true -> begin
(

let uu____15321 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name uu____15321))
end
| uu____15324 -> begin
()
end));
(

let env = (get_env tcenv)
in (

let uu____15326 = (encode_signature (

let uu___160_15330 = env
in {bindings = uu___160_15330.bindings; depth = uu___160_15330.depth; tcenv = uu___160_15330.tcenv; warn = false; cache = uu___160_15330.cache; nolabels = uu___160_15330.nolabels; use_zfuel_name = uu___160_15330.use_zfuel_name; encode_non_total_function_typ = uu___160_15330.encode_non_total_function_typ}) modul.FStar_Syntax_Syntax.exports)
in (match (uu____15326) with
| (decls, env) -> begin
(

let caption = (fun decls -> (

let uu____15342 = (FStar_Options.log_queries ())
in (match (uu____15342) with
| true -> begin
(

let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::decls) ((FStar_SMTEncoding_Term.Caption ((Prims.strcat "End " msg)))::[])))
end
| uu____15345 -> begin
decls
end)))
in ((set_env (

let uu___161_15347 = env
in {bindings = uu___161_15347.bindings; depth = uu___161_15347.depth; tcenv = uu___161_15347.tcenv; warn = true; cache = uu___161_15347.cache; nolabels = uu___161_15347.nolabels; use_zfuel_name = uu___161_15347.use_zfuel_name; encode_non_total_function_typ = uu___161_15347.encode_non_total_function_typ}));
(

let uu____15349 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____15349) with
| true -> begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end
| uu____15350 -> begin
()
end));
(

let decls = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls));
))
end)));
)))


let encode_query : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_ErrorReporting.label Prims.list * FStar_SMTEncoding_Term.decl * FStar_SMTEncoding_Term.decl Prims.list) = (fun use_env_msg tcenv q -> ((

let uu____15384 = (

let uu____15385 = (FStar_TypeChecker_Env.current_module tcenv)
in uu____15385.FStar_Ident.str)
in (FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name uu____15384));
(

let env = (get_env tcenv)
in (

let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (

let uu____15393 = (

let rec aux = (fun bindings -> (match (bindings) with
| (FStar_TypeChecker_Env.Binding_var (x))::rest -> begin
(

let uu____15414 = (aux rest)
in (match (uu____15414) with
| (out, rest) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (

let uu____15430 = (

let uu____15432 = (FStar_Syntax_Syntax.mk_binder (

let uu___162_15433 = x
in {FStar_Syntax_Syntax.ppname = uu___162_15433.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___162_15433.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (uu____15432)::out)
in ((uu____15430), (rest))))
end))
end
| uu____15436 -> begin
(([]), (bindings))
end))
in (

let uu____15440 = (aux bindings)
in (match (uu____15440) with
| (closing, bindings) -> begin
(

let uu____15454 = (FStar_Syntax_Util.close_forall (FStar_List.rev closing) q)
in ((uu____15454), (bindings)))
end)))
in (match (uu____15393) with
| (q, bindings) -> begin
(

let uu____15467 = (

let uu____15470 = (FStar_List.filter (fun uu___133_15472 -> (match (uu___133_15472) with
| FStar_TypeChecker_Env.Binding_sig (uu____15473) -> begin
false
end
| uu____15477 -> begin
true
end)) bindings)
in (encode_env_bindings env uu____15470))
in (match (uu____15467) with
| (env_decls, env) -> begin
((

let uu____15488 = (((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTQuery"))))
in (match (uu____15488) with
| true -> begin
(

let uu____15489 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" uu____15489))
end
| uu____15490 -> begin
()
end));
(

let uu____15491 = (encode_formula q env)
in (match (uu____15491) with
| (phi, qdecls) -> begin
(

let uu____15503 = (

let uu____15506 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg uu____15506 phi))
in (match (uu____15503) with
| (labels, phi) -> begin
(

let uu____15516 = (encode_labels labels)
in (match (uu____15516) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append env_decls (FStar_List.append label_prefix qdecls))
in (

let qry = (

let uu____15537 = (

let uu____15542 = (FStar_SMTEncoding_Util.mkNot phi)
in (

let uu____15543 = (

let uu____15545 = (varops.mk_unique "@query")
in Some (uu____15545))
in ((uu____15542), (Some ("query")), (uu____15543))))
in FStar_SMTEncoding_Term.Assume (uu____15537))
in (

let suffix = (

let uu____15550 = (

let uu____15552 = (

let uu____15554 = (FStar_Options.print_z3_statistics ())
in (match (uu____15554) with
| true -> begin
(FStar_SMTEncoding_Term.PrintStats)::[]
end
| uu____15556 -> begin
[]
end))
in (FStar_List.append uu____15552 ((FStar_SMTEncoding_Term.Echo ("Done!"))::[])))
in (FStar_List.append label_suffix uu____15550))
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

let uu____15567 = (encode_formula q env)
in (match (uu____15567) with
| (f, uu____15571) -> begin
((FStar_SMTEncoding_Z3.pop "query");
(match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____15573) -> begin
true
end
| uu____15576 -> begin
false
end);
)
end));
)))




