
open Prims

let str : Prims.string  ->  FStar_Pprint.document = (fun s -> (FStar_Pprint.doc_of_string s))


let default_or_map = (fun n f x -> (match (x) with
| None -> begin
n
end
| Some (x') -> begin
(f x')
end))


let prefix2 : FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun prefix_ body -> (FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "1") prefix_ body))


let op_Hat_Slash_Plus_Hat : FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun prefix_ body -> (prefix2 prefix_ body))


let jump2 : FStar_Pprint.document  ->  FStar_Pprint.document = (fun body -> (FStar_Pprint.jump (Prims.parse_int "2") (Prims.parse_int "1") body))


let infix2 : FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (FStar_Pprint.infix (Prims.parse_int "2") (Prims.parse_int "1"))


let break1 : FStar_Pprint.document = (FStar_Pprint.break_ (Prims.parse_int "1"))


let separate_break_map = (fun sep f l -> (let _165_30 = (let _165_29 = (let _165_28 = (FStar_Pprint.op_Hat_Hat sep break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_28))
in (FStar_Pprint.separate_map _165_29 f l))
in (FStar_Pprint.group _165_30)))


let precede_break_separate_map = (fun prec sep f l -> (let _165_47 = (let _165_40 = (FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space)
in (let _165_39 = (let _165_38 = (FStar_List.hd l)
in (FStar_All.pipe_right _165_38 f))
in (FStar_Pprint.precede _165_40 _165_39)))
in (let _165_46 = (let _165_45 = (FStar_List.tl l)
in (FStar_Pprint.concat_map (fun x -> (let _165_44 = (let _165_43 = (let _165_42 = (f x)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_42))
in (FStar_Pprint.op_Hat_Hat sep _165_43))
in (FStar_Pprint.op_Hat_Hat break1 _165_44))) _165_45))
in (FStar_Pprint.op_Hat_Hat _165_47 _165_46))))


let concat_break_map = (fun f l -> (let _165_55 = (FStar_Pprint.concat_map (fun x -> (let _165_54 = (f x)
in (FStar_Pprint.op_Hat_Hat _165_54 break1))) l)
in (FStar_Pprint.group _165_55)))


let parens_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lparen contents FStar_Pprint.rparen))


let braces_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbrace contents FStar_Pprint.rbrace))


let brackets_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbracket contents FStar_Pprint.rbracket))


let doc_of_fsdoc : (Prims.string * (Prims.string * Prims.string) Prims.list)  ->  FStar_Pprint.document = (fun _67_46 -> (match (_67_46) with
| (comment, keywords) -> begin
(let _165_75 = (let _165_74 = (let _165_73 = (str comment)
in (let _165_72 = (let _165_71 = (let _165_70 = (FStar_Pprint.separate_map FStar_Pprint.comma (fun _67_49 -> (match (_67_49) with
| (k, v) -> begin
(let _165_69 = (let _165_68 = (str k)
in (let _165_67 = (let _165_66 = (let _165_65 = (str v)
in (_165_65)::[])
in (FStar_Pprint.rarrow)::_165_66)
in (_165_68)::_165_67))
in (FStar_Pprint.concat _165_69))
end)) keywords)
in (_165_70)::[])
in (FStar_Pprint.space)::_165_71)
in (_165_73)::_165_72))
in (FStar_Pprint.concat _165_74))
in (FStar_Pprint.group _165_75))
end))


let is_unit : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Const (FStar_Const.Const_unit) -> begin
true
end
| _67_54 -> begin
false
end))


let matches_var : FStar_Parser_AST.term  ->  FStar_Ident.ident  ->  Prims.bool = (fun t x -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (y) -> begin
(x.FStar_Ident.idText = (FStar_Ident.text_of_lid y))
end
| _67_60 -> begin
false
end))


let is_tuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Syntax_Util.is_tuple_data_lid'


let is_dtuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Syntax_Util.is_dtuple_data_lid'


let is_list_structure : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun cons_lid nil_lid -> (

let rec aux = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (lid, []) -> begin
(FStar_Ident.lid_equals lid nil_lid)
end
| FStar_Parser_AST.Construct (lid, (_67_75)::((e2, _67_72))::[]) -> begin
((FStar_Ident.lid_equals lid cons_lid) && (aux e2))
end
| _67_80 -> begin
false
end))
in aux))


let is_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Syntax_Const.cons_lid FStar_Syntax_Const.nil_lid)


let is_lex_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Syntax_Const.lexcons_lid FStar_Syntax_Const.lextop_lid)


let rec extract_from_list : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (_67_83, []) -> begin
[]
end
| FStar_Parser_AST.Construct (_67_88, ((e1, FStar_Parser_AST.Nothing))::((e2, FStar_Parser_AST.Nothing))::[]) -> begin
(let _165_98 = (extract_from_list e2)
in (e1)::_165_98)
end
| _67_99 -> begin
(let _165_100 = (let _165_99 = (FStar_Parser_AST.term_to_string e)
in (FStar_Util.format1 "Not a list %s" _165_99))
in (FStar_All.failwith _165_100))
end))


let is_array : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (lid); FStar_Parser_AST.range = _67_104; FStar_Parser_AST.level = _67_102}, l, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals lid FStar_Syntax_Const.array_mk_array_lid) && (is_list l))
end
| _67_113 -> begin
false
end))


let rec is_ref_set : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (maybe_empty_lid) -> begin
(FStar_Ident.lid_equals maybe_empty_lid FStar_Syntax_Const.tset_empty)
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_singleton_lid); FStar_Parser_AST.range = _67_120; FStar_Parser_AST.level = _67_118}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_ref_lid); FStar_Parser_AST.range = _67_131; FStar_Parser_AST.level = _67_129}, e, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = _67_127; FStar_Parser_AST.level = _67_125}, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals maybe_singleton_lid FStar_Syntax_Const.tset_singleton) && (FStar_Ident.lid_equals maybe_ref_lid FStar_Syntax_Const.heap_ref))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_union_lid); FStar_Parser_AST.range = _67_150; FStar_Parser_AST.level = _67_148}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = _67_146; FStar_Parser_AST.level = _67_144}, e2, FStar_Parser_AST.Nothing) -> begin
(((FStar_Ident.lid_equals maybe_union_lid FStar_Syntax_Const.tset_union) && (is_ref_set e1)) && (is_ref_set e2))
end
| _67_164 -> begin
false
end))


let rec extract_from_ref_set : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (_67_167) -> begin
[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (_67_174); FStar_Parser_AST.range = _67_172; FStar_Parser_AST.level = _67_170}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (_67_186); FStar_Parser_AST.range = _67_184; FStar_Parser_AST.level = _67_182}, e, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = _67_180; FStar_Parser_AST.level = _67_178}, FStar_Parser_AST.Nothing) -> begin
(e)::[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (_67_206); FStar_Parser_AST.range = _67_204; FStar_Parser_AST.level = _67_202}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = _67_200; FStar_Parser_AST.level = _67_198}, e2, FStar_Parser_AST.Nothing) -> begin
(let _165_108 = (extract_from_ref_set e1)
in (let _165_107 = (extract_from_ref_set e2)
in (FStar_List.append _165_108 _165_107)))
end
| _67_219 -> begin
(let _165_110 = (let _165_109 = (FStar_Parser_AST.term_to_string e)
in (FStar_Util.format1 "Not a ref set %s" _165_109))
in (FStar_All.failwith _165_110))
end))


let is_general_application : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (not (((((is_array e) || (is_list e)) || (is_lex_list e)) || (is_ref_set e)))))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun e -> (

let rec aux = (fun e acc -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App (head, arg, imp) -> begin
(aux head ((((arg), (imp)))::acc))
end
| _67_231 -> begin
((e), (acc))
end))
in (aux e [])))


type associativity =
| Left
| Right
| NonAssoc


let is_Left = (fun _discr_ -> (match (_discr_) with
| Left (_) -> begin
true
end
| _ -> begin
false
end))


let is_Right = (fun _discr_ -> (match (_discr_) with
| Right (_) -> begin
true
end
| _ -> begin
false
end))


let is_NonAssoc = (fun _discr_ -> (match (_discr_) with
| NonAssoc (_) -> begin
true
end
| _ -> begin
false
end))


type token =
(FStar_Char.char, Prims.string) FStar_Util.either


type associativity_level =
(associativity * token Prims.list)


let token_to_string : (FStar_BaseTypes.char, Prims.string) FStar_Util.either  ->  Prims.string = (fun _67_1 -> (match (_67_1) with
| FStar_Util.Inl (c) -> begin
(Prims.strcat (FStar_Util.string_of_char c) ".*")
end
| FStar_Util.Inr (s) -> begin
s
end))


let matches_token : Prims.string  ->  (FStar_Char.char, Prims.string) FStar_Util.either  ->  Prims.bool = (fun s _67_2 -> (match (_67_2) with
| FStar_Util.Inl (c) -> begin
((FStar_String.get s (Prims.parse_int "0")) = c)
end
| FStar_Util.Inr (s') -> begin
(s = s')
end))


let matches_level = (fun s _67_246 -> (match (_67_246) with
| (assoc_levels, tokens) -> begin
((FStar_List.tryFind (matches_token s) tokens) <> None)
end))


let opinfix4 = ((Right), ((FStar_Util.Inr ("**"))::[]))


let opinfix3 = ((Left), ((FStar_Util.Inl ('*'))::(FStar_Util.Inl ('/'))::(FStar_Util.Inl ('%'))::[]))


let opinfix2 = ((Left), ((FStar_Util.Inl ('+'))::(FStar_Util.Inl ('-'))::[]))


let minus_lvl = ((Left), ((FStar_Util.Inr ("-"))::[]))


let opinfix1 = ((Right), ((FStar_Util.Inl ('@'))::(FStar_Util.Inl ('^'))::[]))


let pipe_right = ((Left), ((FStar_Util.Inr ("|>"))::[]))


let opinfix0d = ((Left), ((FStar_Util.Inl ('$'))::[]))


let opinfix0c = ((Left), ((FStar_Util.Inl ('='))::(FStar_Util.Inl ('<'))::(FStar_Util.Inl ('>'))::[]))


let equal = ((Left), ((FStar_Util.Inr ("="))::[]))


let opinfix0b = ((Left), ((FStar_Util.Inl ('&'))::[]))


let opinfix0a = ((Left), ((FStar_Util.Inl ('|'))::[]))


let colon_equals = ((NonAssoc), ((FStar_Util.Inr (":="))::[]))


let amp = ((Right), ((FStar_Util.Inr ("&"))::[]))


let colon_colon = ((Right), ((FStar_Util.Inr ("::"))::[]))


let level_associativity_spec : (associativity * (FStar_Char.char, Prims.string) FStar_Util.either Prims.list) Prims.list = (colon_colon)::(amp)::(colon_equals)::(opinfix0a)::(opinfix0b)::(opinfix0c)::(opinfix0d)::(pipe_right)::(opinfix1)::(opinfix2)::(opinfix3)::(opinfix4)::[]


let level_table : ((Prims.int * Prims.int * Prims.int) * (FStar_Char.char, Prims.string) FStar_Util.either Prims.list) Prims.list = (

let levels_from_associativity = (fun l _67_3 -> (match (_67_3) with
| Left -> begin
((l), (l), ((l - (Prims.parse_int "1"))))
end
| Right -> begin
(((l - (Prims.parse_int "1"))), (l), (l))
end
| NonAssoc -> begin
((l), (l), (l))
end))
in (FStar_List.mapi (fun i _67_256 -> (match (_67_256) with
| (assoc, tokens) -> begin
(((levels_from_associativity i assoc)), (tokens))
end)) level_associativity_spec))


let assign_levels : associativity_level Prims.list  ->  Prims.string  ->  (Prims.int * Prims.int * Prims.int) = (fun token_associativity_spec s -> (match ((FStar_List.tryFind (matches_level s) level_table)) with
| Some (assoc_levels, _67_261) -> begin
assoc_levels
end
| _67_265 -> begin
(FStar_All.failwith (Prims.strcat "Unrecognized operator " s))
end))


let max : Prims.int  ->  Prims.int  ->  Prims.int = (fun k1 k2 -> if (k1 > k2) then begin
k1
end else begin
k2
end)


let max_level = (fun l -> (

let find_level_and_max = (fun n level -> (match ((FStar_List.tryFind (fun _67_275 -> (match (_67_275) with
| (_67_273, tokens) -> begin
(tokens = (Prims.snd level))
end)) level_table)) with
| Some ((_67_277, l, _67_280), _67_283) -> begin
(max n l)
end
| None -> begin
(let _165_152 = (let _165_151 = (let _165_150 = (FStar_List.map token_to_string (Prims.snd level))
in (FStar_String.concat "," _165_150))
in (FStar_Util.format1 "Undefined associativity level %s" _165_151))
in (FStar_All.failwith _165_152))
end))
in (FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l)))


let levels : Prims.string  ->  (Prims.int * Prims.int * Prims.int) = (assign_levels level_associativity_spec)


let operatorInfix0ad12 = (opinfix0a)::(opinfix0b)::(opinfix0c)::(opinfix0d)::(opinfix1)::(opinfix2)::[]


let is_operatorInfix0ad12 : Prims.string  ->  Prims.bool = (fun op -> ((FStar_List.tryFind (matches_level op) operatorInfix0ad12) <> None))


let is_operatorInfix34 : Prims.string  ->  Prims.bool = (

let opinfix34 = (opinfix3)::(opinfix4)::[]
in (fun op -> ((FStar_List.tryFind (matches_level op) opinfix34) <> None)))


let doc_of_let_qualifier : FStar_Parser_AST.let_qualifier  ->  FStar_Pprint.document = (fun _67_4 -> (match (_67_4) with
| FStar_Parser_AST.NoLetQualifier -> begin
FStar_Pprint.empty
end
| FStar_Parser_AST.Rec -> begin
(str "rec")
end
| FStar_Parser_AST.Mutable -> begin
(str "mutable")
end))


let doc_of_imp : FStar_Parser_AST.imp  ->  FStar_Pprint.document = (fun _67_5 -> (match (_67_5) with
| FStar_Parser_AST.Hash -> begin
(str "#")
end
| FStar_Parser_AST.UnivApp -> begin
(str "u#")
end
| (FStar_Parser_AST.Nothing) | (FStar_Parser_AST.FsTypApp) -> begin
FStar_Pprint.empty
end))


let rec p_decl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (let _165_254 = (FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc)
in (let _165_253 = (p_decl2 d)
in (FStar_Pprint.op_Hat_Hat _165_254 _165_253))))
and p_fsdoc : FStar_Parser_AST.fsdoc  ->  FStar_Pprint.document = (fun _67_302 -> (match (_67_302) with
| (doc, kwd_args) -> begin
(let _165_266 = (let _165_265 = (str doc)
in (let _165_264 = (let _165_263 = (FStar_Pprint.concat_map (fun _67_305 -> (match (_67_305) with
| (kwd, arg) -> begin
(let _165_262 = (str "@")
in (let _165_261 = (let _165_260 = (str kwd)
in (let _165_259 = (let _165_258 = (let _165_257 = (str arg)
in (FStar_Pprint.op_Hat_Hat _165_257 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_258))
in (FStar_Pprint.op_Hat_Hat _165_260 _165_259)))
in (FStar_Pprint.op_Hat_Hat _165_262 _165_261)))
end)) kwd_args)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline _165_263))
in (FStar_Pprint.op_Hat_Hat _165_265 _165_264)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline _165_266))
end))
and p_decl2 : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Open (uid) -> begin
(let _165_270 = (let _165_269 = (str "open")
in (let _165_268 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat _165_269 _165_268)))
in (FStar_Pprint.group _165_270))
end
| FStar_Parser_AST.ModuleAbbrev (uid1, uid2) -> begin
(let _165_277 = (let _165_275 = (str "module")
in (let _165_274 = (let _165_273 = (let _165_272 = (p_uident uid1)
in (let _165_271 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _165_272 _165_271)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_273))
in (FStar_Pprint.op_Hat_Hat _165_275 _165_274)))
in (let _165_276 = (p_quident uid2)
in (op_Hat_Slash_Plus_Hat _165_277 _165_276)))
end
| FStar_Parser_AST.TopLevelModule (uid) -> begin
(let _165_281 = (let _165_280 = (str "module")
in (let _165_279 = (let _165_278 = (p_quident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_278))
in (FStar_Pprint.op_Hat_Hat _165_280 _165_279)))
in (FStar_Pprint.group _165_281))
end
| FStar_Parser_AST.KindAbbrev (_67_316) -> begin
(FStar_All.failwith "Deprecated, please stop throwing your old stuff at me !")
end
| FStar_Parser_AST.Tycon (qs, ((FStar_Parser_AST.TyconAbbrev (uid, tpars, None, t), None))::[]) when (FStar_List.contains FStar_Parser_AST.Effect qs) -> begin
(

let qs = (FStar_List.filter (fun q -> (q <> FStar_Parser_AST.Effect)) qs)
in (

let effect_prefix_doc = (let _165_287 = (p_qualifiers qs)
in (let _165_286 = (let _165_285 = (str "effect")
in (let _165_284 = (let _165_283 = (p_uident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_283))
in (FStar_Pprint.op_Hat_Hat _165_285 _165_284)))
in (FStar_Pprint.op_Hat_Hat _165_287 _165_286)))
in (let _165_290 = (let _165_288 = (p_typars tpars)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") effect_prefix_doc _165_288 FStar_Pprint.equals))
in (let _165_289 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _165_290 _165_289)))))
end
| FStar_Parser_AST.Tycon (qs, tcdefs) -> begin
(

let type_doc = (let _165_292 = (p_qualifiers qs)
in (let _165_291 = (str "type")
in (FStar_Pprint.op_Hat_Hat _165_292 _165_291)))
in (let _165_293 = (str "and")
in (precede_break_separate_map type_doc _165_293 p_fsdocTypeDeclPairs tcdefs)))
end
| FStar_Parser_AST.TopLevelLet (qs, q, lbs) -> begin
(

let let_doc = (let _165_297 = (p_qualifiers qs)
in (let _165_296 = (let _165_295 = (str "let")
in (let _165_294 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat _165_295 _165_294)))
in (FStar_Pprint.op_Hat_Hat _165_297 _165_296)))
in (let _165_298 = (str "and")
in (precede_break_separate_map let_doc _165_298 p_letbinding lbs)))
end
| FStar_Parser_AST.Val (qs, lid, t) -> begin
(let _165_307 = (let _165_305 = (p_qualifiers qs)
in (let _165_304 = (let _165_303 = (str "val")
in (let _165_302 = (let _165_301 = (let _165_300 = (p_lident lid)
in (let _165_299 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat _165_300 _165_299)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_301))
in (FStar_Pprint.op_Hat_Hat _165_303 _165_302)))
in (FStar_Pprint.op_Hat_Hat _165_305 _165_304)))
in (let _165_306 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _165_307 _165_306)))
end
| FStar_Parser_AST.Assume (qs, id, t) -> begin
(

let decl_keyword = if (let _165_308 = (FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_All.pipe_right _165_308 FStar_Util.is_upper)) then begin
FStar_Pprint.empty
end else begin
(let _165_309 = (str "val")
in (FStar_Pprint.op_Hat_Hat _165_309 FStar_Pprint.space))
end
in (let _165_316 = (let _165_314 = (p_qualifiers qs)
in (let _165_313 = (let _165_312 = (let _165_311 = (p_ident id)
in (let _165_310 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat _165_311 _165_310)))
in (FStar_Pprint.op_Hat_Hat decl_keyword _165_312))
in (FStar_Pprint.op_Hat_Hat _165_314 _165_313)))
in (let _165_315 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _165_316 _165_315))))
end
| FStar_Parser_AST.Exception (uid, t_opt) -> begin
(let _165_324 = (str "exception")
in (let _165_323 = (let _165_322 = (let _165_321 = (p_uident uid)
in (let _165_320 = (FStar_Pprint.optional (fun t -> (let _165_319 = (str "of")
in (let _165_318 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _165_319 _165_318)))) t_opt)
in (FStar_Pprint.op_Hat_Hat _165_321 _165_320)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_322))
in (FStar_Pprint.op_Hat_Hat _165_324 _165_323)))
end
| FStar_Parser_AST.NewEffect (qs, ne) -> begin
(let _165_329 = (p_qualifiers qs)
in (let _165_328 = (let _165_327 = (str "new_effect")
in (let _165_326 = (let _165_325 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_325))
in (FStar_Pprint.op_Hat_Hat _165_327 _165_326)))
in (FStar_Pprint.op_Hat_Hat _165_329 _165_328)))
end
| FStar_Parser_AST.SubEffect (se) -> begin
(let _165_332 = (str "sub_effect")
in (let _165_331 = (let _165_330 = (p_subEffect se)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_330))
in (FStar_Pprint.op_Hat_Hat _165_332 _165_331)))
end
| FStar_Parser_AST.NewEffectForFree (qs, ne) -> begin
(let _165_337 = (p_qualifiers qs)
in (let _165_336 = (let _165_335 = (str "new_effect_for_free")
in (let _165_334 = (let _165_333 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_333))
in (FStar_Pprint.op_Hat_Hat _165_335 _165_334)))
in (FStar_Pprint.op_Hat_Hat _165_337 _165_336)))
end
| FStar_Parser_AST.Pragma (p) -> begin
(p_pragma p)
end
| FStar_Parser_AST.Fsdoc (doc) -> begin
(let _165_338 = (p_fsdoc doc)
in (FStar_Pprint.op_Hat_Hat _165_338 FStar_Pprint.hardline))
end
| FStar_Parser_AST.Main (_67_375) -> begin
(FStar_All.failwith "*Main declaration* : Is that really still in use ??")
end))
and p_pragma : FStar_Parser_AST.pragma  ->  FStar_Pprint.document = (fun _67_6 -> (match (_67_6) with
| FStar_Parser_AST.SetOptions (s) -> begin
(let _165_343 = (str "#set-options")
in (let _165_342 = (let _165_341 = (let _165_340 = (str s)
in (FStar_Pprint.dquotes _165_340))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_341))
in (FStar_Pprint.op_Hat_Hat _165_343 _165_342)))
end
| FStar_Parser_AST.ResetOptions (s_opt) -> begin
(let _165_348 = (str "#reset-options")
in (let _165_347 = (FStar_Pprint.optional (fun s -> (let _165_346 = (let _165_345 = (str s)
in (FStar_Pprint.dquotes _165_345))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_346))) s_opt)
in (FStar_Pprint.op_Hat_Hat _165_348 _165_347)))
end))
and p_typars : FStar_Parser_AST.binder Prims.list  ->  FStar_Pprint.document = (fun bs -> (p_binders bs))
and p_fsdocTypeDeclPairs : (FStar_Parser_AST.tycon * FStar_Parser_AST.fsdoc Prims.option)  ->  FStar_Pprint.document = (fun _67_386 -> (match (_67_386) with
| (typedecl, fsdoc_opt) -> begin
(let _165_352 = (FStar_Pprint.optional p_fsdoc fsdoc_opt)
in (let _165_351 = (p_typeDecl typedecl)
in (FStar_Pprint.op_Hat_Hat _165_352 _165_351)))
end))
and p_typeDecl : FStar_Parser_AST.tycon  ->  FStar_Pprint.document = (fun _67_7 -> (match (_67_7) with
| FStar_Parser_AST.TyconAbstract (lid, bs, typ_opt) -> begin
(p_typeDeclPrefix lid bs typ_opt)
end
| FStar_Parser_AST.TyconAbbrev (lid, bs, typ_opt, t) -> begin
(let _165_355 = (p_typeDeclPrefix lid bs typ_opt)
in (let _165_354 = (p_typ t)
in (infix2 FStar_Pprint.equals _165_355 _165_354)))
end
| FStar_Parser_AST.TyconRecord (lid, bs, typ_opt, record_field_decls) -> begin
(let _165_359 = (p_typeDeclPrefix lid bs typ_opt)
in (let _165_358 = (let _165_357 = (let _165_356 = (separate_break_map FStar_Pprint.semi p_recordFieldDecl record_field_decls)
in (braces_with_nesting _165_356))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.equals _165_357))
in (FStar_Pprint.op_Hat_Slash_Hat _165_359 _165_358)))
end
| FStar_Parser_AST.TyconVariant (lid, bs, typ_opt, ct_decls) -> begin
(let _165_366 = (p_typeDeclPrefix lid bs typ_opt)
in (let _165_365 = (let _165_364 = (FStar_Pprint.separate_map break1 (fun decl -> (let _165_363 = (let _165_362 = (let _165_361 = (p_constructorDecl decl)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_361))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar _165_362))
in (FStar_Pprint.group _165_363))) ct_decls)
in (FStar_Pprint.group _165_364))
in (infix2 FStar_Pprint.equals _165_366 _165_365)))
end))
and p_typeDeclPrefix : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.knd Prims.option  ->  FStar_Pprint.document = (fun lid bs typ_opt -> (let _165_376 = (p_ident lid)
in (let _165_375 = (let _165_374 = (p_typars bs)
in (let _165_373 = (FStar_Pprint.optional (fun t -> (let _165_372 = (let _165_371 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_371))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_372))) typ_opt)
in (FStar_Pprint.op_Hat_Hat _165_374 _165_373)))
in (op_Hat_Slash_Plus_Hat _165_376 _165_375))))
and p_recordFieldDecl : (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc Prims.option)  ->  FStar_Pprint.document = (fun _67_419 -> (match (_67_419) with
| (lid, t, doc_opt) -> begin
(let _165_382 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (let _165_381 = (let _165_380 = (p_lident lid)
in (let _165_379 = (let _165_378 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_378))
in (FStar_Pprint.op_Hat_Hat _165_380 _165_379)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_382 _165_381)))
end))
and p_constructorDecl : (FStar_Ident.ident * FStar_Parser_AST.term Prims.option * FStar_Parser_AST.fsdoc Prims.option * Prims.bool)  ->  FStar_Pprint.document = (fun _67_424 -> (match (_67_424) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let sep = if use_of then begin
(str "of")
end else begin
FStar_Pprint.colon
end
in (

let uid_doc = (p_uident uid)
in (let _165_389 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (let _165_388 = (default_or_map uid_doc (fun t -> (let _165_387 = (let _165_385 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep)
in (FStar_Pprint.op_Hat_Hat uid_doc _165_385))
in (let _165_386 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _165_387 _165_386)))) t_opt)
in (FStar_Pprint.op_Hat_Hat _165_389 _165_388)))))
end))
and p_letbinding : (FStar_Parser_AST.pattern * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun _67_430 -> (match (_67_430) with
| (pat, e) -> begin
(

let pat_doc = (

let _67_439 = (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, t) -> begin
(let _165_394 = (let _165_393 = (let _165_392 = (let _165_391 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat break1 _165_391))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_392))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_393))
in ((pat), (_165_394)))
end
| _67_436 -> begin
((pat), (FStar_Pprint.empty))
end)
in (match (_67_439) with
| (pat, ascr_doc) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _67_444); FStar_Parser_AST.prange = _67_441}, pats) -> begin
(let _165_397 = (p_lident x)
in (let _165_396 = (let _165_395 = (FStar_Pprint.separate_map break1 p_tuplePattern pats)
in (FStar_Pprint.op_Hat_Hat _165_395 ascr_doc))
in (prefix2 _165_397 _165_396)))
end
| _67_452 -> begin
(let _165_398 = (p_tuplePattern pat)
in (FStar_Pprint.op_Hat_Hat _165_398 ascr_doc))
end)
end))
in (let _165_401 = (let _165_400 = (let _165_399 = (p_term e)
in (prefix2 FStar_Pprint.equals _165_399))
in (FStar_Pprint.op_Hat_Slash_Hat pat_doc _165_400))
in (FStar_Pprint.group _165_401)))
end))
and p_newEffect : FStar_Parser_AST.effect_decl  ->  FStar_Pprint.document = (fun _67_8 -> (match (_67_8) with
| FStar_Parser_AST.RedefineEffect (lid, bs, t) -> begin
(p_effectRedefinition lid bs t)
end
| FStar_Parser_AST.DefineEffect (lid, bs, t, eff_decls, action_decls) -> begin
(p_effectDefinition lid bs t eff_decls action_decls)
end))
and p_effectRedefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun uid bs t -> (let _165_409 = (p_uident uid)
in (let _165_408 = (p_binders bs)
in (let _165_407 = (let _165_406 = (p_simpleTerm t)
in (prefix2 FStar_Pprint.equals _165_406))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_409 _165_408 _165_407)))))
and p_effectDefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun uid bs t eff_decls action_decls -> (let _165_427 = (let _165_426 = (let _165_420 = (let _165_419 = (let _165_416 = (p_uident uid)
in (let _165_415 = (p_binders bs)
in (prefix2 _165_416 _165_415)))
in (let _165_418 = (let _165_417 = (p_typ t)
in (prefix2 FStar_Pprint.colon _165_417))
in (FStar_Pprint.op_Hat_Hat _165_419 _165_418)))
in (FStar_Pprint.group _165_420))
in (let _165_425 = (let _165_424 = (let _165_422 = (str "with")
in (let _165_421 = (separate_break_map FStar_Pprint.semi p_effectDecl eff_decls)
in (prefix2 _165_422 _165_421)))
in (let _165_423 = (p_actionDecls action_decls)
in (FStar_Pprint.op_Hat_Hat _165_424 _165_423)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_426 _165_425)))
in (braces_with_nesting _165_427)))
and p_actionDecls : FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun _67_9 -> (match (_67_9) with
| [] -> begin
FStar_Pprint.empty
end
| l -> begin
(let _165_431 = (let _165_430 = (str "and actions")
in (let _165_429 = (separate_break_map FStar_Pprint.semi p_effectDecl l)
in (prefix2 _165_430 _165_429)))
in (FStar_Pprint.op_Hat_Hat break1 _165_431))
end))
and p_effectDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon ([], ((FStar_Parser_AST.TyconAbbrev (lid, [], None, e), None))::[]) -> begin
(let _165_436 = (let _165_434 = (p_lident lid)
in (let _165_433 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _165_434 _165_433)))
in (let _165_435 = (p_simpleTerm e)
in (prefix2 _165_436 _165_435)))
end
| _67_492 -> begin
(let _165_438 = (let _165_437 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "Not a declaration of an effect member... or at least I hope so : %s" _165_437))
in (FStar_All.failwith _165_438))
end))
and p_subEffect : FStar_Parser_AST.lift  ->  FStar_Pprint.document = (fun lift -> (

let lift_op_doc = (

let lifts = (match (lift.FStar_Parser_AST.lift_op) with
| FStar_Parser_AST.NonReifiableLift (t) -> begin
((("lift_wp"), (t)))::[]
end
| FStar_Parser_AST.ReifiableLift (t1, t2) -> begin
((("lif_wp"), (t1)))::((("lift"), (t2)))::[]
end
| FStar_Parser_AST.LiftForFree (t) -> begin
((("lift"), (t)))::[]
end)
in (

let p_lift = (fun _67_506 -> (match (_67_506) with
| (kwd, t) -> begin
(let _165_445 = (let _165_443 = (str kwd)
in (let _165_442 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _165_443 _165_442)))
in (let _165_444 = (p_simpleTerm t)
in (prefix2 _165_445 _165_444)))
end))
in (separate_break_map FStar_Pprint.semi p_lift lifts)))
in (let _165_453 = (let _165_450 = (let _165_448 = (p_quident lift.FStar_Parser_AST.msource)
in (let _165_447 = (let _165_446 = (str "~>")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_446))
in (FStar_Pprint.op_Hat_Hat _165_448 _165_447)))
in (let _165_449 = (p_quident lift.FStar_Parser_AST.mdest)
in (prefix2 _165_450 _165_449)))
in (let _165_452 = (let _165_451 = (braces_with_nesting lift_op_doc)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_451))
in (FStar_Pprint.op_Hat_Hat _165_453 _165_452)))))
and p_qualifier : FStar_Parser_AST.qualifier  ->  FStar_Pprint.document = (fun _67_10 -> (match (_67_10) with
| FStar_Parser_AST.Private -> begin
(str "private")
end
| FStar_Parser_AST.Abstract -> begin
(str "abstract")
end
| FStar_Parser_AST.Noeq -> begin
(str "noeq")
end
| FStar_Parser_AST.Unopteq -> begin
(str "unopteq")
end
| FStar_Parser_AST.Assumption -> begin
(str "assume")
end
| FStar_Parser_AST.DefaultEffect -> begin
(str "default")
end
| FStar_Parser_AST.TotalEffect -> begin
(str "total")
end
| FStar_Parser_AST.Effect -> begin
FStar_Pprint.empty
end
| FStar_Parser_AST.New -> begin
(str "new")
end
| FStar_Parser_AST.Inline -> begin
(str "inline")
end
| FStar_Parser_AST.Visible -> begin
FStar_Pprint.empty
end
| FStar_Parser_AST.Unfold_for_unification_and_vcgen -> begin
(str "unfold")
end
| FStar_Parser_AST.Inline_for_extraction -> begin
(str "inline_for_extraction")
end
| FStar_Parser_AST.Irreducible -> begin
(str "irreducible")
end
| FStar_Parser_AST.NoExtract -> begin
(str "noextract")
end
| FStar_Parser_AST.Reifiable -> begin
(str "reifiable")
end
| FStar_Parser_AST.Reflectable -> begin
(str "reflectable")
end
| FStar_Parser_AST.Opaque -> begin
(str "opaque")
end
| FStar_Parser_AST.Logic -> begin
(str "logic")
end))
and p_qualifiers : FStar_Parser_AST.qualifier Prims.list  ->  FStar_Pprint.document = (fun qs -> (let _165_457 = (let _165_456 = (FStar_Pprint.separate_map break1 p_qualifier qs)
in (FStar_Pprint.op_Hat_Hat _165_456 (if (qs = []) then begin
FStar_Pprint.empty
end else begin
FStar_Pprint.space
end)))
in (FStar_Pprint.group _165_457)))
and p_letqualifier : FStar_Parser_AST.let_qualifier  ->  FStar_Pprint.document = (fun _67_11 -> (match (_67_11) with
| FStar_Parser_AST.Rec -> begin
(let _165_459 = (str "rec")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_459))
end
| FStar_Parser_AST.Mutable -> begin
(let _165_460 = (str "mutable")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_460))
end
| FStar_Parser_AST.NoLetQualifier -> begin
FStar_Pprint.empty
end))
and p_aqual : FStar_Parser_AST.arg_qualifier  ->  FStar_Pprint.document = (fun _67_12 -> (match (_67_12) with
| FStar_Parser_AST.Implicit -> begin
(str "#")
end
| FStar_Parser_AST.Equality -> begin
(str "$")
end))
and p_disjunctivePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr (pats) -> begin
(let _165_465 = (let _165_464 = (let _165_463 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space)
in (FStar_Pprint.op_Hat_Hat break1 _165_463))
in (FStar_Pprint.separate_map _165_464 p_tuplePattern pats))
in (FStar_Pprint.group _165_465))
end
| _67_540 -> begin
(p_tuplePattern p)
end))
and p_tuplePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTuple (pats, false) -> begin
(let _165_467 = (separate_break_map FStar_Pprint.comma p_constructorPattern pats)
in (FStar_Pprint.group _165_467))
end
| _67_547 -> begin
(p_constructorPattern p)
end))
and p_constructorPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (maybe_cons_lid); FStar_Parser_AST.prange = _67_550}, (hd)::(tl)::[]) when (FStar_Ident.lid_equals maybe_cons_lid FStar_Syntax_Const.cons_lid) -> begin
(let _165_471 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon)
in (let _165_470 = (p_constructorPattern hd)
in (let _165_469 = (p_constructorPattern tl)
in (infix2 _165_471 _165_470 _165_469))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (uid); FStar_Parser_AST.prange = _67_560}, pats) -> begin
(let _165_473 = (p_quident uid)
in (let _165_472 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (prefix2 _165_473 _165_472)))
end
| _67_568 -> begin
(p_atomicPattern p)
end))
and p_atomicPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, t) -> begin
(let _165_477 = (let _165_476 = (p_tuplePattern pat)
in (let _165_475 = (p_typ t)
in (infix2 FStar_Pprint.colon _165_476 _165_475)))
in (parens_with_nesting _165_477))
end
| FStar_Parser_AST.PatList (pats) -> begin
(let _165_478 = (separate_break_map FStar_Pprint.semi p_tuplePattern pats)
in (brackets_with_nesting _165_478))
end
| FStar_Parser_AST.PatRecord (pats) -> begin
(

let p_recordFieldPat = (fun _67_581 -> (match (_67_581) with
| (lid, pat) -> begin
(let _165_482 = (p_qlident lid)
in (let _165_481 = (p_tuplePattern pat)
in (infix2 FStar_Pprint.equals _165_482 _165_481)))
end))
in (let _165_483 = (separate_break_map FStar_Pprint.semi p_recordFieldPat pats)
in (braces_with_nesting _165_483)))
end
| FStar_Parser_AST.PatTuple (pats, true) -> begin
(let _165_487 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (let _165_486 = (let _165_484 = (str "&")
in (separate_break_map _165_484 p_constructorPattern pats))
in (let _165_485 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_487 _165_486 _165_485))))
end
| FStar_Parser_AST.PatTvar (tv, arg_qualifier_opt) -> begin
(

let _67_590 = ()
in (p_tvar tv))
end
| FStar_Parser_AST.PatOp (op) -> begin
(let _165_491 = (let _165_490 = (let _165_489 = (str op)
in (let _165_488 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat _165_489 _165_488)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_490))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_491))
end
| FStar_Parser_AST.PatWild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.PatConst (c) -> begin
(p_constant c)
end
| FStar_Parser_AST.PatVar (lid, aqual) -> begin
(let _165_493 = (FStar_Pprint.optional p_aqual aqual)
in (let _165_492 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat _165_493 _165_492)))
end
| FStar_Parser_AST.PatName (uid) -> begin
(p_quident uid)
end
| FStar_Parser_AST.PatOr (_67_604) -> begin
(FStar_All.failwith "Inner or pattern !")
end
| (FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (_); FStar_Parser_AST.prange = _}, _)) | (FStar_Parser_AST.PatTuple (_, false)) -> begin
(let _165_494 = (p_tuplePattern p)
in (parens_with_nesting _165_494))
end
| _67_622 -> begin
(let _165_496 = (let _165_495 = (FStar_Parser_AST.pat_to_string p)
in (FStar_Util.format1 "Invalid pattern %s" _165_495))
in (FStar_All.failwith _165_496))
end))
and p_binder : FStar_Parser_AST.binder  ->  FStar_Pprint.document = (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (lid) -> begin
(let _165_499 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (let _165_498 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat _165_499 _165_498)))
end
| FStar_Parser_AST.TVariable (lid) -> begin
(p_lident lid)
end
| FStar_Parser_AST.Annotated (lid, t) -> begin
(let _165_506 = (let _165_505 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (let _165_504 = (let _165_503 = (p_lident lid)
in (let _165_502 = (let _165_501 = (let _165_500 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat _165_500 FStar_Pprint.rparen))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_501))
in (FStar_Pprint.op_Hat_Hat _165_503 _165_502)))
in (FStar_Pprint.op_Hat_Hat _165_505 _165_504)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_506))
end
| FStar_Parser_AST.TAnnotated (_67_633) -> begin
(FStar_All.failwith "Is this still used ?")
end
| FStar_Parser_AST.NoName (t) -> begin
(let _165_512 = (let _165_511 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (let _165_510 = (let _165_509 = (let _165_508 = (let _165_507 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat _165_507 FStar_Pprint.rparen))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_508))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.underscore _165_509))
in (FStar_Pprint.op_Hat_Hat _165_511 _165_510)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_512))
end))
and p_binders : FStar_Parser_AST.binder Prims.list  ->  FStar_Pprint.document = (fun bs -> (concat_break_map p_binder bs))
and p_qlident : FStar_Ident.lid  ->  FStar_Pprint.document = (fun lid -> (str (FStar_Ident.text_of_lid lid)))
and p_quident : FStar_Ident.lid  ->  FStar_Pprint.document = (fun lid -> (str (FStar_Ident.text_of_lid lid)))
and p_ident : FStar_Ident.ident  ->  FStar_Pprint.document = (fun lid -> (str (FStar_Ident.text_of_id lid)))
and p_lident : FStar_Ident.ident  ->  FStar_Pprint.document = (fun lid -> (str (FStar_Ident.text_of_id lid)))
and p_uident : FStar_Ident.ident  ->  FStar_Pprint.document = (fun lid -> (str (FStar_Ident.text_of_id lid)))
and p_tvar : FStar_Ident.ident  ->  FStar_Pprint.document = (fun lid -> (str (FStar_Ident.text_of_id lid)))
and p_lidentOrUnderscore : FStar_Ident.ident  ->  FStar_Pprint.document = (fun id -> if (FStar_Util.starts_with FStar_Ident.reserved_prefix id.FStar_Ident.idText) then begin
FStar_Pprint.underscore
end else begin
(p_lident id)
end)
and p_term : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Seq (e1, e2) -> begin
(let _165_525 = (let _165_523 = (let _165_522 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat _165_522 FStar_Pprint.semi))
in (FStar_Pprint.group _165_523))
in (let _165_524 = (p_term e2)
in (FStar_Pprint.op_Hat_Slash_Hat _165_525 _165_524)))
end
| _67_651 -> begin
(let _165_526 = (p_noSeqTerm e)
in (FStar_Pprint.group _165_526))
end))
and p_noSeqTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Ascribed (e, t) -> begin
(let _165_532 = (let _165_531 = (p_tmIff e)
in (let _165_530 = (let _165_529 = (let _165_528 = (p_typ t)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon _165_528))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.langle _165_529))
in (FStar_Pprint.op_Hat_Slash_Hat _165_531 _165_530)))
in (FStar_Pprint.group _165_532))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::(e3)::[]) when (op = ".()<-") -> begin
(let _165_543 = (let _165_542 = (let _165_539 = (let _165_538 = (p_atomicTermNotQUident e1)
in (let _165_537 = (let _165_536 = (let _165_535 = (let _165_533 = (p_term e2)
in (parens_with_nesting _165_533))
in (let _165_534 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat _165_535 _165_534)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_536))
in (FStar_Pprint.op_Hat_Hat _165_538 _165_537)))
in (FStar_Pprint.group _165_539))
in (let _165_541 = (let _165_540 = (p_noSeqTerm e3)
in (jump2 _165_540))
in (FStar_Pprint.op_Hat_Hat _165_542 _165_541)))
in (FStar_Pprint.group _165_543))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::(e3)::[]) when (op = ".[]<-") -> begin
(let _165_554 = (let _165_553 = (let _165_550 = (let _165_549 = (p_atomicTermNotQUident e1)
in (let _165_548 = (let _165_547 = (let _165_546 = (let _165_544 = (p_term e2)
in (brackets_with_nesting _165_544))
in (let _165_545 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat _165_546 _165_545)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_547))
in (FStar_Pprint.op_Hat_Hat _165_549 _165_548)))
in (FStar_Pprint.group _165_550))
in (let _165_552 = (let _165_551 = (p_noSeqTerm e3)
in (jump2 _165_551))
in (FStar_Pprint.op_Hat_Hat _165_553 _165_552)))
in (FStar_Pprint.group _165_554))
end
| FStar_Parser_AST.Requires (e, wtf) -> begin
(

let _67_675 = ()
in (let _165_557 = (let _165_556 = (str "requires")
in (let _165_555 = (p_typ e)
in (FStar_Pprint.op_Hat_Slash_Hat _165_556 _165_555)))
in (FStar_Pprint.group _165_557)))
end
| FStar_Parser_AST.Ensures (e, wtf) -> begin
(

let _67_681 = ()
in (let _165_560 = (let _165_559 = (str "ensures")
in (let _165_558 = (p_typ e)
in (FStar_Pprint.op_Hat_Slash_Hat _165_559 _165_558)))
in (FStar_Pprint.group _165_560)))
end
| FStar_Parser_AST.Attributes (es) -> begin
(let _165_563 = (let _165_562 = (str "attributes")
in (let _165_561 = (FStar_Pprint.separate_map break1 p_atomicTerm es)
in (FStar_Pprint.op_Hat_Slash_Hat _165_562 _165_561)))
in (FStar_Pprint.group _165_563))
end
| FStar_Parser_AST.If (e1, e2, e3) -> begin
if (is_unit e3) then begin
(let _165_570 = (let _165_569 = (let _165_565 = (str "if")
in (let _165_564 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat _165_565 _165_564)))
in (let _165_568 = (let _165_567 = (str "then")
in (let _165_566 = (p_noSeqTerm e2)
in (op_Hat_Slash_Plus_Hat _165_567 _165_566)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_569 _165_568)))
in (FStar_Pprint.group _165_570))
end else begin
(

let e2_doc = (match (e2.FStar_Parser_AST.tm) with
| FStar_Parser_AST.If (_67_691, _67_693, e3) when (is_unit e3) -> begin
(let _165_571 = (p_noSeqTerm e2)
in (parens_with_nesting _165_571))
end
| _67_698 -> begin
(p_noSeqTerm e2)
end)
in (let _165_581 = (let _165_580 = (let _165_573 = (str "if")
in (let _165_572 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat _165_573 _165_572)))
in (let _165_579 = (let _165_578 = (let _165_574 = (str "then")
in (op_Hat_Slash_Plus_Hat _165_574 e2_doc))
in (let _165_577 = (let _165_576 = (str "else")
in (let _165_575 = (p_noSeqTerm e3)
in (op_Hat_Slash_Plus_Hat _165_576 _165_575)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_578 _165_577)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_580 _165_579)))
in (FStar_Pprint.group _165_581)))
end
end
| FStar_Parser_AST.TryWith (e, branches) -> begin
(let _165_589 = (let _165_588 = (let _165_583 = (str "try")
in (let _165_582 = (p_noSeqTerm e)
in (prefix2 _165_583 _165_582)))
in (let _165_587 = (let _165_586 = (str "with")
in (let _165_585 = (let _165_584 = (FStar_Pprint.concat_map p_patternBranch branches)
in (jump2 _165_584))
in (FStar_Pprint.op_Hat_Slash_Hat _165_586 _165_585)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_588 _165_587)))
in (FStar_Pprint.group _165_589))
end
| FStar_Parser_AST.Match (e, branches) -> begin
(let _165_597 = (let _165_596 = (let _165_591 = (str "match")
in (let _165_590 = (p_noSeqTerm e)
in (prefix2 _165_591 _165_590)))
in (let _165_595 = (let _165_594 = (str "with")
in (let _165_593 = (let _165_592 = (FStar_Pprint.concat_map p_patternBranch branches)
in (jump2 _165_592))
in (FStar_Pprint.op_Hat_Slash_Hat _165_594 _165_593)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_596 _165_595)))
in (FStar_Pprint.group _165_597))
end
| FStar_Parser_AST.LetOpen (uid, e) -> begin
(let _165_602 = (let _165_601 = (str "let open")
in (let _165_600 = (let _165_599 = (p_quident uid)
in (let _165_598 = (str "in")
in (FStar_Pprint.op_Hat_Slash_Hat _165_599 _165_598)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_601 _165_600)))
in (FStar_Pprint.group _165_602))
end
| FStar_Parser_AST.Let (q, lbs, e) -> begin
(

let let_doc = (let _165_604 = (str "let")
in (let _165_603 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat _165_604 _165_603)))
in (let _165_607 = (let _165_605 = (str "and")
in (precede_break_separate_map let_doc _165_605 p_letbinding lbs))
in (let _165_606 = (str "in")
in (FStar_Pprint.op_Hat_Slash_Hat _165_607 _165_606))))
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, typ_opt); FStar_Parser_AST.prange = _67_719})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, branches); FStar_Parser_AST.range = _67_729; FStar_Parser_AST.level = _67_727}) when (matches_var maybe_x x) -> begin
(let _165_609 = (str "function")
in (let _165_608 = (FStar_Pprint.concat_map p_patternBranch branches)
in (op_Hat_Slash_Plus_Hat _165_609 _165_608)))
end
| FStar_Parser_AST.Assign (id, e) -> begin
(let _165_613 = (let _165_612 = (p_lident id)
in (let _165_611 = (let _165_610 = (p_noSeqTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow _165_610))
in (FStar_Pprint.op_Hat_Slash_Hat _165_612 _165_611)))
in (FStar_Pprint.group _165_613))
end
| _67_742 -> begin
(p_typ e)
end))
and p_typ : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| (FStar_Parser_AST.QForall (bs, trigger, e1)) | (FStar_Parser_AST.QExists (bs, trigger, e1)) -> begin
(let _165_623 = (let _165_622 = (let _165_620 = (let _165_619 = (p_quantifier e)
in (let _165_618 = (let _165_617 = (p_binders bs)
in (let _165_616 = (let _165_615 = (p_trigger trigger)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_615))
in (FStar_Pprint.op_Hat_Hat _165_617 _165_616)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_619 _165_618)))
in (FStar_Pprint.group _165_620))
in (let _165_621 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Slash_Hat _165_622 _165_621)))
in (FStar_Pprint.group _165_623))
end
| _67_752 -> begin
(p_simpleTerm e)
end))
and p_quantifier : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.QForall (_67_755) -> begin
(str "forall")
end
| FStar_Parser_AST.QExists (_67_758) -> begin
(str "exists")
end
| _67_761 -> begin
(FStar_All.failwith "Imposible : p_quantifier called on a non-quantifier term")
end))
and p_trigger : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun _67_13 -> (match (_67_13) with
| [] -> begin
FStar_Pprint.empty
end
| pats -> begin
(let _165_631 = (let _165_630 = (let _165_629 = (str "pattern")
in (let _165_628 = (let _165_627 = (let _165_626 = (p_disjunctivePats pats)
in (jump2 _165_626))
in (FStar_Pprint.op_Hat_Slash_Hat _165_627 FStar_Pprint.rbrace))
in (FStar_Pprint.op_Hat_Slash_Hat _165_629 _165_628)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_630))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace _165_631))
end))
and p_disjunctivePats : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun pats -> (let _165_633 = (str "\\/")
in (FStar_Pprint.separate_map _165_633 p_conjunctivePats pats)))
and p_conjunctivePats : FStar_Parser_AST.term Prims.list  ->  FStar_Pprint.document = (fun pats -> (let _165_635 = (FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats)
in (FStar_Pprint.group _165_635)))
and p_simpleTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Abs (pats, e) -> begin
(let _165_641 = (let _165_639 = (str "fun")
in (let _165_638 = (let _165_637 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Slash_Hat _165_637 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat _165_639 _165_638)))
in (let _165_640 = (p_term e)
in (op_Hat_Slash_Plus_Hat _165_641 _165_640)))
end
| _67_773 -> begin
(p_tmIff e)
end))
and p_maybeFocusArrow : Prims.bool  ->  FStar_Pprint.document = (fun b -> if b then begin
(str "~>")
end else begin
FStar_Pprint.rarrow
end)
and p_patternBranch : FStar_Parser_AST.branch  ->  FStar_Pprint.document = (fun _67_778 -> (match (_67_778) with
| (pat, when_opt, e) -> begin
(let _165_650 = (let _165_649 = (let _165_648 = (p_disjunctivePattern pat)
in (let _165_647 = (let _165_646 = (p_maybeWhen when_opt)
in (let _165_645 = (let _165_644 = (p_term e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.rarrow _165_644))
in (FStar_Pprint.op_Hat_Hat _165_646 _165_645)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_648 _165_647)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_649))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar _165_650))
end))
and p_maybeWhen : FStar_Parser_AST.term Prims.option  ->  FStar_Pprint.document = (fun _67_14 -> (match (_67_14) with
| None -> begin
FStar_Pprint.empty
end
| Some (e) -> begin
(let _165_654 = (str "when")
in (let _165_653 = (let _165_652 = (p_tmFormula e)
in (FStar_Pprint.op_Hat_Hat _165_652 FStar_Pprint.space))
in (op_Hat_Slash_Plus_Hat _165_654 _165_653)))
end))
and p_tmIff : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("<==>", (e1)::(e2)::[]) -> begin
(let _165_658 = (str "<==>")
in (let _165_657 = (p_tmImplies e1)
in (let _165_656 = (p_tmIff e2)
in (infix2 _165_658 _165_657 _165_656))))
end
| _67_791 -> begin
(p_tmImplies e)
end))
and p_tmImplies : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("==>", (e1)::(e2)::[]) -> begin
(let _165_662 = (str "==>")
in (let _165_661 = (p_tmArrow p_tmFormula e1)
in (let _165_660 = (p_tmImplies e2)
in (infix2 _165_662 _165_661 _165_660))))
end
| _67_800 -> begin
(p_tmArrow p_tmFormula e)
end))
and p_tmArrow : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_Tm e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Product (bs, tgt) -> begin
(let _165_674 = (let _165_673 = (FStar_Pprint.concat_map (fun b -> (let _165_671 = (p_binder b)
in (let _165_670 = (let _165_669 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_669))
in (FStar_Pprint.op_Hat_Hat _165_671 _165_670)))) bs)
in (let _165_672 = (p_tmArrow p_Tm tgt)
in (FStar_Pprint.op_Hat_Hat _165_673 _165_672)))
in (FStar_Pprint.group _165_674))
end
| _67_809 -> begin
(p_Tm e)
end))
and p_tmFormula : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("\\/", (e1)::(e2)::[]) -> begin
(let _165_678 = (str "\\/")
in (let _165_677 = (p_tmFormula e1)
in (let _165_676 = (p_tmConjunction e2)
in (infix2 _165_678 _165_677 _165_676))))
end
| _67_818 -> begin
(p_tmConjunction e)
end))
and p_tmConjunction : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("/\\", (e1)::(e2)::[]) -> begin
(let _165_682 = (str "/\\")
in (let _165_681 = (p_tmConjunction e1)
in (let _165_680 = (p_tmTuple e2)
in (infix2 _165_682 _165_681 _165_680))))
end
| _67_827 -> begin
(p_tmTuple e)
end))
and p_tmTuple : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (lid, args) when (is_tuple_constructor lid) -> begin
(FStar_Pprint.separate_map FStar_Pprint.comma (fun _67_836 -> (match (_67_836) with
| (e, _67_835) -> begin
(p_tmEq e)
end)) args)
end
| _67_838 -> begin
(p_tmEq e)
end))
and paren_if : Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun curr mine doc -> if (mine <= curr) then begin
doc
end else begin
(let _165_689 = (let _165_688 = (FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_688))
in (FStar_Pprint.group _165_689))
end)
and p_tmEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n = (max_level (FStar_List.append ((colon_equals)::(pipe_right)::[]) operatorInfix0ad12))
in (p_tmEq' n e)))
and p_tmEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (((is_operatorInfix0ad12 op) || (op = "=")) || (op = "|>")) -> begin
(

let _67_855 = (levels op)
in (match (_67_855) with
| (left, mine, right) -> begin
(let _165_696 = (let _165_695 = (str op)
in (let _165_694 = (p_tmEq' left e1)
in (let _165_693 = (p_tmEq' right e2)
in (infix2 _165_695 _165_694 _165_693))))
in (paren_if curr mine _165_696))
end))
end
| FStar_Parser_AST.Op (":=", (e1)::(e2)::[]) -> begin
(let _165_701 = (let _165_700 = (p_tmEq e1)
in (let _165_699 = (let _165_698 = (let _165_697 = (p_tmEq e2)
in (op_Hat_Slash_Plus_Hat FStar_Pprint.equals _165_697))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_698))
in (FStar_Pprint.op_Hat_Hat _165_700 _165_699)))
in (FStar_Pprint.group _165_701))
end
| _67_863 -> begin
(p_tmNoEq e)
end))
and p_tmNoEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n = (max_level ((colon_colon)::(amp)::(opinfix3)::(opinfix4)::[]))
in (p_tmNoEq' n e)))
and p_tmNoEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (lid, ((e1, _67_875))::((e2, _67_871))::[]) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.cons_lid) -> begin
(

let op = "::"
in (

let _67_884 = (levels op)
in (match (_67_884) with
| (left, mine, right) -> begin
(let _165_708 = (let _165_707 = (str op)
in (let _165_706 = (p_tmNoEq' left e1)
in (let _165_705 = (p_tmNoEq' right e2)
in (infix2 _165_707 _165_706 _165_705))))
in (paren_if curr mine _165_708))
end)))
end
| FStar_Parser_AST.Sum (binders, res) -> begin
(

let op = "&"
in (

let _67_893 = (levels op)
in (match (_67_893) with
| (left, mine, right) -> begin
(

let p_dsumfst = (fun b -> (let _165_714 = (p_binder b)
in (let _165_713 = (let _165_712 = (let _165_711 = (str "&")
in (FStar_Pprint.op_Hat_Hat _165_711 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_712))
in (FStar_Pprint.op_Hat_Hat _165_714 _165_713))))
in (let _165_717 = (let _165_716 = (FStar_Pprint.concat_map p_dsumfst binders)
in (let _165_715 = (p_tmNoEq' right res)
in (FStar_Pprint.op_Hat_Hat _165_716 _165_715)))
in (paren_if curr mine _165_717)))
end)))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (is_operatorInfix34 op) -> begin
(

let _67_905 = (levels op)
in (match (_67_905) with
| (left, mine, right) -> begin
(let _165_721 = (let _165_720 = (str op)
in (let _165_719 = (p_tmNoEq' left e1)
in (let _165_718 = (p_tmNoEq' right e2)
in (infix2 _165_720 _165_719 _165_718))))
in (paren_if curr mine _165_721))
end))
end
| FStar_Parser_AST.Op ("-", (e)::[]) -> begin
(

let _67_914 = (levels "-")
in (match (_67_914) with
| (left, mine, right) -> begin
(let _165_722 = (p_tmNoEq' mine e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus _165_722))
end))
end
| FStar_Parser_AST.NamedTyp (lid, e) -> begin
(let _165_726 = (let _165_725 = (p_lidentOrUnderscore lid)
in (let _165_724 = (let _165_723 = (p_appTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon _165_723))
in (FStar_Pprint.op_Hat_Slash_Hat _165_725 _165_724)))
in (FStar_Pprint.group _165_726))
end
| FStar_Parser_AST.Refine (b, phi) -> begin
(p_refinedBinder b phi)
end
| FStar_Parser_AST.Record (with_opt, record_fields) -> begin
(let _165_729 = (let _165_728 = (default_or_map FStar_Pprint.empty p_with_clause with_opt)
in (let _165_727 = (FStar_Pprint.separate_map FStar_Pprint.semi p_simpleDef record_fields)
in (FStar_Pprint.op_Hat_Hat _165_728 _165_727)))
in (braces_with_nesting _165_729))
end
| FStar_Parser_AST.Op ("~", (e)::[]) -> begin
(let _165_732 = (let _165_731 = (str "~")
in (let _165_730 = (p_atomicTerm e)
in (FStar_Pprint.op_Hat_Hat _165_731 _165_730)))
in (FStar_Pprint.group _165_732))
end
| _67_933 -> begin
(p_appTerm e)
end))
and p_with_clause : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (let _165_737 = (p_appTerm e)
in (let _165_736 = (let _165_735 = (let _165_734 = (str "with")
in (FStar_Pprint.op_Hat_Hat _165_734 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_735))
in (FStar_Pprint.op_Hat_Hat _165_737 _165_736))))
and p_refinedBinder : FStar_Parser_AST.binder  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun b phi -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (lid, t) -> begin
(let _165_747 = (let _165_746 = (p_lident lid)
in (let _165_745 = (let _165_744 = (let _165_743 = (p_typ t)
in (let _165_742 = (let _165_741 = (let _165_740 = (p_term phi)
in (braces_with_nesting _165_740))
in (FStar_Pprint.op_Hat_Hat _165_741 FStar_Pprint.rparen))
in (FStar_Pprint.op_Hat_Hat _165_743 _165_742)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_744))
in (FStar_Pprint.op_Hat_Hat _165_746 _165_745)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_747))
end
| FStar_Parser_AST.TAnnotated (_67_942) -> begin
(FStar_All.failwith "Is this still used ?")
end
| (FStar_Parser_AST.Variable (_)) | (FStar_Parser_AST.TVariable (_)) | (FStar_Parser_AST.NoName (_)) -> begin
(let _165_749 = (let _165_748 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" _165_748))
in (FStar_All.failwith _165_749))
end))
and p_simpleDef : (FStar_Ident.lid * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun _67_955 -> (match (_67_955) with
| (lid, e) -> begin
(let _165_754 = (let _165_753 = (p_qlident lid)
in (let _165_752 = (let _165_751 = (p_simpleTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals _165_751))
in (FStar_Pprint.op_Hat_Slash_Hat _165_753 _165_752)))
in (FStar_Pprint.group _165_754))
end))
and p_appTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App (_67_958) when (is_general_application e) -> begin
(

let _67_962 = (head_and_args e)
in (match (_67_962) with
| (head, args) -> begin
(let _165_757 = (p_indexingTerm head)
in (let _165_756 = (FStar_Pprint.separate_map FStar_Pprint.space p_argTerm args)
in (op_Hat_Slash_Plus_Hat _165_757 _165_756)))
end))
end
| FStar_Parser_AST.Construct (lid, args) when (not ((is_dtuple_constructor lid))) -> begin
(let _165_759 = (p_quident lid)
in (let _165_758 = (FStar_Pprint.separate_map FStar_Pprint.space p_argTerm args)
in (op_Hat_Slash_Plus_Hat _165_759 _165_758)))
end
| _67_968 -> begin
(p_indexingTerm e)
end))
and p_argTerm : (FStar_Parser_AST.term * FStar_Parser_AST.imp)  ->  FStar_Pprint.document = (fun arg_imp -> (match (arg_imp) with
| ({FStar_Parser_AST.tm = FStar_Parser_AST.Uvar (_67_975); FStar_Parser_AST.range = _67_973; FStar_Parser_AST.level = _67_971}, FStar_Parser_AST.UnivApp) -> begin
(p_univar (Prims.fst arg_imp))
end
| (u, FStar_Parser_AST.UnivApp) -> begin
(p_universe u)
end
| (e, FStar_Parser_AST.FsTypApp) -> begin
(let _165_761 = (p_indexingTerm e)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.langle _165_761 FStar_Pprint.rangle))
end
| (e, FStar_Parser_AST.Hash) -> begin
(let _165_763 = (str "#")
in (let _165_762 = (p_indexingTerm e)
in (FStar_Pprint.op_Hat_Hat _165_763 _165_762)))
end
| (e, FStar_Parser_AST.Nothing) -> begin
(p_indexingTerm e)
end))
and p_indexingTerm_aux : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun exit e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op (".()", (e1)::(e2)::[]) -> begin
(let _165_773 = (let _165_772 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (let _165_771 = (let _165_770 = (let _165_769 = (p_term e2)
in (parens_with_nesting _165_769))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_770))
in (FStar_Pprint.op_Hat_Hat _165_772 _165_771)))
in (FStar_Pprint.group _165_773))
end
| FStar_Parser_AST.Op (".[]", (e1)::(e2)::[]) -> begin
(let _165_778 = (let _165_777 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (let _165_776 = (let _165_775 = (let _165_774 = (p_term e2)
in (brackets_with_nesting _165_774))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_775))
in (FStar_Pprint.op_Hat_Hat _165_777 _165_776)))
in (FStar_Pprint.group _165_778))
end
| _67_1007 -> begin
(exit e)
end))
and p_indexingTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_indexingTerm_aux p_atomicTerm e))
and p_atomicTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.LetOpen (lid, e) -> begin
(let _165_784 = (p_quident lid)
in (let _165_783 = (let _165_782 = (let _165_781 = (p_term e)
in (parens_with_nesting _165_781))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_782))
in (FStar_Pprint.op_Hat_Hat _165_784 _165_783)))
end
| FStar_Parser_AST.Name (lid) -> begin
(p_quident lid)
end
| FStar_Parser_AST.Op (op, (e)::[]) -> begin
(let _165_786 = (str op)
in (let _165_785 = (p_atomicTerm e)
in (FStar_Pprint.op_Hat_Hat _165_786 _165_785)))
end
| _67_1022 -> begin
(p_atomicTermNotQUident e)
end))
and p_atomicTermNotQUident : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Wild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.Var (lid) when ((FStar_Ident.text_of_lid lid) = "assert") -> begin
(str "assert")
end
| FStar_Parser_AST.Tvar (tv) -> begin
(p_tvar tv)
end
| FStar_Parser_AST.Const (c) -> begin
(p_constant c)
end
| FStar_Parser_AST.Name (lid) when ((FStar_Ident.text_of_lid lid) = "True") -> begin
(str "True")
end
| FStar_Parser_AST.Name (lid) when ((FStar_Ident.text_of_lid lid) = "False") -> begin
(str "False")
end
| FStar_Parser_AST.Op (op, (e)::[]) -> begin
(let _165_789 = (str op)
in (let _165_788 = (p_atomicTermNotQUident e)
in (FStar_Pprint.op_Hat_Hat _165_789 _165_788)))
end
| FStar_Parser_AST.Op (op, []) -> begin
(let _165_793 = (let _165_792 = (let _165_791 = (str op)
in (let _165_790 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat _165_791 _165_790)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_792))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_793))
end
| FStar_Parser_AST.Construct (lid, args) when (is_dtuple_constructor lid) -> begin
(let _165_797 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (let _165_796 = (let _165_794 = (FStar_List.map Prims.fst args)
in (FStar_Pprint.separate_map FStar_Pprint.comma p_tmEq _165_794))
in (let _165_795 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_797 _165_796 _165_795))))
end
| FStar_Parser_AST.Project (e, lid) -> begin
(let _165_801 = (let _165_800 = (p_atomicTermNotQUident e)
in (let _165_799 = (let _165_798 = (p_qlident lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_798))
in (FStar_Pprint.op_Hat_Slash_Hat _165_800 _165_799)))
in (FStar_Pprint.group _165_801))
end
| _67_1053 -> begin
(p_projectionLHS e)
end))
and p_projectionLHS : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (lid) -> begin
(p_qlident lid)
end
| FStar_Parser_AST.Projector (constr_lid, field_lid) -> begin
(let _165_806 = (p_quident constr_lid)
in (let _165_805 = (let _165_804 = (let _165_803 = (p_lident field_lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_803))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark _165_804))
in (FStar_Pprint.op_Hat_Hat _165_806 _165_805)))
end
| FStar_Parser_AST.Discrim (constr_lid) -> begin
(let _165_807 = (p_quident constr_lid)
in (FStar_Pprint.op_Hat_Hat _165_807 FStar_Pprint.qmark))
end
| FStar_Parser_AST.Paren (e) -> begin
(let _165_808 = (p_term e)
in (parens_with_nesting _165_808))
end
| _67_1066 when (is_array e) -> begin
(

let es = (extract_from_list e)
in (let _165_811 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar)
in (let _165_810 = (FStar_Pprint.separate_map FStar_Pprint.semi p_noSeqTerm es)
in (let _165_809 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_811 _165_810 _165_809)))))
end
| _67_1069 when (is_list e) -> begin
(let _165_813 = (let _165_812 = (extract_from_list e)
in (FStar_Pprint.separate_map FStar_Pprint.semi p_noSeqTerm _165_812))
in (brackets_with_nesting _165_813))
end
| _67_1071 when (is_lex_list e) -> begin
(let _165_816 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket)
in (let _165_815 = (let _165_814 = (extract_from_list e)
in (FStar_Pprint.separate_map FStar_Pprint.semi p_noSeqTerm _165_814))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_816 _165_815 FStar_Pprint.rbracket)))
end
| _67_1073 when (is_ref_set e) -> begin
(

let es = (extract_from_ref_set e)
in (let _165_818 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace)
in (let _165_817 = (FStar_Pprint.separate_map FStar_Pprint.comma p_appTerm es)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_818 _165_817 FStar_Pprint.rbrace))))
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Op (_)) | (FStar_Parser_AST.Tvar (_)) | (FStar_Parser_AST.Uvar (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) | (FStar_Parser_AST.Construct (_)) | (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.App (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.LetOpen (_)) | (FStar_Parser_AST.Seq (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Ascribed (_)) | (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Project (_)) | (FStar_Parser_AST.Product (_)) | (FStar_Parser_AST.Sum (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Refine (_)) | (FStar_Parser_AST.NamedTyp (_)) | (FStar_Parser_AST.Requires (_)) | (FStar_Parser_AST.Ensures (_)) | (FStar_Parser_AST.Assign (_)) | (FStar_Parser_AST.Attributes (_)) -> begin
(let _165_819 = (p_term e)
in (parens_with_nesting _165_819))
end
| FStar_Parser_AST.Labeled (_67_1161) -> begin
(FStar_All.failwith "Not valid in universe")
end))
and p_constant : FStar_Const.sconst  ->  FStar_Pprint.document = (fun _67_17 -> (match (_67_17) with
| FStar_Const.Const_effect -> begin
(str "Effect")
end
| FStar_Const.Const_unit -> begin
(str "()")
end
| FStar_Const.Const_bool (b) -> begin
(FStar_Pprint.doc_of_bool b)
end
| FStar_Const.Const_float (x) -> begin
(str (FStar_Util.string_of_float x))
end
| FStar_Const.Const_char (x) -> begin
(let _165_821 = (FStar_Pprint.doc_of_char x)
in (FStar_Pprint.squotes _165_821))
end
| FStar_Const.Const_string (bytes, _67_1174) -> begin
(let _165_822 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes _165_822))
end
| FStar_Const.Const_bytearray (bytes, _67_1179) -> begin
(let _165_825 = (let _165_823 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes _165_823))
in (let _165_824 = (str "B")
in (FStar_Pprint.op_Hat_Hat _165_825 _165_824)))
end
| FStar_Const.Const_int (repr, sign_width_opt) -> begin
(

let signedness = (fun _67_15 -> (match (_67_15) with
| FStar_Const.Unsigned -> begin
(str "u")
end
| FStar_Const.Signed -> begin
FStar_Pprint.empty
end))
in (

let width = (fun _67_16 -> (match (_67_16) with
| FStar_Const.Int8 -> begin
(str "y")
end
| FStar_Const.Int16 -> begin
(str "s")
end
| FStar_Const.Int32 -> begin
(str "l")
end
| FStar_Const.Int64 -> begin
(str "L")
end))
in (

let ending = (default_or_map FStar_Pprint.empty (fun _67_1198 -> (match (_67_1198) with
| (s, w) -> begin
(let _165_832 = (signedness s)
in (let _165_831 = (width w)
in (FStar_Pprint.op_Hat_Hat _165_832 _165_831)))
end)) sign_width_opt)
in (let _165_833 = (str repr)
in (FStar_Pprint.op_Hat_Hat _165_833 ending)))))
end
| FStar_Const.Const_range (r) -> begin
(let _165_834 = (FStar_Range.string_of_range r)
in (str _165_834))
end
| FStar_Const.Const_reify -> begin
(str "reify")
end
| FStar_Const.Const_reflect (lid) -> begin
(let _165_838 = (p_quident lid)
in (let _165_837 = (let _165_836 = (let _165_835 = (str "reflect")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_835))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark _165_836))
in (FStar_Pprint.op_Hat_Hat _165_838 _165_837)))
end))
and p_universe : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (let _165_841 = (str "u#")
in (let _165_840 = (p_atomicUniverse u)
in (FStar_Pprint.op_Hat_Hat _165_841 _165_840))))
and p_universeFrom : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match (u.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("+", (u1)::(u2)::[]) -> begin
(let _165_846 = (let _165_845 = (p_universeFrom u1)
in (let _165_844 = (let _165_843 = (p_universeFrom u2)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus _165_843))
in (FStar_Pprint.op_Hat_Slash_Hat _165_845 _165_844)))
in (FStar_Pprint.group _165_846))
end
| FStar_Parser_AST.App (_67_1214) -> begin
(

let _67_1218 = (head_and_args u)
in (match (_67_1218) with
| (head, args) -> begin
(match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (maybe_max_lid) when (FStar_Ident.lid_equals maybe_max_lid FStar_Syntax_Const.max_lid) -> begin
(let _165_850 = (let _165_849 = (p_qlident FStar_Syntax_Const.max_lid)
in (let _165_848 = (FStar_Pprint.separate_map FStar_Pprint.space (fun _67_1224 -> (match (_67_1224) with
| (u, _67_1223) -> begin
(p_atomicUniverse u)
end)) args)
in (op_Hat_Slash_Plus_Hat _165_849 _165_848)))
in (FStar_Pprint.group _165_850))
end
| _67_1226 -> begin
(let _165_852 = (let _165_851 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" _165_851))
in (FStar_All.failwith _165_852))
end)
end))
end
| _67_1228 -> begin
(p_atomicUniverse u)
end))
and p_atomicUniverse : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match (u.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Wild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (r, sw)) -> begin
(p_constant (FStar_Const.Const_int (((r), (sw)))))
end
| FStar_Parser_AST.Uvar (_67_1237) -> begin
(p_univar u)
end
| FStar_Parser_AST.Paren (u) -> begin
(let _165_854 = (p_universeFrom u)
in (parens_with_nesting _165_854))
end
| (FStar_Parser_AST.Op ("+", (_)::(_)::[])) | (FStar_Parser_AST.App (_)) -> begin
(let _165_855 = (p_universeFrom u)
in (parens_with_nesting _165_855))
end
| _67_1253 -> begin
(let _165_857 = (let _165_856 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" _165_856))
in (FStar_All.failwith _165_857))
end))
and p_univar : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match (u.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Uvar (id) -> begin
(str (FStar_Ident.text_of_id id))
end
| _67_1258 -> begin
(let _165_860 = (let _165_859 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Not a universe variable %s" _165_859))
in (FStar_All.failwith _165_860))
end))


let term_to_document : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_term e))


let decl_to_document : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun e -> (p_decl e))


let modul_to_document : FStar_Parser_AST.modul  ->  FStar_Pprint.document = (fun m -> (match (m) with
| (FStar_Parser_AST.Module (_, decls)) | (FStar_Parser_AST.Interface (_, decls, _)) -> begin
(let _165_867 = (FStar_All.pipe_right decls (FStar_List.map decl_to_document))
in (FStar_All.pipe_right _165_867 (FStar_Pprint.separate FStar_Pprint.hardline)))
end))




