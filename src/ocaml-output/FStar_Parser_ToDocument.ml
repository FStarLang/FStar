
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
(let _165_273 = (let _165_272 = (let _165_271 = (let _165_270 = (let _165_269 = (str doc)
in (let _165_268 = (let _165_267 = (let _165_266 = (FStar_Pprint.concat_map (fun _67_305 -> (match (_67_305) with
| (kwd, arg) -> begin
(let _165_262 = (str "@")
in (let _165_261 = (let _165_260 = (str kwd)
in (let _165_259 = (let _165_258 = (let _165_257 = (str arg)
in (FStar_Pprint.op_Hat_Hat _165_257 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_258))
in (FStar_Pprint.op_Hat_Hat _165_260 _165_259)))
in (FStar_Pprint.op_Hat_Hat _165_262 _165_261)))
end)) kwd_args)
in (let _165_265 = (let _165_264 = (let _165_263 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _165_263))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _165_264))
in (FStar_Pprint.op_Hat_Hat _165_266 _165_265)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline _165_267))
in (FStar_Pprint.op_Hat_Hat _165_269 _165_268)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _165_270))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _165_271))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_272))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline _165_273))
end))
and p_decl2 : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Open (uid) -> begin
(let _165_277 = (let _165_276 = (str "open")
in (let _165_275 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat _165_276 _165_275)))
in (FStar_Pprint.group _165_277))
end
| FStar_Parser_AST.ModuleAbbrev (uid1, uid2) -> begin
(let _165_284 = (let _165_282 = (str "module")
in (let _165_281 = (let _165_280 = (let _165_279 = (p_uident uid1)
in (let _165_278 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _165_279 _165_278)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_280))
in (FStar_Pprint.op_Hat_Hat _165_282 _165_281)))
in (let _165_283 = (p_quident uid2)
in (op_Hat_Slash_Plus_Hat _165_284 _165_283)))
end
| FStar_Parser_AST.TopLevelModule (uid) -> begin
(let _165_288 = (let _165_287 = (str "module")
in (let _165_286 = (let _165_285 = (p_quident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_285))
in (FStar_Pprint.op_Hat_Hat _165_287 _165_286)))
in (FStar_Pprint.group _165_288))
end
| FStar_Parser_AST.KindAbbrev (_67_316) -> begin
(FStar_All.failwith "Deprecated, please stop throwing your old stuff at me !")
end
| FStar_Parser_AST.Tycon (qs, ((FStar_Parser_AST.TyconAbbrev (uid, tpars, None, t), None))::[]) when (FStar_List.contains FStar_Parser_AST.Effect qs) -> begin
(

let qs = (FStar_List.filter (fun q -> (q <> FStar_Parser_AST.Effect)) qs)
in (

let effect_prefix_doc = (let _165_294 = (p_qualifiers qs)
in (let _165_293 = (let _165_292 = (str "effect")
in (let _165_291 = (let _165_290 = (p_uident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_290))
in (FStar_Pprint.op_Hat_Hat _165_292 _165_291)))
in (FStar_Pprint.op_Hat_Hat _165_294 _165_293)))
in (let _165_297 = (let _165_295 = (p_typars tpars)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") effect_prefix_doc _165_295 FStar_Pprint.equals))
in (let _165_296 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _165_297 _165_296)))))
end
| FStar_Parser_AST.Tycon (qs, tcdefs) -> begin
(

let type_doc = (let _165_299 = (p_qualifiers qs)
in (let _165_298 = (str "type")
in (FStar_Pprint.op_Hat_Hat _165_299 _165_298)))
in (let _165_300 = (str "and")
in (precede_break_separate_map type_doc _165_300 p_fsdocTypeDeclPairs tcdefs)))
end
| FStar_Parser_AST.TopLevelLet (qs, q, lbs) -> begin
(

let let_doc = (let _165_304 = (p_qualifiers qs)
in (let _165_303 = (let _165_302 = (str "let")
in (let _165_301 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat _165_302 _165_301)))
in (FStar_Pprint.op_Hat_Hat _165_304 _165_303)))
in (let _165_305 = (str "and")
in (precede_break_separate_map let_doc _165_305 p_letbinding lbs)))
end
| FStar_Parser_AST.Val (qs, lid, t) -> begin
(let _165_314 = (let _165_312 = (p_qualifiers qs)
in (let _165_311 = (let _165_310 = (str "val")
in (let _165_309 = (let _165_308 = (let _165_307 = (p_lident lid)
in (let _165_306 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat _165_307 _165_306)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_308))
in (FStar_Pprint.op_Hat_Hat _165_310 _165_309)))
in (FStar_Pprint.op_Hat_Hat _165_312 _165_311)))
in (let _165_313 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _165_314 _165_313)))
end
| FStar_Parser_AST.Assume (qs, id, t) -> begin
(

let decl_keyword = if (let _165_315 = (FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_All.pipe_right _165_315 FStar_Util.is_upper)) then begin
FStar_Pprint.empty
end else begin
(let _165_316 = (str "val")
in (FStar_Pprint.op_Hat_Hat _165_316 FStar_Pprint.space))
end
in (let _165_323 = (let _165_321 = (p_qualifiers qs)
in (let _165_320 = (let _165_319 = (let _165_318 = (p_ident id)
in (let _165_317 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat _165_318 _165_317)))
in (FStar_Pprint.op_Hat_Hat decl_keyword _165_319))
in (FStar_Pprint.op_Hat_Hat _165_321 _165_320)))
in (let _165_322 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _165_323 _165_322))))
end
| FStar_Parser_AST.Exception (uid, t_opt) -> begin
(let _165_331 = (str "exception")
in (let _165_330 = (let _165_329 = (let _165_328 = (p_uident uid)
in (let _165_327 = (FStar_Pprint.optional (fun t -> (let _165_326 = (str "of")
in (let _165_325 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _165_326 _165_325)))) t_opt)
in (FStar_Pprint.op_Hat_Hat _165_328 _165_327)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_329))
in (FStar_Pprint.op_Hat_Hat _165_331 _165_330)))
end
| FStar_Parser_AST.NewEffect (qs, ne) -> begin
(let _165_336 = (p_qualifiers qs)
in (let _165_335 = (let _165_334 = (str "new_effect")
in (let _165_333 = (let _165_332 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_332))
in (FStar_Pprint.op_Hat_Hat _165_334 _165_333)))
in (FStar_Pprint.op_Hat_Hat _165_336 _165_335)))
end
| FStar_Parser_AST.SubEffect (se) -> begin
(let _165_339 = (str "sub_effect")
in (let _165_338 = (let _165_337 = (p_subEffect se)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_337))
in (FStar_Pprint.op_Hat_Hat _165_339 _165_338)))
end
| FStar_Parser_AST.NewEffectForFree (qs, ne) -> begin
(let _165_344 = (p_qualifiers qs)
in (let _165_343 = (let _165_342 = (str "new_effect_for_free")
in (let _165_341 = (let _165_340 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_340))
in (FStar_Pprint.op_Hat_Hat _165_342 _165_341)))
in (FStar_Pprint.op_Hat_Hat _165_344 _165_343)))
end
| FStar_Parser_AST.Pragma (p) -> begin
(p_pragma p)
end
| FStar_Parser_AST.Fsdoc (doc) -> begin
(let _165_345 = (p_fsdoc doc)
in (FStar_Pprint.op_Hat_Hat _165_345 FStar_Pprint.hardline))
end
| FStar_Parser_AST.Main (_67_375) -> begin
(FStar_All.failwith "*Main declaration* : Is that really still in use ??")
end))
and p_pragma : FStar_Parser_AST.pragma  ->  FStar_Pprint.document = (fun _67_6 -> (match (_67_6) with
| FStar_Parser_AST.SetOptions (s) -> begin
(let _165_350 = (str "#set-options")
in (let _165_349 = (let _165_348 = (let _165_347 = (str s)
in (FStar_Pprint.dquotes _165_347))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_348))
in (FStar_Pprint.op_Hat_Hat _165_350 _165_349)))
end
| FStar_Parser_AST.ResetOptions (s_opt) -> begin
(let _165_355 = (str "#reset-options")
in (let _165_354 = (FStar_Pprint.optional (fun s -> (let _165_353 = (let _165_352 = (str s)
in (FStar_Pprint.dquotes _165_352))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_353))) s_opt)
in (FStar_Pprint.op_Hat_Hat _165_355 _165_354)))
end))
and p_typars : FStar_Parser_AST.binder Prims.list  ->  FStar_Pprint.document = (fun bs -> (p_binders bs))
and p_fsdocTypeDeclPairs : (FStar_Parser_AST.tycon * FStar_Parser_AST.fsdoc Prims.option)  ->  FStar_Pprint.document = (fun _67_386 -> (match (_67_386) with
| (typedecl, fsdoc_opt) -> begin
(let _165_359 = (FStar_Pprint.optional p_fsdoc fsdoc_opt)
in (let _165_358 = (p_typeDecl typedecl)
in (FStar_Pprint.op_Hat_Hat _165_359 _165_358)))
end))
and p_typeDecl : FStar_Parser_AST.tycon  ->  FStar_Pprint.document = (fun _67_7 -> (match (_67_7) with
| FStar_Parser_AST.TyconAbstract (lid, bs, typ_opt) -> begin
(p_typeDeclPrefix lid bs typ_opt)
end
| FStar_Parser_AST.TyconAbbrev (lid, bs, typ_opt, t) -> begin
(let _165_362 = (p_typeDeclPrefix lid bs typ_opt)
in (let _165_361 = (p_typ t)
in (infix2 FStar_Pprint.equals _165_362 _165_361)))
end
| FStar_Parser_AST.TyconRecord (lid, bs, typ_opt, record_field_decls) -> begin
(let _165_366 = (p_typeDeclPrefix lid bs typ_opt)
in (let _165_365 = (let _165_364 = (let _165_363 = (separate_break_map FStar_Pprint.semi p_recordFieldDecl record_field_decls)
in (braces_with_nesting _165_363))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.equals _165_364))
in (FStar_Pprint.op_Hat_Slash_Hat _165_366 _165_365)))
end
| FStar_Parser_AST.TyconVariant (lid, bs, typ_opt, ct_decls) -> begin
(let _165_373 = (p_typeDeclPrefix lid bs typ_opt)
in (let _165_372 = (let _165_371 = (FStar_Pprint.separate_map break1 (fun decl -> (let _165_370 = (let _165_369 = (let _165_368 = (p_constructorDecl decl)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_368))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar _165_369))
in (FStar_Pprint.group _165_370))) ct_decls)
in (FStar_Pprint.group _165_371))
in (infix2 FStar_Pprint.equals _165_373 _165_372)))
end))
and p_typeDeclPrefix : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.knd Prims.option  ->  FStar_Pprint.document = (fun lid bs typ_opt -> (let _165_383 = (p_ident lid)
in (let _165_382 = (let _165_381 = (p_typars bs)
in (let _165_380 = (FStar_Pprint.optional (fun t -> (let _165_379 = (let _165_378 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_378))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_379))) typ_opt)
in (FStar_Pprint.op_Hat_Hat _165_381 _165_380)))
in (op_Hat_Slash_Plus_Hat _165_383 _165_382))))
and p_recordFieldDecl : (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc Prims.option)  ->  FStar_Pprint.document = (fun _67_419 -> (match (_67_419) with
| (lid, t, doc_opt) -> begin
(let _165_389 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (let _165_388 = (let _165_387 = (p_lident lid)
in (let _165_386 = (let _165_385 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_385))
in (FStar_Pprint.op_Hat_Hat _165_387 _165_386)))
in (FStar_Pprint.op_Hat_Hat _165_389 _165_388)))
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
in (let _165_396 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (let _165_395 = (default_or_map uid_doc (fun t -> (let _165_394 = (let _165_392 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep)
in (FStar_Pprint.op_Hat_Hat uid_doc _165_392))
in (let _165_393 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _165_394 _165_393)))) t_opt)
in (FStar_Pprint.op_Hat_Hat _165_396 _165_395)))))
end))
and p_letbinding : (FStar_Parser_AST.pattern * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun _67_430 -> (match (_67_430) with
| (pat, e) -> begin
(

let pat_doc = (

let _67_439 = (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, t) -> begin
(let _165_401 = (let _165_400 = (let _165_399 = (let _165_398 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat break1 _165_398))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_399))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_400))
in ((pat), (_165_401)))
end
| _67_436 -> begin
((pat), (FStar_Pprint.empty))
end)
in (match (_67_439) with
| (pat, ascr_doc) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _67_444); FStar_Parser_AST.prange = _67_441}, pats) -> begin
(let _165_404 = (p_lident x)
in (let _165_403 = (let _165_402 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Hat _165_402 ascr_doc))
in (prefix2 _165_404 _165_403)))
end
| _67_452 -> begin
(let _165_405 = (p_tuplePattern pat)
in (FStar_Pprint.op_Hat_Hat _165_405 ascr_doc))
end)
end))
in (let _165_408 = (let _165_407 = (let _165_406 = (p_term e)
in (prefix2 FStar_Pprint.equals _165_406))
in (FStar_Pprint.op_Hat_Slash_Hat pat_doc _165_407))
in (FStar_Pprint.group _165_408)))
end))
and p_newEffect : FStar_Parser_AST.effect_decl  ->  FStar_Pprint.document = (fun _67_8 -> (match (_67_8) with
| FStar_Parser_AST.RedefineEffect (lid, bs, t) -> begin
(p_effectRedefinition lid bs t)
end
| FStar_Parser_AST.DefineEffect (lid, bs, t, eff_decls, action_decls) -> begin
(p_effectDefinition lid bs t eff_decls action_decls)
end))
and p_effectRedefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun uid bs t -> (let _165_416 = (p_uident uid)
in (let _165_415 = (p_binders bs)
in (let _165_414 = (let _165_413 = (p_simpleTerm t)
in (prefix2 FStar_Pprint.equals _165_413))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_416 _165_415 _165_414)))))
and p_effectDefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun uid bs t eff_decls action_decls -> (let _165_434 = (let _165_433 = (let _165_427 = (let _165_426 = (let _165_423 = (p_uident uid)
in (let _165_422 = (p_binders bs)
in (prefix2 _165_423 _165_422)))
in (let _165_425 = (let _165_424 = (p_typ t)
in (prefix2 FStar_Pprint.colon _165_424))
in (FStar_Pprint.op_Hat_Hat _165_426 _165_425)))
in (FStar_Pprint.group _165_427))
in (let _165_432 = (let _165_431 = (let _165_429 = (str "with")
in (let _165_428 = (separate_break_map FStar_Pprint.semi p_effectDecl eff_decls)
in (prefix2 _165_429 _165_428)))
in (let _165_430 = (p_actionDecls action_decls)
in (FStar_Pprint.op_Hat_Hat _165_431 _165_430)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_433 _165_432)))
in (braces_with_nesting _165_434)))
and p_actionDecls : FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun _67_9 -> (match (_67_9) with
| [] -> begin
FStar_Pprint.empty
end
| l -> begin
(let _165_438 = (let _165_437 = (str "and actions")
in (let _165_436 = (separate_break_map FStar_Pprint.semi p_effectDecl l)
in (prefix2 _165_437 _165_436)))
in (FStar_Pprint.op_Hat_Hat break1 _165_438))
end))
and p_effectDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon ([], ((FStar_Parser_AST.TyconAbbrev (lid, [], None, e), None))::[]) -> begin
(let _165_443 = (let _165_441 = (p_lident lid)
in (let _165_440 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _165_441 _165_440)))
in (let _165_442 = (p_simpleTerm e)
in (prefix2 _165_443 _165_442)))
end
| _67_492 -> begin
(let _165_445 = (let _165_444 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "Not a declaration of an effect member... or at least I hope so : %s" _165_444))
in (FStar_All.failwith _165_445))
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
(let _165_452 = (let _165_450 = (str kwd)
in (let _165_449 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _165_450 _165_449)))
in (let _165_451 = (p_simpleTerm t)
in (prefix2 _165_452 _165_451)))
end))
in (separate_break_map FStar_Pprint.semi p_lift lifts)))
in (let _165_460 = (let _165_457 = (let _165_455 = (p_quident lift.FStar_Parser_AST.msource)
in (let _165_454 = (let _165_453 = (str "~>")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_453))
in (FStar_Pprint.op_Hat_Hat _165_455 _165_454)))
in (let _165_456 = (p_quident lift.FStar_Parser_AST.mdest)
in (prefix2 _165_457 _165_456)))
in (let _165_459 = (let _165_458 = (braces_with_nesting lift_op_doc)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_458))
in (FStar_Pprint.op_Hat_Hat _165_460 _165_459)))))
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
and p_qualifiers : FStar_Parser_AST.qualifier Prims.list  ->  FStar_Pprint.document = (fun qs -> (let _165_464 = (let _165_463 = (FStar_Pprint.separate_map break1 p_qualifier qs)
in (FStar_Pprint.op_Hat_Hat _165_463 (if (qs = []) then begin
FStar_Pprint.empty
end else begin
FStar_Pprint.space
end)))
in (FStar_Pprint.group _165_464)))
and p_letqualifier : FStar_Parser_AST.let_qualifier  ->  FStar_Pprint.document = (fun _67_11 -> (match (_67_11) with
| FStar_Parser_AST.Rec -> begin
(let _165_466 = (str "rec")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_466))
end
| FStar_Parser_AST.Mutable -> begin
(let _165_467 = (str "mutable")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_467))
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
(let _165_472 = (let _165_471 = (let _165_470 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space)
in (FStar_Pprint.op_Hat_Hat break1 _165_470))
in (FStar_Pprint.separate_map _165_471 p_tuplePattern pats))
in (FStar_Pprint.group _165_472))
end
| _67_540 -> begin
(p_tuplePattern p)
end))
and p_tuplePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTuple (pats, false) -> begin
(let _165_474 = (separate_break_map FStar_Pprint.comma p_constructorPattern pats)
in (FStar_Pprint.group _165_474))
end
| _67_547 -> begin
(p_constructorPattern p)
end))
and p_constructorPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (maybe_cons_lid); FStar_Parser_AST.prange = _67_550}, (hd)::(tl)::[]) when (FStar_Ident.lid_equals maybe_cons_lid FStar_Syntax_Const.cons_lid) -> begin
(let _165_478 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon)
in (let _165_477 = (p_constructorPattern hd)
in (let _165_476 = (p_constructorPattern tl)
in (infix2 _165_478 _165_477 _165_476))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (uid); FStar_Parser_AST.prange = _67_560}, pats) -> begin
(let _165_480 = (p_quident uid)
in (let _165_479 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (prefix2 _165_480 _165_479)))
end
| _67_568 -> begin
(p_atomicPattern p)
end))
and p_atomicPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, t) -> begin
(let _165_484 = (let _165_483 = (p_tuplePattern pat)
in (let _165_482 = (p_typ t)
in (infix2 FStar_Pprint.colon _165_483 _165_482)))
in (parens_with_nesting _165_484))
end
| FStar_Parser_AST.PatList (pats) -> begin
(let _165_485 = (separate_break_map FStar_Pprint.semi p_tuplePattern pats)
in (brackets_with_nesting _165_485))
end
| FStar_Parser_AST.PatRecord (pats) -> begin
(

let p_recordFieldPat = (fun _67_581 -> (match (_67_581) with
| (lid, pat) -> begin
(let _165_489 = (p_qlident lid)
in (let _165_488 = (p_tuplePattern pat)
in (infix2 FStar_Pprint.equals _165_489 _165_488)))
end))
in (let _165_490 = (separate_break_map FStar_Pprint.semi p_recordFieldPat pats)
in (braces_with_nesting _165_490)))
end
| FStar_Parser_AST.PatTuple (pats, true) -> begin
(let _165_493 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (let _165_492 = (separate_break_map FStar_Pprint.comma p_constructorPattern pats)
in (let _165_491 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_493 _165_492 _165_491))))
end
| FStar_Parser_AST.PatTvar (tv, arg_qualifier_opt) -> begin
(

let _67_590 = ()
in (p_tvar tv))
end
| FStar_Parser_AST.PatOp (op) -> begin
(let _165_497 = (let _165_496 = (let _165_495 = (str op)
in (let _165_494 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat _165_495 _165_494)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_496))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_497))
end
| FStar_Parser_AST.PatWild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.PatConst (c) -> begin
(p_constant c)
end
| FStar_Parser_AST.PatVar (lid, aqual) -> begin
(let _165_499 = (FStar_Pprint.optional p_aqual aqual)
in (let _165_498 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat _165_499 _165_498)))
end
| FStar_Parser_AST.PatName (uid) -> begin
(p_quident uid)
end
| FStar_Parser_AST.PatOr (_67_604) -> begin
(FStar_All.failwith "Inner or pattern !")
end
| (FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (_); FStar_Parser_AST.prange = _}, _)) | (FStar_Parser_AST.PatTuple (_, false)) -> begin
(let _165_500 = (p_tuplePattern p)
in (parens_with_nesting _165_500))
end
| _67_622 -> begin
(let _165_502 = (let _165_501 = (FStar_Parser_AST.pat_to_string p)
in (FStar_Util.format1 "Invalid pattern %s" _165_501))
in (FStar_All.failwith _165_502))
end))
and p_binder : FStar_Parser_AST.binder  ->  FStar_Pprint.document = (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (lid) -> begin
(let _165_505 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (let _165_504 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat _165_505 _165_504)))
end
| FStar_Parser_AST.TVariable (lid) -> begin
(p_lident lid)
end
| FStar_Parser_AST.Annotated (lid, t) -> begin
(let _165_512 = (let _165_511 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (let _165_510 = (let _165_509 = (p_lident lid)
in (let _165_508 = (let _165_507 = (let _165_506 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat _165_506 FStar_Pprint.rparen))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_507))
in (FStar_Pprint.op_Hat_Hat _165_509 _165_508)))
in (FStar_Pprint.op_Hat_Hat _165_511 _165_510)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_512))
end
| FStar_Parser_AST.TAnnotated (_67_633) -> begin
(FStar_All.failwith "Is this still used ?")
end
| FStar_Parser_AST.NoName (t) -> begin
(let _165_518 = (let _165_517 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (let _165_516 = (let _165_515 = (let _165_514 = (let _165_513 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat _165_513 FStar_Pprint.rparen))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_514))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.underscore _165_515))
in (FStar_Pprint.op_Hat_Hat _165_517 _165_516)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_518))
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
(let _165_531 = (let _165_529 = (let _165_528 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat _165_528 FStar_Pprint.semi))
in (FStar_Pprint.group _165_529))
in (let _165_530 = (p_term e2)
in (FStar_Pprint.op_Hat_Slash_Hat _165_531 _165_530)))
end
| _67_651 -> begin
(let _165_532 = (p_noSeqTerm e)
in (FStar_Pprint.group _165_532))
end))
and p_noSeqTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Ascribed (e, t) -> begin
(let _165_538 = (let _165_537 = (p_tmIff e)
in (let _165_536 = (let _165_535 = (let _165_534 = (p_typ t)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon _165_534))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.langle _165_535))
in (FStar_Pprint.op_Hat_Slash_Hat _165_537 _165_536)))
in (FStar_Pprint.group _165_538))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::(e3)::[]) when (op = ".()<-") -> begin
(let _165_549 = (let _165_548 = (let _165_545 = (let _165_544 = (p_atomicTermNotQUident e1)
in (let _165_543 = (let _165_542 = (let _165_541 = (let _165_539 = (p_term e2)
in (parens_with_nesting _165_539))
in (let _165_540 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat _165_541 _165_540)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_542))
in (FStar_Pprint.op_Hat_Hat _165_544 _165_543)))
in (FStar_Pprint.group _165_545))
in (let _165_547 = (let _165_546 = (p_noSeqTerm e3)
in (jump2 _165_546))
in (FStar_Pprint.op_Hat_Hat _165_548 _165_547)))
in (FStar_Pprint.group _165_549))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::(e3)::[]) when (op = ".[]<-") -> begin
(let _165_560 = (let _165_559 = (let _165_556 = (let _165_555 = (p_atomicTermNotQUident e1)
in (let _165_554 = (let _165_553 = (let _165_552 = (let _165_550 = (p_term e2)
in (brackets_with_nesting _165_550))
in (let _165_551 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat _165_552 _165_551)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_553))
in (FStar_Pprint.op_Hat_Hat _165_555 _165_554)))
in (FStar_Pprint.group _165_556))
in (let _165_558 = (let _165_557 = (p_noSeqTerm e3)
in (jump2 _165_557))
in (FStar_Pprint.op_Hat_Hat _165_559 _165_558)))
in (FStar_Pprint.group _165_560))
end
| FStar_Parser_AST.Requires (e, wtf) -> begin
(

let _67_675 = ()
in (let _165_563 = (let _165_562 = (str "requires")
in (let _165_561 = (p_typ e)
in (FStar_Pprint.op_Hat_Slash_Hat _165_562 _165_561)))
in (FStar_Pprint.group _165_563)))
end
| FStar_Parser_AST.Ensures (e, wtf) -> begin
(

let _67_681 = ()
in (let _165_566 = (let _165_565 = (str "ensures")
in (let _165_564 = (p_typ e)
in (FStar_Pprint.op_Hat_Slash_Hat _165_565 _165_564)))
in (FStar_Pprint.group _165_566)))
end
| FStar_Parser_AST.Attributes (es) -> begin
(let _165_569 = (let _165_568 = (str "attributes")
in (let _165_567 = (FStar_Pprint.separate_map break1 p_atomicTerm es)
in (FStar_Pprint.op_Hat_Slash_Hat _165_568 _165_567)))
in (FStar_Pprint.group _165_569))
end
| FStar_Parser_AST.If (e1, e2, e3) -> begin
if (is_unit e3) then begin
(let _165_576 = (let _165_575 = (let _165_571 = (str "if")
in (let _165_570 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat _165_571 _165_570)))
in (let _165_574 = (let _165_573 = (str "then")
in (let _165_572 = (p_noSeqTerm e2)
in (op_Hat_Slash_Plus_Hat _165_573 _165_572)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_575 _165_574)))
in (FStar_Pprint.group _165_576))
end else begin
(

let e2_doc = (match (e2.FStar_Parser_AST.tm) with
| FStar_Parser_AST.If (_67_691, _67_693, e3) when (is_unit e3) -> begin
(let _165_577 = (p_noSeqTerm e2)
in (parens_with_nesting _165_577))
end
| _67_698 -> begin
(p_noSeqTerm e2)
end)
in (let _165_587 = (let _165_586 = (let _165_579 = (str "if")
in (let _165_578 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat _165_579 _165_578)))
in (let _165_585 = (let _165_584 = (let _165_580 = (str "then")
in (op_Hat_Slash_Plus_Hat _165_580 e2_doc))
in (let _165_583 = (let _165_582 = (str "else")
in (let _165_581 = (p_noSeqTerm e3)
in (op_Hat_Slash_Plus_Hat _165_582 _165_581)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_584 _165_583)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_586 _165_585)))
in (FStar_Pprint.group _165_587)))
end
end
| FStar_Parser_AST.TryWith (e, branches) -> begin
(let _165_595 = (let _165_594 = (let _165_589 = (str "try")
in (let _165_588 = (p_noSeqTerm e)
in (prefix2 _165_589 _165_588)))
in (let _165_593 = (let _165_592 = (str "with")
in (let _165_591 = (let _165_590 = (FStar_Pprint.concat_map p_patternBranch branches)
in (jump2 _165_590))
in (FStar_Pprint.op_Hat_Slash_Hat _165_592 _165_591)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_594 _165_593)))
in (FStar_Pprint.group _165_595))
end
| FStar_Parser_AST.Match (e, branches) -> begin
(let _165_603 = (let _165_602 = (let _165_597 = (str "match")
in (let _165_596 = (p_noSeqTerm e)
in (prefix2 _165_597 _165_596)))
in (let _165_601 = (let _165_600 = (str "with")
in (let _165_599 = (let _165_598 = (FStar_Pprint.concat_map p_patternBranch branches)
in (jump2 _165_598))
in (FStar_Pprint.op_Hat_Slash_Hat _165_600 _165_599)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_602 _165_601)))
in (FStar_Pprint.group _165_603))
end
| FStar_Parser_AST.LetOpen (uid, e) -> begin
(let _165_609 = (let _165_608 = (let _165_606 = (str "let open")
in (let _165_605 = (p_quident uid)
in (let _165_604 = (str "in")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_606 _165_605 _165_604))))
in (let _165_607 = (p_term e)
in (FStar_Pprint.op_Hat_Slash_Hat _165_608 _165_607)))
in (FStar_Pprint.group _165_609))
end
| FStar_Parser_AST.Let (q, lbs, e) -> begin
(

let let_doc = (let _165_611 = (str "let")
in (let _165_610 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat _165_611 _165_610)))
in (let _165_616 = (let _165_612 = (str "and")
in (precede_break_separate_map let_doc _165_612 p_letbinding lbs))
in (let _165_615 = (let _165_614 = (str "in")
in (let _165_613 = (p_term e)
in (prefix2 _165_614 _165_613)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_616 _165_615))))
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, typ_opt); FStar_Parser_AST.prange = _67_719})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, branches); FStar_Parser_AST.range = _67_729; FStar_Parser_AST.level = _67_727}) when (matches_var maybe_x x) -> begin
(let _165_618 = (str "function")
in (let _165_617 = (FStar_Pprint.concat_map p_patternBranch branches)
in (op_Hat_Slash_Plus_Hat _165_618 _165_617)))
end
| FStar_Parser_AST.Assign (id, e) -> begin
(let _165_622 = (let _165_621 = (p_lident id)
in (let _165_620 = (let _165_619 = (p_noSeqTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow _165_619))
in (FStar_Pprint.op_Hat_Slash_Hat _165_621 _165_620)))
in (FStar_Pprint.group _165_622))
end
| _67_742 -> begin
(p_typ e)
end))
and p_typ : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| (FStar_Parser_AST.QForall (bs, trigger, e1)) | (FStar_Parser_AST.QExists (bs, trigger, e1)) -> begin
(let _165_632 = (let _165_631 = (let _165_629 = (let _165_628 = (p_quantifier e)
in (let _165_627 = (let _165_626 = (p_binders bs)
in (let _165_625 = (let _165_624 = (p_trigger trigger)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_624))
in (FStar_Pprint.op_Hat_Hat _165_626 _165_625)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_628 _165_627)))
in (FStar_Pprint.group _165_629))
in (let _165_630 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Slash_Hat _165_631 _165_630)))
in (FStar_Pprint.group _165_632))
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
(let _165_640 = (let _165_639 = (let _165_638 = (str "pattern")
in (let _165_637 = (let _165_636 = (let _165_635 = (p_disjunctivePats pats)
in (jump2 _165_635))
in (FStar_Pprint.op_Hat_Slash_Hat _165_636 FStar_Pprint.rbrace))
in (FStar_Pprint.op_Hat_Slash_Hat _165_638 _165_637)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_639))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace _165_640))
end))
and p_disjunctivePats : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun pats -> (let _165_642 = (str "\\/")
in (FStar_Pprint.separate_map _165_642 p_conjunctivePats pats)))
and p_conjunctivePats : FStar_Parser_AST.term Prims.list  ->  FStar_Pprint.document = (fun pats -> (let _165_644 = (FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats)
in (FStar_Pprint.group _165_644)))
and p_simpleTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Abs (pats, e) -> begin
(let _165_650 = (let _165_648 = (str "fun")
in (let _165_647 = (let _165_646 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Slash_Hat _165_646 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat _165_648 _165_647)))
in (let _165_649 = (p_term e)
in (op_Hat_Slash_Plus_Hat _165_650 _165_649)))
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
(let _165_659 = (let _165_658 = (let _165_657 = (p_disjunctivePattern pat)
in (let _165_656 = (let _165_655 = (p_maybeWhen when_opt)
in (let _165_654 = (let _165_653 = (p_term e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.rarrow _165_653))
in (FStar_Pprint.op_Hat_Hat _165_655 _165_654)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_657 _165_656)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_658))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar _165_659))
end))
and p_maybeWhen : FStar_Parser_AST.term Prims.option  ->  FStar_Pprint.document = (fun _67_14 -> (match (_67_14) with
| None -> begin
FStar_Pprint.empty
end
| Some (e) -> begin
(let _165_663 = (str "when")
in (let _165_662 = (let _165_661 = (p_tmFormula e)
in (FStar_Pprint.op_Hat_Hat _165_661 FStar_Pprint.space))
in (op_Hat_Slash_Plus_Hat _165_663 _165_662)))
end))
and p_tmIff : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("<==>", (e1)::(e2)::[]) -> begin
(let _165_667 = (str "<==>")
in (let _165_666 = (p_tmImplies e1)
in (let _165_665 = (p_tmIff e2)
in (infix2 _165_667 _165_666 _165_665))))
end
| _67_791 -> begin
(p_tmImplies e)
end))
and p_tmImplies : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("==>", (e1)::(e2)::[]) -> begin
(let _165_671 = (str "==>")
in (let _165_670 = (p_tmArrow p_tmFormula e1)
in (let _165_669 = (p_tmImplies e2)
in (infix2 _165_671 _165_670 _165_669))))
end
| _67_800 -> begin
(p_tmArrow p_tmFormula e)
end))
and p_tmArrow : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_Tm e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Product (bs, tgt) -> begin
(let _165_683 = (let _165_682 = (FStar_Pprint.concat_map (fun b -> (let _165_680 = (p_binder b)
in (let _165_679 = (let _165_678 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_678))
in (FStar_Pprint.op_Hat_Hat _165_680 _165_679)))) bs)
in (let _165_681 = (p_tmArrow p_Tm tgt)
in (FStar_Pprint.op_Hat_Hat _165_682 _165_681)))
in (FStar_Pprint.group _165_683))
end
| _67_809 -> begin
(p_Tm e)
end))
and p_tmFormula : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("\\/", (e1)::(e2)::[]) -> begin
(let _165_687 = (str "\\/")
in (let _165_686 = (p_tmFormula e1)
in (let _165_685 = (p_tmConjunction e2)
in (infix2 _165_687 _165_686 _165_685))))
end
| _67_818 -> begin
(p_tmConjunction e)
end))
and p_tmConjunction : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("/\\", (e1)::(e2)::[]) -> begin
(let _165_691 = (str "/\\")
in (let _165_690 = (p_tmConjunction e1)
in (let _165_689 = (p_tmTuple e2)
in (infix2 _165_691 _165_690 _165_689))))
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
(let _165_698 = (let _165_697 = (FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_697))
in (FStar_Pprint.group _165_698))
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
(let _165_705 = (let _165_704 = (str op)
in (let _165_703 = (p_tmEq' left e1)
in (let _165_702 = (p_tmEq' right e2)
in (infix2 _165_704 _165_703 _165_702))))
in (paren_if curr mine _165_705))
end))
end
| FStar_Parser_AST.Op (":=", (e1)::(e2)::[]) -> begin
(let _165_711 = (let _165_710 = (p_tmEq e1)
in (let _165_709 = (let _165_708 = (let _165_707 = (let _165_706 = (p_tmEq e2)
in (op_Hat_Slash_Plus_Hat FStar_Pprint.equals _165_706))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_707))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_708))
in (FStar_Pprint.op_Hat_Hat _165_710 _165_709)))
in (FStar_Pprint.group _165_711))
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
(let _165_718 = (let _165_717 = (str op)
in (let _165_716 = (p_tmNoEq' left e1)
in (let _165_715 = (p_tmNoEq' right e2)
in (infix2 _165_717 _165_716 _165_715))))
in (paren_if curr mine _165_718))
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

let p_dsumfst = (fun b -> (let _165_724 = (p_binder b)
in (let _165_723 = (let _165_722 = (let _165_721 = (str "&")
in (FStar_Pprint.op_Hat_Hat _165_721 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_722))
in (FStar_Pprint.op_Hat_Hat _165_724 _165_723))))
in (let _165_727 = (let _165_726 = (FStar_Pprint.concat_map p_dsumfst binders)
in (let _165_725 = (p_tmNoEq' right res)
in (FStar_Pprint.op_Hat_Hat _165_726 _165_725)))
in (paren_if curr mine _165_727)))
end)))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (is_operatorInfix34 op) -> begin
(

let _67_905 = (levels op)
in (match (_67_905) with
| (left, mine, right) -> begin
(let _165_731 = (let _165_730 = (str op)
in (let _165_729 = (p_tmNoEq' left e1)
in (let _165_728 = (p_tmNoEq' right e2)
in (infix2 _165_730 _165_729 _165_728))))
in (paren_if curr mine _165_731))
end))
end
| FStar_Parser_AST.Op ("-", (e)::[]) -> begin
(

let _67_914 = (levels "-")
in (match (_67_914) with
| (left, mine, right) -> begin
(let _165_732 = (p_tmNoEq' mine e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus _165_732))
end))
end
| FStar_Parser_AST.NamedTyp (lid, e) -> begin
(let _165_736 = (let _165_735 = (p_lidentOrUnderscore lid)
in (let _165_734 = (let _165_733 = (p_appTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon _165_733))
in (FStar_Pprint.op_Hat_Slash_Hat _165_735 _165_734)))
in (FStar_Pprint.group _165_736))
end
| FStar_Parser_AST.Refine (b, phi) -> begin
(p_refinedBinder b phi)
end
| FStar_Parser_AST.Record (with_opt, record_fields) -> begin
(let _165_739 = (let _165_738 = (default_or_map FStar_Pprint.empty p_with_clause with_opt)
in (let _165_737 = (FStar_Pprint.separate_map FStar_Pprint.semi p_simpleDef record_fields)
in (FStar_Pprint.op_Hat_Hat _165_738 _165_737)))
in (braces_with_nesting _165_739))
end
| FStar_Parser_AST.Op ("~", (e)::[]) -> begin
(let _165_742 = (let _165_741 = (str "~")
in (let _165_740 = (p_atomicTerm e)
in (FStar_Pprint.op_Hat_Hat _165_741 _165_740)))
in (FStar_Pprint.group _165_742))
end
| _67_933 -> begin
(p_appTerm e)
end))
and p_with_clause : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (let _165_747 = (p_appTerm e)
in (let _165_746 = (let _165_745 = (let _165_744 = (str "with")
in (FStar_Pprint.op_Hat_Hat _165_744 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_745))
in (FStar_Pprint.op_Hat_Hat _165_747 _165_746))))
and p_refinedBinder : FStar_Parser_AST.binder  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun b phi -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (lid, t) -> begin
(let _165_757 = (let _165_756 = (p_lident lid)
in (let _165_755 = (let _165_754 = (let _165_753 = (p_typ t)
in (let _165_752 = (let _165_751 = (let _165_750 = (p_term phi)
in (braces_with_nesting _165_750))
in (FStar_Pprint.op_Hat_Hat _165_751 FStar_Pprint.rparen))
in (FStar_Pprint.op_Hat_Hat _165_753 _165_752)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_754))
in (FStar_Pprint.op_Hat_Hat _165_756 _165_755)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_757))
end
| FStar_Parser_AST.TAnnotated (_67_942) -> begin
(FStar_All.failwith "Is this still used ?")
end
| (FStar_Parser_AST.Variable (_)) | (FStar_Parser_AST.TVariable (_)) | (FStar_Parser_AST.NoName (_)) -> begin
(let _165_759 = (let _165_758 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" _165_758))
in (FStar_All.failwith _165_759))
end))
and p_simpleDef : (FStar_Ident.lid * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun _67_955 -> (match (_67_955) with
| (lid, e) -> begin
(let _165_764 = (let _165_763 = (p_qlident lid)
in (let _165_762 = (let _165_761 = (p_simpleTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals _165_761))
in (FStar_Pprint.op_Hat_Slash_Hat _165_763 _165_762)))
in (FStar_Pprint.group _165_764))
end))
and p_appTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App (_67_958) when (is_general_application e) -> begin
(

let _67_962 = (head_and_args e)
in (match (_67_962) with
| (head, args) -> begin
(let _165_767 = (p_indexingTerm head)
in (let _165_766 = (FStar_Pprint.separate_map FStar_Pprint.space p_argTerm args)
in (op_Hat_Slash_Plus_Hat _165_767 _165_766)))
end))
end
| FStar_Parser_AST.Construct (lid, args) when (not ((is_dtuple_constructor lid))) -> begin
(let _165_769 = (p_quident lid)
in (let _165_768 = (FStar_Pprint.separate_map FStar_Pprint.space p_argTerm args)
in (op_Hat_Slash_Plus_Hat _165_769 _165_768)))
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
(let _165_771 = (p_indexingTerm e)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.langle _165_771 FStar_Pprint.rangle))
end
| (e, FStar_Parser_AST.Hash) -> begin
(let _165_773 = (str "#")
in (let _165_772 = (p_indexingTerm e)
in (FStar_Pprint.op_Hat_Hat _165_773 _165_772)))
end
| (e, FStar_Parser_AST.Nothing) -> begin
(p_indexingTerm e)
end))
and p_indexingTerm_aux : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun exit e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op (".()", (e1)::(e2)::[]) -> begin
(let _165_783 = (let _165_782 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (let _165_781 = (let _165_780 = (let _165_779 = (p_term e2)
in (parens_with_nesting _165_779))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_780))
in (FStar_Pprint.op_Hat_Hat _165_782 _165_781)))
in (FStar_Pprint.group _165_783))
end
| FStar_Parser_AST.Op (".[]", (e1)::(e2)::[]) -> begin
(let _165_788 = (let _165_787 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (let _165_786 = (let _165_785 = (let _165_784 = (p_term e2)
in (brackets_with_nesting _165_784))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_785))
in (FStar_Pprint.op_Hat_Hat _165_787 _165_786)))
in (FStar_Pprint.group _165_788))
end
| _67_1007 -> begin
(exit e)
end))
and p_indexingTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_indexingTerm_aux p_atomicTerm e))
and p_atomicTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.LetOpen (lid, e) -> begin
(let _165_794 = (p_quident lid)
in (let _165_793 = (let _165_792 = (let _165_791 = (p_term e)
in (parens_with_nesting _165_791))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_792))
in (FStar_Pprint.op_Hat_Hat _165_794 _165_793)))
end
| FStar_Parser_AST.Name (lid) -> begin
(p_quident lid)
end
| FStar_Parser_AST.Op (op, (e)::[]) -> begin
(let _165_796 = (str op)
in (let _165_795 = (p_atomicTerm e)
in (FStar_Pprint.op_Hat_Hat _165_796 _165_795)))
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
(let _165_799 = (str op)
in (let _165_798 = (p_atomicTermNotQUident e)
in (FStar_Pprint.op_Hat_Hat _165_799 _165_798)))
end
| FStar_Parser_AST.Op (op, []) -> begin
(let _165_803 = (let _165_802 = (let _165_801 = (str op)
in (let _165_800 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat _165_801 _165_800)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_802))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_803))
end
| FStar_Parser_AST.Construct (lid, args) when (is_dtuple_constructor lid) -> begin
(let _165_807 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (let _165_806 = (let _165_804 = (FStar_List.map Prims.fst args)
in (FStar_Pprint.separate_map FStar_Pprint.comma p_tmEq _165_804))
in (let _165_805 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_807 _165_806 _165_805))))
end
| FStar_Parser_AST.Project (e, lid) -> begin
(let _165_811 = (let _165_810 = (p_atomicTermNotQUident e)
in (let _165_809 = (let _165_808 = (p_qlident lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_808))
in (FStar_Pprint.op_Hat_Slash_Hat _165_810 _165_809)))
in (FStar_Pprint.group _165_811))
end
| _67_1053 -> begin
(p_projectionLHS e)
end))
and p_projectionLHS : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (lid) -> begin
(p_qlident lid)
end
| FStar_Parser_AST.Projector (constr_lid, field_lid) -> begin
(let _165_816 = (p_quident constr_lid)
in (let _165_815 = (let _165_814 = (let _165_813 = (p_lident field_lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_813))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark _165_814))
in (FStar_Pprint.op_Hat_Hat _165_816 _165_815)))
end
| FStar_Parser_AST.Discrim (constr_lid) -> begin
(let _165_817 = (p_quident constr_lid)
in (FStar_Pprint.op_Hat_Hat _165_817 FStar_Pprint.qmark))
end
| FStar_Parser_AST.Paren (e) -> begin
(let _165_818 = (p_term e)
in (parens_with_nesting _165_818))
end
| _67_1066 when (is_array e) -> begin
(

let es = (extract_from_list e)
in (let _165_821 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar)
in (let _165_820 = (FStar_Pprint.separate_map FStar_Pprint.semi p_noSeqTerm es)
in (let _165_819 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_821 _165_820 _165_819)))))
end
| _67_1069 when (is_list e) -> begin
(let _165_823 = (let _165_822 = (extract_from_list e)
in (FStar_Pprint.separate_map FStar_Pprint.semi p_noSeqTerm _165_822))
in (brackets_with_nesting _165_823))
end
| _67_1071 when (is_lex_list e) -> begin
(let _165_826 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket)
in (let _165_825 = (let _165_824 = (extract_from_list e)
in (FStar_Pprint.separate_map FStar_Pprint.semi p_noSeqTerm _165_824))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_826 _165_825 FStar_Pprint.rbracket)))
end
| _67_1073 when (is_ref_set e) -> begin
(

let es = (extract_from_ref_set e)
in (let _165_828 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace)
in (let _165_827 = (FStar_Pprint.separate_map FStar_Pprint.comma p_appTerm es)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_828 _165_827 FStar_Pprint.rbrace))))
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Op (_)) | (FStar_Parser_AST.Tvar (_)) | (FStar_Parser_AST.Uvar (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) | (FStar_Parser_AST.Construct (_)) | (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.App (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.LetOpen (_)) | (FStar_Parser_AST.Seq (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Ascribed (_)) | (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Project (_)) | (FStar_Parser_AST.Product (_)) | (FStar_Parser_AST.Sum (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Refine (_)) | (FStar_Parser_AST.NamedTyp (_)) | (FStar_Parser_AST.Requires (_)) | (FStar_Parser_AST.Ensures (_)) | (FStar_Parser_AST.Assign (_)) | (FStar_Parser_AST.Attributes (_)) -> begin
(let _165_829 = (p_term e)
in (parens_with_nesting _165_829))
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
(let _165_831 = (FStar_Pprint.doc_of_char x)
in (FStar_Pprint.squotes _165_831))
end
| FStar_Const.Const_string (bytes, _67_1174) -> begin
(let _165_832 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes _165_832))
end
| FStar_Const.Const_bytearray (bytes, _67_1179) -> begin
(let _165_835 = (let _165_833 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes _165_833))
in (let _165_834 = (str "B")
in (FStar_Pprint.op_Hat_Hat _165_835 _165_834)))
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
(let _165_842 = (signedness s)
in (let _165_841 = (width w)
in (FStar_Pprint.op_Hat_Hat _165_842 _165_841)))
end)) sign_width_opt)
in (let _165_843 = (str repr)
in (FStar_Pprint.op_Hat_Hat _165_843 ending)))))
end
| FStar_Const.Const_range (r) -> begin
(let _165_844 = (FStar_Range.string_of_range r)
in (str _165_844))
end
| FStar_Const.Const_reify -> begin
(str "reify")
end
| FStar_Const.Const_reflect (lid) -> begin
(let _165_848 = (p_quident lid)
in (let _165_847 = (let _165_846 = (let _165_845 = (str "reflect")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_845))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark _165_846))
in (FStar_Pprint.op_Hat_Hat _165_848 _165_847)))
end))
and p_universe : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (let _165_851 = (str "u#")
in (let _165_850 = (p_atomicUniverse u)
in (FStar_Pprint.op_Hat_Hat _165_851 _165_850))))
and p_universeFrom : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match (u.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("+", (u1)::(u2)::[]) -> begin
(let _165_856 = (let _165_855 = (p_universeFrom u1)
in (let _165_854 = (let _165_853 = (p_universeFrom u2)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus _165_853))
in (FStar_Pprint.op_Hat_Slash_Hat _165_855 _165_854)))
in (FStar_Pprint.group _165_856))
end
| FStar_Parser_AST.App (_67_1214) -> begin
(

let _67_1218 = (head_and_args u)
in (match (_67_1218) with
| (head, args) -> begin
(match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (maybe_max_lid) when (FStar_Ident.lid_equals maybe_max_lid FStar_Syntax_Const.max_lid) -> begin
(let _165_860 = (let _165_859 = (p_qlident FStar_Syntax_Const.max_lid)
in (let _165_858 = (FStar_Pprint.separate_map FStar_Pprint.space (fun _67_1224 -> (match (_67_1224) with
| (u, _67_1223) -> begin
(p_atomicUniverse u)
end)) args)
in (op_Hat_Slash_Plus_Hat _165_859 _165_858)))
in (FStar_Pprint.group _165_860))
end
| _67_1226 -> begin
(let _165_862 = (let _165_861 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" _165_861))
in (FStar_All.failwith _165_862))
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
(let _165_864 = (p_universeFrom u)
in (parens_with_nesting _165_864))
end
| (FStar_Parser_AST.Op ("+", (_)::(_)::[])) | (FStar_Parser_AST.App (_)) -> begin
(let _165_865 = (p_universeFrom u)
in (parens_with_nesting _165_865))
end
| _67_1253 -> begin
(let _165_867 = (let _165_866 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" _165_866))
in (FStar_All.failwith _165_867))
end))
and p_univar : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match (u.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Uvar (id) -> begin
(str (FStar_Ident.text_of_id id))
end
| _67_1258 -> begin
(let _165_870 = (let _165_869 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Not a universe variable %s" _165_869))
in (FStar_All.failwith _165_870))
end))


let term_to_document : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_term e))


let decl_to_document : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun e -> (p_decl e))


let modul_to_document : FStar_Parser_AST.modul  ->  FStar_Pprint.document = (fun m -> (match (m) with
| (FStar_Parser_AST.Module (_, decls)) | (FStar_Parser_AST.Interface (_, decls, _)) -> begin
(let _165_877 = (FStar_All.pipe_right decls (FStar_List.map decl_to_document))
in (FStar_All.pipe_right _165_877 (FStar_Pprint.separate FStar_Pprint.hardline)))
end))




