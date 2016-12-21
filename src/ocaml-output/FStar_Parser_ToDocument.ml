
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


let separate_map_or_flow = (fun sep f l -> if ((FStar_List.length l) < (Prims.parse_int "10")) then begin
(FStar_Pprint.separate_map sep f l)
end else begin
(FStar_Pprint.flow_map sep f l)
end)


let doc_of_fsdoc : (Prims.string * (Prims.string * Prims.string) Prims.list)  ->  FStar_Pprint.document = (fun _67_49 -> (match (_67_49) with
| (comment, keywords) -> begin
(let _165_81 = (let _165_80 = (let _165_79 = (str comment)
in (let _165_78 = (let _165_77 = (let _165_76 = (FStar_Pprint.separate_map FStar_Pprint.comma (fun _67_52 -> (match (_67_52) with
| (k, v) -> begin
(let _165_75 = (let _165_74 = (str k)
in (let _165_73 = (let _165_72 = (let _165_71 = (str v)
in (_165_71)::[])
in (FStar_Pprint.rarrow)::_165_72)
in (_165_74)::_165_73))
in (FStar_Pprint.concat _165_75))
end)) keywords)
in (_165_76)::[])
in (FStar_Pprint.space)::_165_77)
in (_165_79)::_165_78))
in (FStar_Pprint.concat _165_80))
in (FStar_Pprint.group _165_81))
end))


let is_unit : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Const (FStar_Const.Const_unit) -> begin
true
end
| _67_57 -> begin
false
end))


let matches_var : FStar_Parser_AST.term  ->  FStar_Ident.ident  ->  Prims.bool = (fun t x -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (y) -> begin
(x.FStar_Ident.idText = (FStar_Ident.text_of_lid y))
end
| _67_63 -> begin
false
end))


let is_tuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Syntax_Util.is_tuple_data_lid'


let is_dtuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Syntax_Util.is_dtuple_data_lid'


let is_list_structure : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun cons_lid nil_lid -> (

let rec aux = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (lid, []) -> begin
(FStar_Ident.lid_equals lid nil_lid)
end
| FStar_Parser_AST.Construct (lid, (_67_78)::((e2, _67_75))::[]) -> begin
((FStar_Ident.lid_equals lid cons_lid) && (aux e2))
end
| _67_83 -> begin
false
end))
in aux))


let is_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Syntax_Const.cons_lid FStar_Syntax_Const.nil_lid)


let is_lex_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Syntax_Const.lexcons_lid FStar_Syntax_Const.lextop_lid)


let rec extract_from_list : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (_67_86, []) -> begin
[]
end
| FStar_Parser_AST.Construct (_67_91, ((e1, FStar_Parser_AST.Nothing))::((e2, FStar_Parser_AST.Nothing))::[]) -> begin
(let _165_104 = (extract_from_list e2)
in (e1)::_165_104)
end
| _67_102 -> begin
(let _165_106 = (let _165_105 = (FStar_Parser_AST.term_to_string e)
in (FStar_Util.format1 "Not a list %s" _165_105))
in (FStar_All.failwith _165_106))
end))


let is_array : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (lid); FStar_Parser_AST.range = _67_107; FStar_Parser_AST.level = _67_105}, l, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals lid FStar_Syntax_Const.array_mk_array_lid) && (is_list l))
end
| _67_116 -> begin
false
end))


let rec is_ref_set : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (maybe_empty_lid) -> begin
(FStar_Ident.lid_equals maybe_empty_lid FStar_Syntax_Const.tset_empty)
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_singleton_lid); FStar_Parser_AST.range = _67_123; FStar_Parser_AST.level = _67_121}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_ref_lid); FStar_Parser_AST.range = _67_134; FStar_Parser_AST.level = _67_132}, e, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = _67_130; FStar_Parser_AST.level = _67_128}, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals maybe_singleton_lid FStar_Syntax_Const.tset_singleton) && (FStar_Ident.lid_equals maybe_ref_lid FStar_Syntax_Const.heap_ref))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_union_lid); FStar_Parser_AST.range = _67_153; FStar_Parser_AST.level = _67_151}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = _67_149; FStar_Parser_AST.level = _67_147}, e2, FStar_Parser_AST.Nothing) -> begin
(((FStar_Ident.lid_equals maybe_union_lid FStar_Syntax_Const.tset_union) && (is_ref_set e1)) && (is_ref_set e2))
end
| _67_167 -> begin
false
end))


let rec extract_from_ref_set : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (_67_170) -> begin
[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (_67_177); FStar_Parser_AST.range = _67_175; FStar_Parser_AST.level = _67_173}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (_67_189); FStar_Parser_AST.range = _67_187; FStar_Parser_AST.level = _67_185}, e, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = _67_183; FStar_Parser_AST.level = _67_181}, FStar_Parser_AST.Nothing) -> begin
(e)::[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (_67_209); FStar_Parser_AST.range = _67_207; FStar_Parser_AST.level = _67_205}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = _67_203; FStar_Parser_AST.level = _67_201}, e2, FStar_Parser_AST.Nothing) -> begin
(let _165_114 = (extract_from_ref_set e1)
in (let _165_113 = (extract_from_ref_set e2)
in (FStar_List.append _165_114 _165_113)))
end
| _67_222 -> begin
(let _165_116 = (let _165_115 = (FStar_Parser_AST.term_to_string e)
in (FStar_Util.format1 "Not a ref set %s" _165_115))
in (FStar_All.failwith _165_116))
end))


let is_general_application : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (not (((is_array e) || (is_ref_set e)))))


let is_general_construction : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (not (((is_list e) || (is_lex_list e)))))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun e -> (

let rec aux = (fun e acc -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App (head, arg, imp) -> begin
(aux head ((((arg), (imp)))::acc))
end
| _67_235 -> begin
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


let matches_level = (fun s _67_250 -> (match (_67_250) with
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
in (FStar_List.mapi (fun i _67_260 -> (match (_67_260) with
| (assoc, tokens) -> begin
(((levels_from_associativity i assoc)), (tokens))
end)) level_associativity_spec))


let assign_levels : associativity_level Prims.list  ->  Prims.string  ->  (Prims.int * Prims.int * Prims.int) = (fun token_associativity_spec s -> (match ((FStar_List.tryFind (matches_level s) level_table)) with
| Some (assoc_levels, _67_265) -> begin
assoc_levels
end
| _67_269 -> begin
(FStar_All.failwith (Prims.strcat "Unrecognized operator " s))
end))


let max : Prims.int  ->  Prims.int  ->  Prims.int = (fun k1 k2 -> if (k1 > k2) then begin
k1
end else begin
k2
end)


let max_level = (fun l -> (

let find_level_and_max = (fun n level -> (match ((FStar_List.tryFind (fun _67_279 -> (match (_67_279) with
| (_67_277, tokens) -> begin
(tokens = (Prims.snd level))
end)) level_table)) with
| Some ((_67_281, l, _67_284), _67_287) -> begin
(max n l)
end
| None -> begin
(let _165_160 = (let _165_159 = (let _165_158 = (FStar_List.map token_to_string (Prims.snd level))
in (FStar_String.concat "," _165_158))
in (FStar_Util.format1 "Undefined associativity level %s" _165_159))
in (FStar_All.failwith _165_160))
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


let rec p_decl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (let _165_263 = (FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc)
in (let _165_262 = (p_decl2 d)
in (FStar_Pprint.op_Hat_Hat _165_263 _165_262))))
and p_fsdoc : FStar_Parser_AST.fsdoc  ->  FStar_Pprint.document = (fun _67_306 -> (match (_67_306) with
| (doc, kwd_args) -> begin
(

let kwd_args_doc = (match (kwd_args) with
| [] -> begin
FStar_Pprint.empty
end
| kwd_args -> begin
(

let process_kwd_arg = (fun _67_312 -> (match (_67_312) with
| (kwd, arg) -> begin
(let _165_271 = (str "@")
in (let _165_270 = (let _165_269 = (str kwd)
in (let _165_268 = (let _165_267 = (str arg)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_267))
in (FStar_Pprint.op_Hat_Hat _165_269 _165_268)))
in (FStar_Pprint.op_Hat_Hat _165_271 _165_270)))
end))
in (let _165_273 = (let _165_272 = (FStar_Pprint.separate_map FStar_Pprint.hardline process_kwd_arg kwd_args)
in (FStar_Pprint.op_Hat_Hat _165_272 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline _165_273)))
end)
in (let _165_281 = (let _165_280 = (let _165_279 = (let _165_278 = (let _165_277 = (str doc)
in (let _165_276 = (let _165_275 = (let _165_274 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _165_274))
in (FStar_Pprint.op_Hat_Hat kwd_args_doc _165_275))
in (FStar_Pprint.op_Hat_Hat _165_277 _165_276)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _165_278))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _165_279))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_280))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline _165_281)))
end))
and p_decl2 : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Open (uid) -> begin
(let _165_285 = (let _165_284 = (str "open")
in (let _165_283 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat _165_284 _165_283)))
in (FStar_Pprint.group _165_285))
end
| FStar_Parser_AST.ModuleAbbrev (uid1, uid2) -> begin
(let _165_292 = (let _165_290 = (str "module")
in (let _165_289 = (let _165_288 = (let _165_287 = (p_uident uid1)
in (let _165_286 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _165_287 _165_286)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_288))
in (FStar_Pprint.op_Hat_Hat _165_290 _165_289)))
in (let _165_291 = (p_quident uid2)
in (op_Hat_Slash_Plus_Hat _165_292 _165_291)))
end
| FStar_Parser_AST.TopLevelModule (uid) -> begin
(let _165_296 = (let _165_295 = (str "module")
in (let _165_294 = (let _165_293 = (p_quident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_293))
in (FStar_Pprint.op_Hat_Hat _165_295 _165_294)))
in (FStar_Pprint.group _165_296))
end
| FStar_Parser_AST.KindAbbrev (_67_324) -> begin
(FStar_All.failwith "Deprecated, please stop throwing your old stuff at me !")
end
| FStar_Parser_AST.Tycon (qs, ((FStar_Parser_AST.TyconAbbrev (uid, tpars, None, t), None))::[]) when (FStar_List.contains FStar_Parser_AST.Effect qs) -> begin
(

let qs = (FStar_List.filter (fun q -> (q <> FStar_Parser_AST.Effect)) qs)
in (

let effect_prefix_doc = (let _165_302 = (p_qualifiers qs)
in (let _165_301 = (let _165_300 = (str "effect")
in (let _165_299 = (let _165_298 = (p_uident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_298))
in (FStar_Pprint.op_Hat_Hat _165_300 _165_299)))
in (FStar_Pprint.op_Hat_Hat _165_302 _165_301)))
in (let _165_305 = (let _165_303 = (p_typars tpars)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") effect_prefix_doc _165_303 FStar_Pprint.equals))
in (let _165_304 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _165_305 _165_304)))))
end
| FStar_Parser_AST.Tycon (qs, tcdefs) -> begin
(

let type_doc = (let _165_307 = (p_qualifiers qs)
in (let _165_306 = (str "type")
in (FStar_Pprint.op_Hat_Hat _165_307 _165_306)))
in (let _165_308 = (str "and")
in (precede_break_separate_map type_doc _165_308 p_fsdocTypeDeclPairs tcdefs)))
end
| FStar_Parser_AST.TopLevelLet (qs, q, lbs) -> begin
(

let let_doc = (let _165_312 = (p_qualifiers qs)
in (let _165_311 = (let _165_310 = (str "let")
in (let _165_309 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat _165_310 _165_309)))
in (FStar_Pprint.op_Hat_Hat _165_312 _165_311)))
in (let _165_313 = (str "and")
in (precede_break_separate_map let_doc _165_313 p_letbinding lbs)))
end
| FStar_Parser_AST.Val (qs, lid, t) -> begin
(let _165_322 = (let _165_320 = (p_qualifiers qs)
in (let _165_319 = (let _165_318 = (str "val")
in (let _165_317 = (let _165_316 = (let _165_315 = (p_lident lid)
in (let _165_314 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat _165_315 _165_314)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_316))
in (FStar_Pprint.op_Hat_Hat _165_318 _165_317)))
in (FStar_Pprint.op_Hat_Hat _165_320 _165_319)))
in (let _165_321 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _165_322 _165_321)))
end
| FStar_Parser_AST.Assume (qs, id, t) -> begin
(

let decl_keyword = if (let _165_323 = (FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_All.pipe_right _165_323 FStar_Util.is_upper)) then begin
FStar_Pprint.empty
end else begin
(let _165_324 = (str "val")
in (FStar_Pprint.op_Hat_Hat _165_324 FStar_Pprint.space))
end
in (let _165_331 = (let _165_329 = (p_qualifiers qs)
in (let _165_328 = (let _165_327 = (let _165_326 = (p_ident id)
in (let _165_325 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat _165_326 _165_325)))
in (FStar_Pprint.op_Hat_Hat decl_keyword _165_327))
in (FStar_Pprint.op_Hat_Hat _165_329 _165_328)))
in (let _165_330 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _165_331 _165_330))))
end
| FStar_Parser_AST.Exception (uid, t_opt) -> begin
(let _165_339 = (str "exception")
in (let _165_338 = (let _165_337 = (let _165_336 = (p_uident uid)
in (let _165_335 = (FStar_Pprint.optional (fun t -> (let _165_334 = (str "of")
in (let _165_333 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _165_334 _165_333)))) t_opt)
in (FStar_Pprint.op_Hat_Hat _165_336 _165_335)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_337))
in (FStar_Pprint.op_Hat_Hat _165_339 _165_338)))
end
| FStar_Parser_AST.NewEffect (qs, ne) -> begin
(let _165_344 = (p_qualifiers qs)
in (let _165_343 = (let _165_342 = (str "new_effect")
in (let _165_341 = (let _165_340 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_340))
in (FStar_Pprint.op_Hat_Hat _165_342 _165_341)))
in (FStar_Pprint.op_Hat_Hat _165_344 _165_343)))
end
| FStar_Parser_AST.SubEffect (se) -> begin
(let _165_347 = (str "sub_effect")
in (let _165_346 = (let _165_345 = (p_subEffect se)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_345))
in (FStar_Pprint.op_Hat_Hat _165_347 _165_346)))
end
| FStar_Parser_AST.NewEffectForFree (qs, ne) -> begin
(let _165_352 = (p_qualifiers qs)
in (let _165_351 = (let _165_350 = (str "new_effect_for_free")
in (let _165_349 = (let _165_348 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_348))
in (FStar_Pprint.op_Hat_Hat _165_350 _165_349)))
in (FStar_Pprint.op_Hat_Hat _165_352 _165_351)))
end
| FStar_Parser_AST.Pragma (p) -> begin
(p_pragma p)
end
| FStar_Parser_AST.Fsdoc (doc) -> begin
(let _165_353 = (p_fsdoc doc)
in (FStar_Pprint.op_Hat_Hat _165_353 FStar_Pprint.hardline))
end
| FStar_Parser_AST.Main (_67_383) -> begin
(FStar_All.failwith "*Main declaration* : Is that really still in use ??")
end))
and p_pragma : FStar_Parser_AST.pragma  ->  FStar_Pprint.document = (fun _67_6 -> (match (_67_6) with
| FStar_Parser_AST.SetOptions (s) -> begin
(let _165_358 = (str "#set-options")
in (let _165_357 = (let _165_356 = (let _165_355 = (str s)
in (FStar_Pprint.dquotes _165_355))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_356))
in (FStar_Pprint.op_Hat_Hat _165_358 _165_357)))
end
| FStar_Parser_AST.ResetOptions (s_opt) -> begin
(let _165_363 = (str "#reset-options")
in (let _165_362 = (FStar_Pprint.optional (fun s -> (let _165_361 = (let _165_360 = (str s)
in (FStar_Pprint.dquotes _165_360))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_361))) s_opt)
in (FStar_Pprint.op_Hat_Hat _165_363 _165_362)))
end))
and p_typars : FStar_Parser_AST.binder Prims.list  ->  FStar_Pprint.document = (fun bs -> (p_binders bs))
and p_fsdocTypeDeclPairs : (FStar_Parser_AST.tycon * FStar_Parser_AST.fsdoc Prims.option)  ->  FStar_Pprint.document = (fun _67_394 -> (match (_67_394) with
| (typedecl, fsdoc_opt) -> begin
(let _165_367 = (FStar_Pprint.optional p_fsdoc fsdoc_opt)
in (let _165_366 = (p_typeDecl typedecl)
in (FStar_Pprint.op_Hat_Hat _165_367 _165_366)))
end))
and p_typeDecl : FStar_Parser_AST.tycon  ->  FStar_Pprint.document = (fun _67_7 -> (match (_67_7) with
| FStar_Parser_AST.TyconAbstract (lid, bs, typ_opt) -> begin
(p_typeDeclPrefix lid bs typ_opt FStar_Pprint.empty)
end
| FStar_Parser_AST.TyconAbbrev (lid, bs, typ_opt, t) -> begin
(let _165_370 = (let _165_369 = (p_typ t)
in (prefix2 FStar_Pprint.equals _165_369))
in (p_typeDeclPrefix lid bs typ_opt _165_370))
end
| FStar_Parser_AST.TyconRecord (lid, bs, typ_opt, record_field_decls) -> begin
(let _165_374 = (let _165_373 = (let _165_372 = (let _165_371 = (separate_break_map FStar_Pprint.semi p_recordFieldDecl record_field_decls)
in (braces_with_nesting _165_371))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_372))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.equals _165_373))
in (p_typeDeclPrefix lid bs typ_opt _165_374))
end
| FStar_Parser_AST.TyconVariant (lid, bs, typ_opt, ct_decls) -> begin
(

let datacon_doc = (match (ct_decls) with
| (datacon)::[] -> begin
(p_constructorDecl datacon)
end
| datacons -> begin
(let _165_379 = (FStar_Pprint.separate_map break1 (fun decl -> (let _165_378 = (let _165_377 = (let _165_376 = (p_constructorDecl decl)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_376))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar _165_377))
in (FStar_Pprint.group _165_378))) datacons)
in (FStar_Pprint.group _165_379))
end)
in (let _165_380 = (prefix2 FStar_Pprint.equals datacon_doc)
in (p_typeDeclPrefix lid bs typ_opt _165_380)))
end))
and p_typeDeclPrefix : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.knd Prims.option  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun lid bs typ_opt cont -> (let _165_391 = (p_ident lid)
in (let _165_390 = (let _165_389 = (p_typars bs)
in (let _165_388 = (FStar_Pprint.optional (fun t -> (let _165_387 = (let _165_386 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_386))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_387))) typ_opt)
in (FStar_Pprint.op_Hat_Slash_Hat _165_389 _165_388)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_391 _165_390 cont))))
and p_recordFieldDecl : (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc Prims.option)  ->  FStar_Pprint.document = (fun _67_432 -> (match (_67_432) with
| (lid, t, doc_opt) -> begin
(let _165_397 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (let _165_396 = (let _165_395 = (p_lident lid)
in (let _165_394 = (let _165_393 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_393))
in (FStar_Pprint.op_Hat_Hat _165_395 _165_394)))
in (FStar_Pprint.op_Hat_Hat _165_397 _165_396)))
end))
and p_constructorDecl : (FStar_Ident.ident * FStar_Parser_AST.term Prims.option * FStar_Parser_AST.fsdoc Prims.option * Prims.bool)  ->  FStar_Pprint.document = (fun _67_437 -> (match (_67_437) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let sep = if use_of then begin
(str "of")
end else begin
FStar_Pprint.colon
end
in (

let uid_doc = (p_uident uid)
in (let _165_404 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (let _165_403 = (default_or_map uid_doc (fun t -> (let _165_402 = (let _165_400 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep)
in (FStar_Pprint.op_Hat_Hat uid_doc _165_400))
in (let _165_401 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _165_402 _165_401)))) t_opt)
in (FStar_Pprint.op_Hat_Hat _165_404 _165_403)))))
end))
and p_letbinding : (FStar_Parser_AST.pattern * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun _67_443 -> (match (_67_443) with
| (pat, e) -> begin
(

let pat_doc = (

let _67_452 = (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, t) -> begin
(let _165_409 = (let _165_408 = (let _165_407 = (let _165_406 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat break1 _165_406))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_407))
in (FStar_Pprint.op_Hat_Hat break1 _165_408))
in ((pat), (_165_409)))
end
| _67_449 -> begin
((pat), (FStar_Pprint.empty))
end)
in (match (_67_452) with
| (pat, ascr_doc) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _67_457); FStar_Parser_AST.prange = _67_454}, pats) -> begin
(let _165_412 = (p_lident x)
in (let _165_411 = (let _165_410 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Hat _165_410 ascr_doc))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_412 _165_411 FStar_Pprint.equals)))
end
| _67_465 -> begin
(let _165_415 = (let _165_414 = (p_tuplePattern pat)
in (let _165_413 = (FStar_Pprint.op_Hat_Slash_Hat ascr_doc FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _165_414 _165_413)))
in (FStar_Pprint.group _165_415))
end)
end))
in (let _165_416 = (p_term e)
in (prefix2 pat_doc _165_416)))
end))
and p_newEffect : FStar_Parser_AST.effect_decl  ->  FStar_Pprint.document = (fun _67_8 -> (match (_67_8) with
| FStar_Parser_AST.RedefineEffect (lid, bs, t) -> begin
(p_effectRedefinition lid bs t)
end
| FStar_Parser_AST.DefineEffect (lid, bs, t, eff_decls, action_decls) -> begin
(p_effectDefinition lid bs t eff_decls action_decls)
end))
and p_effectRedefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun uid bs t -> (let _165_424 = (p_uident uid)
in (let _165_423 = (p_binders bs)
in (let _165_422 = (let _165_421 = (p_simpleTerm t)
in (prefix2 FStar_Pprint.equals _165_421))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_424 _165_423 _165_422)))))
and p_effectDefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun uid bs t eff_decls action_decls -> (let _165_441 = (let _165_440 = (let _165_434 = (let _165_433 = (p_uident uid)
in (let _165_432 = (p_binders bs)
in (let _165_431 = (let _165_430 = (p_typ t)
in (prefix2 FStar_Pprint.colon _165_430))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_433 _165_432 _165_431))))
in (FStar_Pprint.group _165_434))
in (let _165_439 = (let _165_438 = (let _165_436 = (str "with")
in (let _165_435 = (separate_break_map FStar_Pprint.semi p_effectDecl eff_decls)
in (prefix2 _165_436 _165_435)))
in (let _165_437 = (p_actionDecls action_decls)
in (FStar_Pprint.op_Hat_Hat _165_438 _165_437)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_440 _165_439)))
in (braces_with_nesting _165_441)))
and p_actionDecls : FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun _67_9 -> (match (_67_9) with
| [] -> begin
FStar_Pprint.empty
end
| l -> begin
(let _165_445 = (let _165_444 = (str "and actions")
in (let _165_443 = (separate_break_map FStar_Pprint.semi p_effectDecl l)
in (prefix2 _165_444 _165_443)))
in (FStar_Pprint.op_Hat_Hat break1 _165_445))
end))
and p_effectDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon ([], ((FStar_Parser_AST.TyconAbbrev (lid, [], None, e), None))::[]) -> begin
(let _165_450 = (let _165_448 = (p_lident lid)
in (let _165_447 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _165_448 _165_447)))
in (let _165_449 = (p_simpleTerm e)
in (prefix2 _165_450 _165_449)))
end
| _67_505 -> begin
(let _165_452 = (let _165_451 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "Not a declaration of an effect member... or at least I hope so : %s" _165_451))
in (FStar_All.failwith _165_452))
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

let p_lift = (fun _67_519 -> (match (_67_519) with
| (kwd, t) -> begin
(let _165_459 = (let _165_457 = (str kwd)
in (let _165_456 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _165_457 _165_456)))
in (let _165_458 = (p_simpleTerm t)
in (prefix2 _165_459 _165_458)))
end))
in (separate_break_map FStar_Pprint.semi p_lift lifts)))
in (let _165_467 = (let _165_464 = (let _165_462 = (p_quident lift.FStar_Parser_AST.msource)
in (let _165_461 = (let _165_460 = (str "~>")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_460))
in (FStar_Pprint.op_Hat_Hat _165_462 _165_461)))
in (let _165_463 = (p_quident lift.FStar_Parser_AST.mdest)
in (prefix2 _165_464 _165_463)))
in (let _165_466 = (let _165_465 = (braces_with_nesting lift_op_doc)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_465))
in (FStar_Pprint.op_Hat_Hat _165_467 _165_466)))))
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
and p_qualifiers : FStar_Parser_AST.qualifier Prims.list  ->  FStar_Pprint.document = (fun qs -> (let _165_471 = (let _165_470 = (FStar_Pprint.separate_map break1 p_qualifier qs)
in (FStar_Pprint.op_Hat_Hat _165_470 (if (qs = []) then begin
FStar_Pprint.empty
end else begin
FStar_Pprint.space
end)))
in (FStar_Pprint.group _165_471)))
and p_letqualifier : FStar_Parser_AST.let_qualifier  ->  FStar_Pprint.document = (fun _67_11 -> (match (_67_11) with
| FStar_Parser_AST.Rec -> begin
(let _165_473 = (str "rec")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_473))
end
| FStar_Parser_AST.Mutable -> begin
(let _165_474 = (str "mutable")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_474))
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
(let _165_479 = (let _165_478 = (let _165_477 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space)
in (FStar_Pprint.op_Hat_Hat break1 _165_477))
in (FStar_Pprint.separate_map _165_478 p_tuplePattern pats))
in (FStar_Pprint.group _165_479))
end
| _67_553 -> begin
(p_tuplePattern p)
end))
and p_tuplePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTuple (pats, false) -> begin
(let _165_482 = (let _165_481 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map _165_481 p_constructorPattern pats))
in (FStar_Pprint.group _165_482))
end
| _67_560 -> begin
(p_constructorPattern p)
end))
and p_constructorPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (maybe_cons_lid); FStar_Parser_AST.prange = _67_563}, (hd)::(tl)::[]) when (FStar_Ident.lid_equals maybe_cons_lid FStar_Syntax_Const.cons_lid) -> begin
(let _165_486 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon)
in (let _165_485 = (p_constructorPattern hd)
in (let _165_484 = (p_constructorPattern tl)
in (infix2 _165_486 _165_485 _165_484))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (uid); FStar_Parser_AST.prange = _67_573}, pats) -> begin
(let _165_488 = (p_quident uid)
in (let _165_487 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (prefix2 _165_488 _165_487)))
end
| _67_581 -> begin
(p_atomicPattern p)
end))
and p_atomicPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, t) -> begin
(let _165_492 = (let _165_491 = (p_tuplePattern pat)
in (let _165_490 = (p_typ t)
in (infix2 FStar_Pprint.colon _165_491 _165_490)))
in (parens_with_nesting _165_492))
end
| FStar_Parser_AST.PatList (pats) -> begin
(let _165_493 = (separate_break_map FStar_Pprint.semi p_tuplePattern pats)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket _165_493 FStar_Pprint.rbracket))
end
| FStar_Parser_AST.PatRecord (pats) -> begin
(

let p_recordFieldPat = (fun _67_594 -> (match (_67_594) with
| (lid, pat) -> begin
(let _165_497 = (p_qlident lid)
in (let _165_496 = (p_tuplePattern pat)
in (infix2 FStar_Pprint.equals _165_497 _165_496)))
end))
in (let _165_498 = (separate_break_map FStar_Pprint.semi p_recordFieldPat pats)
in (braces_with_nesting _165_498)))
end
| FStar_Parser_AST.PatTuple (pats, true) -> begin
(let _165_501 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (let _165_500 = (separate_break_map FStar_Pprint.comma p_constructorPattern pats)
in (let _165_499 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_501 _165_500 _165_499))))
end
| FStar_Parser_AST.PatTvar (tv, arg_qualifier_opt) -> begin
(

let _67_603 = ()
in (p_tvar tv))
end
| FStar_Parser_AST.PatOp (op) -> begin
(let _165_505 = (let _165_504 = (let _165_503 = (str op)
in (let _165_502 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat _165_503 _165_502)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_504))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_505))
end
| FStar_Parser_AST.PatWild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.PatConst (c) -> begin
(p_constant c)
end
| FStar_Parser_AST.PatVar (lid, aqual) -> begin
(let _165_507 = (FStar_Pprint.optional p_aqual aqual)
in (let _165_506 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat _165_507 _165_506)))
end
| FStar_Parser_AST.PatName (uid) -> begin
(p_quident uid)
end
| FStar_Parser_AST.PatOr (_67_617) -> begin
(FStar_All.failwith "Inner or pattern !")
end
| (FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (_); FStar_Parser_AST.prange = _}, _)) | (FStar_Parser_AST.PatTuple (_, false)) -> begin
(let _165_508 = (p_tuplePattern p)
in (parens_with_nesting _165_508))
end
| _67_635 -> begin
(let _165_510 = (let _165_509 = (FStar_Parser_AST.pat_to_string p)
in (FStar_Util.format1 "Invalid pattern %s" _165_509))
in (FStar_All.failwith _165_510))
end))
and p_binder : FStar_Parser_AST.binder  ->  FStar_Pprint.document = (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (lid) -> begin
(let _165_513 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (let _165_512 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat _165_513 _165_512)))
end
| FStar_Parser_AST.TVariable (lid) -> begin
(p_lident lid)
end
| FStar_Parser_AST.Annotated (lid, t) -> begin
(let _165_520 = (let _165_519 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (let _165_518 = (let _165_517 = (p_lident lid)
in (let _165_516 = (let _165_515 = (let _165_514 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat _165_514 FStar_Pprint.rparen))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_515))
in (FStar_Pprint.op_Hat_Hat _165_517 _165_516)))
in (FStar_Pprint.op_Hat_Hat _165_519 _165_518)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_520))
end
| FStar_Parser_AST.TAnnotated (_67_646) -> begin
(FStar_All.failwith "Is this still used ?")
end
| FStar_Parser_AST.NoName (t) -> begin
(p_atomicTerm t)
end))
and p_binders : FStar_Parser_AST.binder Prims.list  ->  FStar_Pprint.document = (fun bs -> (FStar_Pprint.separate_map break1 p_binder bs))
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
(let _165_533 = (let _165_531 = (let _165_530 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat _165_530 FStar_Pprint.semi))
in (FStar_Pprint.group _165_531))
in (let _165_532 = (p_term e2)
in (FStar_Pprint.op_Hat_Slash_Hat _165_533 _165_532)))
end
| _67_664 -> begin
(let _165_534 = (p_noSeqTerm e)
in (FStar_Pprint.group _165_534))
end))
and p_noSeqTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Ascribed (e, t) -> begin
(let _165_540 = (let _165_539 = (p_tmIff e)
in (let _165_538 = (let _165_537 = (let _165_536 = (p_typ t)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon _165_536))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.langle _165_537))
in (FStar_Pprint.op_Hat_Slash_Hat _165_539 _165_538)))
in (FStar_Pprint.group _165_540))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::(e3)::[]) when (op = ".()<-") -> begin
(let _165_551 = (let _165_550 = (let _165_547 = (let _165_546 = (p_atomicTermNotQUident e1)
in (let _165_545 = (let _165_544 = (let _165_543 = (let _165_541 = (p_term e2)
in (parens_with_nesting _165_541))
in (let _165_542 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat _165_543 _165_542)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_544))
in (FStar_Pprint.op_Hat_Hat _165_546 _165_545)))
in (FStar_Pprint.group _165_547))
in (let _165_549 = (let _165_548 = (p_noSeqTerm e3)
in (jump2 _165_548))
in (FStar_Pprint.op_Hat_Hat _165_550 _165_549)))
in (FStar_Pprint.group _165_551))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::(e3)::[]) when (op = ".[]<-") -> begin
(let _165_562 = (let _165_561 = (let _165_558 = (let _165_557 = (p_atomicTermNotQUident e1)
in (let _165_556 = (let _165_555 = (let _165_554 = (let _165_552 = (p_term e2)
in (brackets_with_nesting _165_552))
in (let _165_553 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat _165_554 _165_553)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_555))
in (FStar_Pprint.op_Hat_Hat _165_557 _165_556)))
in (FStar_Pprint.group _165_558))
in (let _165_560 = (let _165_559 = (p_noSeqTerm e3)
in (jump2 _165_559))
in (FStar_Pprint.op_Hat_Hat _165_561 _165_560)))
in (FStar_Pprint.group _165_562))
end
| FStar_Parser_AST.Requires (e, wtf) -> begin
(

let _67_688 = ()
in (let _165_565 = (let _165_564 = (str "requires")
in (let _165_563 = (p_typ e)
in (FStar_Pprint.op_Hat_Slash_Hat _165_564 _165_563)))
in (FStar_Pprint.group _165_565)))
end
| FStar_Parser_AST.Ensures (e, wtf) -> begin
(

let _67_694 = ()
in (let _165_568 = (let _165_567 = (str "ensures")
in (let _165_566 = (p_typ e)
in (FStar_Pprint.op_Hat_Slash_Hat _165_567 _165_566)))
in (FStar_Pprint.group _165_568)))
end
| FStar_Parser_AST.Attributes (es) -> begin
(let _165_571 = (let _165_570 = (str "attributes")
in (let _165_569 = (FStar_Pprint.separate_map break1 p_atomicTerm es)
in (FStar_Pprint.op_Hat_Slash_Hat _165_570 _165_569)))
in (FStar_Pprint.group _165_571))
end
| FStar_Parser_AST.If (e1, e2, e3) -> begin
if (is_unit e3) then begin
(let _165_578 = (let _165_577 = (let _165_573 = (str "if")
in (let _165_572 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat _165_573 _165_572)))
in (let _165_576 = (let _165_575 = (str "then")
in (let _165_574 = (p_noSeqTerm e2)
in (op_Hat_Slash_Plus_Hat _165_575 _165_574)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_577 _165_576)))
in (FStar_Pprint.group _165_578))
end else begin
(

let e2_doc = (match (e2.FStar_Parser_AST.tm) with
| FStar_Parser_AST.If (_67_704, _67_706, e3) when (is_unit e3) -> begin
(let _165_579 = (p_noSeqTerm e2)
in (parens_with_nesting _165_579))
end
| _67_711 -> begin
(p_noSeqTerm e2)
end)
in (let _165_589 = (let _165_588 = (let _165_581 = (str "if")
in (let _165_580 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat _165_581 _165_580)))
in (let _165_587 = (let _165_586 = (let _165_582 = (str "then")
in (op_Hat_Slash_Plus_Hat _165_582 e2_doc))
in (let _165_585 = (let _165_584 = (str "else")
in (let _165_583 = (p_noSeqTerm e3)
in (op_Hat_Slash_Plus_Hat _165_584 _165_583)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_586 _165_585)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_588 _165_587)))
in (FStar_Pprint.group _165_589)))
end
end
| FStar_Parser_AST.TryWith (e, branches) -> begin
(let _165_597 = (let _165_596 = (let _165_591 = (str "try")
in (let _165_590 = (p_noSeqTerm e)
in (prefix2 _165_591 _165_590)))
in (let _165_595 = (let _165_594 = (str "with")
in (let _165_593 = (let _165_592 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (jump2 _165_592))
in (FStar_Pprint.op_Hat_Hat _165_594 _165_593)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_596 _165_595)))
in (FStar_Pprint.group _165_597))
end
| FStar_Parser_AST.Match (e, branches) -> begin
(let _165_604 = (let _165_603 = (let _165_600 = (str "match")
in (let _165_599 = (p_noSeqTerm e)
in (let _165_598 = (str "with")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_600 _165_599 _165_598))))
in (let _165_602 = (let _165_601 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (jump2 _165_601))
in (FStar_Pprint.op_Hat_Hat _165_603 _165_602)))
in (FStar_Pprint.group _165_604))
end
| FStar_Parser_AST.LetOpen (uid, e) -> begin
(let _165_610 = (let _165_609 = (let _165_607 = (str "let open")
in (let _165_606 = (p_quident uid)
in (let _165_605 = (str "in")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_607 _165_606 _165_605))))
in (let _165_608 = (p_term e)
in (FStar_Pprint.op_Hat_Slash_Hat _165_609 _165_608)))
in (FStar_Pprint.group _165_610))
end
| FStar_Parser_AST.Let (q, lbs, e) -> begin
(

let let_doc = (let _165_612 = (str "let")
in (let _165_611 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat _165_612 _165_611)))
in (let _165_617 = (let _165_613 = (str "and")
in (precede_break_separate_map let_doc _165_613 p_letbinding lbs))
in (let _165_616 = (let _165_615 = (str "in")
in (let _165_614 = (p_term e)
in (prefix2 _165_615 _165_614)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_617 _165_616))))
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, typ_opt); FStar_Parser_AST.prange = _67_732})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, branches); FStar_Parser_AST.range = _67_742; FStar_Parser_AST.level = _67_740}) when (matches_var maybe_x x) -> begin
(let _165_619 = (str "function")
in (let _165_618 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (op_Hat_Slash_Plus_Hat _165_619 _165_618)))
end
| FStar_Parser_AST.Assign (id, e) -> begin
(let _165_623 = (let _165_622 = (p_lident id)
in (let _165_621 = (let _165_620 = (p_noSeqTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow _165_620))
in (FStar_Pprint.op_Hat_Slash_Hat _165_622 _165_621)))
in (FStar_Pprint.group _165_623))
end
| _67_755 -> begin
(p_typ e)
end))
and p_typ : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| (FStar_Parser_AST.QForall (bs, trigger, e1)) | (FStar_Parser_AST.QExists (bs, trigger, e1)) -> begin
(let _165_630 = (let _165_626 = (p_quantifier e)
in (let _165_625 = (p_binders bs)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_626 _165_625 FStar_Pprint.dot)))
in (let _165_629 = (let _165_628 = (p_trigger trigger)
in (let _165_627 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Slash_Hat _165_628 _165_627)))
in (prefix2 _165_630 _165_629)))
end
| _67_765 -> begin
(p_simpleTerm e)
end))
and p_quantifier : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.QForall (_67_768) -> begin
(str "forall")
end
| FStar_Parser_AST.QExists (_67_771) -> begin
(str "exists")
end
| _67_774 -> begin
(FStar_All.failwith "Imposible : p_quantifier called on a non-quantifier term")
end))
and p_trigger : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun _67_13 -> (match (_67_13) with
| [] -> begin
FStar_Pprint.empty
end
| pats -> begin
(let _165_638 = (let _165_637 = (let _165_636 = (str "pattern")
in (let _165_635 = (let _165_634 = (let _165_633 = (p_disjunctivePats pats)
in (jump2 _165_633))
in (FStar_Pprint.op_Hat_Slash_Hat _165_634 FStar_Pprint.rbrace))
in (FStar_Pprint.op_Hat_Slash_Hat _165_636 _165_635)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_637))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace _165_638))
end))
and p_disjunctivePats : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun pats -> (let _165_640 = (str "\\/")
in (FStar_Pprint.separate_map _165_640 p_conjunctivePats pats)))
and p_conjunctivePats : FStar_Parser_AST.term Prims.list  ->  FStar_Pprint.document = (fun pats -> (let _165_642 = (FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats)
in (FStar_Pprint.group _165_642)))
and p_simpleTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Abs (pats, e) -> begin
(let _165_648 = (let _165_646 = (str "fun")
in (let _165_645 = (let _165_644 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Slash_Hat _165_644 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat _165_646 _165_645)))
in (let _165_647 = (p_term e)
in (op_Hat_Slash_Plus_Hat _165_648 _165_647)))
end
| _67_786 -> begin
(p_tmIff e)
end))
and p_maybeFocusArrow : Prims.bool  ->  FStar_Pprint.document = (fun b -> if b then begin
(str "~>")
end else begin
FStar_Pprint.rarrow
end)
and p_patternBranch : FStar_Parser_AST.branch  ->  FStar_Pprint.document = (fun _67_791 -> (match (_67_791) with
| (pat, when_opt, e) -> begin
(let _165_659 = (let _165_658 = (let _165_656 = (let _165_655 = (let _165_654 = (let _165_653 = (p_disjunctivePattern pat)
in (let _165_652 = (let _165_651 = (p_maybeWhen when_opt)
in (FStar_Pprint.op_Hat_Hat _165_651 FStar_Pprint.rarrow))
in (FStar_Pprint.op_Hat_Slash_Hat _165_653 _165_652)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_654))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar _165_655))
in (FStar_Pprint.group _165_656))
in (let _165_657 = (p_term e)
in (op_Hat_Slash_Plus_Hat _165_658 _165_657)))
in (FStar_Pprint.group _165_659))
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
| _67_804 -> begin
(p_tmImplies e)
end))
and p_tmImplies : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("==>", (e1)::(e2)::[]) -> begin
(let _165_671 = (str "==>")
in (let _165_670 = (p_tmArrow p_tmFormula e1)
in (let _165_669 = (p_tmImplies e2)
in (infix2 _165_671 _165_670 _165_669))))
end
| _67_813 -> begin
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
| _67_822 -> begin
(p_Tm e)
end))
and p_tmFormula : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("\\/", (e1)::(e2)::[]) -> begin
(let _165_687 = (str "\\/")
in (let _165_686 = (p_tmFormula e1)
in (let _165_685 = (p_tmConjunction e2)
in (infix2 _165_687 _165_686 _165_685))))
end
| _67_831 -> begin
(p_tmConjunction e)
end))
and p_tmConjunction : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("/\\", (e1)::(e2)::[]) -> begin
(let _165_691 = (str "/\\")
in (let _165_690 = (p_tmConjunction e1)
in (let _165_689 = (p_tmTuple e2)
in (infix2 _165_691 _165_690 _165_689))))
end
| _67_840 -> begin
(p_tmTuple e)
end))
and p_tmTuple : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (lid, args) when (is_tuple_constructor lid) -> begin
(let _165_694 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map _165_694 (fun _67_849 -> (match (_67_849) with
| (e, _67_848) -> begin
(p_tmEq e)
end)) args))
end
| _67_851 -> begin
(p_tmEq e)
end))
and paren_if : Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun curr mine doc -> if (mine <= curr) then begin
doc
end else begin
(let _165_699 = (let _165_698 = (FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_698))
in (FStar_Pprint.group _165_699))
end)
and p_tmEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n = (max_level (FStar_List.append ((colon_equals)::(pipe_right)::[]) operatorInfix0ad12))
in (p_tmEq' n e)))
and p_tmEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (((is_operatorInfix0ad12 op) || (op = "=")) || (op = "|>")) -> begin
(

let _67_868 = (levels op)
in (match (_67_868) with
| (left, mine, right) -> begin
(let _165_706 = (let _165_705 = (str op)
in (let _165_704 = (p_tmEq' left e1)
in (let _165_703 = (p_tmEq' right e2)
in (infix2 _165_705 _165_704 _165_703))))
in (paren_if curr mine _165_706))
end))
end
| FStar_Parser_AST.Op (":=", (e1)::(e2)::[]) -> begin
(let _165_712 = (let _165_711 = (p_tmEq e1)
in (let _165_710 = (let _165_709 = (let _165_708 = (let _165_707 = (p_tmEq e2)
in (op_Hat_Slash_Plus_Hat FStar_Pprint.equals _165_707))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_708))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_709))
in (FStar_Pprint.op_Hat_Hat _165_711 _165_710)))
in (FStar_Pprint.group _165_712))
end
| _67_876 -> begin
(p_tmNoEq e)
end))
and p_tmNoEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n = (max_level ((colon_colon)::(amp)::(opinfix3)::(opinfix4)::[]))
in (p_tmNoEq' n e)))
and p_tmNoEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (lid, ((e1, _67_888))::((e2, _67_884))::[]) when ((FStar_Ident.lid_equals lid FStar_Syntax_Const.cons_lid) && (not ((is_list e)))) -> begin
(

let op = "::"
in (

let _67_897 = (levels op)
in (match (_67_897) with
| (left, mine, right) -> begin
(let _165_719 = (let _165_718 = (str op)
in (let _165_717 = (p_tmNoEq' left e1)
in (let _165_716 = (p_tmNoEq' right e2)
in (infix2 _165_718 _165_717 _165_716))))
in (paren_if curr mine _165_719))
end)))
end
| FStar_Parser_AST.Sum (binders, res) -> begin
(

let op = "&"
in (

let _67_906 = (levels op)
in (match (_67_906) with
| (left, mine, right) -> begin
(

let p_dsumfst = (fun b -> (let _165_725 = (p_binder b)
in (let _165_724 = (let _165_723 = (let _165_722 = (str "&")
in (FStar_Pprint.op_Hat_Hat _165_722 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_723))
in (FStar_Pprint.op_Hat_Hat _165_725 _165_724))))
in (let _165_728 = (let _165_727 = (FStar_Pprint.concat_map p_dsumfst binders)
in (let _165_726 = (p_tmNoEq' right res)
in (FStar_Pprint.op_Hat_Hat _165_727 _165_726)))
in (paren_if curr mine _165_728)))
end)))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (is_operatorInfix34 op) -> begin
(

let _67_918 = (levels op)
in (match (_67_918) with
| (left, mine, right) -> begin
(let _165_732 = (let _165_731 = (str op)
in (let _165_730 = (p_tmNoEq' left e1)
in (let _165_729 = (p_tmNoEq' right e2)
in (infix2 _165_731 _165_730 _165_729))))
in (paren_if curr mine _165_732))
end))
end
| FStar_Parser_AST.Op ("-", (e)::[]) -> begin
(

let _67_927 = (levels "-")
in (match (_67_927) with
| (left, mine, right) -> begin
(let _165_733 = (p_tmNoEq' mine e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus _165_733))
end))
end
| FStar_Parser_AST.NamedTyp (lid, e) -> begin
(let _165_737 = (let _165_736 = (p_lidentOrUnderscore lid)
in (let _165_735 = (let _165_734 = (p_appTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon _165_734))
in (FStar_Pprint.op_Hat_Slash_Hat _165_736 _165_735)))
in (FStar_Pprint.group _165_737))
end
| FStar_Parser_AST.Refine (b, phi) -> begin
(p_refinedBinder b phi)
end
| FStar_Parser_AST.Record (with_opt, record_fields) -> begin
(let _165_740 = (let _165_739 = (default_or_map FStar_Pprint.empty p_with_clause with_opt)
in (let _165_738 = (FStar_Pprint.separate_map FStar_Pprint.semi p_simpleDef record_fields)
in (FStar_Pprint.op_Hat_Hat _165_739 _165_738)))
in (braces_with_nesting _165_740))
end
| FStar_Parser_AST.Op ("~", (e)::[]) -> begin
(let _165_743 = (let _165_742 = (str "~")
in (let _165_741 = (p_atomicTerm e)
in (FStar_Pprint.op_Hat_Hat _165_742 _165_741)))
in (FStar_Pprint.group _165_743))
end
| _67_946 -> begin
(p_appTerm e)
end))
and p_with_clause : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (let _165_748 = (p_appTerm e)
in (let _165_747 = (let _165_746 = (let _165_745 = (str "with")
in (FStar_Pprint.op_Hat_Hat _165_745 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_746))
in (FStar_Pprint.op_Hat_Hat _165_748 _165_747))))
and p_refinedBinder : FStar_Parser_AST.binder  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun b phi -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (lid, t) -> begin
(let _165_758 = (let _165_757 = (p_lident lid)
in (let _165_756 = (let _165_755 = (let _165_754 = (p_typ t)
in (let _165_753 = (let _165_752 = (let _165_751 = (p_term phi)
in (braces_with_nesting _165_751))
in (FStar_Pprint.op_Hat_Hat _165_752 FStar_Pprint.rparen))
in (FStar_Pprint.op_Hat_Hat _165_754 _165_753)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_755))
in (FStar_Pprint.op_Hat_Hat _165_757 _165_756)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_758))
end
| FStar_Parser_AST.TAnnotated (_67_955) -> begin
(FStar_All.failwith "Is this still used ?")
end
| (FStar_Parser_AST.Variable (_)) | (FStar_Parser_AST.TVariable (_)) | (FStar_Parser_AST.NoName (_)) -> begin
(let _165_760 = (let _165_759 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" _165_759))
in (FStar_All.failwith _165_760))
end))
and p_simpleDef : (FStar_Ident.lid * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun _67_968 -> (match (_67_968) with
| (lid, e) -> begin
(let _165_765 = (let _165_764 = (p_qlident lid)
in (let _165_763 = (let _165_762 = (p_simpleTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals _165_762))
in (FStar_Pprint.op_Hat_Slash_Hat _165_764 _165_763)))
in (FStar_Pprint.group _165_765))
end))
and p_appTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App (_67_971) when (is_general_application e) -> begin
(

let _67_975 = (head_and_args e)
in (match (_67_975) with
| (head, args) -> begin
(let _165_768 = (p_indexingTerm head)
in (let _165_767 = (FStar_Pprint.separate_map FStar_Pprint.space p_argTerm args)
in (op_Hat_Slash_Plus_Hat _165_768 _165_767)))
end))
end
| FStar_Parser_AST.Construct (lid, args) when ((is_general_construction e) && (not ((is_dtuple_constructor lid)))) -> begin
if (args = []) then begin
(p_quident lid)
end else begin
(let _165_770 = (p_quident lid)
in (let _165_769 = (FStar_Pprint.separate_map break1 p_argTerm args)
in (op_Hat_Slash_Plus_Hat _165_770 _165_769)))
end
end
| _67_981 -> begin
(p_indexingTerm e)
end))
and p_argTerm : (FStar_Parser_AST.term * FStar_Parser_AST.imp)  ->  FStar_Pprint.document = (fun arg_imp -> (match (arg_imp) with
| ({FStar_Parser_AST.tm = FStar_Parser_AST.Uvar (_67_988); FStar_Parser_AST.range = _67_986; FStar_Parser_AST.level = _67_984}, FStar_Parser_AST.UnivApp) -> begin
(p_univar (Prims.fst arg_imp))
end
| (u, FStar_Parser_AST.UnivApp) -> begin
(p_universe u)
end
| (e, FStar_Parser_AST.FsTypApp) -> begin
(let _165_772 = (p_indexingTerm e)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.langle _165_772 FStar_Pprint.rangle))
end
| (e, FStar_Parser_AST.Hash) -> begin
(let _165_774 = (str "#")
in (let _165_773 = (p_indexingTerm e)
in (FStar_Pprint.op_Hat_Hat _165_774 _165_773)))
end
| (e, FStar_Parser_AST.Nothing) -> begin
(p_indexingTerm e)
end))
and p_indexingTerm_aux : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun exit e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op (".()", (e1)::(e2)::[]) -> begin
(let _165_784 = (let _165_783 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (let _165_782 = (let _165_781 = (let _165_780 = (p_term e2)
in (parens_with_nesting _165_780))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_781))
in (FStar_Pprint.op_Hat_Hat _165_783 _165_782)))
in (FStar_Pprint.group _165_784))
end
| FStar_Parser_AST.Op (".[]", (e1)::(e2)::[]) -> begin
(let _165_789 = (let _165_788 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (let _165_787 = (let _165_786 = (let _165_785 = (p_term e2)
in (brackets_with_nesting _165_785))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_786))
in (FStar_Pprint.op_Hat_Hat _165_788 _165_787)))
in (FStar_Pprint.group _165_789))
end
| _67_1020 -> begin
(exit e)
end))
and p_indexingTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_indexingTerm_aux p_atomicTerm e))
and p_atomicTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.LetOpen (lid, e) -> begin
(let _165_795 = (p_quident lid)
in (let _165_794 = (let _165_793 = (let _165_792 = (p_term e)
in (parens_with_nesting _165_792))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_793))
in (FStar_Pprint.op_Hat_Hat _165_795 _165_794)))
end
| FStar_Parser_AST.Name (lid) -> begin
(p_quident lid)
end
| FStar_Parser_AST.Op (op, (e)::[]) -> begin
(let _165_797 = (str op)
in (let _165_796 = (p_atomicTerm e)
in (FStar_Pprint.op_Hat_Hat _165_797 _165_796)))
end
| _67_1035 -> begin
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
(let _165_800 = (str op)
in (let _165_799 = (p_atomicTermNotQUident e)
in (FStar_Pprint.op_Hat_Hat _165_800 _165_799)))
end
| FStar_Parser_AST.Op (op, []) -> begin
(let _165_804 = (let _165_803 = (let _165_802 = (str op)
in (let _165_801 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat _165_802 _165_801)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_803))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_804))
end
| FStar_Parser_AST.Construct (lid, args) when (is_dtuple_constructor lid) -> begin
(let _165_809 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (let _165_808 = (let _165_806 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (let _165_805 = (FStar_List.map Prims.fst args)
in (FStar_Pprint.separate_map _165_806 p_tmEq _165_805)))
in (let _165_807 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_809 _165_808 _165_807))))
end
| FStar_Parser_AST.Project (e, lid) -> begin
(let _165_813 = (let _165_812 = (p_atomicTermNotQUident e)
in (let _165_811 = (let _165_810 = (p_qlident lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_810))
in (FStar_Pprint.op_Hat_Slash_Hat _165_812 _165_811)))
in (FStar_Pprint.group _165_813))
end
| _67_1066 -> begin
(p_projectionLHS e)
end))
and p_projectionLHS : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (lid) -> begin
(p_qlident lid)
end
| FStar_Parser_AST.Projector (constr_lid, field_lid) -> begin
(let _165_818 = (p_quident constr_lid)
in (let _165_817 = (let _165_816 = (let _165_815 = (p_lident field_lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_815))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark _165_816))
in (FStar_Pprint.op_Hat_Hat _165_818 _165_817)))
end
| FStar_Parser_AST.Discrim (constr_lid) -> begin
(let _165_819 = (p_quident constr_lid)
in (FStar_Pprint.op_Hat_Hat _165_819 FStar_Pprint.qmark))
end
| FStar_Parser_AST.Paren (e) -> begin
(let _165_820 = (p_term e)
in (parens_with_nesting _165_820))
end
| _67_1079 when (is_array e) -> begin
(

let es = (extract_from_list e)
in (let _165_823 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar)
in (let _165_822 = (separate_map_or_flow FStar_Pprint.semi p_noSeqTerm es)
in (let _165_821 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") _165_823 _165_822 _165_821)))))
end
| _67_1082 when (is_list e) -> begin
(let _165_825 = (let _165_824 = (extract_from_list e)
in (separate_map_or_flow FStar_Pprint.semi p_noSeqTerm _165_824))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket _165_825 FStar_Pprint.rbracket))
end
| _67_1084 when (is_lex_list e) -> begin
(let _165_828 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket)
in (let _165_827 = (let _165_826 = (extract_from_list e)
in (separate_map_or_flow FStar_Pprint.semi p_noSeqTerm _165_826))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_828 _165_827 FStar_Pprint.rbracket)))
end
| _67_1086 when (is_ref_set e) -> begin
(

let es = (extract_from_ref_set e)
in (let _165_830 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace)
in (let _165_829 = (separate_map_or_flow FStar_Pprint.comma p_appTerm es)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") _165_830 _165_829 FStar_Pprint.rbrace))))
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Op (_)) | (FStar_Parser_AST.Tvar (_)) | (FStar_Parser_AST.Uvar (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) | (FStar_Parser_AST.Construct (_)) | (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.App (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.LetOpen (_)) | (FStar_Parser_AST.Seq (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Ascribed (_)) | (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Project (_)) | (FStar_Parser_AST.Product (_)) | (FStar_Parser_AST.Sum (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Refine (_)) | (FStar_Parser_AST.NamedTyp (_)) | (FStar_Parser_AST.Requires (_)) | (FStar_Parser_AST.Ensures (_)) | (FStar_Parser_AST.Assign (_)) | (FStar_Parser_AST.Attributes (_)) -> begin
(let _165_831 = (p_term e)
in (parens_with_nesting _165_831))
end
| FStar_Parser_AST.Labeled (_67_1174) -> begin
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
(let _165_833 = (FStar_Pprint.doc_of_char x)
in (FStar_Pprint.squotes _165_833))
end
| FStar_Const.Const_string (bytes, _67_1187) -> begin
(let _165_834 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes _165_834))
end
| FStar_Const.Const_bytearray (bytes, _67_1192) -> begin
(let _165_837 = (let _165_835 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes _165_835))
in (let _165_836 = (str "B")
in (FStar_Pprint.op_Hat_Hat _165_837 _165_836)))
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

let ending = (default_or_map FStar_Pprint.empty (fun _67_1211 -> (match (_67_1211) with
| (s, w) -> begin
(let _165_844 = (signedness s)
in (let _165_843 = (width w)
in (FStar_Pprint.op_Hat_Hat _165_844 _165_843)))
end)) sign_width_opt)
in (let _165_845 = (str repr)
in (FStar_Pprint.op_Hat_Hat _165_845 ending)))))
end
| FStar_Const.Const_range (r) -> begin
(let _165_846 = (FStar_Range.string_of_range r)
in (str _165_846))
end
| FStar_Const.Const_reify -> begin
(str "reify")
end
| FStar_Const.Const_reflect (lid) -> begin
(let _165_850 = (p_quident lid)
in (let _165_849 = (let _165_848 = (let _165_847 = (str "reflect")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_847))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark _165_848))
in (FStar_Pprint.op_Hat_Hat _165_850 _165_849)))
end))
and p_universe : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (let _165_853 = (str "u#")
in (let _165_852 = (p_atomicUniverse u)
in (FStar_Pprint.op_Hat_Hat _165_853 _165_852))))
and p_universeFrom : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match (u.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("+", (u1)::(u2)::[]) -> begin
(let _165_858 = (let _165_857 = (p_universeFrom u1)
in (let _165_856 = (let _165_855 = (p_universeFrom u2)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus _165_855))
in (FStar_Pprint.op_Hat_Slash_Hat _165_857 _165_856)))
in (FStar_Pprint.group _165_858))
end
| FStar_Parser_AST.App (_67_1227) -> begin
(

let _67_1231 = (head_and_args u)
in (match (_67_1231) with
| (head, args) -> begin
(match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (maybe_max_lid) when (FStar_Ident.lid_equals maybe_max_lid FStar_Syntax_Const.max_lid) -> begin
(let _165_862 = (let _165_861 = (p_qlident FStar_Syntax_Const.max_lid)
in (let _165_860 = (FStar_Pprint.separate_map FStar_Pprint.space (fun _67_1237 -> (match (_67_1237) with
| (u, _67_1236) -> begin
(p_atomicUniverse u)
end)) args)
in (op_Hat_Slash_Plus_Hat _165_861 _165_860)))
in (FStar_Pprint.group _165_862))
end
| _67_1239 -> begin
(let _165_864 = (let _165_863 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" _165_863))
in (FStar_All.failwith _165_864))
end)
end))
end
| _67_1241 -> begin
(p_atomicUniverse u)
end))
and p_atomicUniverse : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match (u.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Wild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (r, sw)) -> begin
(p_constant (FStar_Const.Const_int (((r), (sw)))))
end
| FStar_Parser_AST.Uvar (_67_1250) -> begin
(p_univar u)
end
| FStar_Parser_AST.Paren (u) -> begin
(let _165_866 = (p_universeFrom u)
in (parens_with_nesting _165_866))
end
| (FStar_Parser_AST.Op ("+", (_)::(_)::[])) | (FStar_Parser_AST.App (_)) -> begin
(let _165_867 = (p_universeFrom u)
in (parens_with_nesting _165_867))
end
| _67_1266 -> begin
(let _165_869 = (let _165_868 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" _165_868))
in (FStar_All.failwith _165_869))
end))
and p_univar : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match (u.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Uvar (id) -> begin
(str (FStar_Ident.text_of_id id))
end
| _67_1271 -> begin
(let _165_872 = (let _165_871 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Not a universe variable %s" _165_871))
in (FStar_All.failwith _165_872))
end))


let term_to_document : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_term e))


let decl_to_document : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun e -> (p_decl e))


let modul_to_document : FStar_Parser_AST.modul  ->  FStar_Pprint.document = (fun m -> (match (m) with
| (FStar_Parser_AST.Module (_, decls)) | (FStar_Parser_AST.Interface (_, decls, _)) -> begin
(let _165_879 = (FStar_All.pipe_right decls (FStar_List.map decl_to_document))
in (FStar_All.pipe_right _165_879 (FStar_Pprint.separate FStar_Pprint.hardline)))
end))




