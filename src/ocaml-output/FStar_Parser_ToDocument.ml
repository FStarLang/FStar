
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


let doc_of_fsdoc : (Prims.string * (Prims.string * Prims.string) Prims.list)  ->  FStar_Pprint.document = (fun _67_51 -> (match (_67_51) with
| (comment, keywords) -> begin
(let _165_81 = (let _165_80 = (let _165_79 = (str comment)
in (let _165_78 = (let _165_77 = (let _165_76 = (FStar_Pprint.separate_map FStar_Pprint.comma (fun _67_54 -> (match (_67_54) with
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
| _67_59 -> begin
false
end))


let matches_var : FStar_Parser_AST.term  ->  FStar_Ident.ident  ->  Prims.bool = (fun t x -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (y) -> begin
(x.FStar_Ident.idText = (FStar_Ident.text_of_lid y))
end
| _67_65 -> begin
false
end))


let is_tuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Syntax_Util.is_tuple_data_lid'


let is_dtuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Syntax_Util.is_dtuple_data_lid'


let is_list_structure : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun cons_lid nil_lid -> (

let rec aux = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (lid, []) -> begin
(FStar_Ident.lid_equals lid nil_lid)
end
| FStar_Parser_AST.Construct (lid, (_67_80)::((e2, _67_77))::[]) -> begin
((FStar_Ident.lid_equals lid cons_lid) && (aux e2))
end
| _67_85 -> begin
false
end))
in aux))


let is_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Syntax_Const.cons_lid FStar_Syntax_Const.nil_lid)


let is_lex_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Syntax_Const.lexcons_lid FStar_Syntax_Const.lextop_lid)


let rec extract_from_list : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (_67_88, []) -> begin
[]
end
| FStar_Parser_AST.Construct (_67_93, ((e1, FStar_Parser_AST.Nothing))::((e2, FStar_Parser_AST.Nothing))::[]) -> begin
(let _165_104 = (extract_from_list e2)
in (e1)::_165_104)
end
| _67_104 -> begin
(let _165_106 = (let _165_105 = (FStar_Parser_AST.term_to_string e)
in (FStar_Util.format1 "Not a list %s" _165_105))
in (FStar_All.failwith _165_106))
end))


let is_array : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (lid); FStar_Parser_AST.range = _67_109; FStar_Parser_AST.level = _67_107}, l, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals lid FStar_Syntax_Const.array_mk_array_lid) && (is_list l))
end
| _67_118 -> begin
false
end))


let rec is_ref_set : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (maybe_empty_lid) -> begin
(FStar_Ident.lid_equals maybe_empty_lid FStar_Syntax_Const.tset_empty)
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_singleton_lid); FStar_Parser_AST.range = _67_125; FStar_Parser_AST.level = _67_123}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_ref_lid); FStar_Parser_AST.range = _67_136; FStar_Parser_AST.level = _67_134}, e, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = _67_132; FStar_Parser_AST.level = _67_130}, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals maybe_singleton_lid FStar_Syntax_Const.tset_singleton) && (FStar_Ident.lid_equals maybe_ref_lid FStar_Syntax_Const.heap_ref))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_union_lid); FStar_Parser_AST.range = _67_155; FStar_Parser_AST.level = _67_153}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = _67_151; FStar_Parser_AST.level = _67_149}, e2, FStar_Parser_AST.Nothing) -> begin
(((FStar_Ident.lid_equals maybe_union_lid FStar_Syntax_Const.tset_union) && (is_ref_set e1)) && (is_ref_set e2))
end
| _67_169 -> begin
false
end))


let rec extract_from_ref_set : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (_67_172) -> begin
[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (_67_179); FStar_Parser_AST.range = _67_177; FStar_Parser_AST.level = _67_175}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (_67_191); FStar_Parser_AST.range = _67_189; FStar_Parser_AST.level = _67_187}, e, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = _67_185; FStar_Parser_AST.level = _67_183}, FStar_Parser_AST.Nothing) -> begin
(e)::[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (_67_211); FStar_Parser_AST.range = _67_209; FStar_Parser_AST.level = _67_207}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = _67_205; FStar_Parser_AST.level = _67_203}, e2, FStar_Parser_AST.Nothing) -> begin
(let _165_114 = (extract_from_ref_set e1)
in (let _165_113 = (extract_from_ref_set e2)
in (FStar_List.append _165_114 _165_113)))
end
| _67_224 -> begin
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
| _67_237 -> begin
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


let matches_level = (fun s _67_252 -> (match (_67_252) with
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
in (FStar_List.mapi (fun i _67_262 -> (match (_67_262) with
| (assoc, tokens) -> begin
(((levels_from_associativity i assoc)), (tokens))
end)) level_associativity_spec))


let assign_levels : associativity_level Prims.list  ->  Prims.string  ->  (Prims.int * Prims.int * Prims.int) = (fun token_associativity_spec s -> (match ((FStar_List.tryFind (matches_level s) level_table)) with
| Some (assoc_levels, _67_267) -> begin
assoc_levels
end
| _67_271 -> begin
(FStar_All.failwith (Prims.strcat "Unrecognized operator " s))
end))


let max : Prims.int  ->  Prims.int  ->  Prims.int = (fun k1 k2 -> if (k1 > k2) then begin
k1
end else begin
k2
end)


let max_level = (fun l -> (

let find_level_and_max = (fun n level -> (match ((FStar_List.tryFind (fun _67_281 -> (match (_67_281) with
| (_67_279, tokens) -> begin
(tokens = (Prims.snd level))
end)) level_table)) with
| Some ((_67_283, l, _67_286), _67_289) -> begin
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


let rec p_decl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (let _165_265 = (FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc)
in (let _165_264 = (p_decl2 d)
in (FStar_Pprint.op_Hat_Hat _165_265 _165_264))))
and p_fsdoc : FStar_Parser_AST.fsdoc  ->  FStar_Pprint.document = (fun _67_308 -> (match (_67_308) with
| (doc, kwd_args) -> begin
(

let kwd_args_doc = (match (kwd_args) with
| [] -> begin
FStar_Pprint.empty
end
| kwd_args -> begin
(

let process_kwd_arg = (fun _67_314 -> (match (_67_314) with
| (kwd, arg) -> begin
(let _165_273 = (str "@")
in (let _165_272 = (let _165_271 = (str kwd)
in (let _165_270 = (let _165_269 = (str arg)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_269))
in (FStar_Pprint.op_Hat_Hat _165_271 _165_270)))
in (FStar_Pprint.op_Hat_Hat _165_273 _165_272)))
end))
in (let _165_275 = (let _165_274 = (FStar_Pprint.separate_map FStar_Pprint.hardline process_kwd_arg kwd_args)
in (FStar_Pprint.op_Hat_Hat _165_274 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline _165_275)))
end)
in (let _165_283 = (let _165_282 = (let _165_281 = (let _165_280 = (let _165_279 = (str doc)
in (let _165_278 = (let _165_277 = (let _165_276 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _165_276))
in (FStar_Pprint.op_Hat_Hat kwd_args_doc _165_277))
in (FStar_Pprint.op_Hat_Hat _165_279 _165_278)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _165_280))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _165_281))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_282))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline _165_283)))
end))
and p_decl2 : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Open (uid) -> begin
(let _165_287 = (let _165_286 = (str "open")
in (let _165_285 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat _165_286 _165_285)))
in (FStar_Pprint.group _165_287))
end
| FStar_Parser_AST.ModuleAbbrev (uid1, uid2) -> begin
(let _165_294 = (let _165_292 = (str "module")
in (let _165_291 = (let _165_290 = (let _165_289 = (p_uident uid1)
in (let _165_288 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _165_289 _165_288)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_290))
in (FStar_Pprint.op_Hat_Hat _165_292 _165_291)))
in (let _165_293 = (p_quident uid2)
in (op_Hat_Slash_Plus_Hat _165_294 _165_293)))
end
| FStar_Parser_AST.TopLevelModule (uid) -> begin
(let _165_298 = (let _165_297 = (str "module")
in (let _165_296 = (let _165_295 = (p_quident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_295))
in (FStar_Pprint.op_Hat_Hat _165_297 _165_296)))
in (FStar_Pprint.group _165_298))
end
| FStar_Parser_AST.KindAbbrev (_67_326) -> begin
(FStar_All.failwith "Deprecated, please stop throwing your old stuff at me !")
end
| FStar_Parser_AST.Tycon (qs, ((FStar_Parser_AST.TyconAbbrev (uid, tpars, None, t), None))::[]) when (FStar_List.contains FStar_Parser_AST.Effect qs) -> begin
(

let qs = (FStar_List.filter (fun q -> (q <> FStar_Parser_AST.Effect)) qs)
in (

let effect_prefix_doc = (let _165_304 = (p_qualifiers qs)
in (let _165_303 = (let _165_302 = (str "effect")
in (let _165_301 = (let _165_300 = (p_uident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_300))
in (FStar_Pprint.op_Hat_Hat _165_302 _165_301)))
in (FStar_Pprint.op_Hat_Hat _165_304 _165_303)))
in (let _165_307 = (let _165_305 = (p_typars tpars)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") effect_prefix_doc _165_305 FStar_Pprint.equals))
in (let _165_306 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _165_307 _165_306)))))
end
| FStar_Parser_AST.Tycon (qs, tcdefs) -> begin
(

let type_doc = (let _165_309 = (p_qualifiers qs)
in (let _165_308 = (str "type")
in (FStar_Pprint.op_Hat_Hat _165_309 _165_308)))
in (let _165_310 = (str "and")
in (precede_break_separate_map type_doc _165_310 p_fsdocTypeDeclPairs tcdefs)))
end
| FStar_Parser_AST.TopLevelLet (qs, q, lbs) -> begin
(

let let_doc = (let _165_314 = (p_qualifiers qs)
in (let _165_313 = (let _165_312 = (str "let")
in (let _165_311 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat _165_312 _165_311)))
in (FStar_Pprint.op_Hat_Hat _165_314 _165_313)))
in (let _165_315 = (str "and")
in (precede_break_separate_map let_doc _165_315 p_letbinding lbs)))
end
| FStar_Parser_AST.Val (qs, lid, t) -> begin
(let _165_324 = (let _165_322 = (p_qualifiers qs)
in (let _165_321 = (let _165_320 = (str "val")
in (let _165_319 = (let _165_318 = (let _165_317 = (p_lident lid)
in (let _165_316 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat _165_317 _165_316)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_318))
in (FStar_Pprint.op_Hat_Hat _165_320 _165_319)))
in (FStar_Pprint.op_Hat_Hat _165_322 _165_321)))
in (let _165_323 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _165_324 _165_323)))
end
| FStar_Parser_AST.Assume (qs, id, t) -> begin
(

let decl_keyword = if (let _165_325 = (FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_All.pipe_right _165_325 FStar_Util.is_upper)) then begin
FStar_Pprint.empty
end else begin
(let _165_326 = (str "val")
in (FStar_Pprint.op_Hat_Hat _165_326 FStar_Pprint.space))
end
in (let _165_333 = (let _165_331 = (p_qualifiers qs)
in (let _165_330 = (let _165_329 = (let _165_328 = (p_ident id)
in (let _165_327 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat _165_328 _165_327)))
in (FStar_Pprint.op_Hat_Hat decl_keyword _165_329))
in (FStar_Pprint.op_Hat_Hat _165_331 _165_330)))
in (let _165_332 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _165_333 _165_332))))
end
| FStar_Parser_AST.Exception (uid, t_opt) -> begin
(let _165_341 = (str "exception")
in (let _165_340 = (let _165_339 = (let _165_338 = (p_uident uid)
in (let _165_337 = (FStar_Pprint.optional (fun t -> (let _165_336 = (str "of")
in (let _165_335 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _165_336 _165_335)))) t_opt)
in (FStar_Pprint.op_Hat_Hat _165_338 _165_337)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_339))
in (FStar_Pprint.op_Hat_Hat _165_341 _165_340)))
end
| FStar_Parser_AST.NewEffect (qs, ne) -> begin
(let _165_346 = (p_qualifiers qs)
in (let _165_345 = (let _165_344 = (str "new_effect")
in (let _165_343 = (let _165_342 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_342))
in (FStar_Pprint.op_Hat_Hat _165_344 _165_343)))
in (FStar_Pprint.op_Hat_Hat _165_346 _165_345)))
end
| FStar_Parser_AST.SubEffect (se) -> begin
(let _165_349 = (str "sub_effect")
in (let _165_348 = (let _165_347 = (p_subEffect se)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_347))
in (FStar_Pprint.op_Hat_Hat _165_349 _165_348)))
end
| FStar_Parser_AST.NewEffectForFree (qs, ne) -> begin
(let _165_354 = (p_qualifiers qs)
in (let _165_353 = (let _165_352 = (str "new_effect_for_free")
in (let _165_351 = (let _165_350 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_350))
in (FStar_Pprint.op_Hat_Hat _165_352 _165_351)))
in (FStar_Pprint.op_Hat_Hat _165_354 _165_353)))
end
| FStar_Parser_AST.Pragma (p) -> begin
(p_pragma p)
end
| FStar_Parser_AST.Fsdoc (doc) -> begin
(let _165_355 = (p_fsdoc doc)
in (FStar_Pprint.op_Hat_Hat _165_355 FStar_Pprint.hardline))
end
| FStar_Parser_AST.Main (_67_385) -> begin
(FStar_All.failwith "*Main declaration* : Is that really still in use ??")
end))
and p_pragma : FStar_Parser_AST.pragma  ->  FStar_Pprint.document = (fun _67_6 -> (match (_67_6) with
| FStar_Parser_AST.SetOptions (s) -> begin
(let _165_360 = (str "#set-options")
in (let _165_359 = (let _165_358 = (let _165_357 = (str s)
in (FStar_Pprint.dquotes _165_357))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_358))
in (FStar_Pprint.op_Hat_Hat _165_360 _165_359)))
end
| FStar_Parser_AST.ResetOptions (s_opt) -> begin
(let _165_365 = (str "#reset-options")
in (let _165_364 = (FStar_Pprint.optional (fun s -> (let _165_363 = (let _165_362 = (str s)
in (FStar_Pprint.dquotes _165_362))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_363))) s_opt)
in (FStar_Pprint.op_Hat_Hat _165_365 _165_364)))
end))
and p_typars : FStar_Parser_AST.binder Prims.list  ->  FStar_Pprint.document = (fun bs -> (p_binders true bs))
and p_fsdocTypeDeclPairs : (FStar_Parser_AST.tycon * FStar_Parser_AST.fsdoc Prims.option)  ->  FStar_Pprint.document = (fun _67_396 -> (match (_67_396) with
| (typedecl, fsdoc_opt) -> begin
(let _165_369 = (FStar_Pprint.optional p_fsdoc fsdoc_opt)
in (let _165_368 = (p_typeDecl typedecl)
in (FStar_Pprint.op_Hat_Hat _165_369 _165_368)))
end))
and p_typeDecl : FStar_Parser_AST.tycon  ->  FStar_Pprint.document = (fun _67_7 -> (match (_67_7) with
| FStar_Parser_AST.TyconAbstract (lid, bs, typ_opt) -> begin
(p_typeDeclPrefix lid bs typ_opt FStar_Pprint.empty)
end
| FStar_Parser_AST.TyconAbbrev (lid, bs, typ_opt, t) -> begin
(let _165_372 = (let _165_371 = (p_typ t)
in (prefix2 FStar_Pprint.equals _165_371))
in (p_typeDeclPrefix lid bs typ_opt _165_372))
end
| FStar_Parser_AST.TyconRecord (lid, bs, typ_opt, record_field_decls) -> begin
(let _165_377 = (let _165_376 = (let _165_375 = (let _165_374 = (let _165_373 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (FStar_Pprint.separate_map _165_373 p_recordFieldDecl record_field_decls))
in (braces_with_nesting _165_374))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_375))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.equals _165_376))
in (p_typeDeclPrefix lid bs typ_opt _165_377))
end
| FStar_Parser_AST.TyconVariant (lid, bs, typ_opt, ct_decls) -> begin
(

let datacon_doc = (let _165_382 = (FStar_Pprint.separate_map break1 (fun decl -> (let _165_381 = (let _165_380 = (let _165_379 = (p_constructorDecl decl)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_379))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar _165_380))
in (FStar_Pprint.group _165_381))) ct_decls)
in (FStar_Pprint.group _165_382))
in (let _165_383 = (prefix2 FStar_Pprint.equals datacon_doc)
in (p_typeDeclPrefix lid bs typ_opt _165_383)))
end))
and p_typeDeclPrefix : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.knd Prims.option  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun lid bs typ_opt cont -> if ((bs = []) && (typ_opt = None)) then begin
(let _165_389 = (p_ident lid)
in (let _165_388 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space cont)
in (FStar_Pprint.op_Hat_Hat _165_389 _165_388)))
end else begin
(

let binders_doc = (let _165_395 = (p_typars bs)
in (let _165_394 = (FStar_Pprint.optional (fun t -> (let _165_393 = (let _165_392 = (let _165_391 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_391))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_392))
in (FStar_Pprint.op_Hat_Hat break1 _165_393))) typ_opt)
in (FStar_Pprint.op_Hat_Hat _165_395 _165_394)))
in (let _165_396 = (p_ident lid)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_396 binders_doc cont)))
end)
and p_recordFieldDecl : (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc Prims.option)  ->  FStar_Pprint.document = (fun _67_432 -> (match (_67_432) with
| (lid, t, doc_opt) -> begin
(let _165_403 = (let _165_402 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (let _165_401 = (let _165_400 = (p_lident lid)
in (let _165_399 = (let _165_398 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_398))
in (FStar_Pprint.op_Hat_Hat _165_400 _165_399)))
in (FStar_Pprint.op_Hat_Hat _165_402 _165_401)))
in (FStar_Pprint.group _165_403))
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
in (let _165_410 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (let _165_409 = (default_or_map uid_doc (fun t -> (let _165_408 = (let _165_406 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep)
in (FStar_Pprint.op_Hat_Hat uid_doc _165_406))
in (let _165_407 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _165_408 _165_407)))) t_opt)
in (FStar_Pprint.op_Hat_Hat _165_410 _165_409)))))
end))
and p_letbinding : (FStar_Parser_AST.pattern * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun _67_443 -> (match (_67_443) with
| (pat, e) -> begin
(

let pat_doc = (

let _67_452 = (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, t) -> begin
(let _165_415 = (let _165_414 = (let _165_413 = (let _165_412 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat break1 _165_412))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_413))
in (FStar_Pprint.op_Hat_Hat break1 _165_414))
in ((pat), (_165_415)))
end
| _67_449 -> begin
((pat), (FStar_Pprint.empty))
end)
in (match (_67_452) with
| (pat, ascr_doc) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _67_457); FStar_Parser_AST.prange = _67_454}, pats) -> begin
(let _165_418 = (p_lident x)
in (let _165_417 = (let _165_416 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Hat _165_416 ascr_doc))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_418 _165_417 FStar_Pprint.equals)))
end
| _67_465 -> begin
(let _165_421 = (let _165_420 = (p_tuplePattern pat)
in (let _165_419 = (FStar_Pprint.op_Hat_Slash_Hat ascr_doc FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _165_420 _165_419)))
in (FStar_Pprint.group _165_421))
end)
end))
in (let _165_422 = (p_term e)
in (prefix2 pat_doc _165_422)))
end))
and p_newEffect : FStar_Parser_AST.effect_decl  ->  FStar_Pprint.document = (fun _67_8 -> (match (_67_8) with
| FStar_Parser_AST.RedefineEffect (lid, bs, t) -> begin
(p_effectRedefinition lid bs t)
end
| FStar_Parser_AST.DefineEffect (lid, bs, t, eff_decls, action_decls) -> begin
(p_effectDefinition lid bs t eff_decls action_decls)
end))
and p_effectRedefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun uid bs t -> (let _165_430 = (p_uident uid)
in (let _165_429 = (p_binders true bs)
in (let _165_428 = (let _165_427 = (p_simpleTerm t)
in (prefix2 FStar_Pprint.equals _165_427))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_430 _165_429 _165_428)))))
and p_effectDefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun uid bs t eff_decls action_decls -> (let _165_447 = (let _165_446 = (let _165_440 = (let _165_439 = (p_uident uid)
in (let _165_438 = (p_binders true bs)
in (let _165_437 = (let _165_436 = (p_typ t)
in (prefix2 FStar_Pprint.colon _165_436))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_439 _165_438 _165_437))))
in (FStar_Pprint.group _165_440))
in (let _165_445 = (let _165_444 = (let _165_442 = (str "with")
in (let _165_441 = (separate_break_map FStar_Pprint.semi p_effectDecl eff_decls)
in (prefix2 _165_442 _165_441)))
in (let _165_443 = (p_actionDecls action_decls)
in (FStar_Pprint.op_Hat_Hat _165_444 _165_443)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_446 _165_445)))
in (braces_with_nesting _165_447)))
and p_actionDecls : FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun _67_9 -> (match (_67_9) with
| [] -> begin
FStar_Pprint.empty
end
| l -> begin
(let _165_451 = (let _165_450 = (str "and actions")
in (let _165_449 = (separate_break_map FStar_Pprint.semi p_effectDecl l)
in (prefix2 _165_450 _165_449)))
in (FStar_Pprint.op_Hat_Hat break1 _165_451))
end))
and p_effectDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon ([], ((FStar_Parser_AST.TyconAbbrev (lid, [], None, e), None))::[]) -> begin
(let _165_456 = (let _165_454 = (p_lident lid)
in (let _165_453 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _165_454 _165_453)))
in (let _165_455 = (p_simpleTerm e)
in (prefix2 _165_456 _165_455)))
end
| _67_505 -> begin
(let _165_458 = (let _165_457 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "Not a declaration of an effect member... or at least I hope so : %s" _165_457))
in (FStar_All.failwith _165_458))
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
(let _165_465 = (let _165_463 = (str kwd)
in (let _165_462 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _165_463 _165_462)))
in (let _165_464 = (p_simpleTerm t)
in (prefix2 _165_465 _165_464)))
end))
in (separate_break_map FStar_Pprint.semi p_lift lifts)))
in (let _165_473 = (let _165_470 = (let _165_468 = (p_quident lift.FStar_Parser_AST.msource)
in (let _165_467 = (let _165_466 = (str "~>")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_466))
in (FStar_Pprint.op_Hat_Hat _165_468 _165_467)))
in (let _165_469 = (p_quident lift.FStar_Parser_AST.mdest)
in (prefix2 _165_470 _165_469)))
in (let _165_472 = (let _165_471 = (braces_with_nesting lift_op_doc)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_471))
in (FStar_Pprint.op_Hat_Hat _165_473 _165_472)))))
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
and p_qualifiers : FStar_Parser_AST.qualifier Prims.list  ->  FStar_Pprint.document = (fun qs -> (let _165_477 = (let _165_476 = (FStar_Pprint.separate_map break1 p_qualifier qs)
in (FStar_Pprint.op_Hat_Hat _165_476 (if (qs = []) then begin
FStar_Pprint.empty
end else begin
FStar_Pprint.space
end)))
in (FStar_Pprint.group _165_477)))
and p_letqualifier : FStar_Parser_AST.let_qualifier  ->  FStar_Pprint.document = (fun _67_11 -> (match (_67_11) with
| FStar_Parser_AST.Rec -> begin
(let _165_479 = (str "rec")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_479))
end
| FStar_Parser_AST.Mutable -> begin
(let _165_480 = (str "mutable")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_480))
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
(let _165_485 = (let _165_484 = (let _165_483 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space)
in (FStar_Pprint.op_Hat_Hat break1 _165_483))
in (FStar_Pprint.separate_map _165_484 p_tuplePattern pats))
in (FStar_Pprint.group _165_485))
end
| _67_553 -> begin
(p_tuplePattern p)
end))
and p_tuplePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTuple (pats, false) -> begin
(let _165_488 = (let _165_487 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map _165_487 p_constructorPattern pats))
in (FStar_Pprint.group _165_488))
end
| _67_560 -> begin
(p_constructorPattern p)
end))
and p_constructorPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (maybe_cons_lid); FStar_Parser_AST.prange = _67_563}, (hd)::(tl)::[]) when (FStar_Ident.lid_equals maybe_cons_lid FStar_Syntax_Const.cons_lid) -> begin
(let _165_492 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon)
in (let _165_491 = (p_constructorPattern hd)
in (let _165_490 = (p_constructorPattern tl)
in (infix2 _165_492 _165_491 _165_490))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (uid); FStar_Parser_AST.prange = _67_573}, pats) -> begin
(let _165_494 = (p_quident uid)
in (let _165_493 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (prefix2 _165_494 _165_493)))
end
| _67_581 -> begin
(p_atomicPattern p)
end))
and p_atomicPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, t) -> begin
(let _165_498 = (let _165_497 = (p_tuplePattern pat)
in (let _165_496 = (p_typ t)
in (infix2 FStar_Pprint.colon _165_497 _165_496)))
in (parens_with_nesting _165_498))
end
| FStar_Parser_AST.PatList (pats) -> begin
(let _165_499 = (separate_break_map FStar_Pprint.semi p_tuplePattern pats)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket _165_499 FStar_Pprint.rbracket))
end
| FStar_Parser_AST.PatRecord (pats) -> begin
(

let p_recordFieldPat = (fun _67_594 -> (match (_67_594) with
| (lid, pat) -> begin
(let _165_503 = (p_qlident lid)
in (let _165_502 = (p_tuplePattern pat)
in (infix2 FStar_Pprint.equals _165_503 _165_502)))
end))
in (let _165_504 = (separate_break_map FStar_Pprint.semi p_recordFieldPat pats)
in (braces_with_nesting _165_504)))
end
| FStar_Parser_AST.PatTuple (pats, true) -> begin
(let _165_507 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (let _165_506 = (separate_break_map FStar_Pprint.comma p_constructorPattern pats)
in (let _165_505 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_507 _165_506 _165_505))))
end
| FStar_Parser_AST.PatTvar (tv, arg_qualifier_opt) -> begin
(

let _67_603 = ()
in (p_tvar tv))
end
| FStar_Parser_AST.PatOp (op) -> begin
(let _165_511 = (let _165_510 = (let _165_509 = (str op)
in (let _165_508 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat _165_509 _165_508)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_510))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_511))
end
| FStar_Parser_AST.PatWild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.PatConst (c) -> begin
(p_constant c)
end
| FStar_Parser_AST.PatVar (lid, aqual) -> begin
(let _165_513 = (FStar_Pprint.optional p_aqual aqual)
in (let _165_512 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat _165_513 _165_512)))
end
| FStar_Parser_AST.PatName (uid) -> begin
(p_quident uid)
end
| FStar_Parser_AST.PatOr (_67_617) -> begin
(FStar_All.failwith "Inner or pattern !")
end
| (FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (_); FStar_Parser_AST.prange = _}, _)) | (FStar_Parser_AST.PatTuple (_, false)) -> begin
(let _165_514 = (p_tuplePattern p)
in (parens_with_nesting _165_514))
end
| _67_635 -> begin
(let _165_516 = (let _165_515 = (FStar_Parser_AST.pat_to_string p)
in (FStar_Util.format1 "Invalid pattern %s" _165_515))
in (FStar_All.failwith _165_516))
end))
and p_binder : Prims.bool  ->  FStar_Parser_AST.binder  ->  FStar_Pprint.document = (fun is_atomic b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (lid) -> begin
(let _165_520 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (let _165_519 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat _165_520 _165_519)))
end
| FStar_Parser_AST.TVariable (lid) -> begin
(p_lident lid)
end
| FStar_Parser_AST.Annotated (lid, t) -> begin
(

let doc = (let _165_525 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (let _165_524 = (let _165_523 = (p_lident lid)
in (let _165_522 = (let _165_521 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_521))
in (FStar_Pprint.op_Hat_Hat _165_523 _165_522)))
in (FStar_Pprint.op_Hat_Hat _165_525 _165_524)))
in if is_atomic then begin
(let _165_527 = (let _165_526 = (FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_526))
in (FStar_Pprint.group _165_527))
end else begin
(FStar_Pprint.group doc)
end)
end
| FStar_Parser_AST.TAnnotated (_67_648) -> begin
(FStar_All.failwith "Is this still used ?")
end
| FStar_Parser_AST.NoName (t) -> begin
if is_atomic then begin
(p_atomicTerm t)
end else begin
(p_appTerm t)
end
end))
and p_binders : Prims.bool  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Pprint.document = (fun is_atomic bs -> (FStar_Pprint.separate_map break1 (p_binder is_atomic) bs))
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
(let _165_541 = (let _165_539 = (let _165_538 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat _165_538 FStar_Pprint.semi))
in (FStar_Pprint.group _165_539))
in (let _165_540 = (p_term e2)
in (FStar_Pprint.op_Hat_Slash_Hat _165_541 _165_540)))
end
| _67_667 -> begin
(let _165_542 = (p_noSeqTerm e)
in (FStar_Pprint.group _165_542))
end))
and p_noSeqTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Ascribed (e, t) -> begin
(let _165_548 = (let _165_547 = (p_tmIff e)
in (let _165_546 = (let _165_545 = (let _165_544 = (p_typ t)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon _165_544))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.langle _165_545))
in (FStar_Pprint.op_Hat_Slash_Hat _165_547 _165_546)))
in (FStar_Pprint.group _165_548))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::(e3)::[]) when (op = ".()<-") -> begin
(let _165_559 = (let _165_558 = (let _165_555 = (let _165_554 = (p_atomicTermNotQUident e1)
in (let _165_553 = (let _165_552 = (let _165_551 = (let _165_549 = (p_term e2)
in (parens_with_nesting _165_549))
in (let _165_550 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat _165_551 _165_550)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_552))
in (FStar_Pprint.op_Hat_Hat _165_554 _165_553)))
in (FStar_Pprint.group _165_555))
in (let _165_557 = (let _165_556 = (p_noSeqTerm e3)
in (jump2 _165_556))
in (FStar_Pprint.op_Hat_Hat _165_558 _165_557)))
in (FStar_Pprint.group _165_559))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::(e3)::[]) when (op = ".[]<-") -> begin
(let _165_570 = (let _165_569 = (let _165_566 = (let _165_565 = (p_atomicTermNotQUident e1)
in (let _165_564 = (let _165_563 = (let _165_562 = (let _165_560 = (p_term e2)
in (brackets_with_nesting _165_560))
in (let _165_561 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat _165_562 _165_561)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_563))
in (FStar_Pprint.op_Hat_Hat _165_565 _165_564)))
in (FStar_Pprint.group _165_566))
in (let _165_568 = (let _165_567 = (p_noSeqTerm e3)
in (jump2 _165_567))
in (FStar_Pprint.op_Hat_Hat _165_569 _165_568)))
in (FStar_Pprint.group _165_570))
end
| FStar_Parser_AST.Requires (e, wtf) -> begin
(

let _67_691 = ()
in (let _165_573 = (let _165_572 = (str "requires")
in (let _165_571 = (p_typ e)
in (FStar_Pprint.op_Hat_Slash_Hat _165_572 _165_571)))
in (FStar_Pprint.group _165_573)))
end
| FStar_Parser_AST.Ensures (e, wtf) -> begin
(

let _67_697 = ()
in (let _165_576 = (let _165_575 = (str "ensures")
in (let _165_574 = (p_typ e)
in (FStar_Pprint.op_Hat_Slash_Hat _165_575 _165_574)))
in (FStar_Pprint.group _165_576)))
end
| FStar_Parser_AST.Attributes (es) -> begin
(let _165_579 = (let _165_578 = (str "attributes")
in (let _165_577 = (FStar_Pprint.separate_map break1 p_atomicTerm es)
in (FStar_Pprint.op_Hat_Slash_Hat _165_578 _165_577)))
in (FStar_Pprint.group _165_579))
end
| FStar_Parser_AST.If (e1, e2, e3) -> begin
if (is_unit e3) then begin
(let _165_586 = (let _165_585 = (let _165_581 = (str "if")
in (let _165_580 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat _165_581 _165_580)))
in (let _165_584 = (let _165_583 = (str "then")
in (let _165_582 = (p_noSeqTerm e2)
in (op_Hat_Slash_Plus_Hat _165_583 _165_582)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_585 _165_584)))
in (FStar_Pprint.group _165_586))
end else begin
(

let e2_doc = (match (e2.FStar_Parser_AST.tm) with
| FStar_Parser_AST.If (_67_707, _67_709, e3) when (is_unit e3) -> begin
(let _165_587 = (p_noSeqTerm e2)
in (parens_with_nesting _165_587))
end
| _67_714 -> begin
(p_noSeqTerm e2)
end)
in (let _165_597 = (let _165_596 = (let _165_589 = (str "if")
in (let _165_588 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat _165_589 _165_588)))
in (let _165_595 = (let _165_594 = (let _165_590 = (str "then")
in (op_Hat_Slash_Plus_Hat _165_590 e2_doc))
in (let _165_593 = (let _165_592 = (str "else")
in (let _165_591 = (p_noSeqTerm e3)
in (op_Hat_Slash_Plus_Hat _165_592 _165_591)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_594 _165_593)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_596 _165_595)))
in (FStar_Pprint.group _165_597)))
end
end
| FStar_Parser_AST.TryWith (e, branches) -> begin
(let _165_604 = (let _165_603 = (let _165_599 = (str "try")
in (let _165_598 = (p_noSeqTerm e)
in (prefix2 _165_599 _165_598)))
in (let _165_602 = (let _165_601 = (str "with")
in (let _165_600 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat _165_601 _165_600)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_603 _165_602)))
in (FStar_Pprint.group _165_604))
end
| FStar_Parser_AST.Match (e, branches) -> begin
(let _165_610 = (let _165_609 = (let _165_607 = (str "match")
in (let _165_606 = (p_noSeqTerm e)
in (let _165_605 = (str "with")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_607 _165_606 _165_605))))
in (let _165_608 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat _165_609 _165_608)))
in (FStar_Pprint.group _165_610))
end
| FStar_Parser_AST.LetOpen (uid, e) -> begin
(let _165_616 = (let _165_615 = (let _165_613 = (str "let open")
in (let _165_612 = (p_quident uid)
in (let _165_611 = (str "in")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_613 _165_612 _165_611))))
in (let _165_614 = (p_term e)
in (FStar_Pprint.op_Hat_Slash_Hat _165_615 _165_614)))
in (FStar_Pprint.group _165_616))
end
| FStar_Parser_AST.Let (q, lbs, e) -> begin
(

let let_doc = (let _165_618 = (str "let")
in (let _165_617 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat _165_618 _165_617)))
in (let _165_623 = (let _165_619 = (str "and")
in (precede_break_separate_map let_doc _165_619 p_letbinding lbs))
in (let _165_622 = (let _165_621 = (str "in")
in (let _165_620 = (p_term e)
in (prefix2 _165_621 _165_620)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_623 _165_622))))
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, typ_opt); FStar_Parser_AST.prange = _67_735})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, branches); FStar_Parser_AST.range = _67_745; FStar_Parser_AST.level = _67_743}) when (matches_var maybe_x x) -> begin
(let _165_626 = (let _165_625 = (str "function")
in (let _165_624 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat _165_625 _165_624)))
in (FStar_Pprint.group _165_626))
end
| FStar_Parser_AST.Assign (id, e) -> begin
(let _165_630 = (let _165_629 = (p_lident id)
in (let _165_628 = (let _165_627 = (p_noSeqTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow _165_627))
in (FStar_Pprint.op_Hat_Slash_Hat _165_629 _165_628)))
in (FStar_Pprint.group _165_630))
end
| _67_758 -> begin
(p_typ e)
end))
and p_typ : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| (FStar_Parser_AST.QForall (bs, trigger, e1)) | (FStar_Parser_AST.QExists (bs, trigger, e1)) -> begin
(let _165_638 = (let _165_634 = (let _165_632 = (p_quantifier e)
in (FStar_Pprint.op_Hat_Hat _165_632 FStar_Pprint.space))
in (let _165_633 = (p_binders true bs)
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") _165_634 _165_633 FStar_Pprint.dot)))
in (let _165_637 = (let _165_636 = (p_trigger trigger)
in (let _165_635 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat _165_636 _165_635)))
in (prefix2 _165_638 _165_637)))
end
| _67_768 -> begin
(p_simpleTerm e)
end))
and p_quantifier : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.QForall (_67_771) -> begin
(str "forall")
end
| FStar_Parser_AST.QExists (_67_774) -> begin
(str "exists")
end
| _67_777 -> begin
(FStar_All.failwith "Imposible : p_quantifier called on a non-quantifier term")
end))
and p_trigger : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun _67_13 -> (match (_67_13) with
| [] -> begin
FStar_Pprint.empty
end
| pats -> begin
(let _165_647 = (let _165_646 = (let _165_645 = (str "pattern")
in (let _165_644 = (let _165_643 = (let _165_641 = (p_disjunctivePats pats)
in (jump2 _165_641))
in (let _165_642 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1)
in (FStar_Pprint.op_Hat_Slash_Hat _165_643 _165_642)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_645 _165_644)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_646))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace _165_647))
end))
and p_disjunctivePats : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun pats -> (let _165_649 = (str "\\/")
in (FStar_Pprint.separate_map _165_649 p_conjunctivePats pats)))
and p_conjunctivePats : FStar_Parser_AST.term Prims.list  ->  FStar_Pprint.document = (fun pats -> (let _165_651 = (FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats)
in (FStar_Pprint.group _165_651)))
and p_simpleTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Abs (pats, e) -> begin
(let _165_657 = (let _165_655 = (str "fun")
in (let _165_654 = (let _165_653 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Slash_Hat _165_653 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat _165_655 _165_654)))
in (let _165_656 = (p_term e)
in (op_Hat_Slash_Plus_Hat _165_657 _165_656)))
end
| _67_789 -> begin
(p_tmIff e)
end))
and p_maybeFocusArrow : Prims.bool  ->  FStar_Pprint.document = (fun b -> if b then begin
(str "~>")
end else begin
FStar_Pprint.rarrow
end)
and p_patternBranch : FStar_Parser_AST.branch  ->  FStar_Pprint.document = (fun _67_794 -> (match (_67_794) with
| (pat, when_opt, e) -> begin
(let _165_668 = (let _165_667 = (let _165_665 = (let _165_664 = (let _165_663 = (let _165_662 = (p_disjunctivePattern pat)
in (let _165_661 = (let _165_660 = (p_maybeWhen when_opt)
in (FStar_Pprint.op_Hat_Hat _165_660 FStar_Pprint.rarrow))
in (FStar_Pprint.op_Hat_Slash_Hat _165_662 _165_661)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_663))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar _165_664))
in (FStar_Pprint.group _165_665))
in (let _165_666 = (p_term e)
in (op_Hat_Slash_Plus_Hat _165_667 _165_666)))
in (FStar_Pprint.group _165_668))
end))
and p_maybeWhen : FStar_Parser_AST.term Prims.option  ->  FStar_Pprint.document = (fun _67_14 -> (match (_67_14) with
| None -> begin
FStar_Pprint.empty
end
| Some (e) -> begin
(let _165_672 = (str "when")
in (let _165_671 = (let _165_670 = (p_tmFormula e)
in (FStar_Pprint.op_Hat_Hat _165_670 FStar_Pprint.space))
in (op_Hat_Slash_Plus_Hat _165_672 _165_671)))
end))
and p_tmIff : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("<==>", (e1)::(e2)::[]) -> begin
(let _165_676 = (str "<==>")
in (let _165_675 = (p_tmImplies e1)
in (let _165_674 = (p_tmIff e2)
in (infix2 _165_676 _165_675 _165_674))))
end
| _67_807 -> begin
(p_tmImplies e)
end))
and p_tmImplies : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("==>", (e1)::(e2)::[]) -> begin
(let _165_680 = (str "==>")
in (let _165_679 = (p_tmArrow p_tmFormula e1)
in (let _165_678 = (p_tmImplies e2)
in (infix2 _165_680 _165_679 _165_678))))
end
| _67_816 -> begin
(p_tmArrow p_tmFormula e)
end))
and p_tmArrow : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_Tm e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Product (bs, tgt) -> begin
(let _165_692 = (let _165_691 = (FStar_Pprint.concat_map (fun b -> (let _165_689 = (p_binder false b)
in (let _165_688 = (let _165_687 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_687))
in (FStar_Pprint.op_Hat_Hat _165_689 _165_688)))) bs)
in (let _165_690 = (p_tmArrow p_Tm tgt)
in (FStar_Pprint.op_Hat_Hat _165_691 _165_690)))
in (FStar_Pprint.group _165_692))
end
| _67_825 -> begin
(p_Tm e)
end))
and p_tmFormula : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("\\/", (e1)::(e2)::[]) -> begin
(let _165_696 = (str "\\/")
in (let _165_695 = (p_tmFormula e1)
in (let _165_694 = (p_tmConjunction e2)
in (infix2 _165_696 _165_695 _165_694))))
end
| _67_834 -> begin
(p_tmConjunction e)
end))
and p_tmConjunction : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("/\\", (e1)::(e2)::[]) -> begin
(let _165_700 = (str "/\\")
in (let _165_699 = (p_tmConjunction e1)
in (let _165_698 = (p_tmTuple e2)
in (infix2 _165_700 _165_699 _165_698))))
end
| _67_843 -> begin
(p_tmTuple e)
end))
and p_tmTuple : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (lid, args) when (is_tuple_constructor lid) -> begin
(let _165_703 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map _165_703 (fun _67_852 -> (match (_67_852) with
| (e, _67_851) -> begin
(p_tmEq e)
end)) args))
end
| _67_854 -> begin
(p_tmEq e)
end))
and paren_if : Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun curr mine doc -> if (mine <= curr) then begin
doc
end else begin
(let _165_708 = (let _165_707 = (FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_707))
in (FStar_Pprint.group _165_708))
end)
and p_tmEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n = (max_level (FStar_List.append ((colon_equals)::(pipe_right)::[]) operatorInfix0ad12))
in (p_tmEq' n e)))
and p_tmEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (((is_operatorInfix0ad12 op) || (op = "=")) || (op = "|>")) -> begin
(

let _67_871 = (levels op)
in (match (_67_871) with
| (left, mine, right) -> begin
(let _165_715 = (let _165_714 = (str op)
in (let _165_713 = (p_tmEq' left e1)
in (let _165_712 = (p_tmEq' right e2)
in (infix2 _165_714 _165_713 _165_712))))
in (paren_if curr mine _165_715))
end))
end
| FStar_Parser_AST.Op (":=", (e1)::(e2)::[]) -> begin
(let _165_721 = (let _165_720 = (p_tmEq e1)
in (let _165_719 = (let _165_718 = (let _165_717 = (let _165_716 = (p_tmEq e2)
in (op_Hat_Slash_Plus_Hat FStar_Pprint.equals _165_716))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_717))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_718))
in (FStar_Pprint.op_Hat_Hat _165_720 _165_719)))
in (FStar_Pprint.group _165_721))
end
| _67_879 -> begin
(p_tmNoEq e)
end))
and p_tmNoEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n = (max_level ((colon_colon)::(amp)::(opinfix3)::(opinfix4)::[]))
in (p_tmNoEq' n e)))
and p_tmNoEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (lid, ((e1, _67_891))::((e2, _67_887))::[]) when ((FStar_Ident.lid_equals lid FStar_Syntax_Const.cons_lid) && (not ((is_list e)))) -> begin
(

let op = "::"
in (

let _67_900 = (levels op)
in (match (_67_900) with
| (left, mine, right) -> begin
(let _165_728 = (let _165_727 = (str op)
in (let _165_726 = (p_tmNoEq' left e1)
in (let _165_725 = (p_tmNoEq' right e2)
in (infix2 _165_727 _165_726 _165_725))))
in (paren_if curr mine _165_728))
end)))
end
| FStar_Parser_AST.Sum (binders, res) -> begin
(

let op = "&"
in (

let _67_909 = (levels op)
in (match (_67_909) with
| (left, mine, right) -> begin
(

let p_dsumfst = (fun b -> (let _165_734 = (p_binder false b)
in (let _165_733 = (let _165_732 = (let _165_731 = (str "&")
in (FStar_Pprint.op_Hat_Hat _165_731 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_732))
in (FStar_Pprint.op_Hat_Hat _165_734 _165_733))))
in (let _165_737 = (let _165_736 = (FStar_Pprint.concat_map p_dsumfst binders)
in (let _165_735 = (p_tmNoEq' right res)
in (FStar_Pprint.op_Hat_Hat _165_736 _165_735)))
in (paren_if curr mine _165_737)))
end)))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (is_operatorInfix34 op) -> begin
(

let _67_921 = (levels op)
in (match (_67_921) with
| (left, mine, right) -> begin
(let _165_741 = (let _165_740 = (str op)
in (let _165_739 = (p_tmNoEq' left e1)
in (let _165_738 = (p_tmNoEq' right e2)
in (infix2 _165_740 _165_739 _165_738))))
in (paren_if curr mine _165_741))
end))
end
| FStar_Parser_AST.Op ("-", (e)::[]) -> begin
(

let _67_930 = (levels "-")
in (match (_67_930) with
| (left, mine, right) -> begin
(let _165_742 = (p_tmNoEq' mine e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus _165_742))
end))
end
| FStar_Parser_AST.NamedTyp (lid, e) -> begin
(let _165_746 = (let _165_745 = (p_lidentOrUnderscore lid)
in (let _165_744 = (let _165_743 = (p_appTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon _165_743))
in (FStar_Pprint.op_Hat_Slash_Hat _165_745 _165_744)))
in (FStar_Pprint.group _165_746))
end
| FStar_Parser_AST.Refine (b, phi) -> begin
(p_refinedBinder b phi)
end
| FStar_Parser_AST.Record (with_opt, record_fields) -> begin
(let _165_750 = (let _165_749 = (default_or_map FStar_Pprint.empty p_with_clause with_opt)
in (let _165_748 = (let _165_747 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (FStar_Pprint.separate_map _165_747 p_simpleDef record_fields))
in (FStar_Pprint.op_Hat_Hat _165_749 _165_748)))
in (braces_with_nesting _165_750))
end
| FStar_Parser_AST.Op ("~", (e)::[]) -> begin
(let _165_753 = (let _165_752 = (str "~")
in (let _165_751 = (p_atomicTerm e)
in (FStar_Pprint.op_Hat_Hat _165_752 _165_751)))
in (FStar_Pprint.group _165_753))
end
| _67_949 -> begin
(p_appTerm e)
end))
and p_with_clause : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (let _165_758 = (p_appTerm e)
in (let _165_757 = (let _165_756 = (let _165_755 = (str "with")
in (FStar_Pprint.op_Hat_Hat _165_755 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_756))
in (FStar_Pprint.op_Hat_Hat _165_758 _165_757))))
and p_refinedBinder : FStar_Parser_AST.binder  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun b phi -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (lid, t) -> begin
(let _165_768 = (let _165_767 = (p_lident lid)
in (let _165_766 = (let _165_765 = (let _165_764 = (p_typ t)
in (let _165_763 = (let _165_762 = (let _165_761 = (p_term phi)
in (braces_with_nesting _165_761))
in (FStar_Pprint.op_Hat_Hat _165_762 FStar_Pprint.rparen))
in (FStar_Pprint.op_Hat_Hat _165_764 _165_763)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_765))
in (FStar_Pprint.op_Hat_Hat _165_767 _165_766)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_768))
end
| FStar_Parser_AST.TAnnotated (_67_958) -> begin
(FStar_All.failwith "Is this still used ?")
end
| (FStar_Parser_AST.Variable (_)) | (FStar_Parser_AST.TVariable (_)) | (FStar_Parser_AST.NoName (_)) -> begin
(let _165_770 = (let _165_769 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" _165_769))
in (FStar_All.failwith _165_770))
end))
and p_simpleDef : (FStar_Ident.lid * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun _67_971 -> (match (_67_971) with
| (lid, e) -> begin
(let _165_775 = (let _165_774 = (p_qlident lid)
in (let _165_773 = (let _165_772 = (p_simpleTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals _165_772))
in (FStar_Pprint.op_Hat_Slash_Hat _165_774 _165_773)))
in (FStar_Pprint.group _165_775))
end))
and p_appTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App (_67_974) when (is_general_application e) -> begin
(

let _67_978 = (head_and_args e)
in (match (_67_978) with
| (head, args) -> begin
(let _165_778 = (p_indexingTerm head)
in (let _165_777 = (FStar_Pprint.separate_map FStar_Pprint.space p_argTerm args)
in (op_Hat_Slash_Plus_Hat _165_778 _165_777)))
end))
end
| FStar_Parser_AST.Construct (lid, args) when ((is_general_construction e) && (not ((is_dtuple_constructor lid)))) -> begin
if (args = []) then begin
(p_quident lid)
end else begin
(let _165_780 = (p_quident lid)
in (let _165_779 = (FStar_Pprint.separate_map break1 p_argTerm args)
in (op_Hat_Slash_Plus_Hat _165_780 _165_779)))
end
end
| _67_984 -> begin
(p_indexingTerm e)
end))
and p_argTerm : (FStar_Parser_AST.term * FStar_Parser_AST.imp)  ->  FStar_Pprint.document = (fun arg_imp -> (match (arg_imp) with
| ({FStar_Parser_AST.tm = FStar_Parser_AST.Uvar (_67_991); FStar_Parser_AST.range = _67_989; FStar_Parser_AST.level = _67_987}, FStar_Parser_AST.UnivApp) -> begin
(p_univar (Prims.fst arg_imp))
end
| (u, FStar_Parser_AST.UnivApp) -> begin
(p_universe u)
end
| (e, FStar_Parser_AST.FsTypApp) -> begin
(let _165_782 = (p_indexingTerm e)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.langle _165_782 FStar_Pprint.rangle))
end
| (e, FStar_Parser_AST.Hash) -> begin
(let _165_784 = (str "#")
in (let _165_783 = (p_indexingTerm e)
in (FStar_Pprint.op_Hat_Hat _165_784 _165_783)))
end
| (e, FStar_Parser_AST.Nothing) -> begin
(p_indexingTerm e)
end))
and p_indexingTerm_aux : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun exit e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op (".()", (e1)::(e2)::[]) -> begin
(let _165_794 = (let _165_793 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (let _165_792 = (let _165_791 = (let _165_790 = (p_term e2)
in (parens_with_nesting _165_790))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_791))
in (FStar_Pprint.op_Hat_Hat _165_793 _165_792)))
in (FStar_Pprint.group _165_794))
end
| FStar_Parser_AST.Op (".[]", (e1)::(e2)::[]) -> begin
(let _165_799 = (let _165_798 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (let _165_797 = (let _165_796 = (let _165_795 = (p_term e2)
in (brackets_with_nesting _165_795))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_796))
in (FStar_Pprint.op_Hat_Hat _165_798 _165_797)))
in (FStar_Pprint.group _165_799))
end
| _67_1023 -> begin
(exit e)
end))
and p_indexingTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_indexingTerm_aux p_atomicTerm e))
and p_atomicTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.LetOpen (lid, e) -> begin
(let _165_805 = (p_quident lid)
in (let _165_804 = (let _165_803 = (let _165_802 = (p_term e)
in (parens_with_nesting _165_802))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_803))
in (FStar_Pprint.op_Hat_Hat _165_805 _165_804)))
end
| FStar_Parser_AST.Name (lid) -> begin
(p_quident lid)
end
| FStar_Parser_AST.Op (op, (e)::[]) -> begin
(let _165_807 = (str op)
in (let _165_806 = (p_atomicTerm e)
in (FStar_Pprint.op_Hat_Hat _165_807 _165_806)))
end
| _67_1038 -> begin
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
(let _165_810 = (str op)
in (let _165_809 = (p_atomicTermNotQUident e)
in (FStar_Pprint.op_Hat_Hat _165_810 _165_809)))
end
| FStar_Parser_AST.Op (op, []) -> begin
(let _165_814 = (let _165_813 = (let _165_812 = (str op)
in (let _165_811 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat _165_812 _165_811)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_813))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_814))
end
| FStar_Parser_AST.Construct (lid, args) when (is_dtuple_constructor lid) -> begin
(let _165_819 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (let _165_818 = (let _165_816 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (let _165_815 = (FStar_List.map Prims.fst args)
in (FStar_Pprint.separate_map _165_816 p_tmEq _165_815)))
in (let _165_817 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_819 _165_818 _165_817))))
end
| FStar_Parser_AST.Project (e, lid) -> begin
(let _165_823 = (let _165_822 = (p_atomicTermNotQUident e)
in (let _165_821 = (let _165_820 = (p_qlident lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_820))
in (FStar_Pprint.op_Hat_Slash_Hat _165_822 _165_821)))
in (FStar_Pprint.group _165_823))
end
| _67_1069 -> begin
(p_projectionLHS e)
end))
and p_projectionLHS : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (lid) -> begin
(p_qlident lid)
end
| FStar_Parser_AST.Projector (constr_lid, field_lid) -> begin
(let _165_828 = (p_quident constr_lid)
in (let _165_827 = (let _165_826 = (let _165_825 = (p_lident field_lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_825))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark _165_826))
in (FStar_Pprint.op_Hat_Hat _165_828 _165_827)))
end
| FStar_Parser_AST.Discrim (constr_lid) -> begin
(let _165_829 = (p_quident constr_lid)
in (FStar_Pprint.op_Hat_Hat _165_829 FStar_Pprint.qmark))
end
| FStar_Parser_AST.Paren (e) -> begin
(let _165_830 = (p_term e)
in (parens_with_nesting _165_830))
end
| _67_1082 when (is_array e) -> begin
(

let es = (extract_from_list e)
in (let _165_833 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar)
in (let _165_832 = (separate_map_or_flow FStar_Pprint.semi p_noSeqTerm es)
in (let _165_831 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") _165_833 _165_832 _165_831)))))
end
| _67_1085 when (is_list e) -> begin
(let _165_835 = (let _165_834 = (extract_from_list e)
in (separate_map_or_flow FStar_Pprint.semi p_noSeqTerm _165_834))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket _165_835 FStar_Pprint.rbracket))
end
| _67_1087 when (is_lex_list e) -> begin
(let _165_838 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket)
in (let _165_837 = (let _165_836 = (extract_from_list e)
in (separate_map_or_flow FStar_Pprint.semi p_noSeqTerm _165_836))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_838 _165_837 FStar_Pprint.rbracket)))
end
| _67_1089 when (is_ref_set e) -> begin
(

let es = (extract_from_ref_set e)
in (let _165_840 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace)
in (let _165_839 = (separate_map_or_flow FStar_Pprint.comma p_appTerm es)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") _165_840 _165_839 FStar_Pprint.rbrace))))
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Op (_)) | (FStar_Parser_AST.Tvar (_)) | (FStar_Parser_AST.Uvar (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) | (FStar_Parser_AST.Construct (_)) | (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.App (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.LetOpen (_)) | (FStar_Parser_AST.Seq (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Ascribed (_)) | (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Project (_)) | (FStar_Parser_AST.Product (_)) | (FStar_Parser_AST.Sum (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Refine (_)) | (FStar_Parser_AST.NamedTyp (_)) | (FStar_Parser_AST.Requires (_)) | (FStar_Parser_AST.Ensures (_)) | (FStar_Parser_AST.Assign (_)) | (FStar_Parser_AST.Attributes (_)) -> begin
(let _165_841 = (p_term e)
in (parens_with_nesting _165_841))
end
| FStar_Parser_AST.Labeled (_67_1177) -> begin
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
(let _165_843 = (FStar_Pprint.doc_of_char x)
in (FStar_Pprint.squotes _165_843))
end
| FStar_Const.Const_string (bytes, _67_1190) -> begin
(let _165_844 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes _165_844))
end
| FStar_Const.Const_bytearray (bytes, _67_1195) -> begin
(let _165_847 = (let _165_845 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes _165_845))
in (let _165_846 = (str "B")
in (FStar_Pprint.op_Hat_Hat _165_847 _165_846)))
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

let ending = (default_or_map FStar_Pprint.empty (fun _67_1214 -> (match (_67_1214) with
| (s, w) -> begin
(let _165_854 = (signedness s)
in (let _165_853 = (width w)
in (FStar_Pprint.op_Hat_Hat _165_854 _165_853)))
end)) sign_width_opt)
in (let _165_855 = (str repr)
in (FStar_Pprint.op_Hat_Hat _165_855 ending)))))
end
| FStar_Const.Const_range (r) -> begin
(let _165_856 = (FStar_Range.string_of_range r)
in (str _165_856))
end
| FStar_Const.Const_reify -> begin
(str "reify")
end
| FStar_Const.Const_reflect (lid) -> begin
(let _165_860 = (p_quident lid)
in (let _165_859 = (let _165_858 = (let _165_857 = (str "reflect")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_857))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark _165_858))
in (FStar_Pprint.op_Hat_Hat _165_860 _165_859)))
end))
and p_universe : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (let _165_863 = (str "u#")
in (let _165_862 = (p_atomicUniverse u)
in (FStar_Pprint.op_Hat_Hat _165_863 _165_862))))
and p_universeFrom : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match (u.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("+", (u1)::(u2)::[]) -> begin
(let _165_868 = (let _165_867 = (p_universeFrom u1)
in (let _165_866 = (let _165_865 = (p_universeFrom u2)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus _165_865))
in (FStar_Pprint.op_Hat_Slash_Hat _165_867 _165_866)))
in (FStar_Pprint.group _165_868))
end
| FStar_Parser_AST.App (_67_1230) -> begin
(

let _67_1234 = (head_and_args u)
in (match (_67_1234) with
| (head, args) -> begin
(match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (maybe_max_lid) when (FStar_Ident.lid_equals maybe_max_lid FStar_Syntax_Const.max_lid) -> begin
(let _165_872 = (let _165_871 = (p_qlident FStar_Syntax_Const.max_lid)
in (let _165_870 = (FStar_Pprint.separate_map FStar_Pprint.space (fun _67_1240 -> (match (_67_1240) with
| (u, _67_1239) -> begin
(p_atomicUniverse u)
end)) args)
in (op_Hat_Slash_Plus_Hat _165_871 _165_870)))
in (FStar_Pprint.group _165_872))
end
| _67_1242 -> begin
(let _165_874 = (let _165_873 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" _165_873))
in (FStar_All.failwith _165_874))
end)
end))
end
| _67_1244 -> begin
(p_atomicUniverse u)
end))
and p_atomicUniverse : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match (u.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Wild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (r, sw)) -> begin
(p_constant (FStar_Const.Const_int (((r), (sw)))))
end
| FStar_Parser_AST.Uvar (_67_1253) -> begin
(p_univar u)
end
| FStar_Parser_AST.Paren (u) -> begin
(let _165_876 = (p_universeFrom u)
in (parens_with_nesting _165_876))
end
| (FStar_Parser_AST.Op ("+", (_)::(_)::[])) | (FStar_Parser_AST.App (_)) -> begin
(let _165_877 = (p_universeFrom u)
in (parens_with_nesting _165_877))
end
| _67_1269 -> begin
(let _165_879 = (let _165_878 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" _165_878))
in (FStar_All.failwith _165_879))
end))
and p_univar : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match (u.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Uvar (id) -> begin
(str (FStar_Ident.text_of_id id))
end
| _67_1274 -> begin
(let _165_882 = (let _165_881 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Not a universe variable %s" _165_881))
in (FStar_All.failwith _165_882))
end))


let term_to_document : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_term e))


let decl_to_document : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun e -> (p_decl e))


let modul_to_document : FStar_Parser_AST.modul  ->  FStar_Pprint.document = (fun m -> (match (m) with
| (FStar_Parser_AST.Module (_, decls)) | (FStar_Parser_AST.Interface (_, decls, _)) -> begin
(let _165_889 = (FStar_All.pipe_right decls (FStar_List.map decl_to_document))
in (FStar_All.pipe_right _165_889 (FStar_Pprint.separate FStar_Pprint.hardline)))
end))


let comments_to_document : (Prims.string * FStar_Range.range) Prims.list  ->  FStar_Pprint.document = (fun comments -> (FStar_Pprint.separate_map FStar_Pprint.hardline (fun _67_1292 -> (match (_67_1292) with
| (comment, range) -> begin
(str comment)
end)) comments))


let modul_with_comments_to_document : FStar_Parser_AST.modul  ->  (Prims.string * FStar_Range.range) Prims.list  ->  (FStar_Pprint.document * (Prims.string * FStar_Range.range) Prims.list) = (fun m comments -> (

let rec aux = (fun _67_1299 decl -> (match (_67_1299) with
| (previous_range, comments, doc) -> begin
(

let current_range = decl.FStar_Parser_AST.drange
in (

let inbetween_range = (

let _67_1302 = if ((FStar_Range.file_of_range previous_range) <> (FStar_Range.file_of_range current_range)) then begin
(let _165_903 = (let _165_902 = (FStar_Range.file_of_range previous_range)
in (let _165_901 = (FStar_Range.file_of_range current_range)
in (FStar_Util.format2 "Given coments from different source files %s - %s" _165_902 _165_901)))
in (FStar_All.failwith _165_903))
end else begin
()
end
in (let _165_906 = (FStar_Range.file_of_range current_range)
in (let _165_905 = (FStar_Range.end_of_range previous_range)
in (let _165_904 = (FStar_Range.start_of_range current_range)
in (FStar_Range.mk_range _165_906 _165_905 _165_904)))))
in (

let _67_1312 = (FStar_Util.take (fun _67_18 -> (match (_67_18) with
| (_67_1307, range) -> begin
(FStar_Range.range_contains_range inbetween_range range)
end)) comments)
in (match (_67_1312) with
| (preceding_comments, comments) -> begin
(

let _67_1320 = (FStar_Util.take (fun _67_19 -> (match (_67_19) with
| (_67_1315, range) -> begin
(FStar_Range.range_contains_range current_range range)
end)) comments)
in (match (_67_1320) with
| (inner_comments, comments) -> begin
(

let range_line_diff = (fun range -> ((let _165_911 = (FStar_Range.end_of_range range)
in (FStar_Range.line_of_pos _165_911)) - (let _165_912 = (FStar_Range.start_of_range range)
in (FStar_Range.line_of_pos _165_912))))
in (

let max = (fun x y -> if (x < y) then begin
y
end else begin
x
end)
in (

let line_count = (((range_line_diff inbetween_range) - (Prims.parse_int "1")) - (FStar_List.fold_left (fun n _67_1330 -> (match (_67_1330) with
| (_67_1328, r) -> begin
(n + (let _165_919 = (range_line_diff r)
in (max _165_919 (Prims.parse_int "1"))))
end)) (Prims.parse_int "0") preceding_comments))
in (

let line_count = (max line_count (if (preceding_comments = []) then begin
(Prims.parse_int "0")
end else begin
(Prims.parse_int "1")
end))
in (

let inner_comments_doc = if (inner_comments = []) then begin
FStar_Pprint.empty
end else begin
(let _165_920 = (comments_to_document inner_comments)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline _165_920))
end
in (

let doc = (let _165_927 = (let _165_926 = (FStar_Pprint.repeat line_count FStar_Pprint.hardline)
in (let _165_925 = (let _165_924 = (comments_to_document preceding_comments)
in (let _165_923 = (let _165_922 = (let _165_921 = (decl_to_document decl)
in (FStar_Pprint.op_Hat_Hat _165_921 inner_comments_doc))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline _165_922))
in (FStar_Pprint.op_Hat_Hat _165_924 _165_923)))
in (FStar_Pprint.op_Hat_Hat _165_926 _165_925)))
in (FStar_Pprint.op_Hat_Hat doc _165_927))
in ((current_range), (comments), (doc))))))))
end))
end))))
end))
in (

let decls = (match (m) with
| (FStar_Parser_AST.Module (_, decls)) | (FStar_Parser_AST.Interface (_, decls, _)) -> begin
decls
end)
in (match (decls) with
| [] -> begin
((FStar_Pprint.empty), (comments))
end
| (d)::_67_1349 -> begin
(

let initial_range = (let _165_928 = (FStar_Range.file_of_range d.FStar_Parser_AST.drange)
in (FStar_Range.mk_range _165_928 FStar_Range.zeroPos FStar_Range.zeroPos))
in (

let _67_1357 = (FStar_List.fold_left aux ((initial_range), (comments), (FStar_Pprint.empty)) decls)
in (match (_67_1357) with
| (_67_1354, comments, doc) -> begin
((doc), (comments))
end)))
end))))




