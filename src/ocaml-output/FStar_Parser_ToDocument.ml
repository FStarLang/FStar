
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
in (failwith _165_106))
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
in (failwith _165_116))
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
(failwith (Prims.strcat "Unrecognized operator " s))
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
in (failwith _165_160))
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


let rec p_decl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (let _165_271 = (FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc)
in (let _165_270 = (let _165_269 = (p_attributes d.FStar_Parser_AST.attrs)
in (let _165_268 = (let _165_267 = (p_qualifiers d.FStar_Parser_AST.quals)
in (let _165_266 = (let _165_265 = (p_rawDecl d)
in (FStar_Pprint.op_Hat_Hat (if (d.FStar_Parser_AST.quals = []) then begin
FStar_Pprint.empty
end else begin
break1
end) _165_265))
in (FStar_Pprint.op_Hat_Hat _165_267 _165_266)))
in (FStar_Pprint.op_Hat_Hat _165_269 _165_268)))
in (FStar_Pprint.op_Hat_Hat _165_271 _165_270))))
and p_attributes : FStar_Parser_AST.attributes_  ->  FStar_Pprint.document = (fun attrs -> (let _165_275 = (let _165_273 = (str "@")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket _165_273))
in (let _165_274 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline)
in (FStar_Pprint.surround_separate_map (Prims.parse_int "0") (Prims.parse_int "2") FStar_Pprint.empty _165_275 FStar_Pprint.space _165_274 p_atomicTerm attrs))))
and p_fsdoc : FStar_Parser_AST.fsdoc  ->  FStar_Pprint.document = (fun _67_309 -> (match (_67_309) with
| (doc, kwd_args) -> begin
(

let kwd_args_doc = (match (kwd_args) with
| [] -> begin
FStar_Pprint.empty
end
| kwd_args -> begin
(

let process_kwd_arg = (fun _67_315 -> (match (_67_315) with
| (kwd, arg) -> begin
(let _165_283 = (str "@")
in (let _165_282 = (let _165_281 = (str kwd)
in (let _165_280 = (let _165_279 = (str arg)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_279))
in (FStar_Pprint.op_Hat_Hat _165_281 _165_280)))
in (FStar_Pprint.op_Hat_Hat _165_283 _165_282)))
end))
in (let _165_285 = (let _165_284 = (FStar_Pprint.separate_map FStar_Pprint.hardline process_kwd_arg kwd_args)
in (FStar_Pprint.op_Hat_Hat _165_284 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline _165_285)))
end)
in (let _165_293 = (let _165_292 = (let _165_291 = (let _165_290 = (let _165_289 = (str doc)
in (let _165_288 = (let _165_287 = (let _165_286 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _165_286))
in (FStar_Pprint.op_Hat_Hat kwd_args_doc _165_287))
in (FStar_Pprint.op_Hat_Hat _165_289 _165_288)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _165_290))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _165_291))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_292))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline _165_293)))
end))
and p_rawDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Open (uid) -> begin
(let _165_297 = (let _165_296 = (str "open")
in (let _165_295 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat _165_296 _165_295)))
in (FStar_Pprint.group _165_297))
end
| FStar_Parser_AST.ModuleAbbrev (uid1, uid2) -> begin
(let _165_304 = (let _165_302 = (str "module")
in (let _165_301 = (let _165_300 = (let _165_299 = (p_uident uid1)
in (let _165_298 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _165_299 _165_298)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_300))
in (FStar_Pprint.op_Hat_Hat _165_302 _165_301)))
in (let _165_303 = (p_quident uid2)
in (op_Hat_Slash_Plus_Hat _165_304 _165_303)))
end
| FStar_Parser_AST.TopLevelModule (uid) -> begin
(let _165_308 = (let _165_307 = (str "module")
in (let _165_306 = (let _165_305 = (p_quident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_305))
in (FStar_Pprint.op_Hat_Hat _165_307 _165_306)))
in (FStar_Pprint.group _165_308))
end
| FStar_Parser_AST.KindAbbrev (_67_327) -> begin
(failwith "Deprecated, please stop throwing your old stuff at me !")
end
| FStar_Parser_AST.Tycon (true, ((FStar_Parser_AST.TyconAbbrev (uid, tpars, None, t), None))::[]) -> begin
(

let effect_prefix_doc = (let _165_311 = (str "effect")
in (let _165_310 = (let _165_309 = (p_uident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_309))
in (FStar_Pprint.op_Hat_Hat _165_311 _165_310)))
in (let _165_314 = (let _165_312 = (p_typars tpars)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") effect_prefix_doc _165_312 FStar_Pprint.equals))
in (let _165_313 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _165_314 _165_313))))
end
| FStar_Parser_AST.Tycon (false, tcdefs) -> begin
(let _165_316 = (str "type")
in (let _165_315 = (str "and")
in (precede_break_separate_map _165_316 _165_315 p_fsdocTypeDeclPairs tcdefs)))
end
| FStar_Parser_AST.TopLevelLet (q, lbs) -> begin
(

let let_doc = (let _165_318 = (str "let")
in (let _165_317 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat _165_318 _165_317)))
in (let _165_319 = (str "and")
in (precede_break_separate_map let_doc _165_319 p_letbinding lbs)))
end
| FStar_Parser_AST.Val (lid, t) -> begin
(let _165_326 = (let _165_324 = (str "val")
in (let _165_323 = (let _165_322 = (let _165_321 = (p_lident lid)
in (let _165_320 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat _165_321 _165_320)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_322))
in (FStar_Pprint.op_Hat_Hat _165_324 _165_323)))
in (let _165_325 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _165_326 _165_325)))
end
| FStar_Parser_AST.Assume (id, t) -> begin
(

let decl_keyword = if (let _165_327 = (FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_All.pipe_right _165_327 FStar_Util.is_upper)) then begin
FStar_Pprint.empty
end else begin
(let _165_328 = (str "val")
in (FStar_Pprint.op_Hat_Hat _165_328 FStar_Pprint.space))
end
in (let _165_333 = (let _165_331 = (let _165_330 = (p_ident id)
in (let _165_329 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat _165_330 _165_329)))
in (FStar_Pprint.op_Hat_Hat decl_keyword _165_331))
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
| FStar_Parser_AST.NewEffect (ne) -> begin
(let _165_344 = (str "new_effect")
in (let _165_343 = (let _165_342 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_342))
in (FStar_Pprint.op_Hat_Hat _165_344 _165_343)))
end
| FStar_Parser_AST.SubEffect (se) -> begin
(let _165_347 = (str "sub_effect")
in (let _165_346 = (let _165_345 = (p_subEffect se)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_345))
in (FStar_Pprint.op_Hat_Hat _165_347 _165_346)))
end
| FStar_Parser_AST.NewEffectForFree (ne) -> begin
(let _165_350 = (str "new_effect_for_free")
in (let _165_349 = (let _165_348 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_348))
in (FStar_Pprint.op_Hat_Hat _165_350 _165_349)))
end
| FStar_Parser_AST.Pragma (p) -> begin
(p_pragma p)
end
| FStar_Parser_AST.Fsdoc (doc) -> begin
(let _165_351 = (p_fsdoc doc)
in (FStar_Pprint.op_Hat_Hat _165_351 FStar_Pprint.hardline))
end
| FStar_Parser_AST.Main (_67_376) -> begin
(failwith "*Main declaration* : Is that really still in use ??")
end
| FStar_Parser_AST.Tycon (true, _67_380) -> begin
(failwith "Effect abbreviation is expected to be defined by an abbreviation")
end))
and p_pragma : FStar_Parser_AST.pragma  ->  FStar_Pprint.document = (fun _67_6 -> (match (_67_6) with
| FStar_Parser_AST.SetOptions (s) -> begin
(let _165_356 = (str "#set-options")
in (let _165_355 = (let _165_354 = (let _165_353 = (str s)
in (FStar_Pprint.dquotes _165_353))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_354))
in (FStar_Pprint.op_Hat_Hat _165_356 _165_355)))
end
| FStar_Parser_AST.ResetOptions (s_opt) -> begin
(let _165_361 = (str "#reset-options")
in (let _165_360 = (FStar_Pprint.optional (fun s -> (let _165_359 = (let _165_358 = (str s)
in (FStar_Pprint.dquotes _165_358))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_359))) s_opt)
in (FStar_Pprint.op_Hat_Hat _165_361 _165_360)))
end))
and p_typars : FStar_Parser_AST.binder Prims.list  ->  FStar_Pprint.document = (fun bs -> (p_binders true bs))
and p_fsdocTypeDeclPairs : (FStar_Parser_AST.tycon * FStar_Parser_AST.fsdoc Prims.option)  ->  FStar_Pprint.document = (fun _67_392 -> (match (_67_392) with
| (typedecl, fsdoc_opt) -> begin
(let _165_365 = (FStar_Pprint.optional p_fsdoc fsdoc_opt)
in (let _165_364 = (p_typeDecl typedecl)
in (FStar_Pprint.op_Hat_Hat _165_365 _165_364)))
end))
and p_typeDecl : FStar_Parser_AST.tycon  ->  FStar_Pprint.document = (fun _67_7 -> (match (_67_7) with
| FStar_Parser_AST.TyconAbstract (lid, bs, typ_opt) -> begin
(p_typeDeclPrefix lid bs typ_opt FStar_Pprint.empty)
end
| FStar_Parser_AST.TyconAbbrev (lid, bs, typ_opt, t) -> begin
(let _165_368 = (let _165_367 = (p_typ t)
in (prefix2 FStar_Pprint.equals _165_367))
in (p_typeDeclPrefix lid bs typ_opt _165_368))
end
| FStar_Parser_AST.TyconRecord (lid, bs, typ_opt, record_field_decls) -> begin
(let _165_373 = (let _165_372 = (let _165_371 = (let _165_370 = (let _165_369 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (FStar_Pprint.separate_map _165_369 p_recordFieldDecl record_field_decls))
in (braces_with_nesting _165_370))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_371))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.equals _165_372))
in (p_typeDeclPrefix lid bs typ_opt _165_373))
end
| FStar_Parser_AST.TyconVariant (lid, bs, typ_opt, ct_decls) -> begin
(

let datacon_doc = (let _165_378 = (FStar_Pprint.separate_map break1 (fun decl -> (let _165_377 = (let _165_376 = (let _165_375 = (p_constructorDecl decl)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_375))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar _165_376))
in (FStar_Pprint.group _165_377))) ct_decls)
in (FStar_Pprint.group _165_378))
in (let _165_379 = (prefix2 FStar_Pprint.equals datacon_doc)
in (p_typeDeclPrefix lid bs typ_opt _165_379)))
end))
and p_typeDeclPrefix : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.knd Prims.option  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun lid bs typ_opt cont -> if ((bs = []) && (typ_opt = None)) then begin
(let _165_385 = (p_ident lid)
in (let _165_384 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space cont)
in (FStar_Pprint.op_Hat_Hat _165_385 _165_384)))
end else begin
(

let binders_doc = (let _165_391 = (p_typars bs)
in (let _165_390 = (FStar_Pprint.optional (fun t -> (let _165_389 = (let _165_388 = (let _165_387 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_387))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_388))
in (FStar_Pprint.op_Hat_Hat break1 _165_389))) typ_opt)
in (FStar_Pprint.op_Hat_Hat _165_391 _165_390)))
in (let _165_392 = (p_ident lid)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_392 binders_doc cont)))
end)
and p_recordFieldDecl : (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc Prims.option)  ->  FStar_Pprint.document = (fun _67_428 -> (match (_67_428) with
| (lid, t, doc_opt) -> begin
(let _165_399 = (let _165_398 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (let _165_397 = (let _165_396 = (p_lident lid)
in (let _165_395 = (let _165_394 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_394))
in (FStar_Pprint.op_Hat_Hat _165_396 _165_395)))
in (FStar_Pprint.op_Hat_Hat _165_398 _165_397)))
in (FStar_Pprint.group _165_399))
end))
and p_constructorDecl : (FStar_Ident.ident * FStar_Parser_AST.term Prims.option * FStar_Parser_AST.fsdoc Prims.option * Prims.bool)  ->  FStar_Pprint.document = (fun _67_433 -> (match (_67_433) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let sep = if use_of then begin
(str "of")
end else begin
FStar_Pprint.colon
end
in (

let uid_doc = (p_uident uid)
in (let _165_406 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (let _165_405 = (default_or_map uid_doc (fun t -> (let _165_404 = (let _165_402 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep)
in (FStar_Pprint.op_Hat_Hat uid_doc _165_402))
in (let _165_403 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _165_404 _165_403)))) t_opt)
in (FStar_Pprint.op_Hat_Hat _165_406 _165_405)))))
end))
and p_letbinding : (FStar_Parser_AST.pattern * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun _67_439 -> (match (_67_439) with
| (pat, e) -> begin
(

let pat_doc = (

let _67_448 = (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, t) -> begin
(let _165_411 = (let _165_410 = (let _165_409 = (let _165_408 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat break1 _165_408))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_409))
in (FStar_Pprint.op_Hat_Hat break1 _165_410))
in ((pat), (_165_411)))
end
| _67_445 -> begin
((pat), (FStar_Pprint.empty))
end)
in (match (_67_448) with
| (pat, ascr_doc) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _67_453); FStar_Parser_AST.prange = _67_450}, pats) -> begin
(let _165_414 = (p_lident x)
in (let _165_413 = (let _165_412 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Hat _165_412 ascr_doc))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_414 _165_413 FStar_Pprint.equals)))
end
| _67_461 -> begin
(let _165_417 = (let _165_416 = (p_tuplePattern pat)
in (let _165_415 = (FStar_Pprint.op_Hat_Slash_Hat ascr_doc FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _165_416 _165_415)))
in (FStar_Pprint.group _165_417))
end)
end))
in (let _165_418 = (p_term e)
in (prefix2 pat_doc _165_418)))
end))
and p_newEffect : FStar_Parser_AST.effect_decl  ->  FStar_Pprint.document = (fun _67_8 -> (match (_67_8) with
| FStar_Parser_AST.RedefineEffect (lid, bs, t) -> begin
(p_effectRedefinition lid bs t)
end
| FStar_Parser_AST.DefineEffect (lid, bs, t, eff_decls, action_decls) -> begin
(p_effectDefinition lid bs t eff_decls action_decls)
end))
and p_effectRedefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun uid bs t -> (let _165_426 = (p_uident uid)
in (let _165_425 = (p_binders true bs)
in (let _165_424 = (let _165_423 = (p_simpleTerm t)
in (prefix2 FStar_Pprint.equals _165_423))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_426 _165_425 _165_424)))))
and p_effectDefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun uid bs t eff_decls action_decls -> (let _165_443 = (let _165_442 = (let _165_436 = (let _165_435 = (p_uident uid)
in (let _165_434 = (p_binders true bs)
in (let _165_433 = (let _165_432 = (p_typ t)
in (prefix2 FStar_Pprint.colon _165_432))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_435 _165_434 _165_433))))
in (FStar_Pprint.group _165_436))
in (let _165_441 = (let _165_440 = (let _165_438 = (str "with")
in (let _165_437 = (separate_break_map FStar_Pprint.semi p_effectDecl eff_decls)
in (prefix2 _165_438 _165_437)))
in (let _165_439 = (p_actionDecls action_decls)
in (FStar_Pprint.op_Hat_Hat _165_440 _165_439)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_442 _165_441)))
in (braces_with_nesting _165_443)))
and p_actionDecls : FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun _67_9 -> (match (_67_9) with
| [] -> begin
FStar_Pprint.empty
end
| l -> begin
(let _165_447 = (let _165_446 = (str "and actions")
in (let _165_445 = (separate_break_map FStar_Pprint.semi p_effectDecl l)
in (prefix2 _165_446 _165_445)))
in (FStar_Pprint.op_Hat_Hat break1 _165_447))
end))
and p_effectDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (false, ((FStar_Parser_AST.TyconAbbrev (lid, [], None, e), None))::[]) -> begin
(let _165_452 = (let _165_450 = (p_lident lid)
in (let _165_449 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _165_450 _165_449)))
in (let _165_451 = (p_simpleTerm e)
in (prefix2 _165_452 _165_451)))
end
| _67_501 -> begin
(let _165_454 = (let _165_453 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "Not a declaration of an effect member... or at least I hope so : %s" _165_453))
in (failwith _165_454))
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

let p_lift = (fun _67_515 -> (match (_67_515) with
| (kwd, t) -> begin
(let _165_461 = (let _165_459 = (str kwd)
in (let _165_458 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _165_459 _165_458)))
in (let _165_460 = (p_simpleTerm t)
in (prefix2 _165_461 _165_460)))
end))
in (separate_break_map FStar_Pprint.semi p_lift lifts)))
in (let _165_469 = (let _165_466 = (let _165_464 = (p_quident lift.FStar_Parser_AST.msource)
in (let _165_463 = (let _165_462 = (str "~>")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_462))
in (FStar_Pprint.op_Hat_Hat _165_464 _165_463)))
in (let _165_465 = (p_quident lift.FStar_Parser_AST.mdest)
in (prefix2 _165_466 _165_465)))
in (let _165_468 = (let _165_467 = (braces_with_nesting lift_op_doc)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_467))
in (FStar_Pprint.op_Hat_Hat _165_469 _165_468)))))
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
and p_qualifiers : FStar_Parser_AST.qualifiers  ->  FStar_Pprint.document = (fun qs -> (let _165_473 = (let _165_472 = (FStar_Pprint.separate_map break1 p_qualifier qs)
in (FStar_Pprint.op_Hat_Hat _165_472 (if (qs = []) then begin
FStar_Pprint.empty
end else begin
FStar_Pprint.space
end)))
in (FStar_Pprint.group _165_473)))
and p_letqualifier : FStar_Parser_AST.let_qualifier  ->  FStar_Pprint.document = (fun _67_11 -> (match (_67_11) with
| FStar_Parser_AST.Rec -> begin
(let _165_475 = (str "rec")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_475))
end
| FStar_Parser_AST.Mutable -> begin
(let _165_476 = (str "mutable")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_476))
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
(let _165_481 = (let _165_480 = (let _165_479 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space)
in (FStar_Pprint.op_Hat_Hat break1 _165_479))
in (FStar_Pprint.separate_map _165_480 p_tuplePattern pats))
in (FStar_Pprint.group _165_481))
end
| _67_549 -> begin
(p_tuplePattern p)
end))
and p_tuplePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTuple (pats, false) -> begin
(let _165_484 = (let _165_483 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map _165_483 p_constructorPattern pats))
in (FStar_Pprint.group _165_484))
end
| _67_556 -> begin
(p_constructorPattern p)
end))
and p_constructorPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (maybe_cons_lid); FStar_Parser_AST.prange = _67_559}, (hd)::(tl)::[]) when (FStar_Ident.lid_equals maybe_cons_lid FStar_Syntax_Const.cons_lid) -> begin
(let _165_488 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon)
in (let _165_487 = (p_constructorPattern hd)
in (let _165_486 = (p_constructorPattern tl)
in (infix2 _165_488 _165_487 _165_486))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (uid); FStar_Parser_AST.prange = _67_569}, pats) -> begin
(let _165_490 = (p_quident uid)
in (let _165_489 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (prefix2 _165_490 _165_489)))
end
| _67_577 -> begin
(p_atomicPattern p)
end))
and p_atomicPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, t) -> begin
(let _165_494 = (let _165_493 = (p_tuplePattern pat)
in (let _165_492 = (p_typ t)
in (infix2 FStar_Pprint.colon _165_493 _165_492)))
in (parens_with_nesting _165_494))
end
| FStar_Parser_AST.PatList (pats) -> begin
(let _165_495 = (separate_break_map FStar_Pprint.semi p_tuplePattern pats)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket _165_495 FStar_Pprint.rbracket))
end
| FStar_Parser_AST.PatRecord (pats) -> begin
(

let p_recordFieldPat = (fun _67_590 -> (match (_67_590) with
| (lid, pat) -> begin
(let _165_499 = (p_qlident lid)
in (let _165_498 = (p_tuplePattern pat)
in (infix2 FStar_Pprint.equals _165_499 _165_498)))
end))
in (let _165_500 = (separate_break_map FStar_Pprint.semi p_recordFieldPat pats)
in (braces_with_nesting _165_500)))
end
| FStar_Parser_AST.PatTuple (pats, true) -> begin
(let _165_503 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (let _165_502 = (separate_break_map FStar_Pprint.comma p_constructorPattern pats)
in (let _165_501 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_503 _165_502 _165_501))))
end
| FStar_Parser_AST.PatTvar (tv, arg_qualifier_opt) -> begin
(

let _67_599 = ()
in (p_tvar tv))
end
| FStar_Parser_AST.PatOp (op) -> begin
(let _165_507 = (let _165_506 = (let _165_505 = (str op)
in (let _165_504 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat _165_505 _165_504)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_506))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_507))
end
| FStar_Parser_AST.PatWild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.PatConst (c) -> begin
(p_constant c)
end
| FStar_Parser_AST.PatVar (lid, aqual) -> begin
(let _165_509 = (FStar_Pprint.optional p_aqual aqual)
in (let _165_508 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat _165_509 _165_508)))
end
| FStar_Parser_AST.PatName (uid) -> begin
(p_quident uid)
end
| FStar_Parser_AST.PatOr (_67_613) -> begin
(failwith "Inner or pattern !")
end
| (FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (_); FStar_Parser_AST.prange = _}, _)) | (FStar_Parser_AST.PatTuple (_, false)) -> begin
(let _165_510 = (p_tuplePattern p)
in (parens_with_nesting _165_510))
end
| _67_631 -> begin
(let _165_512 = (let _165_511 = (FStar_Parser_AST.pat_to_string p)
in (FStar_Util.format1 "Invalid pattern %s" _165_511))
in (failwith _165_512))
end))
and p_binder : Prims.bool  ->  FStar_Parser_AST.binder  ->  FStar_Pprint.document = (fun is_atomic b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (lid) -> begin
(let _165_516 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (let _165_515 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat _165_516 _165_515)))
end
| FStar_Parser_AST.TVariable (lid) -> begin
(p_lident lid)
end
| FStar_Parser_AST.Annotated (lid, t) -> begin
(

let doc = (let _165_521 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (let _165_520 = (let _165_519 = (p_lident lid)
in (let _165_518 = (let _165_517 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_517))
in (FStar_Pprint.op_Hat_Hat _165_519 _165_518)))
in (FStar_Pprint.op_Hat_Hat _165_521 _165_520)))
in if is_atomic then begin
(let _165_523 = (let _165_522 = (FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_522))
in (FStar_Pprint.group _165_523))
end else begin
(FStar_Pprint.group doc)
end)
end
| FStar_Parser_AST.TAnnotated (_67_644) -> begin
(failwith "Is this still used ?")
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
(let _165_537 = (let _165_535 = (let _165_534 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat _165_534 FStar_Pprint.semi))
in (FStar_Pprint.group _165_535))
in (let _165_536 = (p_term e2)
in (FStar_Pprint.op_Hat_Slash_Hat _165_537 _165_536)))
end
| _67_663 -> begin
(let _165_538 = (p_noSeqTerm e)
in (FStar_Pprint.group _165_538))
end))
and p_noSeqTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Ascribed (e, t) -> begin
(let _165_544 = (let _165_543 = (p_tmIff e)
in (let _165_542 = (let _165_541 = (let _165_540 = (p_typ t)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon _165_540))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.langle _165_541))
in (FStar_Pprint.op_Hat_Slash_Hat _165_543 _165_542)))
in (FStar_Pprint.group _165_544))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::(e3)::[]) when (op = ".()<-") -> begin
(let _165_555 = (let _165_554 = (let _165_551 = (let _165_550 = (p_atomicTermNotQUident e1)
in (let _165_549 = (let _165_548 = (let _165_547 = (let _165_545 = (p_term e2)
in (parens_with_nesting _165_545))
in (let _165_546 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat _165_547 _165_546)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_548))
in (FStar_Pprint.op_Hat_Hat _165_550 _165_549)))
in (FStar_Pprint.group _165_551))
in (let _165_553 = (let _165_552 = (p_noSeqTerm e3)
in (jump2 _165_552))
in (FStar_Pprint.op_Hat_Hat _165_554 _165_553)))
in (FStar_Pprint.group _165_555))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::(e3)::[]) when (op = ".[]<-") -> begin
(let _165_566 = (let _165_565 = (let _165_562 = (let _165_561 = (p_atomicTermNotQUident e1)
in (let _165_560 = (let _165_559 = (let _165_558 = (let _165_556 = (p_term e2)
in (brackets_with_nesting _165_556))
in (let _165_557 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat _165_558 _165_557)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_559))
in (FStar_Pprint.op_Hat_Hat _165_561 _165_560)))
in (FStar_Pprint.group _165_562))
in (let _165_564 = (let _165_563 = (p_noSeqTerm e3)
in (jump2 _165_563))
in (FStar_Pprint.op_Hat_Hat _165_565 _165_564)))
in (FStar_Pprint.group _165_566))
end
| FStar_Parser_AST.Requires (e, wtf) -> begin
(

let _67_687 = ()
in (let _165_569 = (let _165_568 = (str "requires")
in (let _165_567 = (p_typ e)
in (FStar_Pprint.op_Hat_Slash_Hat _165_568 _165_567)))
in (FStar_Pprint.group _165_569)))
end
| FStar_Parser_AST.Ensures (e, wtf) -> begin
(

let _67_693 = ()
in (let _165_572 = (let _165_571 = (str "ensures")
in (let _165_570 = (p_typ e)
in (FStar_Pprint.op_Hat_Slash_Hat _165_571 _165_570)))
in (FStar_Pprint.group _165_572)))
end
| FStar_Parser_AST.Attributes (es) -> begin
(let _165_575 = (let _165_574 = (str "attributes")
in (let _165_573 = (FStar_Pprint.separate_map break1 p_atomicTerm es)
in (FStar_Pprint.op_Hat_Slash_Hat _165_574 _165_573)))
in (FStar_Pprint.group _165_575))
end
| FStar_Parser_AST.If (e1, e2, e3) -> begin
if (is_unit e3) then begin
(let _165_582 = (let _165_581 = (let _165_577 = (str "if")
in (let _165_576 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat _165_577 _165_576)))
in (let _165_580 = (let _165_579 = (str "then")
in (let _165_578 = (p_noSeqTerm e2)
in (op_Hat_Slash_Plus_Hat _165_579 _165_578)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_581 _165_580)))
in (FStar_Pprint.group _165_582))
end else begin
(

let e2_doc = (match (e2.FStar_Parser_AST.tm) with
| FStar_Parser_AST.If (_67_703, _67_705, e3) when (is_unit e3) -> begin
(let _165_583 = (p_noSeqTerm e2)
in (parens_with_nesting _165_583))
end
| _67_710 -> begin
(p_noSeqTerm e2)
end)
in (let _165_593 = (let _165_592 = (let _165_585 = (str "if")
in (let _165_584 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat _165_585 _165_584)))
in (let _165_591 = (let _165_590 = (let _165_586 = (str "then")
in (op_Hat_Slash_Plus_Hat _165_586 e2_doc))
in (let _165_589 = (let _165_588 = (str "else")
in (let _165_587 = (p_noSeqTerm e3)
in (op_Hat_Slash_Plus_Hat _165_588 _165_587)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_590 _165_589)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_592 _165_591)))
in (FStar_Pprint.group _165_593)))
end
end
| FStar_Parser_AST.TryWith (e, branches) -> begin
(let _165_600 = (let _165_599 = (let _165_595 = (str "try")
in (let _165_594 = (p_noSeqTerm e)
in (prefix2 _165_595 _165_594)))
in (let _165_598 = (let _165_597 = (str "with")
in (let _165_596 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat _165_597 _165_596)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_599 _165_598)))
in (FStar_Pprint.group _165_600))
end
| FStar_Parser_AST.Match (e, branches) -> begin
(let _165_606 = (let _165_605 = (let _165_603 = (str "match")
in (let _165_602 = (p_noSeqTerm e)
in (let _165_601 = (str "with")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_603 _165_602 _165_601))))
in (let _165_604 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat _165_605 _165_604)))
in (FStar_Pprint.group _165_606))
end
| FStar_Parser_AST.LetOpen (uid, e) -> begin
(let _165_612 = (let _165_611 = (let _165_609 = (str "let open")
in (let _165_608 = (p_quident uid)
in (let _165_607 = (str "in")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_609 _165_608 _165_607))))
in (let _165_610 = (p_term e)
in (FStar_Pprint.op_Hat_Slash_Hat _165_611 _165_610)))
in (FStar_Pprint.group _165_612))
end
| FStar_Parser_AST.Let (q, lbs, e) -> begin
(

let let_doc = (let _165_614 = (str "let")
in (let _165_613 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat _165_614 _165_613)))
in (let _165_619 = (let _165_615 = (str "and")
in (precede_break_separate_map let_doc _165_615 p_letbinding lbs))
in (let _165_618 = (let _165_617 = (str "in")
in (let _165_616 = (p_term e)
in (prefix2 _165_617 _165_616)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_619 _165_618))))
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, typ_opt); FStar_Parser_AST.prange = _67_731})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, branches); FStar_Parser_AST.range = _67_741; FStar_Parser_AST.level = _67_739}) when (matches_var maybe_x x) -> begin
(let _165_622 = (let _165_621 = (str "function")
in (let _165_620 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat _165_621 _165_620)))
in (FStar_Pprint.group _165_622))
end
| FStar_Parser_AST.Assign (id, e) -> begin
(let _165_626 = (let _165_625 = (p_lident id)
in (let _165_624 = (let _165_623 = (p_noSeqTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow _165_623))
in (FStar_Pprint.op_Hat_Slash_Hat _165_625 _165_624)))
in (FStar_Pprint.group _165_626))
end
| _67_754 -> begin
(p_typ e)
end))
and p_typ : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| (FStar_Parser_AST.QForall (bs, trigger, e1)) | (FStar_Parser_AST.QExists (bs, trigger, e1)) -> begin
(let _165_634 = (let _165_630 = (let _165_628 = (p_quantifier e)
in (FStar_Pprint.op_Hat_Hat _165_628 FStar_Pprint.space))
in (let _165_629 = (p_binders true bs)
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") _165_630 _165_629 FStar_Pprint.dot)))
in (let _165_633 = (let _165_632 = (p_trigger trigger)
in (let _165_631 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat _165_632 _165_631)))
in (prefix2 _165_634 _165_633)))
end
| _67_764 -> begin
(p_simpleTerm e)
end))
and p_quantifier : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.QForall (_67_767) -> begin
(str "forall")
end
| FStar_Parser_AST.QExists (_67_770) -> begin
(str "exists")
end
| _67_773 -> begin
(failwith "Imposible : p_quantifier called on a non-quantifier term")
end))
and p_trigger : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun _67_13 -> (match (_67_13) with
| [] -> begin
FStar_Pprint.empty
end
| pats -> begin
(let _165_643 = (let _165_642 = (let _165_641 = (str "pattern")
in (let _165_640 = (let _165_639 = (let _165_637 = (p_disjunctivePats pats)
in (jump2 _165_637))
in (let _165_638 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1)
in (FStar_Pprint.op_Hat_Slash_Hat _165_639 _165_638)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_641 _165_640)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_642))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace _165_643))
end))
and p_disjunctivePats : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun pats -> (let _165_645 = (str "\\/")
in (FStar_Pprint.separate_map _165_645 p_conjunctivePats pats)))
and p_conjunctivePats : FStar_Parser_AST.term Prims.list  ->  FStar_Pprint.document = (fun pats -> (let _165_647 = (FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats)
in (FStar_Pprint.group _165_647)))
and p_simpleTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Abs (pats, e) -> begin
(let _165_653 = (let _165_651 = (str "fun")
in (let _165_650 = (let _165_649 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Slash_Hat _165_649 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat _165_651 _165_650)))
in (let _165_652 = (p_term e)
in (op_Hat_Slash_Plus_Hat _165_653 _165_652)))
end
| _67_785 -> begin
(p_tmIff e)
end))
and p_maybeFocusArrow : Prims.bool  ->  FStar_Pprint.document = (fun b -> if b then begin
(str "~>")
end else begin
FStar_Pprint.rarrow
end)
and p_patternBranch : FStar_Parser_AST.branch  ->  FStar_Pprint.document = (fun _67_790 -> (match (_67_790) with
| (pat, when_opt, e) -> begin
(let _165_664 = (let _165_663 = (let _165_661 = (let _165_660 = (let _165_659 = (let _165_658 = (p_disjunctivePattern pat)
in (let _165_657 = (let _165_656 = (p_maybeWhen when_opt)
in (FStar_Pprint.op_Hat_Hat _165_656 FStar_Pprint.rarrow))
in (FStar_Pprint.op_Hat_Slash_Hat _165_658 _165_657)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_659))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar _165_660))
in (FStar_Pprint.group _165_661))
in (let _165_662 = (p_term e)
in (op_Hat_Slash_Plus_Hat _165_663 _165_662)))
in (FStar_Pprint.group _165_664))
end))
and p_maybeWhen : FStar_Parser_AST.term Prims.option  ->  FStar_Pprint.document = (fun _67_14 -> (match (_67_14) with
| None -> begin
FStar_Pprint.empty
end
| Some (e) -> begin
(let _165_668 = (str "when")
in (let _165_667 = (let _165_666 = (p_tmFormula e)
in (FStar_Pprint.op_Hat_Hat _165_666 FStar_Pprint.space))
in (op_Hat_Slash_Plus_Hat _165_668 _165_667)))
end))
and p_tmIff : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("<==>", (e1)::(e2)::[]) -> begin
(let _165_672 = (str "<==>")
in (let _165_671 = (p_tmImplies e1)
in (let _165_670 = (p_tmIff e2)
in (infix2 _165_672 _165_671 _165_670))))
end
| _67_803 -> begin
(p_tmImplies e)
end))
and p_tmImplies : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("==>", (e1)::(e2)::[]) -> begin
(let _165_676 = (str "==>")
in (let _165_675 = (p_tmArrow p_tmFormula e1)
in (let _165_674 = (p_tmImplies e2)
in (infix2 _165_676 _165_675 _165_674))))
end
| _67_812 -> begin
(p_tmArrow p_tmFormula e)
end))
and p_tmArrow : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_Tm e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Product (bs, tgt) -> begin
(let _165_688 = (let _165_687 = (FStar_Pprint.concat_map (fun b -> (let _165_685 = (p_binder false b)
in (let _165_684 = (let _165_683 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_683))
in (FStar_Pprint.op_Hat_Hat _165_685 _165_684)))) bs)
in (let _165_686 = (p_tmArrow p_Tm tgt)
in (FStar_Pprint.op_Hat_Hat _165_687 _165_686)))
in (FStar_Pprint.group _165_688))
end
| _67_821 -> begin
(p_Tm e)
end))
and p_tmFormula : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("\\/", (e1)::(e2)::[]) -> begin
(let _165_692 = (str "\\/")
in (let _165_691 = (p_tmFormula e1)
in (let _165_690 = (p_tmConjunction e2)
in (infix2 _165_692 _165_691 _165_690))))
end
| _67_830 -> begin
(p_tmConjunction e)
end))
and p_tmConjunction : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("/\\", (e1)::(e2)::[]) -> begin
(let _165_696 = (str "/\\")
in (let _165_695 = (p_tmConjunction e1)
in (let _165_694 = (p_tmTuple e2)
in (infix2 _165_696 _165_695 _165_694))))
end
| _67_839 -> begin
(p_tmTuple e)
end))
and p_tmTuple : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (lid, args) when (is_tuple_constructor lid) -> begin
(let _165_699 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map _165_699 (fun _67_848 -> (match (_67_848) with
| (e, _67_847) -> begin
(p_tmEq e)
end)) args))
end
| _67_850 -> begin
(p_tmEq e)
end))
and paren_if : Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun curr mine doc -> if (mine <= curr) then begin
doc
end else begin
(let _165_704 = (let _165_703 = (FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_703))
in (FStar_Pprint.group _165_704))
end)
and p_tmEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n = (max_level (FStar_List.append ((colon_equals)::(pipe_right)::[]) operatorInfix0ad12))
in (p_tmEq' n e)))
and p_tmEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (((is_operatorInfix0ad12 op) || (op = "=")) || (op = "|>")) -> begin
(

let _67_867 = (levels op)
in (match (_67_867) with
| (left, mine, right) -> begin
(let _165_711 = (let _165_710 = (str op)
in (let _165_709 = (p_tmEq' left e1)
in (let _165_708 = (p_tmEq' right e2)
in (infix2 _165_710 _165_709 _165_708))))
in (paren_if curr mine _165_711))
end))
end
| FStar_Parser_AST.Op (":=", (e1)::(e2)::[]) -> begin
(let _165_717 = (let _165_716 = (p_tmEq e1)
in (let _165_715 = (let _165_714 = (let _165_713 = (let _165_712 = (p_tmEq e2)
in (op_Hat_Slash_Plus_Hat FStar_Pprint.equals _165_712))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_713))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_714))
in (FStar_Pprint.op_Hat_Hat _165_716 _165_715)))
in (FStar_Pprint.group _165_717))
end
| _67_875 -> begin
(p_tmNoEq e)
end))
and p_tmNoEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n = (max_level ((colon_colon)::(amp)::(opinfix3)::(opinfix4)::[]))
in (p_tmNoEq' n e)))
and p_tmNoEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (lid, ((e1, _67_887))::((e2, _67_883))::[]) when ((FStar_Ident.lid_equals lid FStar_Syntax_Const.cons_lid) && (not ((is_list e)))) -> begin
(

let op = "::"
in (

let _67_896 = (levels op)
in (match (_67_896) with
| (left, mine, right) -> begin
(let _165_724 = (let _165_723 = (str op)
in (let _165_722 = (p_tmNoEq' left e1)
in (let _165_721 = (p_tmNoEq' right e2)
in (infix2 _165_723 _165_722 _165_721))))
in (paren_if curr mine _165_724))
end)))
end
| FStar_Parser_AST.Sum (binders, res) -> begin
(

let op = "&"
in (

let _67_905 = (levels op)
in (match (_67_905) with
| (left, mine, right) -> begin
(

let p_dsumfst = (fun b -> (let _165_730 = (p_binder false b)
in (let _165_729 = (let _165_728 = (let _165_727 = (str "&")
in (FStar_Pprint.op_Hat_Hat _165_727 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_728))
in (FStar_Pprint.op_Hat_Hat _165_730 _165_729))))
in (let _165_733 = (let _165_732 = (FStar_Pprint.concat_map p_dsumfst binders)
in (let _165_731 = (p_tmNoEq' right res)
in (FStar_Pprint.op_Hat_Hat _165_732 _165_731)))
in (paren_if curr mine _165_733)))
end)))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (is_operatorInfix34 op) -> begin
(

let _67_917 = (levels op)
in (match (_67_917) with
| (left, mine, right) -> begin
(let _165_737 = (let _165_736 = (str op)
in (let _165_735 = (p_tmNoEq' left e1)
in (let _165_734 = (p_tmNoEq' right e2)
in (infix2 _165_736 _165_735 _165_734))))
in (paren_if curr mine _165_737))
end))
end
| FStar_Parser_AST.Op ("-", (e)::[]) -> begin
(

let _67_926 = (levels "-")
in (match (_67_926) with
| (left, mine, right) -> begin
(let _165_738 = (p_tmNoEq' mine e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus _165_738))
end))
end
| FStar_Parser_AST.NamedTyp (lid, e) -> begin
(let _165_742 = (let _165_741 = (p_lidentOrUnderscore lid)
in (let _165_740 = (let _165_739 = (p_appTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon _165_739))
in (FStar_Pprint.op_Hat_Slash_Hat _165_741 _165_740)))
in (FStar_Pprint.group _165_742))
end
| FStar_Parser_AST.Refine (b, phi) -> begin
(p_refinedBinder b phi)
end
| FStar_Parser_AST.Record (with_opt, record_fields) -> begin
(let _165_746 = (let _165_745 = (default_or_map FStar_Pprint.empty p_with_clause with_opt)
in (let _165_744 = (let _165_743 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (FStar_Pprint.separate_map _165_743 p_simpleDef record_fields))
in (FStar_Pprint.op_Hat_Hat _165_745 _165_744)))
in (braces_with_nesting _165_746))
end
| FStar_Parser_AST.Op ("~", (e)::[]) -> begin
(let _165_749 = (let _165_748 = (str "~")
in (let _165_747 = (p_atomicTerm e)
in (FStar_Pprint.op_Hat_Hat _165_748 _165_747)))
in (FStar_Pprint.group _165_749))
end
| _67_945 -> begin
(p_appTerm e)
end))
and p_with_clause : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (let _165_754 = (p_appTerm e)
in (let _165_753 = (let _165_752 = (let _165_751 = (str "with")
in (FStar_Pprint.op_Hat_Hat _165_751 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_752))
in (FStar_Pprint.op_Hat_Hat _165_754 _165_753))))
and p_refinedBinder : FStar_Parser_AST.binder  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun b phi -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (lid, t) -> begin
(let _165_764 = (let _165_763 = (p_lident lid)
in (let _165_762 = (let _165_761 = (let _165_760 = (p_typ t)
in (let _165_759 = (let _165_758 = (let _165_757 = (p_term phi)
in (braces_with_nesting _165_757))
in (FStar_Pprint.op_Hat_Hat _165_758 FStar_Pprint.rparen))
in (FStar_Pprint.op_Hat_Hat _165_760 _165_759)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_761))
in (FStar_Pprint.op_Hat_Hat _165_763 _165_762)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_764))
end
| FStar_Parser_AST.TAnnotated (_67_954) -> begin
(failwith "Is this still used ?")
end
| (FStar_Parser_AST.Variable (_)) | (FStar_Parser_AST.TVariable (_)) | (FStar_Parser_AST.NoName (_)) -> begin
(let _165_766 = (let _165_765 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" _165_765))
in (failwith _165_766))
end))
and p_simpleDef : (FStar_Ident.lid * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun _67_967 -> (match (_67_967) with
| (lid, e) -> begin
(let _165_771 = (let _165_770 = (p_qlident lid)
in (let _165_769 = (let _165_768 = (p_simpleTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals _165_768))
in (FStar_Pprint.op_Hat_Slash_Hat _165_770 _165_769)))
in (FStar_Pprint.group _165_771))
end))
and p_appTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App (_67_970) when (is_general_application e) -> begin
(

let _67_974 = (head_and_args e)
in (match (_67_974) with
| (head, args) -> begin
(let _165_774 = (p_indexingTerm head)
in (let _165_773 = (FStar_Pprint.separate_map FStar_Pprint.space p_argTerm args)
in (op_Hat_Slash_Plus_Hat _165_774 _165_773)))
end))
end
| FStar_Parser_AST.Construct (lid, args) when ((is_general_construction e) && (not ((is_dtuple_constructor lid)))) -> begin
if (args = []) then begin
(p_quident lid)
end else begin
(let _165_776 = (p_quident lid)
in (let _165_775 = (FStar_Pprint.separate_map break1 p_argTerm args)
in (op_Hat_Slash_Plus_Hat _165_776 _165_775)))
end
end
| _67_980 -> begin
(p_indexingTerm e)
end))
and p_argTerm : (FStar_Parser_AST.term * FStar_Parser_AST.imp)  ->  FStar_Pprint.document = (fun arg_imp -> (match (arg_imp) with
| ({FStar_Parser_AST.tm = FStar_Parser_AST.Uvar (_67_987); FStar_Parser_AST.range = _67_985; FStar_Parser_AST.level = _67_983}, FStar_Parser_AST.UnivApp) -> begin
(p_univar (Prims.fst arg_imp))
end
| (u, FStar_Parser_AST.UnivApp) -> begin
(p_universe u)
end
| (e, FStar_Parser_AST.FsTypApp) -> begin
(let _165_778 = (p_indexingTerm e)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.langle _165_778 FStar_Pprint.rangle))
end
| (e, FStar_Parser_AST.Hash) -> begin
(let _165_780 = (str "#")
in (let _165_779 = (p_indexingTerm e)
in (FStar_Pprint.op_Hat_Hat _165_780 _165_779)))
end
| (e, FStar_Parser_AST.Nothing) -> begin
(p_indexingTerm e)
end))
and p_indexingTerm_aux : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun exit e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op (".()", (e1)::(e2)::[]) -> begin
(let _165_790 = (let _165_789 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (let _165_788 = (let _165_787 = (let _165_786 = (p_term e2)
in (parens_with_nesting _165_786))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_787))
in (FStar_Pprint.op_Hat_Hat _165_789 _165_788)))
in (FStar_Pprint.group _165_790))
end
| FStar_Parser_AST.Op (".[]", (e1)::(e2)::[]) -> begin
(let _165_795 = (let _165_794 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (let _165_793 = (let _165_792 = (let _165_791 = (p_term e2)
in (brackets_with_nesting _165_791))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_792))
in (FStar_Pprint.op_Hat_Hat _165_794 _165_793)))
in (FStar_Pprint.group _165_795))
end
| _67_1019 -> begin
(exit e)
end))
and p_indexingTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_indexingTerm_aux p_atomicTerm e))
and p_atomicTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.LetOpen (lid, e) -> begin
(let _165_801 = (p_quident lid)
in (let _165_800 = (let _165_799 = (let _165_798 = (p_term e)
in (parens_with_nesting _165_798))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_799))
in (FStar_Pprint.op_Hat_Hat _165_801 _165_800)))
end
| FStar_Parser_AST.Name (lid) -> begin
(p_quident lid)
end
| FStar_Parser_AST.Op (op, (e)::[]) -> begin
(let _165_803 = (str op)
in (let _165_802 = (p_atomicTerm e)
in (FStar_Pprint.op_Hat_Hat _165_803 _165_802)))
end
| _67_1034 -> begin
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
(let _165_806 = (str op)
in (let _165_805 = (p_atomicTermNotQUident e)
in (FStar_Pprint.op_Hat_Hat _165_806 _165_805)))
end
| FStar_Parser_AST.Op (op, []) -> begin
(let _165_810 = (let _165_809 = (let _165_808 = (str op)
in (let _165_807 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat _165_808 _165_807)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_809))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_810))
end
| FStar_Parser_AST.Construct (lid, args) when (is_dtuple_constructor lid) -> begin
(let _165_815 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (let _165_814 = (let _165_812 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (let _165_811 = (FStar_List.map Prims.fst args)
in (FStar_Pprint.separate_map _165_812 p_tmEq _165_811)))
in (let _165_813 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_815 _165_814 _165_813))))
end
| FStar_Parser_AST.Project (e, lid) -> begin
(let _165_819 = (let _165_818 = (p_atomicTermNotQUident e)
in (let _165_817 = (let _165_816 = (p_qlident lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_816))
in (FStar_Pprint.op_Hat_Slash_Hat _165_818 _165_817)))
in (FStar_Pprint.group _165_819))
end
| _67_1065 -> begin
(p_projectionLHS e)
end))
and p_projectionLHS : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (lid) -> begin
(p_qlident lid)
end
| FStar_Parser_AST.Projector (constr_lid, field_lid) -> begin
(let _165_824 = (p_quident constr_lid)
in (let _165_823 = (let _165_822 = (let _165_821 = (p_lident field_lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_821))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark _165_822))
in (FStar_Pprint.op_Hat_Hat _165_824 _165_823)))
end
| FStar_Parser_AST.Discrim (constr_lid) -> begin
(let _165_825 = (p_quident constr_lid)
in (FStar_Pprint.op_Hat_Hat _165_825 FStar_Pprint.qmark))
end
| FStar_Parser_AST.Paren (e) -> begin
(let _165_826 = (p_term e)
in (parens_with_nesting _165_826))
end
| _67_1078 when (is_array e) -> begin
(

let es = (extract_from_list e)
in (let _165_829 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar)
in (let _165_828 = (separate_map_or_flow FStar_Pprint.semi p_noSeqTerm es)
in (let _165_827 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") _165_829 _165_828 _165_827)))))
end
| _67_1081 when (is_list e) -> begin
(let _165_831 = (let _165_830 = (extract_from_list e)
in (separate_map_or_flow FStar_Pprint.semi p_noSeqTerm _165_830))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket _165_831 FStar_Pprint.rbracket))
end
| _67_1083 when (is_lex_list e) -> begin
(let _165_834 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket)
in (let _165_833 = (let _165_832 = (extract_from_list e)
in (separate_map_or_flow FStar_Pprint.semi p_noSeqTerm _165_832))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_834 _165_833 FStar_Pprint.rbracket)))
end
| _67_1085 when (is_ref_set e) -> begin
(

let es = (extract_from_ref_set e)
in (let _165_836 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace)
in (let _165_835 = (separate_map_or_flow FStar_Pprint.comma p_appTerm es)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") _165_836 _165_835 FStar_Pprint.rbrace))))
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Op (_)) | (FStar_Parser_AST.Tvar (_)) | (FStar_Parser_AST.Uvar (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) | (FStar_Parser_AST.Construct (_)) | (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.App (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.LetOpen (_)) | (FStar_Parser_AST.Seq (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Ascribed (_)) | (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Project (_)) | (FStar_Parser_AST.Product (_)) | (FStar_Parser_AST.Sum (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Refine (_)) | (FStar_Parser_AST.NamedTyp (_)) | (FStar_Parser_AST.Requires (_)) | (FStar_Parser_AST.Ensures (_)) | (FStar_Parser_AST.Assign (_)) | (FStar_Parser_AST.Attributes (_)) -> begin
(let _165_837 = (p_term e)
in (parens_with_nesting _165_837))
end
| FStar_Parser_AST.Labeled (_67_1173) -> begin
(failwith "Not valid in universe")
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
(let _165_839 = (FStar_Pprint.doc_of_char x)
in (FStar_Pprint.squotes _165_839))
end
| FStar_Const.Const_string (bytes, _67_1186) -> begin
(let _165_840 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes _165_840))
end
| FStar_Const.Const_bytearray (bytes, _67_1191) -> begin
(let _165_843 = (let _165_841 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes _165_841))
in (let _165_842 = (str "B")
in (FStar_Pprint.op_Hat_Hat _165_843 _165_842)))
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

let ending = (default_or_map FStar_Pprint.empty (fun _67_1210 -> (match (_67_1210) with
| (s, w) -> begin
(let _165_850 = (signedness s)
in (let _165_849 = (width w)
in (FStar_Pprint.op_Hat_Hat _165_850 _165_849)))
end)) sign_width_opt)
in (let _165_851 = (str repr)
in (FStar_Pprint.op_Hat_Hat _165_851 ending)))))
end
| FStar_Const.Const_range (r) -> begin
(let _165_852 = (FStar_Range.string_of_range r)
in (str _165_852))
end
| FStar_Const.Const_reify -> begin
(str "reify")
end
| FStar_Const.Const_reflect (lid) -> begin
(let _165_856 = (p_quident lid)
in (let _165_855 = (let _165_854 = (let _165_853 = (str "reflect")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_853))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark _165_854))
in (FStar_Pprint.op_Hat_Hat _165_856 _165_855)))
end))
and p_universe : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (let _165_859 = (str "u#")
in (let _165_858 = (p_atomicUniverse u)
in (FStar_Pprint.op_Hat_Hat _165_859 _165_858))))
and p_universeFrom : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match (u.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("+", (u1)::(u2)::[]) -> begin
(let _165_864 = (let _165_863 = (p_universeFrom u1)
in (let _165_862 = (let _165_861 = (p_universeFrom u2)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus _165_861))
in (FStar_Pprint.op_Hat_Slash_Hat _165_863 _165_862)))
in (FStar_Pprint.group _165_864))
end
| FStar_Parser_AST.App (_67_1226) -> begin
(

let _67_1230 = (head_and_args u)
in (match (_67_1230) with
| (head, args) -> begin
(match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (maybe_max_lid) when (FStar_Ident.lid_equals maybe_max_lid FStar_Syntax_Const.max_lid) -> begin
(let _165_868 = (let _165_867 = (p_qlident FStar_Syntax_Const.max_lid)
in (let _165_866 = (FStar_Pprint.separate_map FStar_Pprint.space (fun _67_1236 -> (match (_67_1236) with
| (u, _67_1235) -> begin
(p_atomicUniverse u)
end)) args)
in (op_Hat_Slash_Plus_Hat _165_867 _165_866)))
in (FStar_Pprint.group _165_868))
end
| _67_1238 -> begin
(let _165_870 = (let _165_869 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" _165_869))
in (failwith _165_870))
end)
end))
end
| _67_1240 -> begin
(p_atomicUniverse u)
end))
and p_atomicUniverse : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match (u.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Wild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (r, sw)) -> begin
(p_constant (FStar_Const.Const_int (((r), (sw)))))
end
| FStar_Parser_AST.Uvar (_67_1249) -> begin
(p_univar u)
end
| FStar_Parser_AST.Paren (u) -> begin
(let _165_872 = (p_universeFrom u)
in (parens_with_nesting _165_872))
end
| (FStar_Parser_AST.Op ("+", (_)::(_)::[])) | (FStar_Parser_AST.App (_)) -> begin
(let _165_873 = (p_universeFrom u)
in (parens_with_nesting _165_873))
end
| _67_1265 -> begin
(let _165_875 = (let _165_874 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" _165_874))
in (failwith _165_875))
end))
and p_univar : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match (u.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Uvar (id) -> begin
(str (FStar_Ident.text_of_id id))
end
| _67_1270 -> begin
(let _165_878 = (let _165_877 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Not a universe variable %s" _165_877))
in (failwith _165_878))
end))


let term_to_document : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_term e))


let decl_to_document : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun e -> (p_decl e))


let modul_to_document : FStar_Parser_AST.modul  ->  FStar_Pprint.document = (fun m -> (match (m) with
| (FStar_Parser_AST.Module (_, decls)) | (FStar_Parser_AST.Interface (_, decls, _)) -> begin
(let _165_885 = (FStar_All.pipe_right decls (FStar_List.map decl_to_document))
in (FStar_All.pipe_right _165_885 (FStar_Pprint.separate FStar_Pprint.hardline)))
end))


let comments_to_document : (Prims.string * FStar_Range.range) Prims.list  ->  FStar_Pprint.document = (fun comments -> (FStar_Pprint.separate_map FStar_Pprint.hardline (fun _67_1288 -> (match (_67_1288) with
| (comment, range) -> begin
(str comment)
end)) comments))


let modul_with_comments_to_document : FStar_Parser_AST.modul  ->  (Prims.string * FStar_Range.range) Prims.list  ->  (FStar_Pprint.document * (Prims.string * FStar_Range.range) Prims.list) = (fun m comments -> (

let rec aux = (fun _67_1295 decl -> (match (_67_1295) with
| (previous_range_end, comments, doc) -> begin
(

let current_range = decl.FStar_Parser_AST.drange
in (

let inbetween_range = (let _165_898 = (FStar_Range.file_of_range current_range)
in (let _165_897 = (FStar_Range.start_of_range current_range)
in (FStar_Range.mk_range _165_898 previous_range_end _165_897)))
in (

let _67_1306 = (FStar_Util.take (fun _67_18 -> (match (_67_18) with
| (_67_1301, range) -> begin
(FStar_Range.range_contains_range inbetween_range range)
end)) comments)
in (match (_67_1306) with
| (preceding_comments, comments) -> begin
(

let _67_1314 = (FStar_Util.take (fun _67_19 -> (match (_67_19) with
| (_67_1309, range) -> begin
(FStar_Range.range_contains_range current_range range)
end)) comments)
in (match (_67_1314) with
| (inner_comments, comments) -> begin
(

let range_line_diff = (fun range -> ((let _165_903 = (FStar_Range.end_of_range range)
in (FStar_Range.line_of_pos _165_903)) - (let _165_904 = (FStar_Range.start_of_range range)
in (FStar_Range.line_of_pos _165_904))))
in (

let max = (fun x y -> if (x < y) then begin
y
end else begin
x
end)
in (

let line_count = (((range_line_diff inbetween_range) - (Prims.parse_int "1")) - (FStar_List.fold_left (fun n _67_1324 -> (match (_67_1324) with
| (_67_1322, r) -> begin
(n + (let _165_911 = (range_line_diff r)
in (max _165_911 (Prims.parse_int "1"))))
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
(let _165_912 = (comments_to_document inner_comments)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline _165_912))
end
in (

let doc = (let _165_919 = (let _165_918 = (FStar_Pprint.repeat line_count FStar_Pprint.hardline)
in (let _165_917 = (let _165_916 = (comments_to_document preceding_comments)
in (let _165_915 = (let _165_914 = (let _165_913 = (decl_to_document decl)
in (FStar_Pprint.op_Hat_Hat _165_913 inner_comments_doc))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline _165_914))
in (FStar_Pprint.op_Hat_Hat _165_916 _165_915)))
in (FStar_Pprint.op_Hat_Hat _165_918 _165_917)))
in (FStar_Pprint.op_Hat_Hat doc _165_919))
in (let _165_920 = (FStar_Range.end_of_range current_range)
in ((_165_920), (comments), (doc)))))))))
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
| (d)::_67_1343 -> begin
(

let _67_1350 = (FStar_List.fold_left aux ((FStar_Range.zeroPos), (comments), (FStar_Pprint.empty)) decls)
in (match (_67_1350) with
| (_67_1347, comments, doc) -> begin
((doc), (comments))
end))
end))))




