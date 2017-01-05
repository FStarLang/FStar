
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


let separate_break_map = (fun sep f l -> (let _167_30 = (let _167_29 = (let _167_28 = (FStar_Pprint.op_Hat_Hat sep break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_28))
in (FStar_Pprint.separate_map _167_29 f l))
in (FStar_Pprint.group _167_30)))


let precede_break_separate_map = (fun prec sep f l -> (let _167_47 = (let _167_40 = (FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space)
in (let _167_39 = (let _167_38 = (FStar_List.hd l)
in (FStar_All.pipe_right _167_38 f))
in (FStar_Pprint.precede _167_40 _167_39)))
in (let _167_46 = (let _167_45 = (FStar_List.tl l)
in (FStar_Pprint.concat_map (fun x -> (let _167_44 = (let _167_43 = (let _167_42 = (f x)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_42))
in (FStar_Pprint.op_Hat_Hat sep _167_43))
in (FStar_Pprint.op_Hat_Hat break1 _167_44))) _167_45))
in (FStar_Pprint.op_Hat_Hat _167_47 _167_46))))


let concat_break_map = (fun f l -> (let _167_55 = (FStar_Pprint.concat_map (fun x -> (let _167_54 = (f x)
in (FStar_Pprint.op_Hat_Hat _167_54 break1))) l)
in (FStar_Pprint.group _167_55)))


let parens_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lparen contents FStar_Pprint.rparen))


let braces_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbrace contents FStar_Pprint.rbrace))


let brackets_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbracket contents FStar_Pprint.rbracket))


let separate_map_or_flow = (fun sep f l -> if ((FStar_List.length l) < (Prims.parse_int "10")) then begin
(FStar_Pprint.separate_map sep f l)
end else begin
(FStar_Pprint.flow_map sep f l)
end)


let doc_of_fsdoc : (Prims.string * (Prims.string * Prims.string) Prims.list)  ->  FStar_Pprint.document = (fun _68_51 -> (match (_68_51) with
| (comment, keywords) -> begin
(let _167_81 = (let _167_80 = (let _167_79 = (str comment)
in (let _167_78 = (let _167_77 = (let _167_76 = (FStar_Pprint.separate_map FStar_Pprint.comma (fun _68_54 -> (match (_68_54) with
| (k, v) -> begin
(let _167_75 = (let _167_74 = (str k)
in (let _167_73 = (let _167_72 = (let _167_71 = (str v)
in (_167_71)::[])
in (FStar_Pprint.rarrow)::_167_72)
in (_167_74)::_167_73))
in (FStar_Pprint.concat _167_75))
end)) keywords)
in (_167_76)::[])
in (FStar_Pprint.space)::_167_77)
in (_167_79)::_167_78))
in (FStar_Pprint.concat _167_80))
in (FStar_Pprint.group _167_81))
end))


let is_unit : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Const (FStar_Const.Const_unit) -> begin
true
end
| _68_59 -> begin
false
end))


let matches_var : FStar_Parser_AST.term  ->  FStar_Ident.ident  ->  Prims.bool = (fun t x -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (y) -> begin
(x.FStar_Ident.idText = (FStar_Ident.text_of_lid y))
end
| _68_65 -> begin
false
end))


let is_tuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Syntax_Util.is_tuple_data_lid'


let is_dtuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Syntax_Util.is_dtuple_data_lid'


let is_list_structure : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun cons_lid nil_lid -> (

let rec aux = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (lid, []) -> begin
(FStar_Ident.lid_equals lid nil_lid)
end
| FStar_Parser_AST.Construct (lid, (_68_80)::((e2, _68_77))::[]) -> begin
((FStar_Ident.lid_equals lid cons_lid) && (aux e2))
end
| _68_85 -> begin
false
end))
in aux))


let is_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Syntax_Const.cons_lid FStar_Syntax_Const.nil_lid)


let is_lex_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Syntax_Const.lexcons_lid FStar_Syntax_Const.lextop_lid)


let rec extract_from_list : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (_68_88, []) -> begin
[]
end
| FStar_Parser_AST.Construct (_68_93, ((e1, FStar_Parser_AST.Nothing))::((e2, FStar_Parser_AST.Nothing))::[]) -> begin
(let _167_104 = (extract_from_list e2)
in (e1)::_167_104)
end
| _68_104 -> begin
(let _167_106 = (let _167_105 = (FStar_Parser_AST.term_to_string e)
in (FStar_Util.format1 "Not a list %s" _167_105))
in (failwith _167_106))
end))


let is_array : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (lid); FStar_Parser_AST.range = _68_109; FStar_Parser_AST.level = _68_107}, l, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals lid FStar_Syntax_Const.array_mk_array_lid) && (is_list l))
end
| _68_118 -> begin
false
end))


let rec is_ref_set : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (maybe_empty_lid) -> begin
(FStar_Ident.lid_equals maybe_empty_lid FStar_Syntax_Const.tset_empty)
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_singleton_lid); FStar_Parser_AST.range = _68_125; FStar_Parser_AST.level = _68_123}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_ref_lid); FStar_Parser_AST.range = _68_136; FStar_Parser_AST.level = _68_134}, e, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = _68_132; FStar_Parser_AST.level = _68_130}, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals maybe_singleton_lid FStar_Syntax_Const.tset_singleton) && (FStar_Ident.lid_equals maybe_ref_lid FStar_Syntax_Const.heap_ref))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_union_lid); FStar_Parser_AST.range = _68_155; FStar_Parser_AST.level = _68_153}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = _68_151; FStar_Parser_AST.level = _68_149}, e2, FStar_Parser_AST.Nothing) -> begin
(((FStar_Ident.lid_equals maybe_union_lid FStar_Syntax_Const.tset_union) && (is_ref_set e1)) && (is_ref_set e2))
end
| _68_169 -> begin
false
end))


let rec extract_from_ref_set : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (_68_172) -> begin
[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (_68_179); FStar_Parser_AST.range = _68_177; FStar_Parser_AST.level = _68_175}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (_68_191); FStar_Parser_AST.range = _68_189; FStar_Parser_AST.level = _68_187}, e, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = _68_185; FStar_Parser_AST.level = _68_183}, FStar_Parser_AST.Nothing) -> begin
(e)::[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (_68_211); FStar_Parser_AST.range = _68_209; FStar_Parser_AST.level = _68_207}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = _68_205; FStar_Parser_AST.level = _68_203}, e2, FStar_Parser_AST.Nothing) -> begin
(let _167_114 = (extract_from_ref_set e1)
in (let _167_113 = (extract_from_ref_set e2)
in (FStar_List.append _167_114 _167_113)))
end
| _68_224 -> begin
(let _167_116 = (let _167_115 = (FStar_Parser_AST.term_to_string e)
in (FStar_Util.format1 "Not a ref set %s" _167_115))
in (failwith _167_116))
end))


let is_general_application : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (not (((is_array e) || (is_ref_set e)))))


let is_general_construction : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (not (((is_list e) || (is_lex_list e)))))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun e -> (

let rec aux = (fun e acc -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App (head, arg, imp) -> begin
(aux head ((((arg), (imp)))::acc))
end
| _68_237 -> begin
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


let token_to_string : (FStar_BaseTypes.char, Prims.string) FStar_Util.either  ->  Prims.string = (fun _68_1 -> (match (_68_1) with
| FStar_Util.Inl (c) -> begin
(Prims.strcat (FStar_Util.string_of_char c) ".*")
end
| FStar_Util.Inr (s) -> begin
s
end))


let matches_token : Prims.string  ->  (FStar_Char.char, Prims.string) FStar_Util.either  ->  Prims.bool = (fun s _68_2 -> (match (_68_2) with
| FStar_Util.Inl (c) -> begin
((FStar_String.get s (Prims.parse_int "0")) = c)
end
| FStar_Util.Inr (s') -> begin
(s = s')
end))


let matches_level = (fun s _68_252 -> (match (_68_252) with
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

let levels_from_associativity = (fun l _68_3 -> (match (_68_3) with
| Left -> begin
((l), (l), ((l - (Prims.parse_int "1"))))
end
| Right -> begin
(((l - (Prims.parse_int "1"))), (l), (l))
end
| NonAssoc -> begin
((l), (l), (l))
end))
in (FStar_List.mapi (fun i _68_262 -> (match (_68_262) with
| (assoc, tokens) -> begin
(((levels_from_associativity i assoc)), (tokens))
end)) level_associativity_spec))


let assign_levels : associativity_level Prims.list  ->  Prims.string  ->  (Prims.int * Prims.int * Prims.int) = (fun token_associativity_spec s -> (match ((FStar_List.tryFind (matches_level s) level_table)) with
| Some (assoc_levels, _68_267) -> begin
assoc_levels
end
| _68_271 -> begin
(failwith (Prims.strcat "Unrecognized operator " s))
end))


let max : Prims.int  ->  Prims.int  ->  Prims.int = (fun k1 k2 -> if (k1 > k2) then begin
k1
end else begin
k2
end)


let max_level = (fun l -> (

let find_level_and_max = (fun n level -> (match ((FStar_List.tryFind (fun _68_281 -> (match (_68_281) with
| (_68_279, tokens) -> begin
(tokens = (Prims.snd level))
end)) level_table)) with
| Some ((_68_283, l, _68_286), _68_289) -> begin
(max n l)
end
| None -> begin
(let _167_160 = (let _167_159 = (let _167_158 = (FStar_List.map token_to_string (Prims.snd level))
in (FStar_String.concat "," _167_158))
in (FStar_Util.format1 "Undefined associativity level %s" _167_159))
in (failwith _167_160))
end))
in (FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l)))


let levels : Prims.string  ->  (Prims.int * Prims.int * Prims.int) = (assign_levels level_associativity_spec)


let operatorInfix0ad12 = (opinfix0a)::(opinfix0b)::(opinfix0c)::(opinfix0d)::(opinfix1)::(opinfix2)::[]


let is_operatorInfix0ad12 : Prims.string  ->  Prims.bool = (fun op -> ((FStar_List.tryFind (matches_level op) operatorInfix0ad12) <> None))


let is_operatorInfix34 : Prims.string  ->  Prims.bool = (

let opinfix34 = (opinfix3)::(opinfix4)::[]
in (fun op -> ((FStar_List.tryFind (matches_level op) opinfix34) <> None)))


let doc_of_let_qualifier : FStar_Parser_AST.let_qualifier  ->  FStar_Pprint.document = (fun _68_4 -> (match (_68_4) with
| FStar_Parser_AST.NoLetQualifier -> begin
FStar_Pprint.empty
end
| FStar_Parser_AST.Rec -> begin
(str "rec")
end
| FStar_Parser_AST.Mutable -> begin
(str "mutable")
end))


let doc_of_imp : FStar_Parser_AST.imp  ->  FStar_Pprint.document = (fun _68_5 -> (match (_68_5) with
| FStar_Parser_AST.Hash -> begin
(str "#")
end
| FStar_Parser_AST.UnivApp -> begin
(str "u#")
end
| (FStar_Parser_AST.Nothing) | (FStar_Parser_AST.FsTypApp) -> begin
FStar_Pprint.empty
end))


let rec p_decl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (let _167_271 = (FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc)
in (let _167_270 = (let _167_269 = (p_attributes d.FStar_Parser_AST.attrs)
in (let _167_268 = (let _167_267 = (p_qualifiers d.FStar_Parser_AST.quals)
in (let _167_266 = (let _167_265 = (p_rawDecl d)
in (FStar_Pprint.op_Hat_Hat (if (d.FStar_Parser_AST.quals = []) then begin
FStar_Pprint.empty
end else begin
break1
end) _167_265))
in (FStar_Pprint.op_Hat_Hat _167_267 _167_266)))
in (FStar_Pprint.op_Hat_Hat _167_269 _167_268)))
in (FStar_Pprint.op_Hat_Hat _167_271 _167_270))))
and p_attributes : FStar_Parser_AST.attributes_  ->  FStar_Pprint.document = (fun attrs -> (let _167_275 = (let _167_273 = (str "@")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket _167_273))
in (let _167_274 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline)
in (FStar_Pprint.surround_separate_map (Prims.parse_int "0") (Prims.parse_int "2") FStar_Pprint.empty _167_275 FStar_Pprint.space _167_274 p_atomicTerm attrs))))
and p_fsdoc : FStar_Parser_AST.fsdoc  ->  FStar_Pprint.document = (fun _68_309 -> (match (_68_309) with
| (doc, kwd_args) -> begin
(

let kwd_args_doc = (match (kwd_args) with
| [] -> begin
FStar_Pprint.empty
end
| kwd_args -> begin
(

let process_kwd_arg = (fun _68_315 -> (match (_68_315) with
| (kwd, arg) -> begin
(let _167_283 = (str "@")
in (let _167_282 = (let _167_281 = (str kwd)
in (let _167_280 = (let _167_279 = (str arg)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_279))
in (FStar_Pprint.op_Hat_Hat _167_281 _167_280)))
in (FStar_Pprint.op_Hat_Hat _167_283 _167_282)))
end))
in (let _167_285 = (let _167_284 = (FStar_Pprint.separate_map FStar_Pprint.hardline process_kwd_arg kwd_args)
in (FStar_Pprint.op_Hat_Hat _167_284 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline _167_285)))
end)
in (let _167_293 = (let _167_292 = (let _167_291 = (let _167_290 = (let _167_289 = (str doc)
in (let _167_288 = (let _167_287 = (let _167_286 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _167_286))
in (FStar_Pprint.op_Hat_Hat kwd_args_doc _167_287))
in (FStar_Pprint.op_Hat_Hat _167_289 _167_288)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _167_290))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _167_291))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _167_292))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline _167_293)))
end))
and p_rawDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Open (uid) -> begin
(let _167_297 = (let _167_296 = (str "open")
in (let _167_295 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat _167_296 _167_295)))
in (FStar_Pprint.group _167_297))
end
| FStar_Parser_AST.Include (uid) -> begin
(let _167_300 = (let _167_299 = (str "include")
in (let _167_298 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat _167_299 _167_298)))
in (FStar_Pprint.group _167_300))
end
| FStar_Parser_AST.ModuleAbbrev (uid1, uid2) -> begin
(let _167_307 = (let _167_305 = (str "module")
in (let _167_304 = (let _167_303 = (let _167_302 = (p_uident uid1)
in (let _167_301 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _167_302 _167_301)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_303))
in (FStar_Pprint.op_Hat_Hat _167_305 _167_304)))
in (let _167_306 = (p_quident uid2)
in (op_Hat_Slash_Plus_Hat _167_307 _167_306)))
end
| FStar_Parser_AST.TopLevelModule (uid) -> begin
(let _167_311 = (let _167_310 = (str "module")
in (let _167_309 = (let _167_308 = (p_quident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_308))
in (FStar_Pprint.op_Hat_Hat _167_310 _167_309)))
in (FStar_Pprint.group _167_311))
end
| FStar_Parser_AST.KindAbbrev (_68_329) -> begin
(failwith "Deprecated, please stop throwing your old stuff at me !")
end
| FStar_Parser_AST.Tycon (true, ((FStar_Parser_AST.TyconAbbrev (uid, tpars, None, t), None))::[]) -> begin
(

let effect_prefix_doc = (let _167_314 = (str "effect")
in (let _167_313 = (let _167_312 = (p_uident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_312))
in (FStar_Pprint.op_Hat_Hat _167_314 _167_313)))
in (let _167_317 = (let _167_315 = (p_typars tpars)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") effect_prefix_doc _167_315 FStar_Pprint.equals))
in (let _167_316 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _167_317 _167_316))))
end
| FStar_Parser_AST.Tycon (false, tcdefs) -> begin
(let _167_319 = (str "type")
in (let _167_318 = (str "and")
in (precede_break_separate_map _167_319 _167_318 p_fsdocTypeDeclPairs tcdefs)))
end
| FStar_Parser_AST.TopLevelLet (q, lbs) -> begin
(

let let_doc = (let _167_321 = (str "let")
in (let _167_320 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat _167_321 _167_320)))
in (let _167_322 = (str "and")
in (precede_break_separate_map let_doc _167_322 p_letbinding lbs)))
end
| FStar_Parser_AST.Val (lid, t) -> begin
(let _167_329 = (let _167_327 = (str "val")
in (let _167_326 = (let _167_325 = (let _167_324 = (p_lident lid)
in (let _167_323 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat _167_324 _167_323)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_325))
in (FStar_Pprint.op_Hat_Hat _167_327 _167_326)))
in (let _167_328 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _167_329 _167_328)))
end
| FStar_Parser_AST.Assume (id, t) -> begin
(

let decl_keyword = if (let _167_330 = (FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_All.pipe_right _167_330 FStar_Util.is_upper)) then begin
FStar_Pprint.empty
end else begin
(let _167_331 = (str "val")
in (FStar_Pprint.op_Hat_Hat _167_331 FStar_Pprint.space))
end
in (let _167_336 = (let _167_334 = (let _167_333 = (p_ident id)
in (let _167_332 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat _167_333 _167_332)))
in (FStar_Pprint.op_Hat_Hat decl_keyword _167_334))
in (let _167_335 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _167_336 _167_335))))
end
| FStar_Parser_AST.Exception (uid, t_opt) -> begin
(let _167_344 = (str "exception")
in (let _167_343 = (let _167_342 = (let _167_341 = (p_uident uid)
in (let _167_340 = (FStar_Pprint.optional (fun t -> (let _167_339 = (str "of")
in (let _167_338 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _167_339 _167_338)))) t_opt)
in (FStar_Pprint.op_Hat_Hat _167_341 _167_340)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_342))
in (FStar_Pprint.op_Hat_Hat _167_344 _167_343)))
end
| FStar_Parser_AST.NewEffect (ne) -> begin
(let _167_347 = (str "new_effect")
in (let _167_346 = (let _167_345 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_345))
in (FStar_Pprint.op_Hat_Hat _167_347 _167_346)))
end
| FStar_Parser_AST.SubEffect (se) -> begin
(let _167_350 = (str "sub_effect")
in (let _167_349 = (let _167_348 = (p_subEffect se)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_348))
in (FStar_Pprint.op_Hat_Hat _167_350 _167_349)))
end
| FStar_Parser_AST.NewEffectForFree (ne) -> begin
(let _167_353 = (str "new_effect_for_free")
in (let _167_352 = (let _167_351 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_351))
in (FStar_Pprint.op_Hat_Hat _167_353 _167_352)))
end
| FStar_Parser_AST.Pragma (p) -> begin
(p_pragma p)
end
| FStar_Parser_AST.Fsdoc (doc) -> begin
(let _167_354 = (p_fsdoc doc)
in (FStar_Pprint.op_Hat_Hat _167_354 FStar_Pprint.hardline))
end
| FStar_Parser_AST.Main (_68_378) -> begin
(failwith "*Main declaration* : Is that really still in use ??")
end
| FStar_Parser_AST.Tycon (true, _68_382) -> begin
(failwith "Effect abbreviation is expected to be defined by an abbreviation")
end))
and p_pragma : FStar_Parser_AST.pragma  ->  FStar_Pprint.document = (fun _68_6 -> (match (_68_6) with
| FStar_Parser_AST.SetOptions (s) -> begin
(let _167_359 = (str "#set-options")
in (let _167_358 = (let _167_357 = (let _167_356 = (str s)
in (FStar_Pprint.dquotes _167_356))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_357))
in (FStar_Pprint.op_Hat_Hat _167_359 _167_358)))
end
| FStar_Parser_AST.ResetOptions (s_opt) -> begin
(let _167_364 = (str "#reset-options")
in (let _167_363 = (FStar_Pprint.optional (fun s -> (let _167_362 = (let _167_361 = (str s)
in (FStar_Pprint.dquotes _167_361))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_362))) s_opt)
in (FStar_Pprint.op_Hat_Hat _167_364 _167_363)))
end))
and p_typars : FStar_Parser_AST.binder Prims.list  ->  FStar_Pprint.document = (fun bs -> (p_binders true bs))
and p_fsdocTypeDeclPairs : (FStar_Parser_AST.tycon * FStar_Parser_AST.fsdoc Prims.option)  ->  FStar_Pprint.document = (fun _68_394 -> (match (_68_394) with
| (typedecl, fsdoc_opt) -> begin
(let _167_368 = (FStar_Pprint.optional p_fsdoc fsdoc_opt)
in (let _167_367 = (p_typeDecl typedecl)
in (FStar_Pprint.op_Hat_Hat _167_368 _167_367)))
end))
and p_typeDecl : FStar_Parser_AST.tycon  ->  FStar_Pprint.document = (fun _68_7 -> (match (_68_7) with
| FStar_Parser_AST.TyconAbstract (lid, bs, typ_opt) -> begin
(p_typeDeclPrefix lid bs typ_opt FStar_Pprint.empty)
end
| FStar_Parser_AST.TyconAbbrev (lid, bs, typ_opt, t) -> begin
(let _167_371 = (let _167_370 = (p_typ t)
in (prefix2 FStar_Pprint.equals _167_370))
in (p_typeDeclPrefix lid bs typ_opt _167_371))
end
| FStar_Parser_AST.TyconRecord (lid, bs, typ_opt, record_field_decls) -> begin
(let _167_376 = (let _167_375 = (let _167_374 = (let _167_373 = (let _167_372 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (FStar_Pprint.separate_map _167_372 p_recordFieldDecl record_field_decls))
in (braces_with_nesting _167_373))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_374))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.equals _167_375))
in (p_typeDeclPrefix lid bs typ_opt _167_376))
end
| FStar_Parser_AST.TyconVariant (lid, bs, typ_opt, ct_decls) -> begin
(

let datacon_doc = (let _167_381 = (FStar_Pprint.separate_map break1 (fun decl -> (let _167_380 = (let _167_379 = (let _167_378 = (p_constructorDecl decl)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_378))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar _167_379))
in (FStar_Pprint.group _167_380))) ct_decls)
in (FStar_Pprint.group _167_381))
in (let _167_382 = (prefix2 FStar_Pprint.equals datacon_doc)
in (p_typeDeclPrefix lid bs typ_opt _167_382)))
end))
and p_typeDeclPrefix : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.knd Prims.option  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun lid bs typ_opt cont -> if ((bs = []) && (typ_opt = None)) then begin
(let _167_388 = (p_ident lid)
in (let _167_387 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space cont)
in (FStar_Pprint.op_Hat_Hat _167_388 _167_387)))
end else begin
(

let binders_doc = (let _167_394 = (p_typars bs)
in (let _167_393 = (FStar_Pprint.optional (fun t -> (let _167_392 = (let _167_391 = (let _167_390 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_390))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _167_391))
in (FStar_Pprint.op_Hat_Hat break1 _167_392))) typ_opt)
in (FStar_Pprint.op_Hat_Hat _167_394 _167_393)))
in (let _167_395 = (p_ident lid)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _167_395 binders_doc cont)))
end)
and p_recordFieldDecl : (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc Prims.option)  ->  FStar_Pprint.document = (fun _68_430 -> (match (_68_430) with
| (lid, t, doc_opt) -> begin
(let _167_402 = (let _167_401 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (let _167_400 = (let _167_399 = (p_lident lid)
in (let _167_398 = (let _167_397 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _167_397))
in (FStar_Pprint.op_Hat_Hat _167_399 _167_398)))
in (FStar_Pprint.op_Hat_Hat _167_401 _167_400)))
in (FStar_Pprint.group _167_402))
end))
and p_constructorDecl : (FStar_Ident.ident * FStar_Parser_AST.term Prims.option * FStar_Parser_AST.fsdoc Prims.option * Prims.bool)  ->  FStar_Pprint.document = (fun _68_435 -> (match (_68_435) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let sep = if use_of then begin
(str "of")
end else begin
FStar_Pprint.colon
end
in (

let uid_doc = (p_uident uid)
in (let _167_409 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (let _167_408 = (default_or_map uid_doc (fun t -> (let _167_407 = (let _167_405 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep)
in (FStar_Pprint.op_Hat_Hat uid_doc _167_405))
in (let _167_406 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _167_407 _167_406)))) t_opt)
in (FStar_Pprint.op_Hat_Hat _167_409 _167_408)))))
end))
and p_letbinding : (FStar_Parser_AST.pattern * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun _68_441 -> (match (_68_441) with
| (pat, e) -> begin
(

let pat_doc = (

let _68_450 = (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, t) -> begin
(let _167_414 = (let _167_413 = (let _167_412 = (let _167_411 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat break1 _167_411))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _167_412))
in (FStar_Pprint.op_Hat_Hat break1 _167_413))
in ((pat), (_167_414)))
end
| _68_447 -> begin
((pat), (FStar_Pprint.empty))
end)
in (match (_68_450) with
| (pat, ascr_doc) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _68_455); FStar_Parser_AST.prange = _68_452}, pats) -> begin
(let _167_417 = (p_lident x)
in (let _167_416 = (let _167_415 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Hat _167_415 ascr_doc))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _167_417 _167_416 FStar_Pprint.equals)))
end
| _68_463 -> begin
(let _167_420 = (let _167_419 = (p_tuplePattern pat)
in (let _167_418 = (FStar_Pprint.op_Hat_Slash_Hat ascr_doc FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _167_419 _167_418)))
in (FStar_Pprint.group _167_420))
end)
end))
in (let _167_421 = (p_term e)
in (prefix2 pat_doc _167_421)))
end))
and p_newEffect : FStar_Parser_AST.effect_decl  ->  FStar_Pprint.document = (fun _68_8 -> (match (_68_8) with
| FStar_Parser_AST.RedefineEffect (lid, bs, t) -> begin
(p_effectRedefinition lid bs t)
end
| FStar_Parser_AST.DefineEffect (lid, bs, t, eff_decls, action_decls) -> begin
(p_effectDefinition lid bs t eff_decls action_decls)
end))
and p_effectRedefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun uid bs t -> (let _167_429 = (p_uident uid)
in (let _167_428 = (p_binders true bs)
in (let _167_427 = (let _167_426 = (p_simpleTerm t)
in (prefix2 FStar_Pprint.equals _167_426))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _167_429 _167_428 _167_427)))))
and p_effectDefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun uid bs t eff_decls action_decls -> (let _167_446 = (let _167_445 = (let _167_439 = (let _167_438 = (p_uident uid)
in (let _167_437 = (p_binders true bs)
in (let _167_436 = (let _167_435 = (p_typ t)
in (prefix2 FStar_Pprint.colon _167_435))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _167_438 _167_437 _167_436))))
in (FStar_Pprint.group _167_439))
in (let _167_444 = (let _167_443 = (let _167_441 = (str "with")
in (let _167_440 = (separate_break_map FStar_Pprint.semi p_effectDecl eff_decls)
in (prefix2 _167_441 _167_440)))
in (let _167_442 = (p_actionDecls action_decls)
in (FStar_Pprint.op_Hat_Hat _167_443 _167_442)))
in (FStar_Pprint.op_Hat_Slash_Hat _167_445 _167_444)))
in (braces_with_nesting _167_446)))
and p_actionDecls : FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun _68_9 -> (match (_68_9) with
| [] -> begin
FStar_Pprint.empty
end
| l -> begin
(let _167_450 = (let _167_449 = (str "and actions")
in (let _167_448 = (separate_break_map FStar_Pprint.semi p_effectDecl l)
in (prefix2 _167_449 _167_448)))
in (FStar_Pprint.op_Hat_Hat break1 _167_450))
end))
and p_effectDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (false, ((FStar_Parser_AST.TyconAbbrev (lid, [], None, e), None))::[]) -> begin
(let _167_455 = (let _167_453 = (p_lident lid)
in (let _167_452 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _167_453 _167_452)))
in (let _167_454 = (p_simpleTerm e)
in (prefix2 _167_455 _167_454)))
end
| _68_503 -> begin
(let _167_457 = (let _167_456 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "Not a declaration of an effect member... or at least I hope so : %s" _167_456))
in (failwith _167_457))
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

let p_lift = (fun _68_517 -> (match (_68_517) with
| (kwd, t) -> begin
(let _167_464 = (let _167_462 = (str kwd)
in (let _167_461 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _167_462 _167_461)))
in (let _167_463 = (p_simpleTerm t)
in (prefix2 _167_464 _167_463)))
end))
in (separate_break_map FStar_Pprint.semi p_lift lifts)))
in (let _167_472 = (let _167_469 = (let _167_467 = (p_quident lift.FStar_Parser_AST.msource)
in (let _167_466 = (let _167_465 = (str "~>")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_465))
in (FStar_Pprint.op_Hat_Hat _167_467 _167_466)))
in (let _167_468 = (p_quident lift.FStar_Parser_AST.mdest)
in (prefix2 _167_469 _167_468)))
in (let _167_471 = (let _167_470 = (braces_with_nesting lift_op_doc)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_470))
in (FStar_Pprint.op_Hat_Hat _167_472 _167_471)))))
and p_qualifier : FStar_Parser_AST.qualifier  ->  FStar_Pprint.document = (fun _68_10 -> (match (_68_10) with
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
and p_qualifiers : FStar_Parser_AST.qualifiers  ->  FStar_Pprint.document = (fun qs -> (let _167_476 = (let _167_475 = (FStar_Pprint.separate_map break1 p_qualifier qs)
in (FStar_Pprint.op_Hat_Hat _167_475 (if (qs = []) then begin
FStar_Pprint.empty
end else begin
FStar_Pprint.space
end)))
in (FStar_Pprint.group _167_476)))
and p_letqualifier : FStar_Parser_AST.let_qualifier  ->  FStar_Pprint.document = (fun _68_11 -> (match (_68_11) with
| FStar_Parser_AST.Rec -> begin
(let _167_478 = (str "rec")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_478))
end
| FStar_Parser_AST.Mutable -> begin
(let _167_479 = (str "mutable")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_479))
end
| FStar_Parser_AST.NoLetQualifier -> begin
FStar_Pprint.empty
end))
and p_aqual : FStar_Parser_AST.arg_qualifier  ->  FStar_Pprint.document = (fun _68_12 -> (match (_68_12) with
| FStar_Parser_AST.Implicit -> begin
(str "#")
end
| FStar_Parser_AST.Equality -> begin
(str "$")
end))
and p_disjunctivePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr (pats) -> begin
(let _167_484 = (let _167_483 = (let _167_482 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space)
in (FStar_Pprint.op_Hat_Hat break1 _167_482))
in (FStar_Pprint.separate_map _167_483 p_tuplePattern pats))
in (FStar_Pprint.group _167_484))
end
| _68_551 -> begin
(p_tuplePattern p)
end))
and p_tuplePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTuple (pats, false) -> begin
(let _167_487 = (let _167_486 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map _167_486 p_constructorPattern pats))
in (FStar_Pprint.group _167_487))
end
| _68_558 -> begin
(p_constructorPattern p)
end))
and p_constructorPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (maybe_cons_lid); FStar_Parser_AST.prange = _68_561}, (hd)::(tl)::[]) when (FStar_Ident.lid_equals maybe_cons_lid FStar_Syntax_Const.cons_lid) -> begin
(let _167_491 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon)
in (let _167_490 = (p_constructorPattern hd)
in (let _167_489 = (p_constructorPattern tl)
in (infix2 _167_491 _167_490 _167_489))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (uid); FStar_Parser_AST.prange = _68_571}, pats) -> begin
(let _167_493 = (p_quident uid)
in (let _167_492 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (prefix2 _167_493 _167_492)))
end
| _68_579 -> begin
(p_atomicPattern p)
end))
and p_atomicPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, t) -> begin
(let _167_497 = (let _167_496 = (p_tuplePattern pat)
in (let _167_495 = (p_typ t)
in (infix2 FStar_Pprint.colon _167_496 _167_495)))
in (parens_with_nesting _167_497))
end
| FStar_Parser_AST.PatList (pats) -> begin
(let _167_498 = (separate_break_map FStar_Pprint.semi p_tuplePattern pats)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket _167_498 FStar_Pprint.rbracket))
end
| FStar_Parser_AST.PatRecord (pats) -> begin
(

let p_recordFieldPat = (fun _68_592 -> (match (_68_592) with
| (lid, pat) -> begin
(let _167_502 = (p_qlident lid)
in (let _167_501 = (p_tuplePattern pat)
in (infix2 FStar_Pprint.equals _167_502 _167_501)))
end))
in (let _167_503 = (separate_break_map FStar_Pprint.semi p_recordFieldPat pats)
in (braces_with_nesting _167_503)))
end
| FStar_Parser_AST.PatTuple (pats, true) -> begin
(let _167_506 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (let _167_505 = (separate_break_map FStar_Pprint.comma p_constructorPattern pats)
in (let _167_504 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _167_506 _167_505 _167_504))))
end
| FStar_Parser_AST.PatTvar (tv, arg_qualifier_opt) -> begin
(

let _68_601 = ()
in (p_tvar tv))
end
| FStar_Parser_AST.PatOp (op) -> begin
(let _167_510 = (let _167_509 = (let _167_508 = (str op)
in (let _167_507 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat _167_508 _167_507)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_509))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _167_510))
end
| FStar_Parser_AST.PatWild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.PatConst (c) -> begin
(p_constant c)
end
| FStar_Parser_AST.PatVar (lid, aqual) -> begin
(let _167_512 = (FStar_Pprint.optional p_aqual aqual)
in (let _167_511 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat _167_512 _167_511)))
end
| FStar_Parser_AST.PatName (uid) -> begin
(p_quident uid)
end
| FStar_Parser_AST.PatOr (_68_615) -> begin
(failwith "Inner or pattern !")
end
| (FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (_); FStar_Parser_AST.prange = _}, _)) | (FStar_Parser_AST.PatTuple (_, false)) -> begin
(let _167_513 = (p_tuplePattern p)
in (parens_with_nesting _167_513))
end
| _68_633 -> begin
(let _167_515 = (let _167_514 = (FStar_Parser_AST.pat_to_string p)
in (FStar_Util.format1 "Invalid pattern %s" _167_514))
in (failwith _167_515))
end))
and p_binder : Prims.bool  ->  FStar_Parser_AST.binder  ->  FStar_Pprint.document = (fun is_atomic b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (lid) -> begin
(let _167_519 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (let _167_518 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat _167_519 _167_518)))
end
| FStar_Parser_AST.TVariable (lid) -> begin
(p_lident lid)
end
| FStar_Parser_AST.Annotated (lid, t) -> begin
(

let doc = (let _167_524 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (let _167_523 = (let _167_522 = (p_lident lid)
in (let _167_521 = (let _167_520 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _167_520))
in (FStar_Pprint.op_Hat_Hat _167_522 _167_521)))
in (FStar_Pprint.op_Hat_Hat _167_524 _167_523)))
in if is_atomic then begin
(let _167_526 = (let _167_525 = (FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _167_525))
in (FStar_Pprint.group _167_526))
end else begin
(FStar_Pprint.group doc)
end)
end
| FStar_Parser_AST.TAnnotated (_68_646) -> begin
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
(let _167_540 = (let _167_538 = (let _167_537 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat _167_537 FStar_Pprint.semi))
in (FStar_Pprint.group _167_538))
in (let _167_539 = (p_term e2)
in (FStar_Pprint.op_Hat_Slash_Hat _167_540 _167_539)))
end
| _68_665 -> begin
(let _167_541 = (p_noSeqTerm e)
in (FStar_Pprint.group _167_541))
end))
and p_noSeqTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Ascribed (e, t) -> begin
(let _167_547 = (let _167_546 = (p_tmIff e)
in (let _167_545 = (let _167_544 = (let _167_543 = (p_typ t)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon _167_543))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.langle _167_544))
in (FStar_Pprint.op_Hat_Slash_Hat _167_546 _167_545)))
in (FStar_Pprint.group _167_547))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::(e3)::[]) when (op = ".()<-") -> begin
(let _167_558 = (let _167_557 = (let _167_554 = (let _167_553 = (p_atomicTermNotQUident e1)
in (let _167_552 = (let _167_551 = (let _167_550 = (let _167_548 = (p_term e2)
in (parens_with_nesting _167_548))
in (let _167_549 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat _167_550 _167_549)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _167_551))
in (FStar_Pprint.op_Hat_Hat _167_553 _167_552)))
in (FStar_Pprint.group _167_554))
in (let _167_556 = (let _167_555 = (p_noSeqTerm e3)
in (jump2 _167_555))
in (FStar_Pprint.op_Hat_Hat _167_557 _167_556)))
in (FStar_Pprint.group _167_558))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::(e3)::[]) when (op = ".[]<-") -> begin
(let _167_569 = (let _167_568 = (let _167_565 = (let _167_564 = (p_atomicTermNotQUident e1)
in (let _167_563 = (let _167_562 = (let _167_561 = (let _167_559 = (p_term e2)
in (brackets_with_nesting _167_559))
in (let _167_560 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat _167_561 _167_560)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _167_562))
in (FStar_Pprint.op_Hat_Hat _167_564 _167_563)))
in (FStar_Pprint.group _167_565))
in (let _167_567 = (let _167_566 = (p_noSeqTerm e3)
in (jump2 _167_566))
in (FStar_Pprint.op_Hat_Hat _167_568 _167_567)))
in (FStar_Pprint.group _167_569))
end
| FStar_Parser_AST.Requires (e, wtf) -> begin
(

let _68_689 = ()
in (let _167_572 = (let _167_571 = (str "requires")
in (let _167_570 = (p_typ e)
in (FStar_Pprint.op_Hat_Slash_Hat _167_571 _167_570)))
in (FStar_Pprint.group _167_572)))
end
| FStar_Parser_AST.Ensures (e, wtf) -> begin
(

let _68_695 = ()
in (let _167_575 = (let _167_574 = (str "ensures")
in (let _167_573 = (p_typ e)
in (FStar_Pprint.op_Hat_Slash_Hat _167_574 _167_573)))
in (FStar_Pprint.group _167_575)))
end
| FStar_Parser_AST.Attributes (es) -> begin
(let _167_578 = (let _167_577 = (str "attributes")
in (let _167_576 = (FStar_Pprint.separate_map break1 p_atomicTerm es)
in (FStar_Pprint.op_Hat_Slash_Hat _167_577 _167_576)))
in (FStar_Pprint.group _167_578))
end
| FStar_Parser_AST.If (e1, e2, e3) -> begin
if (is_unit e3) then begin
(let _167_585 = (let _167_584 = (let _167_580 = (str "if")
in (let _167_579 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat _167_580 _167_579)))
in (let _167_583 = (let _167_582 = (str "then")
in (let _167_581 = (p_noSeqTerm e2)
in (op_Hat_Slash_Plus_Hat _167_582 _167_581)))
in (FStar_Pprint.op_Hat_Slash_Hat _167_584 _167_583)))
in (FStar_Pprint.group _167_585))
end else begin
(

let e2_doc = (match (e2.FStar_Parser_AST.tm) with
| FStar_Parser_AST.If (_68_705, _68_707, e3) when (is_unit e3) -> begin
(let _167_586 = (p_noSeqTerm e2)
in (parens_with_nesting _167_586))
end
| _68_712 -> begin
(p_noSeqTerm e2)
end)
in (let _167_596 = (let _167_595 = (let _167_588 = (str "if")
in (let _167_587 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat _167_588 _167_587)))
in (let _167_594 = (let _167_593 = (let _167_589 = (str "then")
in (op_Hat_Slash_Plus_Hat _167_589 e2_doc))
in (let _167_592 = (let _167_591 = (str "else")
in (let _167_590 = (p_noSeqTerm e3)
in (op_Hat_Slash_Plus_Hat _167_591 _167_590)))
in (FStar_Pprint.op_Hat_Slash_Hat _167_593 _167_592)))
in (FStar_Pprint.op_Hat_Slash_Hat _167_595 _167_594)))
in (FStar_Pprint.group _167_596)))
end
end
| FStar_Parser_AST.TryWith (e, branches) -> begin
(let _167_603 = (let _167_602 = (let _167_598 = (str "try")
in (let _167_597 = (p_noSeqTerm e)
in (prefix2 _167_598 _167_597)))
in (let _167_601 = (let _167_600 = (str "with")
in (let _167_599 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat _167_600 _167_599)))
in (FStar_Pprint.op_Hat_Slash_Hat _167_602 _167_601)))
in (FStar_Pprint.group _167_603))
end
| FStar_Parser_AST.Match (e, branches) -> begin
(let _167_609 = (let _167_608 = (let _167_606 = (str "match")
in (let _167_605 = (p_noSeqTerm e)
in (let _167_604 = (str "with")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _167_606 _167_605 _167_604))))
in (let _167_607 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat _167_608 _167_607)))
in (FStar_Pprint.group _167_609))
end
| FStar_Parser_AST.LetOpen (uid, e) -> begin
(let _167_615 = (let _167_614 = (let _167_612 = (str "let open")
in (let _167_611 = (p_quident uid)
in (let _167_610 = (str "in")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _167_612 _167_611 _167_610))))
in (let _167_613 = (p_term e)
in (FStar_Pprint.op_Hat_Slash_Hat _167_614 _167_613)))
in (FStar_Pprint.group _167_615))
end
| FStar_Parser_AST.Let (q, lbs, e) -> begin
(

let let_doc = (let _167_617 = (str "let")
in (let _167_616 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat _167_617 _167_616)))
in (let _167_622 = (let _167_618 = (str "and")
in (precede_break_separate_map let_doc _167_618 p_letbinding lbs))
in (let _167_621 = (let _167_620 = (str "in")
in (let _167_619 = (p_term e)
in (prefix2 _167_620 _167_619)))
in (FStar_Pprint.op_Hat_Slash_Hat _167_622 _167_621))))
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, typ_opt); FStar_Parser_AST.prange = _68_733})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, branches); FStar_Parser_AST.range = _68_743; FStar_Parser_AST.level = _68_741}) when (matches_var maybe_x x) -> begin
(let _167_625 = (let _167_624 = (str "function")
in (let _167_623 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat _167_624 _167_623)))
in (FStar_Pprint.group _167_625))
end
| FStar_Parser_AST.Assign (id, e) -> begin
(let _167_629 = (let _167_628 = (p_lident id)
in (let _167_627 = (let _167_626 = (p_noSeqTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow _167_626))
in (FStar_Pprint.op_Hat_Slash_Hat _167_628 _167_627)))
in (FStar_Pprint.group _167_629))
end
| _68_756 -> begin
(p_typ e)
end))
and p_typ : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| (FStar_Parser_AST.QForall (bs, trigger, e1)) | (FStar_Parser_AST.QExists (bs, trigger, e1)) -> begin
(let _167_637 = (let _167_633 = (let _167_631 = (p_quantifier e)
in (FStar_Pprint.op_Hat_Hat _167_631 FStar_Pprint.space))
in (let _167_632 = (p_binders true bs)
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") _167_633 _167_632 FStar_Pprint.dot)))
in (let _167_636 = (let _167_635 = (p_trigger trigger)
in (let _167_634 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat _167_635 _167_634)))
in (prefix2 _167_637 _167_636)))
end
| _68_766 -> begin
(p_simpleTerm e)
end))
and p_quantifier : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.QForall (_68_769) -> begin
(str "forall")
end
| FStar_Parser_AST.QExists (_68_772) -> begin
(str "exists")
end
| _68_775 -> begin
(failwith "Imposible : p_quantifier called on a non-quantifier term")
end))
and p_trigger : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun _68_13 -> (match (_68_13) with
| [] -> begin
FStar_Pprint.empty
end
| pats -> begin
(let _167_646 = (let _167_645 = (let _167_644 = (str "pattern")
in (let _167_643 = (let _167_642 = (let _167_640 = (p_disjunctivePats pats)
in (jump2 _167_640))
in (let _167_641 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1)
in (FStar_Pprint.op_Hat_Slash_Hat _167_642 _167_641)))
in (FStar_Pprint.op_Hat_Slash_Hat _167_644 _167_643)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _167_645))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace _167_646))
end))
and p_disjunctivePats : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun pats -> (let _167_648 = (str "\\/")
in (FStar_Pprint.separate_map _167_648 p_conjunctivePats pats)))
and p_conjunctivePats : FStar_Parser_AST.term Prims.list  ->  FStar_Pprint.document = (fun pats -> (let _167_650 = (FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats)
in (FStar_Pprint.group _167_650)))
and p_simpleTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Abs (pats, e) -> begin
(let _167_656 = (let _167_654 = (str "fun")
in (let _167_653 = (let _167_652 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Slash_Hat _167_652 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat _167_654 _167_653)))
in (let _167_655 = (p_term e)
in (op_Hat_Slash_Plus_Hat _167_656 _167_655)))
end
| _68_787 -> begin
(p_tmIff e)
end))
and p_maybeFocusArrow : Prims.bool  ->  FStar_Pprint.document = (fun b -> if b then begin
(str "~>")
end else begin
FStar_Pprint.rarrow
end)
and p_patternBranch : FStar_Parser_AST.branch  ->  FStar_Pprint.document = (fun _68_792 -> (match (_68_792) with
| (pat, when_opt, e) -> begin
(let _167_667 = (let _167_666 = (let _167_664 = (let _167_663 = (let _167_662 = (let _167_661 = (p_disjunctivePattern pat)
in (let _167_660 = (let _167_659 = (p_maybeWhen when_opt)
in (FStar_Pprint.op_Hat_Hat _167_659 FStar_Pprint.rarrow))
in (FStar_Pprint.op_Hat_Slash_Hat _167_661 _167_660)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_662))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar _167_663))
in (FStar_Pprint.group _167_664))
in (let _167_665 = (p_term e)
in (op_Hat_Slash_Plus_Hat _167_666 _167_665)))
in (FStar_Pprint.group _167_667))
end))
and p_maybeWhen : FStar_Parser_AST.term Prims.option  ->  FStar_Pprint.document = (fun _68_14 -> (match (_68_14) with
| None -> begin
FStar_Pprint.empty
end
| Some (e) -> begin
(let _167_671 = (str "when")
in (let _167_670 = (let _167_669 = (p_tmFormula e)
in (FStar_Pprint.op_Hat_Hat _167_669 FStar_Pprint.space))
in (op_Hat_Slash_Plus_Hat _167_671 _167_670)))
end))
and p_tmIff : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("<==>", (e1)::(e2)::[]) -> begin
(let _167_675 = (str "<==>")
in (let _167_674 = (p_tmImplies e1)
in (let _167_673 = (p_tmIff e2)
in (infix2 _167_675 _167_674 _167_673))))
end
| _68_805 -> begin
(p_tmImplies e)
end))
and p_tmImplies : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("==>", (e1)::(e2)::[]) -> begin
(let _167_679 = (str "==>")
in (let _167_678 = (p_tmArrow p_tmFormula e1)
in (let _167_677 = (p_tmImplies e2)
in (infix2 _167_679 _167_678 _167_677))))
end
| _68_814 -> begin
(p_tmArrow p_tmFormula e)
end))
and p_tmArrow : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_Tm e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Product (bs, tgt) -> begin
(let _167_691 = (let _167_690 = (FStar_Pprint.concat_map (fun b -> (let _167_688 = (p_binder false b)
in (let _167_687 = (let _167_686 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_686))
in (FStar_Pprint.op_Hat_Hat _167_688 _167_687)))) bs)
in (let _167_689 = (p_tmArrow p_Tm tgt)
in (FStar_Pprint.op_Hat_Hat _167_690 _167_689)))
in (FStar_Pprint.group _167_691))
end
| _68_823 -> begin
(p_Tm e)
end))
and p_tmFormula : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("\\/", (e1)::(e2)::[]) -> begin
(let _167_695 = (str "\\/")
in (let _167_694 = (p_tmFormula e1)
in (let _167_693 = (p_tmConjunction e2)
in (infix2 _167_695 _167_694 _167_693))))
end
| _68_832 -> begin
(p_tmConjunction e)
end))
and p_tmConjunction : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("/\\", (e1)::(e2)::[]) -> begin
(let _167_699 = (str "/\\")
in (let _167_698 = (p_tmConjunction e1)
in (let _167_697 = (p_tmTuple e2)
in (infix2 _167_699 _167_698 _167_697))))
end
| _68_841 -> begin
(p_tmTuple e)
end))
and p_tmTuple : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (lid, args) when (is_tuple_constructor lid) -> begin
(let _167_702 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map _167_702 (fun _68_850 -> (match (_68_850) with
| (e, _68_849) -> begin
(p_tmEq e)
end)) args))
end
| _68_852 -> begin
(p_tmEq e)
end))
and paren_if : Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun curr mine doc -> if (mine <= curr) then begin
doc
end else begin
(let _167_707 = (let _167_706 = (FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _167_706))
in (FStar_Pprint.group _167_707))
end)
and p_tmEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n = (max_level (FStar_List.append ((colon_equals)::(pipe_right)::[]) operatorInfix0ad12))
in (p_tmEq' n e)))
and p_tmEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (((is_operatorInfix0ad12 op) || (op = "=")) || (op = "|>")) -> begin
(

let _68_869 = (levels op)
in (match (_68_869) with
| (left, mine, right) -> begin
(let _167_714 = (let _167_713 = (str op)
in (let _167_712 = (p_tmEq' left e1)
in (let _167_711 = (p_tmEq' right e2)
in (infix2 _167_713 _167_712 _167_711))))
in (paren_if curr mine _167_714))
end))
end
| FStar_Parser_AST.Op (":=", (e1)::(e2)::[]) -> begin
(let _167_720 = (let _167_719 = (p_tmEq e1)
in (let _167_718 = (let _167_717 = (let _167_716 = (let _167_715 = (p_tmEq e2)
in (op_Hat_Slash_Plus_Hat FStar_Pprint.equals _167_715))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _167_716))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_717))
in (FStar_Pprint.op_Hat_Hat _167_719 _167_718)))
in (FStar_Pprint.group _167_720))
end
| _68_877 -> begin
(p_tmNoEq e)
end))
and p_tmNoEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n = (max_level ((colon_colon)::(amp)::(opinfix3)::(opinfix4)::[]))
in (p_tmNoEq' n e)))
and p_tmNoEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (lid, ((e1, _68_889))::((e2, _68_885))::[]) when ((FStar_Ident.lid_equals lid FStar_Syntax_Const.cons_lid) && (not ((is_list e)))) -> begin
(

let op = "::"
in (

let _68_898 = (levels op)
in (match (_68_898) with
| (left, mine, right) -> begin
(let _167_727 = (let _167_726 = (str op)
in (let _167_725 = (p_tmNoEq' left e1)
in (let _167_724 = (p_tmNoEq' right e2)
in (infix2 _167_726 _167_725 _167_724))))
in (paren_if curr mine _167_727))
end)))
end
| FStar_Parser_AST.Sum (binders, res) -> begin
(

let op = "&"
in (

let _68_907 = (levels op)
in (match (_68_907) with
| (left, mine, right) -> begin
(

let p_dsumfst = (fun b -> (let _167_733 = (p_binder false b)
in (let _167_732 = (let _167_731 = (let _167_730 = (str "&")
in (FStar_Pprint.op_Hat_Hat _167_730 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_731))
in (FStar_Pprint.op_Hat_Hat _167_733 _167_732))))
in (let _167_736 = (let _167_735 = (FStar_Pprint.concat_map p_dsumfst binders)
in (let _167_734 = (p_tmNoEq' right res)
in (FStar_Pprint.op_Hat_Hat _167_735 _167_734)))
in (paren_if curr mine _167_736)))
end)))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (is_operatorInfix34 op) -> begin
(

let _68_919 = (levels op)
in (match (_68_919) with
| (left, mine, right) -> begin
(let _167_740 = (let _167_739 = (str op)
in (let _167_738 = (p_tmNoEq' left e1)
in (let _167_737 = (p_tmNoEq' right e2)
in (infix2 _167_739 _167_738 _167_737))))
in (paren_if curr mine _167_740))
end))
end
| FStar_Parser_AST.Op ("-", (e)::[]) -> begin
(

let _68_928 = (levels "-")
in (match (_68_928) with
| (left, mine, right) -> begin
(let _167_741 = (p_tmNoEq' mine e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus _167_741))
end))
end
| FStar_Parser_AST.NamedTyp (lid, e) -> begin
(let _167_745 = (let _167_744 = (p_lidentOrUnderscore lid)
in (let _167_743 = (let _167_742 = (p_appTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon _167_742))
in (FStar_Pprint.op_Hat_Slash_Hat _167_744 _167_743)))
in (FStar_Pprint.group _167_745))
end
| FStar_Parser_AST.Refine (b, phi) -> begin
(p_refinedBinder b phi)
end
| FStar_Parser_AST.Record (with_opt, record_fields) -> begin
(let _167_749 = (let _167_748 = (default_or_map FStar_Pprint.empty p_with_clause with_opt)
in (let _167_747 = (let _167_746 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (FStar_Pprint.separate_map _167_746 p_simpleDef record_fields))
in (FStar_Pprint.op_Hat_Hat _167_748 _167_747)))
in (braces_with_nesting _167_749))
end
| FStar_Parser_AST.Op ("~", (e)::[]) -> begin
(let _167_752 = (let _167_751 = (str "~")
in (let _167_750 = (p_atomicTerm e)
in (FStar_Pprint.op_Hat_Hat _167_751 _167_750)))
in (FStar_Pprint.group _167_752))
end
| _68_947 -> begin
(p_appTerm e)
end))
and p_with_clause : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (let _167_757 = (p_appTerm e)
in (let _167_756 = (let _167_755 = (let _167_754 = (str "with")
in (FStar_Pprint.op_Hat_Hat _167_754 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_755))
in (FStar_Pprint.op_Hat_Hat _167_757 _167_756))))
and p_refinedBinder : FStar_Parser_AST.binder  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun b phi -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (lid, t) -> begin
(let _167_767 = (let _167_766 = (p_lident lid)
in (let _167_765 = (let _167_764 = (let _167_763 = (p_typ t)
in (let _167_762 = (let _167_761 = (let _167_760 = (p_term phi)
in (braces_with_nesting _167_760))
in (FStar_Pprint.op_Hat_Hat _167_761 FStar_Pprint.rparen))
in (FStar_Pprint.op_Hat_Hat _167_763 _167_762)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _167_764))
in (FStar_Pprint.op_Hat_Hat _167_766 _167_765)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _167_767))
end
| FStar_Parser_AST.TAnnotated (_68_956) -> begin
(failwith "Is this still used ?")
end
| (FStar_Parser_AST.Variable (_)) | (FStar_Parser_AST.TVariable (_)) | (FStar_Parser_AST.NoName (_)) -> begin
(let _167_769 = (let _167_768 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" _167_768))
in (failwith _167_769))
end))
and p_simpleDef : (FStar_Ident.lid * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun _68_969 -> (match (_68_969) with
| (lid, e) -> begin
(let _167_774 = (let _167_773 = (p_qlident lid)
in (let _167_772 = (let _167_771 = (p_simpleTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals _167_771))
in (FStar_Pprint.op_Hat_Slash_Hat _167_773 _167_772)))
in (FStar_Pprint.group _167_774))
end))
and p_appTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App (_68_972) when (is_general_application e) -> begin
(

let _68_976 = (head_and_args e)
in (match (_68_976) with
| (head, args) -> begin
(let _167_777 = (p_indexingTerm head)
in (let _167_776 = (FStar_Pprint.separate_map FStar_Pprint.space p_argTerm args)
in (op_Hat_Slash_Plus_Hat _167_777 _167_776)))
end))
end
| FStar_Parser_AST.Construct (lid, args) when ((is_general_construction e) && (not ((is_dtuple_constructor lid)))) -> begin
if (args = []) then begin
(p_quident lid)
end else begin
(let _167_779 = (p_quident lid)
in (let _167_778 = (FStar_Pprint.separate_map break1 p_argTerm args)
in (op_Hat_Slash_Plus_Hat _167_779 _167_778)))
end
end
| _68_982 -> begin
(p_indexingTerm e)
end))
and p_argTerm : (FStar_Parser_AST.term * FStar_Parser_AST.imp)  ->  FStar_Pprint.document = (fun arg_imp -> (match (arg_imp) with
| ({FStar_Parser_AST.tm = FStar_Parser_AST.Uvar (_68_989); FStar_Parser_AST.range = _68_987; FStar_Parser_AST.level = _68_985}, FStar_Parser_AST.UnivApp) -> begin
(p_univar (Prims.fst arg_imp))
end
| (u, FStar_Parser_AST.UnivApp) -> begin
(p_universe u)
end
| (e, FStar_Parser_AST.FsTypApp) -> begin
(let _167_781 = (p_indexingTerm e)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.langle _167_781 FStar_Pprint.rangle))
end
| (e, FStar_Parser_AST.Hash) -> begin
(let _167_783 = (str "#")
in (let _167_782 = (p_indexingTerm e)
in (FStar_Pprint.op_Hat_Hat _167_783 _167_782)))
end
| (e, FStar_Parser_AST.Nothing) -> begin
(p_indexingTerm e)
end))
and p_indexingTerm_aux : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun exit e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op (".()", (e1)::(e2)::[]) -> begin
(let _167_793 = (let _167_792 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (let _167_791 = (let _167_790 = (let _167_789 = (p_term e2)
in (parens_with_nesting _167_789))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _167_790))
in (FStar_Pprint.op_Hat_Hat _167_792 _167_791)))
in (FStar_Pprint.group _167_793))
end
| FStar_Parser_AST.Op (".[]", (e1)::(e2)::[]) -> begin
(let _167_798 = (let _167_797 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (let _167_796 = (let _167_795 = (let _167_794 = (p_term e2)
in (brackets_with_nesting _167_794))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _167_795))
in (FStar_Pprint.op_Hat_Hat _167_797 _167_796)))
in (FStar_Pprint.group _167_798))
end
| _68_1021 -> begin
(exit e)
end))
and p_indexingTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_indexingTerm_aux p_atomicTerm e))
and p_atomicTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.LetOpen (lid, e) -> begin
(let _167_804 = (p_quident lid)
in (let _167_803 = (let _167_802 = (let _167_801 = (p_term e)
in (parens_with_nesting _167_801))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _167_802))
in (FStar_Pprint.op_Hat_Hat _167_804 _167_803)))
end
| FStar_Parser_AST.Name (lid) -> begin
(p_quident lid)
end
| FStar_Parser_AST.Op (op, (e)::[]) -> begin
(let _167_806 = (str op)
in (let _167_805 = (p_atomicTerm e)
in (FStar_Pprint.op_Hat_Hat _167_806 _167_805)))
end
| _68_1036 -> begin
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
(let _167_809 = (str op)
in (let _167_808 = (p_atomicTermNotQUident e)
in (FStar_Pprint.op_Hat_Hat _167_809 _167_808)))
end
| FStar_Parser_AST.Op (op, []) -> begin
(let _167_813 = (let _167_812 = (let _167_811 = (str op)
in (let _167_810 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat _167_811 _167_810)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_812))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _167_813))
end
| FStar_Parser_AST.Construct (lid, args) when (is_dtuple_constructor lid) -> begin
(let _167_818 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (let _167_817 = (let _167_815 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (let _167_814 = (FStar_List.map Prims.fst args)
in (FStar_Pprint.separate_map _167_815 p_tmEq _167_814)))
in (let _167_816 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _167_818 _167_817 _167_816))))
end
| FStar_Parser_AST.Project (e, lid) -> begin
(let _167_822 = (let _167_821 = (p_atomicTermNotQUident e)
in (let _167_820 = (let _167_819 = (p_qlident lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _167_819))
in (FStar_Pprint.op_Hat_Slash_Hat _167_821 _167_820)))
in (FStar_Pprint.group _167_822))
end
| _68_1067 -> begin
(p_projectionLHS e)
end))
and p_projectionLHS : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (lid) -> begin
(p_qlident lid)
end
| FStar_Parser_AST.Projector (constr_lid, field_lid) -> begin
(let _167_827 = (p_quident constr_lid)
in (let _167_826 = (let _167_825 = (let _167_824 = (p_lident field_lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _167_824))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark _167_825))
in (FStar_Pprint.op_Hat_Hat _167_827 _167_826)))
end
| FStar_Parser_AST.Discrim (constr_lid) -> begin
(let _167_828 = (p_quident constr_lid)
in (FStar_Pprint.op_Hat_Hat _167_828 FStar_Pprint.qmark))
end
| FStar_Parser_AST.Paren (e) -> begin
(let _167_829 = (p_term e)
in (parens_with_nesting _167_829))
end
| _68_1080 when (is_array e) -> begin
(

let es = (extract_from_list e)
in (let _167_832 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar)
in (let _167_831 = (separate_map_or_flow FStar_Pprint.semi p_noSeqTerm es)
in (let _167_830 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") _167_832 _167_831 _167_830)))))
end
| _68_1083 when (is_list e) -> begin
(let _167_834 = (let _167_833 = (extract_from_list e)
in (separate_map_or_flow FStar_Pprint.semi p_noSeqTerm _167_833))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket _167_834 FStar_Pprint.rbracket))
end
| _68_1085 when (is_lex_list e) -> begin
(let _167_837 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket)
in (let _167_836 = (let _167_835 = (extract_from_list e)
in (separate_map_or_flow FStar_Pprint.semi p_noSeqTerm _167_835))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _167_837 _167_836 FStar_Pprint.rbracket)))
end
| _68_1087 when (is_ref_set e) -> begin
(

let es = (extract_from_ref_set e)
in (let _167_839 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace)
in (let _167_838 = (separate_map_or_flow FStar_Pprint.comma p_appTerm es)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") _167_839 _167_838 FStar_Pprint.rbrace))))
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Op (_)) | (FStar_Parser_AST.Tvar (_)) | (FStar_Parser_AST.Uvar (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) | (FStar_Parser_AST.Construct (_)) | (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.App (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.LetOpen (_)) | (FStar_Parser_AST.Seq (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Ascribed (_)) | (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Project (_)) | (FStar_Parser_AST.Product (_)) | (FStar_Parser_AST.Sum (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Refine (_)) | (FStar_Parser_AST.NamedTyp (_)) | (FStar_Parser_AST.Requires (_)) | (FStar_Parser_AST.Ensures (_)) | (FStar_Parser_AST.Assign (_)) | (FStar_Parser_AST.Attributes (_)) -> begin
(let _167_840 = (p_term e)
in (parens_with_nesting _167_840))
end
| FStar_Parser_AST.Labeled (_68_1175) -> begin
(failwith "Not valid in universe")
end))
and p_constant : FStar_Const.sconst  ->  FStar_Pprint.document = (fun _68_17 -> (match (_68_17) with
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
(let _167_842 = (FStar_Pprint.doc_of_char x)
in (FStar_Pprint.squotes _167_842))
end
| FStar_Const.Const_string (bytes, _68_1188) -> begin
(let _167_843 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes _167_843))
end
| FStar_Const.Const_bytearray (bytes, _68_1193) -> begin
(let _167_846 = (let _167_844 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes _167_844))
in (let _167_845 = (str "B")
in (FStar_Pprint.op_Hat_Hat _167_846 _167_845)))
end
| FStar_Const.Const_int (repr, sign_width_opt) -> begin
(

let signedness = (fun _68_15 -> (match (_68_15) with
| FStar_Const.Unsigned -> begin
(str "u")
end
| FStar_Const.Signed -> begin
FStar_Pprint.empty
end))
in (

let width = (fun _68_16 -> (match (_68_16) with
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

let ending = (default_or_map FStar_Pprint.empty (fun _68_1212 -> (match (_68_1212) with
| (s, w) -> begin
(let _167_853 = (signedness s)
in (let _167_852 = (width w)
in (FStar_Pprint.op_Hat_Hat _167_853 _167_852)))
end)) sign_width_opt)
in (let _167_854 = (str repr)
in (FStar_Pprint.op_Hat_Hat _167_854 ending)))))
end
| FStar_Const.Const_range (r) -> begin
(let _167_855 = (FStar_Range.string_of_range r)
in (str _167_855))
end
| FStar_Const.Const_reify -> begin
(str "reify")
end
| FStar_Const.Const_reflect (lid) -> begin
(let _167_859 = (p_quident lid)
in (let _167_858 = (let _167_857 = (let _167_856 = (str "reflect")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _167_856))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark _167_857))
in (FStar_Pprint.op_Hat_Hat _167_859 _167_858)))
end))
and p_universe : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (let _167_862 = (str "u#")
in (let _167_861 = (p_atomicUniverse u)
in (FStar_Pprint.op_Hat_Hat _167_862 _167_861))))
and p_universeFrom : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match (u.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("+", (u1)::(u2)::[]) -> begin
(let _167_867 = (let _167_866 = (p_universeFrom u1)
in (let _167_865 = (let _167_864 = (p_universeFrom u2)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus _167_864))
in (FStar_Pprint.op_Hat_Slash_Hat _167_866 _167_865)))
in (FStar_Pprint.group _167_867))
end
| FStar_Parser_AST.App (_68_1228) -> begin
(

let _68_1232 = (head_and_args u)
in (match (_68_1232) with
| (head, args) -> begin
(match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (maybe_max_lid) when (FStar_Ident.lid_equals maybe_max_lid FStar_Syntax_Const.max_lid) -> begin
(let _167_871 = (let _167_870 = (p_qlident FStar_Syntax_Const.max_lid)
in (let _167_869 = (FStar_Pprint.separate_map FStar_Pprint.space (fun _68_1238 -> (match (_68_1238) with
| (u, _68_1237) -> begin
(p_atomicUniverse u)
end)) args)
in (op_Hat_Slash_Plus_Hat _167_870 _167_869)))
in (FStar_Pprint.group _167_871))
end
| _68_1240 -> begin
(let _167_873 = (let _167_872 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" _167_872))
in (failwith _167_873))
end)
end))
end
| _68_1242 -> begin
(p_atomicUniverse u)
end))
and p_atomicUniverse : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match (u.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Wild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (r, sw)) -> begin
(p_constant (FStar_Const.Const_int (((r), (sw)))))
end
| FStar_Parser_AST.Uvar (_68_1251) -> begin
(p_univar u)
end
| FStar_Parser_AST.Paren (u) -> begin
(let _167_875 = (p_universeFrom u)
in (parens_with_nesting _167_875))
end
| (FStar_Parser_AST.Op ("+", (_)::(_)::[])) | (FStar_Parser_AST.App (_)) -> begin
(let _167_876 = (p_universeFrom u)
in (parens_with_nesting _167_876))
end
| _68_1267 -> begin
(let _167_878 = (let _167_877 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" _167_877))
in (failwith _167_878))
end))
and p_univar : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match (u.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Uvar (id) -> begin
(str (FStar_Ident.text_of_id id))
end
| _68_1272 -> begin
(let _167_881 = (let _167_880 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Not a universe variable %s" _167_880))
in (failwith _167_881))
end))


let term_to_document : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_term e))


let decl_to_document : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun e -> (p_decl e))


let modul_to_document : FStar_Parser_AST.modul  ->  FStar_Pprint.document = (fun m -> (match (m) with
| (FStar_Parser_AST.Module (_, decls)) | (FStar_Parser_AST.Interface (_, decls, _)) -> begin
(let _167_888 = (FStar_All.pipe_right decls (FStar_List.map decl_to_document))
in (FStar_All.pipe_right _167_888 (FStar_Pprint.separate FStar_Pprint.hardline)))
end))


let comments_to_document : (Prims.string * FStar_Range.range) Prims.list  ->  FStar_Pprint.document = (fun comments -> (FStar_Pprint.separate_map FStar_Pprint.hardline (fun _68_1290 -> (match (_68_1290) with
| (comment, range) -> begin
(str comment)
end)) comments))


let modul_with_comments_to_document : FStar_Parser_AST.modul  ->  (Prims.string * FStar_Range.range) Prims.list  ->  (FStar_Pprint.document * (Prims.string * FStar_Range.range) Prims.list) = (fun m comments -> (

let rec aux = (fun _68_1297 decl -> (match (_68_1297) with
| (previous_range_end, comments, doc) -> begin
(

let current_range = decl.FStar_Parser_AST.drange
in (

let inbetween_range = (let _167_901 = (FStar_Range.file_of_range current_range)
in (let _167_900 = (FStar_Range.start_of_range current_range)
in (FStar_Range.mk_range _167_901 previous_range_end _167_900)))
in (

let _68_1308 = (FStar_Util.take (fun _68_18 -> (match (_68_18) with
| (_68_1303, range) -> begin
(FStar_Range.range_contains_range inbetween_range range)
end)) comments)
in (match (_68_1308) with
| (preceding_comments, comments) -> begin
(

let _68_1316 = (FStar_Util.take (fun _68_19 -> (match (_68_19) with
| (_68_1311, range) -> begin
(FStar_Range.range_contains_range current_range range)
end)) comments)
in (match (_68_1316) with
| (inner_comments, comments) -> begin
(

let range_line_diff = (fun range -> ((let _167_906 = (FStar_Range.end_of_range range)
in (FStar_Range.line_of_pos _167_906)) - (let _167_907 = (FStar_Range.start_of_range range)
in (FStar_Range.line_of_pos _167_907))))
in (

let max = (fun x y -> if (x < y) then begin
y
end else begin
x
end)
in (

let line_count = (((range_line_diff inbetween_range) - (Prims.parse_int "1")) - (FStar_List.fold_left (fun n _68_1326 -> (match (_68_1326) with
| (_68_1324, r) -> begin
(n + (let _167_914 = (range_line_diff r)
in (max _167_914 (Prims.parse_int "1"))))
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
(let _167_915 = (comments_to_document inner_comments)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline _167_915))
end
in (

let doc = (let _167_922 = (let _167_921 = (FStar_Pprint.repeat line_count FStar_Pprint.hardline)
in (let _167_920 = (let _167_919 = (comments_to_document preceding_comments)
in (let _167_918 = (let _167_917 = (let _167_916 = (decl_to_document decl)
in (FStar_Pprint.op_Hat_Hat _167_916 inner_comments_doc))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline _167_917))
in (FStar_Pprint.op_Hat_Hat _167_919 _167_918)))
in (FStar_Pprint.op_Hat_Hat _167_921 _167_920)))
in (FStar_Pprint.op_Hat_Hat doc _167_922))
in (let _167_923 = (FStar_Range.end_of_range current_range)
in ((_167_923), (comments), (doc)))))))))
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
| (d)::_68_1345 -> begin
(

let _68_1352 = (FStar_List.fold_left aux ((FStar_Range.zeroPos), (comments), (FStar_Pprint.empty)) decls)
in (match (_68_1352) with
| (_68_1349, comments, doc) -> begin
((doc), (comments))
end))
end))))




