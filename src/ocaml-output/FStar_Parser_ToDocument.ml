
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
in (failwith _165_106))
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
in (failwith _165_116))
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
(failwith (Prims.strcat "Unrecognized operator " s))
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
in (failwith _165_160))
end))
in (FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l)))


let levels : Prims.string  ->  (Prims.int * Prims.int * Prims.int) = (assign_levels level_associativity_spec)


let operatorInfix0ad12 = (opinfix0a)::(opinfix0b)::(opinfix0c)::(opinfix0d)::(opinfix1)::(opinfix2)::[]


let is_operatorInfix0ad12 : Prims.string  ->  Prims.bool = (fun op -> ((FStar_List.tryFind (matches_level op) operatorInfix0ad12) <> None))


let is_operatorInfix34 : Prims.string  ->  Prims.bool = (

let opinfix34 = (opinfix3)::(opinfix4)::[]
in (fun op -> ((FStar_List.tryFind (matches_level op) opinfix34) <> None)))


let comment_stack : (Prims.string * FStar_Range.range) Prims.list FStar_ST.ref = (FStar_ST.alloc [])


let with_comment = (fun printer tm tmrange -> (

let rec comments_before_pos = (fun acc print_pos lookahead_pos -> (match ((FStar_ST.read comment_stack)) with
| [] -> begin
((acc), (false))
end
| ((comment, crange))::cs -> begin
if (FStar_Range.range_before_pos crange print_pos) then begin
(

let _67_307 = (FStar_ST.op_Colon_Equals comment_stack cs)
in (let _165_180 = (let _165_179 = (let _165_178 = (str comment)
in (FStar_Pprint.op_Hat_Hat _165_178 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat acc _165_179))
in (comments_before_pos _165_180 print_pos lookahead_pos)))
end else begin
(let _165_181 = (FStar_Range.range_before_pos crange lookahead_pos)
in ((acc), (_165_181)))
end
end))
in (

let _67_311 = (let _165_183 = (FStar_Range.start_of_range tmrange)
in (let _165_182 = (FStar_Range.end_of_range tmrange)
in (comments_before_pos FStar_Pprint.empty _165_183 _165_182)))
in (match (_67_311) with
| (comments, has_lookahead) -> begin
(

let printed_e = (printer tm)
in (

let comments = if has_lookahead then begin
(

let pos = (FStar_Range.end_of_range tmrange)
in (let _165_184 = (comments_before_pos comments pos pos)
in (Prims.fst _165_184)))
end else begin
comments
end
in (let _165_185 = (FStar_Pprint.op_Hat_Hat comments printed_e)
in (FStar_Pprint.group _165_185))))
end))))


let rec p_decl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (let _165_290 = (FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc)
in (let _165_289 = (let _165_288 = (p_attributes d.FStar_Parser_AST.attrs)
in (let _165_287 = (let _165_286 = (p_qualifiers d.FStar_Parser_AST.quals)
in (let _165_285 = (let _165_284 = (p_rawDecl d)
in (FStar_Pprint.op_Hat_Hat (if (d.FStar_Parser_AST.quals = []) then begin
FStar_Pprint.empty
end else begin
break1
end) _165_284))
in (FStar_Pprint.op_Hat_Hat _165_286 _165_285)))
in (FStar_Pprint.op_Hat_Hat _165_288 _165_287)))
in (FStar_Pprint.op_Hat_Hat _165_290 _165_289))))
and p_attributes : FStar_Parser_AST.attributes_  ->  FStar_Pprint.document = (fun attrs -> (let _165_294 = (let _165_292 = (str "@")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket _165_292))
in (let _165_293 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline)
in (FStar_Pprint.surround_separate_map (Prims.parse_int "0") (Prims.parse_int "2") FStar_Pprint.empty _165_294 FStar_Pprint.space _165_293 p_atomicTerm attrs))))
and p_fsdoc : FStar_Parser_AST.fsdoc  ->  FStar_Pprint.document = (fun _67_319 -> (match (_67_319) with
| (doc, kwd_args) -> begin
(

let kwd_args_doc = (match (kwd_args) with
| [] -> begin
FStar_Pprint.empty
end
| kwd_args -> begin
(

let process_kwd_arg = (fun _67_325 -> (match (_67_325) with
| (kwd, arg) -> begin
(let _165_302 = (str "@")
in (let _165_301 = (let _165_300 = (str kwd)
in (let _165_299 = (let _165_298 = (str arg)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_298))
in (FStar_Pprint.op_Hat_Hat _165_300 _165_299)))
in (FStar_Pprint.op_Hat_Hat _165_302 _165_301)))
end))
in (let _165_304 = (let _165_303 = (FStar_Pprint.separate_map FStar_Pprint.hardline process_kwd_arg kwd_args)
in (FStar_Pprint.op_Hat_Hat _165_303 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline _165_304)))
end)
in (let _165_312 = (let _165_311 = (let _165_310 = (let _165_309 = (let _165_308 = (str doc)
in (let _165_307 = (let _165_306 = (let _165_305 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _165_305))
in (FStar_Pprint.op_Hat_Hat kwd_args_doc _165_306))
in (FStar_Pprint.op_Hat_Hat _165_308 _165_307)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _165_309))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _165_310))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_311))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline _165_312)))
end))
and p_rawDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Open (uid) -> begin
(let _165_316 = (let _165_315 = (str "open")
in (let _165_314 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat _165_315 _165_314)))
in (FStar_Pprint.group _165_316))
end
| FStar_Parser_AST.Include (uid) -> begin
(let _165_319 = (let _165_318 = (str "include")
in (let _165_317 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat _165_318 _165_317)))
in (FStar_Pprint.group _165_319))
end
| FStar_Parser_AST.ModuleAbbrev (uid1, uid2) -> begin
(let _165_326 = (let _165_324 = (str "module")
in (let _165_323 = (let _165_322 = (let _165_321 = (p_uident uid1)
in (let _165_320 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _165_321 _165_320)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_322))
in (FStar_Pprint.op_Hat_Hat _165_324 _165_323)))
in (let _165_325 = (p_quident uid2)
in (op_Hat_Slash_Plus_Hat _165_326 _165_325)))
end
| FStar_Parser_AST.TopLevelModule (uid) -> begin
(let _165_330 = (let _165_329 = (str "module")
in (let _165_328 = (let _165_327 = (p_quident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_327))
in (FStar_Pprint.op_Hat_Hat _165_329 _165_328)))
in (FStar_Pprint.group _165_330))
end
| FStar_Parser_AST.KindAbbrev (_67_339) -> begin
(failwith "Deprecated, please stop throwing your old stuff at me !")
end
| FStar_Parser_AST.Tycon (true, ((FStar_Parser_AST.TyconAbbrev (uid, tpars, None, t), None))::[]) -> begin
(

let effect_prefix_doc = (let _165_333 = (str "effect")
in (let _165_332 = (let _165_331 = (p_uident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_331))
in (FStar_Pprint.op_Hat_Hat _165_333 _165_332)))
in (let _165_336 = (let _165_334 = (p_typars tpars)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") effect_prefix_doc _165_334 FStar_Pprint.equals))
in (let _165_335 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _165_336 _165_335))))
end
| FStar_Parser_AST.Tycon (false, tcdefs) -> begin
(let _165_338 = (str "type")
in (let _165_337 = (str "and")
in (precede_break_separate_map _165_338 _165_337 p_fsdocTypeDeclPairs tcdefs)))
end
| FStar_Parser_AST.TopLevelLet (q, lbs) -> begin
(

let let_doc = (let _165_340 = (str "let")
in (let _165_339 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat _165_340 _165_339)))
in (let _165_341 = (str "and")
in (precede_break_separate_map let_doc _165_341 p_letbinding lbs)))
end
| FStar_Parser_AST.Val (lid, t) -> begin
(let _165_348 = (let _165_346 = (str "val")
in (let _165_345 = (let _165_344 = (let _165_343 = (p_lident lid)
in (let _165_342 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat _165_343 _165_342)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_344))
in (FStar_Pprint.op_Hat_Hat _165_346 _165_345)))
in (let _165_347 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _165_348 _165_347)))
end
| FStar_Parser_AST.Assume (id, t) -> begin
(

let decl_keyword = if (let _165_349 = (FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_All.pipe_right _165_349 FStar_Util.is_upper)) then begin
FStar_Pprint.empty
end else begin
(let _165_350 = (str "val")
in (FStar_Pprint.op_Hat_Hat _165_350 FStar_Pprint.space))
end
in (let _165_355 = (let _165_353 = (let _165_352 = (p_ident id)
in (let _165_351 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat _165_352 _165_351)))
in (FStar_Pprint.op_Hat_Hat decl_keyword _165_353))
in (let _165_354 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _165_355 _165_354))))
end
| FStar_Parser_AST.Exception (uid, t_opt) -> begin
(let _165_363 = (str "exception")
in (let _165_362 = (let _165_361 = (let _165_360 = (p_uident uid)
in (let _165_359 = (FStar_Pprint.optional (fun t -> (let _165_358 = (str "of")
in (let _165_357 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _165_358 _165_357)))) t_opt)
in (FStar_Pprint.op_Hat_Hat _165_360 _165_359)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_361))
in (FStar_Pprint.op_Hat_Hat _165_363 _165_362)))
end
| FStar_Parser_AST.NewEffect (ne) -> begin
(let _165_366 = (str "new_effect")
in (let _165_365 = (let _165_364 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_364))
in (FStar_Pprint.op_Hat_Hat _165_366 _165_365)))
end
| FStar_Parser_AST.SubEffect (se) -> begin
(let _165_369 = (str "sub_effect")
in (let _165_368 = (let _165_367 = (p_subEffect se)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_367))
in (FStar_Pprint.op_Hat_Hat _165_369 _165_368)))
end
| FStar_Parser_AST.NewEffectForFree (ne) -> begin
(let _165_372 = (str "new_effect_for_free")
in (let _165_371 = (let _165_370 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_370))
in (FStar_Pprint.op_Hat_Hat _165_372 _165_371)))
end
| FStar_Parser_AST.Pragma (p) -> begin
(p_pragma p)
end
| FStar_Parser_AST.Fsdoc (doc) -> begin
(let _165_373 = (p_fsdoc doc)
in (FStar_Pprint.op_Hat_Hat _165_373 FStar_Pprint.hardline))
end
| FStar_Parser_AST.Main (_67_388) -> begin
(failwith "*Main declaration* : Is that really still in use ??")
end
| FStar_Parser_AST.Tycon (true, _67_392) -> begin
(failwith "Effect abbreviation is expected to be defined by an abbreviation")
end))
and p_pragma : FStar_Parser_AST.pragma  ->  FStar_Pprint.document = (fun _67_4 -> (match (_67_4) with
| FStar_Parser_AST.SetOptions (s) -> begin
(let _165_378 = (str "#set-options")
in (let _165_377 = (let _165_376 = (let _165_375 = (str s)
in (FStar_Pprint.dquotes _165_375))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_376))
in (FStar_Pprint.op_Hat_Hat _165_378 _165_377)))
end
| FStar_Parser_AST.ResetOptions (s_opt) -> begin
(let _165_383 = (str "#reset-options")
in (let _165_382 = (FStar_Pprint.optional (fun s -> (let _165_381 = (let _165_380 = (str s)
in (FStar_Pprint.dquotes _165_380))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_381))) s_opt)
in (FStar_Pprint.op_Hat_Hat _165_383 _165_382)))
end))
and p_typars : FStar_Parser_AST.binder Prims.list  ->  FStar_Pprint.document = (fun bs -> (p_binders true bs))
and p_fsdocTypeDeclPairs : (FStar_Parser_AST.tycon * FStar_Parser_AST.fsdoc Prims.option)  ->  FStar_Pprint.document = (fun _67_404 -> (match (_67_404) with
| (typedecl, fsdoc_opt) -> begin
(let _165_387 = (FStar_Pprint.optional p_fsdoc fsdoc_opt)
in (let _165_386 = (p_typeDecl typedecl)
in (FStar_Pprint.op_Hat_Hat _165_387 _165_386)))
end))
and p_typeDecl : FStar_Parser_AST.tycon  ->  FStar_Pprint.document = (fun _67_5 -> (match (_67_5) with
| FStar_Parser_AST.TyconAbstract (lid, bs, typ_opt) -> begin
(

let empty' = (fun _67_411 -> (match (()) with
| () -> begin
FStar_Pprint.empty
end))
in (p_typeDeclPrefix lid bs typ_opt empty'))
end
| FStar_Parser_AST.TyconAbbrev (lid, bs, typ_opt, t) -> begin
(

let f = (fun _67_420 -> (match (()) with
| () -> begin
(let _165_393 = (p_typ t)
in (prefix2 FStar_Pprint.equals _165_393))
end))
in (p_typeDeclPrefix lid bs typ_opt f))
end
| FStar_Parser_AST.TyconRecord (lid, bs, typ_opt, record_field_decls) -> begin
(

let p_recordFieldAndComments = (fun _67_431 -> (match (_67_431) with
| (lid, t, doc_opt) -> begin
(with_comment p_recordFieldDecl ((lid), (t), (doc_opt)) t.FStar_Parser_AST.range)
end))
in (

let p_fields = (fun _67_433 -> (match (()) with
| () -> begin
(let _165_401 = (let _165_400 = (let _165_399 = (let _165_398 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (FStar_Pprint.separate_map _165_398 p_recordFieldAndComments record_field_decls))
in (braces_with_nesting _165_399))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_400))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.equals _165_401))
end))
in (p_typeDeclPrefix lid bs typ_opt p_fields)))
end
| FStar_Parser_AST.TyconVariant (lid, bs, typ_opt, ct_decls) -> begin
(

let p_constructorBranchAndComments = (fun _67_445 -> (match (_67_445) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let range = (let _165_405 = (FStar_Util.map_opt t_opt (fun t -> t.FStar_Parser_AST.range))
in (FStar_Util.dflt uid.FStar_Ident.idRange _165_405))
in (

let p_constructorBranch = (fun decl -> (let _165_410 = (let _165_409 = (let _165_408 = (p_constructorDecl decl)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_408))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar _165_409))
in (FStar_Pprint.group _165_410)))
in (with_comment p_constructorBranch ((uid), (t_opt), (doc_opt), (use_of)) range)))
end))
in (

let datacon_doc = (fun _67_451 -> (match (()) with
| () -> begin
(let _165_413 = (FStar_Pprint.separate_map break1 p_constructorBranchAndComments ct_decls)
in (FStar_Pprint.group _165_413))
end))
in (p_typeDeclPrefix lid bs typ_opt (fun _67_452 -> (match (()) with
| () -> begin
(let _165_415 = (datacon_doc ())
in (prefix2 FStar_Pprint.equals _165_415))
end)))))
end))
and p_typeDeclPrefix : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.knd Prims.option  ->  (Prims.unit  ->  FStar_Pprint.document)  ->  FStar_Pprint.document = (fun lid bs typ_opt cont -> if ((bs = []) && (typ_opt = None)) then begin
(let _165_425 = (p_ident lid)
in (let _165_424 = (let _165_423 = (cont ())
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_423))
in (FStar_Pprint.op_Hat_Hat _165_425 _165_424)))
end else begin
(

let binders_doc = (let _165_431 = (p_typars bs)
in (let _165_430 = (FStar_Pprint.optional (fun t -> (let _165_429 = (let _165_428 = (let _165_427 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_427))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_428))
in (FStar_Pprint.op_Hat_Hat break1 _165_429))) typ_opt)
in (FStar_Pprint.op_Hat_Hat _165_431 _165_430)))
in (let _165_433 = (p_ident lid)
in (let _165_432 = (cont ())
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_433 binders_doc _165_432))))
end)
and p_recordFieldDecl : (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc Prims.option)  ->  FStar_Pprint.document = (fun _67_462 -> (match (_67_462) with
| (lid, t, doc_opt) -> begin
(let _165_440 = (let _165_439 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (let _165_438 = (let _165_437 = (p_lident lid)
in (let _165_436 = (let _165_435 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_435))
in (FStar_Pprint.op_Hat_Hat _165_437 _165_436)))
in (FStar_Pprint.op_Hat_Hat _165_439 _165_438)))
in (FStar_Pprint.group _165_440))
end))
and p_constructorDecl : (FStar_Ident.ident * FStar_Parser_AST.term Prims.option * FStar_Parser_AST.fsdoc Prims.option * Prims.bool)  ->  FStar_Pprint.document = (fun _67_467 -> (match (_67_467) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let sep = if use_of then begin
(str "of")
end else begin
FStar_Pprint.colon
end
in (

let uid_doc = (p_uident uid)
in (let _165_447 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (let _165_446 = (default_or_map uid_doc (fun t -> (let _165_445 = (let _165_443 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep)
in (FStar_Pprint.op_Hat_Hat uid_doc _165_443))
in (let _165_444 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _165_445 _165_444)))) t_opt)
in (FStar_Pprint.op_Hat_Hat _165_447 _165_446)))))
end))
and p_letbinding : (FStar_Parser_AST.pattern * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun _67_473 -> (match (_67_473) with
| (pat, e) -> begin
(

let pat_doc = (

let _67_482 = (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, t) -> begin
(let _165_452 = (let _165_451 = (let _165_450 = (let _165_449 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat break1 _165_449))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_450))
in (FStar_Pprint.op_Hat_Hat break1 _165_451))
in ((pat), (_165_452)))
end
| _67_479 -> begin
((pat), (FStar_Pprint.empty))
end)
in (match (_67_482) with
| (pat, ascr_doc) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _67_487); FStar_Parser_AST.prange = _67_484}, pats) -> begin
(let _165_455 = (p_lident x)
in (let _165_454 = (let _165_453 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Hat _165_453 ascr_doc))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_455 _165_454 FStar_Pprint.equals)))
end
| _67_495 -> begin
(let _165_458 = (let _165_457 = (p_tuplePattern pat)
in (let _165_456 = (FStar_Pprint.op_Hat_Slash_Hat ascr_doc FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _165_457 _165_456)))
in (FStar_Pprint.group _165_458))
end)
end))
in (let _165_459 = (p_term e)
in (prefix2 pat_doc _165_459)))
end))
and p_newEffect : FStar_Parser_AST.effect_decl  ->  FStar_Pprint.document = (fun _67_6 -> (match (_67_6) with
| FStar_Parser_AST.RedefineEffect (lid, bs, t) -> begin
(p_effectRedefinition lid bs t)
end
| FStar_Parser_AST.DefineEffect (lid, bs, t, eff_decls, action_decls) -> begin
(p_effectDefinition lid bs t eff_decls action_decls)
end))
and p_effectRedefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun uid bs t -> (let _165_467 = (p_uident uid)
in (let _165_466 = (p_binders true bs)
in (let _165_465 = (let _165_464 = (p_simpleTerm t)
in (prefix2 FStar_Pprint.equals _165_464))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_467 _165_466 _165_465)))))
and p_effectDefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun uid bs t eff_decls action_decls -> (let _165_484 = (let _165_483 = (let _165_477 = (let _165_476 = (p_uident uid)
in (let _165_475 = (p_binders true bs)
in (let _165_474 = (let _165_473 = (p_typ t)
in (prefix2 FStar_Pprint.colon _165_473))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_476 _165_475 _165_474))))
in (FStar_Pprint.group _165_477))
in (let _165_482 = (let _165_481 = (let _165_479 = (str "with")
in (let _165_478 = (separate_break_map FStar_Pprint.semi p_effectDecl eff_decls)
in (prefix2 _165_479 _165_478)))
in (let _165_480 = (p_actionDecls action_decls)
in (FStar_Pprint.op_Hat_Hat _165_481 _165_480)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_483 _165_482)))
in (braces_with_nesting _165_484)))
and p_actionDecls : FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun _67_7 -> (match (_67_7) with
| [] -> begin
FStar_Pprint.empty
end
| l -> begin
(let _165_488 = (let _165_487 = (str "and actions")
in (let _165_486 = (separate_break_map FStar_Pprint.semi p_effectDecl l)
in (prefix2 _165_487 _165_486)))
in (FStar_Pprint.op_Hat_Hat break1 _165_488))
end))
and p_effectDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (false, ((FStar_Parser_AST.TyconAbbrev (lid, [], None, e), None))::[]) -> begin
(let _165_493 = (let _165_491 = (p_lident lid)
in (let _165_490 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _165_491 _165_490)))
in (let _165_492 = (p_simpleTerm e)
in (prefix2 _165_493 _165_492)))
end
| _67_535 -> begin
(let _165_495 = (let _165_494 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "Not a declaration of an effect member... or at least I hope so : %s" _165_494))
in (failwith _165_495))
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

let p_lift = (fun _67_549 -> (match (_67_549) with
| (kwd, t) -> begin
(let _165_502 = (let _165_500 = (str kwd)
in (let _165_499 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _165_500 _165_499)))
in (let _165_501 = (p_simpleTerm t)
in (prefix2 _165_502 _165_501)))
end))
in (separate_break_map FStar_Pprint.semi p_lift lifts)))
in (let _165_510 = (let _165_507 = (let _165_505 = (p_quident lift.FStar_Parser_AST.msource)
in (let _165_504 = (let _165_503 = (str "~>")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_503))
in (FStar_Pprint.op_Hat_Hat _165_505 _165_504)))
in (let _165_506 = (p_quident lift.FStar_Parser_AST.mdest)
in (prefix2 _165_507 _165_506)))
in (let _165_509 = (let _165_508 = (braces_with_nesting lift_op_doc)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_508))
in (FStar_Pprint.op_Hat_Hat _165_510 _165_509)))))
and p_qualifier : FStar_Parser_AST.qualifier  ->  FStar_Pprint.document = (fun _67_8 -> (match (_67_8) with
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
and p_qualifiers : FStar_Parser_AST.qualifiers  ->  FStar_Pprint.document = (fun qs -> (let _165_513 = (FStar_Pprint.separate_map break1 p_qualifier qs)
in (FStar_Pprint.group _165_513)))
and p_letqualifier : FStar_Parser_AST.let_qualifier  ->  FStar_Pprint.document = (fun _67_9 -> (match (_67_9) with
| FStar_Parser_AST.Rec -> begin
(let _165_515 = (str "rec")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_515))
end
| FStar_Parser_AST.Mutable -> begin
(let _165_516 = (str "mutable")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_516))
end
| FStar_Parser_AST.NoLetQualifier -> begin
FStar_Pprint.empty
end))
and p_aqual : FStar_Parser_AST.arg_qualifier  ->  FStar_Pprint.document = (fun _67_10 -> (match (_67_10) with
| FStar_Parser_AST.Implicit -> begin
(str "#")
end
| FStar_Parser_AST.Equality -> begin
(str "$")
end))
and p_disjunctivePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr (pats) -> begin
(let _165_521 = (let _165_520 = (let _165_519 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space)
in (FStar_Pprint.op_Hat_Hat break1 _165_519))
in (FStar_Pprint.separate_map _165_520 p_tuplePattern pats))
in (FStar_Pprint.group _165_521))
end
| _67_583 -> begin
(p_tuplePattern p)
end))
and p_tuplePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTuple (pats, false) -> begin
(let _165_524 = (let _165_523 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map _165_523 p_constructorPattern pats))
in (FStar_Pprint.group _165_524))
end
| _67_590 -> begin
(p_constructorPattern p)
end))
and p_constructorPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (maybe_cons_lid); FStar_Parser_AST.prange = _67_593}, (hd)::(tl)::[]) when (FStar_Ident.lid_equals maybe_cons_lid FStar_Syntax_Const.cons_lid) -> begin
(let _165_528 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon)
in (let _165_527 = (p_constructorPattern hd)
in (let _165_526 = (p_constructorPattern tl)
in (infix2 _165_528 _165_527 _165_526))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (uid); FStar_Parser_AST.prange = _67_603}, pats) -> begin
(let _165_530 = (p_quident uid)
in (let _165_529 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (prefix2 _165_530 _165_529)))
end
| _67_611 -> begin
(p_atomicPattern p)
end))
and p_atomicPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, t) -> begin
(let _165_534 = (let _165_533 = (p_tuplePattern pat)
in (let _165_532 = (p_typ t)
in (infix2 FStar_Pprint.colon _165_533 _165_532)))
in (parens_with_nesting _165_534))
end
| FStar_Parser_AST.PatList (pats) -> begin
(let _165_535 = (separate_break_map FStar_Pprint.semi p_tuplePattern pats)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket _165_535 FStar_Pprint.rbracket))
end
| FStar_Parser_AST.PatRecord (pats) -> begin
(

let p_recordFieldPat = (fun _67_624 -> (match (_67_624) with
| (lid, pat) -> begin
(let _165_539 = (p_qlident lid)
in (let _165_538 = (p_tuplePattern pat)
in (infix2 FStar_Pprint.equals _165_539 _165_538)))
end))
in (let _165_540 = (separate_break_map FStar_Pprint.semi p_recordFieldPat pats)
in (braces_with_nesting _165_540)))
end
| FStar_Parser_AST.PatTuple (pats, true) -> begin
(let _165_543 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (let _165_542 = (separate_break_map FStar_Pprint.comma p_constructorPattern pats)
in (let _165_541 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_543 _165_542 _165_541))))
end
| FStar_Parser_AST.PatTvar (tv, arg_qualifier_opt) -> begin
(

let _67_633 = ()
in (p_tvar tv))
end
| FStar_Parser_AST.PatOp (op) -> begin
(let _165_547 = (let _165_546 = (let _165_545 = (str op)
in (let _165_544 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat _165_545 _165_544)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_546))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_547))
end
| FStar_Parser_AST.PatWild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.PatConst (c) -> begin
(p_constant c)
end
| FStar_Parser_AST.PatVar (lid, aqual) -> begin
(let _165_549 = (FStar_Pprint.optional p_aqual aqual)
in (let _165_548 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat _165_549 _165_548)))
end
| FStar_Parser_AST.PatName (uid) -> begin
(p_quident uid)
end
| FStar_Parser_AST.PatOr (_67_647) -> begin
(failwith "Inner or pattern !")
end
| (FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (_); FStar_Parser_AST.prange = _}, _)) | (FStar_Parser_AST.PatTuple (_, false)) -> begin
(let _165_550 = (p_tuplePattern p)
in (parens_with_nesting _165_550))
end
| _67_665 -> begin
(let _165_552 = (let _165_551 = (FStar_Parser_AST.pat_to_string p)
in (FStar_Util.format1 "Invalid pattern %s" _165_551))
in (failwith _165_552))
end))
and p_binder : Prims.bool  ->  FStar_Parser_AST.binder  ->  FStar_Pprint.document = (fun is_atomic b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (lid) -> begin
(let _165_556 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (let _165_555 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat _165_556 _165_555)))
end
| FStar_Parser_AST.TVariable (lid) -> begin
(p_lident lid)
end
| FStar_Parser_AST.Annotated (lid, t) -> begin
(

let doc = (let _165_561 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (let _165_560 = (let _165_559 = (p_lident lid)
in (let _165_558 = (let _165_557 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_557))
in (FStar_Pprint.op_Hat_Hat _165_559 _165_558)))
in (FStar_Pprint.op_Hat_Hat _165_561 _165_560)))
in if is_atomic then begin
(let _165_563 = (let _165_562 = (FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_562))
in (FStar_Pprint.group _165_563))
end else begin
(FStar_Pprint.group doc)
end)
end
| FStar_Parser_AST.TAnnotated (_67_678) -> begin
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
(let _165_577 = (let _165_575 = (let _165_574 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat _165_574 FStar_Pprint.semi))
in (FStar_Pprint.group _165_575))
in (let _165_576 = (p_term e2)
in (FStar_Pprint.op_Hat_Slash_Hat _165_577 _165_576)))
end
| _67_697 -> begin
(let _165_578 = (p_noSeqTerm e)
in (FStar_Pprint.group _165_578))
end))
and p_noSeqTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_noSeqTerm' e e.FStar_Parser_AST.range))
and p_noSeqTerm' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Ascribed (e, t) -> begin
(let _165_585 = (let _165_584 = (p_tmIff e)
in (let _165_583 = (let _165_582 = (let _165_581 = (p_typ t)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon _165_581))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.langle _165_582))
in (FStar_Pprint.op_Hat_Slash_Hat _165_584 _165_583)))
in (FStar_Pprint.group _165_585))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::(e3)::[]) when (op = ".()<-") -> begin
(let _165_596 = (let _165_595 = (let _165_592 = (let _165_591 = (p_atomicTermNotQUident e1)
in (let _165_590 = (let _165_589 = (let _165_588 = (let _165_586 = (p_term e2)
in (parens_with_nesting _165_586))
in (let _165_587 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat _165_588 _165_587)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_589))
in (FStar_Pprint.op_Hat_Hat _165_591 _165_590)))
in (FStar_Pprint.group _165_592))
in (let _165_594 = (let _165_593 = (p_noSeqTerm e3)
in (jump2 _165_593))
in (FStar_Pprint.op_Hat_Hat _165_595 _165_594)))
in (FStar_Pprint.group _165_596))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::(e3)::[]) when (op = ".[]<-") -> begin
(let _165_607 = (let _165_606 = (let _165_603 = (let _165_602 = (p_atomicTermNotQUident e1)
in (let _165_601 = (let _165_600 = (let _165_599 = (let _165_597 = (p_term e2)
in (brackets_with_nesting _165_597))
in (let _165_598 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat _165_599 _165_598)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_600))
in (FStar_Pprint.op_Hat_Hat _165_602 _165_601)))
in (FStar_Pprint.group _165_603))
in (let _165_605 = (let _165_604 = (p_noSeqTerm e3)
in (jump2 _165_604))
in (FStar_Pprint.op_Hat_Hat _165_606 _165_605)))
in (FStar_Pprint.group _165_607))
end
| FStar_Parser_AST.Requires (e, wtf) -> begin
(

let _67_722 = ()
in (let _165_610 = (let _165_609 = (str "requires")
in (let _165_608 = (p_typ e)
in (FStar_Pprint.op_Hat_Slash_Hat _165_609 _165_608)))
in (FStar_Pprint.group _165_610)))
end
| FStar_Parser_AST.Ensures (e, wtf) -> begin
(

let _67_728 = ()
in (let _165_613 = (let _165_612 = (str "ensures")
in (let _165_611 = (p_typ e)
in (FStar_Pprint.op_Hat_Slash_Hat _165_612 _165_611)))
in (FStar_Pprint.group _165_613)))
end
| FStar_Parser_AST.Attributes (es) -> begin
(let _165_616 = (let _165_615 = (str "attributes")
in (let _165_614 = (FStar_Pprint.separate_map break1 p_atomicTerm es)
in (FStar_Pprint.op_Hat_Slash_Hat _165_615 _165_614)))
in (FStar_Pprint.group _165_616))
end
| FStar_Parser_AST.If (e1, e2, e3) -> begin
if (is_unit e3) then begin
(let _165_623 = (let _165_622 = (let _165_618 = (str "if")
in (let _165_617 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat _165_618 _165_617)))
in (let _165_621 = (let _165_620 = (str "then")
in (let _165_619 = (p_noSeqTerm e2)
in (op_Hat_Slash_Plus_Hat _165_620 _165_619)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_622 _165_621)))
in (FStar_Pprint.group _165_623))
end else begin
(

let e2_doc = (match (e2.FStar_Parser_AST.tm) with
| FStar_Parser_AST.If (_67_738, _67_740, e3) when (is_unit e3) -> begin
(let _165_624 = (p_noSeqTerm e2)
in (parens_with_nesting _165_624))
end
| _67_745 -> begin
(p_noSeqTerm e2)
end)
in (let _165_634 = (let _165_633 = (let _165_626 = (str "if")
in (let _165_625 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat _165_626 _165_625)))
in (let _165_632 = (let _165_631 = (let _165_627 = (str "then")
in (op_Hat_Slash_Plus_Hat _165_627 e2_doc))
in (let _165_630 = (let _165_629 = (str "else")
in (let _165_628 = (p_noSeqTerm e3)
in (op_Hat_Slash_Plus_Hat _165_629 _165_628)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_631 _165_630)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_633 _165_632)))
in (FStar_Pprint.group _165_634)))
end
end
| FStar_Parser_AST.TryWith (e, branches) -> begin
(let _165_641 = (let _165_640 = (let _165_636 = (str "try")
in (let _165_635 = (p_noSeqTerm e)
in (prefix2 _165_636 _165_635)))
in (let _165_639 = (let _165_638 = (str "with")
in (let _165_637 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat _165_638 _165_637)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_640 _165_639)))
in (FStar_Pprint.group _165_641))
end
| FStar_Parser_AST.Match (e, branches) -> begin
(let _165_647 = (let _165_646 = (let _165_644 = (str "match")
in (let _165_643 = (p_noSeqTerm e)
in (let _165_642 = (str "with")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_644 _165_643 _165_642))))
in (let _165_645 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat _165_646 _165_645)))
in (FStar_Pprint.group _165_647))
end
| FStar_Parser_AST.LetOpen (uid, e) -> begin
(let _165_653 = (let _165_652 = (let _165_650 = (str "let open")
in (let _165_649 = (p_quident uid)
in (let _165_648 = (str "in")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_650 _165_649 _165_648))))
in (let _165_651 = (p_term e)
in (FStar_Pprint.op_Hat_Slash_Hat _165_652 _165_651)))
in (FStar_Pprint.group _165_653))
end
| FStar_Parser_AST.Let (q, lbs, e) -> begin
(

let let_doc = (let _165_655 = (str "let")
in (let _165_654 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat _165_655 _165_654)))
in (let _165_660 = (let _165_656 = (str "and")
in (precede_break_separate_map let_doc _165_656 p_letbinding lbs))
in (let _165_659 = (let _165_658 = (str "in")
in (let _165_657 = (p_term e)
in (prefix2 _165_658 _165_657)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_660 _165_659))))
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, typ_opt); FStar_Parser_AST.prange = _67_766})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, branches); FStar_Parser_AST.range = _67_776; FStar_Parser_AST.level = _67_774}) when (matches_var maybe_x x) -> begin
(let _165_663 = (let _165_662 = (str "function")
in (let _165_661 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat _165_662 _165_661)))
in (FStar_Pprint.group _165_663))
end
| FStar_Parser_AST.Assign (id, e) -> begin
(let _165_667 = (let _165_666 = (p_lident id)
in (let _165_665 = (let _165_664 = (p_noSeqTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow _165_664))
in (FStar_Pprint.op_Hat_Slash_Hat _165_666 _165_665)))
in (FStar_Pprint.group _165_667))
end
| _67_789 -> begin
(p_typ e)
end))
and p_typ : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| (FStar_Parser_AST.QForall (bs, trigger, e1)) | (FStar_Parser_AST.QExists (bs, trigger, e1)) -> begin
(let _165_675 = (let _165_671 = (let _165_669 = (p_quantifier e)
in (FStar_Pprint.op_Hat_Hat _165_669 FStar_Pprint.space))
in (let _165_670 = (p_binders true bs)
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") _165_671 _165_670 FStar_Pprint.dot)))
in (let _165_674 = (let _165_673 = (p_trigger trigger)
in (let _165_672 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat _165_673 _165_672)))
in (prefix2 _165_675 _165_674)))
end
| _67_799 -> begin
(p_simpleTerm e)
end))
and p_quantifier : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.QForall (_67_802) -> begin
(str "forall")
end
| FStar_Parser_AST.QExists (_67_805) -> begin
(str "exists")
end
| _67_808 -> begin
(failwith "Imposible : p_quantifier called on a non-quantifier term")
end))
and p_trigger : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun _67_11 -> (match (_67_11) with
| [] -> begin
FStar_Pprint.empty
end
| pats -> begin
(let _165_684 = (let _165_683 = (let _165_682 = (str "pattern")
in (let _165_681 = (let _165_680 = (let _165_678 = (p_disjunctivePats pats)
in (jump2 _165_678))
in (let _165_679 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1)
in (FStar_Pprint.op_Hat_Slash_Hat _165_680 _165_679)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_682 _165_681)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_683))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace _165_684))
end))
and p_disjunctivePats : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun pats -> (let _165_686 = (str "\\/")
in (FStar_Pprint.separate_map _165_686 p_conjunctivePats pats)))
and p_conjunctivePats : FStar_Parser_AST.term Prims.list  ->  FStar_Pprint.document = (fun pats -> (let _165_688 = (FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats)
in (FStar_Pprint.group _165_688)))
and p_simpleTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Abs (pats, e) -> begin
(let _165_694 = (let _165_692 = (str "fun")
in (let _165_691 = (let _165_690 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Slash_Hat _165_690 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat _165_692 _165_691)))
in (let _165_693 = (p_term e)
in (op_Hat_Slash_Plus_Hat _165_694 _165_693)))
end
| _67_820 -> begin
(p_tmIff e)
end))
and p_maybeFocusArrow : Prims.bool  ->  FStar_Pprint.document = (fun b -> if b then begin
(str "~>")
end else begin
FStar_Pprint.rarrow
end)
and p_patternBranch : FStar_Parser_AST.branch  ->  FStar_Pprint.document = (fun _67_825 -> (match (_67_825) with
| (pat, when_opt, e) -> begin
(let _165_705 = (let _165_704 = (let _165_702 = (let _165_701 = (let _165_700 = (let _165_699 = (p_disjunctivePattern pat)
in (let _165_698 = (let _165_697 = (p_maybeWhen when_opt)
in (FStar_Pprint.op_Hat_Hat _165_697 FStar_Pprint.rarrow))
in (FStar_Pprint.op_Hat_Slash_Hat _165_699 _165_698)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_700))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar _165_701))
in (FStar_Pprint.group _165_702))
in (let _165_703 = (p_term e)
in (op_Hat_Slash_Plus_Hat _165_704 _165_703)))
in (FStar_Pprint.group _165_705))
end))
and p_maybeWhen : FStar_Parser_AST.term Prims.option  ->  FStar_Pprint.document = (fun _67_12 -> (match (_67_12) with
| None -> begin
FStar_Pprint.empty
end
| Some (e) -> begin
(let _165_709 = (str "when")
in (let _165_708 = (let _165_707 = (p_tmFormula e)
in (FStar_Pprint.op_Hat_Hat _165_707 FStar_Pprint.space))
in (op_Hat_Slash_Plus_Hat _165_709 _165_708)))
end))
and p_tmIff : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("<==>", (e1)::(e2)::[]) -> begin
(let _165_713 = (str "<==>")
in (let _165_712 = (p_tmImplies e1)
in (let _165_711 = (p_tmIff e2)
in (infix2 _165_713 _165_712 _165_711))))
end
| _67_838 -> begin
(p_tmImplies e)
end))
and p_tmImplies : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("==>", (e1)::(e2)::[]) -> begin
(let _165_717 = (str "==>")
in (let _165_716 = (p_tmArrow p_tmFormula e1)
in (let _165_715 = (p_tmImplies e2)
in (infix2 _165_717 _165_716 _165_715))))
end
| _67_847 -> begin
(p_tmArrow p_tmFormula e)
end))
and p_tmArrow : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_Tm e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Product (bs, tgt) -> begin
(let _165_729 = (let _165_728 = (FStar_Pprint.concat_map (fun b -> (let _165_726 = (p_binder false b)
in (let _165_725 = (let _165_724 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_724))
in (FStar_Pprint.op_Hat_Hat _165_726 _165_725)))) bs)
in (let _165_727 = (p_tmArrow p_Tm tgt)
in (FStar_Pprint.op_Hat_Hat _165_728 _165_727)))
in (FStar_Pprint.group _165_729))
end
| _67_856 -> begin
(p_Tm e)
end))
and p_tmFormula : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("\\/", (e1)::(e2)::[]) -> begin
(let _165_733 = (str "\\/")
in (let _165_732 = (p_tmFormula e1)
in (let _165_731 = (p_tmConjunction e2)
in (infix2 _165_733 _165_732 _165_731))))
end
| _67_865 -> begin
(p_tmConjunction e)
end))
and p_tmConjunction : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("/\\", (e1)::(e2)::[]) -> begin
(let _165_737 = (str "/\\")
in (let _165_736 = (p_tmConjunction e1)
in (let _165_735 = (p_tmTuple e2)
in (infix2 _165_737 _165_736 _165_735))))
end
| _67_874 -> begin
(p_tmTuple e)
end))
and p_tmTuple : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (lid, args) when (is_tuple_constructor lid) -> begin
(let _165_740 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map _165_740 (fun _67_883 -> (match (_67_883) with
| (e, _67_882) -> begin
(p_tmEq e)
end)) args))
end
| _67_885 -> begin
(p_tmEq e)
end))
and paren_if : Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun curr mine doc -> if (mine <= curr) then begin
doc
end else begin
(let _165_745 = (let _165_744 = (FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_744))
in (FStar_Pprint.group _165_745))
end)
and p_tmEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n = (max_level (FStar_List.append ((colon_equals)::(pipe_right)::[]) operatorInfix0ad12))
in (p_tmEq' n e)))
and p_tmEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (((is_operatorInfix0ad12 op) || (op = "=")) || (op = "|>")) -> begin
(

let _67_902 = (levels op)
in (match (_67_902) with
| (left, mine, right) -> begin
(let _165_752 = (let _165_751 = (str op)
in (let _165_750 = (p_tmEq' left e1)
in (let _165_749 = (p_tmEq' right e2)
in (infix2 _165_751 _165_750 _165_749))))
in (paren_if curr mine _165_752))
end))
end
| FStar_Parser_AST.Op (":=", (e1)::(e2)::[]) -> begin
(let _165_758 = (let _165_757 = (p_tmEq e1)
in (let _165_756 = (let _165_755 = (let _165_754 = (let _165_753 = (p_tmEq e2)
in (op_Hat_Slash_Plus_Hat FStar_Pprint.equals _165_753))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_754))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_755))
in (FStar_Pprint.op_Hat_Hat _165_757 _165_756)))
in (FStar_Pprint.group _165_758))
end
| _67_910 -> begin
(p_tmNoEq e)
end))
and p_tmNoEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n = (max_level ((colon_colon)::(amp)::(opinfix3)::(opinfix4)::[]))
in (p_tmNoEq' n e)))
and p_tmNoEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (lid, ((e1, _67_922))::((e2, _67_918))::[]) when ((FStar_Ident.lid_equals lid FStar_Syntax_Const.cons_lid) && (not ((is_list e)))) -> begin
(

let op = "::"
in (

let _67_931 = (levels op)
in (match (_67_931) with
| (left, mine, right) -> begin
(let _165_765 = (let _165_764 = (str op)
in (let _165_763 = (p_tmNoEq' left e1)
in (let _165_762 = (p_tmNoEq' right e2)
in (infix2 _165_764 _165_763 _165_762))))
in (paren_if curr mine _165_765))
end)))
end
| FStar_Parser_AST.Sum (binders, res) -> begin
(

let op = "&"
in (

let _67_940 = (levels op)
in (match (_67_940) with
| (left, mine, right) -> begin
(

let p_dsumfst = (fun b -> (let _165_771 = (p_binder false b)
in (let _165_770 = (let _165_769 = (let _165_768 = (str "&")
in (FStar_Pprint.op_Hat_Hat _165_768 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_769))
in (FStar_Pprint.op_Hat_Hat _165_771 _165_770))))
in (let _165_774 = (let _165_773 = (FStar_Pprint.concat_map p_dsumfst binders)
in (let _165_772 = (p_tmNoEq' right res)
in (FStar_Pprint.op_Hat_Hat _165_773 _165_772)))
in (paren_if curr mine _165_774)))
end)))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (is_operatorInfix34 op) -> begin
(

let _67_952 = (levels op)
in (match (_67_952) with
| (left, mine, right) -> begin
(let _165_778 = (let _165_777 = (str op)
in (let _165_776 = (p_tmNoEq' left e1)
in (let _165_775 = (p_tmNoEq' right e2)
in (infix2 _165_777 _165_776 _165_775))))
in (paren_if curr mine _165_778))
end))
end
| FStar_Parser_AST.Op ("-", (e)::[]) -> begin
(

let _67_961 = (levels "-")
in (match (_67_961) with
| (left, mine, right) -> begin
(let _165_779 = (p_tmNoEq' mine e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus _165_779))
end))
end
| FStar_Parser_AST.NamedTyp (lid, e) -> begin
(let _165_783 = (let _165_782 = (p_lidentOrUnderscore lid)
in (let _165_781 = (let _165_780 = (p_appTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon _165_780))
in (FStar_Pprint.op_Hat_Slash_Hat _165_782 _165_781)))
in (FStar_Pprint.group _165_783))
end
| FStar_Parser_AST.Refine (b, phi) -> begin
(p_refinedBinder b phi)
end
| FStar_Parser_AST.Record (with_opt, record_fields) -> begin
(let _165_787 = (let _165_786 = (default_or_map FStar_Pprint.empty p_with_clause with_opt)
in (let _165_785 = (let _165_784 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (FStar_Pprint.separate_map _165_784 p_simpleDef record_fields))
in (FStar_Pprint.op_Hat_Hat _165_786 _165_785)))
in (braces_with_nesting _165_787))
end
| FStar_Parser_AST.Op ("~", (e)::[]) -> begin
(let _165_790 = (let _165_789 = (str "~")
in (let _165_788 = (p_atomicTerm e)
in (FStar_Pprint.op_Hat_Hat _165_789 _165_788)))
in (FStar_Pprint.group _165_790))
end
| _67_980 -> begin
(p_appTerm e)
end))
and p_with_clause : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (let _165_795 = (p_appTerm e)
in (let _165_794 = (let _165_793 = (let _165_792 = (str "with")
in (FStar_Pprint.op_Hat_Hat _165_792 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_793))
in (FStar_Pprint.op_Hat_Hat _165_795 _165_794))))
and p_refinedBinder : FStar_Parser_AST.binder  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun b phi -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (lid, t) -> begin
(let _165_805 = (let _165_804 = (p_lident lid)
in (let _165_803 = (let _165_802 = (let _165_801 = (p_typ t)
in (let _165_800 = (let _165_799 = (let _165_798 = (p_term phi)
in (braces_with_nesting _165_798))
in (FStar_Pprint.op_Hat_Hat _165_799 FStar_Pprint.rparen))
in (FStar_Pprint.op_Hat_Hat _165_801 _165_800)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_802))
in (FStar_Pprint.op_Hat_Hat _165_804 _165_803)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_805))
end
| FStar_Parser_AST.TAnnotated (_67_989) -> begin
(failwith "Is this still used ?")
end
| (FStar_Parser_AST.Variable (_)) | (FStar_Parser_AST.TVariable (_)) | (FStar_Parser_AST.NoName (_)) -> begin
(let _165_807 = (let _165_806 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" _165_806))
in (failwith _165_807))
end))
and p_simpleDef : (FStar_Ident.lid * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun _67_1002 -> (match (_67_1002) with
| (lid, e) -> begin
(let _165_812 = (let _165_811 = (p_qlident lid)
in (let _165_810 = (let _165_809 = (p_simpleTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals _165_809))
in (FStar_Pprint.op_Hat_Slash_Hat _165_811 _165_810)))
in (FStar_Pprint.group _165_812))
end))
and p_appTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App (_67_1005) when (is_general_application e) -> begin
(

let _67_1009 = (head_and_args e)
in (match (_67_1009) with
| (head, args) -> begin
(let _165_815 = (p_indexingTerm head)
in (let _165_814 = (FStar_Pprint.separate_map FStar_Pprint.space p_argTerm args)
in (op_Hat_Slash_Plus_Hat _165_815 _165_814)))
end))
end
| FStar_Parser_AST.Construct (lid, args) when ((is_general_construction e) && (not ((is_dtuple_constructor lid)))) -> begin
if (args = []) then begin
(p_quident lid)
end else begin
(let _165_817 = (p_quident lid)
in (let _165_816 = (FStar_Pprint.separate_map break1 p_argTerm args)
in (op_Hat_Slash_Plus_Hat _165_817 _165_816)))
end
end
| _67_1015 -> begin
(p_indexingTerm e)
end))
and p_argTerm : (FStar_Parser_AST.term * FStar_Parser_AST.imp)  ->  FStar_Pprint.document = (fun arg_imp -> (match (arg_imp) with
| ({FStar_Parser_AST.tm = FStar_Parser_AST.Uvar (_67_1022); FStar_Parser_AST.range = _67_1020; FStar_Parser_AST.level = _67_1018}, FStar_Parser_AST.UnivApp) -> begin
(p_univar (Prims.fst arg_imp))
end
| (u, FStar_Parser_AST.UnivApp) -> begin
(p_universe u)
end
| (e, FStar_Parser_AST.FsTypApp) -> begin
(let _165_819 = (p_indexingTerm e)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.langle _165_819 FStar_Pprint.rangle))
end
| (e, FStar_Parser_AST.Hash) -> begin
(let _165_821 = (str "#")
in (let _165_820 = (p_indexingTerm e)
in (FStar_Pprint.op_Hat_Hat _165_821 _165_820)))
end
| (e, FStar_Parser_AST.Nothing) -> begin
(p_indexingTerm e)
end))
and p_indexingTerm_aux : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun exit e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op (".()", (e1)::(e2)::[]) -> begin
(let _165_831 = (let _165_830 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (let _165_829 = (let _165_828 = (let _165_827 = (p_term e2)
in (parens_with_nesting _165_827))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_828))
in (FStar_Pprint.op_Hat_Hat _165_830 _165_829)))
in (FStar_Pprint.group _165_831))
end
| FStar_Parser_AST.Op (".[]", (e1)::(e2)::[]) -> begin
(let _165_836 = (let _165_835 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (let _165_834 = (let _165_833 = (let _165_832 = (p_term e2)
in (brackets_with_nesting _165_832))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_833))
in (FStar_Pprint.op_Hat_Hat _165_835 _165_834)))
in (FStar_Pprint.group _165_836))
end
| _67_1054 -> begin
(exit e)
end))
and p_indexingTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_indexingTerm_aux p_atomicTerm e))
and p_atomicTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.LetOpen (lid, e) -> begin
(let _165_842 = (p_quident lid)
in (let _165_841 = (let _165_840 = (let _165_839 = (p_term e)
in (parens_with_nesting _165_839))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_840))
in (FStar_Pprint.op_Hat_Hat _165_842 _165_841)))
end
| FStar_Parser_AST.Name (lid) -> begin
(p_quident lid)
end
| FStar_Parser_AST.Op (op, (e)::[]) -> begin
(let _165_844 = (str op)
in (let _165_843 = (p_atomicTerm e)
in (FStar_Pprint.op_Hat_Hat _165_844 _165_843)))
end
| _67_1069 -> begin
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
(let _165_847 = (str op)
in (let _165_846 = (p_atomicTermNotQUident e)
in (FStar_Pprint.op_Hat_Hat _165_847 _165_846)))
end
| FStar_Parser_AST.Op (op, []) -> begin
(let _165_851 = (let _165_850 = (let _165_849 = (str op)
in (let _165_848 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat _165_849 _165_848)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_850))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_851))
end
| FStar_Parser_AST.Construct (lid, args) when (is_dtuple_constructor lid) -> begin
(let _165_856 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (let _165_855 = (let _165_853 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (let _165_852 = (FStar_List.map Prims.fst args)
in (FStar_Pprint.separate_map _165_853 p_tmEq _165_852)))
in (let _165_854 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_856 _165_855 _165_854))))
end
| FStar_Parser_AST.Project (e, lid) -> begin
(let _165_860 = (let _165_859 = (p_atomicTermNotQUident e)
in (let _165_858 = (let _165_857 = (p_qlident lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_857))
in (FStar_Pprint.op_Hat_Slash_Hat _165_859 _165_858)))
in (FStar_Pprint.group _165_860))
end
| _67_1100 -> begin
(p_projectionLHS e)
end))
and p_projectionLHS : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (lid) -> begin
(p_qlident lid)
end
| FStar_Parser_AST.Projector (constr_lid, field_lid) -> begin
(let _165_865 = (p_quident constr_lid)
in (let _165_864 = (let _165_863 = (let _165_862 = (p_lident field_lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_862))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark _165_863))
in (FStar_Pprint.op_Hat_Hat _165_865 _165_864)))
end
| FStar_Parser_AST.Discrim (constr_lid) -> begin
(let _165_866 = (p_quident constr_lid)
in (FStar_Pprint.op_Hat_Hat _165_866 FStar_Pprint.qmark))
end
| FStar_Parser_AST.Paren (e) -> begin
(let _165_867 = (p_term e)
in (parens_with_nesting _165_867))
end
| _67_1113 when (is_array e) -> begin
(

let es = (extract_from_list e)
in (let _165_870 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar)
in (let _165_869 = (separate_map_or_flow FStar_Pprint.semi p_noSeqTerm es)
in (let _165_868 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") _165_870 _165_869 _165_868)))))
end
| _67_1116 when (is_list e) -> begin
(let _165_872 = (let _165_871 = (extract_from_list e)
in (separate_map_or_flow FStar_Pprint.semi p_noSeqTerm _165_871))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket _165_872 FStar_Pprint.rbracket))
end
| _67_1118 when (is_lex_list e) -> begin
(let _165_875 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket)
in (let _165_874 = (let _165_873 = (extract_from_list e)
in (separate_map_or_flow FStar_Pprint.semi p_noSeqTerm _165_873))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_875 _165_874 FStar_Pprint.rbracket)))
end
| _67_1120 when (is_ref_set e) -> begin
(

let es = (extract_from_ref_set e)
in (let _165_877 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace)
in (let _165_876 = (separate_map_or_flow FStar_Pprint.comma p_appTerm es)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") _165_877 _165_876 FStar_Pprint.rbrace))))
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Op (_)) | (FStar_Parser_AST.Tvar (_)) | (FStar_Parser_AST.Uvar (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) | (FStar_Parser_AST.Construct (_)) | (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.App (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.LetOpen (_)) | (FStar_Parser_AST.Seq (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Ascribed (_)) | (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Project (_)) | (FStar_Parser_AST.Product (_)) | (FStar_Parser_AST.Sum (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Refine (_)) | (FStar_Parser_AST.NamedTyp (_)) | (FStar_Parser_AST.Requires (_)) | (FStar_Parser_AST.Ensures (_)) | (FStar_Parser_AST.Assign (_)) | (FStar_Parser_AST.Attributes (_)) -> begin
(let _165_878 = (p_term e)
in (parens_with_nesting _165_878))
end
| FStar_Parser_AST.Labeled (_67_1208) -> begin
(failwith "Not valid in universe")
end))
and p_constant : FStar_Const.sconst  ->  FStar_Pprint.document = (fun _67_15 -> (match (_67_15) with
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
(let _165_880 = (FStar_Pprint.doc_of_char x)
in (FStar_Pprint.squotes _165_880))
end
| FStar_Const.Const_string (bytes, _67_1221) -> begin
(let _165_881 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes _165_881))
end
| FStar_Const.Const_bytearray (bytes, _67_1226) -> begin
(let _165_884 = (let _165_882 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes _165_882))
in (let _165_883 = (str "B")
in (FStar_Pprint.op_Hat_Hat _165_884 _165_883)))
end
| FStar_Const.Const_int (repr, sign_width_opt) -> begin
(

let signedness = (fun _67_13 -> (match (_67_13) with
| FStar_Const.Unsigned -> begin
(str "u")
end
| FStar_Const.Signed -> begin
FStar_Pprint.empty
end))
in (

let width = (fun _67_14 -> (match (_67_14) with
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

let ending = (default_or_map FStar_Pprint.empty (fun _67_1245 -> (match (_67_1245) with
| (s, w) -> begin
(let _165_891 = (signedness s)
in (let _165_890 = (width w)
in (FStar_Pprint.op_Hat_Hat _165_891 _165_890)))
end)) sign_width_opt)
in (let _165_892 = (str repr)
in (FStar_Pprint.op_Hat_Hat _165_892 ending)))))
end
| FStar_Const.Const_range (r) -> begin
(let _165_893 = (FStar_Range.string_of_range r)
in (str _165_893))
end
| FStar_Const.Const_reify -> begin
(str "reify")
end
| FStar_Const.Const_reflect (lid) -> begin
(let _165_897 = (p_quident lid)
in (let _165_896 = (let _165_895 = (let _165_894 = (str "reflect")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_894))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark _165_895))
in (FStar_Pprint.op_Hat_Hat _165_897 _165_896)))
end))
and p_universe : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (let _165_900 = (str "u#")
in (let _165_899 = (p_atomicUniverse u)
in (FStar_Pprint.op_Hat_Hat _165_900 _165_899))))
and p_universeFrom : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match (u.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("+", (u1)::(u2)::[]) -> begin
(let _165_905 = (let _165_904 = (p_universeFrom u1)
in (let _165_903 = (let _165_902 = (p_universeFrom u2)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus _165_902))
in (FStar_Pprint.op_Hat_Slash_Hat _165_904 _165_903)))
in (FStar_Pprint.group _165_905))
end
| FStar_Parser_AST.App (_67_1261) -> begin
(

let _67_1265 = (head_and_args u)
in (match (_67_1265) with
| (head, args) -> begin
(match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (maybe_max_lid) when (FStar_Ident.lid_equals maybe_max_lid FStar_Syntax_Const.max_lid) -> begin
(let _165_909 = (let _165_908 = (p_qlident FStar_Syntax_Const.max_lid)
in (let _165_907 = (FStar_Pprint.separate_map FStar_Pprint.space (fun _67_1271 -> (match (_67_1271) with
| (u, _67_1270) -> begin
(p_atomicUniverse u)
end)) args)
in (op_Hat_Slash_Plus_Hat _165_908 _165_907)))
in (FStar_Pprint.group _165_909))
end
| _67_1273 -> begin
(let _165_911 = (let _165_910 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" _165_910))
in (failwith _165_911))
end)
end))
end
| _67_1275 -> begin
(p_atomicUniverse u)
end))
and p_atomicUniverse : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match (u.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Wild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (r, sw)) -> begin
(p_constant (FStar_Const.Const_int (((r), (sw)))))
end
| FStar_Parser_AST.Uvar (_67_1284) -> begin
(p_univar u)
end
| FStar_Parser_AST.Paren (u) -> begin
(let _165_913 = (p_universeFrom u)
in (parens_with_nesting _165_913))
end
| (FStar_Parser_AST.Op ("+", (_)::(_)::[])) | (FStar_Parser_AST.App (_)) -> begin
(let _165_914 = (p_universeFrom u)
in (parens_with_nesting _165_914))
end
| _67_1300 -> begin
(let _165_916 = (let _165_915 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" _165_915))
in (failwith _165_916))
end))
and p_univar : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match (u.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Uvar (id) -> begin
(str (FStar_Ident.text_of_id id))
end
| _67_1305 -> begin
(let _165_919 = (let _165_918 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Not a universe variable %s" _165_918))
in (failwith _165_919))
end))


let term_to_document : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_term e))


let decl_to_document : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun e -> (p_decl e))


let modul_to_document : FStar_Parser_AST.modul  ->  FStar_Pprint.document = (fun m -> (match (m) with
| (FStar_Parser_AST.Module (_, decls)) | (FStar_Parser_AST.Interface (_, decls, _)) -> begin
(let _165_926 = (FStar_All.pipe_right decls (FStar_List.map decl_to_document))
in (FStar_All.pipe_right _165_926 (FStar_Pprint.separate FStar_Pprint.hardline)))
end))


let comments_to_document : (Prims.string * FStar_Range.range) Prims.list  ->  FStar_Pprint.document = (fun comments -> (FStar_Pprint.separate_map FStar_Pprint.hardline (fun _67_1323 -> (match (_67_1323) with
| (comment, range) -> begin
(str comment)
end)) comments))


let modul_with_comments_to_document : FStar_Parser_AST.modul  ->  (Prims.string * FStar_Range.range) Prims.list  ->  (FStar_Pprint.document * (Prims.string * FStar_Range.range) Prims.list) = (fun m comments -> (

let rec aux = (fun _67_1330 decl -> (match (_67_1330) with
| (previous_range_end, comments, doc) -> begin
(

let current_range = decl.FStar_Parser_AST.drange
in (

let inbetween_range = (let _165_939 = (FStar_Range.file_of_range current_range)
in (let _165_938 = (FStar_Range.start_of_range current_range)
in (FStar_Range.mk_range _165_939 previous_range_end _165_938)))
in (

let _67_1341 = (FStar_Util.take (fun _67_16 -> (match (_67_16) with
| (_67_1336, range) -> begin
(FStar_Range.range_contains_range inbetween_range range)
end)) comments)
in (match (_67_1341) with
| (preceding_comments, comments) -> begin
(

let _67_1349 = (FStar_Util.take (fun _67_17 -> (match (_67_17) with
| (_67_1344, range) -> begin
(FStar_Range.range_contains_range current_range range)
end)) comments)
in (match (_67_1349) with
| (inner_comments, comments) -> begin
(

let range_line_diff = (fun range -> ((let _165_944 = (FStar_Range.end_of_range range)
in (FStar_Range.line_of_pos _165_944)) - (let _165_945 = (FStar_Range.start_of_range range)
in (FStar_Range.line_of_pos _165_945))))
in (

let max = (fun x y -> if (x < y) then begin
y
end else begin
x
end)
in (

let line_count = (((range_line_diff inbetween_range) - (Prims.parse_int "1")) - (FStar_List.fold_left (fun n _67_1359 -> (match (_67_1359) with
| (_67_1357, r) -> begin
(n + (let _165_952 = (range_line_diff r)
in (max _165_952 (Prims.parse_int "1"))))
end)) (Prims.parse_int "0") preceding_comments))
in (

let line_count = (max line_count (if (preceding_comments = []) then begin
(Prims.parse_int "0")
end else begin
(Prims.parse_int "1")
end))
in (

let _67_1362 = (FStar_ST.op_Colon_Equals comment_stack inner_comments)
in (

let doc = (let _165_958 = (let _165_957 = (FStar_Pprint.repeat line_count FStar_Pprint.hardline)
in (let _165_956 = (let _165_955 = (comments_to_document preceding_comments)
in (let _165_954 = (let _165_953 = (decl_to_document decl)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline _165_953))
in (FStar_Pprint.op_Hat_Hat _165_955 _165_954)))
in (FStar_Pprint.op_Hat_Hat _165_957 _165_956)))
in (FStar_Pprint.op_Hat_Hat doc _165_958))
in (

let _67_1365 = if ((FStar_ST.read comment_stack) <> []) then begin
(let _165_962 = (let _165_961 = (let _165_960 = (let _165_959 = (FStar_ST.read comment_stack)
in (FStar_List.map Prims.fst _165_959))
in (FStar_String.concat " ; " _165_960))
in (Prims.strcat "Something went wrong with the comment stack, leftover comments : " _165_961))
in (failwith _165_962))
end else begin
()
end
in (match (()) with
| () -> begin
(let _165_963 = (FStar_Range.end_of_range current_range)
in ((_165_963), (comments), (doc)))
end))))))))
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
| (d)::_67_1380 -> begin
(

let _67_1387 = (FStar_List.fold_left aux ((FStar_Range.zeroPos), (comments), (FStar_Pprint.empty)) decls)
in (match (_67_1387) with
| (_67_1384, comments, doc) -> begin
((doc), (comments))
end))
end))))




