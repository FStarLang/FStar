
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


let infix0 : FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (FStar_Pprint.infix (Prims.parse_int "0") (Prims.parse_int "1"))


let break1 : FStar_Pprint.document = (FStar_Pprint.break_ (Prims.parse_int "1"))


let separate_break_map = (fun sep f l -> (let _165_33 = (let _165_32 = (let _165_31 = (FStar_Pprint.op_Hat_Hat sep break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_31))
in (FStar_Pprint.separate_map _165_32 f l))
in (FStar_Pprint.group _165_33)))


let precede_break_separate_map = (fun prec sep f l -> (let _165_50 = (let _165_43 = (FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space)
in (let _165_42 = (let _165_41 = (FStar_List.hd l)
in (FStar_All.pipe_right _165_41 f))
in (FStar_Pprint.precede _165_43 _165_42)))
in (let _165_49 = (let _165_48 = (FStar_List.tl l)
in (FStar_Pprint.concat_map (fun x -> (let _165_47 = (let _165_46 = (let _165_45 = (f x)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_45))
in (FStar_Pprint.op_Hat_Hat sep _165_46))
in (FStar_Pprint.op_Hat_Hat break1 _165_47))) _165_48))
in (FStar_Pprint.op_Hat_Hat _165_50 _165_49))))


let concat_break_map = (fun f l -> (let _165_58 = (FStar_Pprint.concat_map (fun x -> (let _165_57 = (f x)
in (FStar_Pprint.op_Hat_Hat _165_57 break1))) l)
in (FStar_Pprint.group _165_58)))


let parens_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lparen contents FStar_Pprint.rparen))


let soft_parens_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lparen contents FStar_Pprint.rparen))


let braces_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbrace contents FStar_Pprint.rbrace))


let soft_braces_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbrace contents FStar_Pprint.rbrace))


let brackets_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbracket contents FStar_Pprint.rbracket))


let soft_brackets_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbracket contents FStar_Pprint.rbracket))


let separate_map_or_flow = (fun sep f l -> if ((FStar_List.length l) < (Prims.parse_int "10")) then begin
(FStar_Pprint.separate_map sep f l)
end else begin
(FStar_Pprint.flow_map sep f l)
end)


let doc_of_fsdoc : (Prims.string * (Prims.string * Prims.string) Prims.list)  ->  FStar_Pprint.document = (fun _67_52 -> (match (_67_52) with
| (comment, keywords) -> begin
(let _165_90 = (let _165_89 = (let _165_88 = (str comment)
in (let _165_87 = (let _165_86 = (let _165_85 = (FStar_Pprint.separate_map FStar_Pprint.comma (fun _67_55 -> (match (_67_55) with
| (k, v) -> begin
(let _165_84 = (let _165_83 = (str k)
in (let _165_82 = (let _165_81 = (let _165_80 = (str v)
in (_165_80)::[])
in (FStar_Pprint.rarrow)::_165_81)
in (_165_83)::_165_82))
in (FStar_Pprint.concat _165_84))
end)) keywords)
in (_165_85)::[])
in (FStar_Pprint.space)::_165_86)
in (_165_88)::_165_87))
in (FStar_Pprint.concat _165_89))
in (FStar_Pprint.group _165_90))
end))


let is_unit : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Const (FStar_Const.Const_unit) -> begin
true
end
| _67_60 -> begin
false
end))


let matches_var : FStar_Parser_AST.term  ->  FStar_Ident.ident  ->  Prims.bool = (fun t x -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (y) -> begin
(x.FStar_Ident.idText = (FStar_Ident.text_of_lid y))
end
| _67_66 -> begin
false
end))


let is_tuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Syntax_Util.is_tuple_data_lid'


let is_dtuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Syntax_Util.is_dtuple_data_lid'


let is_list_structure : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun cons_lid nil_lid -> (

let rec aux = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (lid, []) -> begin
(FStar_Ident.lid_equals lid nil_lid)
end
| FStar_Parser_AST.Construct (lid, (_67_81)::((e2, _67_78))::[]) -> begin
((FStar_Ident.lid_equals lid cons_lid) && (aux e2))
end
| _67_86 -> begin
false
end))
in aux))


let is_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Syntax_Const.cons_lid FStar_Syntax_Const.nil_lid)


let is_lex_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Syntax_Const.lexcons_lid FStar_Syntax_Const.lextop_lid)


let rec extract_from_list : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (_67_89, []) -> begin
[]
end
| FStar_Parser_AST.Construct (_67_94, ((e1, FStar_Parser_AST.Nothing))::((e2, FStar_Parser_AST.Nothing))::[]) -> begin
(let _165_113 = (extract_from_list e2)
in (e1)::_165_113)
end
| _67_105 -> begin
(let _165_115 = (let _165_114 = (FStar_Parser_AST.term_to_string e)
in (FStar_Util.format1 "Not a list %s" _165_114))
in (failwith _165_115))
end))


let is_array : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (lid); FStar_Parser_AST.range = _67_110; FStar_Parser_AST.level = _67_108}, l, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals lid FStar_Syntax_Const.array_mk_array_lid) && (is_list l))
end
| _67_119 -> begin
false
end))


let rec is_ref_set : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (maybe_empty_lid) -> begin
(FStar_Ident.lid_equals maybe_empty_lid FStar_Syntax_Const.tset_empty)
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_singleton_lid); FStar_Parser_AST.range = _67_126; FStar_Parser_AST.level = _67_124}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_ref_lid); FStar_Parser_AST.range = _67_137; FStar_Parser_AST.level = _67_135}, e, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = _67_133; FStar_Parser_AST.level = _67_131}, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals maybe_singleton_lid FStar_Syntax_Const.tset_singleton) && (FStar_Ident.lid_equals maybe_ref_lid FStar_Syntax_Const.heap_ref))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_union_lid); FStar_Parser_AST.range = _67_156; FStar_Parser_AST.level = _67_154}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = _67_152; FStar_Parser_AST.level = _67_150}, e2, FStar_Parser_AST.Nothing) -> begin
(((FStar_Ident.lid_equals maybe_union_lid FStar_Syntax_Const.tset_union) && (is_ref_set e1)) && (is_ref_set e2))
end
| _67_170 -> begin
false
end))


let rec extract_from_ref_set : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (_67_173) -> begin
[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (_67_180); FStar_Parser_AST.range = _67_178; FStar_Parser_AST.level = _67_176}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (_67_192); FStar_Parser_AST.range = _67_190; FStar_Parser_AST.level = _67_188}, e, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = _67_186; FStar_Parser_AST.level = _67_184}, FStar_Parser_AST.Nothing) -> begin
(e)::[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (_67_212); FStar_Parser_AST.range = _67_210; FStar_Parser_AST.level = _67_208}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = _67_206; FStar_Parser_AST.level = _67_204}, e2, FStar_Parser_AST.Nothing) -> begin
(let _165_123 = (extract_from_ref_set e1)
in (let _165_122 = (extract_from_ref_set e2)
in (FStar_List.append _165_123 _165_122)))
end
| _67_225 -> begin
(let _165_125 = (let _165_124 = (FStar_Parser_AST.term_to_string e)
in (FStar_Util.format1 "Not a ref set %s" _165_124))
in (failwith _165_125))
end))


let is_general_application : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (not (((is_array e) || (is_ref_set e)))))


let is_general_construction : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (not (((is_list e) || (is_lex_list e)))))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun e -> (

let rec aux = (fun e acc -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App (head, arg, imp) -> begin
(aux head ((((arg), (imp)))::acc))
end
| _67_238 -> begin
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


let matches_level = (fun s _67_253 -> (match (_67_253) with
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
in (FStar_List.mapi (fun i _67_263 -> (match (_67_263) with
| (assoc, tokens) -> begin
(((levels_from_associativity i assoc)), (tokens))
end)) level_associativity_spec))


let assign_levels : associativity_level Prims.list  ->  Prims.string  ->  (Prims.int * Prims.int * Prims.int) = (fun token_associativity_spec s -> (match ((FStar_List.tryFind (matches_level s) level_table)) with
| Some (assoc_levels, _67_268) -> begin
assoc_levels
end
| _67_272 -> begin
(failwith (Prims.strcat "Unrecognized operator " s))
end))


let max : Prims.int  ->  Prims.int  ->  Prims.int = (fun k1 k2 -> if (k1 > k2) then begin
k1
end else begin
k2
end)


let max_level = (fun l -> (

let find_level_and_max = (fun n level -> (match ((FStar_List.tryFind (fun _67_282 -> (match (_67_282) with
| (_67_280, tokens) -> begin
(tokens = (Prims.snd level))
end)) level_table)) with
| Some ((_67_284, l, _67_287), _67_290) -> begin
(max n l)
end
| None -> begin
(let _165_169 = (let _165_168 = (let _165_167 = (FStar_List.map token_to_string (Prims.snd level))
in (FStar_String.concat "," _165_167))
in (FStar_Util.format1 "Undefined associativity level %s" _165_168))
in (failwith _165_169))
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

let _67_310 = (FStar_ST.op_Colon_Equals comment_stack cs)
in (let _165_189 = (let _165_188 = (let _165_187 = (str comment)
in (FStar_Pprint.op_Hat_Hat _165_187 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat acc _165_188))
in (comments_before_pos _165_189 print_pos lookahead_pos)))
end else begin
(let _165_190 = (FStar_Range.range_before_pos crange lookahead_pos)
in ((acc), (_165_190)))
end
end))
in (

let _67_314 = (let _165_193 = (let _165_191 = (FStar_Range.start_of_range tmrange)
in (FStar_Range.end_of_line _165_191))
in (let _165_192 = (FStar_Range.end_of_range tmrange)
in (comments_before_pos FStar_Pprint.empty _165_193 _165_192)))
in (match (_67_314) with
| (comments, has_lookahead) -> begin
(

let printed_e = (printer tm)
in (

let comments = if has_lookahead then begin
(

let pos = (FStar_Range.end_of_range tmrange)
in (let _165_194 = (comments_before_pos comments pos pos)
in (Prims.fst _165_194)))
end else begin
comments
end
in (let _165_195 = (FStar_Pprint.op_Hat_Hat comments printed_e)
in (FStar_Pprint.group _165_195))))
end))))


let rec p_decl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (let _165_301 = (FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc)
in (let _165_300 = (let _165_299 = (p_attributes d.FStar_Parser_AST.attrs)
in (let _165_298 = (let _165_297 = (p_qualifiers d.FStar_Parser_AST.quals)
in (let _165_296 = (let _165_295 = (p_rawDecl d)
in (FStar_Pprint.op_Hat_Hat (if (d.FStar_Parser_AST.quals = []) then begin
FStar_Pprint.empty
end else begin
break1
end) _165_295))
in (FStar_Pprint.op_Hat_Hat _165_297 _165_296)))
in (FStar_Pprint.op_Hat_Hat _165_299 _165_298)))
in (FStar_Pprint.op_Hat_Hat _165_301 _165_300))))
and p_attributes : FStar_Parser_AST.attributes_  ->  FStar_Pprint.document = (fun attrs -> (let _165_305 = (let _165_303 = (str "@")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket _165_303))
in (let _165_304 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline)
in (FStar_Pprint.surround_separate_map (Prims.parse_int "0") (Prims.parse_int "2") FStar_Pprint.empty _165_305 FStar_Pprint.space _165_304 p_atomicTerm attrs))))
and p_fsdoc : FStar_Parser_AST.fsdoc  ->  FStar_Pprint.document = (fun _67_322 -> (match (_67_322) with
| (doc, kwd_args) -> begin
(

let kwd_args_doc = (match (kwd_args) with
| [] -> begin
FStar_Pprint.empty
end
| kwd_args -> begin
(

let process_kwd_arg = (fun _67_328 -> (match (_67_328) with
| (kwd, arg) -> begin
(let _165_313 = (str "@")
in (let _165_312 = (let _165_311 = (str kwd)
in (let _165_310 = (let _165_309 = (str arg)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_309))
in (FStar_Pprint.op_Hat_Hat _165_311 _165_310)))
in (FStar_Pprint.op_Hat_Hat _165_313 _165_312)))
end))
in (let _165_315 = (let _165_314 = (FStar_Pprint.separate_map FStar_Pprint.hardline process_kwd_arg kwd_args)
in (FStar_Pprint.op_Hat_Hat _165_314 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline _165_315)))
end)
in (let _165_323 = (let _165_322 = (let _165_321 = (let _165_320 = (let _165_319 = (str doc)
in (let _165_318 = (let _165_317 = (let _165_316 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _165_316))
in (FStar_Pprint.op_Hat_Hat kwd_args_doc _165_317))
in (FStar_Pprint.op_Hat_Hat _165_319 _165_318)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _165_320))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _165_321))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_322))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline _165_323)))
end))
and p_rawDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Open (uid) -> begin
(let _165_327 = (let _165_326 = (str "open")
in (let _165_325 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat _165_326 _165_325)))
in (FStar_Pprint.group _165_327))
end
| FStar_Parser_AST.Include (uid) -> begin
(let _165_330 = (let _165_329 = (str "include")
in (let _165_328 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat _165_329 _165_328)))
in (FStar_Pprint.group _165_330))
end
| FStar_Parser_AST.ModuleAbbrev (uid1, uid2) -> begin
(let _165_337 = (let _165_335 = (str "module")
in (let _165_334 = (let _165_333 = (let _165_332 = (p_uident uid1)
in (let _165_331 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _165_332 _165_331)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_333))
in (FStar_Pprint.op_Hat_Hat _165_335 _165_334)))
in (let _165_336 = (p_quident uid2)
in (op_Hat_Slash_Plus_Hat _165_337 _165_336)))
end
| FStar_Parser_AST.TopLevelModule (uid) -> begin
(let _165_341 = (let _165_340 = (str "module")
in (let _165_339 = (let _165_338 = (p_quident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_338))
in (FStar_Pprint.op_Hat_Hat _165_340 _165_339)))
in (FStar_Pprint.group _165_341))
end
| FStar_Parser_AST.KindAbbrev (_67_342) -> begin
(failwith "Deprecated, please stop throwing your old stuff at me !")
end
| FStar_Parser_AST.Tycon (true, ((FStar_Parser_AST.TyconAbbrev (uid, tpars, None, t), None))::[]) -> begin
(

let effect_prefix_doc = (let _165_344 = (str "effect")
in (let _165_343 = (let _165_342 = (p_uident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_342))
in (FStar_Pprint.op_Hat_Hat _165_344 _165_343)))
in (let _165_347 = (let _165_345 = (p_typars tpars)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") effect_prefix_doc _165_345 FStar_Pprint.equals))
in (let _165_346 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _165_347 _165_346))))
end
| FStar_Parser_AST.Tycon (false, tcdefs) -> begin
(let _165_349 = (str "type")
in (let _165_348 = (str "and")
in (precede_break_separate_map _165_349 _165_348 p_fsdocTypeDeclPairs tcdefs)))
end
| FStar_Parser_AST.TopLevelLet (q, lbs) -> begin
(

let let_doc = (let _165_351 = (str "let")
in (let _165_350 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat _165_351 _165_350)))
in (let _165_352 = (str "and")
in (precede_break_separate_map let_doc _165_352 p_letbinding lbs)))
end
| FStar_Parser_AST.Val (lid, t) -> begin
(let _165_359 = (let _165_357 = (str "val")
in (let _165_356 = (let _165_355 = (let _165_354 = (p_lident lid)
in (let _165_353 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat _165_354 _165_353)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_355))
in (FStar_Pprint.op_Hat_Hat _165_357 _165_356)))
in (let _165_358 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _165_359 _165_358)))
end
| FStar_Parser_AST.Assume (id, t) -> begin
(

let decl_keyword = if (let _165_360 = (FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_All.pipe_right _165_360 FStar_Util.is_upper)) then begin
FStar_Pprint.empty
end else begin
(let _165_361 = (str "val")
in (FStar_Pprint.op_Hat_Hat _165_361 FStar_Pprint.space))
end
in (let _165_366 = (let _165_364 = (let _165_363 = (p_ident id)
in (let _165_362 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat _165_363 _165_362)))
in (FStar_Pprint.op_Hat_Hat decl_keyword _165_364))
in (let _165_365 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _165_366 _165_365))))
end
| FStar_Parser_AST.Exception (uid, t_opt) -> begin
(let _165_374 = (str "exception")
in (let _165_373 = (let _165_372 = (let _165_371 = (p_uident uid)
in (let _165_370 = (FStar_Pprint.optional (fun t -> (let _165_369 = (str "of")
in (let _165_368 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _165_369 _165_368)))) t_opt)
in (FStar_Pprint.op_Hat_Hat _165_371 _165_370)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_372))
in (FStar_Pprint.op_Hat_Hat _165_374 _165_373)))
end
| FStar_Parser_AST.NewEffect (ne) -> begin
(let _165_377 = (str "new_effect")
in (let _165_376 = (let _165_375 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_375))
in (FStar_Pprint.op_Hat_Hat _165_377 _165_376)))
end
| FStar_Parser_AST.SubEffect (se) -> begin
(let _165_380 = (str "sub_effect")
in (let _165_379 = (let _165_378 = (p_subEffect se)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_378))
in (FStar_Pprint.op_Hat_Hat _165_380 _165_379)))
end
| FStar_Parser_AST.NewEffectForFree (ne) -> begin
(let _165_383 = (str "new_effect_for_free")
in (let _165_382 = (let _165_381 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_381))
in (FStar_Pprint.op_Hat_Hat _165_383 _165_382)))
end
| FStar_Parser_AST.Pragma (p) -> begin
(p_pragma p)
end
| FStar_Parser_AST.Fsdoc (doc) -> begin
(let _165_384 = (p_fsdoc doc)
in (FStar_Pprint.op_Hat_Hat _165_384 FStar_Pprint.hardline))
end
| FStar_Parser_AST.Main (_67_391) -> begin
(failwith "*Main declaration* : Is that really still in use ??")
end
| FStar_Parser_AST.Tycon (true, _67_395) -> begin
(failwith "Effect abbreviation is expected to be defined by an abbreviation")
end))
and p_pragma : FStar_Parser_AST.pragma  ->  FStar_Pprint.document = (fun _67_4 -> (match (_67_4) with
| FStar_Parser_AST.SetOptions (s) -> begin
(let _165_389 = (str "#set-options")
in (let _165_388 = (let _165_387 = (let _165_386 = (str s)
in (FStar_Pprint.dquotes _165_386))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_387))
in (FStar_Pprint.op_Hat_Hat _165_389 _165_388)))
end
| FStar_Parser_AST.ResetOptions (s_opt) -> begin
(let _165_394 = (str "#reset-options")
in (let _165_393 = (FStar_Pprint.optional (fun s -> (let _165_392 = (let _165_391 = (str s)
in (FStar_Pprint.dquotes _165_391))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_392))) s_opt)
in (FStar_Pprint.op_Hat_Hat _165_394 _165_393)))
end))
and p_typars : FStar_Parser_AST.binder Prims.list  ->  FStar_Pprint.document = (fun bs -> (p_binders true bs))
and p_fsdocTypeDeclPairs : (FStar_Parser_AST.tycon * FStar_Parser_AST.fsdoc Prims.option)  ->  FStar_Pprint.document = (fun _67_407 -> (match (_67_407) with
| (typedecl, fsdoc_opt) -> begin
(let _165_398 = (FStar_Pprint.optional p_fsdoc fsdoc_opt)
in (let _165_397 = (p_typeDecl typedecl)
in (FStar_Pprint.op_Hat_Hat _165_398 _165_397)))
end))
and p_typeDecl : FStar_Parser_AST.tycon  ->  FStar_Pprint.document = (fun _67_5 -> (match (_67_5) with
| FStar_Parser_AST.TyconAbstract (lid, bs, typ_opt) -> begin
(

let empty' = (fun _67_414 -> (match (()) with
| () -> begin
FStar_Pprint.empty
end))
in (p_typeDeclPrefix lid bs typ_opt empty'))
end
| FStar_Parser_AST.TyconAbbrev (lid, bs, typ_opt, t) -> begin
(

let f = (fun _67_423 -> (match (()) with
| () -> begin
(let _165_404 = (p_typ t)
in (prefix2 FStar_Pprint.equals _165_404))
end))
in (p_typeDeclPrefix lid bs typ_opt f))
end
| FStar_Parser_AST.TyconRecord (lid, bs, typ_opt, record_field_decls) -> begin
(

let p_recordFieldAndComments = (fun _67_434 -> (match (_67_434) with
| (lid, t, doc_opt) -> begin
(with_comment p_recordFieldDecl ((lid), (t), (doc_opt)) t.FStar_Parser_AST.range)
end))
in (

let p_fields = (fun _67_436 -> (match (()) with
| () -> begin
(let _165_412 = (let _165_411 = (let _165_410 = (let _165_409 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (FStar_Pprint.separate_map _165_409 p_recordFieldAndComments record_field_decls))
in (braces_with_nesting _165_410))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_411))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.equals _165_412))
end))
in (p_typeDeclPrefix lid bs typ_opt p_fields)))
end
| FStar_Parser_AST.TyconVariant (lid, bs, typ_opt, ct_decls) -> begin
(

let p_constructorBranchAndComments = (fun _67_448 -> (match (_67_448) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let range = (let _165_416 = (FStar_Util.map_opt t_opt (fun t -> t.FStar_Parser_AST.range))
in (FStar_Util.dflt uid.FStar_Ident.idRange _165_416))
in (

let p_constructorBranch = (fun decl -> (let _165_421 = (let _165_420 = (let _165_419 = (p_constructorDecl decl)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_419))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar _165_420))
in (FStar_Pprint.group _165_421)))
in (with_comment p_constructorBranch ((uid), (t_opt), (doc_opt), (use_of)) range)))
end))
in (

let datacon_doc = (fun _67_454 -> (match (()) with
| () -> begin
(let _165_424 = (FStar_Pprint.separate_map break1 p_constructorBranchAndComments ct_decls)
in (FStar_Pprint.group _165_424))
end))
in (p_typeDeclPrefix lid bs typ_opt (fun _67_455 -> (match (()) with
| () -> begin
(let _165_426 = (datacon_doc ())
in (prefix2 FStar_Pprint.equals _165_426))
end)))))
end))
and p_typeDeclPrefix : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.knd Prims.option  ->  (Prims.unit  ->  FStar_Pprint.document)  ->  FStar_Pprint.document = (fun lid bs typ_opt cont -> if ((bs = []) && (typ_opt = None)) then begin
(let _165_436 = (p_ident lid)
in (let _165_435 = (let _165_434 = (cont ())
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_434))
in (FStar_Pprint.op_Hat_Hat _165_436 _165_435)))
end else begin
(

let binders_doc = (let _165_442 = (p_typars bs)
in (let _165_441 = (FStar_Pprint.optional (fun t -> (let _165_440 = (let _165_439 = (let _165_438 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_438))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_439))
in (FStar_Pprint.op_Hat_Hat break1 _165_440))) typ_opt)
in (FStar_Pprint.op_Hat_Hat _165_442 _165_441)))
in (let _165_444 = (p_ident lid)
in (let _165_443 = (cont ())
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_444 binders_doc _165_443))))
end)
and p_recordFieldDecl : (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc Prims.option)  ->  FStar_Pprint.document = (fun _67_465 -> (match (_67_465) with
| (lid, t, doc_opt) -> begin
(let _165_451 = (let _165_450 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (let _165_449 = (let _165_448 = (p_lident lid)
in (let _165_447 = (let _165_446 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_446))
in (FStar_Pprint.op_Hat_Hat _165_448 _165_447)))
in (FStar_Pprint.op_Hat_Hat _165_450 _165_449)))
in (FStar_Pprint.group _165_451))
end))
and p_constructorDecl : (FStar_Ident.ident * FStar_Parser_AST.term Prims.option * FStar_Parser_AST.fsdoc Prims.option * Prims.bool)  ->  FStar_Pprint.document = (fun _67_470 -> (match (_67_470) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let sep = if use_of then begin
(str "of")
end else begin
FStar_Pprint.colon
end
in (

let uid_doc = (p_uident uid)
in (let _165_458 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (let _165_457 = (default_or_map uid_doc (fun t -> (let _165_456 = (let _165_454 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep)
in (FStar_Pprint.op_Hat_Hat uid_doc _165_454))
in (let _165_455 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _165_456 _165_455)))) t_opt)
in (FStar_Pprint.op_Hat_Hat _165_458 _165_457)))))
end))
and p_letbinding : (FStar_Parser_AST.pattern * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun _67_476 -> (match (_67_476) with
| (pat, e) -> begin
(

let pat_doc = (

let _67_485 = (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, t) -> begin
(let _165_463 = (let _165_462 = (let _165_461 = (let _165_460 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat break1 _165_460))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_461))
in (FStar_Pprint.op_Hat_Hat break1 _165_462))
in ((pat), (_165_463)))
end
| _67_482 -> begin
((pat), (FStar_Pprint.empty))
end)
in (match (_67_485) with
| (pat, ascr_doc) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _67_490); FStar_Parser_AST.prange = _67_487}, pats) -> begin
(let _165_466 = (p_lident x)
in (let _165_465 = (let _165_464 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Hat _165_464 ascr_doc))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_466 _165_465 FStar_Pprint.equals)))
end
| _67_498 -> begin
(let _165_469 = (let _165_468 = (p_tuplePattern pat)
in (let _165_467 = (FStar_Pprint.op_Hat_Slash_Hat ascr_doc FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _165_468 _165_467)))
in (FStar_Pprint.group _165_469))
end)
end))
in (let _165_470 = (p_term e)
in (prefix2 pat_doc _165_470)))
end))
and p_newEffect : FStar_Parser_AST.effect_decl  ->  FStar_Pprint.document = (fun _67_6 -> (match (_67_6) with
| FStar_Parser_AST.RedefineEffect (lid, bs, t) -> begin
(p_effectRedefinition lid bs t)
end
| FStar_Parser_AST.DefineEffect (lid, bs, t, eff_decls, action_decls) -> begin
(p_effectDefinition lid bs t eff_decls action_decls)
end))
and p_effectRedefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun uid bs t -> (let _165_478 = (p_uident uid)
in (let _165_477 = (p_binders true bs)
in (let _165_476 = (let _165_475 = (p_simpleTerm t)
in (prefix2 FStar_Pprint.equals _165_475))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_478 _165_477 _165_476)))))
and p_effectDefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun uid bs t eff_decls action_decls -> (let _165_495 = (let _165_494 = (let _165_488 = (let _165_487 = (p_uident uid)
in (let _165_486 = (p_binders true bs)
in (let _165_485 = (let _165_484 = (p_typ t)
in (prefix2 FStar_Pprint.colon _165_484))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_487 _165_486 _165_485))))
in (FStar_Pprint.group _165_488))
in (let _165_493 = (let _165_492 = (let _165_490 = (str "with")
in (let _165_489 = (separate_break_map FStar_Pprint.semi p_effectDecl eff_decls)
in (prefix2 _165_490 _165_489)))
in (let _165_491 = (p_actionDecls action_decls)
in (FStar_Pprint.op_Hat_Hat _165_492 _165_491)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_494 _165_493)))
in (braces_with_nesting _165_495)))
and p_actionDecls : FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun _67_7 -> (match (_67_7) with
| [] -> begin
FStar_Pprint.empty
end
| l -> begin
(let _165_499 = (let _165_498 = (str "and actions")
in (let _165_497 = (separate_break_map FStar_Pprint.semi p_effectDecl l)
in (prefix2 _165_498 _165_497)))
in (FStar_Pprint.op_Hat_Hat break1 _165_499))
end))
and p_effectDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (false, ((FStar_Parser_AST.TyconAbbrev (lid, [], None, e), None))::[]) -> begin
(let _165_504 = (let _165_502 = (p_lident lid)
in (let _165_501 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _165_502 _165_501)))
in (let _165_503 = (p_simpleTerm e)
in (prefix2 _165_504 _165_503)))
end
| _67_538 -> begin
(let _165_506 = (let _165_505 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "Not a declaration of an effect member... or at least I hope so : %s" _165_505))
in (failwith _165_506))
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

let p_lift = (fun _67_552 -> (match (_67_552) with
| (kwd, t) -> begin
(let _165_513 = (let _165_511 = (str kwd)
in (let _165_510 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _165_511 _165_510)))
in (let _165_512 = (p_simpleTerm t)
in (prefix2 _165_513 _165_512)))
end))
in (separate_break_map FStar_Pprint.semi p_lift lifts)))
in (let _165_521 = (let _165_518 = (let _165_516 = (p_quident lift.FStar_Parser_AST.msource)
in (let _165_515 = (let _165_514 = (str "~>")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_514))
in (FStar_Pprint.op_Hat_Hat _165_516 _165_515)))
in (let _165_517 = (p_quident lift.FStar_Parser_AST.mdest)
in (prefix2 _165_518 _165_517)))
in (let _165_520 = (let _165_519 = (braces_with_nesting lift_op_doc)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_519))
in (FStar_Pprint.op_Hat_Hat _165_521 _165_520)))))
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
and p_qualifiers : FStar_Parser_AST.qualifiers  ->  FStar_Pprint.document = (fun qs -> (let _165_524 = (FStar_Pprint.separate_map break1 p_qualifier qs)
in (FStar_Pprint.group _165_524)))
and p_letqualifier : FStar_Parser_AST.let_qualifier  ->  FStar_Pprint.document = (fun _67_9 -> (match (_67_9) with
| FStar_Parser_AST.Rec -> begin
(let _165_526 = (str "rec")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_526))
end
| FStar_Parser_AST.Mutable -> begin
(let _165_527 = (str "mutable")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_527))
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
(let _165_532 = (let _165_531 = (let _165_530 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space)
in (FStar_Pprint.op_Hat_Hat break1 _165_530))
in (FStar_Pprint.separate_map _165_531 p_tuplePattern pats))
in (FStar_Pprint.group _165_532))
end
| _67_586 -> begin
(p_tuplePattern p)
end))
and p_tuplePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTuple (pats, false) -> begin
(let _165_535 = (let _165_534 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map _165_534 p_constructorPattern pats))
in (FStar_Pprint.group _165_535))
end
| _67_593 -> begin
(p_constructorPattern p)
end))
and p_constructorPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (maybe_cons_lid); FStar_Parser_AST.prange = _67_596}, (hd)::(tl)::[]) when (FStar_Ident.lid_equals maybe_cons_lid FStar_Syntax_Const.cons_lid) -> begin
(let _165_539 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon)
in (let _165_538 = (p_constructorPattern hd)
in (let _165_537 = (p_constructorPattern tl)
in (infix0 _165_539 _165_538 _165_537))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (uid); FStar_Parser_AST.prange = _67_606}, pats) -> begin
(let _165_541 = (p_quident uid)
in (let _165_540 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (prefix2 _165_541 _165_540)))
end
| _67_614 -> begin
(p_atomicPattern p)
end))
and p_atomicPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, t) -> begin
(let _165_545 = (let _165_544 = (p_tuplePattern pat)
in (let _165_543 = (p_typ t)
in (infix2 FStar_Pprint.colon _165_544 _165_543)))
in (soft_parens_with_nesting _165_545))
end
| FStar_Parser_AST.PatList (pats) -> begin
(let _165_546 = (separate_break_map FStar_Pprint.semi p_tuplePattern pats)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket _165_546 FStar_Pprint.rbracket))
end
| FStar_Parser_AST.PatRecord (pats) -> begin
(

let p_recordFieldPat = (fun _67_627 -> (match (_67_627) with
| (lid, pat) -> begin
(let _165_550 = (p_qlident lid)
in (let _165_549 = (p_tuplePattern pat)
in (infix2 FStar_Pprint.equals _165_550 _165_549)))
end))
in (let _165_551 = (separate_break_map FStar_Pprint.semi p_recordFieldPat pats)
in (soft_braces_with_nesting _165_551)))
end
| FStar_Parser_AST.PatTuple (pats, true) -> begin
(let _165_554 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (let _165_553 = (separate_break_map FStar_Pprint.comma p_constructorPattern pats)
in (let _165_552 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_554 _165_553 _165_552))))
end
| FStar_Parser_AST.PatTvar (tv, arg_qualifier_opt) -> begin
(

let _67_636 = ()
in (p_tvar tv))
end
| FStar_Parser_AST.PatOp (op) -> begin
(let _165_558 = (let _165_557 = (let _165_556 = (str op)
in (let _165_555 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat _165_556 _165_555)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_557))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_558))
end
| FStar_Parser_AST.PatWild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.PatConst (c) -> begin
(p_constant c)
end
| FStar_Parser_AST.PatVar (lid, aqual) -> begin
(let _165_560 = (FStar_Pprint.optional p_aqual aqual)
in (let _165_559 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat _165_560 _165_559)))
end
| FStar_Parser_AST.PatName (uid) -> begin
(p_quident uid)
end
| FStar_Parser_AST.PatOr (_67_650) -> begin
(failwith "Inner or pattern !")
end
| (FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (_); FStar_Parser_AST.prange = _}, _)) | (FStar_Parser_AST.PatTuple (_, false)) -> begin
(let _165_561 = (p_tuplePattern p)
in (soft_parens_with_nesting _165_561))
end
| _67_668 -> begin
(let _165_563 = (let _165_562 = (FStar_Parser_AST.pat_to_string p)
in (FStar_Util.format1 "Invalid pattern %s" _165_562))
in (failwith _165_563))
end))
and p_binder : Prims.bool  ->  FStar_Parser_AST.binder  ->  FStar_Pprint.document = (fun is_atomic b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (lid) -> begin
(let _165_567 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (let _165_566 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat _165_567 _165_566)))
end
| FStar_Parser_AST.TVariable (lid) -> begin
(p_lident lid)
end
| FStar_Parser_AST.Annotated (lid, t) -> begin
(

let doc = (let _165_572 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (let _165_571 = (let _165_570 = (p_lident lid)
in (let _165_569 = (let _165_568 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_568))
in (FStar_Pprint.op_Hat_Hat _165_570 _165_569)))
in (FStar_Pprint.op_Hat_Hat _165_572 _165_571)))
in if is_atomic then begin
(let _165_574 = (let _165_573 = (FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_573))
in (FStar_Pprint.group _165_574))
end else begin
(FStar_Pprint.group doc)
end)
end
| FStar_Parser_AST.TAnnotated (_67_681) -> begin
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
(let _165_588 = (let _165_586 = (let _165_585 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat _165_585 FStar_Pprint.semi))
in (FStar_Pprint.group _165_586))
in (let _165_587 = (p_term e2)
in (FStar_Pprint.op_Hat_Slash_Hat _165_588 _165_587)))
end
| _67_700 -> begin
(let _165_589 = (p_noSeqTerm e)
in (FStar_Pprint.group _165_589))
end))
and p_noSeqTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_noSeqTerm' e e.FStar_Parser_AST.range))
and p_noSeqTerm' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Ascribed (e, t) -> begin
(let _165_596 = (let _165_595 = (p_tmIff e)
in (let _165_594 = (let _165_593 = (let _165_592 = (p_typ t)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon _165_592))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.langle _165_593))
in (FStar_Pprint.op_Hat_Slash_Hat _165_595 _165_594)))
in (FStar_Pprint.group _165_596))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::(e3)::[]) when (op = ".()<-") -> begin
(let _165_607 = (let _165_606 = (let _165_603 = (let _165_602 = (p_atomicTermNotQUident e1)
in (let _165_601 = (let _165_600 = (let _165_599 = (let _165_597 = (p_term e2)
in (soft_parens_with_nesting _165_597))
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
| FStar_Parser_AST.Op (op, (e1)::(e2)::(e3)::[]) when (op = ".[]<-") -> begin
(let _165_618 = (let _165_617 = (let _165_614 = (let _165_613 = (p_atomicTermNotQUident e1)
in (let _165_612 = (let _165_611 = (let _165_610 = (let _165_608 = (p_term e2)
in (soft_brackets_with_nesting _165_608))
in (let _165_609 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat _165_610 _165_609)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_611))
in (FStar_Pprint.op_Hat_Hat _165_613 _165_612)))
in (FStar_Pprint.group _165_614))
in (let _165_616 = (let _165_615 = (p_noSeqTerm e3)
in (jump2 _165_615))
in (FStar_Pprint.op_Hat_Hat _165_617 _165_616)))
in (FStar_Pprint.group _165_618))
end
| FStar_Parser_AST.Requires (e, wtf) -> begin
(

let _67_725 = ()
in (let _165_621 = (let _165_620 = (str "requires")
in (let _165_619 = (p_typ e)
in (FStar_Pprint.op_Hat_Slash_Hat _165_620 _165_619)))
in (FStar_Pprint.group _165_621)))
end
| FStar_Parser_AST.Ensures (e, wtf) -> begin
(

let _67_731 = ()
in (let _165_624 = (let _165_623 = (str "ensures")
in (let _165_622 = (p_typ e)
in (FStar_Pprint.op_Hat_Slash_Hat _165_623 _165_622)))
in (FStar_Pprint.group _165_624)))
end
| FStar_Parser_AST.Attributes (es) -> begin
(let _165_627 = (let _165_626 = (str "attributes")
in (let _165_625 = (FStar_Pprint.separate_map break1 p_atomicTerm es)
in (FStar_Pprint.op_Hat_Slash_Hat _165_626 _165_625)))
in (FStar_Pprint.group _165_627))
end
| FStar_Parser_AST.If (e1, e2, e3) -> begin
if (is_unit e3) then begin
(let _165_634 = (let _165_633 = (let _165_629 = (str "if")
in (let _165_628 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat _165_629 _165_628)))
in (let _165_632 = (let _165_631 = (str "then")
in (let _165_630 = (p_noSeqTerm e2)
in (op_Hat_Slash_Plus_Hat _165_631 _165_630)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_633 _165_632)))
in (FStar_Pprint.group _165_634))
end else begin
(

let e2_doc = (match (e2.FStar_Parser_AST.tm) with
| FStar_Parser_AST.If (_67_741, _67_743, e3) when (is_unit e3) -> begin
(let _165_635 = (p_noSeqTerm e2)
in (soft_parens_with_nesting _165_635))
end
| _67_748 -> begin
(p_noSeqTerm e2)
end)
in (let _165_645 = (let _165_644 = (let _165_637 = (str "if")
in (let _165_636 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat _165_637 _165_636)))
in (let _165_643 = (let _165_642 = (let _165_638 = (str "then")
in (op_Hat_Slash_Plus_Hat _165_638 e2_doc))
in (let _165_641 = (let _165_640 = (str "else")
in (let _165_639 = (p_noSeqTerm e3)
in (op_Hat_Slash_Plus_Hat _165_640 _165_639)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_642 _165_641)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_644 _165_643)))
in (FStar_Pprint.group _165_645)))
end
end
| FStar_Parser_AST.TryWith (e, branches) -> begin
(let _165_652 = (let _165_651 = (let _165_647 = (str "try")
in (let _165_646 = (p_noSeqTerm e)
in (prefix2 _165_647 _165_646)))
in (let _165_650 = (let _165_649 = (str "with")
in (let _165_648 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat _165_649 _165_648)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_651 _165_650)))
in (FStar_Pprint.group _165_652))
end
| FStar_Parser_AST.Match (e, branches) -> begin
(let _165_658 = (let _165_657 = (let _165_655 = (str "match")
in (let _165_654 = (p_noSeqTerm e)
in (let _165_653 = (str "with")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_655 _165_654 _165_653))))
in (let _165_656 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat _165_657 _165_656)))
in (FStar_Pprint.group _165_658))
end
| FStar_Parser_AST.LetOpen (uid, e) -> begin
(let _165_664 = (let _165_663 = (let _165_661 = (str "let open")
in (let _165_660 = (p_quident uid)
in (let _165_659 = (str "in")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_661 _165_660 _165_659))))
in (let _165_662 = (p_term e)
in (FStar_Pprint.op_Hat_Slash_Hat _165_663 _165_662)))
in (FStar_Pprint.group _165_664))
end
| FStar_Parser_AST.Let (q, lbs, e) -> begin
(

let let_doc = (let _165_666 = (str "let")
in (let _165_665 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat _165_666 _165_665)))
in (let _165_672 = (let _165_670 = (let _165_669 = (let _165_667 = (str "and")
in (precede_break_separate_map let_doc _165_667 p_letbinding lbs))
in (let _165_668 = (str "in")
in (FStar_Pprint.op_Hat_Slash_Hat _165_669 _165_668)))
in (FStar_Pprint.group _165_670))
in (let _165_671 = (p_term e)
in (FStar_Pprint.op_Hat_Slash_Hat _165_672 _165_671))))
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, typ_opt); FStar_Parser_AST.prange = _67_769})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, branches); FStar_Parser_AST.range = _67_779; FStar_Parser_AST.level = _67_777}) when (matches_var maybe_x x) -> begin
(let _165_675 = (let _165_674 = (str "function")
in (let _165_673 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat _165_674 _165_673)))
in (FStar_Pprint.group _165_675))
end
| FStar_Parser_AST.Assign (id, e) -> begin
(let _165_679 = (let _165_678 = (p_lident id)
in (let _165_677 = (let _165_676 = (p_noSeqTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow _165_676))
in (FStar_Pprint.op_Hat_Slash_Hat _165_678 _165_677)))
in (FStar_Pprint.group _165_679))
end
| _67_792 -> begin
(p_typ e)
end))
and p_typ : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_typ' e e.FStar_Parser_AST.range))
and p_typ' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| (FStar_Parser_AST.QForall (bs, trigger, e1)) | (FStar_Parser_AST.QExists (bs, trigger, e1)) -> begin
(let _165_688 = (let _165_684 = (let _165_682 = (p_quantifier e)
in (FStar_Pprint.op_Hat_Hat _165_682 FStar_Pprint.space))
in (let _165_683 = (p_binders true bs)
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") _165_684 _165_683 FStar_Pprint.dot)))
in (let _165_687 = (let _165_686 = (p_trigger trigger)
in (let _165_685 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat _165_686 _165_685)))
in (prefix2 _165_688 _165_687)))
end
| _67_803 -> begin
(p_simpleTerm e)
end))
and p_quantifier : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.QForall (_67_806) -> begin
(str "forall")
end
| FStar_Parser_AST.QExists (_67_809) -> begin
(str "exists")
end
| _67_812 -> begin
(failwith "Imposible : p_quantifier called on a non-quantifier term")
end))
and p_trigger : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun _67_11 -> (match (_67_11) with
| [] -> begin
FStar_Pprint.empty
end
| pats -> begin
(let _165_697 = (let _165_696 = (let _165_695 = (str "pattern")
in (let _165_694 = (let _165_693 = (let _165_691 = (p_disjunctivePats pats)
in (jump2 _165_691))
in (let _165_692 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1)
in (FStar_Pprint.op_Hat_Slash_Hat _165_693 _165_692)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_695 _165_694)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_696))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace _165_697))
end))
and p_disjunctivePats : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun pats -> (let _165_699 = (str "\\/")
in (FStar_Pprint.separate_map _165_699 p_conjunctivePats pats)))
and p_conjunctivePats : FStar_Parser_AST.term Prims.list  ->  FStar_Pprint.document = (fun pats -> (let _165_701 = (FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats)
in (FStar_Pprint.group _165_701)))
and p_simpleTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Abs (pats, e) -> begin
(let _165_707 = (let _165_705 = (str "fun")
in (let _165_704 = (let _165_703 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Slash_Hat _165_703 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat _165_705 _165_704)))
in (let _165_706 = (p_term e)
in (op_Hat_Slash_Plus_Hat _165_707 _165_706)))
end
| _67_824 -> begin
(p_tmIff e)
end))
and p_maybeFocusArrow : Prims.bool  ->  FStar_Pprint.document = (fun b -> if b then begin
(str "~>")
end else begin
FStar_Pprint.rarrow
end)
and p_patternBranch : FStar_Parser_AST.branch  ->  FStar_Pprint.document = (fun _67_829 -> (match (_67_829) with
| (pat, when_opt, e) -> begin
(let _165_718 = (let _165_717 = (let _165_715 = (let _165_714 = (let _165_713 = (let _165_712 = (p_disjunctivePattern pat)
in (let _165_711 = (let _165_710 = (p_maybeWhen when_opt)
in (FStar_Pprint.op_Hat_Hat _165_710 FStar_Pprint.rarrow))
in (FStar_Pprint.op_Hat_Slash_Hat _165_712 _165_711)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_713))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar _165_714))
in (FStar_Pprint.group _165_715))
in (let _165_716 = (p_term e)
in (op_Hat_Slash_Plus_Hat _165_717 _165_716)))
in (FStar_Pprint.group _165_718))
end))
and p_maybeWhen : FStar_Parser_AST.term Prims.option  ->  FStar_Pprint.document = (fun _67_12 -> (match (_67_12) with
| None -> begin
FStar_Pprint.empty
end
| Some (e) -> begin
(let _165_722 = (str "when")
in (let _165_721 = (let _165_720 = (p_tmFormula e)
in (FStar_Pprint.op_Hat_Hat _165_720 FStar_Pprint.space))
in (op_Hat_Slash_Plus_Hat _165_722 _165_721)))
end))
and p_tmIff : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("<==>", (e1)::(e2)::[]) -> begin
(let _165_726 = (str "<==>")
in (let _165_725 = (p_tmImplies e1)
in (let _165_724 = (p_tmIff e2)
in (infix0 _165_726 _165_725 _165_724))))
end
| _67_842 -> begin
(p_tmImplies e)
end))
and p_tmImplies : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("==>", (e1)::(e2)::[]) -> begin
(let _165_730 = (str "==>")
in (let _165_729 = (p_tmArrow p_tmFormula e1)
in (let _165_728 = (p_tmImplies e2)
in (infix0 _165_730 _165_729 _165_728))))
end
| _67_851 -> begin
(p_tmArrow p_tmFormula e)
end))
and p_tmArrow : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_Tm e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Product (bs, tgt) -> begin
(let _165_742 = (let _165_741 = (FStar_Pprint.concat_map (fun b -> (let _165_739 = (p_binder false b)
in (let _165_738 = (let _165_737 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_737))
in (FStar_Pprint.op_Hat_Hat _165_739 _165_738)))) bs)
in (let _165_740 = (p_tmArrow p_Tm tgt)
in (FStar_Pprint.op_Hat_Hat _165_741 _165_740)))
in (FStar_Pprint.group _165_742))
end
| _67_860 -> begin
(p_Tm e)
end))
and p_tmFormula : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("\\/", (e1)::(e2)::[]) -> begin
(let _165_746 = (str "\\/")
in (let _165_745 = (p_tmFormula e1)
in (let _165_744 = (p_tmConjunction e2)
in (infix0 _165_746 _165_745 _165_744))))
end
| _67_869 -> begin
(p_tmConjunction e)
end))
and p_tmConjunction : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("/\\", (e1)::(e2)::[]) -> begin
(let _165_750 = (str "/\\")
in (let _165_749 = (p_tmConjunction e1)
in (let _165_748 = (p_tmTuple e2)
in (infix0 _165_750 _165_749 _165_748))))
end
| _67_878 -> begin
(p_tmTuple e)
end))
and p_tmTuple : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (lid, args) when (is_tuple_constructor lid) -> begin
(let _165_753 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map _165_753 (fun _67_887 -> (match (_67_887) with
| (e, _67_886) -> begin
(p_tmEq e)
end)) args))
end
| _67_889 -> begin
(p_tmEq e)
end))
and paren_if : Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun curr mine doc -> if (mine <= curr) then begin
doc
end else begin
(let _165_758 = (let _165_757 = (FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_757))
in (FStar_Pprint.group _165_758))
end)
and p_tmEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n = (max_level (FStar_List.append ((colon_equals)::(pipe_right)::[]) operatorInfix0ad12))
in (p_tmEq' n e)))
and p_tmEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (((is_operatorInfix0ad12 op) || (op = "=")) || (op = "|>")) -> begin
(

let _67_906 = (levels op)
in (match (_67_906) with
| (left, mine, right) -> begin
(let _165_765 = (let _165_764 = (str op)
in (let _165_763 = (p_tmEq' left e1)
in (let _165_762 = (p_tmEq' right e2)
in (infix0 _165_764 _165_763 _165_762))))
in (paren_if curr mine _165_765))
end))
end
| FStar_Parser_AST.Op (":=", (e1)::(e2)::[]) -> begin
(let _165_771 = (let _165_770 = (p_tmEq e1)
in (let _165_769 = (let _165_768 = (let _165_767 = (let _165_766 = (p_tmEq e2)
in (op_Hat_Slash_Plus_Hat FStar_Pprint.equals _165_766))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_767))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_768))
in (FStar_Pprint.op_Hat_Hat _165_770 _165_769)))
in (FStar_Pprint.group _165_771))
end
| _67_914 -> begin
(p_tmNoEq e)
end))
and p_tmNoEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n = (max_level ((colon_colon)::(amp)::(opinfix3)::(opinfix4)::[]))
in (p_tmNoEq' n e)))
and p_tmNoEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (lid, ((e1, _67_926))::((e2, _67_922))::[]) when ((FStar_Ident.lid_equals lid FStar_Syntax_Const.cons_lid) && (not ((is_list e)))) -> begin
(

let op = "::"
in (

let _67_935 = (levels op)
in (match (_67_935) with
| (left, mine, right) -> begin
(let _165_778 = (let _165_777 = (str op)
in (let _165_776 = (p_tmNoEq' left e1)
in (let _165_775 = (p_tmNoEq' right e2)
in (infix0 _165_777 _165_776 _165_775))))
in (paren_if curr mine _165_778))
end)))
end
| FStar_Parser_AST.Sum (binders, res) -> begin
(

let op = "&"
in (

let _67_944 = (levels op)
in (match (_67_944) with
| (left, mine, right) -> begin
(

let p_dsumfst = (fun b -> (let _165_784 = (p_binder false b)
in (let _165_783 = (let _165_782 = (let _165_781 = (str "&")
in (FStar_Pprint.op_Hat_Hat _165_781 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_782))
in (FStar_Pprint.op_Hat_Hat _165_784 _165_783))))
in (let _165_787 = (let _165_786 = (FStar_Pprint.concat_map p_dsumfst binders)
in (let _165_785 = (p_tmNoEq' right res)
in (FStar_Pprint.op_Hat_Hat _165_786 _165_785)))
in (paren_if curr mine _165_787)))
end)))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (is_operatorInfix34 op) -> begin
(

let _67_956 = (levels op)
in (match (_67_956) with
| (left, mine, right) -> begin
(let _165_791 = (let _165_790 = (str op)
in (let _165_789 = (p_tmNoEq' left e1)
in (let _165_788 = (p_tmNoEq' right e2)
in (infix0 _165_790 _165_789 _165_788))))
in (paren_if curr mine _165_791))
end))
end
| FStar_Parser_AST.Op ("-", (e)::[]) -> begin
(

let _67_965 = (levels "-")
in (match (_67_965) with
| (left, mine, right) -> begin
(let _165_792 = (p_tmNoEq' mine e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus _165_792))
end))
end
| FStar_Parser_AST.NamedTyp (lid, e) -> begin
(let _165_796 = (let _165_795 = (p_lidentOrUnderscore lid)
in (let _165_794 = (let _165_793 = (p_appTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon _165_793))
in (FStar_Pprint.op_Hat_Slash_Hat _165_795 _165_794)))
in (FStar_Pprint.group _165_796))
end
| FStar_Parser_AST.Refine (b, phi) -> begin
(p_refinedBinder b phi)
end
| FStar_Parser_AST.Record (with_opt, record_fields) -> begin
(let _165_800 = (let _165_799 = (default_or_map FStar_Pprint.empty p_with_clause with_opt)
in (let _165_798 = (let _165_797 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (FStar_Pprint.separate_map _165_797 p_simpleDef record_fields))
in (FStar_Pprint.op_Hat_Hat _165_799 _165_798)))
in (braces_with_nesting _165_800))
end
| FStar_Parser_AST.Op ("~", (e)::[]) -> begin
(let _165_803 = (let _165_802 = (str "~")
in (let _165_801 = (p_atomicTerm e)
in (FStar_Pprint.op_Hat_Hat _165_802 _165_801)))
in (FStar_Pprint.group _165_803))
end
| _67_984 -> begin
(p_appTerm e)
end))
and p_with_clause : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (let _165_808 = (p_appTerm e)
in (let _165_807 = (let _165_806 = (let _165_805 = (str "with")
in (FStar_Pprint.op_Hat_Hat _165_805 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_806))
in (FStar_Pprint.op_Hat_Hat _165_808 _165_807))))
and p_refinedBinder : FStar_Parser_AST.binder  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun b phi -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (lid, t) -> begin
(let _165_818 = (let _165_817 = (p_lident lid)
in (let _165_816 = (let _165_815 = (let _165_814 = (p_typ t)
in (let _165_813 = (let _165_812 = (let _165_811 = (p_term phi)
in (soft_braces_with_nesting _165_811))
in (FStar_Pprint.op_Hat_Hat _165_812 FStar_Pprint.rparen))
in (FStar_Pprint.op_Hat_Hat _165_814 _165_813)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_815))
in (FStar_Pprint.op_Hat_Hat _165_817 _165_816)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_818))
end
| FStar_Parser_AST.TAnnotated (_67_993) -> begin
(failwith "Is this still used ?")
end
| (FStar_Parser_AST.Variable (_)) | (FStar_Parser_AST.TVariable (_)) | (FStar_Parser_AST.NoName (_)) -> begin
(let _165_820 = (let _165_819 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" _165_819))
in (failwith _165_820))
end))
and p_simpleDef : (FStar_Ident.lid * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun _67_1006 -> (match (_67_1006) with
| (lid, e) -> begin
(let _165_825 = (let _165_824 = (p_qlident lid)
in (let _165_823 = (let _165_822 = (p_simpleTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals _165_822))
in (FStar_Pprint.op_Hat_Slash_Hat _165_824 _165_823)))
in (FStar_Pprint.group _165_825))
end))
and p_appTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App (_67_1009) when (is_general_application e) -> begin
(

let _67_1013 = (head_and_args e)
in (match (_67_1013) with
| (head, args) -> begin
(let _165_828 = (p_indexingTerm head)
in (let _165_827 = (FStar_Pprint.separate_map FStar_Pprint.space p_argTerm args)
in (op_Hat_Slash_Plus_Hat _165_828 _165_827)))
end))
end
| FStar_Parser_AST.Construct (lid, args) when ((is_general_construction e) && (not ((is_dtuple_constructor lid)))) -> begin
(match (args) with
| [] -> begin
(p_quident lid)
end
| (arg)::[] -> begin
(let _165_831 = (let _165_830 = (p_quident lid)
in (let _165_829 = (p_argTerm arg)
in (FStar_Pprint.op_Hat_Slash_Hat _165_830 _165_829)))
in (FStar_Pprint.group _165_831))
end
| (hd)::tl -> begin
(let _165_838 = (let _165_837 = (let _165_834 = (let _165_833 = (p_quident lid)
in (let _165_832 = (p_argTerm hd)
in (FStar_Pprint.op_Hat_Slash_Hat _165_833 _165_832)))
in (FStar_Pprint.group _165_834))
in (let _165_836 = (let _165_835 = (FStar_Pprint.separate_map break1 p_argTerm tl)
in (jump2 _165_835))
in (FStar_Pprint.op_Hat_Hat _165_837 _165_836)))
in (FStar_Pprint.group _165_838))
end)
end
| _67_1025 -> begin
(p_indexingTerm e)
end))
and p_argTerm : (FStar_Parser_AST.term * FStar_Parser_AST.imp)  ->  FStar_Pprint.document = (fun arg_imp -> (match (arg_imp) with
| ({FStar_Parser_AST.tm = FStar_Parser_AST.Uvar (_67_1032); FStar_Parser_AST.range = _67_1030; FStar_Parser_AST.level = _67_1028}, FStar_Parser_AST.UnivApp) -> begin
(p_univar (Prims.fst arg_imp))
end
| (u, FStar_Parser_AST.UnivApp) -> begin
(p_universe u)
end
| (e, FStar_Parser_AST.FsTypApp) -> begin
(let _165_840 = (p_indexingTerm e)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.langle _165_840 FStar_Pprint.rangle))
end
| (e, FStar_Parser_AST.Hash) -> begin
(let _165_842 = (str "#")
in (let _165_841 = (p_indexingTerm e)
in (FStar_Pprint.op_Hat_Hat _165_842 _165_841)))
end
| (e, FStar_Parser_AST.Nothing) -> begin
(p_indexingTerm e)
end))
and p_indexingTerm_aux : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun exit e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op (".()", (e1)::(e2)::[]) -> begin
(let _165_852 = (let _165_851 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (let _165_850 = (let _165_849 = (let _165_848 = (p_term e2)
in (soft_parens_with_nesting _165_848))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_849))
in (FStar_Pprint.op_Hat_Hat _165_851 _165_850)))
in (FStar_Pprint.group _165_852))
end
| FStar_Parser_AST.Op (".[]", (e1)::(e2)::[]) -> begin
(let _165_857 = (let _165_856 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (let _165_855 = (let _165_854 = (let _165_853 = (p_term e2)
in (soft_brackets_with_nesting _165_853))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_854))
in (FStar_Pprint.op_Hat_Hat _165_856 _165_855)))
in (FStar_Pprint.group _165_857))
end
| _67_1064 -> begin
(exit e)
end))
and p_indexingTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_indexingTerm_aux p_atomicTerm e))
and p_atomicTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.LetOpen (lid, e) -> begin
(let _165_863 = (p_quident lid)
in (let _165_862 = (let _165_861 = (let _165_860 = (p_term e)
in (soft_parens_with_nesting _165_860))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_861))
in (FStar_Pprint.op_Hat_Hat _165_863 _165_862)))
end
| FStar_Parser_AST.Name (lid) -> begin
(p_quident lid)
end
| FStar_Parser_AST.Op (op, (e)::[]) -> begin
(let _165_865 = (str op)
in (let _165_864 = (p_atomicTerm e)
in (FStar_Pprint.op_Hat_Hat _165_865 _165_864)))
end
| _67_1079 -> begin
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
(let _165_868 = (str op)
in (let _165_867 = (p_atomicTermNotQUident e)
in (FStar_Pprint.op_Hat_Hat _165_868 _165_867)))
end
| FStar_Parser_AST.Op (op, []) -> begin
(let _165_872 = (let _165_871 = (let _165_870 = (str op)
in (let _165_869 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat _165_870 _165_869)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_871))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_872))
end
| FStar_Parser_AST.Construct (lid, args) when (is_dtuple_constructor lid) -> begin
(let _165_877 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (let _165_876 = (let _165_874 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (let _165_873 = (FStar_List.map Prims.fst args)
in (FStar_Pprint.separate_map _165_874 p_tmEq _165_873)))
in (let _165_875 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_877 _165_876 _165_875))))
end
| FStar_Parser_AST.Project (e, lid) -> begin
(let _165_881 = (let _165_880 = (p_atomicTermNotQUident e)
in (let _165_879 = (let _165_878 = (p_qlident lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_878))
in (FStar_Pprint.op_Hat_Slash_Hat _165_880 _165_879)))
in (FStar_Pprint.group _165_881))
end
| _67_1110 -> begin
(p_projectionLHS e)
end))
and p_projectionLHS : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (lid) -> begin
(p_qlident lid)
end
| FStar_Parser_AST.Projector (constr_lid, field_lid) -> begin
(let _165_886 = (p_quident constr_lid)
in (let _165_885 = (let _165_884 = (let _165_883 = (p_lident field_lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_883))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark _165_884))
in (FStar_Pprint.op_Hat_Hat _165_886 _165_885)))
end
| FStar_Parser_AST.Discrim (constr_lid) -> begin
(let _165_887 = (p_quident constr_lid)
in (FStar_Pprint.op_Hat_Hat _165_887 FStar_Pprint.qmark))
end
| FStar_Parser_AST.Paren (e) -> begin
(let _165_888 = (p_term e)
in (soft_parens_with_nesting _165_888))
end
| _67_1123 when (is_array e) -> begin
(

let es = (extract_from_list e)
in (let _165_892 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar)
in (let _165_891 = (let _165_889 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (separate_map_or_flow _165_889 p_noSeqTerm es))
in (let _165_890 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") _165_892 _165_891 _165_890)))))
end
| _67_1126 when (is_list e) -> begin
(let _165_895 = (let _165_894 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (let _165_893 = (extract_from_list e)
in (separate_map_or_flow _165_894 p_noSeqTerm _165_893)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket _165_895 FStar_Pprint.rbracket))
end
| _67_1128 when (is_lex_list e) -> begin
(let _165_899 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket)
in (let _165_898 = (let _165_897 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (let _165_896 = (extract_from_list e)
in (separate_map_or_flow _165_897 p_noSeqTerm _165_896)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_899 _165_898 FStar_Pprint.rbracket)))
end
| _67_1130 when (is_ref_set e) -> begin
(

let es = (extract_from_ref_set e)
in (let _165_902 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace)
in (let _165_901 = (let _165_900 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (separate_map_or_flow _165_900 p_appTerm es))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") _165_902 _165_901 FStar_Pprint.rbrace))))
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Op (_)) | (FStar_Parser_AST.Tvar (_)) | (FStar_Parser_AST.Uvar (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) | (FStar_Parser_AST.Construct (_)) | (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.App (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.LetOpen (_)) | (FStar_Parser_AST.Seq (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Ascribed (_)) | (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Project (_)) | (FStar_Parser_AST.Product (_)) | (FStar_Parser_AST.Sum (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Refine (_)) | (FStar_Parser_AST.NamedTyp (_)) | (FStar_Parser_AST.Requires (_)) | (FStar_Parser_AST.Ensures (_)) | (FStar_Parser_AST.Assign (_)) | (FStar_Parser_AST.Attributes (_)) -> begin
(let _165_903 = (p_term e)
in (soft_parens_with_nesting _165_903))
end
| FStar_Parser_AST.Labeled (_67_1218) -> begin
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
(let _165_905 = (FStar_Pprint.doc_of_char x)
in (FStar_Pprint.squotes _165_905))
end
| FStar_Const.Const_string (bytes, _67_1231) -> begin
(let _165_906 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes _165_906))
end
| FStar_Const.Const_bytearray (bytes, _67_1236) -> begin
(let _165_909 = (let _165_907 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes _165_907))
in (let _165_908 = (str "B")
in (FStar_Pprint.op_Hat_Hat _165_909 _165_908)))
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

let ending = (default_or_map FStar_Pprint.empty (fun _67_1255 -> (match (_67_1255) with
| (s, w) -> begin
(let _165_916 = (signedness s)
in (let _165_915 = (width w)
in (FStar_Pprint.op_Hat_Hat _165_916 _165_915)))
end)) sign_width_opt)
in (let _165_917 = (str repr)
in (FStar_Pprint.op_Hat_Hat _165_917 ending)))))
end
| FStar_Const.Const_range (r) -> begin
(let _165_918 = (FStar_Range.string_of_range r)
in (str _165_918))
end
| FStar_Const.Const_reify -> begin
(str "reify")
end
| FStar_Const.Const_reflect (lid) -> begin
(let _165_922 = (p_quident lid)
in (let _165_921 = (let _165_920 = (let _165_919 = (str "reflect")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_919))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark _165_920))
in (FStar_Pprint.op_Hat_Hat _165_922 _165_921)))
end))
and p_universe : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (let _165_925 = (str "u#")
in (let _165_924 = (p_atomicUniverse u)
in (FStar_Pprint.op_Hat_Hat _165_925 _165_924))))
and p_universeFrom : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match (u.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("+", (u1)::(u2)::[]) -> begin
(let _165_930 = (let _165_929 = (p_universeFrom u1)
in (let _165_928 = (let _165_927 = (p_universeFrom u2)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus _165_927))
in (FStar_Pprint.op_Hat_Slash_Hat _165_929 _165_928)))
in (FStar_Pprint.group _165_930))
end
| FStar_Parser_AST.App (_67_1271) -> begin
(

let _67_1275 = (head_and_args u)
in (match (_67_1275) with
| (head, args) -> begin
(match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (maybe_max_lid) when (FStar_Ident.lid_equals maybe_max_lid FStar_Syntax_Const.max_lid) -> begin
(let _165_934 = (let _165_933 = (p_qlident FStar_Syntax_Const.max_lid)
in (let _165_932 = (FStar_Pprint.separate_map FStar_Pprint.space (fun _67_1281 -> (match (_67_1281) with
| (u, _67_1280) -> begin
(p_atomicUniverse u)
end)) args)
in (op_Hat_Slash_Plus_Hat _165_933 _165_932)))
in (FStar_Pprint.group _165_934))
end
| _67_1283 -> begin
(let _165_936 = (let _165_935 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" _165_935))
in (failwith _165_936))
end)
end))
end
| _67_1285 -> begin
(p_atomicUniverse u)
end))
and p_atomicUniverse : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match (u.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Wild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (r, sw)) -> begin
(p_constant (FStar_Const.Const_int (((r), (sw)))))
end
| FStar_Parser_AST.Uvar (_67_1294) -> begin
(p_univar u)
end
| FStar_Parser_AST.Paren (u) -> begin
(let _165_938 = (p_universeFrom u)
in (soft_parens_with_nesting _165_938))
end
| (FStar_Parser_AST.Op ("+", (_)::(_)::[])) | (FStar_Parser_AST.App (_)) -> begin
(let _165_939 = (p_universeFrom u)
in (soft_parens_with_nesting _165_939))
end
| _67_1310 -> begin
(let _165_941 = (let _165_940 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" _165_940))
in (failwith _165_941))
end))
and p_univar : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match (u.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Uvar (id) -> begin
(str (FStar_Ident.text_of_id id))
end
| _67_1315 -> begin
(let _165_944 = (let _165_943 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Not a universe variable %s" _165_943))
in (failwith _165_944))
end))


let term_to_document : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_term e))


let decl_to_document : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun e -> (p_decl e))


let modul_to_document : FStar_Parser_AST.modul  ->  FStar_Pprint.document = (fun m -> (match (m) with
| (FStar_Parser_AST.Module (_, decls)) | (FStar_Parser_AST.Interface (_, decls, _)) -> begin
(let _165_951 = (FStar_All.pipe_right decls (FStar_List.map decl_to_document))
in (FStar_All.pipe_right _165_951 (FStar_Pprint.separate FStar_Pprint.hardline)))
end))


let comments_to_document : (Prims.string * FStar_Range.range) Prims.list  ->  FStar_Pprint.document = (fun comments -> (FStar_Pprint.separate_map FStar_Pprint.hardline (fun _67_1333 -> (match (_67_1333) with
| (comment, range) -> begin
(str comment)
end)) comments))


let modul_with_comments_to_document : FStar_Parser_AST.modul  ->  (Prims.string * FStar_Range.range) Prims.list  ->  (FStar_Pprint.document * (Prims.string * FStar_Range.range) Prims.list) = (fun m comments -> (

let rec aux = (fun _67_1340 decl -> (match (_67_1340) with
| (previous_range_end, comments, doc) -> begin
(

let current_range = (FStar_Range.extend_to_end_of_line decl.FStar_Parser_AST.drange)
in (

let max = (fun x y -> if (x < y) then begin
y
end else begin
x
end)
in (

let rec process_preceding_comments = (fun doc last_line end_pos n _67_16 -> (match (_67_16) with
| ((comment, range))::comments when (let _165_977 = (FStar_Range.start_of_range range)
in (FStar_Range.pos_geq end_pos _165_977)) -> begin
(

let l = (let _165_979 = ((let _165_978 = (FStar_Range.start_of_range range)
in (FStar_Range.line_of_pos _165_978)) - last_line)
in (max (Prims.parse_int "1") _165_979))
in (

let doc = (let _165_982 = (let _165_981 = (FStar_Pprint.repeat l FStar_Pprint.hardline)
in (let _165_980 = (str comment)
in (FStar_Pprint.op_Hat_Hat _165_981 _165_980)))
in (FStar_Pprint.op_Hat_Hat doc _165_982))
in (let _165_984 = (let _165_983 = (FStar_Range.end_of_range range)
in (FStar_Range.line_of_pos _165_983))
in (process_preceding_comments doc _165_984 end_pos (Prims.parse_int "1") comments))))
end
| comments -> begin
(

let l = (let _165_985 = ((FStar_Range.line_of_pos end_pos) - last_line)
in (max n _165_985))
in (let _165_987 = (let _165_986 = (FStar_Pprint.repeat l FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat doc _165_986))
in ((_165_987), (comments))))
end))
in (

let _67_1363 = (let _165_990 = (FStar_Range.line_of_pos previous_range_end)
in (let _165_989 = (let _165_988 = (FStar_Range.start_of_range current_range)
in (FStar_Range.end_of_line _165_988))
in (process_preceding_comments doc _165_990 _165_989 (Prims.parse_int "0") comments)))
in (match (_67_1363) with
| (doc, comments) -> begin
(

let _67_1371 = (FStar_Util.take (fun _67_17 -> (match (_67_17) with
| (_67_1366, range) -> begin
(FStar_Range.range_contains_range current_range range)
end)) comments)
in (match (_67_1371) with
| (inner_comments, comments) -> begin
(

let _67_1372 = (FStar_ST.op_Colon_Equals comment_stack inner_comments)
in (

let doc = (let _165_992 = (decl_to_document decl)
in (FStar_Pprint.op_Hat_Hat doc _165_992))
in (

let inner_comments_doc = if ((FStar_ST.read comment_stack) = []) then begin
FStar_Pprint.empty
end else begin
(

let _67_1375 = (let _165_995 = (let _165_994 = (let _165_993 = (FStar_ST.read comment_stack)
in (FStar_List.map Prims.fst _165_993))
in (FStar_String.concat " ; " _165_994))
in (FStar_Util.print1_warning "Leftover comments : %s\n" _165_995))
in (let _165_996 = (FStar_ST.read comment_stack)
in (comments_to_document _165_996)))
end
in (let _165_998 = (FStar_Range.end_of_range decl.FStar_Parser_AST.drange)
in (let _165_997 = (FStar_Pprint.op_Hat_Hat doc inner_comments_doc)
in ((_165_998), (comments), (_165_997)))))))
end))
end)))))
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
| (d)::_67_1392 -> begin
(

let _67_1399 = (FStar_List.fold_left aux ((FStar_Range.zeroPos), (comments), (FStar_Pprint.empty)) decls)
in (match (_67_1399) with
| (_67_1396, comments, doc) -> begin
((doc), (comments))
end))
end))))




