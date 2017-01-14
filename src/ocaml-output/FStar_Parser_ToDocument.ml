
open Prims

let should_unparen : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref true)


let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> if (not ((FStar_ST.read should_unparen))) then begin
t
end else begin
(match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| _65_5 -> begin
t
end)
end)


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


let separate_break_map = (fun sep f l -> (let _166_35 = (let _166_34 = (let _166_33 = (FStar_Pprint.op_Hat_Hat sep break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _166_33))
in (FStar_Pprint.separate_map _166_34 f l))
in (FStar_Pprint.group _166_35)))


let precede_break_separate_map = (fun prec sep f l -> (let _166_52 = (let _166_45 = (FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space)
in (let _166_44 = (let _166_43 = (FStar_List.hd l)
in (FStar_All.pipe_right _166_43 f))
in (FStar_Pprint.precede _166_45 _166_44)))
in (let _166_51 = (let _166_50 = (FStar_List.tl l)
in (FStar_Pprint.concat_map (fun x -> (let _166_49 = (let _166_48 = (let _166_47 = (f x)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _166_47))
in (FStar_Pprint.op_Hat_Hat sep _166_48))
in (FStar_Pprint.op_Hat_Hat break1 _166_49))) _166_50))
in (FStar_Pprint.op_Hat_Hat _166_52 _166_51))))


let concat_break_map = (fun f l -> (let _166_60 = (FStar_Pprint.concat_map (fun x -> (let _166_59 = (f x)
in (FStar_Pprint.op_Hat_Hat _166_59 break1))) l)
in (FStar_Pprint.group _166_60)))


let parens_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lparen contents FStar_Pprint.rparen))


let soft_parens_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lparen contents FStar_Pprint.rparen))


let braces_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbrace contents FStar_Pprint.rbrace))


let soft_braces_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbrace contents FStar_Pprint.rbrace))


let brackets_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbracket contents FStar_Pprint.rbracket))


let soft_brackets_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbracket contents FStar_Pprint.rbracket))


let soft_begin_end_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (let _166_76 = (str "begin")
in (let _166_75 = (str "end")
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") _166_76 contents _166_75))))


let separate_map_or_flow = (fun sep f l -> if ((FStar_List.length l) < (Prims.parse_int "10")) then begin
(FStar_Pprint.separate_map sep f l)
end else begin
(FStar_Pprint.flow_map sep f l)
end)


let doc_of_fsdoc : (Prims.string * (Prims.string * Prims.string) Prims.list)  ->  FStar_Pprint.document = (fun _65_41 -> (match (_65_41) with
| (comment, keywords) -> begin
(let _166_96 = (let _166_95 = (let _166_94 = (str comment)
in (let _166_93 = (let _166_92 = (let _166_91 = (FStar_Pprint.separate_map FStar_Pprint.comma (fun _65_44 -> (match (_65_44) with
| (k, v) -> begin
(let _166_90 = (let _166_89 = (str k)
in (let _166_88 = (let _166_87 = (let _166_86 = (str v)
in (_166_86)::[])
in (FStar_Pprint.rarrow)::_166_87)
in (_166_89)::_166_88))
in (FStar_Pprint.concat _166_90))
end)) keywords)
in (_166_91)::[])
in (FStar_Pprint.space)::_166_92)
in (_166_94)::_166_93))
in (FStar_Pprint.concat _166_95))
in (FStar_Pprint.group _166_96))
end))


let is_unit : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match ((let _166_99 = (unparen e)
in _166_99.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Const (FStar_Const.Const_unit) -> begin
true
end
| _65_49 -> begin
false
end))


let matches_var : FStar_Parser_AST.term  ->  FStar_Ident.ident  ->  Prims.bool = (fun t x -> (match ((let _166_104 = (unparen t)
in _166_104.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Var (y) -> begin
(x.FStar_Ident.idText = (FStar_Ident.text_of_lid y))
end
| _65_55 -> begin
false
end))


let is_tuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Syntax_Util.is_tuple_data_lid'


let is_dtuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Syntax_Util.is_dtuple_data_lid'


let is_list_structure : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun cons_lid nil_lid -> (

let rec aux = (fun e -> (match ((let _166_117 = (unparen e)
in _166_117.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Construct (lid, []) -> begin
(FStar_Ident.lid_equals lid nil_lid)
end
| FStar_Parser_AST.Construct (lid, (_65_70)::((e2, _65_67))::[]) -> begin
((FStar_Ident.lid_equals lid cons_lid) && (aux e2))
end
| _65_75 -> begin
false
end))
in aux))


let is_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Syntax_Const.cons_lid FStar_Syntax_Const.nil_lid)


let is_lex_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Syntax_Const.lexcons_lid FStar_Syntax_Const.lextop_lid)


let rec extract_from_list : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (match ((let _166_122 = (unparen e)
in _166_122.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Construct (_65_78, []) -> begin
[]
end
| FStar_Parser_AST.Construct (_65_83, ((e1, FStar_Parser_AST.Nothing))::((e2, FStar_Parser_AST.Nothing))::[]) -> begin
(let _166_123 = (extract_from_list e2)
in (e1)::_166_123)
end
| _65_94 -> begin
(let _166_125 = (let _166_124 = (FStar_Parser_AST.term_to_string e)
in (FStar_Util.format1 "Not a list %s" _166_124))
in (failwith _166_125))
end))


let is_array : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match ((let _166_128 = (unparen e)
in _166_128.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (lid); FStar_Parser_AST.range = _65_99; FStar_Parser_AST.level = _65_97}, l, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals lid FStar_Syntax_Const.array_mk_array_lid) && (is_list l))
end
| _65_108 -> begin
false
end))


let rec is_ref_set : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match ((let _166_131 = (unparen e)
in _166_131.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Var (maybe_empty_lid) -> begin
(FStar_Ident.lid_equals maybe_empty_lid FStar_Syntax_Const.tset_empty)
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_singleton_lid); FStar_Parser_AST.range = _65_115; FStar_Parser_AST.level = _65_113}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_ref_lid); FStar_Parser_AST.range = _65_126; FStar_Parser_AST.level = _65_124}, e, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = _65_122; FStar_Parser_AST.level = _65_120}, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals maybe_singleton_lid FStar_Syntax_Const.tset_singleton) && (FStar_Ident.lid_equals maybe_ref_lid FStar_Syntax_Const.heap_ref))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_union_lid); FStar_Parser_AST.range = _65_145; FStar_Parser_AST.level = _65_143}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = _65_141; FStar_Parser_AST.level = _65_139}, e2, FStar_Parser_AST.Nothing) -> begin
(((FStar_Ident.lid_equals maybe_union_lid FStar_Syntax_Const.tset_union) && (is_ref_set e1)) && (is_ref_set e2))
end
| _65_159 -> begin
false
end))


let rec extract_from_ref_set : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (match ((let _166_134 = (unparen e)
in _166_134.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Var (_65_162) -> begin
[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (_65_169); FStar_Parser_AST.range = _65_167; FStar_Parser_AST.level = _65_165}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (_65_181); FStar_Parser_AST.range = _65_179; FStar_Parser_AST.level = _65_177}, e, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = _65_175; FStar_Parser_AST.level = _65_173}, FStar_Parser_AST.Nothing) -> begin
(e)::[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (_65_201); FStar_Parser_AST.range = _65_199; FStar_Parser_AST.level = _65_197}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = _65_195; FStar_Parser_AST.level = _65_193}, e2, FStar_Parser_AST.Nothing) -> begin
(let _166_136 = (extract_from_ref_set e1)
in (let _166_135 = (extract_from_ref_set e2)
in (FStar_List.append _166_136 _166_135)))
end
| _65_214 -> begin
(let _166_138 = (let _166_137 = (FStar_Parser_AST.term_to_string e)
in (FStar_Util.format1 "Not a ref set %s" _166_137))
in (failwith _166_138))
end))


let is_general_application : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (not (((is_array e) || (is_ref_set e)))))


let is_general_construction : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (not (((is_list e) || (is_lex_list e)))))


let is_general_prefix_op : Prims.string  ->  Prims.bool = (fun op -> (op <> "~"))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun e -> (

let rec aux = (fun e acc -> (match ((let _166_151 = (unparen e)
in _166_151.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (head, arg, imp) -> begin
(aux head ((((arg), (imp)))::acc))
end
| _65_228 -> begin
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


let token_to_string : (FStar_BaseTypes.char, Prims.string) FStar_Util.either  ->  Prims.string = (fun uu___365 -> (match (uu___365) with
| FStar_Util.Inl (c) -> begin
(Prims.strcat (FStar_Util.string_of_char c) ".*")
end
| FStar_Util.Inr (s) -> begin
s
end))


let matches_token : Prims.string  ->  (FStar_Char.char, Prims.string) FStar_Util.either  ->  Prims.bool = (fun s uu___366 -> (match (uu___366) with
| FStar_Util.Inl (c) -> begin
((FStar_String.get s (Prims.parse_int "0")) = c)
end
| FStar_Util.Inr (s') -> begin
(s = s')
end))


let matches_level = (fun s _65_243 -> (match (_65_243) with
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


let level_associativity_spec : (associativity * (FStar_Char.char, Prims.string) FStar_Util.either Prims.list) Prims.list = (opinfix4)::(opinfix3)::(opinfix2)::(opinfix1)::(pipe_right)::(opinfix0d)::(opinfix0c)::(opinfix0b)::(opinfix0a)::(colon_equals)::(amp)::(colon_colon)::[]


let level_table : ((Prims.int * Prims.int * Prims.int) * (FStar_Char.char, Prims.string) FStar_Util.either Prims.list) Prims.list = (

let levels_from_associativity = (fun l uu___367 -> (match (uu___367) with
| Left -> begin
((l), (l), ((l - (Prims.parse_int "1"))))
end
| Right -> begin
(((l - (Prims.parse_int "1"))), (l), (l))
end
| NonAssoc -> begin
((l), (l), (l))
end))
in (FStar_List.mapi (fun i _65_253 -> (match (_65_253) with
| (assoc, tokens) -> begin
(((levels_from_associativity i assoc)), (tokens))
end)) level_associativity_spec))


let assign_levels : associativity_level Prims.list  ->  Prims.string  ->  (Prims.int * Prims.int * Prims.int) = (fun token_associativity_spec s -> (match ((FStar_List.tryFind (matches_level s) level_table)) with
| Some (assoc_levels, _65_258) -> begin
assoc_levels
end
| _65_262 -> begin
(failwith (Prims.strcat "Unrecognized operator " s))
end))


let max : Prims.int  ->  Prims.int  ->  Prims.int = (fun k1 k2 -> if (k1 > k2) then begin
k1
end else begin
k2
end)


let max_level = (fun l -> (

let find_level_and_max = (fun n level -> (match ((FStar_List.tryFind (fun _65_272 -> (match (_65_272) with
| (_65_270, tokens) -> begin
(tokens = (Prims.snd level))
end)) level_table)) with
| Some ((_65_274, l, _65_277), _65_280) -> begin
(max n l)
end
| None -> begin
(let _166_185 = (let _166_184 = (let _166_183 = (FStar_List.map token_to_string (Prims.snd level))
in (FStar_String.concat "," _166_183))
in (FStar_Util.format1 "Undefined associativity level %s" _166_184))
in (failwith _166_185))
end))
in (FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l)))


let levels : Prims.string  ->  (Prims.int * Prims.int * Prims.int) = (assign_levels level_associativity_spec)


let operatorInfix0ad12 = (opinfix0a)::(opinfix0b)::(opinfix0c)::(opinfix0d)::(opinfix1)::(opinfix2)::[]


let is_operatorInfix0ad12 : Prims.string  ->  Prims.bool = (fun op -> ((FStar_List.tryFind (matches_level op) operatorInfix0ad12) <> None))


let is_operatorInfix34 : Prims.string  ->  Prims.bool = (

let opinfix34 = (opinfix3)::(opinfix4)::[]
in (fun op -> ((FStar_List.tryFind (matches_level op) opinfix34) <> None)))


let comment_stack : (Prims.string * FStar_Range.range) Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let with_comment = (fun printer tm tmrange -> (

let rec comments_before_pos = (fun acc print_pos lookahead_pos -> (match ((FStar_ST.read comment_stack)) with
| [] -> begin
((acc), (false))
end
| ((comment, crange))::cs -> begin
if (FStar_Range.range_before_pos crange print_pos) then begin
(

let _65_300 = (FStar_ST.op_Colon_Equals comment_stack cs)
in (let _166_205 = (let _166_204 = (let _166_203 = (str comment)
in (FStar_Pprint.op_Hat_Hat _166_203 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat acc _166_204))
in (comments_before_pos _166_205 print_pos lookahead_pos)))
end else begin
(let _166_206 = (FStar_Range.range_before_pos crange lookahead_pos)
in ((acc), (_166_206)))
end
end))
in (

let _65_304 = (let _166_209 = (let _166_207 = (FStar_Range.start_of_range tmrange)
in (FStar_Range.end_of_line _166_207))
in (let _166_208 = (FStar_Range.end_of_range tmrange)
in (comments_before_pos FStar_Pprint.empty _166_209 _166_208)))
in (match (_65_304) with
| (comments, has_lookahead) -> begin
(

let printed_e = (printer tm)
in (

let comments = if has_lookahead then begin
(

let pos = (FStar_Range.end_of_range tmrange)
in (let _166_210 = (comments_before_pos comments pos pos)
in (Prims.fst _166_210)))
end else begin
comments
end
in (let _166_211 = (FStar_Pprint.op_Hat_Hat comments printed_e)
in (FStar_Pprint.group _166_211))))
end))))


let rec p_decl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (let _166_322 = (let _166_321 = (FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc)
in (let _166_320 = (let _166_319 = (p_attributes d.FStar_Parser_AST.attrs)
in (let _166_318 = (let _166_317 = (p_qualifiers d.FStar_Parser_AST.quals)
in (let _166_316 = (let _166_315 = (p_rawDecl d)
in (FStar_Pprint.op_Hat_Hat (if (d.FStar_Parser_AST.quals = []) then begin
FStar_Pprint.empty
end else begin
break1
end) _166_315))
in (FStar_Pprint.op_Hat_Hat _166_317 _166_316)))
in (FStar_Pprint.op_Hat_Hat _166_319 _166_318)))
in (FStar_Pprint.op_Hat_Hat _166_321 _166_320)))
in (FStar_Pprint.group _166_322)))
and p_attributes : FStar_Parser_AST.attributes_  ->  FStar_Pprint.document = (fun attrs -> (let _166_326 = (let _166_324 = (str "@")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket _166_324))
in (let _166_325 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline)
in (FStar_Pprint.surround_separate_map (Prims.parse_int "0") (Prims.parse_int "2") FStar_Pprint.empty _166_326 FStar_Pprint.space _166_325 p_atomicTerm attrs))))
and p_fsdoc : FStar_Parser_AST.fsdoc  ->  FStar_Pprint.document = (fun _65_312 -> (match (_65_312) with
| (doc, kwd_args) -> begin
(

let kwd_args_doc = (match (kwd_args) with
| [] -> begin
FStar_Pprint.empty
end
| kwd_args -> begin
(

let process_kwd_arg = (fun _65_318 -> (match (_65_318) with
| (kwd, arg) -> begin
(let _166_334 = (str "@")
in (let _166_333 = (let _166_332 = (str kwd)
in (let _166_331 = (let _166_330 = (str arg)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _166_330))
in (FStar_Pprint.op_Hat_Hat _166_332 _166_331)))
in (FStar_Pprint.op_Hat_Hat _166_334 _166_333)))
end))
in (let _166_336 = (let _166_335 = (FStar_Pprint.separate_map FStar_Pprint.hardline process_kwd_arg kwd_args)
in (FStar_Pprint.op_Hat_Hat _166_335 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline _166_336)))
end)
in (let _166_344 = (let _166_343 = (let _166_342 = (let _166_341 = (let _166_340 = (str doc)
in (let _166_339 = (let _166_338 = (let _166_337 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _166_337))
in (FStar_Pprint.op_Hat_Hat kwd_args_doc _166_338))
in (FStar_Pprint.op_Hat_Hat _166_340 _166_339)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _166_341))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _166_342))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _166_343))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline _166_344)))
end))
and p_rawDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Open (uid) -> begin
(let _166_348 = (let _166_347 = (str "open")
in (let _166_346 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat _166_347 _166_346)))
in (FStar_Pprint.group _166_348))
end
| FStar_Parser_AST.Include (uid) -> begin
(let _166_351 = (let _166_350 = (str "include")
in (let _166_349 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat _166_350 _166_349)))
in (FStar_Pprint.group _166_351))
end
| FStar_Parser_AST.ModuleAbbrev (uid1, uid2) -> begin
(let _166_358 = (let _166_356 = (str "module")
in (let _166_355 = (let _166_354 = (let _166_353 = (p_uident uid1)
in (let _166_352 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _166_353 _166_352)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _166_354))
in (FStar_Pprint.op_Hat_Hat _166_356 _166_355)))
in (let _166_357 = (p_quident uid2)
in (op_Hat_Slash_Plus_Hat _166_358 _166_357)))
end
| FStar_Parser_AST.TopLevelModule (uid) -> begin
(let _166_362 = (let _166_361 = (str "module")
in (let _166_360 = (let _166_359 = (p_quident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _166_359))
in (FStar_Pprint.op_Hat_Hat _166_361 _166_360)))
in (FStar_Pprint.group _166_362))
end
| FStar_Parser_AST.KindAbbrev (_65_332) -> begin
(failwith "Deprecated, please stop throwing your old stuff at me !")
end
| FStar_Parser_AST.Tycon (true, ((FStar_Parser_AST.TyconAbbrev (uid, tpars, None, t), None))::[]) -> begin
(

let effect_prefix_doc = (let _166_365 = (str "effect")
in (let _166_364 = (let _166_363 = (p_uident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _166_363))
in (FStar_Pprint.op_Hat_Hat _166_365 _166_364)))
in (let _166_368 = (let _166_366 = (p_typars tpars)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") effect_prefix_doc _166_366 FStar_Pprint.equals))
in (let _166_367 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _166_368 _166_367))))
end
| FStar_Parser_AST.Tycon (false, tcdefs) -> begin
(let _166_370 = (str "type")
in (let _166_369 = (str "and")
in (precede_break_separate_map _166_370 _166_369 p_fsdocTypeDeclPairs tcdefs)))
end
| FStar_Parser_AST.TopLevelLet (q, lbs) -> begin
(

let let_doc = (let _166_372 = (str "let")
in (let _166_371 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat _166_372 _166_371)))
in (let _166_373 = (str "and")
in (precede_break_separate_map let_doc _166_373 p_letbinding lbs)))
end
| FStar_Parser_AST.Val (lid, t) -> begin
(let _166_380 = (let _166_378 = (str "val")
in (let _166_377 = (let _166_376 = (let _166_375 = (p_lident lid)
in (let _166_374 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat _166_375 _166_374)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _166_376))
in (FStar_Pprint.op_Hat_Hat _166_378 _166_377)))
in (let _166_379 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _166_380 _166_379)))
end
| FStar_Parser_AST.Assume (id, t) -> begin
(

let decl_keyword = if (let _166_381 = (FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_All.pipe_right _166_381 FStar_Util.is_upper)) then begin
FStar_Pprint.empty
end else begin
(let _166_382 = (str "val")
in (FStar_Pprint.op_Hat_Hat _166_382 FStar_Pprint.space))
end
in (let _166_387 = (let _166_385 = (let _166_384 = (p_ident id)
in (let _166_383 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat _166_384 _166_383)))
in (FStar_Pprint.op_Hat_Hat decl_keyword _166_385))
in (let _166_386 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _166_387 _166_386))))
end
| FStar_Parser_AST.Exception (uid, t_opt) -> begin
(let _166_395 = (str "exception")
in (let _166_394 = (let _166_393 = (let _166_392 = (p_uident uid)
in (let _166_391 = (FStar_Pprint.optional (fun t -> (let _166_390 = (str "of")
in (let _166_389 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _166_390 _166_389)))) t_opt)
in (FStar_Pprint.op_Hat_Hat _166_392 _166_391)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _166_393))
in (FStar_Pprint.op_Hat_Hat _166_395 _166_394)))
end
| FStar_Parser_AST.NewEffect (ne) -> begin
(let _166_398 = (str "new_effect")
in (let _166_397 = (let _166_396 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _166_396))
in (FStar_Pprint.op_Hat_Hat _166_398 _166_397)))
end
| FStar_Parser_AST.SubEffect (se) -> begin
(let _166_401 = (str "sub_effect")
in (let _166_400 = (let _166_399 = (p_subEffect se)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _166_399))
in (FStar_Pprint.op_Hat_Hat _166_401 _166_400)))
end
| FStar_Parser_AST.NewEffectForFree (ne) -> begin
(let _166_404 = (str "new_effect_for_free")
in (let _166_403 = (let _166_402 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _166_402))
in (FStar_Pprint.op_Hat_Hat _166_404 _166_403)))
end
| FStar_Parser_AST.Pragma (p) -> begin
(p_pragma p)
end
| FStar_Parser_AST.Fsdoc (doc) -> begin
(let _166_405 = (p_fsdoc doc)
in (FStar_Pprint.op_Hat_Hat _166_405 FStar_Pprint.hardline))
end
| FStar_Parser_AST.Main (_65_381) -> begin
(failwith "*Main declaration* : Is that really still in use ??")
end
| FStar_Parser_AST.Tycon (true, _65_385) -> begin
(failwith "Effect abbreviation is expected to be defined by an abbreviation")
end))
and p_pragma : FStar_Parser_AST.pragma  ->  FStar_Pprint.document = (fun uu___368 -> (match (uu___368) with
| FStar_Parser_AST.SetOptions (s) -> begin
(let _166_410 = (str "#set-options")
in (let _166_409 = (let _166_408 = (let _166_407 = (str s)
in (FStar_Pprint.dquotes _166_407))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _166_408))
in (FStar_Pprint.op_Hat_Hat _166_410 _166_409)))
end
| FStar_Parser_AST.ResetOptions (s_opt) -> begin
(let _166_415 = (str "#reset-options")
in (let _166_414 = (FStar_Pprint.optional (fun s -> (let _166_413 = (let _166_412 = (str s)
in (FStar_Pprint.dquotes _166_412))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _166_413))) s_opt)
in (FStar_Pprint.op_Hat_Hat _166_415 _166_414)))
end))
and p_typars : FStar_Parser_AST.binder Prims.list  ->  FStar_Pprint.document = (fun bs -> (p_binders true bs))
and p_fsdocTypeDeclPairs : (FStar_Parser_AST.tycon * FStar_Parser_AST.fsdoc Prims.option)  ->  FStar_Pprint.document = (fun _65_397 -> (match (_65_397) with
| (typedecl, fsdoc_opt) -> begin
(let _166_419 = (FStar_Pprint.optional p_fsdoc fsdoc_opt)
in (let _166_418 = (p_typeDecl typedecl)
in (FStar_Pprint.op_Hat_Hat _166_419 _166_418)))
end))
and p_typeDecl : FStar_Parser_AST.tycon  ->  FStar_Pprint.document = (fun uu___369 -> (match (uu___369) with
| FStar_Parser_AST.TyconAbstract (lid, bs, typ_opt) -> begin
(

let empty' = (fun _65_404 -> (match (()) with
| () -> begin
FStar_Pprint.empty
end))
in (p_typeDeclPrefix lid bs typ_opt empty'))
end
| FStar_Parser_AST.TyconAbbrev (lid, bs, typ_opt, t) -> begin
(

let f = (fun _65_413 -> (match (()) with
| () -> begin
(let _166_425 = (p_typ t)
in (prefix2 FStar_Pprint.equals _166_425))
end))
in (p_typeDeclPrefix lid bs typ_opt f))
end
| FStar_Parser_AST.TyconRecord (lid, bs, typ_opt, record_field_decls) -> begin
(

let p_recordFieldAndComments = (fun _65_424 -> (match (_65_424) with
| (lid, t, doc_opt) -> begin
(let _166_428 = (FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range)
in (with_comment p_recordFieldDecl ((lid), (t), (doc_opt)) _166_428))
end))
in (

let p_fields = (fun _65_426 -> (match (()) with
| () -> begin
(let _166_434 = (let _166_433 = (let _166_432 = (let _166_431 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (FStar_Pprint.separate_map _166_431 p_recordFieldAndComments record_field_decls))
in (braces_with_nesting _166_432))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _166_433))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.equals _166_434))
end))
in (p_typeDeclPrefix lid bs typ_opt p_fields)))
end
| FStar_Parser_AST.TyconVariant (lid, bs, typ_opt, ct_decls) -> begin
(

let p_constructorBranchAndComments = (fun _65_438 -> (match (_65_438) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let range = (let _166_439 = (let _166_438 = (FStar_Util.map_opt t_opt (fun t -> t.FStar_Parser_AST.range))
in (FStar_Util.dflt uid.FStar_Ident.idRange _166_438))
in (FStar_Range.extend_to_end_of_line _166_439))
in (

let p_constructorBranch = (fun decl -> (let _166_444 = (let _166_443 = (let _166_442 = (p_constructorDecl decl)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _166_442))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar _166_443))
in (FStar_Pprint.group _166_444)))
in (with_comment p_constructorBranch ((uid), (t_opt), (doc_opt), (use_of)) range)))
end))
in (

let datacon_doc = (fun _65_444 -> (match (()) with
| () -> begin
(let _166_447 = (FStar_Pprint.separate_map break1 p_constructorBranchAndComments ct_decls)
in (FStar_Pprint.group _166_447))
end))
in (p_typeDeclPrefix lid bs typ_opt (fun _65_445 -> (match (()) with
| () -> begin
(let _166_449 = (datacon_doc ())
in (prefix2 FStar_Pprint.equals _166_449))
end)))))
end))
and p_typeDeclPrefix : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.knd Prims.option  ->  (Prims.unit  ->  FStar_Pprint.document)  ->  FStar_Pprint.document = (fun lid bs typ_opt cont -> if ((bs = []) && (typ_opt = None)) then begin
(let _166_459 = (p_ident lid)
in (let _166_458 = (let _166_457 = (cont ())
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _166_457))
in (FStar_Pprint.op_Hat_Hat _166_459 _166_458)))
end else begin
(

let binders_doc = (let _166_465 = (p_typars bs)
in (let _166_464 = (FStar_Pprint.optional (fun t -> (let _166_463 = (let _166_462 = (let _166_461 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _166_461))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _166_462))
in (FStar_Pprint.op_Hat_Hat break1 _166_463))) typ_opt)
in (FStar_Pprint.op_Hat_Hat _166_465 _166_464)))
in (let _166_467 = (p_ident lid)
in (let _166_466 = (cont ())
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _166_467 binders_doc _166_466))))
end)
and p_recordFieldDecl : (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc Prims.option)  ->  FStar_Pprint.document = (fun _65_455 -> (match (_65_455) with
| (lid, t, doc_opt) -> begin
(let _166_474 = (let _166_473 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (let _166_472 = (let _166_471 = (p_lident lid)
in (let _166_470 = (let _166_469 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _166_469))
in (FStar_Pprint.op_Hat_Hat _166_471 _166_470)))
in (FStar_Pprint.op_Hat_Hat _166_473 _166_472)))
in (FStar_Pprint.group _166_474))
end))
and p_constructorDecl : (FStar_Ident.ident * FStar_Parser_AST.term Prims.option * FStar_Parser_AST.fsdoc Prims.option * Prims.bool)  ->  FStar_Pprint.document = (fun _65_460 -> (match (_65_460) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let sep = if use_of then begin
(str "of")
end else begin
FStar_Pprint.colon
end
in (

let uid_doc = (p_uident uid)
in (let _166_481 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (let _166_480 = (default_or_map uid_doc (fun t -> (let _166_479 = (let _166_477 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep)
in (FStar_Pprint.op_Hat_Hat uid_doc _166_477))
in (let _166_478 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _166_479 _166_478)))) t_opt)
in (FStar_Pprint.op_Hat_Hat _166_481 _166_480)))))
end))
and p_letbinding : (FStar_Parser_AST.pattern * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun _65_466 -> (match (_65_466) with
| (pat, e) -> begin
(

let pat_doc = (

let _65_475 = (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, t) -> begin
(let _166_487 = (let _166_486 = (let _166_485 = (let _166_484 = (let _166_483 = (p_tmArrow p_tmNoEq t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _166_483))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _166_484))
in (FStar_Pprint.group _166_485))
in (FStar_Pprint.op_Hat_Hat break1 _166_486))
in ((pat), (_166_487)))
end
| _65_472 -> begin
((pat), (FStar_Pprint.empty))
end)
in (match (_65_475) with
| (pat, ascr_doc) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _65_480); FStar_Parser_AST.prange = _65_477}, pats) -> begin
(let _166_490 = (p_lident x)
in (let _166_489 = (let _166_488 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Hat _166_488 ascr_doc))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _166_490 _166_489 FStar_Pprint.equals)))
end
| _65_488 -> begin
(let _166_493 = (let _166_492 = (p_tuplePattern pat)
in (let _166_491 = (FStar_Pprint.op_Hat_Slash_Hat ascr_doc FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _166_492 _166_491)))
in (FStar_Pprint.group _166_493))
end)
end))
in (let _166_494 = (p_term e)
in (prefix2 pat_doc _166_494)))
end))
and p_newEffect : FStar_Parser_AST.effect_decl  ->  FStar_Pprint.document = (fun uu___370 -> (match (uu___370) with
| FStar_Parser_AST.RedefineEffect (lid, bs, t) -> begin
(p_effectRedefinition lid bs t)
end
| FStar_Parser_AST.DefineEffect (lid, bs, t, eff_decls, action_decls) -> begin
(p_effectDefinition lid bs t eff_decls action_decls)
end))
and p_effectRedefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun uid bs t -> (let _166_502 = (p_uident uid)
in (let _166_501 = (p_binders true bs)
in (let _166_500 = (let _166_499 = (p_simpleTerm t)
in (prefix2 FStar_Pprint.equals _166_499))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _166_502 _166_501 _166_500)))))
and p_effectDefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun uid bs t eff_decls action_decls -> (let _166_519 = (let _166_518 = (let _166_512 = (let _166_511 = (p_uident uid)
in (let _166_510 = (p_binders true bs)
in (let _166_509 = (let _166_508 = (p_typ t)
in (prefix2 FStar_Pprint.colon _166_508))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _166_511 _166_510 _166_509))))
in (FStar_Pprint.group _166_512))
in (let _166_517 = (let _166_516 = (let _166_514 = (str "with")
in (let _166_513 = (separate_break_map FStar_Pprint.semi p_effectDecl eff_decls)
in (prefix2 _166_514 _166_513)))
in (let _166_515 = (p_actionDecls action_decls)
in (FStar_Pprint.op_Hat_Hat _166_516 _166_515)))
in (FStar_Pprint.op_Hat_Slash_Hat _166_518 _166_517)))
in (braces_with_nesting _166_519)))
and p_actionDecls : FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun uu___371 -> (match (uu___371) with
| [] -> begin
FStar_Pprint.empty
end
| l -> begin
(let _166_523 = (let _166_522 = (str "and actions")
in (let _166_521 = (separate_break_map FStar_Pprint.semi p_effectDecl l)
in (prefix2 _166_522 _166_521)))
in (FStar_Pprint.op_Hat_Hat break1 _166_523))
end))
and p_effectDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (false, ((FStar_Parser_AST.TyconAbbrev (lid, [], None, e), None))::[]) -> begin
(let _166_528 = (let _166_526 = (p_lident lid)
in (let _166_525 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _166_526 _166_525)))
in (let _166_527 = (p_simpleTerm e)
in (prefix2 _166_528 _166_527)))
end
| _65_528 -> begin
(let _166_530 = (let _166_529 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "Not a declaration of an effect member... or at least I hope so : %s" _166_529))
in (failwith _166_530))
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

let p_lift = (fun _65_542 -> (match (_65_542) with
| (kwd, t) -> begin
(let _166_537 = (let _166_535 = (str kwd)
in (let _166_534 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _166_535 _166_534)))
in (let _166_536 = (p_simpleTerm t)
in (prefix2 _166_537 _166_536)))
end))
in (separate_break_map FStar_Pprint.semi p_lift lifts)))
in (let _166_545 = (let _166_542 = (let _166_540 = (p_quident lift.FStar_Parser_AST.msource)
in (let _166_539 = (let _166_538 = (str "~>")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _166_538))
in (FStar_Pprint.op_Hat_Hat _166_540 _166_539)))
in (let _166_541 = (p_quident lift.FStar_Parser_AST.mdest)
in (prefix2 _166_542 _166_541)))
in (let _166_544 = (let _166_543 = (braces_with_nesting lift_op_doc)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _166_543))
in (FStar_Pprint.op_Hat_Hat _166_545 _166_544)))))
and p_qualifier : FStar_Parser_AST.qualifier  ->  FStar_Pprint.document = (fun uu___372 -> (match (uu___372) with
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
| FStar_Parser_AST.Effect_qual -> begin
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
and p_qualifiers : FStar_Parser_AST.qualifiers  ->  FStar_Pprint.document = (fun qs -> (let _166_548 = (FStar_Pprint.separate_map break1 p_qualifier qs)
in (FStar_Pprint.group _166_548)))
and p_letqualifier : FStar_Parser_AST.let_qualifier  ->  FStar_Pprint.document = (fun uu___373 -> (match (uu___373) with
| FStar_Parser_AST.Rec -> begin
(let _166_550 = (str "rec")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _166_550))
end
| FStar_Parser_AST.Mutable -> begin
(let _166_551 = (str "mutable")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _166_551))
end
| FStar_Parser_AST.NoLetQualifier -> begin
FStar_Pprint.empty
end))
and p_aqual : FStar_Parser_AST.arg_qualifier  ->  FStar_Pprint.document = (fun uu___374 -> (match (uu___374) with
| FStar_Parser_AST.Implicit -> begin
(str "#")
end
| FStar_Parser_AST.Equality -> begin
(str "$")
end))
and p_disjunctivePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr (pats) -> begin
(let _166_556 = (let _166_555 = (let _166_554 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space)
in (FStar_Pprint.op_Hat_Hat break1 _166_554))
in (FStar_Pprint.separate_map _166_555 p_tuplePattern pats))
in (FStar_Pprint.group _166_556))
end
| _65_576 -> begin
(p_tuplePattern p)
end))
and p_tuplePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTuple (pats, false) -> begin
(let _166_559 = (let _166_558 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map _166_558 p_constructorPattern pats))
in (FStar_Pprint.group _166_559))
end
| _65_583 -> begin
(p_constructorPattern p)
end))
and p_constructorPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (maybe_cons_lid); FStar_Parser_AST.prange = _65_586}, (hd)::(tl)::[]) when (FStar_Ident.lid_equals maybe_cons_lid FStar_Syntax_Const.cons_lid) -> begin
(let _166_563 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon)
in (let _166_562 = (p_constructorPattern hd)
in (let _166_561 = (p_constructorPattern tl)
in (infix0 _166_563 _166_562 _166_561))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (uid); FStar_Parser_AST.prange = _65_596}, pats) -> begin
(let _166_565 = (p_quident uid)
in (let _166_564 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (prefix2 _166_565 _166_564)))
end
| _65_604 -> begin
(p_atomicPattern p)
end))
and p_atomicPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, t) -> begin
(match ((let _166_568 = (let _166_567 = (unparen t)
in _166_567.FStar_Parser_AST.tm)
in ((pat.FStar_Parser_AST.pat), (_166_568)))) with
| (FStar_Parser_AST.PatVar (lid, aqual), FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t); FStar_Parser_AST.brange = _65_619; FStar_Parser_AST.blevel = _65_617; FStar_Parser_AST.aqual = _65_615}, phi)) when (lid.FStar_Ident.idText = lid'.FStar_Ident.idText) -> begin
(let _166_570 = (let _166_569 = (p_ident lid)
in (p_refinement aqual _166_569 t phi))
in (soft_parens_with_nesting _166_570))
end
| (FStar_Parser_AST.PatWild, FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t); FStar_Parser_AST.brange = _65_635; FStar_Parser_AST.blevel = _65_633; FStar_Parser_AST.aqual = _65_631}, phi)) -> begin
(let _166_571 = (p_refinement None FStar_Pprint.underscore t phi)
in (soft_parens_with_nesting _166_571))
end
| _65_644 -> begin
(let _166_577 = (let _166_576 = (p_tuplePattern pat)
in (let _166_575 = (let _166_574 = (FStar_Pprint.break_ (Prims.parse_int "0"))
in (let _166_573 = (let _166_572 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _166_572))
in (FStar_Pprint.op_Hat_Hat _166_574 _166_573)))
in (FStar_Pprint.op_Hat_Hat _166_576 _166_575)))
in (soft_parens_with_nesting _166_577))
end)
end
| FStar_Parser_AST.PatList (pats) -> begin
(let _166_578 = (separate_break_map FStar_Pprint.semi p_tuplePattern pats)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket _166_578 FStar_Pprint.rbracket))
end
| FStar_Parser_AST.PatRecord (pats) -> begin
(

let p_recordFieldPat = (fun _65_652 -> (match (_65_652) with
| (lid, pat) -> begin
(let _166_582 = (p_qlident lid)
in (let _166_581 = (p_tuplePattern pat)
in (infix2 FStar_Pprint.equals _166_582 _166_581)))
end))
in (let _166_583 = (separate_break_map FStar_Pprint.semi p_recordFieldPat pats)
in (soft_braces_with_nesting _166_583)))
end
| FStar_Parser_AST.PatTuple (pats, true) -> begin
(let _166_586 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (let _166_585 = (separate_break_map FStar_Pprint.comma p_constructorPattern pats)
in (let _166_584 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _166_586 _166_585 _166_584))))
end
| FStar_Parser_AST.PatTvar (tv, arg_qualifier_opt) -> begin
(

let _65_661 = ()
in (p_tvar tv))
end
| FStar_Parser_AST.PatOp (op) -> begin
(let _166_590 = (let _166_589 = (let _166_588 = (str op)
in (let _166_587 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat _166_588 _166_587)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _166_589))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _166_590))
end
| FStar_Parser_AST.PatWild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.PatConst (c) -> begin
(p_constant c)
end
| FStar_Parser_AST.PatVar (lid, aqual) -> begin
(let _166_592 = (FStar_Pprint.optional p_aqual aqual)
in (let _166_591 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat _166_592 _166_591)))
end
| FStar_Parser_AST.PatName (uid) -> begin
(p_quident uid)
end
| FStar_Parser_AST.PatOr (_65_675) -> begin
(failwith "Inner or pattern !")
end
| (FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (_); FStar_Parser_AST.prange = _}, _)) | (FStar_Parser_AST.PatTuple (_, false)) -> begin
(let _166_593 = (p_tuplePattern p)
in (soft_parens_with_nesting _166_593))
end
| _65_693 -> begin
(let _166_595 = (let _166_594 = (FStar_Parser_AST.pat_to_string p)
in (FStar_Util.format1 "Invalid pattern %s" _166_594))
in (failwith _166_595))
end))
and p_binder : Prims.bool  ->  FStar_Parser_AST.binder  ->  FStar_Pprint.document = (fun is_atomic b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (lid) -> begin
(let _166_599 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (let _166_598 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat _166_599 _166_598)))
end
| FStar_Parser_AST.TVariable (lid) -> begin
(p_lident lid)
end
| FStar_Parser_AST.Annotated (lid, t) -> begin
(

let doc = (match ((let _166_600 = (unparen t)
in _166_600.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t); FStar_Parser_AST.brange = _65_709; FStar_Parser_AST.blevel = _65_707; FStar_Parser_AST.aqual = _65_705}, phi) when (lid.FStar_Ident.idText = lid'.FStar_Ident.idText) -> begin
(let _166_601 = (p_ident lid)
in (p_refinement b.FStar_Parser_AST.aqual _166_601 t phi))
end
| _65_719 -> begin
(let _166_608 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (let _166_607 = (let _166_606 = (p_lident lid)
in (let _166_605 = (let _166_604 = (let _166_603 = (FStar_Pprint.break_ (Prims.parse_int "0"))
in (let _166_602 = (p_tmFormula t)
in (FStar_Pprint.op_Hat_Hat _166_603 _166_602)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _166_604))
in (FStar_Pprint.op_Hat_Hat _166_606 _166_605)))
in (FStar_Pprint.op_Hat_Hat _166_608 _166_607)))
end)
in if is_atomic then begin
(let _166_610 = (let _166_609 = (FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _166_609))
in (FStar_Pprint.group _166_610))
end else begin
(FStar_Pprint.group doc)
end)
end
| FStar_Parser_AST.TAnnotated (_65_722) -> begin
(failwith "Is this still used ?")
end
| FStar_Parser_AST.NoName (t) -> begin
(match ((let _166_611 = (unparen t)
in _166_611.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t); FStar_Parser_AST.brange = _65_731; FStar_Parser_AST.blevel = _65_729; FStar_Parser_AST.aqual = _65_727}, phi) -> begin
if is_atomic then begin
(let _166_614 = (let _166_613 = (let _166_612 = (p_refinement b.FStar_Parser_AST.aqual FStar_Pprint.underscore t phi)
in (FStar_Pprint.op_Hat_Hat _166_612 FStar_Pprint.rparen))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _166_613))
in (FStar_Pprint.group _166_614))
end else begin
(let _166_615 = (p_refinement b.FStar_Parser_AST.aqual FStar_Pprint.underscore t phi)
in (FStar_Pprint.group _166_615))
end
end
| _65_739 -> begin
if is_atomic then begin
(p_atomicTerm t)
end else begin
(p_appTerm t)
end
end)
end))
and p_refinement : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Pprint.document  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun aqual_opt binder t phi -> (let _166_626 = (FStar_Pprint.optional p_aqual aqual_opt)
in (let _166_625 = (let _166_624 = (let _166_623 = (let _166_622 = (p_appTerm t)
in (let _166_621 = (let _166_620 = (p_noSeqTerm phi)
in (soft_braces_with_nesting _166_620))
in (FStar_Pprint.op_Hat_Hat _166_622 _166_621)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _166_623))
in (FStar_Pprint.op_Hat_Hat binder _166_624))
in (FStar_Pprint.op_Hat_Hat _166_626 _166_625))))
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
and p_term : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _166_637 = (unparen e)
in _166_637.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Seq (e1, e2) -> begin
(let _166_641 = (let _166_639 = (let _166_638 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat _166_638 FStar_Pprint.semi))
in (FStar_Pprint.group _166_639))
in (let _166_640 = (p_term e2)
in (FStar_Pprint.op_Hat_Slash_Hat _166_641 _166_640)))
end
| _65_759 -> begin
(let _166_642 = (p_noSeqTerm e)
in (FStar_Pprint.group _166_642))
end))
and p_noSeqTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_noSeqTerm' e e.FStar_Parser_AST.range))
and p_noSeqTerm' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _166_645 = (unparen e)
in _166_645.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Ascribed (e, t) -> begin
(let _166_650 = (let _166_649 = (p_tmIff e)
in (let _166_648 = (let _166_647 = (let _166_646 = (p_typ t)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon _166_646))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.langle _166_647))
in (FStar_Pprint.op_Hat_Slash_Hat _166_649 _166_648)))
in (FStar_Pprint.group _166_650))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::(e3)::[]) when (op = ".()<-") -> begin
(let _166_661 = (let _166_660 = (let _166_657 = (let _166_656 = (p_atomicTermNotQUident e1)
in (let _166_655 = (let _166_654 = (let _166_653 = (let _166_651 = (p_term e2)
in (soft_parens_with_nesting _166_651))
in (let _166_652 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat _166_653 _166_652)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _166_654))
in (FStar_Pprint.op_Hat_Hat _166_656 _166_655)))
in (FStar_Pprint.group _166_657))
in (let _166_659 = (let _166_658 = (p_noSeqTerm e3)
in (jump2 _166_658))
in (FStar_Pprint.op_Hat_Hat _166_660 _166_659)))
in (FStar_Pprint.group _166_661))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::(e3)::[]) when (op = ".[]<-") -> begin
(let _166_672 = (let _166_671 = (let _166_668 = (let _166_667 = (p_atomicTermNotQUident e1)
in (let _166_666 = (let _166_665 = (let _166_664 = (let _166_662 = (p_term e2)
in (soft_brackets_with_nesting _166_662))
in (let _166_663 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat _166_664 _166_663)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _166_665))
in (FStar_Pprint.op_Hat_Hat _166_667 _166_666)))
in (FStar_Pprint.group _166_668))
in (let _166_670 = (let _166_669 = (p_noSeqTerm e3)
in (jump2 _166_669))
in (FStar_Pprint.op_Hat_Hat _166_671 _166_670)))
in (FStar_Pprint.group _166_672))
end
| FStar_Parser_AST.Requires (e, wtf) -> begin
(

let _65_784 = ()
in (let _166_675 = (let _166_674 = (str "requires")
in (let _166_673 = (p_typ e)
in (FStar_Pprint.op_Hat_Slash_Hat _166_674 _166_673)))
in (FStar_Pprint.group _166_675)))
end
| FStar_Parser_AST.Ensures (e, wtf) -> begin
(

let _65_790 = ()
in (let _166_678 = (let _166_677 = (str "ensures")
in (let _166_676 = (p_typ e)
in (FStar_Pprint.op_Hat_Slash_Hat _166_677 _166_676)))
in (FStar_Pprint.group _166_678)))
end
| FStar_Parser_AST.Attributes (es) -> begin
(let _166_681 = (let _166_680 = (str "attributes")
in (let _166_679 = (FStar_Pprint.separate_map break1 p_atomicTerm es)
in (FStar_Pprint.op_Hat_Slash_Hat _166_680 _166_679)))
in (FStar_Pprint.group _166_681))
end
| FStar_Parser_AST.If (e1, e2, e3) -> begin
if (is_unit e3) then begin
(let _166_688 = (let _166_687 = (let _166_683 = (str "if")
in (let _166_682 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat _166_683 _166_682)))
in (let _166_686 = (let _166_685 = (str "then")
in (let _166_684 = (p_noSeqTerm e2)
in (op_Hat_Slash_Plus_Hat _166_685 _166_684)))
in (FStar_Pprint.op_Hat_Slash_Hat _166_687 _166_686)))
in (FStar_Pprint.group _166_688))
end else begin
(

let e2_doc = (match ((let _166_689 = (unparen e2)
in _166_689.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.If (_65_800, _65_802, e3) when (is_unit e3) -> begin
(let _166_690 = (p_noSeqTerm e2)
in (soft_parens_with_nesting _166_690))
end
| _65_807 -> begin
(p_noSeqTerm e2)
end)
in (let _166_700 = (let _166_699 = (let _166_692 = (str "if")
in (let _166_691 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat _166_692 _166_691)))
in (let _166_698 = (let _166_697 = (let _166_693 = (str "then")
in (op_Hat_Slash_Plus_Hat _166_693 e2_doc))
in (let _166_696 = (let _166_695 = (str "else")
in (let _166_694 = (p_noSeqTerm e3)
in (op_Hat_Slash_Plus_Hat _166_695 _166_694)))
in (FStar_Pprint.op_Hat_Slash_Hat _166_697 _166_696)))
in (FStar_Pprint.op_Hat_Slash_Hat _166_699 _166_698)))
in (FStar_Pprint.group _166_700)))
end
end
| FStar_Parser_AST.TryWith (e, branches) -> begin
(let _166_707 = (let _166_706 = (let _166_702 = (str "try")
in (let _166_701 = (p_noSeqTerm e)
in (prefix2 _166_702 _166_701)))
in (let _166_705 = (let _166_704 = (str "with")
in (let _166_703 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat _166_704 _166_703)))
in (FStar_Pprint.op_Hat_Slash_Hat _166_706 _166_705)))
in (FStar_Pprint.group _166_707))
end
| FStar_Parser_AST.Match (e, branches) -> begin
(let _166_713 = (let _166_712 = (let _166_710 = (str "match")
in (let _166_709 = (p_noSeqTerm e)
in (let _166_708 = (str "with")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _166_710 _166_709 _166_708))))
in (let _166_711 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat _166_712 _166_711)))
in (FStar_Pprint.group _166_713))
end
| FStar_Parser_AST.LetOpen (uid, e) -> begin
(let _166_719 = (let _166_718 = (let _166_716 = (str "let open")
in (let _166_715 = (p_quident uid)
in (let _166_714 = (str "in")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _166_716 _166_715 _166_714))))
in (let _166_717 = (p_term e)
in (FStar_Pprint.op_Hat_Slash_Hat _166_718 _166_717)))
in (FStar_Pprint.group _166_719))
end
| FStar_Parser_AST.Let (q, lbs, e) -> begin
(

let let_doc = (let _166_721 = (str "let")
in (let _166_720 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat _166_721 _166_720)))
in (let _166_727 = (let _166_725 = (let _166_724 = (let _166_722 = (str "and")
in (precede_break_separate_map let_doc _166_722 p_letbinding lbs))
in (let _166_723 = (str "in")
in (FStar_Pprint.op_Hat_Slash_Hat _166_724 _166_723)))
in (FStar_Pprint.group _166_725))
in (let _166_726 = (p_term e)
in (FStar_Pprint.op_Hat_Slash_Hat _166_727 _166_726))))
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, typ_opt); FStar_Parser_AST.prange = _65_828})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, branches); FStar_Parser_AST.range = _65_838; FStar_Parser_AST.level = _65_836}) when (matches_var maybe_x x) -> begin
(let _166_730 = (let _166_729 = (str "function")
in (let _166_728 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat _166_729 _166_728)))
in (FStar_Pprint.group _166_730))
end
| FStar_Parser_AST.Assign (id, e) -> begin
(let _166_734 = (let _166_733 = (p_lident id)
in (let _166_732 = (let _166_731 = (p_noSeqTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow _166_731))
in (FStar_Pprint.op_Hat_Slash_Hat _166_733 _166_732)))
in (FStar_Pprint.group _166_734))
end
| _65_851 -> begin
(p_typ e)
end))
and p_typ : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_typ' e e.FStar_Parser_AST.range))
and p_typ' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _166_737 = (unparen e)
in _166_737.FStar_Parser_AST.tm)) with
| (FStar_Parser_AST.QForall (bs, trigger, e1)) | (FStar_Parser_AST.QExists (bs, trigger, e1)) -> begin
(let _166_744 = (let _166_740 = (let _166_738 = (p_quantifier e)
in (FStar_Pprint.op_Hat_Hat _166_738 FStar_Pprint.space))
in (let _166_739 = (p_binders true bs)
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") _166_740 _166_739 FStar_Pprint.dot)))
in (let _166_743 = (let _166_742 = (p_trigger trigger)
in (let _166_741 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat _166_742 _166_741)))
in (prefix2 _166_744 _166_743)))
end
| _65_862 -> begin
(p_simpleTerm e)
end))
and p_quantifier : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _166_746 = (unparen e)
in _166_746.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.QForall (_65_865) -> begin
(str "forall")
end
| FStar_Parser_AST.QExists (_65_868) -> begin
(str "exists")
end
| _65_871 -> begin
(failwith "Imposible : p_quantifier called on a non-quantifier term")
end))
and p_trigger : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun uu___375 -> (match (uu___375) with
| [] -> begin
FStar_Pprint.empty
end
| pats -> begin
(let _166_754 = (let _166_753 = (let _166_752 = (str "pattern")
in (let _166_751 = (let _166_750 = (let _166_748 = (p_disjunctivePats pats)
in (jump2 _166_748))
in (let _166_749 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1)
in (FStar_Pprint.op_Hat_Slash_Hat _166_750 _166_749)))
in (FStar_Pprint.op_Hat_Slash_Hat _166_752 _166_751)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _166_753))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace _166_754))
end))
and p_disjunctivePats : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun pats -> (let _166_756 = (str "\\/")
in (FStar_Pprint.separate_map _166_756 p_conjunctivePats pats)))
and p_conjunctivePats : FStar_Parser_AST.term Prims.list  ->  FStar_Pprint.document = (fun pats -> (let _166_758 = (FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats)
in (FStar_Pprint.group _166_758)))
and p_simpleTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _166_760 = (unparen e)
in _166_760.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Abs (pats, e) -> begin
(let _166_765 = (let _166_763 = (str "fun")
in (let _166_762 = (let _166_761 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Slash_Hat _166_761 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat _166_763 _166_762)))
in (let _166_764 = (p_term e)
in (op_Hat_Slash_Plus_Hat _166_765 _166_764)))
end
| _65_883 -> begin
(p_tmIff e)
end))
and p_maybeFocusArrow : Prims.bool  ->  FStar_Pprint.document = (fun b -> if b then begin
(str "~>")
end else begin
FStar_Pprint.rarrow
end)
and p_patternBranch : FStar_Parser_AST.branch  ->  FStar_Pprint.document = (fun _65_888 -> (match (_65_888) with
| (pat, when_opt, e) -> begin
(

let maybe_paren = (match ((let _166_770 = (unparen e)
in _166_770.FStar_Parser_AST.tm)) with
| (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) -> begin
soft_begin_end_with_nesting
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _65_899); FStar_Parser_AST.prange = _65_896})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, _65_910); FStar_Parser_AST.range = _65_907; FStar_Parser_AST.level = _65_905}) when (matches_var maybe_x x) -> begin
soft_begin_end_with_nesting
end
| _65_917 -> begin
(fun x -> x)
end)
in (let _166_781 = (let _166_780 = (let _166_777 = (let _166_776 = (let _166_775 = (let _166_774 = (p_disjunctivePattern pat)
in (let _166_773 = (let _166_772 = (p_maybeWhen when_opt)
in (FStar_Pprint.op_Hat_Hat _166_772 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat _166_774 _166_773)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _166_775))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar _166_776))
in (FStar_Pprint.group _166_777))
in (let _166_779 = (let _166_778 = (p_term e)
in (maybe_paren _166_778))
in (op_Hat_Slash_Plus_Hat _166_780 _166_779)))
in (FStar_Pprint.group _166_781)))
end))
and p_maybeWhen : FStar_Parser_AST.term Prims.option  ->  FStar_Pprint.document = (fun uu___376 -> (match (uu___376) with
| None -> begin
FStar_Pprint.empty
end
| Some (e) -> begin
(let _166_785 = (str "when")
in (let _166_784 = (let _166_783 = (p_tmFormula e)
in (FStar_Pprint.op_Hat_Hat _166_783 FStar_Pprint.space))
in (op_Hat_Slash_Plus_Hat _166_785 _166_784)))
end))
and p_tmIff : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _166_787 = (unparen e)
in _166_787.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Op ("<==>", (e1)::(e2)::[]) -> begin
(let _166_790 = (str "<==>")
in (let _166_789 = (p_tmImplies e1)
in (let _166_788 = (p_tmIff e2)
in (infix0 _166_790 _166_789 _166_788))))
end
| _65_932 -> begin
(p_tmImplies e)
end))
and p_tmImplies : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _166_792 = (unparen e)
in _166_792.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Op ("==>", (e1)::(e2)::[]) -> begin
(let _166_795 = (str "==>")
in (let _166_794 = (p_tmArrow p_tmFormula e1)
in (let _166_793 = (p_tmImplies e2)
in (infix0 _166_795 _166_794 _166_793))))
end
| _65_941 -> begin
(p_tmArrow p_tmFormula e)
end))
and p_tmArrow : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_Tm e -> (match ((let _166_801 = (unparen e)
in _166_801.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Product (bs, tgt) -> begin
(let _166_808 = (let _166_807 = (FStar_Pprint.concat_map (fun b -> (let _166_805 = (p_binder false b)
in (let _166_804 = (let _166_803 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _166_803))
in (FStar_Pprint.op_Hat_Hat _166_805 _166_804)))) bs)
in (let _166_806 = (p_tmArrow p_Tm tgt)
in (FStar_Pprint.op_Hat_Hat _166_807 _166_806)))
in (FStar_Pprint.group _166_808))
end
| _65_950 -> begin
(p_Tm e)
end))
and p_tmFormula : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _166_810 = (unparen e)
in _166_810.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Op ("\\/", (e1)::(e2)::[]) -> begin
(let _166_813 = (str "\\/")
in (let _166_812 = (p_tmFormula e1)
in (let _166_811 = (p_tmConjunction e2)
in (infix0 _166_813 _166_812 _166_811))))
end
| _65_959 -> begin
(p_tmConjunction e)
end))
and p_tmConjunction : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _166_815 = (unparen e)
in _166_815.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Op ("/\\", (e1)::(e2)::[]) -> begin
(let _166_818 = (str "/\\")
in (let _166_817 = (p_tmConjunction e1)
in (let _166_816 = (p_tmTuple e2)
in (infix0 _166_818 _166_817 _166_816))))
end
| _65_968 -> begin
(p_tmTuple e)
end))
and p_tmTuple : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _166_820 = (unparen e)
in _166_820.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Construct (lid, args) when (is_tuple_constructor lid) -> begin
(let _166_822 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map _166_822 (fun _65_977 -> (match (_65_977) with
| (e, _65_976) -> begin
(p_tmEq e)
end)) args))
end
| _65_979 -> begin
(p_tmEq e)
end))
and paren_if : Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun curr mine doc -> if (mine <= curr) then begin
doc
end else begin
(let _166_827 = (let _166_826 = (FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _166_826))
in (FStar_Pprint.group _166_827))
end)
and p_tmEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n = (max_level (FStar_List.append ((colon_equals)::(pipe_right)::[]) operatorInfix0ad12))
in (p_tmEq' n e)))
and p_tmEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (match ((let _166_831 = (unparen e)
in _166_831.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (((is_operatorInfix0ad12 op) || (op = "=")) || (op = "|>")) -> begin
(

let _65_996 = (levels op)
in (match (_65_996) with
| (left, mine, right) -> begin
(let _166_835 = (let _166_834 = (str op)
in (let _166_833 = (p_tmEq' left e1)
in (let _166_832 = (p_tmEq' right e2)
in (infix0 _166_834 _166_833 _166_832))))
in (paren_if curr mine _166_835))
end))
end
| FStar_Parser_AST.Op (":=", (e1)::(e2)::[]) -> begin
(let _166_841 = (let _166_840 = (p_tmEq e1)
in (let _166_839 = (let _166_838 = (let _166_837 = (let _166_836 = (p_tmEq e2)
in (op_Hat_Slash_Plus_Hat FStar_Pprint.equals _166_836))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _166_837))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _166_838))
in (FStar_Pprint.op_Hat_Hat _166_840 _166_839)))
in (FStar_Pprint.group _166_841))
end
| _65_1004 -> begin
(p_tmNoEq e)
end))
and p_tmNoEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n = (max_level ((colon_colon)::(amp)::(opinfix3)::(opinfix4)::[]))
in (p_tmNoEq' n e)))
and p_tmNoEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (match ((let _166_845 = (unparen e)
in _166_845.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Construct (lid, ((e1, _65_1016))::((e2, _65_1012))::[]) when ((FStar_Ident.lid_equals lid FStar_Syntax_Const.cons_lid) && (not ((is_list e)))) -> begin
(

let op = "::"
in (

let _65_1025 = (levels op)
in (match (_65_1025) with
| (left, mine, right) -> begin
(let _166_849 = (let _166_848 = (str op)
in (let _166_847 = (p_tmNoEq' left e1)
in (let _166_846 = (p_tmNoEq' right e2)
in (infix0 _166_848 _166_847 _166_846))))
in (paren_if curr mine _166_849))
end)))
end
| FStar_Parser_AST.Sum (binders, res) -> begin
(

let op = "&"
in (

let _65_1034 = (levels op)
in (match (_65_1034) with
| (left, mine, right) -> begin
(

let p_dsumfst = (fun b -> (let _166_855 = (p_binder false b)
in (let _166_854 = (let _166_853 = (let _166_852 = (str "&")
in (FStar_Pprint.op_Hat_Hat _166_852 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _166_853))
in (FStar_Pprint.op_Hat_Hat _166_855 _166_854))))
in (let _166_858 = (let _166_857 = (FStar_Pprint.concat_map p_dsumfst binders)
in (let _166_856 = (p_tmNoEq' right res)
in (FStar_Pprint.op_Hat_Hat _166_857 _166_856)))
in (paren_if curr mine _166_858)))
end)))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (is_operatorInfix34 op) -> begin
(

let _65_1046 = (levels op)
in (match (_65_1046) with
| (left, mine, right) -> begin
(let _166_862 = (let _166_861 = (str op)
in (let _166_860 = (p_tmNoEq' left e1)
in (let _166_859 = (p_tmNoEq' right e2)
in (infix0 _166_861 _166_860 _166_859))))
in (paren_if curr mine _166_862))
end))
end
| FStar_Parser_AST.Op ("-", (e)::[]) -> begin
(

let _65_1055 = (levels "-")
in (match (_65_1055) with
| (left, mine, right) -> begin
(let _166_863 = (p_tmNoEq' mine e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus _166_863))
end))
end
| FStar_Parser_AST.NamedTyp (lid, e) -> begin
(let _166_867 = (let _166_866 = (p_lidentOrUnderscore lid)
in (let _166_865 = (let _166_864 = (p_appTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon _166_864))
in (FStar_Pprint.op_Hat_Slash_Hat _166_866 _166_865)))
in (FStar_Pprint.group _166_867))
end
| FStar_Parser_AST.Refine (b, phi) -> begin
(p_refinedBinder b phi)
end
| FStar_Parser_AST.Record (with_opt, record_fields) -> begin
(let _166_871 = (let _166_870 = (default_or_map FStar_Pprint.empty p_with_clause with_opt)
in (let _166_869 = (let _166_868 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (FStar_Pprint.separate_map _166_868 p_simpleDef record_fields))
in (FStar_Pprint.op_Hat_Hat _166_870 _166_869)))
in (braces_with_nesting _166_871))
end
| FStar_Parser_AST.Op ("~", (e)::[]) -> begin
(let _166_874 = (let _166_873 = (str "~")
in (let _166_872 = (p_atomicTerm e)
in (FStar_Pprint.op_Hat_Hat _166_873 _166_872)))
in (FStar_Pprint.group _166_874))
end
| _65_1074 -> begin
(p_appTerm e)
end))
and p_with_clause : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (let _166_879 = (p_appTerm e)
in (let _166_878 = (let _166_877 = (let _166_876 = (str "with")
in (FStar_Pprint.op_Hat_Hat _166_876 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _166_877))
in (FStar_Pprint.op_Hat_Hat _166_879 _166_878))))
and p_refinedBinder : FStar_Parser_AST.binder  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun b phi -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (lid, t) -> begin
(let _166_883 = (let _166_882 = (p_lident lid)
in (p_refinement b.FStar_Parser_AST.aqual _166_882 t phi))
in (soft_parens_with_nesting _166_883))
end
| FStar_Parser_AST.TAnnotated (_65_1083) -> begin
(failwith "Is this still used ?")
end
| (FStar_Parser_AST.Variable (_)) | (FStar_Parser_AST.TVariable (_)) | (FStar_Parser_AST.NoName (_)) -> begin
(let _166_885 = (let _166_884 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" _166_884))
in (failwith _166_885))
end))
and p_simpleDef : (FStar_Ident.lid * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun _65_1096 -> (match (_65_1096) with
| (lid, e) -> begin
(let _166_890 = (let _166_889 = (p_qlident lid)
in (let _166_888 = (let _166_887 = (p_tmIff e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals _166_887))
in (FStar_Pprint.op_Hat_Slash_Hat _166_889 _166_888)))
in (FStar_Pprint.group _166_890))
end))
and p_appTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _166_892 = (unparen e)
in _166_892.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (_65_1099) when (is_general_application e) -> begin
(

let _65_1103 = (head_and_args e)
in (match (_65_1103) with
| (head, args) -> begin
(let _166_894 = (p_indexingTerm head)
in (let _166_893 = (FStar_Pprint.separate_map FStar_Pprint.space p_argTerm args)
in (op_Hat_Slash_Plus_Hat _166_894 _166_893)))
end))
end
| FStar_Parser_AST.Construct (lid, args) when ((is_general_construction e) && (not ((is_dtuple_constructor lid)))) -> begin
(match (args) with
| [] -> begin
(p_quident lid)
end
| (arg)::[] -> begin
(let _166_897 = (let _166_896 = (p_quident lid)
in (let _166_895 = (p_argTerm arg)
in (FStar_Pprint.op_Hat_Slash_Hat _166_896 _166_895)))
in (FStar_Pprint.group _166_897))
end
| (hd)::tl -> begin
(let _166_904 = (let _166_903 = (let _166_900 = (let _166_899 = (p_quident lid)
in (let _166_898 = (p_argTerm hd)
in (FStar_Pprint.op_Hat_Slash_Hat _166_899 _166_898)))
in (FStar_Pprint.group _166_900))
in (let _166_902 = (let _166_901 = (FStar_Pprint.separate_map break1 p_argTerm tl)
in (jump2 _166_901))
in (FStar_Pprint.op_Hat_Hat _166_903 _166_902)))
in (FStar_Pprint.group _166_904))
end)
end
| _65_1115 -> begin
(p_indexingTerm e)
end))
and p_argTerm : (FStar_Parser_AST.term * FStar_Parser_AST.imp)  ->  FStar_Pprint.document = (fun arg_imp -> (match (arg_imp) with
| ({FStar_Parser_AST.tm = FStar_Parser_AST.Uvar (_65_1122); FStar_Parser_AST.range = _65_1120; FStar_Parser_AST.level = _65_1118}, FStar_Parser_AST.UnivApp) -> begin
(p_univar (Prims.fst arg_imp))
end
| (u, FStar_Parser_AST.UnivApp) -> begin
(p_universe u)
end
| (e, FStar_Parser_AST.FsTypApp) -> begin
(let _166_906 = (p_indexingTerm e)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.langle _166_906 FStar_Pprint.rangle))
end
| (e, FStar_Parser_AST.Hash) -> begin
(let _166_908 = (str "#")
in (let _166_907 = (p_indexingTerm e)
in (FStar_Pprint.op_Hat_Hat _166_908 _166_907)))
end
| (e, FStar_Parser_AST.Nothing) -> begin
(p_indexingTerm e)
end))
and p_indexingTerm_aux : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun exit e -> (match ((let _166_914 = (unparen e)
in _166_914.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Op (".()", (e1)::(e2)::[]) -> begin
(let _166_919 = (let _166_918 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (let _166_917 = (let _166_916 = (let _166_915 = (p_term e2)
in (soft_parens_with_nesting _166_915))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _166_916))
in (FStar_Pprint.op_Hat_Hat _166_918 _166_917)))
in (FStar_Pprint.group _166_919))
end
| FStar_Parser_AST.Op (".[]", (e1)::(e2)::[]) -> begin
(let _166_924 = (let _166_923 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (let _166_922 = (let _166_921 = (let _166_920 = (p_term e2)
in (soft_brackets_with_nesting _166_920))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _166_921))
in (FStar_Pprint.op_Hat_Hat _166_923 _166_922)))
in (FStar_Pprint.group _166_924))
end
| _65_1154 -> begin
(exit e)
end))
and p_indexingTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_indexingTerm_aux p_atomicTerm e))
and p_atomicTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _166_927 = (unparen e)
in _166_927.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.LetOpen (lid, e) -> begin
(let _166_931 = (p_quident lid)
in (let _166_930 = (let _166_929 = (let _166_928 = (p_term e)
in (soft_parens_with_nesting _166_928))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _166_929))
in (FStar_Pprint.op_Hat_Hat _166_931 _166_930)))
end
| FStar_Parser_AST.Name (lid) -> begin
(p_quident lid)
end
| FStar_Parser_AST.Op (op, (e)::[]) when (is_general_prefix_op op) -> begin
(let _166_933 = (str op)
in (let _166_932 = (p_atomicTerm e)
in (FStar_Pprint.op_Hat_Hat _166_933 _166_932)))
end
| _65_1169 -> begin
(p_atomicTermNotQUident e)
end))
and p_atomicTermNotQUident : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _166_935 = (unparen e)
in _166_935.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.Var (lid) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.assert_lid) -> begin
(str "assert")
end
| FStar_Parser_AST.Tvar (tv) -> begin
(p_tvar tv)
end
| FStar_Parser_AST.Const (c) -> begin
(p_constant c)
end
| FStar_Parser_AST.Name (lid) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.true_lid) -> begin
(str "True")
end
| FStar_Parser_AST.Name (lid) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.false_lid) -> begin
(str "False")
end
| FStar_Parser_AST.Op (op, (e)::[]) when (is_general_prefix_op op) -> begin
(let _166_937 = (str op)
in (let _166_936 = (p_atomicTermNotQUident e)
in (FStar_Pprint.op_Hat_Hat _166_937 _166_936)))
end
| FStar_Parser_AST.Op (op, []) -> begin
(let _166_941 = (let _166_940 = (let _166_939 = (str op)
in (let _166_938 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat _166_939 _166_938)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _166_940))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _166_941))
end
| FStar_Parser_AST.Construct (lid, args) when (is_dtuple_constructor lid) -> begin
(let _166_946 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (let _166_945 = (let _166_943 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (let _166_942 = (FStar_List.map Prims.fst args)
in (FStar_Pprint.separate_map _166_943 p_tmEq _166_942)))
in (let _166_944 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _166_946 _166_945 _166_944))))
end
| FStar_Parser_AST.Project (e, lid) -> begin
(let _166_950 = (let _166_949 = (p_atomicTermNotQUident e)
in (let _166_948 = (let _166_947 = (p_qlident lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _166_947))
in (FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0") _166_949 _166_948)))
in (FStar_Pprint.group _166_950))
end
| _65_1200 -> begin
(p_projectionLHS e)
end))
and p_projectionLHS : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _166_952 = (unparen e)
in _166_952.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Var (lid) -> begin
(p_qlident lid)
end
| FStar_Parser_AST.Projector (constr_lid, field_lid) -> begin
(let _166_956 = (p_quident constr_lid)
in (let _166_955 = (let _166_954 = (let _166_953 = (p_lident field_lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _166_953))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark _166_954))
in (FStar_Pprint.op_Hat_Hat _166_956 _166_955)))
end
| FStar_Parser_AST.Discrim (constr_lid) -> begin
(let _166_957 = (p_quident constr_lid)
in (FStar_Pprint.op_Hat_Hat _166_957 FStar_Pprint.qmark))
end
| FStar_Parser_AST.Paren (e) -> begin
(let _166_958 = (p_term e)
in (soft_parens_with_nesting _166_958))
end
| _65_1213 when (is_array e) -> begin
(

let es = (extract_from_list e)
in (let _166_962 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar)
in (let _166_961 = (let _166_959 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (separate_map_or_flow _166_959 p_noSeqTerm es))
in (let _166_960 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") _166_962 _166_961 _166_960)))))
end
| _65_1216 when (is_list e) -> begin
(let _166_965 = (let _166_964 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (let _166_963 = (extract_from_list e)
in (separate_map_or_flow _166_964 p_noSeqTerm _166_963)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket _166_965 FStar_Pprint.rbracket))
end
| _65_1218 when (is_lex_list e) -> begin
(let _166_969 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket)
in (let _166_968 = (let _166_967 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (let _166_966 = (extract_from_list e)
in (separate_map_or_flow _166_967 p_noSeqTerm _166_966)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _166_969 _166_968 FStar_Pprint.rbracket)))
end
| _65_1220 when (is_ref_set e) -> begin
(

let es = (extract_from_ref_set e)
in (let _166_972 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace)
in (let _166_971 = (let _166_970 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (separate_map_or_flow _166_970 p_appTerm es))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") _166_972 _166_971 FStar_Pprint.rbrace))))
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Op (_)) | (FStar_Parser_AST.Tvar (_)) | (FStar_Parser_AST.Uvar (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) | (FStar_Parser_AST.Construct (_)) | (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.App (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.LetOpen (_)) | (FStar_Parser_AST.Seq (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Ascribed (_)) | (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Project (_)) | (FStar_Parser_AST.Product (_)) | (FStar_Parser_AST.Sum (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Refine (_)) | (FStar_Parser_AST.NamedTyp (_)) | (FStar_Parser_AST.Requires (_)) | (FStar_Parser_AST.Ensures (_)) | (FStar_Parser_AST.Assign (_)) | (FStar_Parser_AST.Attributes (_)) -> begin
(let _166_973 = (p_term e)
in (soft_parens_with_nesting _166_973))
end
| FStar_Parser_AST.Labeled (_65_1308) -> begin
(failwith "Not valid in universe")
end))
and p_constant : FStar_Const.sconst  ->  FStar_Pprint.document = (fun uu___379 -> (match (uu___379) with
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
(let _166_975 = (FStar_Pprint.doc_of_char x)
in (FStar_Pprint.squotes _166_975))
end
| FStar_Const.Const_string (bytes, _65_1321) -> begin
(let _166_976 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes _166_976))
end
| FStar_Const.Const_bytearray (bytes, _65_1326) -> begin
(let _166_979 = (let _166_977 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes _166_977))
in (let _166_978 = (str "B")
in (FStar_Pprint.op_Hat_Hat _166_979 _166_978)))
end
| FStar_Const.Const_int (repr, sign_width_opt) -> begin
(

let signedness = (fun uu___377 -> (match (uu___377) with
| FStar_Const.Unsigned -> begin
(str "u")
end
| FStar_Const.Signed -> begin
FStar_Pprint.empty
end))
in (

let width = (fun uu___378 -> (match (uu___378) with
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

let ending = (default_or_map FStar_Pprint.empty (fun _65_1345 -> (match (_65_1345) with
| (s, w) -> begin
(let _166_986 = (signedness s)
in (let _166_985 = (width w)
in (FStar_Pprint.op_Hat_Hat _166_986 _166_985)))
end)) sign_width_opt)
in (let _166_987 = (str repr)
in (FStar_Pprint.op_Hat_Hat _166_987 ending)))))
end
| FStar_Const.Const_range (r) -> begin
(let _166_988 = (FStar_Range.string_of_range r)
in (str _166_988))
end
| FStar_Const.Const_reify -> begin
(str "reify")
end
| FStar_Const.Const_reflect (lid) -> begin
(let _166_992 = (p_quident lid)
in (let _166_991 = (let _166_990 = (let _166_989 = (str "reflect")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _166_989))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark _166_990))
in (FStar_Pprint.op_Hat_Hat _166_992 _166_991)))
end))
and p_universe : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (let _166_995 = (str "u#")
in (let _166_994 = (p_atomicUniverse u)
in (FStar_Pprint.op_Hat_Hat _166_995 _166_994))))
and p_universeFrom : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match ((let _166_997 = (unparen u)
in _166_997.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Op ("+", (u1)::(u2)::[]) -> begin
(let _166_1001 = (let _166_1000 = (p_universeFrom u1)
in (let _166_999 = (let _166_998 = (p_universeFrom u2)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus _166_998))
in (FStar_Pprint.op_Hat_Slash_Hat _166_1000 _166_999)))
in (FStar_Pprint.group _166_1001))
end
| FStar_Parser_AST.App (_65_1361) -> begin
(

let _65_1365 = (head_and_args u)
in (match (_65_1365) with
| (head, args) -> begin
(match ((let _166_1002 = (unparen head)
in _166_1002.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Var (maybe_max_lid) when (FStar_Ident.lid_equals maybe_max_lid FStar_Syntax_Const.max_lid) -> begin
(let _166_1006 = (let _166_1005 = (p_qlident FStar_Syntax_Const.max_lid)
in (let _166_1004 = (FStar_Pprint.separate_map FStar_Pprint.space (fun _65_1371 -> (match (_65_1371) with
| (u, _65_1370) -> begin
(p_atomicUniverse u)
end)) args)
in (op_Hat_Slash_Plus_Hat _166_1005 _166_1004)))
in (FStar_Pprint.group _166_1006))
end
| _65_1373 -> begin
(let _166_1008 = (let _166_1007 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" _166_1007))
in (failwith _166_1008))
end)
end))
end
| _65_1375 -> begin
(p_atomicUniverse u)
end))
and p_atomicUniverse : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match ((let _166_1010 = (unparen u)
in _166_1010.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (r, sw)) -> begin
(p_constant (FStar_Const.Const_int (((r), (sw)))))
end
| FStar_Parser_AST.Uvar (_65_1384) -> begin
(p_univar u)
end
| FStar_Parser_AST.Paren (u) -> begin
(let _166_1011 = (p_universeFrom u)
in (soft_parens_with_nesting _166_1011))
end
| (FStar_Parser_AST.Op ("+", (_)::(_)::[])) | (FStar_Parser_AST.App (_)) -> begin
(let _166_1012 = (p_universeFrom u)
in (soft_parens_with_nesting _166_1012))
end
| _65_1400 -> begin
(let _166_1014 = (let _166_1013 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" _166_1013))
in (failwith _166_1014))
end))
and p_univar : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match ((let _166_1016 = (unparen u)
in _166_1016.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Uvar (id) -> begin
(str (FStar_Ident.text_of_id id))
end
| _65_1405 -> begin
(let _166_1018 = (let _166_1017 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Not a universe variable %s" _166_1017))
in (failwith _166_1018))
end))


let term_to_document : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_term e))


let decl_to_document : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun e -> (p_decl e))


let modul_to_document : FStar_Parser_AST.modul  ->  FStar_Pprint.document = (fun m -> (match (m) with
| (FStar_Parser_AST.Module (_, decls)) | (FStar_Parser_AST.Interface (_, decls, _)) -> begin
(let _166_1025 = (FStar_All.pipe_right decls (FStar_List.map decl_to_document))
in (FStar_All.pipe_right _166_1025 (FStar_Pprint.separate FStar_Pprint.hardline)))
end))


let comments_to_document : (Prims.string * FStar_Range.range) Prims.list  ->  FStar_Pprint.document = (fun comments -> (FStar_Pprint.separate_map FStar_Pprint.hardline (fun _65_1423 -> (match (_65_1423) with
| (comment, range) -> begin
(str comment)
end)) comments))


let modul_with_comments_to_document : FStar_Parser_AST.modul  ->  (Prims.string * FStar_Range.range) Prims.list  ->  (FStar_Pprint.document * (Prims.string * FStar_Range.range) Prims.list) = (fun m comments -> (

let rec aux = (fun _65_1430 decl -> (match (_65_1430) with
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

let rec process_preceding_comments = (fun doc last_line end_pos n uu___380 -> (match (uu___380) with
| ((comment, range))::comments when (let _166_1051 = (FStar_Range.start_of_range range)
in (FStar_Range.pos_geq end_pos _166_1051)) -> begin
(

let l = (let _166_1053 = ((let _166_1052 = (FStar_Range.start_of_range range)
in (FStar_Range.line_of_pos _166_1052)) - last_line)
in (max (Prims.parse_int "1") _166_1053))
in (

let doc = (let _166_1056 = (let _166_1055 = (FStar_Pprint.repeat l FStar_Pprint.hardline)
in (let _166_1054 = (str comment)
in (FStar_Pprint.op_Hat_Hat _166_1055 _166_1054)))
in (FStar_Pprint.op_Hat_Hat doc _166_1056))
in (let _166_1058 = (let _166_1057 = (FStar_Range.end_of_range range)
in (FStar_Range.line_of_pos _166_1057))
in (process_preceding_comments doc _166_1058 end_pos (Prims.parse_int "1") comments))))
end
| comments -> begin
(

let l = (let _166_1059 = ((FStar_Range.line_of_pos end_pos) - last_line)
in (max n _166_1059))
in (let _166_1061 = (let _166_1060 = (FStar_Pprint.repeat l FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat doc _166_1060))
in ((_166_1061), (comments))))
end))
in (

let _65_1453 = (let _166_1064 = (FStar_Range.line_of_pos previous_range_end)
in (let _166_1063 = (let _166_1062 = (FStar_Range.start_of_range current_range)
in (FStar_Range.end_of_line _166_1062))
in (process_preceding_comments doc _166_1064 _166_1063 (Prims.parse_int "0") comments)))
in (match (_65_1453) with
| (doc, comments) -> begin
(

let _65_1461 = (FStar_Util.take (fun uu___381 -> (match (uu___381) with
| (_65_1456, range) -> begin
(FStar_Range.range_contains_range current_range range)
end)) comments)
in (match (_65_1461) with
| (inner_comments, comments) -> begin
(

let _65_1462 = (FStar_ST.op_Colon_Equals comment_stack inner_comments)
in (

let doc = (let _166_1066 = (decl_to_document decl)
in (FStar_Pprint.op_Hat_Hat doc _166_1066))
in (

let inner_comments_doc = if ((FStar_ST.read comment_stack) = []) then begin
FStar_Pprint.empty
end else begin
(

let _65_1465 = (let _166_1069 = (let _166_1068 = (let _166_1067 = (FStar_ST.read comment_stack)
in (FStar_List.map Prims.fst _166_1067))
in (FStar_String.concat " ; " _166_1068))
in (FStar_Util.print1_warning "Leftover comments : %s\n" _166_1069))
in (let _166_1070 = (FStar_ST.read comment_stack)
in (comments_to_document _166_1070)))
end
in (let _166_1072 = (FStar_Range.end_of_range decl.FStar_Parser_AST.drange)
in (let _166_1071 = (FStar_Pprint.op_Hat_Hat doc inner_comments_doc)
in ((_166_1072), (comments), (_166_1071)))))))
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
| (d)::_65_1482 -> begin
(

let _65_1489 = (FStar_List.fold_left aux ((FStar_Range.zeroPos), (comments), (FStar_Pprint.empty)) decls)
in (match (_65_1489) with
| (_65_1486, comments, doc) -> begin
((doc), (comments))
end))
end))))




