
open Prims

let should_unparen : Prims.bool FStar_ST.ref = (FStar_ST.alloc true)


let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> if (not ((FStar_ST.read should_unparen))) then begin
t
end else begin
(match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| _68_22 -> begin
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


let separate_break_map = (fun sep f l -> (let _167_35 = (let _167_34 = (let _167_33 = (FStar_Pprint.op_Hat_Hat sep break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_33))
in (FStar_Pprint.separate_map _167_34 f l))
in (FStar_Pprint.group _167_35)))


let precede_break_separate_map = (fun prec sep f l -> (let _167_52 = (let _167_45 = (FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space)
in (let _167_44 = (let _167_43 = (FStar_List.hd l)
in (FStar_All.pipe_right _167_43 f))
in (FStar_Pprint.precede _167_45 _167_44)))
in (let _167_51 = (let _167_50 = (FStar_List.tl l)
in (FStar_Pprint.concat_map (fun x -> (let _167_49 = (let _167_48 = (let _167_47 = (f x)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_47))
in (FStar_Pprint.op_Hat_Hat sep _167_48))
in (FStar_Pprint.op_Hat_Hat break1 _167_49))) _167_50))
in (FStar_Pprint.op_Hat_Hat _167_52 _167_51))))


let concat_break_map = (fun f l -> (let _167_60 = (FStar_Pprint.concat_map (fun x -> (let _167_59 = (f x)
in (FStar_Pprint.op_Hat_Hat _167_59 break1))) l)
in (FStar_Pprint.group _167_60)))


let parens_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lparen contents FStar_Pprint.rparen))


let soft_parens_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lparen contents FStar_Pprint.rparen))


let braces_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbrace contents FStar_Pprint.rbrace))


let soft_braces_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbrace contents FStar_Pprint.rbrace))


let brackets_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbracket contents FStar_Pprint.rbracket))


let soft_brackets_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbracket contents FStar_Pprint.rbracket))


let soft_begin_end_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (let _167_76 = (str "begin")
in (let _167_75 = (str "end")
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") _167_76 contents _167_75))))


let separate_map_or_flow = (fun sep f l -> if ((FStar_List.length l) < (Prims.parse_int "10")) then begin
(FStar_Pprint.separate_map sep f l)
end else begin
(FStar_Pprint.flow_map sep f l)
end)


let doc_of_fsdoc : (Prims.string * (Prims.string * Prims.string) Prims.list)  ->  FStar_Pprint.document = (fun _68_58 -> (match (_68_58) with
| (comment, keywords) -> begin
(let _167_96 = (let _167_95 = (let _167_94 = (str comment)
in (let _167_93 = (let _167_92 = (let _167_91 = (FStar_Pprint.separate_map FStar_Pprint.comma (fun _68_61 -> (match (_68_61) with
| (k, v) -> begin
(let _167_90 = (let _167_89 = (str k)
in (let _167_88 = (let _167_87 = (let _167_86 = (str v)
in (_167_86)::[])
in (FStar_Pprint.rarrow)::_167_87)
in (_167_89)::_167_88))
in (FStar_Pprint.concat _167_90))
end)) keywords)
in (_167_91)::[])
in (FStar_Pprint.space)::_167_92)
in (_167_94)::_167_93))
in (FStar_Pprint.concat _167_95))
in (FStar_Pprint.group _167_96))
end))


let is_unit : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match ((let _167_99 = (unparen e)
in _167_99.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Const (FStar_Const.Const_unit) -> begin
true
end
| _68_66 -> begin
false
end))


let matches_var : FStar_Parser_AST.term  ->  FStar_Ident.ident  ->  Prims.bool = (fun t x -> (match ((let _167_104 = (unparen t)
in _167_104.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Var (y) -> begin
(x.FStar_Ident.idText = (FStar_Ident.text_of_lid y))
end
| _68_72 -> begin
false
end))


let is_tuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Syntax_Util.is_tuple_data_lid'


let is_dtuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Syntax_Util.is_dtuple_data_lid'


let is_list_structure : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun cons_lid nil_lid -> (

let rec aux = (fun e -> (match ((let _167_117 = (unparen e)
in _167_117.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Construct (lid, []) -> begin
(FStar_Ident.lid_equals lid nil_lid)
end
| FStar_Parser_AST.Construct (lid, (_68_87)::((e2, _68_84))::[]) -> begin
((FStar_Ident.lid_equals lid cons_lid) && (aux e2))
end
| _68_92 -> begin
false
end))
in aux))


let is_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Syntax_Const.cons_lid FStar_Syntax_Const.nil_lid)


let is_lex_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Syntax_Const.lexcons_lid FStar_Syntax_Const.lextop_lid)


let rec extract_from_list : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (match ((let _167_122 = (unparen e)
in _167_122.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Construct (_68_95, []) -> begin
[]
end
| FStar_Parser_AST.Construct (_68_100, ((e1, FStar_Parser_AST.Nothing))::((e2, FStar_Parser_AST.Nothing))::[]) -> begin
(let _167_123 = (extract_from_list e2)
in (e1)::_167_123)
end
| _68_111 -> begin
(let _167_125 = (let _167_124 = (FStar_Parser_AST.term_to_string e)
in (FStar_Util.format1 "Not a list %s" _167_124))
in (failwith _167_125))
end))


let is_array : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match ((let _167_128 = (unparen e)
in _167_128.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (lid); FStar_Parser_AST.range = _68_116; FStar_Parser_AST.level = _68_114}, l, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals lid FStar_Syntax_Const.array_mk_array_lid) && (is_list l))
end
| _68_125 -> begin
false
end))


let rec is_ref_set : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match ((let _167_131 = (unparen e)
in _167_131.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Var (maybe_empty_lid) -> begin
(FStar_Ident.lid_equals maybe_empty_lid FStar_Syntax_Const.tset_empty)
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_singleton_lid); FStar_Parser_AST.range = _68_132; FStar_Parser_AST.level = _68_130}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_ref_lid); FStar_Parser_AST.range = _68_143; FStar_Parser_AST.level = _68_141}, e, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = _68_139; FStar_Parser_AST.level = _68_137}, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals maybe_singleton_lid FStar_Syntax_Const.tset_singleton) && (FStar_Ident.lid_equals maybe_ref_lid FStar_Syntax_Const.heap_ref))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_union_lid); FStar_Parser_AST.range = _68_162; FStar_Parser_AST.level = _68_160}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = _68_158; FStar_Parser_AST.level = _68_156}, e2, FStar_Parser_AST.Nothing) -> begin
(((FStar_Ident.lid_equals maybe_union_lid FStar_Syntax_Const.tset_union) && (is_ref_set e1)) && (is_ref_set e2))
end
| _68_176 -> begin
false
end))


let rec extract_from_ref_set : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (match ((let _167_134 = (unparen e)
in _167_134.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Var (_68_179) -> begin
[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (_68_186); FStar_Parser_AST.range = _68_184; FStar_Parser_AST.level = _68_182}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (_68_198); FStar_Parser_AST.range = _68_196; FStar_Parser_AST.level = _68_194}, e, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = _68_192; FStar_Parser_AST.level = _68_190}, FStar_Parser_AST.Nothing) -> begin
(e)::[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (_68_218); FStar_Parser_AST.range = _68_216; FStar_Parser_AST.level = _68_214}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = _68_212; FStar_Parser_AST.level = _68_210}, e2, FStar_Parser_AST.Nothing) -> begin
(let _167_136 = (extract_from_ref_set e1)
in (let _167_135 = (extract_from_ref_set e2)
in (FStar_List.append _167_136 _167_135)))
end
| _68_231 -> begin
(let _167_138 = (let _167_137 = (FStar_Parser_AST.term_to_string e)
in (FStar_Util.format1 "Not a ref set %s" _167_137))
in (failwith _167_138))
end))


let is_general_application : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (not (((is_array e) || (is_ref_set e)))))


let is_general_construction : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (not (((is_list e) || (is_lex_list e)))))


let is_general_prefix_op : Prims.string  ->  Prims.bool = (fun op -> (op <> "~"))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun e -> (

let rec aux = (fun e acc -> (match ((let _167_151 = (unparen e)
in _167_151.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (head, arg, imp) -> begin
(aux head ((((arg), (imp)))::acc))
end
| _68_245 -> begin
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


let matches_level = (fun s _68_260 -> (match (_68_260) with
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
in (FStar_List.mapi (fun i _68_270 -> (match (_68_270) with
| (assoc, tokens) -> begin
(((levels_from_associativity i assoc)), (tokens))
end)) level_associativity_spec))


let assign_levels : associativity_level Prims.list  ->  Prims.string  ->  (Prims.int * Prims.int * Prims.int) = (fun token_associativity_spec s -> (match ((FStar_List.tryFind (matches_level s) level_table)) with
| Some (assoc_levels, _68_275) -> begin
assoc_levels
end
| _68_279 -> begin
(failwith (Prims.strcat "Unrecognized operator " s))
end))


let max : Prims.int  ->  Prims.int  ->  Prims.int = (fun k1 k2 -> if (k1 > k2) then begin
k1
end else begin
k2
end)


let max_level = (fun l -> (

let find_level_and_max = (fun n level -> (match ((FStar_List.tryFind (fun _68_289 -> (match (_68_289) with
| (_68_287, tokens) -> begin
(tokens = (Prims.snd level))
end)) level_table)) with
| Some ((_68_291, l, _68_294), _68_297) -> begin
(max n l)
end
| None -> begin
(let _167_185 = (let _167_184 = (let _167_183 = (FStar_List.map token_to_string (Prims.snd level))
in (FStar_String.concat "," _167_183))
in (FStar_Util.format1 "Undefined associativity level %s" _167_184))
in (failwith _167_185))
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

let _68_317 = (FStar_ST.op_Colon_Equals comment_stack cs)
in (let _167_205 = (let _167_204 = (let _167_203 = (str comment)
in (FStar_Pprint.op_Hat_Hat _167_203 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat acc _167_204))
in (comments_before_pos _167_205 print_pos lookahead_pos)))
end else begin
(let _167_206 = (FStar_Range.range_before_pos crange lookahead_pos)
in ((acc), (_167_206)))
end
end))
in (

let _68_321 = (let _167_209 = (let _167_207 = (FStar_Range.start_of_range tmrange)
in (FStar_Range.end_of_line _167_207))
in (let _167_208 = (FStar_Range.end_of_range tmrange)
in (comments_before_pos FStar_Pprint.empty _167_209 _167_208)))
in (match (_68_321) with
| (comments, has_lookahead) -> begin
(

let printed_e = (printer tm)
in (

let comments = if has_lookahead then begin
(

let pos = (FStar_Range.end_of_range tmrange)
in (let _167_210 = (comments_before_pos comments pos pos)
in (Prims.fst _167_210)))
end else begin
comments
end
in (let _167_211 = (FStar_Pprint.op_Hat_Hat comments printed_e)
in (FStar_Pprint.group _167_211))))
end))))


let rec p_decl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (let _167_322 = (let _167_321 = (FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc)
in (let _167_320 = (let _167_319 = (p_attributes d.FStar_Parser_AST.attrs)
in (let _167_318 = (let _167_317 = (p_qualifiers d.FStar_Parser_AST.quals)
in (let _167_316 = (let _167_315 = (p_rawDecl d)
in (FStar_Pprint.op_Hat_Hat (if (d.FStar_Parser_AST.quals = []) then begin
FStar_Pprint.empty
end else begin
break1
end) _167_315))
in (FStar_Pprint.op_Hat_Hat _167_317 _167_316)))
in (FStar_Pprint.op_Hat_Hat _167_319 _167_318)))
in (FStar_Pprint.op_Hat_Hat _167_321 _167_320)))
in (FStar_Pprint.group _167_322)))
and p_attributes : FStar_Parser_AST.attributes_  ->  FStar_Pprint.document = (fun attrs -> (let _167_326 = (let _167_324 = (str "@")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket _167_324))
in (let _167_325 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline)
in (FStar_Pprint.surround_separate_map (Prims.parse_int "0") (Prims.parse_int "2") FStar_Pprint.empty _167_326 FStar_Pprint.space _167_325 p_atomicTerm attrs))))
and p_fsdoc : FStar_Parser_AST.fsdoc  ->  FStar_Pprint.document = (fun _68_329 -> (match (_68_329) with
| (doc, kwd_args) -> begin
(

let kwd_args_doc = (match (kwd_args) with
| [] -> begin
FStar_Pprint.empty
end
| kwd_args -> begin
(

let process_kwd_arg = (fun _68_335 -> (match (_68_335) with
| (kwd, arg) -> begin
(let _167_334 = (str "@")
in (let _167_333 = (let _167_332 = (str kwd)
in (let _167_331 = (let _167_330 = (str arg)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_330))
in (FStar_Pprint.op_Hat_Hat _167_332 _167_331)))
in (FStar_Pprint.op_Hat_Hat _167_334 _167_333)))
end))
in (let _167_336 = (let _167_335 = (FStar_Pprint.separate_map FStar_Pprint.hardline process_kwd_arg kwd_args)
in (FStar_Pprint.op_Hat_Hat _167_335 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline _167_336)))
end)
in (let _167_344 = (let _167_343 = (let _167_342 = (let _167_341 = (let _167_340 = (str doc)
in (let _167_339 = (let _167_338 = (let _167_337 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _167_337))
in (FStar_Pprint.op_Hat_Hat kwd_args_doc _167_338))
in (FStar_Pprint.op_Hat_Hat _167_340 _167_339)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _167_341))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _167_342))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _167_343))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline _167_344)))
end))
and p_rawDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Open (uid) -> begin
(let _167_348 = (let _167_347 = (str "open")
in (let _167_346 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat _167_347 _167_346)))
in (FStar_Pprint.group _167_348))
end
| FStar_Parser_AST.Include (uid) -> begin
(let _167_351 = (let _167_350 = (str "include")
in (let _167_349 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat _167_350 _167_349)))
in (FStar_Pprint.group _167_351))
end
| FStar_Parser_AST.ModuleAbbrev (uid1, uid2) -> begin
(let _167_358 = (let _167_356 = (str "module")
in (let _167_355 = (let _167_354 = (let _167_353 = (p_uident uid1)
in (let _167_352 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _167_353 _167_352)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_354))
in (FStar_Pprint.op_Hat_Hat _167_356 _167_355)))
in (let _167_357 = (p_quident uid2)
in (op_Hat_Slash_Plus_Hat _167_358 _167_357)))
end
| FStar_Parser_AST.TopLevelModule (uid) -> begin
(let _167_362 = (let _167_361 = (str "module")
in (let _167_360 = (let _167_359 = (p_quident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_359))
in (FStar_Pprint.op_Hat_Hat _167_361 _167_360)))
in (FStar_Pprint.group _167_362))
end
| FStar_Parser_AST.KindAbbrev (_68_349) -> begin
(failwith "Deprecated, please stop throwing your old stuff at me !")
end
| FStar_Parser_AST.Tycon (true, ((FStar_Parser_AST.TyconAbbrev (uid, tpars, None, t), None))::[]) -> begin
(

let effect_prefix_doc = (let _167_365 = (str "effect")
in (let _167_364 = (let _167_363 = (p_uident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_363))
in (FStar_Pprint.op_Hat_Hat _167_365 _167_364)))
in (let _167_368 = (let _167_366 = (p_typars tpars)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") effect_prefix_doc _167_366 FStar_Pprint.equals))
in (let _167_367 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _167_368 _167_367))))
end
| FStar_Parser_AST.Tycon (false, tcdefs) -> begin
(let _167_370 = (str "type")
in (let _167_369 = (str "and")
in (precede_break_separate_map _167_370 _167_369 p_fsdocTypeDeclPairs tcdefs)))
end
| FStar_Parser_AST.TopLevelLet (q, lbs) -> begin
(

let let_doc = (let _167_372 = (str "let")
in (let _167_371 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat _167_372 _167_371)))
in (let _167_373 = (str "and")
in (precede_break_separate_map let_doc _167_373 p_letbinding lbs)))
end
| FStar_Parser_AST.Val (lid, t) -> begin
(let _167_380 = (let _167_378 = (str "val")
in (let _167_377 = (let _167_376 = (let _167_375 = (p_lident lid)
in (let _167_374 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat _167_375 _167_374)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_376))
in (FStar_Pprint.op_Hat_Hat _167_378 _167_377)))
in (let _167_379 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _167_380 _167_379)))
end
| FStar_Parser_AST.Assume (id, t) -> begin
(

let decl_keyword = if (let _167_381 = (FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_All.pipe_right _167_381 FStar_Util.is_upper)) then begin
FStar_Pprint.empty
end else begin
(let _167_382 = (str "val")
in (FStar_Pprint.op_Hat_Hat _167_382 FStar_Pprint.space))
end
in (let _167_387 = (let _167_385 = (let _167_384 = (p_ident id)
in (let _167_383 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat _167_384 _167_383)))
in (FStar_Pprint.op_Hat_Hat decl_keyword _167_385))
in (let _167_386 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _167_387 _167_386))))
end
| FStar_Parser_AST.Exception (uid, t_opt) -> begin
(let _167_395 = (str "exception")
in (let _167_394 = (let _167_393 = (let _167_392 = (p_uident uid)
in (let _167_391 = (FStar_Pprint.optional (fun t -> (let _167_390 = (str "of")
in (let _167_389 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _167_390 _167_389)))) t_opt)
in (FStar_Pprint.op_Hat_Hat _167_392 _167_391)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_393))
in (FStar_Pprint.op_Hat_Hat _167_395 _167_394)))
end
| FStar_Parser_AST.NewEffect (ne) -> begin
(let _167_398 = (str "new_effect")
in (let _167_397 = (let _167_396 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_396))
in (FStar_Pprint.op_Hat_Hat _167_398 _167_397)))
end
| FStar_Parser_AST.SubEffect (se) -> begin
(let _167_401 = (str "sub_effect")
in (let _167_400 = (let _167_399 = (p_subEffect se)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_399))
in (FStar_Pprint.op_Hat_Hat _167_401 _167_400)))
end
| FStar_Parser_AST.NewEffectForFree (ne) -> begin
(let _167_404 = (str "new_effect_for_free")
in (let _167_403 = (let _167_402 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_402))
in (FStar_Pprint.op_Hat_Hat _167_404 _167_403)))
end
| FStar_Parser_AST.Pragma (p) -> begin
(p_pragma p)
end
| FStar_Parser_AST.Fsdoc (doc) -> begin
(let _167_405 = (p_fsdoc doc)
in (FStar_Pprint.op_Hat_Hat _167_405 FStar_Pprint.hardline))
end
| FStar_Parser_AST.Main (_68_398) -> begin
(failwith "*Main declaration* : Is that really still in use ??")
end
| FStar_Parser_AST.Tycon (true, _68_402) -> begin
(failwith "Effect abbreviation is expected to be defined by an abbreviation")
end))
and p_pragma : FStar_Parser_AST.pragma  ->  FStar_Pprint.document = (fun _68_4 -> (match (_68_4) with
| FStar_Parser_AST.SetOptions (s) -> begin
(let _167_410 = (str "#set-options")
in (let _167_409 = (let _167_408 = (let _167_407 = (str s)
in (FStar_Pprint.dquotes _167_407))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_408))
in (FStar_Pprint.op_Hat_Hat _167_410 _167_409)))
end
| FStar_Parser_AST.ResetOptions (s_opt) -> begin
(let _167_415 = (str "#reset-options")
in (let _167_414 = (FStar_Pprint.optional (fun s -> (let _167_413 = (let _167_412 = (str s)
in (FStar_Pprint.dquotes _167_412))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_413))) s_opt)
in (FStar_Pprint.op_Hat_Hat _167_415 _167_414)))
end))
and p_typars : FStar_Parser_AST.binder Prims.list  ->  FStar_Pprint.document = (fun bs -> (p_binders true bs))
and p_fsdocTypeDeclPairs : (FStar_Parser_AST.tycon * FStar_Parser_AST.fsdoc Prims.option)  ->  FStar_Pprint.document = (fun _68_414 -> (match (_68_414) with
| (typedecl, fsdoc_opt) -> begin
(let _167_419 = (FStar_Pprint.optional p_fsdoc fsdoc_opt)
in (let _167_418 = (p_typeDecl typedecl)
in (FStar_Pprint.op_Hat_Hat _167_419 _167_418)))
end))
and p_typeDecl : FStar_Parser_AST.tycon  ->  FStar_Pprint.document = (fun _68_5 -> (match (_68_5) with
| FStar_Parser_AST.TyconAbstract (lid, bs, typ_opt) -> begin
(

let empty' = (fun _68_421 -> (match (()) with
| () -> begin
FStar_Pprint.empty
end))
in (p_typeDeclPrefix lid bs typ_opt empty'))
end
| FStar_Parser_AST.TyconAbbrev (lid, bs, typ_opt, t) -> begin
(

let f = (fun _68_430 -> (match (()) with
| () -> begin
(let _167_425 = (p_typ t)
in (prefix2 FStar_Pprint.equals _167_425))
end))
in (p_typeDeclPrefix lid bs typ_opt f))
end
| FStar_Parser_AST.TyconRecord (lid, bs, typ_opt, record_field_decls) -> begin
(

let p_recordFieldAndComments = (fun _68_441 -> (match (_68_441) with
| (lid, t, doc_opt) -> begin
(let _167_428 = (FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range)
in (with_comment p_recordFieldDecl ((lid), (t), (doc_opt)) _167_428))
end))
in (

let p_fields = (fun _68_443 -> (match (()) with
| () -> begin
(let _167_434 = (let _167_433 = (let _167_432 = (let _167_431 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (FStar_Pprint.separate_map _167_431 p_recordFieldAndComments record_field_decls))
in (braces_with_nesting _167_432))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_433))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.equals _167_434))
end))
in (p_typeDeclPrefix lid bs typ_opt p_fields)))
end
| FStar_Parser_AST.TyconVariant (lid, bs, typ_opt, ct_decls) -> begin
(

let p_constructorBranchAndComments = (fun _68_455 -> (match (_68_455) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let range = (let _167_439 = (let _167_438 = (FStar_Util.map_opt t_opt (fun t -> t.FStar_Parser_AST.range))
in (FStar_Util.dflt uid.FStar_Ident.idRange _167_438))
in (FStar_Range.extend_to_end_of_line _167_439))
in (

let p_constructorBranch = (fun decl -> (let _167_444 = (let _167_443 = (let _167_442 = (p_constructorDecl decl)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_442))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar _167_443))
in (FStar_Pprint.group _167_444)))
in (with_comment p_constructorBranch ((uid), (t_opt), (doc_opt), (use_of)) range)))
end))
in (

let datacon_doc = (fun _68_461 -> (match (()) with
| () -> begin
(let _167_447 = (FStar_Pprint.separate_map break1 p_constructorBranchAndComments ct_decls)
in (FStar_Pprint.group _167_447))
end))
in (p_typeDeclPrefix lid bs typ_opt (fun _68_462 -> (match (()) with
| () -> begin
(let _167_449 = (datacon_doc ())
in (prefix2 FStar_Pprint.equals _167_449))
end)))))
end))
and p_typeDeclPrefix : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.knd Prims.option  ->  (Prims.unit  ->  FStar_Pprint.document)  ->  FStar_Pprint.document = (fun lid bs typ_opt cont -> if ((bs = []) && (typ_opt = None)) then begin
(let _167_459 = (p_ident lid)
in (let _167_458 = (let _167_457 = (cont ())
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_457))
in (FStar_Pprint.op_Hat_Hat _167_459 _167_458)))
end else begin
(

let binders_doc = (let _167_465 = (p_typars bs)
in (let _167_464 = (FStar_Pprint.optional (fun t -> (let _167_463 = (let _167_462 = (let _167_461 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_461))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _167_462))
in (FStar_Pprint.op_Hat_Hat break1 _167_463))) typ_opt)
in (FStar_Pprint.op_Hat_Hat _167_465 _167_464)))
in (let _167_467 = (p_ident lid)
in (let _167_466 = (cont ())
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _167_467 binders_doc _167_466))))
end)
and p_recordFieldDecl : (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc Prims.option)  ->  FStar_Pprint.document = (fun _68_472 -> (match (_68_472) with
| (lid, t, doc_opt) -> begin
(let _167_474 = (let _167_473 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (let _167_472 = (let _167_471 = (p_lident lid)
in (let _167_470 = (let _167_469 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _167_469))
in (FStar_Pprint.op_Hat_Hat _167_471 _167_470)))
in (FStar_Pprint.op_Hat_Hat _167_473 _167_472)))
in (FStar_Pprint.group _167_474))
end))
and p_constructorDecl : (FStar_Ident.ident * FStar_Parser_AST.term Prims.option * FStar_Parser_AST.fsdoc Prims.option * Prims.bool)  ->  FStar_Pprint.document = (fun _68_477 -> (match (_68_477) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let sep = if use_of then begin
(str "of")
end else begin
FStar_Pprint.colon
end
in (

let uid_doc = (p_uident uid)
in (let _167_481 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (let _167_480 = (default_or_map uid_doc (fun t -> (let _167_479 = (let _167_477 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep)
in (FStar_Pprint.op_Hat_Hat uid_doc _167_477))
in (let _167_478 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _167_479 _167_478)))) t_opt)
in (FStar_Pprint.op_Hat_Hat _167_481 _167_480)))))
end))
and p_letbinding : (FStar_Parser_AST.pattern * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun _68_483 -> (match (_68_483) with
| (pat, e) -> begin
(

let pat_doc = (

let _68_492 = (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, t) -> begin
(let _167_487 = (let _167_486 = (let _167_485 = (let _167_484 = (let _167_483 = (p_tmArrow p_tmNoEq t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_483))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _167_484))
in (FStar_Pprint.group _167_485))
in (FStar_Pprint.op_Hat_Hat break1 _167_486))
in ((pat), (_167_487)))
end
| _68_489 -> begin
((pat), (FStar_Pprint.empty))
end)
in (match (_68_492) with
| (pat, ascr_doc) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _68_497); FStar_Parser_AST.prange = _68_494}, pats) -> begin
(let _167_490 = (p_lident x)
in (let _167_489 = (let _167_488 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Hat _167_488 ascr_doc))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _167_490 _167_489 FStar_Pprint.equals)))
end
| _68_505 -> begin
(let _167_493 = (let _167_492 = (p_tuplePattern pat)
in (let _167_491 = (FStar_Pprint.op_Hat_Slash_Hat ascr_doc FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _167_492 _167_491)))
in (FStar_Pprint.group _167_493))
end)
end))
in (let _167_494 = (p_term e)
in (prefix2 pat_doc _167_494)))
end))
and p_newEffect : FStar_Parser_AST.effect_decl  ->  FStar_Pprint.document = (fun _68_6 -> (match (_68_6) with
| FStar_Parser_AST.RedefineEffect (lid, bs, t) -> begin
(p_effectRedefinition lid bs t)
end
| FStar_Parser_AST.DefineEffect (lid, bs, t, eff_decls, action_decls) -> begin
(p_effectDefinition lid bs t eff_decls action_decls)
end))
and p_effectRedefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun uid bs t -> (let _167_502 = (p_uident uid)
in (let _167_501 = (p_binders true bs)
in (let _167_500 = (let _167_499 = (p_simpleTerm t)
in (prefix2 FStar_Pprint.equals _167_499))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _167_502 _167_501 _167_500)))))
and p_effectDefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun uid bs t eff_decls action_decls -> (let _167_519 = (let _167_518 = (let _167_512 = (let _167_511 = (p_uident uid)
in (let _167_510 = (p_binders true bs)
in (let _167_509 = (let _167_508 = (p_typ t)
in (prefix2 FStar_Pprint.colon _167_508))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _167_511 _167_510 _167_509))))
in (FStar_Pprint.group _167_512))
in (let _167_517 = (let _167_516 = (let _167_514 = (str "with")
in (let _167_513 = (separate_break_map FStar_Pprint.semi p_effectDecl eff_decls)
in (prefix2 _167_514 _167_513)))
in (let _167_515 = (p_actionDecls action_decls)
in (FStar_Pprint.op_Hat_Hat _167_516 _167_515)))
in (FStar_Pprint.op_Hat_Slash_Hat _167_518 _167_517)))
in (braces_with_nesting _167_519)))
and p_actionDecls : FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun _68_7 -> (match (_68_7) with
| [] -> begin
FStar_Pprint.empty
end
| l -> begin
(let _167_523 = (let _167_522 = (str "and actions")
in (let _167_521 = (separate_break_map FStar_Pprint.semi p_effectDecl l)
in (prefix2 _167_522 _167_521)))
in (FStar_Pprint.op_Hat_Hat break1 _167_523))
end))
and p_effectDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (false, ((FStar_Parser_AST.TyconAbbrev (lid, [], None, e), None))::[]) -> begin
(let _167_528 = (let _167_526 = (p_lident lid)
in (let _167_525 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _167_526 _167_525)))
in (let _167_527 = (p_simpleTerm e)
in (prefix2 _167_528 _167_527)))
end
| _68_545 -> begin
(let _167_530 = (let _167_529 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "Not a declaration of an effect member... or at least I hope so : %s" _167_529))
in (failwith _167_530))
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

let p_lift = (fun _68_559 -> (match (_68_559) with
| (kwd, t) -> begin
(let _167_537 = (let _167_535 = (str kwd)
in (let _167_534 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _167_535 _167_534)))
in (let _167_536 = (p_simpleTerm t)
in (prefix2 _167_537 _167_536)))
end))
in (separate_break_map FStar_Pprint.semi p_lift lifts)))
in (let _167_545 = (let _167_542 = (let _167_540 = (p_quident lift.FStar_Parser_AST.msource)
in (let _167_539 = (let _167_538 = (str "~>")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_538))
in (FStar_Pprint.op_Hat_Hat _167_540 _167_539)))
in (let _167_541 = (p_quident lift.FStar_Parser_AST.mdest)
in (prefix2 _167_542 _167_541)))
in (let _167_544 = (let _167_543 = (braces_with_nesting lift_op_doc)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_543))
in (FStar_Pprint.op_Hat_Hat _167_545 _167_544)))))
and p_qualifier : FStar_Parser_AST.qualifier  ->  FStar_Pprint.document = (fun _68_8 -> (match (_68_8) with
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
and p_qualifiers : FStar_Parser_AST.qualifiers  ->  FStar_Pprint.document = (fun qs -> (let _167_548 = (FStar_Pprint.separate_map break1 p_qualifier qs)
in (FStar_Pprint.group _167_548)))
and p_letqualifier : FStar_Parser_AST.let_qualifier  ->  FStar_Pprint.document = (fun _68_9 -> (match (_68_9) with
| FStar_Parser_AST.Rec -> begin
(let _167_550 = (str "rec")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_550))
end
| FStar_Parser_AST.Mutable -> begin
(let _167_551 = (str "mutable")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_551))
end
| FStar_Parser_AST.NoLetQualifier -> begin
FStar_Pprint.empty
end))
and p_aqual : FStar_Parser_AST.arg_qualifier  ->  FStar_Pprint.document = (fun _68_10 -> (match (_68_10) with
| FStar_Parser_AST.Implicit -> begin
(str "#")
end
| FStar_Parser_AST.Equality -> begin
(str "$")
end))
and p_disjunctivePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr (pats) -> begin
(let _167_556 = (let _167_555 = (let _167_554 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space)
in (FStar_Pprint.op_Hat_Hat break1 _167_554))
in (FStar_Pprint.separate_map _167_555 p_tuplePattern pats))
in (FStar_Pprint.group _167_556))
end
| _68_593 -> begin
(p_tuplePattern p)
end))
and p_tuplePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTuple (pats, false) -> begin
(let _167_559 = (let _167_558 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map _167_558 p_constructorPattern pats))
in (FStar_Pprint.group _167_559))
end
| _68_600 -> begin
(p_constructorPattern p)
end))
and p_constructorPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (maybe_cons_lid); FStar_Parser_AST.prange = _68_603}, (hd)::(tl)::[]) when (FStar_Ident.lid_equals maybe_cons_lid FStar_Syntax_Const.cons_lid) -> begin
(let _167_563 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon)
in (let _167_562 = (p_constructorPattern hd)
in (let _167_561 = (p_constructorPattern tl)
in (infix0 _167_563 _167_562 _167_561))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (uid); FStar_Parser_AST.prange = _68_613}, pats) -> begin
(let _167_565 = (p_quident uid)
in (let _167_564 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (prefix2 _167_565 _167_564)))
end
| _68_621 -> begin
(p_atomicPattern p)
end))
and p_atomicPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, t) -> begin
(match ((let _167_568 = (let _167_567 = (unparen t)
in _167_567.FStar_Parser_AST.tm)
in ((pat.FStar_Parser_AST.pat), (_167_568)))) with
| (FStar_Parser_AST.PatVar (lid, aqual), FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t); FStar_Parser_AST.brange = _68_636; FStar_Parser_AST.blevel = _68_634; FStar_Parser_AST.aqual = _68_632}, phi)) when (lid.FStar_Ident.idText = lid'.FStar_Ident.idText) -> begin
(let _167_570 = (let _167_569 = (p_ident lid)
in (p_refinement aqual _167_569 t phi))
in (soft_parens_with_nesting _167_570))
end
| (FStar_Parser_AST.PatWild, FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t); FStar_Parser_AST.brange = _68_652; FStar_Parser_AST.blevel = _68_650; FStar_Parser_AST.aqual = _68_648}, phi)) -> begin
(let _167_571 = (p_refinement None FStar_Pprint.underscore t phi)
in (soft_parens_with_nesting _167_571))
end
| _68_661 -> begin
(let _167_577 = (let _167_576 = (p_tuplePattern pat)
in (let _167_575 = (let _167_574 = (FStar_Pprint.break_ (Prims.parse_int "0"))
in (let _167_573 = (let _167_572 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _167_572))
in (FStar_Pprint.op_Hat_Hat _167_574 _167_573)))
in (FStar_Pprint.op_Hat_Hat _167_576 _167_575)))
in (soft_parens_with_nesting _167_577))
end)
end
| FStar_Parser_AST.PatList (pats) -> begin
(let _167_578 = (separate_break_map FStar_Pprint.semi p_tuplePattern pats)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket _167_578 FStar_Pprint.rbracket))
end
| FStar_Parser_AST.PatRecord (pats) -> begin
(

let p_recordFieldPat = (fun _68_669 -> (match (_68_669) with
| (lid, pat) -> begin
(let _167_582 = (p_qlident lid)
in (let _167_581 = (p_tuplePattern pat)
in (infix2 FStar_Pprint.equals _167_582 _167_581)))
end))
in (let _167_583 = (separate_break_map FStar_Pprint.semi p_recordFieldPat pats)
in (soft_braces_with_nesting _167_583)))
end
| FStar_Parser_AST.PatTuple (pats, true) -> begin
(let _167_586 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (let _167_585 = (separate_break_map FStar_Pprint.comma p_constructorPattern pats)
in (let _167_584 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _167_586 _167_585 _167_584))))
end
| FStar_Parser_AST.PatTvar (tv, arg_qualifier_opt) -> begin
(

let _68_678 = ()
in (p_tvar tv))
end
| FStar_Parser_AST.PatOp (op) -> begin
(let _167_590 = (let _167_589 = (let _167_588 = (str op)
in (let _167_587 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat _167_588 _167_587)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_589))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _167_590))
end
| FStar_Parser_AST.PatWild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.PatConst (c) -> begin
(p_constant c)
end
| FStar_Parser_AST.PatVar (lid, aqual) -> begin
(let _167_592 = (FStar_Pprint.optional p_aqual aqual)
in (let _167_591 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat _167_592 _167_591)))
end
| FStar_Parser_AST.PatName (uid) -> begin
(p_quident uid)
end
| FStar_Parser_AST.PatOr (_68_692) -> begin
(failwith "Inner or pattern !")
end
| (FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (_); FStar_Parser_AST.prange = _}, _)) | (FStar_Parser_AST.PatTuple (_, false)) -> begin
(let _167_593 = (p_tuplePattern p)
in (soft_parens_with_nesting _167_593))
end
| _68_710 -> begin
(let _167_595 = (let _167_594 = (FStar_Parser_AST.pat_to_string p)
in (FStar_Util.format1 "Invalid pattern %s" _167_594))
in (failwith _167_595))
end))
and p_binder : Prims.bool  ->  FStar_Parser_AST.binder  ->  FStar_Pprint.document = (fun is_atomic b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (lid) -> begin
(let _167_599 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (let _167_598 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat _167_599 _167_598)))
end
| FStar_Parser_AST.TVariable (lid) -> begin
(p_lident lid)
end
| FStar_Parser_AST.Annotated (lid, t) -> begin
(

let doc = (match ((let _167_600 = (unparen t)
in _167_600.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t); FStar_Parser_AST.brange = _68_726; FStar_Parser_AST.blevel = _68_724; FStar_Parser_AST.aqual = _68_722}, phi) when (lid.FStar_Ident.idText = lid'.FStar_Ident.idText) -> begin
(let _167_601 = (p_ident lid)
in (p_refinement b.FStar_Parser_AST.aqual _167_601 t phi))
end
| _68_736 -> begin
(let _167_608 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (let _167_607 = (let _167_606 = (p_lident lid)
in (let _167_605 = (let _167_604 = (let _167_603 = (FStar_Pprint.break_ (Prims.parse_int "0"))
in (let _167_602 = (p_tmFormula t)
in (FStar_Pprint.op_Hat_Hat _167_603 _167_602)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _167_604))
in (FStar_Pprint.op_Hat_Hat _167_606 _167_605)))
in (FStar_Pprint.op_Hat_Hat _167_608 _167_607)))
end)
in if is_atomic then begin
(let _167_610 = (let _167_609 = (FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _167_609))
in (FStar_Pprint.group _167_610))
end else begin
(FStar_Pprint.group doc)
end)
end
| FStar_Parser_AST.TAnnotated (_68_739) -> begin
(failwith "Is this still used ?")
end
| FStar_Parser_AST.NoName (t) -> begin
(match ((let _167_611 = (unparen t)
in _167_611.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t); FStar_Parser_AST.brange = _68_748; FStar_Parser_AST.blevel = _68_746; FStar_Parser_AST.aqual = _68_744}, phi) -> begin
if is_atomic then begin
(let _167_614 = (let _167_613 = (let _167_612 = (p_refinement b.FStar_Parser_AST.aqual FStar_Pprint.underscore t phi)
in (FStar_Pprint.op_Hat_Hat _167_612 FStar_Pprint.rparen))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _167_613))
in (FStar_Pprint.group _167_614))
end else begin
(let _167_615 = (p_refinement b.FStar_Parser_AST.aqual FStar_Pprint.underscore t phi)
in (FStar_Pprint.group _167_615))
end
end
| _68_756 -> begin
if is_atomic then begin
(p_atomicTerm t)
end else begin
(p_appTerm t)
end
end)
end))
and p_refinement : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Pprint.document  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun aqual_opt binder t phi -> (let _167_626 = (FStar_Pprint.optional p_aqual aqual_opt)
in (let _167_625 = (let _167_624 = (let _167_623 = (let _167_622 = (p_appTerm t)
in (let _167_621 = (let _167_620 = (p_noSeqTerm phi)
in (soft_braces_with_nesting _167_620))
in (FStar_Pprint.op_Hat_Hat _167_622 _167_621)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _167_623))
in (FStar_Pprint.op_Hat_Hat binder _167_624))
in (FStar_Pprint.op_Hat_Hat _167_626 _167_625))))
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
and p_term : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _167_637 = (unparen e)
in _167_637.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Seq (e1, e2) -> begin
(let _167_641 = (let _167_639 = (let _167_638 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat _167_638 FStar_Pprint.semi))
in (FStar_Pprint.group _167_639))
in (let _167_640 = (p_term e2)
in (FStar_Pprint.op_Hat_Slash_Hat _167_641 _167_640)))
end
| _68_776 -> begin
(let _167_642 = (p_noSeqTerm e)
in (FStar_Pprint.group _167_642))
end))
and p_noSeqTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_noSeqTerm' e e.FStar_Parser_AST.range))
and p_noSeqTerm' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _167_645 = (unparen e)
in _167_645.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Ascribed (e, t) -> begin
(let _167_650 = (let _167_649 = (p_tmIff e)
in (let _167_648 = (let _167_647 = (let _167_646 = (p_typ t)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon _167_646))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.langle _167_647))
in (FStar_Pprint.op_Hat_Slash_Hat _167_649 _167_648)))
in (FStar_Pprint.group _167_650))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::(e3)::[]) when (op = ".()<-") -> begin
(let _167_661 = (let _167_660 = (let _167_657 = (let _167_656 = (p_atomicTermNotQUident e1)
in (let _167_655 = (let _167_654 = (let _167_653 = (let _167_651 = (p_term e2)
in (soft_parens_with_nesting _167_651))
in (let _167_652 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat _167_653 _167_652)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _167_654))
in (FStar_Pprint.op_Hat_Hat _167_656 _167_655)))
in (FStar_Pprint.group _167_657))
in (let _167_659 = (let _167_658 = (p_noSeqTerm e3)
in (jump2 _167_658))
in (FStar_Pprint.op_Hat_Hat _167_660 _167_659)))
in (FStar_Pprint.group _167_661))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::(e3)::[]) when (op = ".[]<-") -> begin
(let _167_672 = (let _167_671 = (let _167_668 = (let _167_667 = (p_atomicTermNotQUident e1)
in (let _167_666 = (let _167_665 = (let _167_664 = (let _167_662 = (p_term e2)
in (soft_brackets_with_nesting _167_662))
in (let _167_663 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat _167_664 _167_663)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _167_665))
in (FStar_Pprint.op_Hat_Hat _167_667 _167_666)))
in (FStar_Pprint.group _167_668))
in (let _167_670 = (let _167_669 = (p_noSeqTerm e3)
in (jump2 _167_669))
in (FStar_Pprint.op_Hat_Hat _167_671 _167_670)))
in (FStar_Pprint.group _167_672))
end
| FStar_Parser_AST.Requires (e, wtf) -> begin
(

let _68_801 = ()
in (let _167_675 = (let _167_674 = (str "requires")
in (let _167_673 = (p_typ e)
in (FStar_Pprint.op_Hat_Slash_Hat _167_674 _167_673)))
in (FStar_Pprint.group _167_675)))
end
| FStar_Parser_AST.Ensures (e, wtf) -> begin
(

let _68_807 = ()
in (let _167_678 = (let _167_677 = (str "ensures")
in (let _167_676 = (p_typ e)
in (FStar_Pprint.op_Hat_Slash_Hat _167_677 _167_676)))
in (FStar_Pprint.group _167_678)))
end
| FStar_Parser_AST.Attributes (es) -> begin
(let _167_681 = (let _167_680 = (str "attributes")
in (let _167_679 = (FStar_Pprint.separate_map break1 p_atomicTerm es)
in (FStar_Pprint.op_Hat_Slash_Hat _167_680 _167_679)))
in (FStar_Pprint.group _167_681))
end
| FStar_Parser_AST.If (e1, e2, e3) -> begin
if (is_unit e3) then begin
(let _167_688 = (let _167_687 = (let _167_683 = (str "if")
in (let _167_682 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat _167_683 _167_682)))
in (let _167_686 = (let _167_685 = (str "then")
in (let _167_684 = (p_noSeqTerm e2)
in (op_Hat_Slash_Plus_Hat _167_685 _167_684)))
in (FStar_Pprint.op_Hat_Slash_Hat _167_687 _167_686)))
in (FStar_Pprint.group _167_688))
end else begin
(

let e2_doc = (match ((let _167_689 = (unparen e2)
in _167_689.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.If (_68_817, _68_819, e3) when (is_unit e3) -> begin
(let _167_690 = (p_noSeqTerm e2)
in (soft_parens_with_nesting _167_690))
end
| _68_824 -> begin
(p_noSeqTerm e2)
end)
in (let _167_700 = (let _167_699 = (let _167_692 = (str "if")
in (let _167_691 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat _167_692 _167_691)))
in (let _167_698 = (let _167_697 = (let _167_693 = (str "then")
in (op_Hat_Slash_Plus_Hat _167_693 e2_doc))
in (let _167_696 = (let _167_695 = (str "else")
in (let _167_694 = (p_noSeqTerm e3)
in (op_Hat_Slash_Plus_Hat _167_695 _167_694)))
in (FStar_Pprint.op_Hat_Slash_Hat _167_697 _167_696)))
in (FStar_Pprint.op_Hat_Slash_Hat _167_699 _167_698)))
in (FStar_Pprint.group _167_700)))
end
end
| FStar_Parser_AST.TryWith (e, branches) -> begin
(let _167_707 = (let _167_706 = (let _167_702 = (str "try")
in (let _167_701 = (p_noSeqTerm e)
in (prefix2 _167_702 _167_701)))
in (let _167_705 = (let _167_704 = (str "with")
in (let _167_703 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat _167_704 _167_703)))
in (FStar_Pprint.op_Hat_Slash_Hat _167_706 _167_705)))
in (FStar_Pprint.group _167_707))
end
| FStar_Parser_AST.Match (e, branches) -> begin
(let _167_713 = (let _167_712 = (let _167_710 = (str "match")
in (let _167_709 = (p_noSeqTerm e)
in (let _167_708 = (str "with")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _167_710 _167_709 _167_708))))
in (let _167_711 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat _167_712 _167_711)))
in (FStar_Pprint.group _167_713))
end
| FStar_Parser_AST.LetOpen (uid, e) -> begin
(let _167_719 = (let _167_718 = (let _167_716 = (str "let open")
in (let _167_715 = (p_quident uid)
in (let _167_714 = (str "in")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _167_716 _167_715 _167_714))))
in (let _167_717 = (p_term e)
in (FStar_Pprint.op_Hat_Slash_Hat _167_718 _167_717)))
in (FStar_Pprint.group _167_719))
end
| FStar_Parser_AST.Let (q, lbs, e) -> begin
(

let let_doc = (let _167_721 = (str "let")
in (let _167_720 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat _167_721 _167_720)))
in (let _167_727 = (let _167_725 = (let _167_724 = (let _167_722 = (str "and")
in (precede_break_separate_map let_doc _167_722 p_letbinding lbs))
in (let _167_723 = (str "in")
in (FStar_Pprint.op_Hat_Slash_Hat _167_724 _167_723)))
in (FStar_Pprint.group _167_725))
in (let _167_726 = (p_term e)
in (FStar_Pprint.op_Hat_Slash_Hat _167_727 _167_726))))
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, typ_opt); FStar_Parser_AST.prange = _68_845})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, branches); FStar_Parser_AST.range = _68_855; FStar_Parser_AST.level = _68_853}) when (matches_var maybe_x x) -> begin
(let _167_730 = (let _167_729 = (str "function")
in (let _167_728 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat _167_729 _167_728)))
in (FStar_Pprint.group _167_730))
end
| FStar_Parser_AST.Assign (id, e) -> begin
(let _167_734 = (let _167_733 = (p_lident id)
in (let _167_732 = (let _167_731 = (p_noSeqTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow _167_731))
in (FStar_Pprint.op_Hat_Slash_Hat _167_733 _167_732)))
in (FStar_Pprint.group _167_734))
end
| _68_868 -> begin
(p_typ e)
end))
and p_typ : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_typ' e e.FStar_Parser_AST.range))
and p_typ' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _167_737 = (unparen e)
in _167_737.FStar_Parser_AST.tm)) with
| (FStar_Parser_AST.QForall (bs, trigger, e1)) | (FStar_Parser_AST.QExists (bs, trigger, e1)) -> begin
(let _167_744 = (let _167_740 = (let _167_738 = (p_quantifier e)
in (FStar_Pprint.op_Hat_Hat _167_738 FStar_Pprint.space))
in (let _167_739 = (p_binders true bs)
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") _167_740 _167_739 FStar_Pprint.dot)))
in (let _167_743 = (let _167_742 = (p_trigger trigger)
in (let _167_741 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat _167_742 _167_741)))
in (prefix2 _167_744 _167_743)))
end
| _68_879 -> begin
(p_simpleTerm e)
end))
and p_quantifier : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _167_746 = (unparen e)
in _167_746.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.QForall (_68_882) -> begin
(str "forall")
end
| FStar_Parser_AST.QExists (_68_885) -> begin
(str "exists")
end
| _68_888 -> begin
(failwith "Imposible : p_quantifier called on a non-quantifier term")
end))
and p_trigger : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun _68_11 -> (match (_68_11) with
| [] -> begin
FStar_Pprint.empty
end
| pats -> begin
(let _167_754 = (let _167_753 = (let _167_752 = (str "pattern")
in (let _167_751 = (let _167_750 = (let _167_748 = (p_disjunctivePats pats)
in (jump2 _167_748))
in (let _167_749 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1)
in (FStar_Pprint.op_Hat_Slash_Hat _167_750 _167_749)))
in (FStar_Pprint.op_Hat_Slash_Hat _167_752 _167_751)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _167_753))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace _167_754))
end))
and p_disjunctivePats : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun pats -> (let _167_756 = (str "\\/")
in (FStar_Pprint.separate_map _167_756 p_conjunctivePats pats)))
and p_conjunctivePats : FStar_Parser_AST.term Prims.list  ->  FStar_Pprint.document = (fun pats -> (let _167_758 = (FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats)
in (FStar_Pprint.group _167_758)))
and p_simpleTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _167_760 = (unparen e)
in _167_760.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Abs (pats, e) -> begin
(let _167_765 = (let _167_763 = (str "fun")
in (let _167_762 = (let _167_761 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Slash_Hat _167_761 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat _167_763 _167_762)))
in (let _167_764 = (p_term e)
in (op_Hat_Slash_Plus_Hat _167_765 _167_764)))
end
| _68_900 -> begin
(p_tmIff e)
end))
and p_maybeFocusArrow : Prims.bool  ->  FStar_Pprint.document = (fun b -> if b then begin
(str "~>")
end else begin
FStar_Pprint.rarrow
end)
and p_patternBranch : FStar_Parser_AST.branch  ->  FStar_Pprint.document = (fun _68_905 -> (match (_68_905) with
| (pat, when_opt, e) -> begin
(

let maybe_paren = (match ((let _167_770 = (unparen e)
in _167_770.FStar_Parser_AST.tm)) with
| (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) -> begin
soft_begin_end_with_nesting
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _68_916); FStar_Parser_AST.prange = _68_913})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, _68_927); FStar_Parser_AST.range = _68_924; FStar_Parser_AST.level = _68_922}) when (matches_var maybe_x x) -> begin
soft_begin_end_with_nesting
end
| _68_934 -> begin
(fun x -> x)
end)
in (let _167_781 = (let _167_780 = (let _167_777 = (let _167_776 = (let _167_775 = (let _167_774 = (p_disjunctivePattern pat)
in (let _167_773 = (let _167_772 = (p_maybeWhen when_opt)
in (FStar_Pprint.op_Hat_Hat _167_772 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat _167_774 _167_773)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_775))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar _167_776))
in (FStar_Pprint.group _167_777))
in (let _167_779 = (let _167_778 = (p_term e)
in (maybe_paren _167_778))
in (op_Hat_Slash_Plus_Hat _167_780 _167_779)))
in (FStar_Pprint.group _167_781)))
end))
and p_maybeWhen : FStar_Parser_AST.term Prims.option  ->  FStar_Pprint.document = (fun _68_12 -> (match (_68_12) with
| None -> begin
FStar_Pprint.empty
end
| Some (e) -> begin
(let _167_785 = (str "when")
in (let _167_784 = (let _167_783 = (p_tmFormula e)
in (FStar_Pprint.op_Hat_Hat _167_783 FStar_Pprint.space))
in (op_Hat_Slash_Plus_Hat _167_785 _167_784)))
end))
and p_tmIff : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _167_787 = (unparen e)
in _167_787.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Op ("<==>", (e1)::(e2)::[]) -> begin
(let _167_790 = (str "<==>")
in (let _167_789 = (p_tmImplies e1)
in (let _167_788 = (p_tmIff e2)
in (infix0 _167_790 _167_789 _167_788))))
end
| _68_949 -> begin
(p_tmImplies e)
end))
and p_tmImplies : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _167_792 = (unparen e)
in _167_792.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Op ("==>", (e1)::(e2)::[]) -> begin
(let _167_795 = (str "==>")
in (let _167_794 = (p_tmArrow p_tmFormula e1)
in (let _167_793 = (p_tmImplies e2)
in (infix0 _167_795 _167_794 _167_793))))
end
| _68_958 -> begin
(p_tmArrow p_tmFormula e)
end))
and p_tmArrow : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_Tm e -> (match ((let _167_801 = (unparen e)
in _167_801.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Product (bs, tgt) -> begin
(let _167_808 = (let _167_807 = (FStar_Pprint.concat_map (fun b -> (let _167_805 = (p_binder false b)
in (let _167_804 = (let _167_803 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_803))
in (FStar_Pprint.op_Hat_Hat _167_805 _167_804)))) bs)
in (let _167_806 = (p_tmArrow p_Tm tgt)
in (FStar_Pprint.op_Hat_Hat _167_807 _167_806)))
in (FStar_Pprint.group _167_808))
end
| _68_967 -> begin
(p_Tm e)
end))
and p_tmFormula : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _167_810 = (unparen e)
in _167_810.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Op ("\\/", (e1)::(e2)::[]) -> begin
(let _167_813 = (str "\\/")
in (let _167_812 = (p_tmFormula e1)
in (let _167_811 = (p_tmConjunction e2)
in (infix0 _167_813 _167_812 _167_811))))
end
| _68_976 -> begin
(p_tmConjunction e)
end))
and p_tmConjunction : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _167_815 = (unparen e)
in _167_815.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Op ("/\\", (e1)::(e2)::[]) -> begin
(let _167_818 = (str "/\\")
in (let _167_817 = (p_tmConjunction e1)
in (let _167_816 = (p_tmTuple e2)
in (infix0 _167_818 _167_817 _167_816))))
end
| _68_985 -> begin
(p_tmTuple e)
end))
and p_tmTuple : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _167_820 = (unparen e)
in _167_820.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Construct (lid, args) when (is_tuple_constructor lid) -> begin
(let _167_822 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map _167_822 (fun _68_994 -> (match (_68_994) with
| (e, _68_993) -> begin
(p_tmEq e)
end)) args))
end
| _68_996 -> begin
(p_tmEq e)
end))
and paren_if : Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun curr mine doc -> if (mine <= curr) then begin
doc
end else begin
(let _167_827 = (let _167_826 = (FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _167_826))
in (FStar_Pprint.group _167_827))
end)
and p_tmEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n = (max_level (FStar_List.append ((colon_equals)::(pipe_right)::[]) operatorInfix0ad12))
in (p_tmEq' n e)))
and p_tmEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (match ((let _167_831 = (unparen e)
in _167_831.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (((is_operatorInfix0ad12 op) || (op = "=")) || (op = "|>")) -> begin
(

let _68_1013 = (levels op)
in (match (_68_1013) with
| (left, mine, right) -> begin
(let _167_835 = (let _167_834 = (str op)
in (let _167_833 = (p_tmEq' left e1)
in (let _167_832 = (p_tmEq' right e2)
in (infix0 _167_834 _167_833 _167_832))))
in (paren_if curr mine _167_835))
end))
end
| FStar_Parser_AST.Op (":=", (e1)::(e2)::[]) -> begin
(let _167_841 = (let _167_840 = (p_tmEq e1)
in (let _167_839 = (let _167_838 = (let _167_837 = (let _167_836 = (p_tmEq e2)
in (op_Hat_Slash_Plus_Hat FStar_Pprint.equals _167_836))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _167_837))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_838))
in (FStar_Pprint.op_Hat_Hat _167_840 _167_839)))
in (FStar_Pprint.group _167_841))
end
| _68_1021 -> begin
(p_tmNoEq e)
end))
and p_tmNoEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n = (max_level ((colon_colon)::(amp)::(opinfix3)::(opinfix4)::[]))
in (p_tmNoEq' n e)))
and p_tmNoEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (match ((let _167_845 = (unparen e)
in _167_845.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Construct (lid, ((e1, _68_1033))::((e2, _68_1029))::[]) when ((FStar_Ident.lid_equals lid FStar_Syntax_Const.cons_lid) && (not ((is_list e)))) -> begin
(

let op = "::"
in (

let _68_1042 = (levels op)
in (match (_68_1042) with
| (left, mine, right) -> begin
(let _167_849 = (let _167_848 = (str op)
in (let _167_847 = (p_tmNoEq' left e1)
in (let _167_846 = (p_tmNoEq' right e2)
in (infix0 _167_848 _167_847 _167_846))))
in (paren_if curr mine _167_849))
end)))
end
| FStar_Parser_AST.Sum (binders, res) -> begin
(

let op = "&"
in (

let _68_1051 = (levels op)
in (match (_68_1051) with
| (left, mine, right) -> begin
(

let p_dsumfst = (fun b -> (let _167_855 = (p_binder false b)
in (let _167_854 = (let _167_853 = (let _167_852 = (str "&")
in (FStar_Pprint.op_Hat_Hat _167_852 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_853))
in (FStar_Pprint.op_Hat_Hat _167_855 _167_854))))
in (let _167_858 = (let _167_857 = (FStar_Pprint.concat_map p_dsumfst binders)
in (let _167_856 = (p_tmNoEq' right res)
in (FStar_Pprint.op_Hat_Hat _167_857 _167_856)))
in (paren_if curr mine _167_858)))
end)))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (is_operatorInfix34 op) -> begin
(

let _68_1063 = (levels op)
in (match (_68_1063) with
| (left, mine, right) -> begin
(let _167_862 = (let _167_861 = (str op)
in (let _167_860 = (p_tmNoEq' left e1)
in (let _167_859 = (p_tmNoEq' right e2)
in (infix0 _167_861 _167_860 _167_859))))
in (paren_if curr mine _167_862))
end))
end
| FStar_Parser_AST.Op ("-", (e)::[]) -> begin
(

let _68_1072 = (levels "-")
in (match (_68_1072) with
| (left, mine, right) -> begin
(let _167_863 = (p_tmNoEq' mine e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus _167_863))
end))
end
| FStar_Parser_AST.NamedTyp (lid, e) -> begin
(let _167_867 = (let _167_866 = (p_lidentOrUnderscore lid)
in (let _167_865 = (let _167_864 = (p_appTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon _167_864))
in (FStar_Pprint.op_Hat_Slash_Hat _167_866 _167_865)))
in (FStar_Pprint.group _167_867))
end
| FStar_Parser_AST.Refine (b, phi) -> begin
(p_refinedBinder b phi)
end
| FStar_Parser_AST.Record (with_opt, record_fields) -> begin
(let _167_871 = (let _167_870 = (default_or_map FStar_Pprint.empty p_with_clause with_opt)
in (let _167_869 = (let _167_868 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (FStar_Pprint.separate_map _167_868 p_simpleDef record_fields))
in (FStar_Pprint.op_Hat_Hat _167_870 _167_869)))
in (braces_with_nesting _167_871))
end
| FStar_Parser_AST.Op ("~", (e)::[]) -> begin
(let _167_874 = (let _167_873 = (str "~")
in (let _167_872 = (p_atomicTerm e)
in (FStar_Pprint.op_Hat_Hat _167_873 _167_872)))
in (FStar_Pprint.group _167_874))
end
| _68_1091 -> begin
(p_appTerm e)
end))
and p_with_clause : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (let _167_879 = (p_appTerm e)
in (let _167_878 = (let _167_877 = (let _167_876 = (str "with")
in (FStar_Pprint.op_Hat_Hat _167_876 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_877))
in (FStar_Pprint.op_Hat_Hat _167_879 _167_878))))
and p_refinedBinder : FStar_Parser_AST.binder  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun b phi -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (lid, t) -> begin
(let _167_883 = (let _167_882 = (p_lident lid)
in (p_refinement b.FStar_Parser_AST.aqual _167_882 t phi))
in (soft_parens_with_nesting _167_883))
end
| FStar_Parser_AST.TAnnotated (_68_1100) -> begin
(failwith "Is this still used ?")
end
| (FStar_Parser_AST.Variable (_)) | (FStar_Parser_AST.TVariable (_)) | (FStar_Parser_AST.NoName (_)) -> begin
(let _167_885 = (let _167_884 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" _167_884))
in (failwith _167_885))
end))
and p_simpleDef : (FStar_Ident.lid * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun _68_1113 -> (match (_68_1113) with
| (lid, e) -> begin
(let _167_890 = (let _167_889 = (p_qlident lid)
in (let _167_888 = (let _167_887 = (p_tmIff e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals _167_887))
in (FStar_Pprint.op_Hat_Slash_Hat _167_889 _167_888)))
in (FStar_Pprint.group _167_890))
end))
and p_appTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _167_892 = (unparen e)
in _167_892.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (_68_1116) when (is_general_application e) -> begin
(

let _68_1120 = (head_and_args e)
in (match (_68_1120) with
| (head, args) -> begin
(let _167_894 = (p_indexingTerm head)
in (let _167_893 = (FStar_Pprint.separate_map FStar_Pprint.space p_argTerm args)
in (op_Hat_Slash_Plus_Hat _167_894 _167_893)))
end))
end
| FStar_Parser_AST.Construct (lid, args) when ((is_general_construction e) && (not ((is_dtuple_constructor lid)))) -> begin
(match (args) with
| [] -> begin
(p_quident lid)
end
| (arg)::[] -> begin
(let _167_897 = (let _167_896 = (p_quident lid)
in (let _167_895 = (p_argTerm arg)
in (FStar_Pprint.op_Hat_Slash_Hat _167_896 _167_895)))
in (FStar_Pprint.group _167_897))
end
| (hd)::tl -> begin
(let _167_904 = (let _167_903 = (let _167_900 = (let _167_899 = (p_quident lid)
in (let _167_898 = (p_argTerm hd)
in (FStar_Pprint.op_Hat_Slash_Hat _167_899 _167_898)))
in (FStar_Pprint.group _167_900))
in (let _167_902 = (let _167_901 = (FStar_Pprint.separate_map break1 p_argTerm tl)
in (jump2 _167_901))
in (FStar_Pprint.op_Hat_Hat _167_903 _167_902)))
in (FStar_Pprint.group _167_904))
end)
end
| _68_1132 -> begin
(p_indexingTerm e)
end))
and p_argTerm : (FStar_Parser_AST.term * FStar_Parser_AST.imp)  ->  FStar_Pprint.document = (fun arg_imp -> (match (arg_imp) with
| ({FStar_Parser_AST.tm = FStar_Parser_AST.Uvar (_68_1139); FStar_Parser_AST.range = _68_1137; FStar_Parser_AST.level = _68_1135}, FStar_Parser_AST.UnivApp) -> begin
(p_univar (Prims.fst arg_imp))
end
| (u, FStar_Parser_AST.UnivApp) -> begin
(p_universe u)
end
| (e, FStar_Parser_AST.FsTypApp) -> begin
(let _167_906 = (p_indexingTerm e)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.langle _167_906 FStar_Pprint.rangle))
end
| (e, FStar_Parser_AST.Hash) -> begin
(let _167_908 = (str "#")
in (let _167_907 = (p_indexingTerm e)
in (FStar_Pprint.op_Hat_Hat _167_908 _167_907)))
end
| (e, FStar_Parser_AST.Nothing) -> begin
(p_indexingTerm e)
end))
and p_indexingTerm_aux : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun exit e -> (match ((let _167_914 = (unparen e)
in _167_914.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Op (".()", (e1)::(e2)::[]) -> begin
(let _167_919 = (let _167_918 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (let _167_917 = (let _167_916 = (let _167_915 = (p_term e2)
in (soft_parens_with_nesting _167_915))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _167_916))
in (FStar_Pprint.op_Hat_Hat _167_918 _167_917)))
in (FStar_Pprint.group _167_919))
end
| FStar_Parser_AST.Op (".[]", (e1)::(e2)::[]) -> begin
(let _167_924 = (let _167_923 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (let _167_922 = (let _167_921 = (let _167_920 = (p_term e2)
in (soft_brackets_with_nesting _167_920))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _167_921))
in (FStar_Pprint.op_Hat_Hat _167_923 _167_922)))
in (FStar_Pprint.group _167_924))
end
| _68_1171 -> begin
(exit e)
end))
and p_indexingTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_indexingTerm_aux p_atomicTerm e))
and p_atomicTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _167_927 = (unparen e)
in _167_927.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.LetOpen (lid, e) -> begin
(let _167_931 = (p_quident lid)
in (let _167_930 = (let _167_929 = (let _167_928 = (p_term e)
in (soft_parens_with_nesting _167_928))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _167_929))
in (FStar_Pprint.op_Hat_Hat _167_931 _167_930)))
end
| FStar_Parser_AST.Name (lid) -> begin
(p_quident lid)
end
| FStar_Parser_AST.Op (op, (e)::[]) when (is_general_prefix_op op) -> begin
(let _167_933 = (str op)
in (let _167_932 = (p_atomicTerm e)
in (FStar_Pprint.op_Hat_Hat _167_933 _167_932)))
end
| _68_1186 -> begin
(p_atomicTermNotQUident e)
end))
and p_atomicTermNotQUident : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _167_935 = (unparen e)
in _167_935.FStar_Parser_AST.tm)) with
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
(let _167_937 = (str op)
in (let _167_936 = (p_atomicTermNotQUident e)
in (FStar_Pprint.op_Hat_Hat _167_937 _167_936)))
end
| FStar_Parser_AST.Op (op, []) -> begin
(let _167_941 = (let _167_940 = (let _167_939 = (str op)
in (let _167_938 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat _167_939 _167_938)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_940))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _167_941))
end
| FStar_Parser_AST.Construct (lid, args) when (is_dtuple_constructor lid) -> begin
(let _167_946 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (let _167_945 = (let _167_943 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (let _167_942 = (FStar_List.map Prims.fst args)
in (FStar_Pprint.separate_map _167_943 p_tmEq _167_942)))
in (let _167_944 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _167_946 _167_945 _167_944))))
end
| FStar_Parser_AST.Project (e, lid) -> begin
(let _167_950 = (let _167_949 = (p_atomicTermNotQUident e)
in (let _167_948 = (let _167_947 = (p_qlident lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _167_947))
in (FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0") _167_949 _167_948)))
in (FStar_Pprint.group _167_950))
end
| _68_1217 -> begin
(p_projectionLHS e)
end))
and p_projectionLHS : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _167_952 = (unparen e)
in _167_952.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Var (lid) -> begin
(p_qlident lid)
end
| FStar_Parser_AST.Projector (constr_lid, field_lid) -> begin
(let _167_956 = (p_quident constr_lid)
in (let _167_955 = (let _167_954 = (let _167_953 = (p_lident field_lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _167_953))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark _167_954))
in (FStar_Pprint.op_Hat_Hat _167_956 _167_955)))
end
| FStar_Parser_AST.Discrim (constr_lid) -> begin
(let _167_957 = (p_quident constr_lid)
in (FStar_Pprint.op_Hat_Hat _167_957 FStar_Pprint.qmark))
end
| FStar_Parser_AST.Paren (e) -> begin
(let _167_958 = (p_term e)
in (soft_parens_with_nesting _167_958))
end
| _68_1230 when (is_array e) -> begin
(

let es = (extract_from_list e)
in (let _167_962 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar)
in (let _167_961 = (let _167_959 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (separate_map_or_flow _167_959 p_noSeqTerm es))
in (let _167_960 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") _167_962 _167_961 _167_960)))))
end
| _68_1233 when (is_list e) -> begin
(let _167_965 = (let _167_964 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (let _167_963 = (extract_from_list e)
in (separate_map_or_flow _167_964 p_noSeqTerm _167_963)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket _167_965 FStar_Pprint.rbracket))
end
| _68_1235 when (is_lex_list e) -> begin
(let _167_969 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket)
in (let _167_968 = (let _167_967 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (let _167_966 = (extract_from_list e)
in (separate_map_or_flow _167_967 p_noSeqTerm _167_966)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _167_969 _167_968 FStar_Pprint.rbracket)))
end
| _68_1237 when (is_ref_set e) -> begin
(

let es = (extract_from_ref_set e)
in (let _167_972 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace)
in (let _167_971 = (let _167_970 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (separate_map_or_flow _167_970 p_appTerm es))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") _167_972 _167_971 FStar_Pprint.rbrace))))
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Op (_)) | (FStar_Parser_AST.Tvar (_)) | (FStar_Parser_AST.Uvar (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) | (FStar_Parser_AST.Construct (_)) | (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.App (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.LetOpen (_)) | (FStar_Parser_AST.Seq (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Ascribed (_)) | (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Project (_)) | (FStar_Parser_AST.Product (_)) | (FStar_Parser_AST.Sum (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Refine (_)) | (FStar_Parser_AST.NamedTyp (_)) | (FStar_Parser_AST.Requires (_)) | (FStar_Parser_AST.Ensures (_)) | (FStar_Parser_AST.Assign (_)) | (FStar_Parser_AST.Attributes (_)) -> begin
(let _167_973 = (p_term e)
in (soft_parens_with_nesting _167_973))
end
| FStar_Parser_AST.Labeled (_68_1325) -> begin
(failwith "Not valid in universe")
end))
and p_constant : FStar_Const.sconst  ->  FStar_Pprint.document = (fun _68_15 -> (match (_68_15) with
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
(let _167_975 = (FStar_Pprint.doc_of_char x)
in (FStar_Pprint.squotes _167_975))
end
| FStar_Const.Const_string (bytes, _68_1338) -> begin
(let _167_976 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes _167_976))
end
| FStar_Const.Const_bytearray (bytes, _68_1343) -> begin
(let _167_979 = (let _167_977 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes _167_977))
in (let _167_978 = (str "B")
in (FStar_Pprint.op_Hat_Hat _167_979 _167_978)))
end
| FStar_Const.Const_int (repr, sign_width_opt) -> begin
(

let signedness = (fun _68_13 -> (match (_68_13) with
| FStar_Const.Unsigned -> begin
(str "u")
end
| FStar_Const.Signed -> begin
FStar_Pprint.empty
end))
in (

let width = (fun _68_14 -> (match (_68_14) with
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

let ending = (default_or_map FStar_Pprint.empty (fun _68_1362 -> (match (_68_1362) with
| (s, w) -> begin
(let _167_986 = (signedness s)
in (let _167_985 = (width w)
in (FStar_Pprint.op_Hat_Hat _167_986 _167_985)))
end)) sign_width_opt)
in (let _167_987 = (str repr)
in (FStar_Pprint.op_Hat_Hat _167_987 ending)))))
end
| FStar_Const.Const_range (r) -> begin
(let _167_988 = (FStar_Range.string_of_range r)
in (str _167_988))
end
| FStar_Const.Const_reify -> begin
(str "reify")
end
| FStar_Const.Const_reflect (lid) -> begin
(let _167_992 = (p_quident lid)
in (let _167_991 = (let _167_990 = (let _167_989 = (str "reflect")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _167_989))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark _167_990))
in (FStar_Pprint.op_Hat_Hat _167_992 _167_991)))
end))
and p_universe : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (let _167_995 = (str "u#")
in (let _167_994 = (p_atomicUniverse u)
in (FStar_Pprint.op_Hat_Hat _167_995 _167_994))))
and p_universeFrom : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match ((let _167_997 = (unparen u)
in _167_997.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Op ("+", (u1)::(u2)::[]) -> begin
(let _167_1001 = (let _167_1000 = (p_universeFrom u1)
in (let _167_999 = (let _167_998 = (p_universeFrom u2)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus _167_998))
in (FStar_Pprint.op_Hat_Slash_Hat _167_1000 _167_999)))
in (FStar_Pprint.group _167_1001))
end
| FStar_Parser_AST.App (_68_1378) -> begin
(

let _68_1382 = (head_and_args u)
in (match (_68_1382) with
| (head, args) -> begin
(match ((let _167_1002 = (unparen head)
in _167_1002.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Var (maybe_max_lid) when (FStar_Ident.lid_equals maybe_max_lid FStar_Syntax_Const.max_lid) -> begin
(let _167_1006 = (let _167_1005 = (p_qlident FStar_Syntax_Const.max_lid)
in (let _167_1004 = (FStar_Pprint.separate_map FStar_Pprint.space (fun _68_1388 -> (match (_68_1388) with
| (u, _68_1387) -> begin
(p_atomicUniverse u)
end)) args)
in (op_Hat_Slash_Plus_Hat _167_1005 _167_1004)))
in (FStar_Pprint.group _167_1006))
end
| _68_1390 -> begin
(let _167_1008 = (let _167_1007 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" _167_1007))
in (failwith _167_1008))
end)
end))
end
| _68_1392 -> begin
(p_atomicUniverse u)
end))
and p_atomicUniverse : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match ((let _167_1010 = (unparen u)
in _167_1010.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (r, sw)) -> begin
(p_constant (FStar_Const.Const_int (((r), (sw)))))
end
| FStar_Parser_AST.Uvar (_68_1401) -> begin
(p_univar u)
end
| FStar_Parser_AST.Paren (u) -> begin
(let _167_1011 = (p_universeFrom u)
in (soft_parens_with_nesting _167_1011))
end
| (FStar_Parser_AST.Op ("+", (_)::(_)::[])) | (FStar_Parser_AST.App (_)) -> begin
(let _167_1012 = (p_universeFrom u)
in (soft_parens_with_nesting _167_1012))
end
| _68_1417 -> begin
(let _167_1014 = (let _167_1013 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" _167_1013))
in (failwith _167_1014))
end))
and p_univar : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match ((let _167_1016 = (unparen u)
in _167_1016.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Uvar (id) -> begin
(str (FStar_Ident.text_of_id id))
end
| _68_1422 -> begin
(let _167_1018 = (let _167_1017 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Not a universe variable %s" _167_1017))
in (failwith _167_1018))
end))


let term_to_document : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_term e))


let decl_to_document : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun e -> (p_decl e))


let modul_to_document : FStar_Parser_AST.modul  ->  FStar_Pprint.document = (fun m -> (match (m) with
| (FStar_Parser_AST.Module (_, decls)) | (FStar_Parser_AST.Interface (_, decls, _)) -> begin
(let _167_1025 = (FStar_All.pipe_right decls (FStar_List.map decl_to_document))
in (FStar_All.pipe_right _167_1025 (FStar_Pprint.separate FStar_Pprint.hardline)))
end))


let comments_to_document : (Prims.string * FStar_Range.range) Prims.list  ->  FStar_Pprint.document = (fun comments -> (FStar_Pprint.separate_map FStar_Pprint.hardline (fun _68_1440 -> (match (_68_1440) with
| (comment, range) -> begin
(str comment)
end)) comments))


let modul_with_comments_to_document : FStar_Parser_AST.modul  ->  (Prims.string * FStar_Range.range) Prims.list  ->  (FStar_Pprint.document * (Prims.string * FStar_Range.range) Prims.list) = (fun m comments -> (

let rec aux = (fun _68_1447 decl -> (match (_68_1447) with
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

let rec process_preceding_comments = (fun doc last_line end_pos n _68_16 -> (match (_68_16) with
| ((comment, range))::comments when (let _167_1051 = (FStar_Range.start_of_range range)
in (FStar_Range.pos_geq end_pos _167_1051)) -> begin
(

let l = (let _167_1053 = ((let _167_1052 = (FStar_Range.start_of_range range)
in (FStar_Range.line_of_pos _167_1052)) - last_line)
in (max (Prims.parse_int "1") _167_1053))
in (

let doc = (let _167_1056 = (let _167_1055 = (FStar_Pprint.repeat l FStar_Pprint.hardline)
in (let _167_1054 = (str comment)
in (FStar_Pprint.op_Hat_Hat _167_1055 _167_1054)))
in (FStar_Pprint.op_Hat_Hat doc _167_1056))
in (let _167_1058 = (let _167_1057 = (FStar_Range.end_of_range range)
in (FStar_Range.line_of_pos _167_1057))
in (process_preceding_comments doc _167_1058 end_pos (Prims.parse_int "1") comments))))
end
| comments -> begin
(

let l = (let _167_1059 = ((FStar_Range.line_of_pos end_pos) - last_line)
in (max n _167_1059))
in (let _167_1061 = (let _167_1060 = (FStar_Pprint.repeat l FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat doc _167_1060))
in ((_167_1061), (comments))))
end))
in (

let _68_1470 = (let _167_1064 = (FStar_Range.line_of_pos previous_range_end)
in (let _167_1063 = (let _167_1062 = (FStar_Range.start_of_range current_range)
in (FStar_Range.end_of_line _167_1062))
in (process_preceding_comments doc _167_1064 _167_1063 (Prims.parse_int "0") comments)))
in (match (_68_1470) with
| (doc, comments) -> begin
(

let _68_1478 = (FStar_Util.take (fun _68_17 -> (match (_68_17) with
| (_68_1473, range) -> begin
(FStar_Range.range_contains_range current_range range)
end)) comments)
in (match (_68_1478) with
| (inner_comments, comments) -> begin
(

let _68_1479 = (FStar_ST.op_Colon_Equals comment_stack inner_comments)
in (

let doc = (let _167_1066 = (decl_to_document decl)
in (FStar_Pprint.op_Hat_Hat doc _167_1066))
in (

let inner_comments_doc = if ((FStar_ST.read comment_stack) = []) then begin
FStar_Pprint.empty
end else begin
(

let _68_1482 = (let _167_1069 = (let _167_1068 = (let _167_1067 = (FStar_ST.read comment_stack)
in (FStar_List.map Prims.fst _167_1067))
in (FStar_String.concat " ; " _167_1068))
in (FStar_Util.print1_warning "Leftover comments : %s\n" _167_1069))
in (let _167_1070 = (FStar_ST.read comment_stack)
in (comments_to_document _167_1070)))
end
in (let _167_1072 = (FStar_Range.end_of_range decl.FStar_Parser_AST.drange)
in (let _167_1071 = (FStar_Pprint.op_Hat_Hat doc inner_comments_doc)
in ((_167_1072), (comments), (_167_1071)))))))
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
| (d)::_68_1499 -> begin
(

let _68_1506 = (FStar_List.fold_left aux ((FStar_Range.zeroPos), (comments), (FStar_Pprint.empty)) decls)
in (match (_68_1506) with
| (_68_1503, comments, doc) -> begin
((doc), (comments))
end))
end))))




