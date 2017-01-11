
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


let rec p_decl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (let _167_323 = (let _167_322 = (FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc)
in (let _167_321 = (let _167_320 = (p_attributes d.FStar_Parser_AST.attrs)
in (let _167_319 = (let _167_318 = (p_qualifiers d.FStar_Parser_AST.quals)
in (let _167_317 = (let _167_316 = (p_rawDecl d)
in (FStar_Pprint.op_Hat_Hat (if (d.FStar_Parser_AST.quals = []) then begin
FStar_Pprint.empty
end else begin
break1
end) _167_316))
in (FStar_Pprint.op_Hat_Hat _167_318 _167_317)))
in (FStar_Pprint.op_Hat_Hat _167_320 _167_319)))
in (FStar_Pprint.op_Hat_Hat _167_322 _167_321)))
in (FStar_Pprint.group _167_323)))
and p_attributes : FStar_Parser_AST.attributes_  ->  FStar_Pprint.document = (fun attrs -> (let _167_327 = (let _167_325 = (str "@")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket _167_325))
in (let _167_326 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline)
in (FStar_Pprint.surround_separate_map (Prims.parse_int "0") (Prims.parse_int "2") FStar_Pprint.empty _167_327 FStar_Pprint.space _167_326 p_atomicTerm attrs))))
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
(let _167_335 = (str "@")
in (let _167_334 = (let _167_333 = (str kwd)
in (let _167_332 = (let _167_331 = (str arg)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_331))
in (FStar_Pprint.op_Hat_Hat _167_333 _167_332)))
in (FStar_Pprint.op_Hat_Hat _167_335 _167_334)))
end))
in (let _167_337 = (let _167_336 = (FStar_Pprint.separate_map FStar_Pprint.hardline process_kwd_arg kwd_args)
in (FStar_Pprint.op_Hat_Hat _167_336 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline _167_337)))
end)
in (let _167_345 = (let _167_344 = (let _167_343 = (let _167_342 = (let _167_341 = (str doc)
in (let _167_340 = (let _167_339 = (let _167_338 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _167_338))
in (FStar_Pprint.op_Hat_Hat kwd_args_doc _167_339))
in (FStar_Pprint.op_Hat_Hat _167_341 _167_340)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _167_342))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _167_343))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _167_344))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline _167_345)))
end))
and p_rawDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Open (uid) -> begin
(let _167_349 = (let _167_348 = (str "open")
in (let _167_347 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat _167_348 _167_347)))
in (FStar_Pprint.group _167_349))
end
| FStar_Parser_AST.Include (uid) -> begin
(let _167_352 = (let _167_351 = (str "include")
in (let _167_350 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat _167_351 _167_350)))
in (FStar_Pprint.group _167_352))
end
| FStar_Parser_AST.ModuleAbbrev (uid1, uid2) -> begin
(let _167_359 = (let _167_357 = (str "module")
in (let _167_356 = (let _167_355 = (let _167_354 = (p_uident uid1)
in (let _167_353 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _167_354 _167_353)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_355))
in (FStar_Pprint.op_Hat_Hat _167_357 _167_356)))
in (let _167_358 = (p_quident uid2)
in (op_Hat_Slash_Plus_Hat _167_359 _167_358)))
end
| FStar_Parser_AST.TopLevelModule (uid) -> begin
(let _167_363 = (let _167_362 = (str "module")
in (let _167_361 = (let _167_360 = (p_quident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_360))
in (FStar_Pprint.op_Hat_Hat _167_362 _167_361)))
in (FStar_Pprint.group _167_363))
end
| FStar_Parser_AST.KindAbbrev (_68_349) -> begin
(failwith "Deprecated, please stop throwing your old stuff at me !")
end
| FStar_Parser_AST.Tycon (true, ((FStar_Parser_AST.TyconAbbrev (uid, tpars, None, t), None))::[]) -> begin
(

let effect_prefix_doc = (let _167_366 = (str "effect")
in (let _167_365 = (let _167_364 = (p_uident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_364))
in (FStar_Pprint.op_Hat_Hat _167_366 _167_365)))
in (let _167_369 = (let _167_367 = (p_typars tpars)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") effect_prefix_doc _167_367 FStar_Pprint.equals))
in (let _167_368 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _167_369 _167_368))))
end
| FStar_Parser_AST.Tycon (false, tcdefs) -> begin
(let _167_371 = (str "type")
in (let _167_370 = (str "and")
in (precede_break_separate_map _167_371 _167_370 p_fsdocTypeDeclPairs tcdefs)))
end
| FStar_Parser_AST.TopLevelLet (q, lbs) -> begin
(

let let_doc = (let _167_373 = (str "let")
in (let _167_372 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat _167_373 _167_372)))
in (let _167_374 = (str "and")
in (precede_break_separate_map let_doc _167_374 p_letbinding lbs)))
end
| FStar_Parser_AST.Val (lid, t) -> begin
(let _167_381 = (let _167_379 = (str "val")
in (let _167_378 = (let _167_377 = (let _167_376 = (p_lident lid)
in (let _167_375 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat _167_376 _167_375)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_377))
in (FStar_Pprint.op_Hat_Hat _167_379 _167_378)))
in (let _167_380 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _167_381 _167_380)))
end
| FStar_Parser_AST.Assume (id, t) -> begin
(

let decl_keyword = if (let _167_382 = (FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_All.pipe_right _167_382 FStar_Util.is_upper)) then begin
FStar_Pprint.empty
end else begin
(let _167_383 = (str "val")
in (FStar_Pprint.op_Hat_Hat _167_383 FStar_Pprint.space))
end
in (let _167_388 = (let _167_386 = (let _167_385 = (p_ident id)
in (let _167_384 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat _167_385 _167_384)))
in (FStar_Pprint.op_Hat_Hat decl_keyword _167_386))
in (let _167_387 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _167_388 _167_387))))
end
| FStar_Parser_AST.Exception (uid, t_opt) -> begin
(let _167_396 = (str "exception")
in (let _167_395 = (let _167_394 = (let _167_393 = (p_uident uid)
in (let _167_392 = (FStar_Pprint.optional (fun t -> (let _167_391 = (str "of")
in (let _167_390 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _167_391 _167_390)))) t_opt)
in (FStar_Pprint.op_Hat_Hat _167_393 _167_392)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_394))
in (FStar_Pprint.op_Hat_Hat _167_396 _167_395)))
end
| FStar_Parser_AST.NewEffect (ne) -> begin
(let _167_399 = (str "new_effect")
in (let _167_398 = (let _167_397 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_397))
in (FStar_Pprint.op_Hat_Hat _167_399 _167_398)))
end
| FStar_Parser_AST.SubEffect (se) -> begin
(let _167_402 = (str "sub_effect")
in (let _167_401 = (let _167_400 = (p_subEffect se)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_400))
in (FStar_Pprint.op_Hat_Hat _167_402 _167_401)))
end
| FStar_Parser_AST.NewEffectForFree (ne) -> begin
(let _167_405 = (str "new_effect_for_free")
in (let _167_404 = (let _167_403 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_403))
in (FStar_Pprint.op_Hat_Hat _167_405 _167_404)))
end
| FStar_Parser_AST.Pragma (p) -> begin
(p_pragma p)
end
| FStar_Parser_AST.Fsdoc (doc) -> begin
(let _167_406 = (p_fsdoc doc)
in (FStar_Pprint.op_Hat_Hat _167_406 FStar_Pprint.hardline))
end
| FStar_Parser_AST.Main (_68_398) -> begin
(failwith "*Main declaration* : Is that really still in use ??")
end
| FStar_Parser_AST.Tycon (true, _68_402) -> begin
(failwith "Effect abbreviation is expected to be defined by an abbreviation")
end))
and p_pragma : FStar_Parser_AST.pragma  ->  FStar_Pprint.document = (fun _68_4 -> (match (_68_4) with
| FStar_Parser_AST.SetOptions (s) -> begin
(let _167_411 = (str "#set-options")
in (let _167_410 = (let _167_409 = (let _167_408 = (str s)
in (FStar_Pprint.dquotes _167_408))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_409))
in (FStar_Pprint.op_Hat_Hat _167_411 _167_410)))
end
| FStar_Parser_AST.ResetOptions (s_opt) -> begin
(let _167_416 = (str "#reset-options")
in (let _167_415 = (FStar_Pprint.optional (fun s -> (let _167_414 = (let _167_413 = (str s)
in (FStar_Pprint.dquotes _167_413))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_414))) s_opt)
in (FStar_Pprint.op_Hat_Hat _167_416 _167_415)))
end))
and p_typars : FStar_Parser_AST.binder Prims.list  ->  FStar_Pprint.document = (fun bs -> (p_binders true bs))
and p_fsdocTypeDeclPairs : (FStar_Parser_AST.tycon * FStar_Parser_AST.fsdoc Prims.option)  ->  FStar_Pprint.document = (fun _68_414 -> (match (_68_414) with
| (typedecl, fsdoc_opt) -> begin
(let _167_420 = (FStar_Pprint.optional p_fsdoc fsdoc_opt)
in (let _167_419 = (p_typeDecl typedecl)
in (FStar_Pprint.op_Hat_Hat _167_420 _167_419)))
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
(let _167_426 = (p_typ t)
in (prefix2 FStar_Pprint.equals _167_426))
end))
in (p_typeDeclPrefix lid bs typ_opt f))
end
| FStar_Parser_AST.TyconRecord (lid, bs, typ_opt, record_field_decls) -> begin
(

let p_recordFieldAndComments = (fun _68_441 -> (match (_68_441) with
| (lid, t, doc_opt) -> begin
(let _167_429 = (FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range)
in (with_comment p_recordFieldDecl ((lid), (t), (doc_opt)) _167_429))
end))
in (

let p_fields = (fun _68_443 -> (match (()) with
| () -> begin
(let _167_435 = (let _167_434 = (let _167_433 = (let _167_432 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (FStar_Pprint.separate_map _167_432 p_recordFieldAndComments record_field_decls))
in (braces_with_nesting _167_433))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_434))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.equals _167_435))
end))
in (p_typeDeclPrefix lid bs typ_opt p_fields)))
end
| FStar_Parser_AST.TyconVariant (lid, bs, typ_opt, ct_decls) -> begin
(

let p_constructorBranchAndComments = (fun _68_455 -> (match (_68_455) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let range = (let _167_440 = (let _167_439 = (FStar_Util.map_opt t_opt (fun t -> t.FStar_Parser_AST.range))
in (FStar_Util.dflt uid.FStar_Ident.idRange _167_439))
in (FStar_Range.extend_to_end_of_line _167_440))
in (

let p_constructorBranch = (fun decl -> (let _167_445 = (let _167_444 = (let _167_443 = (p_constructorDecl decl)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_443))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar _167_444))
in (FStar_Pprint.group _167_445)))
in (with_comment p_constructorBranch ((uid), (t_opt), (doc_opt), (use_of)) range)))
end))
in (

let datacon_doc = (fun _68_461 -> (match (()) with
| () -> begin
(let _167_448 = (FStar_Pprint.separate_map break1 p_constructorBranchAndComments ct_decls)
in (FStar_Pprint.group _167_448))
end))
in (p_typeDeclPrefix lid bs typ_opt (fun _68_462 -> (match (()) with
| () -> begin
(let _167_450 = (datacon_doc ())
in (prefix2 FStar_Pprint.equals _167_450))
end)))))
end))
and p_typeDeclPrefix : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.knd Prims.option  ->  (Prims.unit  ->  FStar_Pprint.document)  ->  FStar_Pprint.document = (fun lid bs typ_opt cont -> if ((bs = []) && (typ_opt = None)) then begin
(let _167_460 = (p_ident lid)
in (let _167_459 = (let _167_458 = (cont ())
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_458))
in (FStar_Pprint.op_Hat_Hat _167_460 _167_459)))
end else begin
(

let binders_doc = (let _167_466 = (p_typars bs)
in (let _167_465 = (FStar_Pprint.optional (fun t -> (let _167_464 = (let _167_463 = (let _167_462 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_462))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _167_463))
in (FStar_Pprint.op_Hat_Hat break1 _167_464))) typ_opt)
in (FStar_Pprint.op_Hat_Hat _167_466 _167_465)))
in (let _167_468 = (p_ident lid)
in (let _167_467 = (cont ())
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _167_468 binders_doc _167_467))))
end)
and p_recordFieldDecl : (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc Prims.option)  ->  FStar_Pprint.document = (fun _68_472 -> (match (_68_472) with
| (lid, t, doc_opt) -> begin
(let _167_475 = (let _167_474 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (let _167_473 = (let _167_472 = (p_lident lid)
in (let _167_471 = (let _167_470 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _167_470))
in (FStar_Pprint.op_Hat_Hat _167_472 _167_471)))
in (FStar_Pprint.op_Hat_Hat _167_474 _167_473)))
in (FStar_Pprint.group _167_475))
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
in (let _167_482 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (let _167_481 = (default_or_map uid_doc (fun t -> (let _167_480 = (let _167_478 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep)
in (FStar_Pprint.op_Hat_Hat uid_doc _167_478))
in (let _167_479 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _167_480 _167_479)))) t_opt)
in (FStar_Pprint.op_Hat_Hat _167_482 _167_481)))))
end))
and p_letbinding : (FStar_Parser_AST.pattern * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun _68_483 -> (match (_68_483) with
| (pat, e) -> begin
(

let pat_doc = (

let _68_492 = (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, t) -> begin
(let _167_488 = (let _167_487 = (let _167_486 = (let _167_485 = (let _167_484 = (p_tmArrow p_tmNoEq t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_484))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _167_485))
in (FStar_Pprint.group _167_486))
in (FStar_Pprint.op_Hat_Hat break1 _167_487))
in ((pat), (_167_488)))
end
| _68_489 -> begin
((pat), (FStar_Pprint.empty))
end)
in (match (_68_492) with
| (pat, ascr_doc) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _68_497); FStar_Parser_AST.prange = _68_494}, pats) -> begin
(let _167_491 = (p_lident x)
in (let _167_490 = (let _167_489 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Hat _167_489 ascr_doc))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _167_491 _167_490 FStar_Pprint.equals)))
end
| _68_505 -> begin
(let _167_494 = (let _167_493 = (p_tuplePattern pat)
in (let _167_492 = (FStar_Pprint.op_Hat_Slash_Hat ascr_doc FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _167_493 _167_492)))
in (FStar_Pprint.group _167_494))
end)
end))
in (let _167_495 = (p_term e)
in (prefix2 pat_doc _167_495)))
end))
and p_newEffect : FStar_Parser_AST.effect_decl  ->  FStar_Pprint.document = (fun _68_6 -> (match (_68_6) with
| FStar_Parser_AST.RedefineEffect (lid, bs, t) -> begin
(p_effectRedefinition lid bs t)
end
| FStar_Parser_AST.DefineEffect (lid, bs, t, eff_decls, action_decls) -> begin
(p_effectDefinition lid bs t eff_decls action_decls)
end))
and p_effectRedefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun uid bs t -> (let _167_503 = (p_uident uid)
in (let _167_502 = (p_binders true bs)
in (let _167_501 = (let _167_500 = (p_simpleTerm t)
in (prefix2 FStar_Pprint.equals _167_500))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _167_503 _167_502 _167_501)))))
and p_effectDefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun uid bs t eff_decls action_decls -> (let _167_520 = (let _167_519 = (let _167_513 = (let _167_512 = (p_uident uid)
in (let _167_511 = (p_binders true bs)
in (let _167_510 = (let _167_509 = (p_typ t)
in (prefix2 FStar_Pprint.colon _167_509))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _167_512 _167_511 _167_510))))
in (FStar_Pprint.group _167_513))
in (let _167_518 = (let _167_517 = (let _167_515 = (str "with")
in (let _167_514 = (separate_break_map FStar_Pprint.semi p_effectDecl eff_decls)
in (prefix2 _167_515 _167_514)))
in (let _167_516 = (p_actionDecls action_decls)
in (FStar_Pprint.op_Hat_Hat _167_517 _167_516)))
in (FStar_Pprint.op_Hat_Slash_Hat _167_519 _167_518)))
in (braces_with_nesting _167_520)))
and p_actionDecls : FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun _68_7 -> (match (_68_7) with
| [] -> begin
FStar_Pprint.empty
end
| l -> begin
(let _167_524 = (let _167_523 = (str "and actions")
in (let _167_522 = (separate_break_map FStar_Pprint.semi p_effectDecl l)
in (prefix2 _167_523 _167_522)))
in (FStar_Pprint.op_Hat_Hat break1 _167_524))
end))
and p_effectDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (false, ((FStar_Parser_AST.TyconAbbrev (lid, [], None, e), None))::[]) -> begin
(let _167_529 = (let _167_527 = (p_lident lid)
in (let _167_526 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _167_527 _167_526)))
in (let _167_528 = (p_simpleTerm e)
in (prefix2 _167_529 _167_528)))
end
| _68_545 -> begin
(let _167_531 = (let _167_530 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "Not a declaration of an effect member... or at least I hope so : %s" _167_530))
in (failwith _167_531))
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
(let _167_538 = (let _167_536 = (str kwd)
in (let _167_535 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _167_536 _167_535)))
in (let _167_537 = (p_simpleTerm t)
in (prefix2 _167_538 _167_537)))
end))
in (separate_break_map FStar_Pprint.semi p_lift lifts)))
in (let _167_546 = (let _167_543 = (let _167_541 = (p_quident lift.FStar_Parser_AST.msource)
in (let _167_540 = (let _167_539 = (str "~>")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_539))
in (FStar_Pprint.op_Hat_Hat _167_541 _167_540)))
in (let _167_542 = (p_quident lift.FStar_Parser_AST.mdest)
in (prefix2 _167_543 _167_542)))
in (let _167_545 = (let _167_544 = (braces_with_nesting lift_op_doc)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_544))
in (FStar_Pprint.op_Hat_Hat _167_546 _167_545)))))
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
and p_qualifiers : FStar_Parser_AST.qualifiers  ->  FStar_Pprint.document = (fun qs -> (let _167_549 = (FStar_Pprint.separate_map break1 p_qualifier qs)
in (FStar_Pprint.group _167_549)))
and p_letqualifier : FStar_Parser_AST.let_qualifier  ->  FStar_Pprint.document = (fun _68_9 -> (match (_68_9) with
| FStar_Parser_AST.Rec -> begin
(let _167_551 = (str "rec")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_551))
end
| FStar_Parser_AST.Mutable -> begin
(let _167_552 = (str "mutable")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_552))
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
(let _167_557 = (let _167_556 = (let _167_555 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space)
in (FStar_Pprint.op_Hat_Hat break1 _167_555))
in (FStar_Pprint.separate_map _167_556 p_tuplePattern pats))
in (FStar_Pprint.group _167_557))
end
| _68_593 -> begin
(p_tuplePattern p)
end))
and p_tuplePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTuple (pats, false) -> begin
(let _167_560 = (let _167_559 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map _167_559 p_constructorPattern pats))
in (FStar_Pprint.group _167_560))
end
| _68_600 -> begin
(p_constructorPattern p)
end))
and p_constructorPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (maybe_cons_lid); FStar_Parser_AST.prange = _68_603}, (hd)::(tl)::[]) when (FStar_Ident.lid_equals maybe_cons_lid FStar_Syntax_Const.cons_lid) -> begin
(let _167_564 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon)
in (let _167_563 = (p_constructorPattern hd)
in (let _167_562 = (p_constructorPattern tl)
in (infix0 _167_564 _167_563 _167_562))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (uid); FStar_Parser_AST.prange = _68_613}, pats) -> begin
(let _167_566 = (p_quident uid)
in (let _167_565 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (prefix2 _167_566 _167_565)))
end
| _68_621 -> begin
(p_atomicPattern p)
end))
and p_atomicPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, t) -> begin
(match ((let _167_569 = (let _167_568 = (unparen t)
in _167_568.FStar_Parser_AST.tm)
in ((pat.FStar_Parser_AST.pat), (_167_569)))) with
| (FStar_Parser_AST.PatVar (lid, aqual), FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t); FStar_Parser_AST.brange = _68_636; FStar_Parser_AST.blevel = _68_634; FStar_Parser_AST.aqual = _68_632}, phi)) when (lid.FStar_Ident.idText = lid'.FStar_Ident.idText) -> begin
(let _167_571 = (let _167_570 = (p_ident lid)
in (p_refinement aqual _167_570 t phi))
in (soft_parens_with_nesting _167_571))
end
| (FStar_Parser_AST.PatWild, FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t); FStar_Parser_AST.brange = _68_652; FStar_Parser_AST.blevel = _68_650; FStar_Parser_AST.aqual = _68_648}, phi)) -> begin
(let _167_572 = (p_refinement None FStar_Pprint.underscore t phi)
in (soft_parens_with_nesting _167_572))
end
| _68_661 -> begin
(let _167_578 = (let _167_577 = (p_tuplePattern pat)
in (let _167_576 = (let _167_575 = (FStar_Pprint.break_ (Prims.parse_int "0"))
in (let _167_574 = (let _167_573 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _167_573))
in (FStar_Pprint.op_Hat_Hat _167_575 _167_574)))
in (FStar_Pprint.op_Hat_Hat _167_577 _167_576)))
in (soft_parens_with_nesting _167_578))
end)
end
| FStar_Parser_AST.PatList (pats) -> begin
(let _167_579 = (separate_break_map FStar_Pprint.semi p_tuplePattern pats)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket _167_579 FStar_Pprint.rbracket))
end
| FStar_Parser_AST.PatRecord (pats) -> begin
(

let p_recordFieldPat = (fun _68_669 -> (match (_68_669) with
| (lid, pat) -> begin
(let _167_583 = (p_qlident lid)
in (let _167_582 = (p_tuplePattern pat)
in (infix2 FStar_Pprint.equals _167_583 _167_582)))
end))
in (let _167_584 = (separate_break_map FStar_Pprint.semi p_recordFieldPat pats)
in (soft_braces_with_nesting _167_584)))
end
| FStar_Parser_AST.PatTuple (pats, true) -> begin
(let _167_587 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (let _167_586 = (separate_break_map FStar_Pprint.comma p_constructorPattern pats)
in (let _167_585 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _167_587 _167_586 _167_585))))
end
| FStar_Parser_AST.PatTvar (tv, arg_qualifier_opt) -> begin
(

let _68_678 = ()
in (p_tvar tv))
end
| FStar_Parser_AST.PatOp (op) -> begin
(let _167_591 = (let _167_590 = (let _167_589 = (str op)
in (let _167_588 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat _167_589 _167_588)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_590))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _167_591))
end
| FStar_Parser_AST.PatWild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.PatConst (c) -> begin
(p_constant c)
end
| FStar_Parser_AST.PatVar (lid, aqual) -> begin
(let _167_593 = (FStar_Pprint.optional p_aqual aqual)
in (let _167_592 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat _167_593 _167_592)))
end
| FStar_Parser_AST.PatName (uid) -> begin
(p_quident uid)
end
| FStar_Parser_AST.PatOr (_68_692) -> begin
(failwith "Inner or pattern !")
end
| (FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (_); FStar_Parser_AST.prange = _}, _)) | (FStar_Parser_AST.PatTuple (_, false)) -> begin
(let _167_594 = (p_tuplePattern p)
in (soft_parens_with_nesting _167_594))
end
| _68_710 -> begin
(let _167_596 = (let _167_595 = (FStar_Parser_AST.pat_to_string p)
in (FStar_Util.format1 "Invalid pattern %s" _167_595))
in (failwith _167_596))
end))
and p_binder : Prims.bool  ->  FStar_Parser_AST.binder  ->  FStar_Pprint.document = (fun is_atomic b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (lid) -> begin
(let _167_600 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (let _167_599 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat _167_600 _167_599)))
end
| FStar_Parser_AST.TVariable (lid) -> begin
(p_lident lid)
end
| FStar_Parser_AST.Annotated (lid, t) -> begin
(

let doc = (match ((let _167_601 = (unparen t)
in _167_601.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t); FStar_Parser_AST.brange = _68_726; FStar_Parser_AST.blevel = _68_724; FStar_Parser_AST.aqual = _68_722}, phi) when (lid.FStar_Ident.idText = lid'.FStar_Ident.idText) -> begin
(let _167_602 = (p_ident lid)
in (p_refinement b.FStar_Parser_AST.aqual _167_602 t phi))
end
| _68_736 -> begin
(let _167_609 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (let _167_608 = (let _167_607 = (p_lident lid)
in (let _167_606 = (let _167_605 = (let _167_604 = (FStar_Pprint.break_ (Prims.parse_int "0"))
in (let _167_603 = (p_tmFormula t)
in (FStar_Pprint.op_Hat_Hat _167_604 _167_603)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _167_605))
in (FStar_Pprint.op_Hat_Hat _167_607 _167_606)))
in (FStar_Pprint.op_Hat_Hat _167_609 _167_608)))
end)
in if is_atomic then begin
(let _167_611 = (let _167_610 = (FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _167_610))
in (FStar_Pprint.group _167_611))
end else begin
(FStar_Pprint.group doc)
end)
end
| FStar_Parser_AST.TAnnotated (_68_739) -> begin
(failwith "Is this still used ?")
end
| FStar_Parser_AST.NoName (t) -> begin
(match ((let _167_612 = (unparen t)
in _167_612.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t); FStar_Parser_AST.brange = _68_748; FStar_Parser_AST.blevel = _68_746; FStar_Parser_AST.aqual = _68_744}, phi) -> begin
if is_atomic then begin
(let _167_615 = (let _167_614 = (let _167_613 = (p_refinement b.FStar_Parser_AST.aqual FStar_Pprint.underscore t phi)
in (FStar_Pprint.op_Hat_Hat _167_613 FStar_Pprint.rparen))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _167_614))
in (FStar_Pprint.group _167_615))
end else begin
(let _167_616 = (p_refinement b.FStar_Parser_AST.aqual FStar_Pprint.underscore t phi)
in (FStar_Pprint.group _167_616))
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
and p_refinement : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Pprint.document  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun aqual_opt binder t phi -> (let _167_627 = (FStar_Pprint.optional p_aqual aqual_opt)
in (let _167_626 = (let _167_625 = (let _167_624 = (let _167_623 = (p_appTerm t)
in (let _167_622 = (let _167_621 = (p_noSeqTerm phi)
in (soft_braces_with_nesting _167_621))
in (FStar_Pprint.op_Hat_Hat _167_623 _167_622)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _167_624))
in (FStar_Pprint.op_Hat_Hat binder _167_625))
in (FStar_Pprint.op_Hat_Hat _167_627 _167_626))))
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
and p_term : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _167_638 = (unparen e)
in _167_638.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Seq (e1, e2) -> begin
(let _167_642 = (let _167_640 = (let _167_639 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat _167_639 FStar_Pprint.semi))
in (FStar_Pprint.group _167_640))
in (let _167_641 = (p_term e2)
in (FStar_Pprint.op_Hat_Slash_Hat _167_642 _167_641)))
end
| _68_776 -> begin
(let _167_643 = (p_noSeqTerm e)
in (FStar_Pprint.group _167_643))
end))
and p_noSeqTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_noSeqTerm' e e.FStar_Parser_AST.range))
and p_noSeqTerm' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _167_646 = (unparen e)
in _167_646.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Ascribed (e, t) -> begin
(let _167_651 = (let _167_650 = (p_tmIff e)
in (let _167_649 = (let _167_648 = (let _167_647 = (p_typ t)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon _167_647))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.langle _167_648))
in (FStar_Pprint.op_Hat_Slash_Hat _167_650 _167_649)))
in (FStar_Pprint.group _167_651))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::(e3)::[]) when (op = ".()<-") -> begin
(let _167_662 = (let _167_661 = (let _167_658 = (let _167_657 = (p_atomicTermNotQUident e1)
in (let _167_656 = (let _167_655 = (let _167_654 = (let _167_652 = (p_term e2)
in (soft_parens_with_nesting _167_652))
in (let _167_653 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat _167_654 _167_653)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _167_655))
in (FStar_Pprint.op_Hat_Hat _167_657 _167_656)))
in (FStar_Pprint.group _167_658))
in (let _167_660 = (let _167_659 = (p_noSeqTerm e3)
in (jump2 _167_659))
in (FStar_Pprint.op_Hat_Hat _167_661 _167_660)))
in (FStar_Pprint.group _167_662))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::(e3)::[]) when (op = ".[]<-") -> begin
(let _167_673 = (let _167_672 = (let _167_669 = (let _167_668 = (p_atomicTermNotQUident e1)
in (let _167_667 = (let _167_666 = (let _167_665 = (let _167_663 = (p_term e2)
in (soft_brackets_with_nesting _167_663))
in (let _167_664 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat _167_665 _167_664)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _167_666))
in (FStar_Pprint.op_Hat_Hat _167_668 _167_667)))
in (FStar_Pprint.group _167_669))
in (let _167_671 = (let _167_670 = (p_noSeqTerm e3)
in (jump2 _167_670))
in (FStar_Pprint.op_Hat_Hat _167_672 _167_671)))
in (FStar_Pprint.group _167_673))
end
| FStar_Parser_AST.Requires (e, wtf) -> begin
(

let _68_801 = ()
in (let _167_676 = (let _167_675 = (str "requires")
in (let _167_674 = (p_typ e)
in (FStar_Pprint.op_Hat_Slash_Hat _167_675 _167_674)))
in (FStar_Pprint.group _167_676)))
end
| FStar_Parser_AST.Ensures (e, wtf) -> begin
(

let _68_807 = ()
in (let _167_679 = (let _167_678 = (str "ensures")
in (let _167_677 = (p_typ e)
in (FStar_Pprint.op_Hat_Slash_Hat _167_678 _167_677)))
in (FStar_Pprint.group _167_679)))
end
| FStar_Parser_AST.Attributes (es) -> begin
(let _167_682 = (let _167_681 = (str "attributes")
in (let _167_680 = (FStar_Pprint.separate_map break1 p_atomicTerm es)
in (FStar_Pprint.op_Hat_Slash_Hat _167_681 _167_680)))
in (FStar_Pprint.group _167_682))
end
| FStar_Parser_AST.If (e1, e2, e3) -> begin
if (is_unit e3) then begin
(let _167_689 = (let _167_688 = (let _167_684 = (str "if")
in (let _167_683 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat _167_684 _167_683)))
in (let _167_687 = (let _167_686 = (str "then")
in (let _167_685 = (p_noSeqTerm e2)
in (op_Hat_Slash_Plus_Hat _167_686 _167_685)))
in (FStar_Pprint.op_Hat_Slash_Hat _167_688 _167_687)))
in (FStar_Pprint.group _167_689))
end else begin
(

let e2_doc = (match ((let _167_690 = (unparen e2)
in _167_690.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.If (_68_817, _68_819, e3) when (is_unit e3) -> begin
(let _167_691 = (p_noSeqTerm e2)
in (soft_parens_with_nesting _167_691))
end
| _68_824 -> begin
(p_noSeqTerm e2)
end)
in (let _167_701 = (let _167_700 = (let _167_693 = (str "if")
in (let _167_692 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat _167_693 _167_692)))
in (let _167_699 = (let _167_698 = (let _167_694 = (str "then")
in (op_Hat_Slash_Plus_Hat _167_694 e2_doc))
in (let _167_697 = (let _167_696 = (str "else")
in (let _167_695 = (p_noSeqTerm e3)
in (op_Hat_Slash_Plus_Hat _167_696 _167_695)))
in (FStar_Pprint.op_Hat_Slash_Hat _167_698 _167_697)))
in (FStar_Pprint.op_Hat_Slash_Hat _167_700 _167_699)))
in (FStar_Pprint.group _167_701)))
end
end
| FStar_Parser_AST.TryWith (e, branches) -> begin
(let _167_708 = (let _167_707 = (let _167_703 = (str "try")
in (let _167_702 = (p_noSeqTerm e)
in (prefix2 _167_703 _167_702)))
in (let _167_706 = (let _167_705 = (str "with")
in (let _167_704 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat _167_705 _167_704)))
in (FStar_Pprint.op_Hat_Slash_Hat _167_707 _167_706)))
in (FStar_Pprint.group _167_708))
end
| FStar_Parser_AST.Match (e, branches) -> begin
(let _167_714 = (let _167_713 = (let _167_711 = (str "match")
in (let _167_710 = (p_noSeqTerm e)
in (let _167_709 = (str "with")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _167_711 _167_710 _167_709))))
in (let _167_712 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat _167_713 _167_712)))
in (FStar_Pprint.group _167_714))
end
| FStar_Parser_AST.LetOpen (uid, e) -> begin
(let _167_720 = (let _167_719 = (let _167_717 = (str "let open")
in (let _167_716 = (p_quident uid)
in (let _167_715 = (str "in")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _167_717 _167_716 _167_715))))
in (let _167_718 = (p_term e)
in (FStar_Pprint.op_Hat_Slash_Hat _167_719 _167_718)))
in (FStar_Pprint.group _167_720))
end
| FStar_Parser_AST.Let (q, lbs, e) -> begin
(

let let_doc = (let _167_722 = (str "let")
in (let _167_721 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat _167_722 _167_721)))
in (let _167_728 = (let _167_726 = (let _167_725 = (let _167_723 = (str "and")
in (precede_break_separate_map let_doc _167_723 p_letbinding lbs))
in (let _167_724 = (str "in")
in (FStar_Pprint.op_Hat_Slash_Hat _167_725 _167_724)))
in (FStar_Pprint.group _167_726))
in (let _167_727 = (p_term e)
in (FStar_Pprint.op_Hat_Slash_Hat _167_728 _167_727))))
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, typ_opt); FStar_Parser_AST.prange = _68_845})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, branches); FStar_Parser_AST.range = _68_855; FStar_Parser_AST.level = _68_853}) when (matches_var maybe_x x) -> begin
(let _167_731 = (let _167_730 = (str "function")
in (let _167_729 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat _167_730 _167_729)))
in (FStar_Pprint.group _167_731))
end
| FStar_Parser_AST.Assign (id, e) -> begin
(let _167_735 = (let _167_734 = (p_lident id)
in (let _167_733 = (let _167_732 = (p_noSeqTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow _167_732))
in (FStar_Pprint.op_Hat_Slash_Hat _167_734 _167_733)))
in (FStar_Pprint.group _167_735))
end
| _68_868 -> begin
(p_typ e)
end))
and p_typ : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_typ' e e.FStar_Parser_AST.range))
and p_typ' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _167_738 = (unparen e)
in _167_738.FStar_Parser_AST.tm)) with
| (FStar_Parser_AST.QForall (bs, trigger, e1)) | (FStar_Parser_AST.QExists (bs, trigger, e1)) -> begin
(let _167_745 = (let _167_741 = (let _167_739 = (p_quantifier e)
in (FStar_Pprint.op_Hat_Hat _167_739 FStar_Pprint.space))
in (let _167_740 = (p_binders true bs)
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") _167_741 _167_740 FStar_Pprint.dot)))
in (let _167_744 = (let _167_743 = (p_trigger trigger)
in (let _167_742 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat _167_743 _167_742)))
in (prefix2 _167_745 _167_744)))
end
| _68_879 -> begin
(p_simpleTerm e)
end))
and p_quantifier : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _167_747 = (unparen e)
in _167_747.FStar_Parser_AST.tm)) with
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
(let _167_755 = (let _167_754 = (let _167_753 = (str "pattern")
in (let _167_752 = (let _167_751 = (let _167_749 = (p_disjunctivePats pats)
in (jump2 _167_749))
in (let _167_750 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1)
in (FStar_Pprint.op_Hat_Slash_Hat _167_751 _167_750)))
in (FStar_Pprint.op_Hat_Slash_Hat _167_753 _167_752)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _167_754))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace _167_755))
end))
and p_disjunctivePats : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun pats -> (let _167_757 = (str "\\/")
in (FStar_Pprint.separate_map _167_757 p_conjunctivePats pats)))
and p_conjunctivePats : FStar_Parser_AST.term Prims.list  ->  FStar_Pprint.document = (fun pats -> (let _167_759 = (FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats)
in (FStar_Pprint.group _167_759)))
and p_simpleTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _167_761 = (unparen e)
in _167_761.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Abs (pats, e) -> begin
(let _167_766 = (let _167_764 = (str "fun")
in (let _167_763 = (let _167_762 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Slash_Hat _167_762 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat _167_764 _167_763)))
in (let _167_765 = (p_term e)
in (op_Hat_Slash_Plus_Hat _167_766 _167_765)))
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

let maybe_paren = (match ((let _167_771 = (unparen e)
in _167_771.FStar_Parser_AST.tm)) with
| (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) -> begin
soft_begin_end_with_nesting
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _68_916); FStar_Parser_AST.prange = _68_913})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, _68_927); FStar_Parser_AST.range = _68_924; FStar_Parser_AST.level = _68_922}) when (matches_var maybe_x x) -> begin
soft_begin_end_with_nesting
end
| _68_934 -> begin
(fun x -> x)
end)
in (let _167_782 = (let _167_781 = (let _167_778 = (let _167_777 = (let _167_776 = (let _167_775 = (p_disjunctivePattern pat)
in (let _167_774 = (let _167_773 = (p_maybeWhen when_opt)
in (FStar_Pprint.op_Hat_Hat _167_773 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat _167_775 _167_774)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_776))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar _167_777))
in (FStar_Pprint.group _167_778))
in (let _167_780 = (let _167_779 = (p_term e)
in (maybe_paren _167_779))
in (op_Hat_Slash_Plus_Hat _167_781 _167_780)))
in (FStar_Pprint.group _167_782)))
end))
and p_maybeWhen : FStar_Parser_AST.term Prims.option  ->  FStar_Pprint.document = (fun _68_12 -> (match (_68_12) with
| None -> begin
FStar_Pprint.empty
end
| Some (e) -> begin
(let _167_786 = (str "when")
in (let _167_785 = (let _167_784 = (p_tmFormula e)
in (FStar_Pprint.op_Hat_Hat _167_784 FStar_Pprint.space))
in (op_Hat_Slash_Plus_Hat _167_786 _167_785)))
end))
and p_tmIff : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _167_788 = (unparen e)
in _167_788.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Op ("<==>", (e1)::(e2)::[]) -> begin
(let _167_791 = (str "<==>")
in (let _167_790 = (p_tmImplies e1)
in (let _167_789 = (p_tmIff e2)
in (infix0 _167_791 _167_790 _167_789))))
end
| _68_949 -> begin
(p_tmImplies e)
end))
and p_tmImplies : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _167_793 = (unparen e)
in _167_793.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Op ("==>", (e1)::(e2)::[]) -> begin
(let _167_796 = (str "==>")
in (let _167_795 = (p_tmArrow p_tmFormula e1)
in (let _167_794 = (p_tmImplies e2)
in (infix0 _167_796 _167_795 _167_794))))
end
| _68_958 -> begin
(p_tmArrow p_tmFormula e)
end))
and p_tmArrow : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_Tm e -> (match ((let _167_802 = (unparen e)
in _167_802.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Product (bs, tgt) -> begin
(let _167_809 = (let _167_808 = (FStar_Pprint.concat_map (fun b -> (let _167_806 = (p_binder false b)
in (let _167_805 = (let _167_804 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_804))
in (FStar_Pprint.op_Hat_Hat _167_806 _167_805)))) bs)
in (let _167_807 = (p_tmArrow p_Tm tgt)
in (FStar_Pprint.op_Hat_Hat _167_808 _167_807)))
in (FStar_Pprint.group _167_809))
end
| _68_967 -> begin
(p_Tm e)
end))
and p_tmFormula : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _167_811 = (unparen e)
in _167_811.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Op ("\\/", (e1)::(e2)::[]) -> begin
(let _167_814 = (str "\\/")
in (let _167_813 = (p_tmFormula e1)
in (let _167_812 = (p_tmConjunction e2)
in (infix0 _167_814 _167_813 _167_812))))
end
| _68_976 -> begin
(p_tmConjunction e)
end))
and p_tmConjunction : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _167_816 = (unparen e)
in _167_816.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Op ("/\\", (e1)::(e2)::[]) -> begin
(let _167_819 = (str "/\\")
in (let _167_818 = (p_tmConjunction e1)
in (let _167_817 = (p_tmTuple e2)
in (infix0 _167_819 _167_818 _167_817))))
end
| _68_985 -> begin
(p_tmTuple e)
end))
and p_tmTuple : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_tmTuple' e e.FStar_Parser_AST.range))
and p_tmTuple' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _167_822 = (unparen e)
in _167_822.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Construct (lid, args) when (is_tuple_constructor lid) -> begin
(let _167_824 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map _167_824 (fun _68_995 -> (match (_68_995) with
| (e, _68_994) -> begin
(p_tmEq e)
end)) args))
end
| _68_997 -> begin
(p_tmEq e)
end))
and paren_if : Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun curr mine doc -> if (mine <= curr) then begin
doc
end else begin
(let _167_829 = (let _167_828 = (FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _167_828))
in (FStar_Pprint.group _167_829))
end)
and p_tmEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n = (max_level (FStar_List.append ((colon_equals)::(pipe_right)::[]) operatorInfix0ad12))
in (p_tmEq' n e)))
and p_tmEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (match ((let _167_833 = (unparen e)
in _167_833.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (((is_operatorInfix0ad12 op) || (op = "=")) || (op = "|>")) -> begin
(

let _68_1014 = (levels op)
in (match (_68_1014) with
| (left, mine, right) -> begin
(let _167_837 = (let _167_836 = (str op)
in (let _167_835 = (p_tmEq' left e1)
in (let _167_834 = (p_tmEq' right e2)
in (infix0 _167_836 _167_835 _167_834))))
in (paren_if curr mine _167_837))
end))
end
| FStar_Parser_AST.Op (":=", (e1)::(e2)::[]) -> begin
(let _167_843 = (let _167_842 = (p_tmEq e1)
in (let _167_841 = (let _167_840 = (let _167_839 = (let _167_838 = (p_tmEq e2)
in (op_Hat_Slash_Plus_Hat FStar_Pprint.equals _167_838))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _167_839))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_840))
in (FStar_Pprint.op_Hat_Hat _167_842 _167_841)))
in (FStar_Pprint.group _167_843))
end
| _68_1022 -> begin
(p_tmNoEq e)
end))
and p_tmNoEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n = (max_level ((colon_colon)::(amp)::(opinfix3)::(opinfix4)::[]))
in (p_tmNoEq' n e)))
and p_tmNoEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (match ((let _167_847 = (unparen e)
in _167_847.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Construct (lid, ((e1, _68_1034))::((e2, _68_1030))::[]) when ((FStar_Ident.lid_equals lid FStar_Syntax_Const.cons_lid) && (not ((is_list e)))) -> begin
(

let op = "::"
in (

let _68_1043 = (levels op)
in (match (_68_1043) with
| (left, mine, right) -> begin
(let _167_851 = (let _167_850 = (str op)
in (let _167_849 = (p_tmNoEq' left e1)
in (let _167_848 = (p_tmNoEq' right e2)
in (infix0 _167_850 _167_849 _167_848))))
in (paren_if curr mine _167_851))
end)))
end
| FStar_Parser_AST.Sum (binders, res) -> begin
(

let op = "&"
in (

let _68_1052 = (levels op)
in (match (_68_1052) with
| (left, mine, right) -> begin
(

let p_dsumfst = (fun b -> (let _167_857 = (p_binder false b)
in (let _167_856 = (let _167_855 = (let _167_854 = (str "&")
in (FStar_Pprint.op_Hat_Hat _167_854 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_855))
in (FStar_Pprint.op_Hat_Hat _167_857 _167_856))))
in (let _167_860 = (let _167_859 = (FStar_Pprint.concat_map p_dsumfst binders)
in (let _167_858 = (p_tmNoEq' right res)
in (FStar_Pprint.op_Hat_Hat _167_859 _167_858)))
in (paren_if curr mine _167_860)))
end)))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (is_operatorInfix34 op) -> begin
(

let _68_1064 = (levels op)
in (match (_68_1064) with
| (left, mine, right) -> begin
(let _167_864 = (let _167_863 = (str op)
in (let _167_862 = (p_tmNoEq' left e1)
in (let _167_861 = (p_tmNoEq' right e2)
in (infix0 _167_863 _167_862 _167_861))))
in (paren_if curr mine _167_864))
end))
end
| FStar_Parser_AST.Op ("-", (e)::[]) -> begin
(

let _68_1073 = (levels "-")
in (match (_68_1073) with
| (left, mine, right) -> begin
(let _167_865 = (p_tmNoEq' mine e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus _167_865))
end))
end
| FStar_Parser_AST.NamedTyp (lid, e) -> begin
(let _167_869 = (let _167_868 = (p_lidentOrUnderscore lid)
in (let _167_867 = (let _167_866 = (p_appTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon _167_866))
in (FStar_Pprint.op_Hat_Slash_Hat _167_868 _167_867)))
in (FStar_Pprint.group _167_869))
end
| FStar_Parser_AST.Refine (b, phi) -> begin
(p_refinedBinder b phi)
end
| FStar_Parser_AST.Record (with_opt, record_fields) -> begin
(let _167_873 = (let _167_872 = (default_or_map FStar_Pprint.empty p_with_clause with_opt)
in (let _167_871 = (let _167_870 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (FStar_Pprint.separate_map _167_870 p_simpleDef record_fields))
in (FStar_Pprint.op_Hat_Hat _167_872 _167_871)))
in (braces_with_nesting _167_873))
end
| FStar_Parser_AST.Op ("~", (e)::[]) -> begin
(let _167_876 = (let _167_875 = (str "~")
in (let _167_874 = (p_atomicTerm e)
in (FStar_Pprint.op_Hat_Hat _167_875 _167_874)))
in (FStar_Pprint.group _167_876))
end
| _68_1092 -> begin
(p_appTerm e)
end))
and p_with_clause : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (let _167_881 = (p_appTerm e)
in (let _167_880 = (let _167_879 = (let _167_878 = (str "with")
in (FStar_Pprint.op_Hat_Hat _167_878 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_879))
in (FStar_Pprint.op_Hat_Hat _167_881 _167_880))))
and p_refinedBinder : FStar_Parser_AST.binder  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun b phi -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (lid, t) -> begin
(let _167_885 = (let _167_884 = (p_lident lid)
in (p_refinement b.FStar_Parser_AST.aqual _167_884 t phi))
in (soft_parens_with_nesting _167_885))
end
| FStar_Parser_AST.TAnnotated (_68_1101) -> begin
(failwith "Is this still used ?")
end
| (FStar_Parser_AST.Variable (_)) | (FStar_Parser_AST.TVariable (_)) | (FStar_Parser_AST.NoName (_)) -> begin
(let _167_887 = (let _167_886 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" _167_886))
in (failwith _167_887))
end))
and p_simpleDef : (FStar_Ident.lid * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun _68_1114 -> (match (_68_1114) with
| (lid, e) -> begin
(let _167_892 = (let _167_891 = (p_qlident lid)
in (let _167_890 = (let _167_889 = (p_tmIff e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals _167_889))
in (FStar_Pprint.op_Hat_Slash_Hat _167_891 _167_890)))
in (FStar_Pprint.group _167_892))
end))
and p_appTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _167_894 = (unparen e)
in _167_894.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (_68_1117) when (is_general_application e) -> begin
(

let _68_1121 = (head_and_args e)
in (match (_68_1121) with
| (head, args) -> begin
(let _167_896 = (p_indexingTerm head)
in (let _167_895 = (FStar_Pprint.separate_map FStar_Pprint.space p_argTerm args)
in (op_Hat_Slash_Plus_Hat _167_896 _167_895)))
end))
end
| FStar_Parser_AST.Construct (lid, args) when ((is_general_construction e) && (not ((is_dtuple_constructor lid)))) -> begin
(match (args) with
| [] -> begin
(p_quident lid)
end
| (arg)::[] -> begin
(let _167_899 = (let _167_898 = (p_quident lid)
in (let _167_897 = (p_argTerm arg)
in (FStar_Pprint.op_Hat_Slash_Hat _167_898 _167_897)))
in (FStar_Pprint.group _167_899))
end
| (hd)::tl -> begin
(let _167_906 = (let _167_905 = (let _167_902 = (let _167_901 = (p_quident lid)
in (let _167_900 = (p_argTerm hd)
in (prefix2 _167_901 _167_900)))
in (FStar_Pprint.group _167_902))
in (let _167_904 = (let _167_903 = (FStar_Pprint.separate_map break1 p_argTerm tl)
in (jump2 _167_903))
in (FStar_Pprint.op_Hat_Hat _167_905 _167_904)))
in (FStar_Pprint.group _167_906))
end)
end
| _68_1133 -> begin
(p_indexingTerm e)
end))
and p_argTerm : (FStar_Parser_AST.term * FStar_Parser_AST.imp)  ->  FStar_Pprint.document = (fun arg_imp -> (match (arg_imp) with
| ({FStar_Parser_AST.tm = FStar_Parser_AST.Uvar (_68_1140); FStar_Parser_AST.range = _68_1138; FStar_Parser_AST.level = _68_1136}, FStar_Parser_AST.UnivApp) -> begin
(p_univar (Prims.fst arg_imp))
end
| (u, FStar_Parser_AST.UnivApp) -> begin
(p_universe u)
end
| (e, FStar_Parser_AST.FsTypApp) -> begin
(let _167_908 = (p_indexingTerm e)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.langle _167_908 FStar_Pprint.rangle))
end
| (e, FStar_Parser_AST.Hash) -> begin
(let _167_910 = (str "#")
in (let _167_909 = (p_indexingTerm e)
in (FStar_Pprint.op_Hat_Hat _167_910 _167_909)))
end
| (e, FStar_Parser_AST.Nothing) -> begin
(p_indexingTerm e)
end))
and p_indexingTerm_aux : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun exit e -> (match ((let _167_916 = (unparen e)
in _167_916.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Op (".()", (e1)::(e2)::[]) -> begin
(let _167_921 = (let _167_920 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (let _167_919 = (let _167_918 = (let _167_917 = (p_term e2)
in (soft_parens_with_nesting _167_917))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _167_918))
in (FStar_Pprint.op_Hat_Hat _167_920 _167_919)))
in (FStar_Pprint.group _167_921))
end
| FStar_Parser_AST.Op (".[]", (e1)::(e2)::[]) -> begin
(let _167_926 = (let _167_925 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (let _167_924 = (let _167_923 = (let _167_922 = (p_term e2)
in (soft_brackets_with_nesting _167_922))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _167_923))
in (FStar_Pprint.op_Hat_Hat _167_925 _167_924)))
in (FStar_Pprint.group _167_926))
end
| _68_1172 -> begin
(exit e)
end))
and p_indexingTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_indexingTerm_aux p_atomicTerm e))
and p_atomicTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _167_929 = (unparen e)
in _167_929.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.LetOpen (lid, e) -> begin
(let _167_933 = (p_quident lid)
in (let _167_932 = (let _167_931 = (let _167_930 = (p_term e)
in (soft_parens_with_nesting _167_930))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _167_931))
in (FStar_Pprint.op_Hat_Hat _167_933 _167_932)))
end
| FStar_Parser_AST.Name (lid) -> begin
(p_quident lid)
end
| FStar_Parser_AST.Op (op, (e)::[]) when (is_general_prefix_op op) -> begin
(let _167_935 = (str op)
in (let _167_934 = (p_atomicTerm e)
in (FStar_Pprint.op_Hat_Hat _167_935 _167_934)))
end
| _68_1187 -> begin
(p_atomicTermNotQUident e)
end))
and p_atomicTermNotQUident : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _167_937 = (unparen e)
in _167_937.FStar_Parser_AST.tm)) with
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
(let _167_939 = (str op)
in (let _167_938 = (p_atomicTermNotQUident e)
in (FStar_Pprint.op_Hat_Hat _167_939 _167_938)))
end
| FStar_Parser_AST.Op (op, []) -> begin
(let _167_943 = (let _167_942 = (let _167_941 = (str op)
in (let _167_940 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat _167_941 _167_940)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _167_942))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _167_943))
end
| FStar_Parser_AST.Construct (lid, args) when (is_dtuple_constructor lid) -> begin
(let _167_948 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (let _167_947 = (let _167_945 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (let _167_944 = (FStar_List.map Prims.fst args)
in (FStar_Pprint.separate_map _167_945 p_tmEq _167_944)))
in (let _167_946 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _167_948 _167_947 _167_946))))
end
| FStar_Parser_AST.Project (e, lid) -> begin
(let _167_952 = (let _167_951 = (p_atomicTermNotQUident e)
in (let _167_950 = (let _167_949 = (p_qlident lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _167_949))
in (FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0") _167_951 _167_950)))
in (FStar_Pprint.group _167_952))
end
| _68_1218 -> begin
(p_projectionLHS e)
end))
and p_projectionLHS : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _167_954 = (unparen e)
in _167_954.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Var (lid) -> begin
(p_qlident lid)
end
| FStar_Parser_AST.Projector (constr_lid, field_lid) -> begin
(let _167_958 = (p_quident constr_lid)
in (let _167_957 = (let _167_956 = (let _167_955 = (p_lident field_lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _167_955))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark _167_956))
in (FStar_Pprint.op_Hat_Hat _167_958 _167_957)))
end
| FStar_Parser_AST.Discrim (constr_lid) -> begin
(let _167_959 = (p_quident constr_lid)
in (FStar_Pprint.op_Hat_Hat _167_959 FStar_Pprint.qmark))
end
| FStar_Parser_AST.Paren (e) -> begin
(let _167_960 = (p_term e)
in (soft_parens_with_nesting _167_960))
end
| _68_1231 when (is_array e) -> begin
(

let es = (extract_from_list e)
in (let _167_964 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar)
in (let _167_963 = (let _167_961 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (separate_map_or_flow _167_961 p_noSeqTerm es))
in (let _167_962 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") _167_964 _167_963 _167_962)))))
end
| _68_1234 when (is_list e) -> begin
(let _167_967 = (let _167_966 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (let _167_965 = (extract_from_list e)
in (separate_map_or_flow _167_966 p_noSeqTerm _167_965)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket _167_967 FStar_Pprint.rbracket))
end
| _68_1236 when (is_lex_list e) -> begin
(let _167_971 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket)
in (let _167_970 = (let _167_969 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (let _167_968 = (extract_from_list e)
in (separate_map_or_flow _167_969 p_noSeqTerm _167_968)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _167_971 _167_970 FStar_Pprint.rbracket)))
end
| _68_1238 when (is_ref_set e) -> begin
(

let es = (extract_from_ref_set e)
in (let _167_974 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace)
in (let _167_973 = (let _167_972 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (separate_map_or_flow _167_972 p_appTerm es))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") _167_974 _167_973 FStar_Pprint.rbrace))))
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Op (_)) | (FStar_Parser_AST.Tvar (_)) | (FStar_Parser_AST.Uvar (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) | (FStar_Parser_AST.Construct (_)) | (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.App (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.LetOpen (_)) | (FStar_Parser_AST.Seq (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Ascribed (_)) | (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Project (_)) | (FStar_Parser_AST.Product (_)) | (FStar_Parser_AST.Sum (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Refine (_)) | (FStar_Parser_AST.NamedTyp (_)) | (FStar_Parser_AST.Requires (_)) | (FStar_Parser_AST.Ensures (_)) | (FStar_Parser_AST.Assign (_)) | (FStar_Parser_AST.Attributes (_)) -> begin
(let _167_975 = (p_term e)
in (soft_parens_with_nesting _167_975))
end
| FStar_Parser_AST.Labeled (_68_1326) -> begin
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
(let _167_977 = (FStar_Pprint.doc_of_char x)
in (FStar_Pprint.squotes _167_977))
end
| FStar_Const.Const_string (bytes, _68_1339) -> begin
(let _167_978 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes _167_978))
end
| FStar_Const.Const_bytearray (bytes, _68_1344) -> begin
(let _167_981 = (let _167_979 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes _167_979))
in (let _167_980 = (str "B")
in (FStar_Pprint.op_Hat_Hat _167_981 _167_980)))
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

let ending = (default_or_map FStar_Pprint.empty (fun _68_1363 -> (match (_68_1363) with
| (s, w) -> begin
(let _167_988 = (signedness s)
in (let _167_987 = (width w)
in (FStar_Pprint.op_Hat_Hat _167_988 _167_987)))
end)) sign_width_opt)
in (let _167_989 = (str repr)
in (FStar_Pprint.op_Hat_Hat _167_989 ending)))))
end
| FStar_Const.Const_range (r) -> begin
(let _167_990 = (FStar_Range.string_of_range r)
in (str _167_990))
end
| FStar_Const.Const_reify -> begin
(str "reify")
end
| FStar_Const.Const_reflect (lid) -> begin
(let _167_994 = (p_quident lid)
in (let _167_993 = (let _167_992 = (let _167_991 = (str "reflect")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _167_991))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark _167_992))
in (FStar_Pprint.op_Hat_Hat _167_994 _167_993)))
end))
and p_universe : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (let _167_997 = (str "u#")
in (let _167_996 = (p_atomicUniverse u)
in (FStar_Pprint.op_Hat_Hat _167_997 _167_996))))
and p_universeFrom : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match ((let _167_999 = (unparen u)
in _167_999.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Op ("+", (u1)::(u2)::[]) -> begin
(let _167_1003 = (let _167_1002 = (p_universeFrom u1)
in (let _167_1001 = (let _167_1000 = (p_universeFrom u2)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus _167_1000))
in (FStar_Pprint.op_Hat_Slash_Hat _167_1002 _167_1001)))
in (FStar_Pprint.group _167_1003))
end
| FStar_Parser_AST.App (_68_1379) -> begin
(

let _68_1383 = (head_and_args u)
in (match (_68_1383) with
| (head, args) -> begin
(match ((let _167_1004 = (unparen head)
in _167_1004.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Var (maybe_max_lid) when (FStar_Ident.lid_equals maybe_max_lid FStar_Syntax_Const.max_lid) -> begin
(let _167_1008 = (let _167_1007 = (p_qlident FStar_Syntax_Const.max_lid)
in (let _167_1006 = (FStar_Pprint.separate_map FStar_Pprint.space (fun _68_1389 -> (match (_68_1389) with
| (u, _68_1388) -> begin
(p_atomicUniverse u)
end)) args)
in (op_Hat_Slash_Plus_Hat _167_1007 _167_1006)))
in (FStar_Pprint.group _167_1008))
end
| _68_1391 -> begin
(let _167_1010 = (let _167_1009 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" _167_1009))
in (failwith _167_1010))
end)
end))
end
| _68_1393 -> begin
(p_atomicUniverse u)
end))
and p_atomicUniverse : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match ((let _167_1012 = (unparen u)
in _167_1012.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (r, sw)) -> begin
(p_constant (FStar_Const.Const_int (((r), (sw)))))
end
| FStar_Parser_AST.Uvar (_68_1402) -> begin
(p_univar u)
end
| FStar_Parser_AST.Paren (u) -> begin
(let _167_1013 = (p_universeFrom u)
in (soft_parens_with_nesting _167_1013))
end
| (FStar_Parser_AST.Op ("+", (_)::(_)::[])) | (FStar_Parser_AST.App (_)) -> begin
(let _167_1014 = (p_universeFrom u)
in (soft_parens_with_nesting _167_1014))
end
| _68_1418 -> begin
(let _167_1016 = (let _167_1015 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" _167_1015))
in (failwith _167_1016))
end))
and p_univar : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match ((let _167_1018 = (unparen u)
in _167_1018.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Uvar (id) -> begin
(str (FStar_Ident.text_of_id id))
end
| _68_1423 -> begin
(let _167_1020 = (let _167_1019 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Not a universe variable %s" _167_1019))
in (failwith _167_1020))
end))


let term_to_document : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_term e))


let decl_to_document : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun e -> (p_decl e))


let modul_to_document : FStar_Parser_AST.modul  ->  FStar_Pprint.document = (fun m -> (match (m) with
| (FStar_Parser_AST.Module (_, decls)) | (FStar_Parser_AST.Interface (_, decls, _)) -> begin
(let _167_1027 = (FStar_All.pipe_right decls (FStar_List.map decl_to_document))
in (FStar_All.pipe_right _167_1027 (FStar_Pprint.separate FStar_Pprint.hardline)))
end))


let comments_to_document : (Prims.string * FStar_Range.range) Prims.list  ->  FStar_Pprint.document = (fun comments -> (FStar_Pprint.separate_map FStar_Pprint.hardline (fun _68_1441 -> (match (_68_1441) with
| (comment, range) -> begin
(str comment)
end)) comments))


let modul_with_comments_to_document : FStar_Parser_AST.modul  ->  (Prims.string * FStar_Range.range) Prims.list  ->  (FStar_Pprint.document * (Prims.string * FStar_Range.range) Prims.list) = (fun m comments -> (

let rec aux = (fun _68_1448 decl -> (match (_68_1448) with
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
| ((comment, range))::comments when (let _167_1053 = (FStar_Range.start_of_range range)
in (FStar_Range.pos_geq end_pos _167_1053)) -> begin
(

let l = (

let min = if (last_line = (Prims.parse_int "1")) then begin
(Prims.parse_int "0")
end else begin
(Prims.parse_int "1")
end
in (let _167_1055 = ((let _167_1054 = (FStar_Range.start_of_range range)
in (FStar_Range.line_of_pos _167_1054)) - last_line)
in (max min _167_1055)))
in (

let doc = (let _167_1058 = (let _167_1057 = (FStar_Pprint.repeat l FStar_Pprint.hardline)
in (let _167_1056 = (str comment)
in (FStar_Pprint.op_Hat_Hat _167_1057 _167_1056)))
in (FStar_Pprint.op_Hat_Hat doc _167_1058))
in (let _167_1060 = (let _167_1059 = (FStar_Range.end_of_range range)
in (FStar_Range.line_of_pos _167_1059))
in (process_preceding_comments doc _167_1060 end_pos (Prims.parse_int "1") comments))))
end
| comments -> begin
(

let l = (let _167_1061 = ((FStar_Range.line_of_pos end_pos) - last_line)
in (max n _167_1061))
in (let _167_1063 = (let _167_1062 = (FStar_Pprint.repeat l FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat doc _167_1062))
in ((_167_1063), (comments))))
end))
in (

let _68_1472 = (let _167_1066 = (FStar_Range.line_of_pos previous_range_end)
in (let _167_1065 = (let _167_1064 = (FStar_Range.start_of_range current_range)
in (FStar_Range.end_of_line _167_1064))
in (process_preceding_comments doc _167_1066 _167_1065 (Prims.parse_int "0") comments)))
in (match (_68_1472) with
| (doc, comments) -> begin
(

let _68_1480 = (FStar_Util.take (fun _68_17 -> (match (_68_17) with
| (_68_1475, range) -> begin
(FStar_Range.range_contains_range current_range range)
end)) comments)
in (match (_68_1480) with
| (inner_comments, comments) -> begin
(

let _68_1481 = (FStar_ST.op_Colon_Equals comment_stack inner_comments)
in (

let doc = (let _167_1068 = (decl_to_document decl)
in (FStar_Pprint.op_Hat_Hat doc _167_1068))
in (

let inner_comments_doc = if ((FStar_ST.read comment_stack) = []) then begin
FStar_Pprint.empty
end else begin
(

let _68_1484 = (let _167_1071 = (let _167_1070 = (let _167_1069 = (FStar_ST.read comment_stack)
in (FStar_List.map Prims.fst _167_1069))
in (FStar_String.concat " ; " _167_1070))
in (FStar_Util.print1_warning "Leftover comments : %s\n" _167_1071))
in (let _167_1072 = (FStar_ST.read comment_stack)
in (comments_to_document _167_1072)))
end
in (let _167_1074 = (FStar_Range.end_of_range decl.FStar_Parser_AST.drange)
in (let _167_1073 = (FStar_Pprint.op_Hat_Hat doc inner_comments_doc)
in ((_167_1074), (comments), (_167_1073)))))))
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
| (d)::_68_1501 -> begin
(

let _68_1508 = (FStar_List.fold_left aux ((FStar_Range.zeroPos), (comments), (FStar_Pprint.empty)) decls)
in (match (_68_1508) with
| (_68_1505, comments, doc) -> begin
((doc), (comments))
end))
end))))




