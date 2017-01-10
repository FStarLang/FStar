
open Prims

let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| _67_22 -> begin
t
end))


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


let separate_break_map = (fun sep f l -> (let _165_35 = (let _165_34 = (let _165_33 = (FStar_Pprint.op_Hat_Hat sep break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_33))
in (FStar_Pprint.separate_map _165_34 f l))
in (FStar_Pprint.group _165_35)))


let precede_break_separate_map = (fun prec sep f l -> (let _165_52 = (let _165_45 = (FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space)
in (let _165_44 = (let _165_43 = (FStar_List.hd l)
in (FStar_All.pipe_right _165_43 f))
in (FStar_Pprint.precede _165_45 _165_44)))
in (let _165_51 = (let _165_50 = (FStar_List.tl l)
in (FStar_Pprint.concat_map (fun x -> (let _165_49 = (let _165_48 = (let _165_47 = (f x)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_47))
in (FStar_Pprint.op_Hat_Hat sep _165_48))
in (FStar_Pprint.op_Hat_Hat break1 _165_49))) _165_50))
in (FStar_Pprint.op_Hat_Hat _165_52 _165_51))))


let concat_break_map = (fun f l -> (let _165_60 = (FStar_Pprint.concat_map (fun x -> (let _165_59 = (f x)
in (FStar_Pprint.op_Hat_Hat _165_59 break1))) l)
in (FStar_Pprint.group _165_60)))


let parens_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lparen contents FStar_Pprint.rparen))


let soft_parens_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lparen contents FStar_Pprint.rparen))


let braces_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbrace contents FStar_Pprint.rbrace))


let soft_braces_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbrace contents FStar_Pprint.rbrace))


let brackets_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbracket contents FStar_Pprint.rbracket))


let soft_brackets_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbracket contents FStar_Pprint.rbracket))


let soft_begin_end_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (let _165_76 = (str "begin")
in (let _165_75 = (str "end")
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") _165_76 contents _165_75))))


let separate_map_or_flow = (fun sep f l -> if ((FStar_List.length l) < (Prims.parse_int "10")) then begin
(FStar_Pprint.separate_map sep f l)
end else begin
(FStar_Pprint.flow_map sep f l)
end)


let doc_of_fsdoc : (Prims.string * (Prims.string * Prims.string) Prims.list)  ->  FStar_Pprint.document = (fun _67_58 -> (match (_67_58) with
| (comment, keywords) -> begin
(let _165_96 = (let _165_95 = (let _165_94 = (str comment)
in (let _165_93 = (let _165_92 = (let _165_91 = (FStar_Pprint.separate_map FStar_Pprint.comma (fun _67_61 -> (match (_67_61) with
| (k, v) -> begin
(let _165_90 = (let _165_89 = (str k)
in (let _165_88 = (let _165_87 = (let _165_86 = (str v)
in (_165_86)::[])
in (FStar_Pprint.rarrow)::_165_87)
in (_165_89)::_165_88))
in (FStar_Pprint.concat _165_90))
end)) keywords)
in (_165_91)::[])
in (FStar_Pprint.space)::_165_92)
in (_165_94)::_165_93))
in (FStar_Pprint.concat _165_95))
in (FStar_Pprint.group _165_96))
end))


let is_unit : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match ((let _165_99 = (unparen e)
in _165_99.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Const (FStar_Const.Const_unit) -> begin
true
end
| _67_66 -> begin
false
end))


let matches_var : FStar_Parser_AST.term  ->  FStar_Ident.ident  ->  Prims.bool = (fun t x -> (match ((let _165_104 = (unparen t)
in _165_104.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Var (y) -> begin
(x.FStar_Ident.idText = (FStar_Ident.text_of_lid y))
end
| _67_72 -> begin
false
end))


let is_tuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Syntax_Util.is_tuple_data_lid'


let is_dtuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Syntax_Util.is_dtuple_data_lid'


let is_list_structure : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun cons_lid nil_lid -> (

let rec aux = (fun e -> (match ((let _165_117 = (unparen e)
in _165_117.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Construct (lid, []) -> begin
(FStar_Ident.lid_equals lid nil_lid)
end
| FStar_Parser_AST.Construct (lid, (_67_87)::((e2, _67_84))::[]) -> begin
((FStar_Ident.lid_equals lid cons_lid) && (aux e2))
end
| _67_92 -> begin
false
end))
in aux))


let is_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Syntax_Const.cons_lid FStar_Syntax_Const.nil_lid)


let is_lex_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Syntax_Const.lexcons_lid FStar_Syntax_Const.lextop_lid)


let rec extract_from_list : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (match ((let _165_122 = (unparen e)
in _165_122.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Construct (_67_95, []) -> begin
[]
end
| FStar_Parser_AST.Construct (_67_100, ((e1, FStar_Parser_AST.Nothing))::((e2, FStar_Parser_AST.Nothing))::[]) -> begin
(let _165_123 = (extract_from_list e2)
in (e1)::_165_123)
end
| _67_111 -> begin
(let _165_125 = (let _165_124 = (FStar_Parser_AST.term_to_string e)
in (FStar_Util.format1 "Not a list %s" _165_124))
in (failwith _165_125))
end))


let is_array : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match ((let _165_128 = (unparen e)
in _165_128.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (lid); FStar_Parser_AST.range = _67_116; FStar_Parser_AST.level = _67_114}, l, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals lid FStar_Syntax_Const.array_mk_array_lid) && (is_list l))
end
| _67_125 -> begin
false
end))


let rec is_ref_set : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match ((let _165_131 = (unparen e)
in _165_131.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Var (maybe_empty_lid) -> begin
(FStar_Ident.lid_equals maybe_empty_lid FStar_Syntax_Const.tset_empty)
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_singleton_lid); FStar_Parser_AST.range = _67_132; FStar_Parser_AST.level = _67_130}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_ref_lid); FStar_Parser_AST.range = _67_143; FStar_Parser_AST.level = _67_141}, e, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = _67_139; FStar_Parser_AST.level = _67_137}, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals maybe_singleton_lid FStar_Syntax_Const.tset_singleton) && (FStar_Ident.lid_equals maybe_ref_lid FStar_Syntax_Const.heap_ref))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_union_lid); FStar_Parser_AST.range = _67_162; FStar_Parser_AST.level = _67_160}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = _67_158; FStar_Parser_AST.level = _67_156}, e2, FStar_Parser_AST.Nothing) -> begin
(((FStar_Ident.lid_equals maybe_union_lid FStar_Syntax_Const.tset_union) && (is_ref_set e1)) && (is_ref_set e2))
end
| _67_176 -> begin
false
end))


let rec extract_from_ref_set : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (match ((let _165_134 = (unparen e)
in _165_134.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Var (_67_179) -> begin
[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (_67_186); FStar_Parser_AST.range = _67_184; FStar_Parser_AST.level = _67_182}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (_67_198); FStar_Parser_AST.range = _67_196; FStar_Parser_AST.level = _67_194}, e, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = _67_192; FStar_Parser_AST.level = _67_190}, FStar_Parser_AST.Nothing) -> begin
(e)::[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (_67_218); FStar_Parser_AST.range = _67_216; FStar_Parser_AST.level = _67_214}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = _67_212; FStar_Parser_AST.level = _67_210}, e2, FStar_Parser_AST.Nothing) -> begin
(let _165_136 = (extract_from_ref_set e1)
in (let _165_135 = (extract_from_ref_set e2)
in (FStar_List.append _165_136 _165_135)))
end
| _67_231 -> begin
(let _165_138 = (let _165_137 = (FStar_Parser_AST.term_to_string e)
in (FStar_Util.format1 "Not a ref set %s" _165_137))
in (failwith _165_138))
end))


let is_general_application : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (not (((is_array e) || (is_ref_set e)))))


let is_general_construction : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (not (((is_list e) || (is_lex_list e)))))


let is_general_prefix_op : Prims.string  ->  Prims.bool = (fun op -> (op <> "~"))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun e -> (

let rec aux = (fun e acc -> (match ((let _165_151 = (unparen e)
in _165_151.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (head, arg, imp) -> begin
(aux head ((((arg), (imp)))::acc))
end
| _67_245 -> begin
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


let matches_level = (fun s _67_260 -> (match (_67_260) with
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
in (FStar_List.mapi (fun i _67_270 -> (match (_67_270) with
| (assoc, tokens) -> begin
(((levels_from_associativity i assoc)), (tokens))
end)) level_associativity_spec))


let assign_levels : associativity_level Prims.list  ->  Prims.string  ->  (Prims.int * Prims.int * Prims.int) = (fun token_associativity_spec s -> (match ((FStar_List.tryFind (matches_level s) level_table)) with
| Some (assoc_levels, _67_275) -> begin
assoc_levels
end
| _67_279 -> begin
(failwith (Prims.strcat "Unrecognized operator " s))
end))


let max : Prims.int  ->  Prims.int  ->  Prims.int = (fun k1 k2 -> if (k1 > k2) then begin
k1
end else begin
k2
end)


let max_level = (fun l -> (

let find_level_and_max = (fun n level -> (match ((FStar_List.tryFind (fun _67_289 -> (match (_67_289) with
| (_67_287, tokens) -> begin
(tokens = (Prims.snd level))
end)) level_table)) with
| Some ((_67_291, l, _67_294), _67_297) -> begin
(max n l)
end
| None -> begin
(let _165_185 = (let _165_184 = (let _165_183 = (FStar_List.map token_to_string (Prims.snd level))
in (FStar_String.concat "," _165_183))
in (FStar_Util.format1 "Undefined associativity level %s" _165_184))
in (failwith _165_185))
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

let _67_317 = (FStar_ST.op_Colon_Equals comment_stack cs)
in (let _165_205 = (let _165_204 = (let _165_203 = (str comment)
in (FStar_Pprint.op_Hat_Hat _165_203 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat acc _165_204))
in (comments_before_pos _165_205 print_pos lookahead_pos)))
end else begin
(let _165_206 = (FStar_Range.range_before_pos crange lookahead_pos)
in ((acc), (_165_206)))
end
end))
in (

let _67_321 = (let _165_209 = (let _165_207 = (FStar_Range.start_of_range tmrange)
in (FStar_Range.end_of_line _165_207))
in (let _165_208 = (FStar_Range.end_of_range tmrange)
in (comments_before_pos FStar_Pprint.empty _165_209 _165_208)))
in (match (_67_321) with
| (comments, has_lookahead) -> begin
(

let printed_e = (printer tm)
in (

let comments = if has_lookahead then begin
(

let pos = (FStar_Range.end_of_range tmrange)
in (let _165_210 = (comments_before_pos comments pos pos)
in (Prims.fst _165_210)))
end else begin
comments
end
in (let _165_211 = (FStar_Pprint.op_Hat_Hat comments printed_e)
in (FStar_Pprint.group _165_211))))
end))))


let rec p_decl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (let _165_322 = (let _165_321 = (FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc)
in (let _165_320 = (let _165_319 = (p_attributes d.FStar_Parser_AST.attrs)
in (let _165_318 = (let _165_317 = (p_qualifiers d.FStar_Parser_AST.quals)
in (let _165_316 = (let _165_315 = (p_rawDecl d)
in (FStar_Pprint.op_Hat_Hat (if (d.FStar_Parser_AST.quals = []) then begin
FStar_Pprint.empty
end else begin
break1
end) _165_315))
in (FStar_Pprint.op_Hat_Hat _165_317 _165_316)))
in (FStar_Pprint.op_Hat_Hat _165_319 _165_318)))
in (FStar_Pprint.op_Hat_Hat _165_321 _165_320)))
in (FStar_Pprint.group _165_322)))
and p_attributes : FStar_Parser_AST.attributes_  ->  FStar_Pprint.document = (fun attrs -> (let _165_326 = (let _165_324 = (str "@")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket _165_324))
in (let _165_325 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline)
in (FStar_Pprint.surround_separate_map (Prims.parse_int "0") (Prims.parse_int "2") FStar_Pprint.empty _165_326 FStar_Pprint.space _165_325 p_atomicTerm attrs))))
and p_fsdoc : FStar_Parser_AST.fsdoc  ->  FStar_Pprint.document = (fun _67_329 -> (match (_67_329) with
| (doc, kwd_args) -> begin
(

let kwd_args_doc = (match (kwd_args) with
| [] -> begin
FStar_Pprint.empty
end
| kwd_args -> begin
(

let process_kwd_arg = (fun _67_335 -> (match (_67_335) with
| (kwd, arg) -> begin
(let _165_334 = (str "@")
in (let _165_333 = (let _165_332 = (str kwd)
in (let _165_331 = (let _165_330 = (str arg)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_330))
in (FStar_Pprint.op_Hat_Hat _165_332 _165_331)))
in (FStar_Pprint.op_Hat_Hat _165_334 _165_333)))
end))
in (let _165_336 = (let _165_335 = (FStar_Pprint.separate_map FStar_Pprint.hardline process_kwd_arg kwd_args)
in (FStar_Pprint.op_Hat_Hat _165_335 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline _165_336)))
end)
in (let _165_344 = (let _165_343 = (let _165_342 = (let _165_341 = (let _165_340 = (str doc)
in (let _165_339 = (let _165_338 = (let _165_337 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _165_337))
in (FStar_Pprint.op_Hat_Hat kwd_args_doc _165_338))
in (FStar_Pprint.op_Hat_Hat _165_340 _165_339)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _165_341))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _165_342))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_343))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline _165_344)))
end))
and p_rawDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Open (uid) -> begin
(let _165_348 = (let _165_347 = (str "open")
in (let _165_346 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat _165_347 _165_346)))
in (FStar_Pprint.group _165_348))
end
| FStar_Parser_AST.Include (uid) -> begin
(let _165_351 = (let _165_350 = (str "include")
in (let _165_349 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat _165_350 _165_349)))
in (FStar_Pprint.group _165_351))
end
| FStar_Parser_AST.ModuleAbbrev (uid1, uid2) -> begin
(let _165_358 = (let _165_356 = (str "module")
in (let _165_355 = (let _165_354 = (let _165_353 = (p_uident uid1)
in (let _165_352 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _165_353 _165_352)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_354))
in (FStar_Pprint.op_Hat_Hat _165_356 _165_355)))
in (let _165_357 = (p_quident uid2)
in (op_Hat_Slash_Plus_Hat _165_358 _165_357)))
end
| FStar_Parser_AST.TopLevelModule (uid) -> begin
(let _165_362 = (let _165_361 = (str "module")
in (let _165_360 = (let _165_359 = (p_quident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_359))
in (FStar_Pprint.op_Hat_Hat _165_361 _165_360)))
in (FStar_Pprint.group _165_362))
end
| FStar_Parser_AST.KindAbbrev (_67_349) -> begin
(failwith "Deprecated, please stop throwing your old stuff at me !")
end
| FStar_Parser_AST.Tycon (true, ((FStar_Parser_AST.TyconAbbrev (uid, tpars, None, t), None))::[]) -> begin
(

let effect_prefix_doc = (let _165_365 = (str "effect")
in (let _165_364 = (let _165_363 = (p_uident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_363))
in (FStar_Pprint.op_Hat_Hat _165_365 _165_364)))
in (let _165_368 = (let _165_366 = (p_typars tpars)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") effect_prefix_doc _165_366 FStar_Pprint.equals))
in (let _165_367 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _165_368 _165_367))))
end
| FStar_Parser_AST.Tycon (false, tcdefs) -> begin
(let _165_370 = (str "type")
in (let _165_369 = (str "and")
in (precede_break_separate_map _165_370 _165_369 p_fsdocTypeDeclPairs tcdefs)))
end
| FStar_Parser_AST.TopLevelLet (q, lbs) -> begin
(

let let_doc = (let _165_372 = (str "let")
in (let _165_371 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat _165_372 _165_371)))
in (let _165_373 = (str "and")
in (precede_break_separate_map let_doc _165_373 p_letbinding lbs)))
end
| FStar_Parser_AST.Val (lid, t) -> begin
(let _165_380 = (let _165_378 = (str "val")
in (let _165_377 = (let _165_376 = (let _165_375 = (p_lident lid)
in (let _165_374 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat _165_375 _165_374)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_376))
in (FStar_Pprint.op_Hat_Hat _165_378 _165_377)))
in (let _165_379 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _165_380 _165_379)))
end
| FStar_Parser_AST.Assume (id, t) -> begin
(

let decl_keyword = if (let _165_381 = (FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_All.pipe_right _165_381 FStar_Util.is_upper)) then begin
FStar_Pprint.empty
end else begin
(let _165_382 = (str "val")
in (FStar_Pprint.op_Hat_Hat _165_382 FStar_Pprint.space))
end
in (let _165_387 = (let _165_385 = (let _165_384 = (p_ident id)
in (let _165_383 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat _165_384 _165_383)))
in (FStar_Pprint.op_Hat_Hat decl_keyword _165_385))
in (let _165_386 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _165_387 _165_386))))
end
| FStar_Parser_AST.Exception (uid, t_opt) -> begin
(let _165_395 = (str "exception")
in (let _165_394 = (let _165_393 = (let _165_392 = (p_uident uid)
in (let _165_391 = (FStar_Pprint.optional (fun t -> (let _165_390 = (str "of")
in (let _165_389 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _165_390 _165_389)))) t_opt)
in (FStar_Pprint.op_Hat_Hat _165_392 _165_391)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_393))
in (FStar_Pprint.op_Hat_Hat _165_395 _165_394)))
end
| FStar_Parser_AST.NewEffect (ne) -> begin
(let _165_398 = (str "new_effect")
in (let _165_397 = (let _165_396 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_396))
in (FStar_Pprint.op_Hat_Hat _165_398 _165_397)))
end
| FStar_Parser_AST.SubEffect (se) -> begin
(let _165_401 = (str "sub_effect")
in (let _165_400 = (let _165_399 = (p_subEffect se)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_399))
in (FStar_Pprint.op_Hat_Hat _165_401 _165_400)))
end
| FStar_Parser_AST.NewEffectForFree (ne) -> begin
(let _165_404 = (str "new_effect_for_free")
in (let _165_403 = (let _165_402 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_402))
in (FStar_Pprint.op_Hat_Hat _165_404 _165_403)))
end
| FStar_Parser_AST.Pragma (p) -> begin
(p_pragma p)
end
| FStar_Parser_AST.Fsdoc (doc) -> begin
(let _165_405 = (p_fsdoc doc)
in (FStar_Pprint.op_Hat_Hat _165_405 FStar_Pprint.hardline))
end
| FStar_Parser_AST.Main (_67_398) -> begin
(failwith "*Main declaration* : Is that really still in use ??")
end
| FStar_Parser_AST.Tycon (true, _67_402) -> begin
(failwith "Effect abbreviation is expected to be defined by an abbreviation")
end))
and p_pragma : FStar_Parser_AST.pragma  ->  FStar_Pprint.document = (fun _67_4 -> (match (_67_4) with
| FStar_Parser_AST.SetOptions (s) -> begin
(let _165_410 = (str "#set-options")
in (let _165_409 = (let _165_408 = (let _165_407 = (str s)
in (FStar_Pprint.dquotes _165_407))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_408))
in (FStar_Pprint.op_Hat_Hat _165_410 _165_409)))
end
| FStar_Parser_AST.ResetOptions (s_opt) -> begin
(let _165_415 = (str "#reset-options")
in (let _165_414 = (FStar_Pprint.optional (fun s -> (let _165_413 = (let _165_412 = (str s)
in (FStar_Pprint.dquotes _165_412))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_413))) s_opt)
in (FStar_Pprint.op_Hat_Hat _165_415 _165_414)))
end))
and p_typars : FStar_Parser_AST.binder Prims.list  ->  FStar_Pprint.document = (fun bs -> (p_binders true bs))
and p_fsdocTypeDeclPairs : (FStar_Parser_AST.tycon * FStar_Parser_AST.fsdoc Prims.option)  ->  FStar_Pprint.document = (fun _67_414 -> (match (_67_414) with
| (typedecl, fsdoc_opt) -> begin
(let _165_419 = (FStar_Pprint.optional p_fsdoc fsdoc_opt)
in (let _165_418 = (p_typeDecl typedecl)
in (FStar_Pprint.op_Hat_Hat _165_419 _165_418)))
end))
and p_typeDecl : FStar_Parser_AST.tycon  ->  FStar_Pprint.document = (fun _67_5 -> (match (_67_5) with
| FStar_Parser_AST.TyconAbstract (lid, bs, typ_opt) -> begin
(

let empty' = (fun _67_421 -> (match (()) with
| () -> begin
FStar_Pprint.empty
end))
in (p_typeDeclPrefix lid bs typ_opt empty'))
end
| FStar_Parser_AST.TyconAbbrev (lid, bs, typ_opt, t) -> begin
(

let f = (fun _67_430 -> (match (()) with
| () -> begin
(let _165_425 = (p_typ t)
in (prefix2 FStar_Pprint.equals _165_425))
end))
in (p_typeDeclPrefix lid bs typ_opt f))
end
| FStar_Parser_AST.TyconRecord (lid, bs, typ_opt, record_field_decls) -> begin
(

let p_recordFieldAndComments = (fun _67_441 -> (match (_67_441) with
| (lid, t, doc_opt) -> begin
(let _165_428 = (FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range)
in (with_comment p_recordFieldDecl ((lid), (t), (doc_opt)) _165_428))
end))
in (

let p_fields = (fun _67_443 -> (match (()) with
| () -> begin
(let _165_434 = (let _165_433 = (let _165_432 = (let _165_431 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (FStar_Pprint.separate_map _165_431 p_recordFieldAndComments record_field_decls))
in (braces_with_nesting _165_432))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_433))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.equals _165_434))
end))
in (p_typeDeclPrefix lid bs typ_opt p_fields)))
end
| FStar_Parser_AST.TyconVariant (lid, bs, typ_opt, ct_decls) -> begin
(

let p_constructorBranchAndComments = (fun _67_455 -> (match (_67_455) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let range = (let _165_439 = (let _165_438 = (FStar_Util.map_opt t_opt (fun t -> t.FStar_Parser_AST.range))
in (FStar_Util.dflt uid.FStar_Ident.idRange _165_438))
in (FStar_Range.extend_to_end_of_line _165_439))
in (

let p_constructorBranch = (fun decl -> (let _165_444 = (let _165_443 = (let _165_442 = (p_constructorDecl decl)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_442))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar _165_443))
in (FStar_Pprint.group _165_444)))
in (with_comment p_constructorBranch ((uid), (t_opt), (doc_opt), (use_of)) range)))
end))
in (

let datacon_doc = (fun _67_461 -> (match (()) with
| () -> begin
(let _165_447 = (FStar_Pprint.separate_map break1 p_constructorBranchAndComments ct_decls)
in (FStar_Pprint.group _165_447))
end))
in (p_typeDeclPrefix lid bs typ_opt (fun _67_462 -> (match (()) with
| () -> begin
(let _165_449 = (datacon_doc ())
in (prefix2 FStar_Pprint.equals _165_449))
end)))))
end))
and p_typeDeclPrefix : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.knd Prims.option  ->  (Prims.unit  ->  FStar_Pprint.document)  ->  FStar_Pprint.document = (fun lid bs typ_opt cont -> if ((bs = []) && (typ_opt = None)) then begin
(let _165_459 = (p_ident lid)
in (let _165_458 = (let _165_457 = (cont ())
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_457))
in (FStar_Pprint.op_Hat_Hat _165_459 _165_458)))
end else begin
(

let binders_doc = (let _165_465 = (p_typars bs)
in (let _165_464 = (FStar_Pprint.optional (fun t -> (let _165_463 = (let _165_462 = (let _165_461 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_461))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_462))
in (FStar_Pprint.op_Hat_Hat break1 _165_463))) typ_opt)
in (FStar_Pprint.op_Hat_Hat _165_465 _165_464)))
in (let _165_467 = (p_ident lid)
in (let _165_466 = (cont ())
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_467 binders_doc _165_466))))
end)
and p_recordFieldDecl : (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc Prims.option)  ->  FStar_Pprint.document = (fun _67_472 -> (match (_67_472) with
| (lid, t, doc_opt) -> begin
(let _165_474 = (let _165_473 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (let _165_472 = (let _165_471 = (p_lident lid)
in (let _165_470 = (let _165_469 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_469))
in (FStar_Pprint.op_Hat_Hat _165_471 _165_470)))
in (FStar_Pprint.op_Hat_Hat _165_473 _165_472)))
in (FStar_Pprint.group _165_474))
end))
and p_constructorDecl : (FStar_Ident.ident * FStar_Parser_AST.term Prims.option * FStar_Parser_AST.fsdoc Prims.option * Prims.bool)  ->  FStar_Pprint.document = (fun _67_477 -> (match (_67_477) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let sep = if use_of then begin
(str "of")
end else begin
FStar_Pprint.colon
end
in (

let uid_doc = (p_uident uid)
in (let _165_481 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (let _165_480 = (default_or_map uid_doc (fun t -> (let _165_479 = (let _165_477 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep)
in (FStar_Pprint.op_Hat_Hat uid_doc _165_477))
in (let _165_478 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _165_479 _165_478)))) t_opt)
in (FStar_Pprint.op_Hat_Hat _165_481 _165_480)))))
end))
and p_letbinding : (FStar_Parser_AST.pattern * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun _67_483 -> (match (_67_483) with
| (pat, e) -> begin
(

let pat_doc = (

let _67_492 = (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, t) -> begin
(let _165_487 = (let _165_486 = (let _165_485 = (let _165_484 = (let _165_483 = (p_tmArrow p_tmNoEq t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_483))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_484))
in (FStar_Pprint.group _165_485))
in (FStar_Pprint.op_Hat_Hat break1 _165_486))
in ((pat), (_165_487)))
end
| _67_489 -> begin
((pat), (FStar_Pprint.empty))
end)
in (match (_67_492) with
| (pat, ascr_doc) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _67_497); FStar_Parser_AST.prange = _67_494}, pats) -> begin
(let _165_490 = (p_lident x)
in (let _165_489 = (let _165_488 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Hat _165_488 ascr_doc))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_490 _165_489 FStar_Pprint.equals)))
end
| _67_505 -> begin
(let _165_493 = (let _165_492 = (p_tuplePattern pat)
in (let _165_491 = (FStar_Pprint.op_Hat_Slash_Hat ascr_doc FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _165_492 _165_491)))
in (FStar_Pprint.group _165_493))
end)
end))
in (let _165_494 = (p_term e)
in (prefix2 pat_doc _165_494)))
end))
and p_newEffect : FStar_Parser_AST.effect_decl  ->  FStar_Pprint.document = (fun _67_6 -> (match (_67_6) with
| FStar_Parser_AST.RedefineEffect (lid, bs, t) -> begin
(p_effectRedefinition lid bs t)
end
| FStar_Parser_AST.DefineEffect (lid, bs, t, eff_decls, action_decls) -> begin
(p_effectDefinition lid bs t eff_decls action_decls)
end))
and p_effectRedefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun uid bs t -> (let _165_502 = (p_uident uid)
in (let _165_501 = (p_binders true bs)
in (let _165_500 = (let _165_499 = (p_simpleTerm t)
in (prefix2 FStar_Pprint.equals _165_499))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_502 _165_501 _165_500)))))
and p_effectDefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun uid bs t eff_decls action_decls -> (let _165_519 = (let _165_518 = (let _165_512 = (let _165_511 = (p_uident uid)
in (let _165_510 = (p_binders true bs)
in (let _165_509 = (let _165_508 = (p_typ t)
in (prefix2 FStar_Pprint.colon _165_508))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_511 _165_510 _165_509))))
in (FStar_Pprint.group _165_512))
in (let _165_517 = (let _165_516 = (let _165_514 = (str "with")
in (let _165_513 = (separate_break_map FStar_Pprint.semi p_effectDecl eff_decls)
in (prefix2 _165_514 _165_513)))
in (let _165_515 = (p_actionDecls action_decls)
in (FStar_Pprint.op_Hat_Hat _165_516 _165_515)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_518 _165_517)))
in (braces_with_nesting _165_519)))
and p_actionDecls : FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun _67_7 -> (match (_67_7) with
| [] -> begin
FStar_Pprint.empty
end
| l -> begin
(let _165_523 = (let _165_522 = (str "and actions")
in (let _165_521 = (separate_break_map FStar_Pprint.semi p_effectDecl l)
in (prefix2 _165_522 _165_521)))
in (FStar_Pprint.op_Hat_Hat break1 _165_523))
end))
and p_effectDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (false, ((FStar_Parser_AST.TyconAbbrev (lid, [], None, e), None))::[]) -> begin
(let _165_528 = (let _165_526 = (p_lident lid)
in (let _165_525 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _165_526 _165_525)))
in (let _165_527 = (p_simpleTerm e)
in (prefix2 _165_528 _165_527)))
end
| _67_545 -> begin
(let _165_530 = (let _165_529 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "Not a declaration of an effect member... or at least I hope so : %s" _165_529))
in (failwith _165_530))
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

let p_lift = (fun _67_559 -> (match (_67_559) with
| (kwd, t) -> begin
(let _165_537 = (let _165_535 = (str kwd)
in (let _165_534 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _165_535 _165_534)))
in (let _165_536 = (p_simpleTerm t)
in (prefix2 _165_537 _165_536)))
end))
in (separate_break_map FStar_Pprint.semi p_lift lifts)))
in (let _165_545 = (let _165_542 = (let _165_540 = (p_quident lift.FStar_Parser_AST.msource)
in (let _165_539 = (let _165_538 = (str "~>")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_538))
in (FStar_Pprint.op_Hat_Hat _165_540 _165_539)))
in (let _165_541 = (p_quident lift.FStar_Parser_AST.mdest)
in (prefix2 _165_542 _165_541)))
in (let _165_544 = (let _165_543 = (braces_with_nesting lift_op_doc)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_543))
in (FStar_Pprint.op_Hat_Hat _165_545 _165_544)))))
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
and p_qualifiers : FStar_Parser_AST.qualifiers  ->  FStar_Pprint.document = (fun qs -> (let _165_548 = (FStar_Pprint.separate_map break1 p_qualifier qs)
in (FStar_Pprint.group _165_548)))
and p_letqualifier : FStar_Parser_AST.let_qualifier  ->  FStar_Pprint.document = (fun _67_9 -> (match (_67_9) with
| FStar_Parser_AST.Rec -> begin
(let _165_550 = (str "rec")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_550))
end
| FStar_Parser_AST.Mutable -> begin
(let _165_551 = (str "mutable")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_551))
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
(let _165_556 = (let _165_555 = (let _165_554 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space)
in (FStar_Pprint.op_Hat_Hat break1 _165_554))
in (FStar_Pprint.separate_map _165_555 p_tuplePattern pats))
in (FStar_Pprint.group _165_556))
end
| _67_593 -> begin
(p_tuplePattern p)
end))
and p_tuplePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTuple (pats, false) -> begin
(let _165_559 = (let _165_558 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map _165_558 p_constructorPattern pats))
in (FStar_Pprint.group _165_559))
end
| _67_600 -> begin
(p_constructorPattern p)
end))
and p_constructorPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (maybe_cons_lid); FStar_Parser_AST.prange = _67_603}, (hd)::(tl)::[]) when (FStar_Ident.lid_equals maybe_cons_lid FStar_Syntax_Const.cons_lid) -> begin
(let _165_563 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon)
in (let _165_562 = (p_constructorPattern hd)
in (let _165_561 = (p_constructorPattern tl)
in (infix0 _165_563 _165_562 _165_561))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (uid); FStar_Parser_AST.prange = _67_613}, pats) -> begin
(let _165_565 = (p_quident uid)
in (let _165_564 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (prefix2 _165_565 _165_564)))
end
| _67_621 -> begin
(p_atomicPattern p)
end))
and p_atomicPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, t) -> begin
(match ((let _165_568 = (let _165_567 = (unparen t)
in _165_567.FStar_Parser_AST.tm)
in ((pat.FStar_Parser_AST.pat), (_165_568)))) with
| (FStar_Parser_AST.PatVar (lid, aqual), FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t); FStar_Parser_AST.brange = _67_636; FStar_Parser_AST.blevel = _67_634; FStar_Parser_AST.aqual = _67_632}, phi)) when (lid.FStar_Ident.idText = lid'.FStar_Ident.idText) -> begin
(let _165_570 = (let _165_569 = (p_ident lid)
in (p_refinement aqual _165_569 t phi))
in (soft_parens_with_nesting _165_570))
end
| (FStar_Parser_AST.PatWild, FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t); FStar_Parser_AST.brange = _67_652; FStar_Parser_AST.blevel = _67_650; FStar_Parser_AST.aqual = _67_648}, phi)) -> begin
(let _165_571 = (p_refinement None FStar_Pprint.underscore t phi)
in (soft_parens_with_nesting _165_571))
end
| _67_661 -> begin
(let _165_577 = (let _165_576 = (p_tuplePattern pat)
in (let _165_575 = (let _165_574 = (FStar_Pprint.break_ (Prims.parse_int "0"))
in (let _165_573 = (let _165_572 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_572))
in (FStar_Pprint.op_Hat_Hat _165_574 _165_573)))
in (FStar_Pprint.op_Hat_Hat _165_576 _165_575)))
in (soft_parens_with_nesting _165_577))
end)
end
| FStar_Parser_AST.PatList (pats) -> begin
(let _165_578 = (separate_break_map FStar_Pprint.semi p_tuplePattern pats)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket _165_578 FStar_Pprint.rbracket))
end
| FStar_Parser_AST.PatRecord (pats) -> begin
(

let p_recordFieldPat = (fun _67_669 -> (match (_67_669) with
| (lid, pat) -> begin
(let _165_582 = (p_qlident lid)
in (let _165_581 = (p_tuplePattern pat)
in (infix2 FStar_Pprint.equals _165_582 _165_581)))
end))
in (let _165_583 = (separate_break_map FStar_Pprint.semi p_recordFieldPat pats)
in (soft_braces_with_nesting _165_583)))
end
| FStar_Parser_AST.PatTuple (pats, true) -> begin
(let _165_586 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (let _165_585 = (separate_break_map FStar_Pprint.comma p_constructorPattern pats)
in (let _165_584 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_586 _165_585 _165_584))))
end
| FStar_Parser_AST.PatTvar (tv, arg_qualifier_opt) -> begin
(

let _67_678 = ()
in (p_tvar tv))
end
| FStar_Parser_AST.PatOp (op) -> begin
(let _165_590 = (let _165_589 = (let _165_588 = (str op)
in (let _165_587 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat _165_588 _165_587)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_589))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_590))
end
| FStar_Parser_AST.PatWild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.PatConst (c) -> begin
(p_constant c)
end
| FStar_Parser_AST.PatVar (lid, aqual) -> begin
(let _165_592 = (FStar_Pprint.optional p_aqual aqual)
in (let _165_591 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat _165_592 _165_591)))
end
| FStar_Parser_AST.PatName (uid) -> begin
(p_quident uid)
end
| FStar_Parser_AST.PatOr (_67_692) -> begin
(failwith "Inner or pattern !")
end
| (FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (_); FStar_Parser_AST.prange = _}, _)) | (FStar_Parser_AST.PatTuple (_, false)) -> begin
(let _165_593 = (p_tuplePattern p)
in (soft_parens_with_nesting _165_593))
end
| _67_710 -> begin
(let _165_595 = (let _165_594 = (FStar_Parser_AST.pat_to_string p)
in (FStar_Util.format1 "Invalid pattern %s" _165_594))
in (failwith _165_595))
end))
and p_binder : Prims.bool  ->  FStar_Parser_AST.binder  ->  FStar_Pprint.document = (fun is_atomic b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (lid) -> begin
(let _165_599 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (let _165_598 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat _165_599 _165_598)))
end
| FStar_Parser_AST.TVariable (lid) -> begin
(p_lident lid)
end
| FStar_Parser_AST.Annotated (lid, t) -> begin
(

let doc = (match ((let _165_600 = (unparen t)
in _165_600.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t); FStar_Parser_AST.brange = _67_726; FStar_Parser_AST.blevel = _67_724; FStar_Parser_AST.aqual = _67_722}, phi) when (lid.FStar_Ident.idText = lid'.FStar_Ident.idText) -> begin
(let _165_601 = (p_ident lid)
in (p_refinement b.FStar_Parser_AST.aqual _165_601 t phi))
end
| _67_736 -> begin
(let _165_608 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (let _165_607 = (let _165_606 = (p_lident lid)
in (let _165_605 = (let _165_604 = (let _165_603 = (FStar_Pprint.break_ (Prims.parse_int "0"))
in (let _165_602 = (p_tmFormula t)
in (FStar_Pprint.op_Hat_Hat _165_603 _165_602)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_604))
in (FStar_Pprint.op_Hat_Hat _165_606 _165_605)))
in (FStar_Pprint.op_Hat_Hat _165_608 _165_607)))
end)
in if is_atomic then begin
(let _165_610 = (let _165_609 = (FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_609))
in (FStar_Pprint.group _165_610))
end else begin
(FStar_Pprint.group doc)
end)
end
| FStar_Parser_AST.TAnnotated (_67_739) -> begin
(failwith "Is this still used ?")
end
| FStar_Parser_AST.NoName (t) -> begin
(match ((let _165_611 = (unparen t)
in _165_611.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t); FStar_Parser_AST.brange = _67_748; FStar_Parser_AST.blevel = _67_746; FStar_Parser_AST.aqual = _67_744}, phi) -> begin
if is_atomic then begin
(let _165_614 = (let _165_613 = (let _165_612 = (p_refinement b.FStar_Parser_AST.aqual FStar_Pprint.underscore t phi)
in (FStar_Pprint.op_Hat_Hat _165_612 FStar_Pprint.rparen))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_613))
in (FStar_Pprint.group _165_614))
end else begin
(let _165_615 = (p_refinement b.FStar_Parser_AST.aqual FStar_Pprint.underscore t phi)
in (FStar_Pprint.group _165_615))
end
end
| _67_756 -> begin
if is_atomic then begin
(p_atomicTerm t)
end else begin
(p_appTerm t)
end
end)
end))
and p_refinement : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Pprint.document  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun aqual_opt binder t phi -> (let _165_626 = (FStar_Pprint.optional p_aqual aqual_opt)
in (let _165_625 = (let _165_624 = (let _165_623 = (let _165_622 = (p_appTerm t)
in (let _165_621 = (let _165_620 = (p_noSeqTerm phi)
in (soft_braces_with_nesting _165_620))
in (FStar_Pprint.op_Hat_Hat _165_622 _165_621)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_623))
in (FStar_Pprint.op_Hat_Hat binder _165_624))
in (FStar_Pprint.op_Hat_Hat _165_626 _165_625))))
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
and p_term : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _165_637 = (unparen e)
in _165_637.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Seq (e1, e2) -> begin
(let _165_641 = (let _165_639 = (let _165_638 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat _165_638 FStar_Pprint.semi))
in (FStar_Pprint.group _165_639))
in (let _165_640 = (p_term e2)
in (FStar_Pprint.op_Hat_Slash_Hat _165_641 _165_640)))
end
| _67_776 -> begin
(let _165_642 = (p_noSeqTerm e)
in (FStar_Pprint.group _165_642))
end))
and p_noSeqTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_noSeqTerm' e e.FStar_Parser_AST.range))
and p_noSeqTerm' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _165_645 = (unparen e)
in _165_645.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Ascribed (e, t) -> begin
(let _165_650 = (let _165_649 = (p_tmIff e)
in (let _165_648 = (let _165_647 = (let _165_646 = (p_typ t)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon _165_646))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.langle _165_647))
in (FStar_Pprint.op_Hat_Slash_Hat _165_649 _165_648)))
in (FStar_Pprint.group _165_650))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::(e3)::[]) when (op = ".()<-") -> begin
(let _165_661 = (let _165_660 = (let _165_657 = (let _165_656 = (p_atomicTermNotQUident e1)
in (let _165_655 = (let _165_654 = (let _165_653 = (let _165_651 = (p_term e2)
in (soft_parens_with_nesting _165_651))
in (let _165_652 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat _165_653 _165_652)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_654))
in (FStar_Pprint.op_Hat_Hat _165_656 _165_655)))
in (FStar_Pprint.group _165_657))
in (let _165_659 = (let _165_658 = (p_noSeqTerm e3)
in (jump2 _165_658))
in (FStar_Pprint.op_Hat_Hat _165_660 _165_659)))
in (FStar_Pprint.group _165_661))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::(e3)::[]) when (op = ".[]<-") -> begin
(let _165_672 = (let _165_671 = (let _165_668 = (let _165_667 = (p_atomicTermNotQUident e1)
in (let _165_666 = (let _165_665 = (let _165_664 = (let _165_662 = (p_term e2)
in (soft_brackets_with_nesting _165_662))
in (let _165_663 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat _165_664 _165_663)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_665))
in (FStar_Pprint.op_Hat_Hat _165_667 _165_666)))
in (FStar_Pprint.group _165_668))
in (let _165_670 = (let _165_669 = (p_noSeqTerm e3)
in (jump2 _165_669))
in (FStar_Pprint.op_Hat_Hat _165_671 _165_670)))
in (FStar_Pprint.group _165_672))
end
| FStar_Parser_AST.Requires (e, wtf) -> begin
(

let _67_801 = ()
in (let _165_675 = (let _165_674 = (str "requires")
in (let _165_673 = (p_typ e)
in (FStar_Pprint.op_Hat_Slash_Hat _165_674 _165_673)))
in (FStar_Pprint.group _165_675)))
end
| FStar_Parser_AST.Ensures (e, wtf) -> begin
(

let _67_807 = ()
in (let _165_678 = (let _165_677 = (str "ensures")
in (let _165_676 = (p_typ e)
in (FStar_Pprint.op_Hat_Slash_Hat _165_677 _165_676)))
in (FStar_Pprint.group _165_678)))
end
| FStar_Parser_AST.Attributes (es) -> begin
(let _165_681 = (let _165_680 = (str "attributes")
in (let _165_679 = (FStar_Pprint.separate_map break1 p_atomicTerm es)
in (FStar_Pprint.op_Hat_Slash_Hat _165_680 _165_679)))
in (FStar_Pprint.group _165_681))
end
| FStar_Parser_AST.If (e1, e2, e3) -> begin
if (is_unit e3) then begin
(let _165_688 = (let _165_687 = (let _165_683 = (str "if")
in (let _165_682 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat _165_683 _165_682)))
in (let _165_686 = (let _165_685 = (str "then")
in (let _165_684 = (p_noSeqTerm e2)
in (op_Hat_Slash_Plus_Hat _165_685 _165_684)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_687 _165_686)))
in (FStar_Pprint.group _165_688))
end else begin
(

let e2_doc = (match ((let _165_689 = (unparen e2)
in _165_689.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.If (_67_817, _67_819, e3) when (is_unit e3) -> begin
(let _165_690 = (p_noSeqTerm e2)
in (soft_parens_with_nesting _165_690))
end
| _67_824 -> begin
(p_noSeqTerm e2)
end)
in (let _165_700 = (let _165_699 = (let _165_692 = (str "if")
in (let _165_691 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat _165_692 _165_691)))
in (let _165_698 = (let _165_697 = (let _165_693 = (str "then")
in (op_Hat_Slash_Plus_Hat _165_693 e2_doc))
in (let _165_696 = (let _165_695 = (str "else")
in (let _165_694 = (p_noSeqTerm e3)
in (op_Hat_Slash_Plus_Hat _165_695 _165_694)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_697 _165_696)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_699 _165_698)))
in (FStar_Pprint.group _165_700)))
end
end
| FStar_Parser_AST.TryWith (e, branches) -> begin
(let _165_707 = (let _165_706 = (let _165_702 = (str "try")
in (let _165_701 = (p_noSeqTerm e)
in (prefix2 _165_702 _165_701)))
in (let _165_705 = (let _165_704 = (str "with")
in (let _165_703 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat _165_704 _165_703)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_706 _165_705)))
in (FStar_Pprint.group _165_707))
end
| FStar_Parser_AST.Match (e, branches) -> begin
(let _165_713 = (let _165_712 = (let _165_710 = (str "match")
in (let _165_709 = (p_noSeqTerm e)
in (let _165_708 = (str "with")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_710 _165_709 _165_708))))
in (let _165_711 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat _165_712 _165_711)))
in (FStar_Pprint.group _165_713))
end
| FStar_Parser_AST.LetOpen (uid, e) -> begin
(let _165_719 = (let _165_718 = (let _165_716 = (str "let open")
in (let _165_715 = (p_quident uid)
in (let _165_714 = (str "in")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_716 _165_715 _165_714))))
in (let _165_717 = (p_term e)
in (FStar_Pprint.op_Hat_Slash_Hat _165_718 _165_717)))
in (FStar_Pprint.group _165_719))
end
| FStar_Parser_AST.Let (q, lbs, e) -> begin
(

let let_doc = (let _165_721 = (str "let")
in (let _165_720 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat _165_721 _165_720)))
in (let _165_727 = (let _165_725 = (let _165_724 = (let _165_722 = (str "and")
in (precede_break_separate_map let_doc _165_722 p_letbinding lbs))
in (let _165_723 = (str "in")
in (FStar_Pprint.op_Hat_Slash_Hat _165_724 _165_723)))
in (FStar_Pprint.group _165_725))
in (let _165_726 = (p_term e)
in (FStar_Pprint.op_Hat_Slash_Hat _165_727 _165_726))))
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, typ_opt); FStar_Parser_AST.prange = _67_845})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, branches); FStar_Parser_AST.range = _67_855; FStar_Parser_AST.level = _67_853}) when (matches_var maybe_x x) -> begin
(let _165_730 = (let _165_729 = (str "function")
in (let _165_728 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat _165_729 _165_728)))
in (FStar_Pprint.group _165_730))
end
| FStar_Parser_AST.Assign (id, e) -> begin
(let _165_734 = (let _165_733 = (p_lident id)
in (let _165_732 = (let _165_731 = (p_noSeqTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow _165_731))
in (FStar_Pprint.op_Hat_Slash_Hat _165_733 _165_732)))
in (FStar_Pprint.group _165_734))
end
| _67_868 -> begin
(p_typ e)
end))
and p_typ : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_typ' e e.FStar_Parser_AST.range))
and p_typ' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _165_737 = (unparen e)
in _165_737.FStar_Parser_AST.tm)) with
| (FStar_Parser_AST.QForall (bs, trigger, e1)) | (FStar_Parser_AST.QExists (bs, trigger, e1)) -> begin
(let _165_744 = (let _165_740 = (let _165_738 = (p_quantifier e)
in (FStar_Pprint.op_Hat_Hat _165_738 FStar_Pprint.space))
in (let _165_739 = (p_binders true bs)
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") _165_740 _165_739 FStar_Pprint.dot)))
in (let _165_743 = (let _165_742 = (p_trigger trigger)
in (let _165_741 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat _165_742 _165_741)))
in (prefix2 _165_744 _165_743)))
end
| _67_879 -> begin
(p_simpleTerm e)
end))
and p_quantifier : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _165_746 = (unparen e)
in _165_746.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.QForall (_67_882) -> begin
(str "forall")
end
| FStar_Parser_AST.QExists (_67_885) -> begin
(str "exists")
end
| _67_888 -> begin
(failwith "Imposible : p_quantifier called on a non-quantifier term")
end))
and p_trigger : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun _67_11 -> (match (_67_11) with
| [] -> begin
FStar_Pprint.empty
end
| pats -> begin
(let _165_754 = (let _165_753 = (let _165_752 = (str "pattern")
in (let _165_751 = (let _165_750 = (let _165_748 = (p_disjunctivePats pats)
in (jump2 _165_748))
in (let _165_749 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1)
in (FStar_Pprint.op_Hat_Slash_Hat _165_750 _165_749)))
in (FStar_Pprint.op_Hat_Slash_Hat _165_752 _165_751)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_753))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace _165_754))
end))
and p_disjunctivePats : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun pats -> (let _165_756 = (str "\\/")
in (FStar_Pprint.separate_map _165_756 p_conjunctivePats pats)))
and p_conjunctivePats : FStar_Parser_AST.term Prims.list  ->  FStar_Pprint.document = (fun pats -> (let _165_758 = (FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats)
in (FStar_Pprint.group _165_758)))
and p_simpleTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _165_760 = (unparen e)
in _165_760.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Abs (pats, e) -> begin
(let _165_765 = (let _165_763 = (str "fun")
in (let _165_762 = (let _165_761 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Slash_Hat _165_761 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat _165_763 _165_762)))
in (let _165_764 = (p_term e)
in (op_Hat_Slash_Plus_Hat _165_765 _165_764)))
end
| _67_900 -> begin
(p_tmIff e)
end))
and p_maybeFocusArrow : Prims.bool  ->  FStar_Pprint.document = (fun b -> if b then begin
(str "~>")
end else begin
FStar_Pprint.rarrow
end)
and p_patternBranch : FStar_Parser_AST.branch  ->  FStar_Pprint.document = (fun _67_905 -> (match (_67_905) with
| (pat, when_opt, e) -> begin
(

let maybe_paren = (match ((let _165_770 = (unparen e)
in _165_770.FStar_Parser_AST.tm)) with
| (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) -> begin
soft_begin_end_with_nesting
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _67_916); FStar_Parser_AST.prange = _67_913})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, _67_927); FStar_Parser_AST.range = _67_924; FStar_Parser_AST.level = _67_922}) when (matches_var maybe_x x) -> begin
soft_begin_end_with_nesting
end
| _67_934 -> begin
(fun x -> x)
end)
in (let _165_781 = (let _165_780 = (let _165_777 = (let _165_776 = (let _165_775 = (let _165_774 = (p_disjunctivePattern pat)
in (let _165_773 = (let _165_772 = (p_maybeWhen when_opt)
in (FStar_Pprint.op_Hat_Hat _165_772 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat _165_774 _165_773)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_775))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar _165_776))
in (FStar_Pprint.group _165_777))
in (let _165_779 = (let _165_778 = (p_term e)
in (maybe_paren _165_778))
in (op_Hat_Slash_Plus_Hat _165_780 _165_779)))
in (FStar_Pprint.group _165_781)))
end))
and p_maybeWhen : FStar_Parser_AST.term Prims.option  ->  FStar_Pprint.document = (fun _67_12 -> (match (_67_12) with
| None -> begin
FStar_Pprint.empty
end
| Some (e) -> begin
(let _165_785 = (str "when")
in (let _165_784 = (let _165_783 = (p_tmFormula e)
in (FStar_Pprint.op_Hat_Hat _165_783 FStar_Pprint.space))
in (op_Hat_Slash_Plus_Hat _165_785 _165_784)))
end))
and p_tmIff : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _165_787 = (unparen e)
in _165_787.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Op ("<==>", (e1)::(e2)::[]) -> begin
(let _165_790 = (str "<==>")
in (let _165_789 = (p_tmImplies e1)
in (let _165_788 = (p_tmIff e2)
in (infix0 _165_790 _165_789 _165_788))))
end
| _67_949 -> begin
(p_tmImplies e)
end))
and p_tmImplies : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _165_792 = (unparen e)
in _165_792.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Op ("==>", (e1)::(e2)::[]) -> begin
(let _165_795 = (str "==>")
in (let _165_794 = (p_tmArrow p_tmFormula e1)
in (let _165_793 = (p_tmImplies e2)
in (infix0 _165_795 _165_794 _165_793))))
end
| _67_958 -> begin
(p_tmArrow p_tmFormula e)
end))
and p_tmArrow : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_Tm e -> (match ((let _165_801 = (unparen e)
in _165_801.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Product (bs, tgt) -> begin
(let _165_808 = (let _165_807 = (FStar_Pprint.concat_map (fun b -> (let _165_805 = (p_binder false b)
in (let _165_804 = (let _165_803 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_803))
in (FStar_Pprint.op_Hat_Hat _165_805 _165_804)))) bs)
in (let _165_806 = (p_tmArrow p_Tm tgt)
in (FStar_Pprint.op_Hat_Hat _165_807 _165_806)))
in (FStar_Pprint.group _165_808))
end
| _67_967 -> begin
(p_Tm e)
end))
and p_tmFormula : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _165_810 = (unparen e)
in _165_810.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Op ("\\/", (e1)::(e2)::[]) -> begin
(let _165_813 = (str "\\/")
in (let _165_812 = (p_tmFormula e1)
in (let _165_811 = (p_tmConjunction e2)
in (infix0 _165_813 _165_812 _165_811))))
end
| _67_976 -> begin
(p_tmConjunction e)
end))
and p_tmConjunction : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _165_815 = (unparen e)
in _165_815.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Op ("/\\", (e1)::(e2)::[]) -> begin
(let _165_818 = (str "/\\")
in (let _165_817 = (p_tmConjunction e1)
in (let _165_816 = (p_tmTuple e2)
in (infix0 _165_818 _165_817 _165_816))))
end
| _67_985 -> begin
(p_tmTuple e)
end))
and p_tmTuple : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _165_820 = (unparen e)
in _165_820.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Construct (lid, args) when (is_tuple_constructor lid) -> begin
(let _165_822 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map _165_822 (fun _67_994 -> (match (_67_994) with
| (e, _67_993) -> begin
(p_tmEq e)
end)) args))
end
| _67_996 -> begin
(p_tmEq e)
end))
and paren_if : Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun curr mine doc -> if (mine <= curr) then begin
doc
end else begin
(let _165_827 = (let _165_826 = (FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_826))
in (FStar_Pprint.group _165_827))
end)
and p_tmEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n = (max_level (FStar_List.append ((colon_equals)::(pipe_right)::[]) operatorInfix0ad12))
in (p_tmEq' n e)))
and p_tmEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (match ((let _165_831 = (unparen e)
in _165_831.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (((is_operatorInfix0ad12 op) || (op = "=")) || (op = "|>")) -> begin
(

let _67_1013 = (levels op)
in (match (_67_1013) with
| (left, mine, right) -> begin
(let _165_835 = (let _165_834 = (str op)
in (let _165_833 = (p_tmEq' left e1)
in (let _165_832 = (p_tmEq' right e2)
in (infix0 _165_834 _165_833 _165_832))))
in (paren_if curr mine _165_835))
end))
end
| FStar_Parser_AST.Op (":=", (e1)::(e2)::[]) -> begin
(let _165_841 = (let _165_840 = (p_tmEq e1)
in (let _165_839 = (let _165_838 = (let _165_837 = (let _165_836 = (p_tmEq e2)
in (op_Hat_Slash_Plus_Hat FStar_Pprint.equals _165_836))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _165_837))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_838))
in (FStar_Pprint.op_Hat_Hat _165_840 _165_839)))
in (FStar_Pprint.group _165_841))
end
| _67_1021 -> begin
(p_tmNoEq e)
end))
and p_tmNoEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n = (max_level ((colon_colon)::(amp)::(opinfix3)::(opinfix4)::[]))
in (p_tmNoEq' n e)))
and p_tmNoEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (match ((let _165_845 = (unparen e)
in _165_845.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Construct (lid, ((e1, _67_1033))::((e2, _67_1029))::[]) when ((FStar_Ident.lid_equals lid FStar_Syntax_Const.cons_lid) && (not ((is_list e)))) -> begin
(

let op = "::"
in (

let _67_1042 = (levels op)
in (match (_67_1042) with
| (left, mine, right) -> begin
(let _165_849 = (let _165_848 = (str op)
in (let _165_847 = (p_tmNoEq' left e1)
in (let _165_846 = (p_tmNoEq' right e2)
in (infix0 _165_848 _165_847 _165_846))))
in (paren_if curr mine _165_849))
end)))
end
| FStar_Parser_AST.Sum (binders, res) -> begin
(

let op = "&"
in (

let _67_1051 = (levels op)
in (match (_67_1051) with
| (left, mine, right) -> begin
(

let p_dsumfst = (fun b -> (let _165_855 = (p_binder false b)
in (let _165_854 = (let _165_853 = (let _165_852 = (str "&")
in (FStar_Pprint.op_Hat_Hat _165_852 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_853))
in (FStar_Pprint.op_Hat_Hat _165_855 _165_854))))
in (let _165_858 = (let _165_857 = (FStar_Pprint.concat_map p_dsumfst binders)
in (let _165_856 = (p_tmNoEq' right res)
in (FStar_Pprint.op_Hat_Hat _165_857 _165_856)))
in (paren_if curr mine _165_858)))
end)))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (is_operatorInfix34 op) -> begin
(

let _67_1063 = (levels op)
in (match (_67_1063) with
| (left, mine, right) -> begin
(let _165_862 = (let _165_861 = (str op)
in (let _165_860 = (p_tmNoEq' left e1)
in (let _165_859 = (p_tmNoEq' right e2)
in (infix0 _165_861 _165_860 _165_859))))
in (paren_if curr mine _165_862))
end))
end
| FStar_Parser_AST.Op ("-", (e)::[]) -> begin
(

let _67_1072 = (levels "-")
in (match (_67_1072) with
| (left, mine, right) -> begin
(let _165_863 = (p_tmNoEq' mine e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus _165_863))
end))
end
| FStar_Parser_AST.NamedTyp (lid, e) -> begin
(let _165_867 = (let _165_866 = (p_lidentOrUnderscore lid)
in (let _165_865 = (let _165_864 = (p_appTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon _165_864))
in (FStar_Pprint.op_Hat_Slash_Hat _165_866 _165_865)))
in (FStar_Pprint.group _165_867))
end
| FStar_Parser_AST.Refine (b, phi) -> begin
(p_refinedBinder b phi)
end
| FStar_Parser_AST.Record (with_opt, record_fields) -> begin
(let _165_871 = (let _165_870 = (default_or_map FStar_Pprint.empty p_with_clause with_opt)
in (let _165_869 = (let _165_868 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (FStar_Pprint.separate_map _165_868 p_simpleDef record_fields))
in (FStar_Pprint.op_Hat_Hat _165_870 _165_869)))
in (braces_with_nesting _165_871))
end
| FStar_Parser_AST.Op ("~", (e)::[]) -> begin
(let _165_874 = (let _165_873 = (str "~")
in (let _165_872 = (p_atomicTerm e)
in (FStar_Pprint.op_Hat_Hat _165_873 _165_872)))
in (FStar_Pprint.group _165_874))
end
| _67_1091 -> begin
(p_appTerm e)
end))
and p_with_clause : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (let _165_879 = (p_appTerm e)
in (let _165_878 = (let _165_877 = (let _165_876 = (str "with")
in (FStar_Pprint.op_Hat_Hat _165_876 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_877))
in (FStar_Pprint.op_Hat_Hat _165_879 _165_878))))
and p_refinedBinder : FStar_Parser_AST.binder  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun b phi -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (lid, t) -> begin
(let _165_883 = (let _165_882 = (p_lident lid)
in (p_refinement b.FStar_Parser_AST.aqual _165_882 t phi))
in (soft_parens_with_nesting _165_883))
end
| FStar_Parser_AST.TAnnotated (_67_1100) -> begin
(failwith "Is this still used ?")
end
| (FStar_Parser_AST.Variable (_)) | (FStar_Parser_AST.TVariable (_)) | (FStar_Parser_AST.NoName (_)) -> begin
(let _165_885 = (let _165_884 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" _165_884))
in (failwith _165_885))
end))
and p_simpleDef : (FStar_Ident.lid * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun _67_1113 -> (match (_67_1113) with
| (lid, e) -> begin
(let _165_890 = (let _165_889 = (p_qlident lid)
in (let _165_888 = (let _165_887 = (p_tmIff e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals _165_887))
in (FStar_Pprint.op_Hat_Slash_Hat _165_889 _165_888)))
in (FStar_Pprint.group _165_890))
end))
and p_appTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _165_892 = (unparen e)
in _165_892.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (_67_1116) when (is_general_application e) -> begin
(

let _67_1120 = (head_and_args e)
in (match (_67_1120) with
| (head, args) -> begin
(let _165_894 = (p_indexingTerm head)
in (let _165_893 = (FStar_Pprint.separate_map FStar_Pprint.space p_argTerm args)
in (op_Hat_Slash_Plus_Hat _165_894 _165_893)))
end))
end
| FStar_Parser_AST.Construct (lid, args) when ((is_general_construction e) && (not ((is_dtuple_constructor lid)))) -> begin
(match (args) with
| [] -> begin
(p_quident lid)
end
| (arg)::[] -> begin
(let _165_897 = (let _165_896 = (p_quident lid)
in (let _165_895 = (p_argTerm arg)
in (FStar_Pprint.op_Hat_Slash_Hat _165_896 _165_895)))
in (FStar_Pprint.group _165_897))
end
| (hd)::tl -> begin
(let _165_904 = (let _165_903 = (let _165_900 = (let _165_899 = (p_quident lid)
in (let _165_898 = (p_argTerm hd)
in (FStar_Pprint.op_Hat_Slash_Hat _165_899 _165_898)))
in (FStar_Pprint.group _165_900))
in (let _165_902 = (let _165_901 = (FStar_Pprint.separate_map break1 p_argTerm tl)
in (jump2 _165_901))
in (FStar_Pprint.op_Hat_Hat _165_903 _165_902)))
in (FStar_Pprint.group _165_904))
end)
end
| _67_1132 -> begin
(p_indexingTerm e)
end))
and p_argTerm : (FStar_Parser_AST.term * FStar_Parser_AST.imp)  ->  FStar_Pprint.document = (fun arg_imp -> (match (arg_imp) with
| ({FStar_Parser_AST.tm = FStar_Parser_AST.Uvar (_67_1139); FStar_Parser_AST.range = _67_1137; FStar_Parser_AST.level = _67_1135}, FStar_Parser_AST.UnivApp) -> begin
(p_univar (Prims.fst arg_imp))
end
| (u, FStar_Parser_AST.UnivApp) -> begin
(p_universe u)
end
| (e, FStar_Parser_AST.FsTypApp) -> begin
(let _165_906 = (p_indexingTerm e)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.langle _165_906 FStar_Pprint.rangle))
end
| (e, FStar_Parser_AST.Hash) -> begin
(let _165_908 = (str "#")
in (let _165_907 = (p_indexingTerm e)
in (FStar_Pprint.op_Hat_Hat _165_908 _165_907)))
end
| (e, FStar_Parser_AST.Nothing) -> begin
(p_indexingTerm e)
end))
and p_indexingTerm_aux : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun exit e -> (match ((let _165_914 = (unparen e)
in _165_914.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Op (".()", (e1)::(e2)::[]) -> begin
(let _165_919 = (let _165_918 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (let _165_917 = (let _165_916 = (let _165_915 = (p_term e2)
in (soft_parens_with_nesting _165_915))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_916))
in (FStar_Pprint.op_Hat_Hat _165_918 _165_917)))
in (FStar_Pprint.group _165_919))
end
| FStar_Parser_AST.Op (".[]", (e1)::(e2)::[]) -> begin
(let _165_924 = (let _165_923 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (let _165_922 = (let _165_921 = (let _165_920 = (p_term e2)
in (soft_brackets_with_nesting _165_920))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_921))
in (FStar_Pprint.op_Hat_Hat _165_923 _165_922)))
in (FStar_Pprint.group _165_924))
end
| _67_1171 -> begin
(exit e)
end))
and p_indexingTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_indexingTerm_aux p_atomicTerm e))
and p_atomicTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _165_927 = (unparen e)
in _165_927.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.LetOpen (lid, e) -> begin
(let _165_931 = (p_quident lid)
in (let _165_930 = (let _165_929 = (let _165_928 = (p_term e)
in (soft_parens_with_nesting _165_928))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_929))
in (FStar_Pprint.op_Hat_Hat _165_931 _165_930)))
end
| FStar_Parser_AST.Name (lid) -> begin
(p_quident lid)
end
| FStar_Parser_AST.Op (op, (e)::[]) when (is_general_prefix_op op) -> begin
(let _165_933 = (str op)
in (let _165_932 = (p_atomicTerm e)
in (FStar_Pprint.op_Hat_Hat _165_933 _165_932)))
end
| _67_1186 -> begin
(p_atomicTermNotQUident e)
end))
and p_atomicTermNotQUident : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _165_935 = (unparen e)
in _165_935.FStar_Parser_AST.tm)) with
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
(let _165_937 = (str op)
in (let _165_936 = (p_atomicTermNotQUident e)
in (FStar_Pprint.op_Hat_Hat _165_937 _165_936)))
end
| FStar_Parser_AST.Op (op, []) -> begin
(let _165_941 = (let _165_940 = (let _165_939 = (str op)
in (let _165_938 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat _165_939 _165_938)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _165_940))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _165_941))
end
| FStar_Parser_AST.Construct (lid, args) when (is_dtuple_constructor lid) -> begin
(let _165_946 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (let _165_945 = (let _165_943 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (let _165_942 = (FStar_List.map Prims.fst args)
in (FStar_Pprint.separate_map _165_943 p_tmEq _165_942)))
in (let _165_944 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_946 _165_945 _165_944))))
end
| FStar_Parser_AST.Project (e, lid) -> begin
(let _165_950 = (let _165_949 = (p_atomicTermNotQUident e)
in (let _165_948 = (let _165_947 = (p_qlident lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_947))
in (FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0") _165_949 _165_948)))
in (FStar_Pprint.group _165_950))
end
| _67_1217 -> begin
(p_projectionLHS e)
end))
and p_projectionLHS : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match ((let _165_952 = (unparen e)
in _165_952.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Var (lid) -> begin
(p_qlident lid)
end
| FStar_Parser_AST.Projector (constr_lid, field_lid) -> begin
(let _165_956 = (p_quident constr_lid)
in (let _165_955 = (let _165_954 = (let _165_953 = (p_lident field_lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_953))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark _165_954))
in (FStar_Pprint.op_Hat_Hat _165_956 _165_955)))
end
| FStar_Parser_AST.Discrim (constr_lid) -> begin
(let _165_957 = (p_quident constr_lid)
in (FStar_Pprint.op_Hat_Hat _165_957 FStar_Pprint.qmark))
end
| FStar_Parser_AST.Paren (e) -> begin
(let _165_958 = (p_term e)
in (soft_parens_with_nesting _165_958))
end
| _67_1230 when (is_array e) -> begin
(

let es = (extract_from_list e)
in (let _165_962 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar)
in (let _165_961 = (let _165_959 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (separate_map_or_flow _165_959 p_noSeqTerm es))
in (let _165_960 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") _165_962 _165_961 _165_960)))))
end
| _67_1233 when (is_list e) -> begin
(let _165_965 = (let _165_964 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (let _165_963 = (extract_from_list e)
in (separate_map_or_flow _165_964 p_noSeqTerm _165_963)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket _165_965 FStar_Pprint.rbracket))
end
| _67_1235 when (is_lex_list e) -> begin
(let _165_969 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket)
in (let _165_968 = (let _165_967 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (let _165_966 = (extract_from_list e)
in (separate_map_or_flow _165_967 p_noSeqTerm _165_966)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _165_969 _165_968 FStar_Pprint.rbracket)))
end
| _67_1237 when (is_ref_set e) -> begin
(

let es = (extract_from_ref_set e)
in (let _165_972 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace)
in (let _165_971 = (let _165_970 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (separate_map_or_flow _165_970 p_appTerm es))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") _165_972 _165_971 FStar_Pprint.rbrace))))
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Op (_)) | (FStar_Parser_AST.Tvar (_)) | (FStar_Parser_AST.Uvar (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) | (FStar_Parser_AST.Construct (_)) | (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.App (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.LetOpen (_)) | (FStar_Parser_AST.Seq (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Ascribed (_)) | (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Project (_)) | (FStar_Parser_AST.Product (_)) | (FStar_Parser_AST.Sum (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Refine (_)) | (FStar_Parser_AST.NamedTyp (_)) | (FStar_Parser_AST.Requires (_)) | (FStar_Parser_AST.Ensures (_)) | (FStar_Parser_AST.Assign (_)) | (FStar_Parser_AST.Attributes (_)) -> begin
(let _165_973 = (p_term e)
in (soft_parens_with_nesting _165_973))
end
| FStar_Parser_AST.Labeled (_67_1325) -> begin
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
(let _165_975 = (FStar_Pprint.doc_of_char x)
in (FStar_Pprint.squotes _165_975))
end
| FStar_Const.Const_string (bytes, _67_1338) -> begin
(let _165_976 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes _165_976))
end
| FStar_Const.Const_bytearray (bytes, _67_1343) -> begin
(let _165_979 = (let _165_977 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes _165_977))
in (let _165_978 = (str "B")
in (FStar_Pprint.op_Hat_Hat _165_979 _165_978)))
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

let ending = (default_or_map FStar_Pprint.empty (fun _67_1362 -> (match (_67_1362) with
| (s, w) -> begin
(let _165_986 = (signedness s)
in (let _165_985 = (width w)
in (FStar_Pprint.op_Hat_Hat _165_986 _165_985)))
end)) sign_width_opt)
in (let _165_987 = (str repr)
in (FStar_Pprint.op_Hat_Hat _165_987 ending)))))
end
| FStar_Const.Const_range (r) -> begin
(let _165_988 = (FStar_Range.string_of_range r)
in (str _165_988))
end
| FStar_Const.Const_reify -> begin
(str "reify")
end
| FStar_Const.Const_reflect (lid) -> begin
(let _165_992 = (p_quident lid)
in (let _165_991 = (let _165_990 = (let _165_989 = (str "reflect")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _165_989))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark _165_990))
in (FStar_Pprint.op_Hat_Hat _165_992 _165_991)))
end))
and p_universe : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (let _165_995 = (str "u#")
in (let _165_994 = (p_atomicUniverse u)
in (FStar_Pprint.op_Hat_Hat _165_995 _165_994))))
and p_universeFrom : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match ((let _165_997 = (unparen u)
in _165_997.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Op ("+", (u1)::(u2)::[]) -> begin
(let _165_1001 = (let _165_1000 = (p_universeFrom u1)
in (let _165_999 = (let _165_998 = (p_universeFrom u2)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus _165_998))
in (FStar_Pprint.op_Hat_Slash_Hat _165_1000 _165_999)))
in (FStar_Pprint.group _165_1001))
end
| FStar_Parser_AST.App (_67_1378) -> begin
(

let _67_1382 = (head_and_args u)
in (match (_67_1382) with
| (head, args) -> begin
(match ((let _165_1002 = (unparen head)
in _165_1002.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Var (maybe_max_lid) when (FStar_Ident.lid_equals maybe_max_lid FStar_Syntax_Const.max_lid) -> begin
(let _165_1006 = (let _165_1005 = (p_qlident FStar_Syntax_Const.max_lid)
in (let _165_1004 = (FStar_Pprint.separate_map FStar_Pprint.space (fun _67_1388 -> (match (_67_1388) with
| (u, _67_1387) -> begin
(p_atomicUniverse u)
end)) args)
in (op_Hat_Slash_Plus_Hat _165_1005 _165_1004)))
in (FStar_Pprint.group _165_1006))
end
| _67_1390 -> begin
(let _165_1008 = (let _165_1007 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" _165_1007))
in (failwith _165_1008))
end)
end))
end
| _67_1392 -> begin
(p_atomicUniverse u)
end))
and p_atomicUniverse : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match ((let _165_1010 = (unparen u)
in _165_1010.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (r, sw)) -> begin
(p_constant (FStar_Const.Const_int (((r), (sw)))))
end
| FStar_Parser_AST.Uvar (_67_1401) -> begin
(p_univar u)
end
| FStar_Parser_AST.Paren (u) -> begin
(let _165_1011 = (p_universeFrom u)
in (soft_parens_with_nesting _165_1011))
end
| (FStar_Parser_AST.Op ("+", (_)::(_)::[])) | (FStar_Parser_AST.App (_)) -> begin
(let _165_1012 = (p_universeFrom u)
in (soft_parens_with_nesting _165_1012))
end
| _67_1417 -> begin
(let _165_1014 = (let _165_1013 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" _165_1013))
in (failwith _165_1014))
end))
and p_univar : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match ((let _165_1016 = (unparen u)
in _165_1016.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Uvar (id) -> begin
(str (FStar_Ident.text_of_id id))
end
| _67_1422 -> begin
(let _165_1018 = (let _165_1017 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Not a universe variable %s" _165_1017))
in (failwith _165_1018))
end))


let term_to_document : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_term e))


let decl_to_document : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun e -> (p_decl e))


let modul_to_document : FStar_Parser_AST.modul  ->  FStar_Pprint.document = (fun m -> (match (m) with
| (FStar_Parser_AST.Module (_, decls)) | (FStar_Parser_AST.Interface (_, decls, _)) -> begin
(let _165_1025 = (FStar_All.pipe_right decls (FStar_List.map decl_to_document))
in (FStar_All.pipe_right _165_1025 (FStar_Pprint.separate FStar_Pprint.hardline)))
end))


let comments_to_document : (Prims.string * FStar_Range.range) Prims.list  ->  FStar_Pprint.document = (fun comments -> (FStar_Pprint.separate_map FStar_Pprint.hardline (fun _67_1440 -> (match (_67_1440) with
| (comment, range) -> begin
(str comment)
end)) comments))


let modul_with_comments_to_document : FStar_Parser_AST.modul  ->  (Prims.string * FStar_Range.range) Prims.list  ->  (FStar_Pprint.document * (Prims.string * FStar_Range.range) Prims.list) = (fun m comments -> (

let rec aux = (fun _67_1447 decl -> (match (_67_1447) with
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
| ((comment, range))::comments when (let _165_1051 = (FStar_Range.start_of_range range)
in (FStar_Range.pos_geq end_pos _165_1051)) -> begin
(

let l = (let _165_1053 = ((let _165_1052 = (FStar_Range.start_of_range range)
in (FStar_Range.line_of_pos _165_1052)) - last_line)
in (max (Prims.parse_int "1") _165_1053))
in (

let doc = (let _165_1056 = (let _165_1055 = (FStar_Pprint.repeat l FStar_Pprint.hardline)
in (let _165_1054 = (str comment)
in (FStar_Pprint.op_Hat_Hat _165_1055 _165_1054)))
in (FStar_Pprint.op_Hat_Hat doc _165_1056))
in (let _165_1058 = (let _165_1057 = (FStar_Range.end_of_range range)
in (FStar_Range.line_of_pos _165_1057))
in (process_preceding_comments doc _165_1058 end_pos (Prims.parse_int "1") comments))))
end
| comments -> begin
(

let l = (let _165_1059 = ((FStar_Range.line_of_pos end_pos) - last_line)
in (max n _165_1059))
in (let _165_1061 = (let _165_1060 = (FStar_Pprint.repeat l FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat doc _165_1060))
in ((_165_1061), (comments))))
end))
in (

let _67_1470 = (let _165_1064 = (FStar_Range.line_of_pos previous_range_end)
in (let _165_1063 = (let _165_1062 = (FStar_Range.start_of_range current_range)
in (FStar_Range.end_of_line _165_1062))
in (process_preceding_comments doc _165_1064 _165_1063 (Prims.parse_int "0") comments)))
in (match (_67_1470) with
| (doc, comments) -> begin
(

let _67_1478 = (FStar_Util.take (fun _67_17 -> (match (_67_17) with
| (_67_1473, range) -> begin
(FStar_Range.range_contains_range current_range range)
end)) comments)
in (match (_67_1478) with
| (inner_comments, comments) -> begin
(

let _67_1479 = (FStar_ST.op_Colon_Equals comment_stack inner_comments)
in (

let doc = (let _165_1066 = (decl_to_document decl)
in (FStar_Pprint.op_Hat_Hat doc _165_1066))
in (

let inner_comments_doc = if ((FStar_ST.read comment_stack) = []) then begin
FStar_Pprint.empty
end else begin
(

let _67_1482 = (let _165_1069 = (let _165_1068 = (let _165_1067 = (FStar_ST.read comment_stack)
in (FStar_List.map Prims.fst _165_1067))
in (FStar_String.concat " ; " _165_1068))
in (FStar_Util.print1_warning "Leftover comments : %s\n" _165_1069))
in (let _165_1070 = (FStar_ST.read comment_stack)
in (comments_to_document _165_1070)))
end
in (let _165_1072 = (FStar_Range.end_of_range decl.FStar_Parser_AST.drange)
in (let _165_1071 = (FStar_Pprint.op_Hat_Hat doc inner_comments_doc)
in ((_165_1072), (comments), (_165_1071)))))))
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
| (d)::_67_1499 -> begin
(

let _67_1506 = (FStar_List.fold_left aux ((FStar_Range.zeroPos), (comments), (FStar_Pprint.empty)) decls)
in (match (_67_1506) with
| (_67_1503, comments, doc) -> begin
((doc), (comments))
end))
end))))




