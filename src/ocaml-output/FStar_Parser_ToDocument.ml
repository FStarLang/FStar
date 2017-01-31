
open Prims

let should_print_fs_typ_app : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let with_fs_typ_app = (fun b printer t -> (

let b0 = (FStar_ST.read should_print_fs_typ_app)
in ((FStar_ST.write should_print_fs_typ_app b);
(

let res = (printer t)
in ((FStar_ST.write should_print_fs_typ_app b0);
res;
));
)))


let should_unparen : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref true)


let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (

let uu____44 = (not ((FStar_ST.read should_unparen)))
in (match (uu____44) with
| true -> begin
t
end
| uu____47 -> begin
(match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| uu____49 -> begin
t
end)
end)))


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


let separate_break_map = (fun sep f l -> (FStar_Pprint.group (let _0_316 = (let _0_315 = (FStar_Pprint.op_Hat_Hat sep break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_315))
in (FStar_Pprint.separate_map _0_316 f l))))


let precede_break_separate_map = (fun prec sep f l -> (let _0_325 = (let _0_319 = (FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space)
in (let _0_318 = (let _0_317 = (FStar_List.hd l)
in (FStar_All.pipe_right _0_317 f))
in (FStar_Pprint.precede _0_319 _0_318)))
in (let _0_324 = (let _0_323 = (FStar_List.tl l)
in (FStar_Pprint.concat_map (fun x -> (let _0_322 = (let _0_321 = (let _0_320 = (f x)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_320))
in (FStar_Pprint.op_Hat_Hat sep _0_321))
in (FStar_Pprint.op_Hat_Hat break1 _0_322))) _0_323))
in (FStar_Pprint.op_Hat_Hat _0_325 _0_324))))


let concat_break_map = (fun f l -> (FStar_Pprint.group (FStar_Pprint.concat_map (fun x -> (let _0_326 = (f x)
in (FStar_Pprint.op_Hat_Hat _0_326 break1))) l)))


let parens_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lparen contents FStar_Pprint.rparen))


let soft_parens_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lparen contents FStar_Pprint.rparen))


let braces_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbrace contents FStar_Pprint.rbrace))


let soft_braces_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbrace contents FStar_Pprint.rbrace))


let brackets_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbracket contents FStar_Pprint.rbracket))


let soft_brackets_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbracket contents FStar_Pprint.rbracket))


let soft_begin_end_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (let _0_328 = (str "begin")
in (let _0_327 = (str "end")
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") _0_328 contents _0_327))))


let separate_map_or_flow = (fun sep f l -> (match (((FStar_List.length l) < (Prims.parse_int "10"))) with
| true -> begin
(FStar_Pprint.separate_map sep f l)
end
| uu____229 -> begin
(FStar_Pprint.flow_map sep f l)
end))


let soft_surround_separate_map = (fun n b void_ opening sep closing f xs -> (match ((xs = [])) with
| true -> begin
void_
end
| uu____280 -> begin
(let _0_329 = (FStar_Pprint.separate_map sep f xs)
in (FStar_Pprint.soft_surround n b opening _0_329 closing))
end))


let doc_of_fsdoc : (Prims.string * (Prims.string * Prims.string) Prims.list)  ->  FStar_Pprint.document = (fun uu____288 -> (match (uu____288) with
| (comment, keywords) -> begin
(FStar_Pprint.group (FStar_Pprint.concat (let _0_337 = (str comment)
in (let _0_336 = (let _0_335 = (let _0_334 = (FStar_Pprint.separate_map FStar_Pprint.comma (fun uu____304 -> (match (uu____304) with
| (k, v) -> begin
(FStar_Pprint.concat (let _0_333 = (str k)
in (let _0_332 = (let _0_331 = (let _0_330 = (str v)
in (_0_330)::[])
in (FStar_Pprint.rarrow)::_0_331)
in (_0_333)::_0_332)))
end)) keywords)
in (_0_334)::[])
in (FStar_Pprint.space)::_0_335)
in (_0_337)::_0_336))))
end))


let is_unit : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____312 = (unparen e).FStar_Parser_AST.tm
in (match (uu____312) with
| FStar_Parser_AST.Const (FStar_Const.Const_unit) -> begin
true
end
| uu____313 -> begin
false
end)))


let matches_var : FStar_Parser_AST.term  ->  FStar_Ident.ident  ->  Prims.bool = (fun t x -> (

let uu____320 = (unparen t).FStar_Parser_AST.tm
in (match (uu____320) with
| FStar_Parser_AST.Var (y) -> begin
(x.FStar_Ident.idText = (FStar_Ident.text_of_lid y))
end
| uu____322 -> begin
false
end)))


let is_tuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Syntax_Util.is_tuple_data_lid'


let is_dtuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Syntax_Util.is_dtuple_data_lid'


let is_list_structure : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun cons_lid nil_lid -> (

let rec aux = (fun e -> (

let uu____339 = (unparen e).FStar_Parser_AST.tm
in (match (uu____339) with
| FStar_Parser_AST.Construct (lid, []) -> begin
(FStar_Ident.lid_equals lid nil_lid)
end
| FStar_Parser_AST.Construct (lid, (uu____347)::((e2, uu____349))::[]) -> begin
((FStar_Ident.lid_equals lid cons_lid) && (aux e2))
end
| uu____361 -> begin
false
end)))
in aux))


let is_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Syntax_Const.cons_lid FStar_Syntax_Const.nil_lid)


let is_lex_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Syntax_Const.lexcons_lid FStar_Syntax_Const.lextop_lid)


let rec extract_from_list : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (

let uu____370 = (unparen e).FStar_Parser_AST.tm
in (match (uu____370) with
| FStar_Parser_AST.Construct (uu____372, []) -> begin
[]
end
| FStar_Parser_AST.Construct (uu____378, ((e1, FStar_Parser_AST.Nothing))::((e2, FStar_Parser_AST.Nothing))::[]) -> begin
(let _0_338 = (extract_from_list e2)
in (e1)::_0_338)
end
| uu____390 -> begin
(failwith (let _0_339 = (FStar_Parser_AST.term_to_string e)
in (FStar_Util.format1 "Not a list %s" _0_339)))
end)))


let is_array : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____395 = (unparen e).FStar_Parser_AST.tm
in (match (uu____395) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (lid); FStar_Parser_AST.range = uu____397; FStar_Parser_AST.level = uu____398}, l, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals lid FStar_Syntax_Const.array_mk_array_lid) && (is_list l))
end
| uu____400 -> begin
false
end)))


let rec is_ref_set : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____404 = (unparen e).FStar_Parser_AST.tm
in (match (uu____404) with
| FStar_Parser_AST.Var (maybe_empty_lid) -> begin
(FStar_Ident.lid_equals maybe_empty_lid FStar_Syntax_Const.tset_empty)
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_singleton_lid); FStar_Parser_AST.range = uu____407; FStar_Parser_AST.level = uu____408}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_ref_lid); FStar_Parser_AST.range = uu____410; FStar_Parser_AST.level = uu____411}, e, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____413; FStar_Parser_AST.level = uu____414}, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals maybe_singleton_lid FStar_Syntax_Const.tset_singleton) && (FStar_Ident.lid_equals maybe_ref_lid FStar_Syntax_Const.heap_ref))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_union_lid); FStar_Parser_AST.range = uu____416; FStar_Parser_AST.level = uu____417}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____419; FStar_Parser_AST.level = uu____420}, e2, FStar_Parser_AST.Nothing) -> begin
(((FStar_Ident.lid_equals maybe_union_lid FStar_Syntax_Const.tset_union) && (is_ref_set e1)) && (is_ref_set e2))
end
| uu____422 -> begin
false
end)))


let rec extract_from_ref_set : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (

let uu____427 = (unparen e).FStar_Parser_AST.tm
in (match (uu____427) with
| FStar_Parser_AST.Var (uu____429) -> begin
[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (uu____430); FStar_Parser_AST.range = uu____431; FStar_Parser_AST.level = uu____432}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (uu____433); FStar_Parser_AST.range = uu____434; FStar_Parser_AST.level = uu____435}, e, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____437; FStar_Parser_AST.level = uu____438}, FStar_Parser_AST.Nothing) -> begin
(e)::[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (uu____439); FStar_Parser_AST.range = uu____440; FStar_Parser_AST.level = uu____441}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____443; FStar_Parser_AST.level = uu____444}, e2, FStar_Parser_AST.Nothing) -> begin
(let _0_341 = (extract_from_ref_set e1)
in (let _0_340 = (extract_from_ref_set e2)
in (FStar_List.append _0_341 _0_340)))
end
| uu____446 -> begin
(failwith (let _0_342 = (FStar_Parser_AST.term_to_string e)
in (FStar_Util.format1 "Not a ref set %s" _0_342)))
end)))


let is_general_application : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (not (((is_array e) || (is_ref_set e)))))


let is_general_construction : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (not (((is_list e) || (is_lex_list e)))))


let is_general_prefix_op : Prims.string  ->  Prims.bool = (fun op -> (op <> "~"))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun e -> (

let rec aux = (fun e acc -> (

let uu____483 = (unparen e).FStar_Parser_AST.tm
in (match (uu____483) with
| FStar_Parser_AST.App (head, arg, imp) -> begin
(aux head ((((arg), (imp)))::acc))
end
| uu____494 -> begin
((e), (acc))
end)))
in (aux e [])))

type associativity =
| Left
| Right
| NonAssoc


let uu___is_Left : associativity  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Left -> begin
true
end
| uu____503 -> begin
false
end))


let uu___is_Right : associativity  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Right -> begin
true
end
| uu____507 -> begin
false
end))


let uu___is_NonAssoc : associativity  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NonAssoc -> begin
true
end
| uu____511 -> begin
false
end))


type token =
(FStar_Char.char, Prims.string) FStar_Util.either


type associativity_level =
(associativity * token Prims.list)


let token_to_string : (FStar_BaseTypes.char, Prims.string) FStar_Util.either  ->  Prims.string = (fun uu___113_521 -> (match (uu___113_521) with
| FStar_Util.Inl (c) -> begin
(Prims.strcat (FStar_Util.string_of_char c) ".*")
end
| FStar_Util.Inr (s) -> begin
s
end))


let matches_token : Prims.string  ->  (FStar_Char.char, Prims.string) FStar_Util.either  ->  Prims.bool = (fun s uu___114_533 -> (match (uu___114_533) with
| FStar_Util.Inl (c) -> begin
(let _0_343 = (FStar_String.get s (Prims.parse_int "0"))
in (_0_343 = c))
end
| FStar_Util.Inr (s') -> begin
(s = s')
end))


let matches_level = (fun s uu____554 -> (match (uu____554) with
| (assoc_levels, tokens) -> begin
(let _0_344 = (FStar_List.tryFind (matches_token s) tokens)
in (_0_344 <> None))
end))


let opinfix4 = (fun uu____582 -> ((Right), ((FStar_Util.Inr ("**"))::[])))


let opinfix3 = (fun uu____597 -> ((Left), ((FStar_Util.Inl ('*'))::(FStar_Util.Inl ('/'))::(FStar_Util.Inl ('%'))::[])))


let opinfix2 = (fun uu____616 -> ((Left), ((FStar_Util.Inl ('+'))::(FStar_Util.Inl ('-'))::[])))


let minus_lvl = (fun uu____633 -> ((Left), ((FStar_Util.Inr ("-"))::[])))


let opinfix1 = (fun uu____648 -> ((Right), ((FStar_Util.Inl ('@'))::(FStar_Util.Inl ('^'))::[])))


let pipe_right = (fun uu____665 -> ((Left), ((FStar_Util.Inr ("|>"))::[])))


let opinfix0d = (fun uu____680 -> ((Left), ((FStar_Util.Inl ('$'))::[])))


let opinfix0c = (fun uu____695 -> ((Left), ((FStar_Util.Inl ('='))::(FStar_Util.Inl ('<'))::(FStar_Util.Inl ('>'))::[])))


let equal = (fun uu____714 -> ((Left), ((FStar_Util.Inr ("="))::[])))


let opinfix0b = (fun uu____729 -> ((Left), ((FStar_Util.Inl ('&'))::[])))


let opinfix0a = (fun uu____744 -> ((Left), ((FStar_Util.Inl ('|'))::[])))


let colon_equals = (fun uu____759 -> ((NonAssoc), ((FStar_Util.Inr (":="))::[])))


let amp = (fun uu____774 -> ((Right), ((FStar_Util.Inr ("&"))::[])))


let colon_colon = (fun uu____789 -> ((Right), ((FStar_Util.Inr ("::"))::[])))


let level_associativity_spec : (associativity * (FStar_Char.char, Prims.string) FStar_Util.either Prims.list) Prims.list = ((opinfix4 ()))::((opinfix3 ()))::((opinfix2 ()))::((opinfix1 ()))::((pipe_right ()))::((opinfix0d ()))::((opinfix0c ()))::((opinfix0b ()))::((opinfix0a ()))::((colon_equals ()))::((amp ()))::((colon_colon ()))::[]


let level_table : ((Prims.int * Prims.int * Prims.int) * (FStar_Char.char, Prims.string) FStar_Util.either Prims.list) Prims.list = (

let levels_from_associativity = (fun l uu___115_886 -> (match (uu___115_886) with
| Left -> begin
((l), (l), ((l - (Prims.parse_int "1"))))
end
| Right -> begin
(((l - (Prims.parse_int "1"))), (l), (l))
end
| NonAssoc -> begin
((l), (l), (l))
end))
in (FStar_List.mapi (fun i uu____904 -> (match (uu____904) with
| (assoc, tokens) -> begin
(((levels_from_associativity i assoc)), (tokens))
end)) level_associativity_spec))


let assign_levels : associativity_level Prims.list  ->  Prims.string  ->  (Prims.int * Prims.int * Prims.int) = (fun token_associativity_spec s -> (

let uu____946 = (FStar_List.tryFind (matches_level s) level_table)
in (match (uu____946) with
| Some (assoc_levels, uu____971) -> begin
assoc_levels
end
| uu____992 -> begin
(failwith (Prims.strcat "Unrecognized operator " s))
end)))


let max : Prims.int  ->  Prims.int  ->  Prims.int = (fun k1 k2 -> (match ((k1 > k2)) with
| true -> begin
k1
end
| uu____1011 -> begin
k2
end))


let max_level = (fun l -> (

let find_level_and_max = (fun n level -> (

let uu____1048 = (FStar_List.tryFind (fun uu____1066 -> (match (uu____1066) with
| (uu____1075, tokens) -> begin
(tokens = (Prims.snd level))
end)) level_table)
in (match (uu____1048) with
| Some ((uu____1095, l, uu____1097), uu____1098) -> begin
(max n l)
end
| None -> begin
(failwith (let _0_346 = (let _0_345 = (FStar_List.map token_to_string (Prims.snd level))
in (FStar_String.concat "," _0_345))
in (FStar_Util.format1 "Undefined associativity level %s" _0_346)))
end)))
in (FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l)))


let levels : Prims.string  ->  (Prims.int * Prims.int * Prims.int) = (assign_levels level_associativity_spec)


let operatorInfix0ad12 = (fun uu____1147 -> ((opinfix0a ()))::((opinfix0b ()))::((opinfix0c ()))::((opinfix0d ()))::((opinfix1 ()))::((opinfix2 ()))::[])


let is_operatorInfix0ad12 : Prims.string  ->  Prims.bool = (fun op -> (let _0_347 = (FStar_List.tryFind (matches_level op) (operatorInfix0ad12 ()))
in (_0_347 <> None)))


let is_operatorInfix34 : Prims.string  ->  Prims.bool = (

let opinfix34 = ((opinfix3 ()))::((opinfix4 ()))::[]
in (fun op -> (let _0_348 = (FStar_List.tryFind (matches_level op) opinfix34)
in (_0_348 <> None))))


let comment_stack : (Prims.string * FStar_Range.range) Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let with_comment = (fun printer tm tmrange -> (

let rec comments_before_pos = (fun acc print_pos lookahead_pos -> (

let uu____1288 = (FStar_ST.read comment_stack)
in (match (uu____1288) with
| [] -> begin
((acc), (false))
end
| ((comment, crange))::cs -> begin
(

let uu____1309 = (FStar_Range.range_before_pos crange print_pos)
in (match (uu____1309) with
| true -> begin
((FStar_ST.write comment_stack cs);
(let _0_351 = (let _0_350 = (let _0_349 = (str comment)
in (FStar_Pprint.op_Hat_Hat _0_349 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat acc _0_350))
in (comments_before_pos _0_351 print_pos lookahead_pos));
)
end
| uu____1318 -> begin
(let _0_352 = (FStar_Range.range_before_pos crange lookahead_pos)
in ((acc), (_0_352)))
end))
end)))
in (

let uu____1319 = (let _0_354 = (FStar_Range.end_of_line (FStar_Range.start_of_range tmrange))
in (let _0_353 = (FStar_Range.end_of_range tmrange)
in (comments_before_pos FStar_Pprint.empty _0_354 _0_353)))
in (match (uu____1319) with
| (comments, has_lookahead) -> begin
(

let printed_e = (printer tm)
in (

let comments = (match (has_lookahead) with
| true -> begin
(

let pos = (FStar_Range.end_of_range tmrange)
in (Prims.fst (comments_before_pos comments pos pos)))
end
| uu____1327 -> begin
comments
end)
in (FStar_Pprint.group (FStar_Pprint.op_Hat_Hat comments printed_e))))
end))))


let rec place_comments_until_pos : Prims.int  ->  Prims.int  ->  FStar_Range.pos  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun k lbegin pos_end doc -> (

let uu____1340 = (FStar_ST.read comment_stack)
in (match (uu____1340) with
| ((comment, crange))::cs when (FStar_Range.range_before_pos crange pos_end) -> begin
((FStar_ST.write comment_stack cs);
(

let lnum = (let _0_356 = (let _0_355 = (FStar_Range.line_of_pos (FStar_Range.start_of_range crange))
in (_0_355 - lbegin))
in (max k _0_356))
in (

let doc = (let _0_359 = (let _0_358 = (FStar_Pprint.repeat lnum FStar_Pprint.hardline)
in (let _0_357 = (str comment)
in (FStar_Pprint.op_Hat_Hat _0_358 _0_357)))
in (FStar_Pprint.op_Hat_Hat doc _0_359))
in (let _0_360 = (FStar_Range.line_of_pos (FStar_Range.end_of_range crange))
in (place_comments_until_pos (Prims.parse_int "1") _0_360 pos_end doc))));
)
end
| uu____1365 -> begin
(

let lnum = (let _0_362 = (let _0_361 = (FStar_Range.line_of_pos pos_end)
in (_0_361 - lbegin))
in (max (Prims.parse_int "1") _0_362))
in (let _0_363 = (FStar_Pprint.repeat lnum FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat doc _0_363)))
end)))


let separate_map_with_comments = (fun prefix sep f xs extract_range -> (

let fold_fun = (fun uu____1418 x -> (match (uu____1418) with
| (last_line, doc) -> begin
(

let r = (extract_range x)
in (

let doc = (let _0_364 = (FStar_Range.start_of_range r)
in (place_comments_until_pos (Prims.parse_int "1") last_line _0_364 doc))
in (let _0_368 = (FStar_Range.line_of_pos (FStar_Range.end_of_range r))
in (let _0_367 = (let _0_366 = (let _0_365 = (f x)
in (FStar_Pprint.op_Hat_Hat sep _0_365))
in (FStar_Pprint.op_Hat_Hat doc _0_366))
in ((_0_368), (_0_367))))))
end))
in (

let uu____1428 = (let _0_370 = (FStar_List.hd xs)
in (let _0_369 = (FStar_List.tl xs)
in ((_0_370), (_0_369))))
in (match (uu____1428) with
| (x, xs) -> begin
(

let init = (let _0_373 = (FStar_Range.line_of_pos (FStar_Range.end_of_range (extract_range x)))
in (let _0_372 = (let _0_371 = (f x)
in (FStar_Pprint.op_Hat_Hat prefix _0_371))
in ((_0_373), (_0_372))))
in (Prims.snd (FStar_List.fold_left fold_fun init xs)))
end))))


let rec p_decl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (FStar_Pprint.group (let _0_380 = (FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc)
in (let _0_379 = (let _0_378 = (p_attributes d.FStar_Parser_AST.attrs)
in (let _0_377 = (let _0_376 = (p_qualifiers d.FStar_Parser_AST.quals)
in (let _0_375 = (let _0_374 = (p_rawDecl d)
in (FStar_Pprint.op_Hat_Hat (match ((d.FStar_Parser_AST.quals = [])) with
| true -> begin
FStar_Pprint.empty
end
| uu____1689 -> begin
break1
end) _0_374))
in (FStar_Pprint.op_Hat_Hat _0_376 _0_375)))
in (FStar_Pprint.op_Hat_Hat _0_378 _0_377)))
in (FStar_Pprint.op_Hat_Hat _0_380 _0_379)))))
and p_attributes : FStar_Parser_AST.attributes_  ->  FStar_Pprint.document = (fun attrs -> (let _0_383 = (let _0_381 = (str "@")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket _0_381))
in (let _0_382 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline)
in (soft_surround_separate_map (Prims.parse_int "0") (Prims.parse_int "2") FStar_Pprint.empty _0_383 FStar_Pprint.space _0_382 p_atomicTerm attrs))))
and p_fsdoc : FStar_Parser_AST.fsdoc  ->  FStar_Pprint.document = (fun uu____1691 -> (match (uu____1691) with
| (doc, kwd_args) -> begin
(

let kwd_args_doc = (match (kwd_args) with
| [] -> begin
FStar_Pprint.empty
end
| kwd_args -> begin
(

let process_kwd_arg = (fun uu____1712 -> (match (uu____1712) with
| (kwd, arg) -> begin
(let _0_388 = (str "@")
in (let _0_387 = (let _0_386 = (str kwd)
in (let _0_385 = (let _0_384 = (str arg)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_384))
in (FStar_Pprint.op_Hat_Hat _0_386 _0_385)))
in (FStar_Pprint.op_Hat_Hat _0_388 _0_387)))
end))
in (let _0_390 = (let _0_389 = (FStar_Pprint.separate_map FStar_Pprint.hardline process_kwd_arg kwd_args)
in (FStar_Pprint.op_Hat_Hat _0_389 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline _0_390)))
end)
in (let _0_398 = (let _0_397 = (let _0_396 = (let _0_395 = (let _0_394 = (str doc)
in (let _0_393 = (let _0_392 = (let _0_391 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _0_391))
in (FStar_Pprint.op_Hat_Hat kwd_args_doc _0_392))
in (FStar_Pprint.op_Hat_Hat _0_394 _0_393)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _0_395))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _0_396))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _0_397))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline _0_398)))
end))
and p_rawDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Open (uid) -> begin
(FStar_Pprint.group (let _0_400 = (str "open")
in (let _0_399 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat _0_400 _0_399))))
end
| FStar_Parser_AST.Include (uid) -> begin
(FStar_Pprint.group (let _0_402 = (str "include")
in (let _0_401 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat _0_402 _0_401))))
end
| FStar_Parser_AST.ModuleAbbrev (uid1, uid2) -> begin
(let _0_409 = (let _0_407 = (str "module")
in (let _0_406 = (let _0_405 = (let _0_404 = (p_uident uid1)
in (let _0_403 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _0_404 _0_403)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_405))
in (FStar_Pprint.op_Hat_Hat _0_407 _0_406)))
in (let _0_408 = (p_quident uid2)
in (op_Hat_Slash_Plus_Hat _0_409 _0_408)))
end
| FStar_Parser_AST.TopLevelModule (uid) -> begin
(FStar_Pprint.group (let _0_412 = (str "module")
in (let _0_411 = (let _0_410 = (p_quident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_410))
in (FStar_Pprint.op_Hat_Hat _0_412 _0_411))))
end
| FStar_Parser_AST.KindAbbrev (uu____1725) -> begin
(failwith "Deprecated, please stop throwing your old stuff at me !")
end
| FStar_Parser_AST.Tycon (true, ((FStar_Parser_AST.TyconAbbrev (uid, tpars, None, t), None))::[]) -> begin
(

let effect_prefix_doc = (let _0_415 = (str "effect")
in (let _0_414 = (let _0_413 = (p_uident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_413))
in (FStar_Pprint.op_Hat_Hat _0_415 _0_414)))
in (let _0_418 = (let _0_416 = (p_typars tpars)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") effect_prefix_doc _0_416 FStar_Pprint.equals))
in (let _0_417 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _0_418 _0_417))))
end
| FStar_Parser_AST.Tycon (false, tcdefs) -> begin
(let _0_420 = (str "type")
in (let _0_419 = (str "and")
in (precede_break_separate_map _0_420 _0_419 p_fsdocTypeDeclPairs tcdefs)))
end
| FStar_Parser_AST.TopLevelLet (q, lbs) -> begin
(

let let_doc = (let _0_423 = (str "let")
in (let _0_422 = (let _0_421 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat _0_421 FStar_Pprint.space))
in (FStar_Pprint.op_Hat_Hat _0_423 _0_422)))
in (let _0_425 = (let _0_424 = (str "and")
in (FStar_Pprint.op_Hat_Hat _0_424 FStar_Pprint.space))
in (separate_map_with_comments let_doc _0_425 p_letbinding lbs (fun uu____1771 -> (match (uu____1771) with
| (p, t) -> begin
(FStar_Range.union_ranges p.FStar_Parser_AST.prange t.FStar_Parser_AST.range)
end)))))
end
| FStar_Parser_AST.Val (lid, t) -> begin
(let _0_432 = (let _0_430 = (str "val")
in (let _0_429 = (let _0_428 = (let _0_427 = (p_lident lid)
in (let _0_426 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat _0_427 _0_426)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_428))
in (FStar_Pprint.op_Hat_Hat _0_430 _0_429)))
in (let _0_431 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _0_432 _0_431)))
end
| FStar_Parser_AST.Assume (id, t) -> begin
(

let decl_keyword = (

let uu____1781 = (let _0_433 = (FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_All.pipe_right _0_433 FStar_Util.is_upper))
in (match (uu____1781) with
| true -> begin
FStar_Pprint.empty
end
| uu____1782 -> begin
(let _0_434 = (str "val")
in (FStar_Pprint.op_Hat_Hat _0_434 FStar_Pprint.space))
end))
in (let _0_439 = (let _0_437 = (let _0_436 = (p_ident id)
in (let _0_435 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat _0_436 _0_435)))
in (FStar_Pprint.op_Hat_Hat decl_keyword _0_437))
in (let _0_438 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _0_439 _0_438))))
end
| FStar_Parser_AST.Exception (uid, t_opt) -> begin
(let _0_446 = (str "exception")
in (let _0_445 = (let _0_444 = (let _0_443 = (p_uident uid)
in (let _0_442 = (FStar_Pprint.optional (fun t -> (let _0_441 = (str "of")
in (let _0_440 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _0_441 _0_440)))) t_opt)
in (FStar_Pprint.op_Hat_Hat _0_443 _0_442)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_444))
in (FStar_Pprint.op_Hat_Hat _0_446 _0_445)))
end
| FStar_Parser_AST.NewEffect (ne) -> begin
(let _0_449 = (str "new_effect")
in (let _0_448 = (let _0_447 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_447))
in (FStar_Pprint.op_Hat_Hat _0_449 _0_448)))
end
| FStar_Parser_AST.SubEffect (se) -> begin
(let _0_452 = (str "sub_effect")
in (let _0_451 = (let _0_450 = (p_subEffect se)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_450))
in (FStar_Pprint.op_Hat_Hat _0_452 _0_451)))
end
| FStar_Parser_AST.NewEffectForFree (ne) -> begin
(let _0_455 = (str "new_effect_for_free")
in (let _0_454 = (let _0_453 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_453))
in (FStar_Pprint.op_Hat_Hat _0_455 _0_454)))
end
| FStar_Parser_AST.Pragma (p) -> begin
(p_pragma p)
end
| FStar_Parser_AST.Fsdoc (doc) -> begin
(let _0_456 = (p_fsdoc doc)
in (FStar_Pprint.op_Hat_Hat _0_456 FStar_Pprint.hardline))
end
| FStar_Parser_AST.Main (uu____1793) -> begin
(failwith "*Main declaration* : Is that really still in use ??")
end
| FStar_Parser_AST.Tycon (true, uu____1794) -> begin
(failwith "Effect abbreviation is expected to be defined by an abbreviation")
end))
and p_pragma : FStar_Parser_AST.pragma  ->  FStar_Pprint.document = (fun uu___116_1803 -> (match (uu___116_1803) with
| FStar_Parser_AST.SetOptions (s) -> begin
(let _0_459 = (str "#set-options")
in (let _0_458 = (let _0_457 = (FStar_Pprint.dquotes (str s))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_457))
in (FStar_Pprint.op_Hat_Hat _0_459 _0_458)))
end
| FStar_Parser_AST.ResetOptions (s_opt) -> begin
(let _0_462 = (str "#reset-options")
in (let _0_461 = (FStar_Pprint.optional (fun s -> (let _0_460 = (FStar_Pprint.dquotes (str s))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_460))) s_opt)
in (FStar_Pprint.op_Hat_Hat _0_462 _0_461)))
end
| FStar_Parser_AST.LightOff -> begin
((FStar_ST.write should_print_fs_typ_app true);
(str "#light \"off\"");
)
end))
and p_typars : FStar_Parser_AST.binder Prims.list  ->  FStar_Pprint.document = (fun bs -> (p_binders true bs))
and p_fsdocTypeDeclPairs : (FStar_Parser_AST.tycon * FStar_Parser_AST.fsdoc Prims.option)  ->  FStar_Pprint.document = (fun uu____1813 -> (match (uu____1813) with
| (typedecl, fsdoc_opt) -> begin
(let _0_464 = (FStar_Pprint.optional p_fsdoc fsdoc_opt)
in (let _0_463 = (p_typeDecl typedecl)
in (FStar_Pprint.op_Hat_Hat _0_464 _0_463)))
end))
and p_typeDecl : FStar_Parser_AST.tycon  ->  FStar_Pprint.document = (fun uu___117_1821 -> (match (uu___117_1821) with
| FStar_Parser_AST.TyconAbstract (lid, bs, typ_opt) -> begin
(

let empty' = (fun uu____1832 -> FStar_Pprint.empty)
in (p_typeDeclPrefix lid bs typ_opt empty'))
end
| FStar_Parser_AST.TyconAbbrev (lid, bs, typ_opt, t) -> begin
(

let f = (fun uu____1844 -> (let _0_465 = (p_typ t)
in (prefix2 FStar_Pprint.equals _0_465)))
in (p_typeDeclPrefix lid bs typ_opt f))
end
| FStar_Parser_AST.TyconRecord (lid, bs, typ_opt, record_field_decls) -> begin
(

let p_recordFieldAndComments = (fun uu____1870 -> (match (uu____1870) with
| (lid, t, doc_opt) -> begin
(let _0_466 = (FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range)
in (with_comment p_recordFieldDecl ((lid), (t), (doc_opt)) _0_466))
end))
in (

let p_fields = (fun uu____1888 -> (let _0_469 = (let _0_468 = (braces_with_nesting (let _0_467 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (FStar_Pprint.separate_map _0_467 p_recordFieldAndComments record_field_decls)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_468))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.equals _0_469)))
in (p_typeDeclPrefix lid bs typ_opt p_fields)))
end
| FStar_Parser_AST.TyconVariant (lid, bs, typ_opt, ct_decls) -> begin
(

let p_constructorBranchAndComments = (fun uu____1924 -> (match (uu____1924) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let range = (FStar_Range.extend_to_end_of_line (let _0_470 = (FStar_Util.map_opt t_opt (fun t -> t.FStar_Parser_AST.range))
in (FStar_Util.dflt uid.FStar_Ident.idRange _0_470)))
in (

let p_constructorBranch = (fun decl -> (FStar_Pprint.group (let _0_472 = (let _0_471 = (p_constructorDecl decl)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_471))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar _0_472))))
in (with_comment p_constructorBranch ((uid), (t_opt), (doc_opt), (use_of)) range)))
end))
in (

let datacon_doc = (fun uu____1968 -> (FStar_Pprint.group (FStar_Pprint.separate_map break1 p_constructorBranchAndComments ct_decls)))
in (p_typeDeclPrefix lid bs typ_opt (fun uu____1975 -> (let _0_473 = (datacon_doc ())
in (prefix2 FStar_Pprint.equals _0_473))))))
end))
and p_typeDeclPrefix : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.knd Prims.option  ->  (Prims.unit  ->  FStar_Pprint.document)  ->  FStar_Pprint.document = (fun lid bs typ_opt cont -> (match (((bs = []) && (typ_opt = None))) with
| true -> begin
(let _0_476 = (p_ident lid)
in (let _0_475 = (let _0_474 = (cont ())
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_474))
in (FStar_Pprint.op_Hat_Hat _0_476 _0_475)))
end
| uu____1986 -> begin
(

let binders_doc = (let _0_481 = (p_typars bs)
in (let _0_480 = (FStar_Pprint.optional (fun t -> (let _0_479 = (let _0_478 = (let _0_477 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_477))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _0_478))
in (FStar_Pprint.op_Hat_Hat break1 _0_479))) typ_opt)
in (FStar_Pprint.op_Hat_Hat _0_481 _0_480)))
in (let _0_483 = (p_ident lid)
in (let _0_482 = (cont ())
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _0_483 binders_doc _0_482))))
end))
and p_recordFieldDecl : (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc Prims.option)  ->  FStar_Pprint.document = (fun uu____1989 -> (match (uu____1989) with
| (lid, t, doc_opt) -> begin
(FStar_Pprint.group (let _0_488 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (let _0_487 = (let _0_486 = (p_lident lid)
in (let _0_485 = (let _0_484 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _0_484))
in (FStar_Pprint.op_Hat_Hat _0_486 _0_485)))
in (FStar_Pprint.op_Hat_Hat _0_488 _0_487))))
end))
and p_constructorDecl : (FStar_Ident.ident * FStar_Parser_AST.term Prims.option * FStar_Parser_AST.fsdoc Prims.option * Prims.bool)  ->  FStar_Pprint.document = (fun uu____1999 -> (match (uu____1999) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let sep = (match (use_of) with
| true -> begin
(str "of")
end
| uu____2015 -> begin
FStar_Pprint.colon
end)
in (

let uid_doc = (p_uident uid)
in (let _0_493 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (let _0_492 = (default_or_map uid_doc (fun t -> (let _0_491 = (let _0_489 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep)
in (FStar_Pprint.op_Hat_Hat uid_doc _0_489))
in (let _0_490 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _0_491 _0_490)))) t_opt)
in (FStar_Pprint.op_Hat_Hat _0_493 _0_492)))))
end))
and p_letbinding : (FStar_Parser_AST.pattern * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun uu____2018 -> (match (uu____2018) with
| (pat, e) -> begin
(

let pat_doc = (

let uu____2024 = (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, t) -> begin
(let _0_497 = (let _0_496 = (FStar_Pprint.group (let _0_495 = (let _0_494 = (p_tmArrow p_tmNoEq t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_494))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _0_495)))
in (FStar_Pprint.op_Hat_Hat break1 _0_496))
in ((pat), (_0_497)))
end
| uu____2031 -> begin
((pat), (FStar_Pprint.empty))
end)
in (match (uu____2024) with
| (pat, ascr_doc) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____2035); FStar_Parser_AST.prange = uu____2036}, pats) -> begin
(let _0_500 = (p_lident x)
in (let _0_499 = (let _0_498 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Hat _0_498 ascr_doc))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _0_500 _0_499 FStar_Pprint.equals)))
end
| uu____2042 -> begin
(FStar_Pprint.group (let _0_502 = (p_tuplePattern pat)
in (let _0_501 = (FStar_Pprint.op_Hat_Slash_Hat ascr_doc FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _0_502 _0_501))))
end)
end))
in (let _0_503 = (p_term e)
in (prefix2 pat_doc _0_503)))
end))
and p_newEffect : FStar_Parser_AST.effect_decl  ->  FStar_Pprint.document = (fun uu___118_2043 -> (match (uu___118_2043) with
| FStar_Parser_AST.RedefineEffect (lid, bs, t) -> begin
(p_effectRedefinition lid bs t)
end
| FStar_Parser_AST.DefineEffect (lid, bs, t, eff_decls, action_decls) -> begin
(p_effectDefinition lid bs t eff_decls action_decls)
end))
and p_effectRedefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun uid bs t -> (let _0_507 = (p_uident uid)
in (let _0_506 = (p_binders true bs)
in (let _0_505 = (let _0_504 = (p_simpleTerm t)
in (prefix2 FStar_Pprint.equals _0_504))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _0_507 _0_506 _0_505)))))
and p_effectDefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun uid bs t eff_decls action_decls -> (braces_with_nesting (let _0_517 = (FStar_Pprint.group (let _0_511 = (p_uident uid)
in (let _0_510 = (p_binders true bs)
in (let _0_509 = (let _0_508 = (p_typ t)
in (prefix2 FStar_Pprint.colon _0_508))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _0_511 _0_510 _0_509)))))
in (let _0_516 = (let _0_515 = (let _0_513 = (str "with")
in (let _0_512 = (separate_break_map FStar_Pprint.semi p_effectDecl eff_decls)
in (prefix2 _0_513 _0_512)))
in (let _0_514 = (p_actionDecls action_decls)
in (FStar_Pprint.op_Hat_Hat _0_515 _0_514)))
in (FStar_Pprint.op_Hat_Slash_Hat _0_517 _0_516)))))
and p_actionDecls : FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun uu___119_2072 -> (match (uu___119_2072) with
| [] -> begin
FStar_Pprint.empty
end
| l -> begin
(let _0_520 = (let _0_519 = (str "and actions")
in (let _0_518 = (separate_break_map FStar_Pprint.semi p_effectDecl l)
in (prefix2 _0_519 _0_518)))
in (FStar_Pprint.op_Hat_Hat break1 _0_520))
end))
and p_effectDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (false, ((FStar_Parser_AST.TyconAbbrev (lid, [], None, e), None))::[]) -> begin
(let _0_524 = (let _0_522 = (p_lident lid)
in (let _0_521 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _0_522 _0_521)))
in (let _0_523 = (p_simpleTerm e)
in (prefix2 _0_524 _0_523)))
end
| uu____2092 -> begin
(failwith (let _0_525 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "Not a declaration of an effect member... or at least I hope so : %s" _0_525)))
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

let p_lift = (fun uu____2125 -> (match (uu____2125) with
| (kwd, t) -> begin
(let _0_529 = (let _0_527 = (str kwd)
in (let _0_526 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _0_527 _0_526)))
in (let _0_528 = (p_simpleTerm t)
in (prefix2 _0_529 _0_528)))
end))
in (separate_break_map FStar_Pprint.semi p_lift lifts)))
in (let _0_537 = (let _0_534 = (let _0_532 = (p_quident lift.FStar_Parser_AST.msource)
in (let _0_531 = (let _0_530 = (str "~>")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_530))
in (FStar_Pprint.op_Hat_Hat _0_532 _0_531)))
in (let _0_533 = (p_quident lift.FStar_Parser_AST.mdest)
in (prefix2 _0_534 _0_533)))
in (let _0_536 = (let _0_535 = (braces_with_nesting lift_op_doc)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_535))
in (FStar_Pprint.op_Hat_Hat _0_537 _0_536)))))
and p_qualifier : FStar_Parser_AST.qualifier  ->  FStar_Pprint.document = (fun uu___120_2132 -> (match (uu___120_2132) with
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
and p_qualifiers : FStar_Parser_AST.qualifiers  ->  FStar_Pprint.document = (fun qs -> (FStar_Pprint.group (FStar_Pprint.separate_map break1 p_qualifier qs)))
and p_letqualifier : FStar_Parser_AST.let_qualifier  ->  FStar_Pprint.document = (fun uu___121_2134 -> (match (uu___121_2134) with
| FStar_Parser_AST.Rec -> begin
(let _0_538 = (str "rec")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_538))
end
| FStar_Parser_AST.Mutable -> begin
(let _0_539 = (str "mutable")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_539))
end
| FStar_Parser_AST.NoLetQualifier -> begin
FStar_Pprint.empty
end))
and p_aqual : FStar_Parser_AST.arg_qualifier  ->  FStar_Pprint.document = (fun uu___122_2135 -> (match (uu___122_2135) with
| FStar_Parser_AST.Implicit -> begin
(str "#")
end
| FStar_Parser_AST.Equality -> begin
(str "$")
end))
and p_disjunctivePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr (pats) -> begin
(FStar_Pprint.group (let _0_541 = (let _0_540 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space)
in (FStar_Pprint.op_Hat_Hat break1 _0_540))
in (FStar_Pprint.separate_map _0_541 p_tuplePattern pats)))
end
| uu____2139 -> begin
(p_tuplePattern p)
end))
and p_tuplePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTuple (pats, false) -> begin
(FStar_Pprint.group (let _0_542 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map _0_542 p_constructorPattern pats)))
end
| uu____2144 -> begin
(p_constructorPattern p)
end))
and p_constructorPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (maybe_cons_lid); FStar_Parser_AST.prange = uu____2147}, (hd)::(tl)::[]) when (FStar_Ident.lid_equals maybe_cons_lid FStar_Syntax_Const.cons_lid) -> begin
(let _0_545 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon)
in (let _0_544 = (p_constructorPattern hd)
in (let _0_543 = (p_constructorPattern tl)
in (infix0 _0_545 _0_544 _0_543))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (uid); FStar_Parser_AST.prange = uu____2152}, pats) -> begin
(let _0_547 = (p_quident uid)
in (let _0_546 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (prefix2 _0_547 _0_546)))
end
| uu____2156 -> begin
(p_atomicPattern p)
end))
and p_atomicPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, t) -> begin
(

let uu____2160 = (let _0_548 = (unparen t).FStar_Parser_AST.tm
in ((pat.FStar_Parser_AST.pat), (_0_548)))
in (match (uu____2160) with
| (FStar_Parser_AST.PatVar (lid, aqual), FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t); FStar_Parser_AST.brange = uu____2167; FStar_Parser_AST.blevel = uu____2168; FStar_Parser_AST.aqual = uu____2169}, phi)) when (lid.FStar_Ident.idText = lid'.FStar_Ident.idText) -> begin
(soft_parens_with_nesting (let _0_549 = (p_ident lid)
in (p_refinement aqual _0_549 t phi)))
end
| (FStar_Parser_AST.PatWild, FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t); FStar_Parser_AST.brange = uu____2174; FStar_Parser_AST.blevel = uu____2175; FStar_Parser_AST.aqual = uu____2176}, phi)) -> begin
(soft_parens_with_nesting (p_refinement None FStar_Pprint.underscore t phi))
end
| uu____2178 -> begin
(soft_parens_with_nesting (let _0_554 = (p_tuplePattern pat)
in (let _0_553 = (let _0_552 = (FStar_Pprint.break_ (Prims.parse_int "0"))
in (let _0_551 = (let _0_550 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _0_550))
in (FStar_Pprint.op_Hat_Hat _0_552 _0_551)))
in (FStar_Pprint.op_Hat_Hat _0_554 _0_553))))
end))
end
| FStar_Parser_AST.PatList (pats) -> begin
(let _0_555 = (separate_break_map FStar_Pprint.semi p_tuplePattern pats)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket _0_555 FStar_Pprint.rbracket))
end
| FStar_Parser_AST.PatRecord (pats) -> begin
(

let p_recordFieldPat = (fun uu____2192 -> (match (uu____2192) with
| (lid, pat) -> begin
(let _0_557 = (p_qlident lid)
in (let _0_556 = (p_tuplePattern pat)
in (infix2 FStar_Pprint.equals _0_557 _0_556)))
end))
in (soft_braces_with_nesting (separate_break_map FStar_Pprint.semi p_recordFieldPat pats)))
end
| FStar_Parser_AST.PatTuple (pats, true) -> begin
(let _0_560 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (let _0_559 = (separate_break_map FStar_Pprint.comma p_constructorPattern pats)
in (let _0_558 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _0_560 _0_559 _0_558))))
end
| FStar_Parser_AST.PatTvar (tv, arg_qualifier_opt) -> begin
(p_tvar tv)
end
| FStar_Parser_AST.PatOp (op) -> begin
(let _0_564 = (let _0_563 = (let _0_562 = (str op)
in (let _0_561 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat _0_562 _0_561)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_563))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _0_564))
end
| FStar_Parser_AST.PatWild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.PatConst (c) -> begin
(p_constant c)
end
| FStar_Parser_AST.PatVar (lid, aqual) -> begin
(let _0_566 = (FStar_Pprint.optional p_aqual aqual)
in (let _0_565 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat _0_566 _0_565)))
end
| FStar_Parser_AST.PatName (uid) -> begin
(p_quident uid)
end
| FStar_Parser_AST.PatOr (uu____2214) -> begin
(failwith "Inner or pattern !")
end
| (FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (_); FStar_Parser_AST.prange = _}, _)) | (FStar_Parser_AST.PatTuple (_, false)) -> begin
(soft_parens_with_nesting (p_tuplePattern p))
end
| uu____2222 -> begin
(failwith (let _0_567 = (FStar_Parser_AST.pat_to_string p)
in (FStar_Util.format1 "Invalid pattern %s" _0_567)))
end))
and p_binder : Prims.bool  ->  FStar_Parser_AST.binder  ->  FStar_Pprint.document = (fun is_atomic b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (lid) -> begin
(let _0_569 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (let _0_568 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat _0_569 _0_568)))
end
| FStar_Parser_AST.TVariable (lid) -> begin
(p_lident lid)
end
| FStar_Parser_AST.Annotated (lid, t) -> begin
(

let doc = (

let uu____2230 = (unparen t).FStar_Parser_AST.tm
in (match (uu____2230) with
| FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t); FStar_Parser_AST.brange = uu____2233; FStar_Parser_AST.blevel = uu____2234; FStar_Parser_AST.aqual = uu____2235}, phi) when (lid.FStar_Ident.idText = lid'.FStar_Ident.idText) -> begin
(let _0_570 = (p_ident lid)
in (p_refinement b.FStar_Parser_AST.aqual _0_570 t phi))
end
| uu____2237 -> begin
(let _0_577 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (let _0_576 = (let _0_575 = (p_lident lid)
in (let _0_574 = (let _0_573 = (let _0_572 = (FStar_Pprint.break_ (Prims.parse_int "0"))
in (let _0_571 = (p_tmFormula t)
in (FStar_Pprint.op_Hat_Hat _0_572 _0_571)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _0_573))
in (FStar_Pprint.op_Hat_Hat _0_575 _0_574)))
in (FStar_Pprint.op_Hat_Hat _0_577 _0_576)))
end))
in (match (is_atomic) with
| true -> begin
(FStar_Pprint.group (let _0_578 = (FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _0_578)))
end
| uu____2238 -> begin
(FStar_Pprint.group doc)
end))
end
| FStar_Parser_AST.TAnnotated (uu____2239) -> begin
(failwith "Is this still used ?")
end
| FStar_Parser_AST.NoName (t) -> begin
(

let uu____2243 = (unparen t).FStar_Parser_AST.tm
in (match (uu____2243) with
| FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t); FStar_Parser_AST.brange = uu____2245; FStar_Parser_AST.blevel = uu____2246; FStar_Parser_AST.aqual = uu____2247}, phi) -> begin
(match (is_atomic) with
| true -> begin
(FStar_Pprint.group (let _0_580 = (let _0_579 = (p_refinement b.FStar_Parser_AST.aqual FStar_Pprint.underscore t phi)
in (FStar_Pprint.op_Hat_Hat _0_579 FStar_Pprint.rparen))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _0_580)))
end
| uu____2249 -> begin
(FStar_Pprint.group (p_refinement b.FStar_Parser_AST.aqual FStar_Pprint.underscore t phi))
end)
end
| uu____2250 -> begin
(match (is_atomic) with
| true -> begin
(p_atomicTerm t)
end
| uu____2251 -> begin
(p_appTerm t)
end)
end))
end))
and p_refinement : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Pprint.document  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun aqual_opt binder t phi -> (let _0_586 = (FStar_Pprint.optional p_aqual aqual_opt)
in (let _0_585 = (let _0_584 = (let _0_583 = (let _0_582 = (p_appTerm t)
in (let _0_581 = (soft_braces_with_nesting (p_noSeqTerm phi))
in (FStar_Pprint.op_Hat_Hat _0_582 _0_581)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _0_583))
in (FStar_Pprint.op_Hat_Hat binder _0_584))
in (FStar_Pprint.op_Hat_Hat _0_586 _0_585))))
and p_binders : Prims.bool  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Pprint.document = (fun is_atomic bs -> (FStar_Pprint.separate_map break1 (p_binder is_atomic) bs))
and p_qlident : FStar_Ident.lid  ->  FStar_Pprint.document = (fun lid -> (str (FStar_Ident.text_of_lid lid)))
and p_quident : FStar_Ident.lid  ->  FStar_Pprint.document = (fun lid -> (str (FStar_Ident.text_of_lid lid)))
and p_ident : FStar_Ident.ident  ->  FStar_Pprint.document = (fun lid -> (str (FStar_Ident.text_of_id lid)))
and p_lident : FStar_Ident.ident  ->  FStar_Pprint.document = (fun lid -> (str (FStar_Ident.text_of_id lid)))
and p_uident : FStar_Ident.ident  ->  FStar_Pprint.document = (fun lid -> (str (FStar_Ident.text_of_id lid)))
and p_tvar : FStar_Ident.ident  ->  FStar_Pprint.document = (fun lid -> (str (FStar_Ident.text_of_id lid)))
and p_lidentOrUnderscore : FStar_Ident.ident  ->  FStar_Pprint.document = (fun id -> (match ((FStar_Util.starts_with FStar_Ident.reserved_prefix id.FStar_Ident.idText)) with
| true -> begin
FStar_Pprint.underscore
end
| uu____2267 -> begin
(p_lident id)
end))
and p_term : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2269 = (unparen e).FStar_Parser_AST.tm
in (match (uu____2269) with
| FStar_Parser_AST.Seq (e1, e2) -> begin
(let _0_589 = (FStar_Pprint.group (let _0_587 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat _0_587 FStar_Pprint.semi)))
in (let _0_588 = (p_term e2)
in (FStar_Pprint.op_Hat_Slash_Hat _0_589 _0_588)))
end
| uu____2272 -> begin
(FStar_Pprint.group (p_noSeqTerm e))
end)))
and p_noSeqTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_noSeqTerm' e e.FStar_Parser_AST.range))
and p_noSeqTerm' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2275 = (unparen e).FStar_Parser_AST.tm
in (match (uu____2275) with
| FStar_Parser_AST.Ascribed (e, t) -> begin
(FStar_Pprint.group (let _0_593 = (p_tmIff e)
in (let _0_592 = (let _0_591 = (let _0_590 = (p_typ t)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon _0_590))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.langle _0_591))
in (FStar_Pprint.op_Hat_Slash_Hat _0_593 _0_592))))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::(e3)::[]) when (op = ".()<-") -> begin
(FStar_Pprint.group (let _0_600 = (FStar_Pprint.group (let _0_598 = (p_atomicTermNotQUident e1)
in (let _0_597 = (let _0_596 = (let _0_595 = (soft_parens_with_nesting (p_term e2))
in (let _0_594 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat _0_595 _0_594)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _0_596))
in (FStar_Pprint.op_Hat_Hat _0_598 _0_597))))
in (let _0_599 = (jump2 (p_noSeqTerm e3))
in (FStar_Pprint.op_Hat_Hat _0_600 _0_599))))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::(e3)::[]) when (op = ".[]<-") -> begin
(FStar_Pprint.group (let _0_607 = (FStar_Pprint.group (let _0_605 = (p_atomicTermNotQUident e1)
in (let _0_604 = (let _0_603 = (let _0_602 = (soft_brackets_with_nesting (p_term e2))
in (let _0_601 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat _0_602 _0_601)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _0_603))
in (FStar_Pprint.op_Hat_Hat _0_605 _0_604))))
in (let _0_606 = (jump2 (p_noSeqTerm e3))
in (FStar_Pprint.op_Hat_Hat _0_607 _0_606))))
end
| FStar_Parser_AST.Requires (e, wtf) -> begin
(FStar_Pprint.group (let _0_609 = (str "requires")
in (let _0_608 = (p_typ e)
in (FStar_Pprint.op_Hat_Slash_Hat _0_609 _0_608))))
end
| FStar_Parser_AST.Ensures (e, wtf) -> begin
(FStar_Pprint.group (let _0_611 = (str "ensures")
in (let _0_610 = (p_typ e)
in (FStar_Pprint.op_Hat_Slash_Hat _0_611 _0_610))))
end
| FStar_Parser_AST.Attributes (es) -> begin
(FStar_Pprint.group (let _0_613 = (str "attributes")
in (let _0_612 = (FStar_Pprint.separate_map break1 p_atomicTerm es)
in (FStar_Pprint.op_Hat_Slash_Hat _0_613 _0_612))))
end
| FStar_Parser_AST.If (e1, e2, e3) -> begin
(

let uu____2303 = (is_unit e3)
in (match (uu____2303) with
| true -> begin
(FStar_Pprint.group (let _0_619 = (let _0_615 = (str "if")
in (let _0_614 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat _0_615 _0_614)))
in (let _0_618 = (let _0_617 = (str "then")
in (let _0_616 = (p_noSeqTerm e2)
in (op_Hat_Slash_Plus_Hat _0_617 _0_616)))
in (FStar_Pprint.op_Hat_Slash_Hat _0_619 _0_618))))
end
| uu____2304 -> begin
(

let e2_doc = (

let uu____2306 = (unparen e2).FStar_Parser_AST.tm
in (match (uu____2306) with
| FStar_Parser_AST.If (uu____2307, uu____2308, e3) when (is_unit e3) -> begin
(soft_parens_with_nesting (p_noSeqTerm e2))
end
| uu____2310 -> begin
(p_noSeqTerm e2)
end))
in (FStar_Pprint.group (let _0_628 = (let _0_621 = (str "if")
in (let _0_620 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat _0_621 _0_620)))
in (let _0_627 = (let _0_626 = (let _0_622 = (str "then")
in (op_Hat_Slash_Plus_Hat _0_622 e2_doc))
in (let _0_625 = (let _0_624 = (str "else")
in (let _0_623 = (p_noSeqTerm e3)
in (op_Hat_Slash_Plus_Hat _0_624 _0_623)))
in (FStar_Pprint.op_Hat_Slash_Hat _0_626 _0_625)))
in (FStar_Pprint.op_Hat_Slash_Hat _0_628 _0_627)))))
end))
end
| FStar_Parser_AST.TryWith (e, branches) -> begin
(FStar_Pprint.group (let _0_634 = (let _0_630 = (str "try")
in (let _0_629 = (p_noSeqTerm e)
in (prefix2 _0_630 _0_629)))
in (let _0_633 = (let _0_632 = (str "with")
in (let _0_631 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat _0_632 _0_631)))
in (FStar_Pprint.op_Hat_Slash_Hat _0_634 _0_633))))
end
| FStar_Parser_AST.Match (e, branches) -> begin
(FStar_Pprint.group (let _0_639 = (let _0_637 = (str "match")
in (let _0_636 = (p_noSeqTerm e)
in (let _0_635 = (str "with")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _0_637 _0_636 _0_635))))
in (let _0_638 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat _0_639 _0_638))))
end
| FStar_Parser_AST.LetOpen (uid, e) -> begin
(FStar_Pprint.group (let _0_644 = (let _0_642 = (str "let open")
in (let _0_641 = (p_quident uid)
in (let _0_640 = (str "in")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _0_642 _0_641 _0_640))))
in (let _0_643 = (p_term e)
in (FStar_Pprint.op_Hat_Slash_Hat _0_644 _0_643))))
end
| FStar_Parser_AST.Let (q, lbs, e) -> begin
(

let let_doc = (let _0_646 = (str "let")
in (let _0_645 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat _0_646 _0_645)))
in (let _0_651 = (FStar_Pprint.group (let _0_649 = (let _0_647 = (str "and")
in (precede_break_separate_map let_doc _0_647 p_letbinding lbs))
in (let _0_648 = (str "in")
in (FStar_Pprint.op_Hat_Slash_Hat _0_649 _0_648))))
in (let _0_650 = (p_term e)
in (FStar_Pprint.op_Hat_Slash_Hat _0_651 _0_650))))
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, typ_opt); FStar_Parser_AST.prange = uu____2359})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, branches); FStar_Parser_AST.range = uu____2362; FStar_Parser_AST.level = uu____2363}) when (matches_var maybe_x x) -> begin
(FStar_Pprint.group (let _0_653 = (str "function")
in (let _0_652 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat _0_653 _0_652))))
end
| FStar_Parser_AST.Assign (id, e) -> begin
(FStar_Pprint.group (let _0_656 = (p_lident id)
in (let _0_655 = (let _0_654 = (p_noSeqTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow _0_654))
in (FStar_Pprint.op_Hat_Slash_Hat _0_656 _0_655))))
end
| uu____2383 -> begin
(p_typ e)
end)))
and p_typ : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_typ' e e.FStar_Parser_AST.range))
and p_typ' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2386 = (unparen e).FStar_Parser_AST.tm
in (match (uu____2386) with
| (FStar_Parser_AST.QForall (bs, trigger, e1)) | (FStar_Parser_AST.QExists (bs, trigger, e1)) -> begin
(let _0_663 = (let _0_659 = (let _0_657 = (p_quantifier e)
in (FStar_Pprint.op_Hat_Hat _0_657 FStar_Pprint.space))
in (let _0_658 = (p_binders true bs)
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") _0_659 _0_658 FStar_Pprint.dot)))
in (let _0_662 = (let _0_661 = (p_trigger trigger)
in (let _0_660 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat _0_661 _0_660)))
in (prefix2 _0_663 _0_662)))
end
| uu____2402 -> begin
(p_simpleTerm e)
end)))
and p_quantifier : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2404 = (unparen e).FStar_Parser_AST.tm
in (match (uu____2404) with
| FStar_Parser_AST.QForall (uu____2405) -> begin
(str "forall")
end
| FStar_Parser_AST.QExists (uu____2412) -> begin
(str "exists")
end
| uu____2419 -> begin
(failwith "Imposible : p_quantifier called on a non-quantifier term")
end)))
and p_trigger : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun uu___123_2420 -> (match (uu___123_2420) with
| [] -> begin
FStar_Pprint.empty
end
| pats -> begin
(let _0_669 = (let _0_668 = (let _0_667 = (str "pattern")
in (let _0_666 = (let _0_665 = (jump2 (p_disjunctivePats pats))
in (let _0_664 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1)
in (FStar_Pprint.op_Hat_Slash_Hat _0_665 _0_664)))
in (FStar_Pprint.op_Hat_Slash_Hat _0_667 _0_666)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _0_668))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace _0_669))
end))
and p_disjunctivePats : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun pats -> (let _0_670 = (str "\\/")
in (FStar_Pprint.separate_map _0_670 p_conjunctivePats pats)))
and p_conjunctivePats : FStar_Parser_AST.term Prims.list  ->  FStar_Pprint.document = (fun pats -> (FStar_Pprint.group (FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats)))
and p_simpleTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2434 = (unparen e).FStar_Parser_AST.tm
in (match (uu____2434) with
| FStar_Parser_AST.Abs (pats, e) -> begin
(let _0_675 = (let _0_673 = (str "fun")
in (let _0_672 = (let _0_671 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Slash_Hat _0_671 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat _0_673 _0_672)))
in (let _0_674 = (p_term e)
in (op_Hat_Slash_Plus_Hat _0_675 _0_674)))
end
| uu____2439 -> begin
(p_tmIff e)
end)))
and p_maybeFocusArrow : Prims.bool  ->  FStar_Pprint.document = (fun b -> (match (b) with
| true -> begin
(str "~>")
end
| uu____2441 -> begin
FStar_Pprint.rarrow
end))
and p_patternBranch : (FStar_Parser_AST.pattern * FStar_Parser_AST.term Prims.option * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun uu____2442 -> (match (uu____2442) with
| (pat, when_opt, e) -> begin
(

let maybe_paren = (

let uu____2455 = (unparen e).FStar_Parser_AST.tm
in (match (uu____2455) with
| (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) -> begin
soft_begin_end_with_nesting
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____2461); FStar_Parser_AST.prange = uu____2462})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, uu____2464); FStar_Parser_AST.range = uu____2465; FStar_Parser_AST.level = uu____2466}) when (matches_var maybe_x x) -> begin
soft_begin_end_with_nesting
end
| uu____2480 -> begin
(fun x -> x)
end))
in (FStar_Pprint.group (let _0_682 = (FStar_Pprint.group (let _0_680 = (let _0_679 = (let _0_678 = (p_disjunctivePattern pat)
in (let _0_677 = (let _0_676 = (p_maybeWhen when_opt)
in (FStar_Pprint.op_Hat_Hat _0_676 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat _0_678 _0_677)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_679))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar _0_680)))
in (let _0_681 = (maybe_paren (p_term e))
in (op_Hat_Slash_Plus_Hat _0_682 _0_681)))))
end))
and p_maybeWhen : FStar_Parser_AST.term Prims.option  ->  FStar_Pprint.document = (fun uu___124_2482 -> (match (uu___124_2482) with
| None -> begin
FStar_Pprint.empty
end
| Some (e) -> begin
(let _0_685 = (str "when")
in (let _0_684 = (let _0_683 = (p_tmFormula e)
in (FStar_Pprint.op_Hat_Hat _0_683 FStar_Pprint.space))
in (op_Hat_Slash_Plus_Hat _0_685 _0_684)))
end))
and p_tmIff : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2486 = (unparen e).FStar_Parser_AST.tm
in (match (uu____2486) with
| FStar_Parser_AST.Op ("<==>", (e1)::(e2)::[]) -> begin
(let _0_688 = (str "<==>")
in (let _0_687 = (p_tmImplies e1)
in (let _0_686 = (p_tmIff e2)
in (infix0 _0_688 _0_687 _0_686))))
end
| uu____2490 -> begin
(p_tmImplies e)
end)))
and p_tmImplies : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2492 = (unparen e).FStar_Parser_AST.tm
in (match (uu____2492) with
| FStar_Parser_AST.Op ("==>", (e1)::(e2)::[]) -> begin
(let _0_691 = (str "==>")
in (let _0_690 = (p_tmArrow p_tmFormula e1)
in (let _0_689 = (p_tmImplies e2)
in (infix0 _0_691 _0_690 _0_689))))
end
| uu____2496 -> begin
(p_tmArrow p_tmFormula e)
end)))
and p_tmArrow : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_Tm e -> (

let uu____2501 = (unparen e).FStar_Parser_AST.tm
in (match (uu____2501) with
| FStar_Parser_AST.Product (bs, tgt) -> begin
(FStar_Pprint.group (let _0_696 = (FStar_Pprint.concat_map (fun b -> (let _0_694 = (p_binder false b)
in (let _0_693 = (let _0_692 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_692))
in (FStar_Pprint.op_Hat_Hat _0_694 _0_693)))) bs)
in (let _0_695 = (p_tmArrow p_Tm tgt)
in (FStar_Pprint.op_Hat_Hat _0_696 _0_695))))
end
| uu____2507 -> begin
(p_Tm e)
end)))
and p_tmFormula : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2509 = (unparen e).FStar_Parser_AST.tm
in (match (uu____2509) with
| FStar_Parser_AST.Op ("\\/", (e1)::(e2)::[]) -> begin
(let _0_699 = (str "\\/")
in (let _0_698 = (p_tmFormula e1)
in (let _0_697 = (p_tmConjunction e2)
in (infix0 _0_699 _0_698 _0_697))))
end
| uu____2513 -> begin
(p_tmConjunction e)
end)))
and p_tmConjunction : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2515 = (unparen e).FStar_Parser_AST.tm
in (match (uu____2515) with
| FStar_Parser_AST.Op ("/\\", (e1)::(e2)::[]) -> begin
(let _0_702 = (str "/\\")
in (let _0_701 = (p_tmConjunction e1)
in (let _0_700 = (p_tmTuple e2)
in (infix0 _0_702 _0_701 _0_700))))
end
| uu____2519 -> begin
(p_tmTuple e)
end)))
and p_tmTuple : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_tmTuple' e e.FStar_Parser_AST.range))
and p_tmTuple' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2522 = (unparen e).FStar_Parser_AST.tm
in (match (uu____2522) with
| FStar_Parser_AST.Construct (lid, args) when (is_tuple_constructor lid) -> begin
(let _0_703 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map _0_703 (fun uu____2533 -> (match (uu____2533) with
| (e, uu____2537) -> begin
(p_tmEq e)
end)) args))
end
| uu____2538 -> begin
(p_tmEq e)
end)))
and paren_if : Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun curr mine doc -> (match ((mine <= curr)) with
| true -> begin
doc
end
| uu____2542 -> begin
(FStar_Pprint.group (let _0_704 = (FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _0_704)))
end))
and p_tmEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n = (max_level (FStar_List.append (((colon_equals ()))::((pipe_right ()))::[]) (operatorInfix0ad12 ())))
in (p_tmEq' n e)))
and p_tmEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (

let uu____2567 = (unparen e).FStar_Parser_AST.tm
in (match (uu____2567) with
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (((is_operatorInfix0ad12 op) || (op = "=")) || (op = "|>")) -> begin
(

let uu____2572 = (levels op)
in (match (uu____2572) with
| (left, mine, right) -> begin
(let _0_708 = (let _0_707 = (str op)
in (let _0_706 = (p_tmEq' left e1)
in (let _0_705 = (p_tmEq' right e2)
in (infix0 _0_707 _0_706 _0_705))))
in (paren_if curr mine _0_708))
end))
end
| FStar_Parser_AST.Op (":=", (e1)::(e2)::[]) -> begin
(FStar_Pprint.group (let _0_713 = (p_tmEq e1)
in (let _0_712 = (let _0_711 = (let _0_710 = (let _0_709 = (p_tmEq e2)
in (op_Hat_Slash_Plus_Hat FStar_Pprint.equals _0_709))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _0_710))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_711))
in (FStar_Pprint.op_Hat_Hat _0_713 _0_712))))
end
| uu____2582 -> begin
(p_tmNoEq e)
end)))
and p_tmNoEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n = (max_level (((colon_colon ()))::((amp ()))::((opinfix3 ()))::((opinfix4 ()))::[]))
in (p_tmNoEq' n e)))
and p_tmNoEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (

let uu____2612 = (unparen e).FStar_Parser_AST.tm
in (match (uu____2612) with
| FStar_Parser_AST.Construct (lid, ((e1, uu____2615))::((e2, uu____2617))::[]) when ((FStar_Ident.lid_equals lid FStar_Syntax_Const.cons_lid) && (not ((is_list e)))) -> begin
(

let op = "::"
in (

let uu____2628 = (levels op)
in (match (uu____2628) with
| (left, mine, right) -> begin
(let _0_717 = (let _0_716 = (str op)
in (let _0_715 = (p_tmNoEq' left e1)
in (let _0_714 = (p_tmNoEq' right e2)
in (infix0 _0_716 _0_715 _0_714))))
in (paren_if curr mine _0_717))
end)))
end
| FStar_Parser_AST.Sum (binders, res) -> begin
(

let op = "&"
in (

let uu____2640 = (levels op)
in (match (uu____2640) with
| (left, mine, right) -> begin
(

let p_dsumfst = (fun b -> (let _0_721 = (p_binder false b)
in (let _0_720 = (let _0_719 = (let _0_718 = (str "&")
in (FStar_Pprint.op_Hat_Hat _0_718 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_719))
in (FStar_Pprint.op_Hat_Hat _0_721 _0_720))))
in (let _0_724 = (let _0_723 = (FStar_Pprint.concat_map p_dsumfst binders)
in (let _0_722 = (p_tmNoEq' right res)
in (FStar_Pprint.op_Hat_Hat _0_723 _0_722)))
in (paren_if curr mine _0_724)))
end)))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (is_operatorInfix34 op) -> begin
(

let uu____2655 = (levels op)
in (match (uu____2655) with
| (left, mine, right) -> begin
(let _0_728 = (let _0_727 = (str op)
in (let _0_726 = (p_tmNoEq' left e1)
in (let _0_725 = (p_tmNoEq' right e2)
in (infix0 _0_727 _0_726 _0_725))))
in (paren_if curr mine _0_728))
end))
end
| FStar_Parser_AST.Op ("-", (e)::[]) -> begin
(

let uu____2664 = (levels "-")
in (match (uu____2664) with
| (left, mine, right) -> begin
(let _0_729 = (p_tmNoEq' mine e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus _0_729))
end))
end
| FStar_Parser_AST.NamedTyp (lid, e) -> begin
(FStar_Pprint.group (let _0_732 = (p_lidentOrUnderscore lid)
in (let _0_731 = (let _0_730 = (p_appTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon _0_730))
in (FStar_Pprint.op_Hat_Slash_Hat _0_732 _0_731))))
end
| FStar_Parser_AST.Refine (b, phi) -> begin
(p_refinedBinder b phi)
end
| FStar_Parser_AST.Record (with_opt, record_fields) -> begin
(braces_with_nesting (let _0_735 = (default_or_map FStar_Pprint.empty p_with_clause with_opt)
in (let _0_734 = (let _0_733 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (FStar_Pprint.separate_map _0_733 p_simpleDef record_fields))
in (FStar_Pprint.op_Hat_Hat _0_735 _0_734))))
end
| FStar_Parser_AST.Op ("~", (e)::[]) -> begin
(FStar_Pprint.group (let _0_737 = (str "~")
in (let _0_736 = (p_atomicTerm e)
in (FStar_Pprint.op_Hat_Hat _0_737 _0_736))))
end
| uu____2689 -> begin
(p_appTerm e)
end)))
and p_with_clause : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (let _0_741 = (p_appTerm e)
in (let _0_740 = (let _0_739 = (let _0_738 = (str "with")
in (FStar_Pprint.op_Hat_Hat _0_738 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_739))
in (FStar_Pprint.op_Hat_Hat _0_741 _0_740))))
and p_refinedBinder : FStar_Parser_AST.binder  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun b phi -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (lid, t) -> begin
(soft_parens_with_nesting (let _0_742 = (p_lident lid)
in (p_refinement b.FStar_Parser_AST.aqual _0_742 t phi)))
end
| FStar_Parser_AST.TAnnotated (uu____2695) -> begin
(failwith "Is this still used ?")
end
| (FStar_Parser_AST.Variable (_)) | (FStar_Parser_AST.TVariable (_)) | (FStar_Parser_AST.NoName (_)) -> begin
(failwith (let _0_743 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" _0_743)))
end))
and p_simpleDef : (FStar_Ident.lid * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun uu____2701 -> (match (uu____2701) with
| (lid, e) -> begin
(FStar_Pprint.group (let _0_746 = (p_qlident lid)
in (let _0_745 = (let _0_744 = (p_tmIff e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals _0_744))
in (FStar_Pprint.op_Hat_Slash_Hat _0_746 _0_745))))
end))
and p_appTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2707 = (unparen e).FStar_Parser_AST.tm
in (match (uu____2707) with
| FStar_Parser_AST.App (uu____2708) when (is_general_application e) -> begin
(

let uu____2712 = (head_and_args e)
in (match (uu____2712) with
| (head, args) -> begin
(

let uu____2726 = (

let uu____2732 = (FStar_ST.read should_print_fs_typ_app)
in (match (uu____2732) with
| true -> begin
(

let uu____2740 = (FStar_Util.take (fun uu____2751 -> (match (uu____2751) with
| (uu____2754, aq) -> begin
(aq = FStar_Parser_AST.FsTypApp)
end)) args)
in (match (uu____2740) with
| (fs_typ_args, args) -> begin
(let _0_750 = (let _0_749 = (p_indexingTerm head)
in (let _0_748 = (let _0_747 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (soft_surround_separate_map (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.empty FStar_Pprint.langle _0_747 FStar_Pprint.rangle p_fsTypArg fs_typ_args))
in (FStar_Pprint.op_Hat_Hat _0_749 _0_748)))
in ((_0_750), (args)))
end))
end
| uu____2780 -> begin
(let _0_751 = (p_indexingTerm head)
in ((_0_751), (args)))
end))
in (match (uu____2726) with
| (head_doc, args) -> begin
(FStar_Pprint.group (let _0_752 = (FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space)
in (soft_surround_separate_map (Prims.parse_int "2") (Prims.parse_int "0") head_doc _0_752 break1 FStar_Pprint.empty p_argTerm args)))
end))
end))
end
| FStar_Parser_AST.Construct (lid, args) when ((is_general_construction e) && (not ((is_dtuple_constructor lid)))) -> begin
(match (args) with
| [] -> begin
(p_quident lid)
end
| (arg)::[] -> begin
(FStar_Pprint.group (let _0_754 = (p_quident lid)
in (let _0_753 = (p_argTerm arg)
in (FStar_Pprint.op_Hat_Slash_Hat _0_754 _0_753))))
end
| (hd)::tl -> begin
(FStar_Pprint.group (let _0_758 = (FStar_Pprint.group (let _0_756 = (p_quident lid)
in (let _0_755 = (p_argTerm hd)
in (prefix2 _0_756 _0_755))))
in (let _0_757 = (jump2 (FStar_Pprint.separate_map break1 p_argTerm tl))
in (FStar_Pprint.op_Hat_Hat _0_758 _0_757))))
end)
end
| uu____2822 -> begin
(p_indexingTerm e)
end)))
and p_argTerm : (FStar_Parser_AST.term * FStar_Parser_AST.imp)  ->  FStar_Pprint.document = (fun arg_imp -> (match (arg_imp) with
| ({FStar_Parser_AST.tm = FStar_Parser_AST.Uvar (uu____2826); FStar_Parser_AST.range = uu____2827; FStar_Parser_AST.level = uu____2828}, FStar_Parser_AST.UnivApp) -> begin
(p_univar (Prims.fst arg_imp))
end
| (u, FStar_Parser_AST.UnivApp) -> begin
(p_universe u)
end
| (e, FStar_Parser_AST.FsTypApp) -> begin
((FStar_Util.print_warning "Unexpected FsTypApp, output might not be formatted correctly.\n");
(let _0_759 = (p_indexingTerm e)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.langle _0_759 FStar_Pprint.rangle));
)
end
| (e, FStar_Parser_AST.Hash) -> begin
(let _0_761 = (str "#")
in (let _0_760 = (p_indexingTerm e)
in (FStar_Pprint.op_Hat_Hat _0_761 _0_760)))
end
| (e, FStar_Parser_AST.Nothing) -> begin
(p_indexingTerm e)
end))
and p_fsTypArg : (FStar_Parser_AST.term * FStar_Parser_AST.imp)  ->  FStar_Pprint.document = (fun uu____2834 -> (match (uu____2834) with
| (e, uu____2838) -> begin
(p_indexingTerm e)
end))
and p_indexingTerm_aux : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun exit e -> (

let uu____2843 = (unparen e).FStar_Parser_AST.tm
in (match (uu____2843) with
| FStar_Parser_AST.Op (".()", (e1)::(e2)::[]) -> begin
(FStar_Pprint.group (let _0_764 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (let _0_763 = (let _0_762 = (soft_parens_with_nesting (p_term e2))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _0_762))
in (FStar_Pprint.op_Hat_Hat _0_764 _0_763))))
end
| FStar_Parser_AST.Op (".[]", (e1)::(e2)::[]) -> begin
(FStar_Pprint.group (let _0_767 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (let _0_766 = (let _0_765 = (soft_brackets_with_nesting (p_term e2))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _0_765))
in (FStar_Pprint.op_Hat_Hat _0_767 _0_766))))
end
| uu____2850 -> begin
(exit e)
end)))
and p_indexingTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_indexingTerm_aux p_atomicTerm e))
and p_atomicTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2853 = (unparen e).FStar_Parser_AST.tm
in (match (uu____2853) with
| FStar_Parser_AST.LetOpen (lid, e) -> begin
(let _0_770 = (p_quident lid)
in (let _0_769 = (let _0_768 = (soft_parens_with_nesting (p_term e))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _0_768))
in (FStar_Pprint.op_Hat_Hat _0_770 _0_769)))
end
| FStar_Parser_AST.Name (lid) -> begin
(p_quident lid)
end
| FStar_Parser_AST.Op (op, (e)::[]) when (is_general_prefix_op op) -> begin
(let _0_772 = (str op)
in (let _0_771 = (p_atomicTerm e)
in (FStar_Pprint.op_Hat_Hat _0_772 _0_771)))
end
| uu____2860 -> begin
(p_atomicTermNotQUident e)
end)))
and p_atomicTermNotQUident : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2862 = (unparen e).FStar_Parser_AST.tm
in (match (uu____2862) with
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
(let _0_774 = (str op)
in (let _0_773 = (p_atomicTermNotQUident e)
in (FStar_Pprint.op_Hat_Hat _0_774 _0_773)))
end
| FStar_Parser_AST.Op (op, []) -> begin
(let _0_778 = (let _0_777 = (let _0_776 = (str op)
in (let _0_775 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat _0_776 _0_775)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_777))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _0_778))
end
| FStar_Parser_AST.Construct (lid, args) when (is_dtuple_constructor lid) -> begin
(let _0_783 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (let _0_782 = (let _0_780 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (let _0_779 = (FStar_List.map Prims.fst args)
in (FStar_Pprint.separate_map _0_780 p_tmEq _0_779)))
in (let _0_781 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _0_783 _0_782 _0_781))))
end
| FStar_Parser_AST.Project (e, lid) -> begin
(FStar_Pprint.group (let _0_786 = (p_atomicTermNotQUident e)
in (let _0_785 = (let _0_784 = (p_qlident lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _0_784))
in (FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0") _0_786 _0_785))))
end
| uu____2885 -> begin
(p_projectionLHS e)
end)))
and p_projectionLHS : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2887 = (unparen e).FStar_Parser_AST.tm
in (match (uu____2887) with
| FStar_Parser_AST.Var (lid) -> begin
(p_qlident lid)
end
| FStar_Parser_AST.Projector (constr_lid, field_lid) -> begin
(let _0_790 = (p_quident constr_lid)
in (let _0_789 = (let _0_788 = (let _0_787 = (p_lident field_lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _0_787))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark _0_788))
in (FStar_Pprint.op_Hat_Hat _0_790 _0_789)))
end
| FStar_Parser_AST.Discrim (constr_lid) -> begin
(let _0_791 = (p_quident constr_lid)
in (FStar_Pprint.op_Hat_Hat _0_791 FStar_Pprint.qmark))
end
| FStar_Parser_AST.Paren (e) -> begin
(soft_parens_with_nesting (p_term e))
end
| uu____2893 when (is_array e) -> begin
(

let es = (extract_from_list e)
in (let _0_795 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar)
in (let _0_794 = (let _0_792 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (separate_map_or_flow _0_792 p_noSeqTerm es))
in (let _0_793 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") _0_795 _0_794 _0_793)))))
end
| uu____2896 when (is_list e) -> begin
(let _0_798 = (let _0_797 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (let _0_796 = (extract_from_list e)
in (separate_map_or_flow _0_797 p_noSeqTerm _0_796)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket _0_798 FStar_Pprint.rbracket))
end
| uu____2897 when (is_lex_list e) -> begin
(let _0_802 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket)
in (let _0_801 = (let _0_800 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (let _0_799 = (extract_from_list e)
in (separate_map_or_flow _0_800 p_noSeqTerm _0_799)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _0_802 _0_801 FStar_Pprint.rbracket)))
end
| uu____2898 when (is_ref_set e) -> begin
(

let es = (extract_from_ref_set e)
in (let _0_805 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace)
in (let _0_804 = (let _0_803 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (separate_map_or_flow _0_803 p_appTerm es))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") _0_805 _0_804 FStar_Pprint.rbrace))))
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Op (_)) | (FStar_Parser_AST.Tvar (_)) | (FStar_Parser_AST.Uvar (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) | (FStar_Parser_AST.Construct (_)) | (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.App (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.LetOpen (_)) | (FStar_Parser_AST.Seq (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Ascribed (_)) | (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Project (_)) | (FStar_Parser_AST.Product (_)) | (FStar_Parser_AST.Sum (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Refine (_)) | (FStar_Parser_AST.NamedTyp (_)) | (FStar_Parser_AST.Requires (_)) | (FStar_Parser_AST.Ensures (_)) | (FStar_Parser_AST.Assign (_)) | (FStar_Parser_AST.Attributes (_)) -> begin
(soft_parens_with_nesting (p_term e))
end
| FStar_Parser_AST.Labeled (uu____2929) -> begin
(failwith "Not valid in universe")
end)))
and p_constant : FStar_Const.sconst  ->  FStar_Pprint.document = (fun uu___127_2933 -> (match (uu___127_2933) with
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
(FStar_Pprint.squotes (FStar_Pprint.doc_of_char x))
end
| FStar_Const.Const_string (bytes, uu____2938) -> begin
(FStar_Pprint.dquotes (str (FStar_Util.string_of_bytes bytes)))
end
| FStar_Const.Const_bytearray (bytes, uu____2942) -> begin
(let _0_807 = (FStar_Pprint.dquotes (str (FStar_Util.string_of_bytes bytes)))
in (let _0_806 = (str "B")
in (FStar_Pprint.op_Hat_Hat _0_807 _0_806)))
end
| FStar_Const.Const_int (repr, sign_width_opt) -> begin
(

let signedness = (fun uu___125_2956 -> (match (uu___125_2956) with
| FStar_Const.Unsigned -> begin
(str "u")
end
| FStar_Const.Signed -> begin
FStar_Pprint.empty
end))
in (

let width = (fun uu___126_2960 -> (match (uu___126_2960) with
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

let ending = (default_or_map FStar_Pprint.empty (fun uu____2964 -> (match (uu____2964) with
| (s, w) -> begin
(let _0_809 = (signedness s)
in (let _0_808 = (width w)
in (FStar_Pprint.op_Hat_Hat _0_809 _0_808)))
end)) sign_width_opt)
in (let _0_810 = (str repr)
in (FStar_Pprint.op_Hat_Hat _0_810 ending)))))
end
| FStar_Const.Const_range (r) -> begin
(str (FStar_Range.string_of_range r))
end
| FStar_Const.Const_reify -> begin
(str "reify")
end
| FStar_Const.Const_reflect (lid) -> begin
(let _0_814 = (p_quident lid)
in (let _0_813 = (let _0_812 = (let _0_811 = (str "reflect")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _0_811))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark _0_812))
in (FStar_Pprint.op_Hat_Hat _0_814 _0_813)))
end))
and p_universe : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (let _0_816 = (str "u#")
in (let _0_815 = (p_atomicUniverse u)
in (FStar_Pprint.op_Hat_Hat _0_816 _0_815))))
and p_universeFrom : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (

let uu____2973 = (unparen u).FStar_Parser_AST.tm
in (match (uu____2973) with
| FStar_Parser_AST.Op ("+", (u1)::(u2)::[]) -> begin
(FStar_Pprint.group (let _0_819 = (p_universeFrom u1)
in (let _0_818 = (let _0_817 = (p_universeFrom u2)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus _0_817))
in (FStar_Pprint.op_Hat_Slash_Hat _0_819 _0_818))))
end
| FStar_Parser_AST.App (uu____2977) -> begin
(

let uu____2981 = (head_and_args u)
in (match (uu____2981) with
| (head, args) -> begin
(

let uu____2995 = (unparen head).FStar_Parser_AST.tm
in (match (uu____2995) with
| FStar_Parser_AST.Var (maybe_max_lid) when (FStar_Ident.lid_equals maybe_max_lid FStar_Syntax_Const.max_lid) -> begin
(FStar_Pprint.group (let _0_821 = (p_qlident FStar_Syntax_Const.max_lid)
in (let _0_820 = (FStar_Pprint.separate_map FStar_Pprint.space (fun uu____2999 -> (match (uu____2999) with
| (u, uu____3003) -> begin
(p_atomicUniverse u)
end)) args)
in (op_Hat_Slash_Plus_Hat _0_821 _0_820))))
end
| uu____3004 -> begin
(failwith (let _0_822 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" _0_822)))
end))
end))
end
| uu____3005 -> begin
(p_atomicUniverse u)
end)))
and p_atomicUniverse : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (

let uu____3007 = (unparen u).FStar_Parser_AST.tm
in (match (uu____3007) with
| FStar_Parser_AST.Wild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (r, sw)) -> begin
(p_constant (FStar_Const.Const_int (((r), (sw)))))
end
| FStar_Parser_AST.Uvar (uu____3019) -> begin
(p_univar u)
end
| FStar_Parser_AST.Paren (u) -> begin
(soft_parens_with_nesting (p_universeFrom u))
end
| (FStar_Parser_AST.Op ("+", (_)::(_)::[])) | (FStar_Parser_AST.App (_)) -> begin
(soft_parens_with_nesting (p_universeFrom u))
end
| uu____3025 -> begin
(failwith (let _0_823 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" _0_823)))
end)))
and p_univar : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (

let uu____3027 = (unparen u).FStar_Parser_AST.tm
in (match (uu____3027) with
| FStar_Parser_AST.Uvar (id) -> begin
(str (FStar_Ident.text_of_id id))
end
| uu____3029 -> begin
(failwith (let _0_824 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Not a universe variable %s" _0_824)))
end)))


let term_to_document : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_term e))


let decl_to_document : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun e -> (p_decl e))


let modul_to_document : FStar_Parser_AST.modul  ->  FStar_Pprint.document = (fun m -> ((FStar_ST.write should_print_fs_typ_app false);
(

let res = (match (m) with
| (FStar_Parser_AST.Module (_, decls)) | (FStar_Parser_AST.Interface (_, decls, _)) -> begin
(let _0_825 = (FStar_All.pipe_right decls (FStar_List.map decl_to_document))
in (FStar_All.pipe_right _0_825 (FStar_Pprint.separate FStar_Pprint.hardline)))
end)
in ((FStar_ST.write should_print_fs_typ_app false);
res;
));
))


let comments_to_document : (Prims.string * FStar_Range.range) Prims.list  ->  FStar_Pprint.document = (fun comments -> (FStar_Pprint.separate_map FStar_Pprint.hardline (fun uu____3068 -> (match (uu____3068) with
| (comment, range) -> begin
(str comment)
end)) comments))


let modul_with_comments_to_document : FStar_Parser_AST.modul  ->  (Prims.string * FStar_Range.range) Prims.list  ->  (FStar_Pprint.document * (Prims.string * FStar_Range.range) Prims.list) = (fun m comments -> (

let decls = (match (m) with
| (FStar_Parser_AST.Module (_, decls)) | (FStar_Parser_AST.Interface (_, decls, _)) -> begin
decls
end)
in ((FStar_ST.write should_print_fs_typ_app false);
(match (decls) with
| [] -> begin
((FStar_Pprint.empty), (comments))
end
| (d)::ds -> begin
(

let uu____3115 = (match (ds) with
| ({FStar_Parser_AST.d = FStar_Parser_AST.Pragma (FStar_Parser_AST.LightOff); FStar_Parser_AST.drange = uu____3122; FStar_Parser_AST.doc = uu____3123; FStar_Parser_AST.quals = uu____3124; FStar_Parser_AST.attrs = uu____3125})::uu____3126 -> begin
(

let d0 = (FStar_List.hd ds)
in (let _0_828 = (let _0_827 = (let _0_826 = (FStar_List.tl ds)
in (d)::_0_826)
in (d0)::_0_827)
in ((_0_828), (d0.FStar_Parser_AST.drange))))
end
| uu____3131 -> begin
(((d)::ds), (d.FStar_Parser_AST.drange))
end)
in (match (uu____3115) with
| (decls, first_range) -> begin
(

let extract_decl_range = (fun d -> d.FStar_Parser_AST.drange)
in ((FStar_ST.write comment_stack comments);
(

let initial_comment = (let _0_829 = (FStar_Range.start_of_range first_range)
in (place_comments_until_pos (Prims.parse_int "0") (Prims.parse_int "1") _0_829 FStar_Pprint.empty))
in (

let doc = (separate_map_with_comments FStar_Pprint.empty FStar_Pprint.empty decl_to_document decls extract_decl_range)
in (

let comments = (FStar_ST.read comment_stack)
in ((FStar_ST.write comment_stack []);
(FStar_ST.write should_print_fs_typ_app false);
(let _0_830 = (FStar_Pprint.op_Hat_Hat initial_comment doc)
in ((_0_830), (comments)));
))));
))
end))
end);
)))




