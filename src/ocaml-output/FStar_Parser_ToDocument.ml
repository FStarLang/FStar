
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

let uu____44 = (

let uu____45 = (FStar_ST.read should_unparen)
in (not (uu____45)))
in (match (uu____44) with
| true -> begin
t
end
| uu____48 -> begin
(match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| uu____50 -> begin
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


let separate_break_map = (fun sep f l -> (

let uu____132 = (

let uu____133 = (

let uu____134 = (FStar_Pprint.op_Hat_Hat sep break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____134))
in (FStar_Pprint.separate_map uu____133 f l))
in (FStar_Pprint.group uu____132)))


let precede_break_separate_map = (fun prec sep f l -> (

let uu____164 = (

let uu____165 = (FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space)
in (

let uu____166 = (

let uu____167 = (FStar_List.hd l)
in (FStar_All.pipe_right uu____167 f))
in (FStar_Pprint.precede uu____165 uu____166)))
in (

let uu____168 = (

let uu____169 = (FStar_List.tl l)
in (FStar_Pprint.concat_map (fun x -> (

let uu____172 = (

let uu____173 = (

let uu____174 = (f x)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____174))
in (FStar_Pprint.op_Hat_Hat sep uu____173))
in (FStar_Pprint.op_Hat_Hat break1 uu____172))) uu____169))
in (FStar_Pprint.op_Hat_Hat uu____164 uu____168))))


let concat_break_map = (fun f l -> (

let uu____194 = (FStar_Pprint.concat_map (fun x -> (

let uu____196 = (f x)
in (FStar_Pprint.op_Hat_Hat uu____196 break1))) l)
in (FStar_Pprint.group uu____194)))


let parens_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lparen contents FStar_Pprint.rparen))


let soft_parens_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lparen contents FStar_Pprint.rparen))


let braces_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbrace contents FStar_Pprint.rbrace))


let soft_braces_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbrace contents FStar_Pprint.rbrace))


let brackets_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbracket contents FStar_Pprint.rbracket))


let soft_brackets_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbracket contents FStar_Pprint.rbracket))


let soft_begin_end_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (

let uu____218 = (str "begin")
in (

let uu____219 = (str "end")
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") uu____218 contents uu____219))))


let separate_map_or_flow = (fun sep f l -> (match (((FStar_List.length l) < (Prims.parse_int "10"))) with
| true -> begin
(FStar_Pprint.separate_map sep f l)
end
| uu____247 -> begin
(FStar_Pprint.flow_map sep f l)
end))


let soft_surround_separate_map = (fun n b void_ opening sep closing f xs -> (match ((xs = [])) with
| true -> begin
void_
end
| uu____298 -> begin
(

let uu____299 = (FStar_Pprint.separate_map sep f xs)
in (FStar_Pprint.soft_surround n b opening uu____299 closing))
end))


let doc_of_fsdoc : (Prims.string * (Prims.string * Prims.string) Prims.list)  ->  FStar_Pprint.document = (fun uu____307 -> (match (uu____307) with
| (comment, keywords) -> begin
(

let uu____321 = (

let uu____322 = (

let uu____324 = (str comment)
in (

let uu____325 = (

let uu____327 = (

let uu____329 = (FStar_Pprint.separate_map FStar_Pprint.comma (fun uu____332 -> (match (uu____332) with
| (k, v) -> begin
(

let uu____337 = (

let uu____339 = (str k)
in (

let uu____340 = (

let uu____342 = (

let uu____344 = (str v)
in (uu____344)::[])
in (FStar_Pprint.rarrow)::uu____342)
in (uu____339)::uu____340))
in (FStar_Pprint.concat uu____337))
end)) keywords)
in (uu____329)::[])
in (FStar_Pprint.space)::uu____327)
in (uu____324)::uu____325))
in (FStar_Pprint.concat uu____322))
in (FStar_Pprint.group uu____321))
end))


let is_unit : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____348 = (

let uu____349 = (unparen e)
in uu____349.FStar_Parser_AST.tm)
in (match (uu____348) with
| FStar_Parser_AST.Const (FStar_Const.Const_unit) -> begin
true
end
| uu____350 -> begin
false
end)))


let matches_var : FStar_Parser_AST.term  ->  FStar_Ident.ident  ->  Prims.bool = (fun t x -> (

let uu____357 = (

let uu____358 = (unparen t)
in uu____358.FStar_Parser_AST.tm)
in (match (uu____357) with
| FStar_Parser_AST.Var (y) -> begin
(x.FStar_Ident.idText = (FStar_Ident.text_of_lid y))
end
| uu____360 -> begin
false
end)))


let is_tuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Syntax_Util.is_tuple_data_lid'


let is_dtuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Syntax_Util.is_dtuple_data_lid'


let is_list_structure : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun cons_lid nil_lid -> (

let rec aux = (fun e -> (

let uu____377 = (

let uu____378 = (unparen e)
in uu____378.FStar_Parser_AST.tm)
in (match (uu____377) with
| FStar_Parser_AST.Construct (lid, []) -> begin
(FStar_Ident.lid_equals lid nil_lid)
end
| FStar_Parser_AST.Construct (lid, (uu____386)::((e2, uu____388))::[]) -> begin
((FStar_Ident.lid_equals lid cons_lid) && (aux e2))
end
| uu____400 -> begin
false
end)))
in aux))


let is_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Syntax_Const.cons_lid FStar_Syntax_Const.nil_lid)


let is_lex_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Syntax_Const.lexcons_lid FStar_Syntax_Const.lextop_lid)


let rec extract_from_list : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (

let uu____409 = (

let uu____410 = (unparen e)
in uu____410.FStar_Parser_AST.tm)
in (match (uu____409) with
| FStar_Parser_AST.Construct (uu____412, []) -> begin
[]
end
| FStar_Parser_AST.Construct (uu____418, ((e1, FStar_Parser_AST.Nothing))::((e2, FStar_Parser_AST.Nothing))::[]) -> begin
(

let uu____430 = (extract_from_list e2)
in (e1)::uu____430)
end
| uu____432 -> begin
(

let uu____433 = (

let uu____434 = (FStar_Parser_AST.term_to_string e)
in (FStar_Util.format1 "Not a list %s" uu____434))
in (failwith uu____433))
end)))


let is_array : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____439 = (

let uu____440 = (unparen e)
in uu____440.FStar_Parser_AST.tm)
in (match (uu____439) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (lid); FStar_Parser_AST.range = uu____442; FStar_Parser_AST.level = uu____443}, l, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals lid FStar_Syntax_Const.array_mk_array_lid) && (is_list l))
end
| uu____445 -> begin
false
end)))


let rec is_ref_set : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____449 = (

let uu____450 = (unparen e)
in uu____450.FStar_Parser_AST.tm)
in (match (uu____449) with
| FStar_Parser_AST.Var (maybe_empty_lid) -> begin
(FStar_Ident.lid_equals maybe_empty_lid FStar_Syntax_Const.tset_empty)
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_singleton_lid); FStar_Parser_AST.range = uu____453; FStar_Parser_AST.level = uu____454}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_ref_lid); FStar_Parser_AST.range = uu____456; FStar_Parser_AST.level = uu____457}, e, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____459; FStar_Parser_AST.level = uu____460}, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals maybe_singleton_lid FStar_Syntax_Const.tset_singleton) && (FStar_Ident.lid_equals maybe_ref_lid FStar_Syntax_Const.heap_ref))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_union_lid); FStar_Parser_AST.range = uu____462; FStar_Parser_AST.level = uu____463}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____465; FStar_Parser_AST.level = uu____466}, e2, FStar_Parser_AST.Nothing) -> begin
(((FStar_Ident.lid_equals maybe_union_lid FStar_Syntax_Const.tset_union) && (is_ref_set e1)) && (is_ref_set e2))
end
| uu____468 -> begin
false
end)))


let rec extract_from_ref_set : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (

let uu____473 = (

let uu____474 = (unparen e)
in uu____474.FStar_Parser_AST.tm)
in (match (uu____473) with
| FStar_Parser_AST.Var (uu____476) -> begin
[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (uu____477); FStar_Parser_AST.range = uu____478; FStar_Parser_AST.level = uu____479}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (uu____480); FStar_Parser_AST.range = uu____481; FStar_Parser_AST.level = uu____482}, e, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____484; FStar_Parser_AST.level = uu____485}, FStar_Parser_AST.Nothing) -> begin
(e)::[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (uu____486); FStar_Parser_AST.range = uu____487; FStar_Parser_AST.level = uu____488}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____490; FStar_Parser_AST.level = uu____491}, e2, FStar_Parser_AST.Nothing) -> begin
(

let uu____493 = (extract_from_ref_set e1)
in (

let uu____495 = (extract_from_ref_set e2)
in (FStar_List.append uu____493 uu____495)))
end
| uu____497 -> begin
(

let uu____498 = (

let uu____499 = (FStar_Parser_AST.term_to_string e)
in (FStar_Util.format1 "Not a ref set %s" uu____499))
in (failwith uu____498))
end)))


let is_general_application : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____504 = ((is_array e) || (is_ref_set e))
in (not (uu____504))))


let is_general_construction : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____508 = ((is_list e) || (is_lex_list e))
in (not (uu____508))))


let is_general_prefix_op : Prims.string  ->  Prims.bool = (fun op -> (op <> "~"))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun e -> (

let rec aux = (fun e acc -> (

let uu____538 = (

let uu____539 = (unparen e)
in uu____539.FStar_Parser_AST.tm)
in (match (uu____538) with
| FStar_Parser_AST.App (head, arg, imp) -> begin
(aux head ((((arg), (imp)))::acc))
end
| uu____550 -> begin
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
| uu____559 -> begin
false
end))


let uu___is_Right : associativity  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Right -> begin
true
end
| uu____563 -> begin
false
end))


let uu___is_NonAssoc : associativity  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NonAssoc -> begin
true
end
| uu____567 -> begin
false
end))


type token =
(FStar_Char.char, Prims.string) FStar_Util.either


type associativity_level =
(associativity * token Prims.list)


let token_to_string : (FStar_BaseTypes.char, Prims.string) FStar_Util.either  ->  Prims.string = (fun uu___113_577 -> (match (uu___113_577) with
| FStar_Util.Inl (c) -> begin
(Prims.strcat (FStar_Util.string_of_char c) ".*")
end
| FStar_Util.Inr (s) -> begin
s
end))


let matches_token : Prims.string  ->  (FStar_Char.char, Prims.string) FStar_Util.either  ->  Prims.bool = (fun s uu___114_589 -> (match (uu___114_589) with
| FStar_Util.Inl (c) -> begin
(

let uu____593 = (FStar_String.get s (Prims.parse_int "0"))
in (uu____593 = c))
end
| FStar_Util.Inr (s') -> begin
(s = s')
end))


let matches_level = (fun s uu____611 -> (match (uu____611) with
| (assoc_levels, tokens) -> begin
(

let uu____625 = (FStar_List.tryFind (matches_token s) tokens)
in (uu____625 <> None))
end))


let opinfix4 = (fun uu____643 -> ((Right), ((FStar_Util.Inr ("**"))::[])))


let opinfix3 = (fun uu____658 -> ((Left), ((FStar_Util.Inl ('*'))::(FStar_Util.Inl ('/'))::(FStar_Util.Inl ('%'))::[])))


let opinfix2 = (fun uu____677 -> ((Left), ((FStar_Util.Inl ('+'))::(FStar_Util.Inl ('-'))::[])))


let minus_lvl = (fun uu____694 -> ((Left), ((FStar_Util.Inr ("-"))::[])))


let opinfix1 = (fun uu____709 -> ((Right), ((FStar_Util.Inl ('@'))::(FStar_Util.Inl ('^'))::[])))


let pipe_right = (fun uu____726 -> ((Left), ((FStar_Util.Inr ("|>"))::[])))


let opinfix0d = (fun uu____741 -> ((Left), ((FStar_Util.Inl ('$'))::[])))


let opinfix0c = (fun uu____756 -> ((Left), ((FStar_Util.Inl ('='))::(FStar_Util.Inl ('<'))::(FStar_Util.Inl ('>'))::[])))


let equal = (fun uu____775 -> ((Left), ((FStar_Util.Inr ("="))::[])))


let opinfix0b = (fun uu____790 -> ((Left), ((FStar_Util.Inl ('&'))::[])))


let opinfix0a = (fun uu____805 -> ((Left), ((FStar_Util.Inl ('|'))::[])))


let colon_equals = (fun uu____820 -> ((NonAssoc), ((FStar_Util.Inr (":="))::[])))


let amp = (fun uu____835 -> ((Right), ((FStar_Util.Inr ("&"))::[])))


let colon_colon = (fun uu____850 -> ((Right), ((FStar_Util.Inr ("::"))::[])))


let level_associativity_spec : (associativity * (FStar_Char.char, Prims.string) FStar_Util.either Prims.list) Prims.list = ((opinfix4 ()))::((opinfix3 ()))::((opinfix2 ()))::((opinfix1 ()))::((pipe_right ()))::((opinfix0d ()))::((opinfix0c ()))::((opinfix0b ()))::((opinfix0a ()))::((colon_equals ()))::((amp ()))::((colon_colon ()))::[]


let level_table : ((Prims.int * Prims.int * Prims.int) * (FStar_Char.char, Prims.string) FStar_Util.either Prims.list) Prims.list = (

let levels_from_associativity = (fun l uu___115_947 -> (match (uu___115_947) with
| Left -> begin
((l), (l), ((l - (Prims.parse_int "1"))))
end
| Right -> begin
(((l - (Prims.parse_int "1"))), (l), (l))
end
| NonAssoc -> begin
((l), (l), (l))
end))
in (FStar_List.mapi (fun i uu____965 -> (match (uu____965) with
| (assoc, tokens) -> begin
(((levels_from_associativity i assoc)), (tokens))
end)) level_associativity_spec))


let assign_levels : associativity_level Prims.list  ->  Prims.string  ->  (Prims.int * Prims.int * Prims.int) = (fun token_associativity_spec s -> (

let uu____1007 = (FStar_List.tryFind (matches_level s) level_table)
in (match (uu____1007) with
| Some (assoc_levels, uu____1032) -> begin
assoc_levels
end
| uu____1053 -> begin
(failwith (Prims.strcat "Unrecognized operator " s))
end)))


let max : Prims.int  ->  Prims.int  ->  Prims.int = (fun k1 k2 -> (match ((k1 > k2)) with
| true -> begin
k1
end
| uu____1072 -> begin
k2
end))


let max_level = (fun l -> (

let find_level_and_max = (fun n level -> (

let uu____1109 = (FStar_List.tryFind (fun uu____1127 -> (match (uu____1127) with
| (uu____1136, tokens) -> begin
(tokens = (Prims.snd level))
end)) level_table)
in (match (uu____1109) with
| Some ((uu____1156, l, uu____1158), uu____1159) -> begin
(max n l)
end
| None -> begin
(

let uu____1185 = (

let uu____1186 = (

let uu____1187 = (FStar_List.map token_to_string (Prims.snd level))
in (FStar_String.concat "," uu____1187))
in (FStar_Util.format1 "Undefined associativity level %s" uu____1186))
in (failwith uu____1185))
end)))
in (FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l)))


let levels : Prims.string  ->  (Prims.int * Prims.int * Prims.int) = (assign_levels level_associativity_spec)


let operatorInfix0ad12 = (fun uu____1212 -> ((opinfix0a ()))::((opinfix0b ()))::((opinfix0c ()))::((opinfix0d ()))::((opinfix1 ()))::((opinfix2 ()))::[])


let is_operatorInfix0ad12 : Prims.string  ->  Prims.bool = (fun op -> (

let uu____1251 = (FStar_List.tryFind (matches_level op) (operatorInfix0ad12 ()))
in (uu____1251 <> None)))


let is_operatorInfix34 : Prims.string  ->  Prims.bool = (

let opinfix34 = ((opinfix3 ()))::((opinfix4 ()))::[]
in (fun op -> (

let uu____1299 = (FStar_List.tryFind (matches_level op) opinfix34)
in (uu____1299 <> None))))


let comment_stack : (Prims.string * FStar_Range.range) Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let with_comment = (fun printer tm tmrange -> (

let rec comments_before_pos = (fun acc print_pos lookahead_pos -> (

let uu____1367 = (FStar_ST.read comment_stack)
in (match (uu____1367) with
| [] -> begin
((acc), (false))
end
| ((comment, crange))::cs -> begin
(

let uu____1388 = (FStar_Range.range_before_pos crange print_pos)
in (match (uu____1388) with
| true -> begin
((FStar_ST.write comment_stack cs);
(

let uu____1397 = (

let uu____1398 = (

let uu____1399 = (str comment)
in (FStar_Pprint.op_Hat_Hat uu____1399 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat acc uu____1398))
in (comments_before_pos uu____1397 print_pos lookahead_pos));
)
end
| uu____1400 -> begin
(

let uu____1401 = (FStar_Range.range_before_pos crange lookahead_pos)
in ((acc), (uu____1401)))
end))
end)))
in (

let uu____1402 = (

let uu____1405 = (

let uu____1406 = (FStar_Range.start_of_range tmrange)
in (FStar_Range.end_of_line uu____1406))
in (

let uu____1407 = (FStar_Range.end_of_range tmrange)
in (comments_before_pos FStar_Pprint.empty uu____1405 uu____1407)))
in (match (uu____1402) with
| (comments, has_lookahead) -> begin
(

let printed_e = (printer tm)
in (

let comments = (match (has_lookahead) with
| true -> begin
(

let pos = (FStar_Range.end_of_range tmrange)
in (

let uu____1413 = (comments_before_pos comments pos pos)
in (Prims.fst uu____1413)))
end
| uu____1416 -> begin
comments
end)
in (

let uu____1417 = (FStar_Pprint.op_Hat_Hat comments printed_e)
in (FStar_Pprint.group uu____1417))))
end))))


let rec place_comments_until_pos : Prims.int  ->  Prims.int  ->  FStar_Range.pos  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun k lbegin pos_end doc -> (

let uu____1430 = (FStar_ST.read comment_stack)
in (match (uu____1430) with
| ((comment, crange))::cs when (FStar_Range.range_before_pos crange pos_end) -> begin
((FStar_ST.write comment_stack cs);
(

let lnum = (

let uu____1454 = (

let uu____1455 = (

let uu____1456 = (FStar_Range.start_of_range crange)
in (FStar_Range.line_of_pos uu____1456))
in (uu____1455 - lbegin))
in (max k uu____1454))
in (

let doc = (

let uu____1458 = (

let uu____1459 = (FStar_Pprint.repeat lnum FStar_Pprint.hardline)
in (

let uu____1460 = (str comment)
in (FStar_Pprint.op_Hat_Hat uu____1459 uu____1460)))
in (FStar_Pprint.op_Hat_Hat doc uu____1458))
in (

let uu____1461 = (

let uu____1462 = (FStar_Range.end_of_range crange)
in (FStar_Range.line_of_pos uu____1462))
in (place_comments_until_pos (Prims.parse_int "1") uu____1461 pos_end doc))));
)
end
| uu____1463 -> begin
(

let lnum = (

let uu____1468 = (

let uu____1469 = (FStar_Range.line_of_pos pos_end)
in (uu____1469 - lbegin))
in (max (Prims.parse_int "1") uu____1468))
in (

let uu____1470 = (FStar_Pprint.repeat lnum FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat doc uu____1470)))
end)))


let separate_map_with_comments = (fun prefix sep f xs extract_range -> (

let fold_fun = (fun uu____1519 x -> (match (uu____1519) with
| (last_line, doc) -> begin
(

let r = (extract_range x)
in (

let doc = (

let uu____1529 = (FStar_Range.start_of_range r)
in (place_comments_until_pos (Prims.parse_int "1") last_line uu____1529 doc))
in (

let uu____1530 = (

let uu____1531 = (FStar_Range.end_of_range r)
in (FStar_Range.line_of_pos uu____1531))
in (

let uu____1532 = (

let uu____1533 = (

let uu____1534 = (f x)
in (FStar_Pprint.op_Hat_Hat sep uu____1534))
in (FStar_Pprint.op_Hat_Hat doc uu____1533))
in ((uu____1530), (uu____1532))))))
end))
in (

let uu____1535 = (

let uu____1539 = (FStar_List.hd xs)
in (

let uu____1540 = (FStar_List.tl xs)
in ((uu____1539), (uu____1540))))
in (match (uu____1535) with
| (x, xs) -> begin
(

let init = (

let uu____1550 = (

let uu____1551 = (

let uu____1552 = (extract_range x)
in (FStar_Range.end_of_range uu____1552))
in (FStar_Range.line_of_pos uu____1551))
in (

let uu____1553 = (

let uu____1554 = (f x)
in (FStar_Pprint.op_Hat_Hat prefix uu____1554))
in ((uu____1550), (uu____1553))))
in (

let uu____1555 = (FStar_List.fold_left fold_fun init xs)
in (Prims.snd uu____1555)))
end))))


let rec p_decl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (

let uu____1801 = (

let uu____1802 = (FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc)
in (

let uu____1803 = (

let uu____1804 = (p_attributes d.FStar_Parser_AST.attrs)
in (

let uu____1805 = (

let uu____1806 = (p_qualifiers d.FStar_Parser_AST.quals)
in (

let uu____1807 = (

let uu____1808 = (p_rawDecl d)
in (FStar_Pprint.op_Hat_Hat (match ((d.FStar_Parser_AST.quals = [])) with
| true -> begin
FStar_Pprint.empty
end
| uu____1809 -> begin
break1
end) uu____1808))
in (FStar_Pprint.op_Hat_Hat uu____1806 uu____1807)))
in (FStar_Pprint.op_Hat_Hat uu____1804 uu____1805)))
in (FStar_Pprint.op_Hat_Hat uu____1802 uu____1803)))
in (FStar_Pprint.group uu____1801)))
and p_attributes : FStar_Parser_AST.attributes_  ->  FStar_Pprint.document = (fun attrs -> (

let uu____1811 = (

let uu____1812 = (str "@")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____1812))
in (

let uu____1813 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline)
in (soft_surround_separate_map (Prims.parse_int "0") (Prims.parse_int "2") FStar_Pprint.empty uu____1811 FStar_Pprint.space uu____1813 p_atomicTerm attrs))))
and p_fsdoc : FStar_Parser_AST.fsdoc  ->  FStar_Pprint.document = (fun uu____1814 -> (match (uu____1814) with
| (doc, kwd_args) -> begin
(

let kwd_args_doc = (match (kwd_args) with
| [] -> begin
FStar_Pprint.empty
end
| kwd_args -> begin
(

let process_kwd_arg = (fun uu____1835 -> (match (uu____1835) with
| (kwd, arg) -> begin
(

let uu____1840 = (str "@")
in (

let uu____1841 = (

let uu____1842 = (str kwd)
in (

let uu____1843 = (

let uu____1844 = (str arg)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1844))
in (FStar_Pprint.op_Hat_Hat uu____1842 uu____1843)))
in (FStar_Pprint.op_Hat_Hat uu____1840 uu____1841)))
end))
in (

let uu____1845 = (

let uu____1846 = (FStar_Pprint.separate_map FStar_Pprint.hardline process_kwd_arg kwd_args)
in (FStar_Pprint.op_Hat_Hat uu____1846 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____1845)))
end)
in (

let uu____1849 = (

let uu____1850 = (

let uu____1851 = (

let uu____1852 = (

let uu____1853 = (str doc)
in (

let uu____1854 = (

let uu____1855 = (

let uu____1856 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1856))
in (FStar_Pprint.op_Hat_Hat kwd_args_doc uu____1855))
in (FStar_Pprint.op_Hat_Hat uu____1853 uu____1854)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1852))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1851))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____1850))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____1849)))
end))
and p_rawDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Open (uid) -> begin
(

let uu____1859 = (

let uu____1860 = (str "open")
in (

let uu____1861 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat uu____1860 uu____1861)))
in (FStar_Pprint.group uu____1859))
end
| FStar_Parser_AST.Include (uid) -> begin
(

let uu____1863 = (

let uu____1864 = (str "include")
in (

let uu____1865 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat uu____1864 uu____1865)))
in (FStar_Pprint.group uu____1863))
end
| FStar_Parser_AST.ModuleAbbrev (uid1, uid2) -> begin
(

let uu____1868 = (

let uu____1869 = (str "module")
in (

let uu____1870 = (

let uu____1871 = (

let uu____1872 = (p_uident uid1)
in (

let uu____1873 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____1872 uu____1873)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1871))
in (FStar_Pprint.op_Hat_Hat uu____1869 uu____1870)))
in (

let uu____1874 = (p_quident uid2)
in (op_Hat_Slash_Plus_Hat uu____1868 uu____1874)))
end
| FStar_Parser_AST.TopLevelModule (uid) -> begin
(

let uu____1876 = (

let uu____1877 = (str "module")
in (

let uu____1878 = (

let uu____1879 = (p_quident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1879))
in (FStar_Pprint.op_Hat_Hat uu____1877 uu____1878)))
in (FStar_Pprint.group uu____1876))
end
| FStar_Parser_AST.Tycon (true, ((FStar_Parser_AST.TyconAbbrev (uid, tpars, None, t), None))::[]) -> begin
(

let effect_prefix_doc = (

let uu____1898 = (str "effect")
in (

let uu____1899 = (

let uu____1900 = (p_uident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1900))
in (FStar_Pprint.op_Hat_Hat uu____1898 uu____1899)))
in (

let uu____1901 = (

let uu____1902 = (p_typars tpars)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") effect_prefix_doc uu____1902 FStar_Pprint.equals))
in (

let uu____1903 = (p_typ t)
in (op_Hat_Slash_Plus_Hat uu____1901 uu____1903))))
end
| FStar_Parser_AST.Tycon (false, tcdefs) -> begin
(

let uu____1913 = (str "type")
in (

let uu____1914 = (str "and")
in (precede_break_separate_map uu____1913 uu____1914 p_fsdocTypeDeclPairs tcdefs)))
end
| FStar_Parser_AST.TopLevelLet (q, lbs) -> begin
(

let let_doc = (

let uu____1927 = (str "let")
in (

let uu____1928 = (

let uu____1929 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat uu____1929 FStar_Pprint.space))
in (FStar_Pprint.op_Hat_Hat uu____1927 uu____1928)))
in (

let uu____1930 = (

let uu____1931 = (str "and")
in (FStar_Pprint.op_Hat_Hat uu____1931 FStar_Pprint.space))
in (separate_map_with_comments let_doc uu____1930 p_letbinding lbs (fun uu____1934 -> (match (uu____1934) with
| (p, t) -> begin
(FStar_Range.union_ranges p.FStar_Parser_AST.prange t.FStar_Parser_AST.range)
end)))))
end
| FStar_Parser_AST.Val (lid, t) -> begin
(

let uu____1941 = (

let uu____1942 = (str "val")
in (

let uu____1943 = (

let uu____1944 = (

let uu____1945 = (p_lident lid)
in (

let uu____1946 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat uu____1945 uu____1946)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1944))
in (FStar_Pprint.op_Hat_Hat uu____1942 uu____1943)))
in (

let uu____1947 = (p_typ t)
in (op_Hat_Slash_Plus_Hat uu____1941 uu____1947)))
end
| FStar_Parser_AST.Assume (id, t) -> begin
(

let decl_keyword = (

let uu____1951 = (

let uu____1952 = (FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_All.pipe_right uu____1952 FStar_Util.is_upper))
in (match (uu____1951) with
| true -> begin
FStar_Pprint.empty
end
| uu____1953 -> begin
(

let uu____1954 = (str "val")
in (FStar_Pprint.op_Hat_Hat uu____1954 FStar_Pprint.space))
end))
in (

let uu____1955 = (

let uu____1956 = (

let uu____1957 = (p_ident id)
in (

let uu____1958 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat uu____1957 uu____1958)))
in (FStar_Pprint.op_Hat_Hat decl_keyword uu____1956))
in (

let uu____1959 = (p_typ t)
in (op_Hat_Slash_Plus_Hat uu____1955 uu____1959))))
end
| FStar_Parser_AST.Exception (uid, t_opt) -> begin
(

let uu____1964 = (str "exception")
in (

let uu____1965 = (

let uu____1966 = (

let uu____1967 = (p_uident uid)
in (

let uu____1968 = (FStar_Pprint.optional (fun t -> (

let uu____1970 = (str "of")
in (

let uu____1971 = (p_typ t)
in (op_Hat_Slash_Plus_Hat uu____1970 uu____1971)))) t_opt)
in (FStar_Pprint.op_Hat_Hat uu____1967 uu____1968)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1966))
in (FStar_Pprint.op_Hat_Hat uu____1964 uu____1965)))
end
| FStar_Parser_AST.NewEffect (ne) -> begin
(

let uu____1973 = (str "new_effect")
in (

let uu____1974 = (

let uu____1975 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1975))
in (FStar_Pprint.op_Hat_Hat uu____1973 uu____1974)))
end
| FStar_Parser_AST.SubEffect (se) -> begin
(

let uu____1977 = (str "sub_effect")
in (

let uu____1978 = (

let uu____1979 = (p_subEffect se)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1979))
in (FStar_Pprint.op_Hat_Hat uu____1977 uu____1978)))
end
| FStar_Parser_AST.Pragma (p) -> begin
(p_pragma p)
end
| FStar_Parser_AST.Fsdoc (doc) -> begin
(

let uu____1982 = (p_fsdoc doc)
in (FStar_Pprint.op_Hat_Hat uu____1982 FStar_Pprint.hardline))
end
| FStar_Parser_AST.Main (uu____1983) -> begin
(failwith "*Main declaration* : Is that really still in use ??")
end
| FStar_Parser_AST.Tycon (true, uu____1984) -> begin
(failwith "Effect abbreviation is expected to be defined by an abbreviation")
end))
and p_pragma : FStar_Parser_AST.pragma  ->  FStar_Pprint.document = (fun uu___116_1993 -> (match (uu___116_1993) with
| FStar_Parser_AST.SetOptions (s) -> begin
(

let uu____1995 = (str "#set-options")
in (

let uu____1996 = (

let uu____1997 = (

let uu____1998 = (str s)
in (FStar_Pprint.dquotes uu____1998))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1997))
in (FStar_Pprint.op_Hat_Hat uu____1995 uu____1996)))
end
| FStar_Parser_AST.ResetOptions (s_opt) -> begin
(

let uu____2001 = (str "#reset-options")
in (

let uu____2002 = (FStar_Pprint.optional (fun s -> (

let uu____2004 = (

let uu____2005 = (str s)
in (FStar_Pprint.dquotes uu____2005))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2004))) s_opt)
in (FStar_Pprint.op_Hat_Hat uu____2001 uu____2002)))
end
| FStar_Parser_AST.LightOff -> begin
((FStar_ST.write should_print_fs_typ_app true);
(str "#light \"off\"");
)
end))
and p_typars : FStar_Parser_AST.binder Prims.list  ->  FStar_Pprint.document = (fun bs -> (p_binders true bs))
and p_fsdocTypeDeclPairs : (FStar_Parser_AST.tycon * FStar_Parser_AST.fsdoc Prims.option)  ->  FStar_Pprint.document = (fun uu____2011 -> (match (uu____2011) with
| (typedecl, fsdoc_opt) -> begin
(

let uu____2019 = (FStar_Pprint.optional p_fsdoc fsdoc_opt)
in (

let uu____2020 = (p_typeDecl typedecl)
in (FStar_Pprint.op_Hat_Hat uu____2019 uu____2020)))
end))
and p_typeDecl : FStar_Parser_AST.tycon  ->  FStar_Pprint.document = (fun uu___117_2021 -> (match (uu___117_2021) with
| FStar_Parser_AST.TyconAbstract (lid, bs, typ_opt) -> begin
(

let empty' = (fun uu____2032 -> FStar_Pprint.empty)
in (p_typeDeclPrefix lid bs typ_opt empty'))
end
| FStar_Parser_AST.TyconAbbrev (lid, bs, typ_opt, t) -> begin
(

let f = (fun uu____2044 -> (

let uu____2045 = (p_typ t)
in (prefix2 FStar_Pprint.equals uu____2045)))
in (p_typeDeclPrefix lid bs typ_opt f))
end
| FStar_Parser_AST.TyconRecord (lid, bs, typ_opt, record_field_decls) -> begin
(

let p_recordFieldAndComments = (fun uu____2071 -> (match (uu____2071) with
| (lid, t, doc_opt) -> begin
(

let uu____2081 = (FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range)
in (with_comment p_recordFieldDecl ((lid), (t), (doc_opt)) uu____2081))
end))
in (

let p_fields = (fun uu____2090 -> (

let uu____2091 = (

let uu____2092 = (

let uu____2093 = (

let uu____2094 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (FStar_Pprint.separate_map uu____2094 p_recordFieldAndComments record_field_decls))
in (braces_with_nesting uu____2093))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2092))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____2091)))
in (p_typeDeclPrefix lid bs typ_opt p_fields)))
end
| FStar_Parser_AST.TyconVariant (lid, bs, typ_opt, ct_decls) -> begin
(

let p_constructorBranchAndComments = (fun uu____2130 -> (match (uu____2130) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let range = (

let uu____2146 = (

let uu____2147 = (FStar_Util.map_opt t_opt (fun t -> t.FStar_Parser_AST.range))
in (FStar_Util.dflt uid.FStar_Ident.idRange uu____2147))
in (FStar_Range.extend_to_end_of_line uu____2146))
in (

let p_constructorBranch = (fun decl -> (

let uu____2166 = (

let uu____2167 = (

let uu____2168 = (p_constructorDecl decl)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2168))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____2167))
in (FStar_Pprint.group uu____2166)))
in (with_comment p_constructorBranch ((uid), (t_opt), (doc_opt), (use_of)) range)))
end))
in (

let datacon_doc = (fun uu____2180 -> (

let uu____2181 = (FStar_Pprint.separate_map break1 p_constructorBranchAndComments ct_decls)
in (FStar_Pprint.group uu____2181)))
in (p_typeDeclPrefix lid bs typ_opt (fun uu____2188 -> (

let uu____2189 = (datacon_doc ())
in (prefix2 FStar_Pprint.equals uu____2189))))))
end))
and p_typeDeclPrefix : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.knd Prims.option  ->  (Prims.unit  ->  FStar_Pprint.document)  ->  FStar_Pprint.document = (fun lid bs typ_opt cont -> (match (((bs = []) && (typ_opt = None))) with
| true -> begin
(

let uu____2200 = (p_ident lid)
in (

let uu____2201 = (

let uu____2202 = (cont ())
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2202))
in (FStar_Pprint.op_Hat_Hat uu____2200 uu____2201)))
end
| uu____2203 -> begin
(

let binders_doc = (

let uu____2205 = (p_typars bs)
in (

let uu____2206 = (FStar_Pprint.optional (fun t -> (

let uu____2208 = (

let uu____2209 = (

let uu____2210 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2210))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2209))
in (FStar_Pprint.op_Hat_Hat break1 uu____2208))) typ_opt)
in (FStar_Pprint.op_Hat_Hat uu____2205 uu____2206)))
in (

let uu____2211 = (p_ident lid)
in (

let uu____2212 = (cont ())
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____2211 binders_doc uu____2212))))
end))
and p_recordFieldDecl : (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc Prims.option)  ->  FStar_Pprint.document = (fun uu____2213 -> (match (uu____2213) with
| (lid, t, doc_opt) -> begin
(

let uu____2223 = (

let uu____2224 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (

let uu____2225 = (

let uu____2226 = (p_lident lid)
in (

let uu____2227 = (

let uu____2228 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2228))
in (FStar_Pprint.op_Hat_Hat uu____2226 uu____2227)))
in (FStar_Pprint.op_Hat_Hat uu____2224 uu____2225)))
in (FStar_Pprint.group uu____2223))
end))
and p_constructorDecl : (FStar_Ident.ident * FStar_Parser_AST.term Prims.option * FStar_Parser_AST.fsdoc Prims.option * Prims.bool)  ->  FStar_Pprint.document = (fun uu____2229 -> (match (uu____2229) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let sep = (match (use_of) with
| true -> begin
(str "of")
end
| uu____2245 -> begin
FStar_Pprint.colon
end)
in (

let uid_doc = (p_uident uid)
in (

let uu____2247 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (

let uu____2248 = (default_or_map uid_doc (fun t -> (

let uu____2250 = (

let uu____2251 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep)
in (FStar_Pprint.op_Hat_Hat uid_doc uu____2251))
in (

let uu____2252 = (p_typ t)
in (op_Hat_Slash_Plus_Hat uu____2250 uu____2252)))) t_opt)
in (FStar_Pprint.op_Hat_Hat uu____2247 uu____2248)))))
end))
and p_letbinding : (FStar_Parser_AST.pattern * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun uu____2253 -> (match (uu____2253) with
| (pat, e) -> begin
(

let pat_doc = (

let uu____2259 = (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, t) -> begin
(

let uu____2266 = (

let uu____2267 = (

let uu____2268 = (

let uu____2269 = (

let uu____2270 = (p_tmArrow p_tmNoEq t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2270))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2269))
in (FStar_Pprint.group uu____2268))
in (FStar_Pprint.op_Hat_Hat break1 uu____2267))
in ((pat), (uu____2266)))
end
| uu____2271 -> begin
((pat), (FStar_Pprint.empty))
end)
in (match (uu____2259) with
| (pat, ascr_doc) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____2275); FStar_Parser_AST.prange = uu____2276}, pats) -> begin
(

let uu____2282 = (p_lident x)
in (

let uu____2283 = (

let uu____2284 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Hat uu____2284 ascr_doc))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____2282 uu____2283 FStar_Pprint.equals)))
end
| uu____2285 -> begin
(

let uu____2286 = (

let uu____2287 = (p_tuplePattern pat)
in (

let uu____2288 = (FStar_Pprint.op_Hat_Slash_Hat ascr_doc FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____2287 uu____2288)))
in (FStar_Pprint.group uu____2286))
end)
end))
in (

let uu____2289 = (p_term e)
in (prefix2 pat_doc uu____2289)))
end))
and p_newEffect : FStar_Parser_AST.effect_decl  ->  FStar_Pprint.document = (fun uu___118_2290 -> (match (uu___118_2290) with
| FStar_Parser_AST.RedefineEffect (lid, bs, t) -> begin
(p_effectRedefinition lid bs t)
end
| FStar_Parser_AST.DefineEffect (lid, bs, t, eff_decls) -> begin
(p_effectDefinition lid bs t eff_decls)
end))
and p_effectRedefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun uid bs t -> (

let uu____2308 = (p_uident uid)
in (

let uu____2309 = (p_binders true bs)
in (

let uu____2310 = (

let uu____2311 = (p_simpleTerm t)
in (prefix2 FStar_Pprint.equals uu____2311))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____2308 uu____2309 uu____2310)))))
and p_effectDefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun uid bs t eff_decls -> (

let uu____2318 = (

let uu____2319 = (

let uu____2320 = (

let uu____2321 = (p_uident uid)
in (

let uu____2322 = (p_binders true bs)
in (

let uu____2323 = (

let uu____2324 = (p_typ t)
in (prefix2 FStar_Pprint.colon uu____2324))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____2321 uu____2322 uu____2323))))
in (FStar_Pprint.group uu____2320))
in (

let uu____2325 = (

let uu____2326 = (str "with")
in (

let uu____2327 = (separate_break_map FStar_Pprint.semi p_effectDecl eff_decls)
in (prefix2 uu____2326 uu____2327)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2319 uu____2325)))
in (braces_with_nesting uu____2318)))
and p_effectDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (false, ((FStar_Parser_AST.TyconAbbrev (lid, [], None, e), None))::[]) -> begin
(

let uu____2344 = (

let uu____2345 = (p_lident lid)
in (

let uu____2346 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____2345 uu____2346)))
in (

let uu____2347 = (p_simpleTerm e)
in (prefix2 uu____2344 uu____2347)))
end
| uu____2348 -> begin
(

let uu____2349 = (

let uu____2350 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "Not a declaration of an effect member... or at least I hope so : %s" uu____2350))
in (failwith uu____2349))
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

let p_lift = (fun uu____2383 -> (match (uu____2383) with
| (kwd, t) -> begin
(

let uu____2388 = (

let uu____2389 = (str kwd)
in (

let uu____2390 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____2389 uu____2390)))
in (

let uu____2391 = (p_simpleTerm t)
in (prefix2 uu____2388 uu____2391)))
end))
in (separate_break_map FStar_Pprint.semi p_lift lifts)))
in (

let uu____2394 = (

let uu____2395 = (

let uu____2396 = (p_quident lift.FStar_Parser_AST.msource)
in (

let uu____2397 = (

let uu____2398 = (str "~>")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2398))
in (FStar_Pprint.op_Hat_Hat uu____2396 uu____2397)))
in (

let uu____2399 = (p_quident lift.FStar_Parser_AST.mdest)
in (prefix2 uu____2395 uu____2399)))
in (

let uu____2400 = (

let uu____2401 = (braces_with_nesting lift_op_doc)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2401))
in (FStar_Pprint.op_Hat_Hat uu____2394 uu____2400)))))
and p_qualifier : FStar_Parser_AST.qualifier  ->  FStar_Pprint.document = (fun uu___119_2402 -> (match (uu___119_2402) with
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
and p_qualifiers : FStar_Parser_AST.qualifiers  ->  FStar_Pprint.document = (fun qs -> (

let uu____2404 = (FStar_Pprint.separate_map break1 p_qualifier qs)
in (FStar_Pprint.group uu____2404)))
and p_letqualifier : FStar_Parser_AST.let_qualifier  ->  FStar_Pprint.document = (fun uu___120_2405 -> (match (uu___120_2405) with
| FStar_Parser_AST.Rec -> begin
(

let uu____2406 = (str "rec")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2406))
end
| FStar_Parser_AST.Mutable -> begin
(

let uu____2407 = (str "mutable")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2407))
end
| FStar_Parser_AST.NoLetQualifier -> begin
FStar_Pprint.empty
end))
and p_aqual : FStar_Parser_AST.arg_qualifier  ->  FStar_Pprint.document = (fun uu___121_2408 -> (match (uu___121_2408) with
| FStar_Parser_AST.Implicit -> begin
(str "#")
end
| FStar_Parser_AST.Equality -> begin
(str "$")
end))
and p_disjunctivePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr (pats) -> begin
(

let uu____2412 = (

let uu____2413 = (

let uu____2414 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space)
in (FStar_Pprint.op_Hat_Hat break1 uu____2414))
in (FStar_Pprint.separate_map uu____2413 p_tuplePattern pats))
in (FStar_Pprint.group uu____2412))
end
| uu____2415 -> begin
(p_tuplePattern p)
end))
and p_tuplePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTuple (pats, false) -> begin
(

let uu____2420 = (

let uu____2421 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map uu____2421 p_constructorPattern pats))
in (FStar_Pprint.group uu____2420))
end
| uu____2422 -> begin
(p_constructorPattern p)
end))
and p_constructorPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (maybe_cons_lid); FStar_Parser_AST.prange = uu____2425}, (hd)::(tl)::[]) when (FStar_Ident.lid_equals maybe_cons_lid FStar_Syntax_Const.cons_lid) -> begin
(

let uu____2429 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon)
in (

let uu____2430 = (p_constructorPattern hd)
in (

let uu____2431 = (p_constructorPattern tl)
in (infix0 uu____2429 uu____2430 uu____2431))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (uid); FStar_Parser_AST.prange = uu____2433}, pats) -> begin
(

let uu____2437 = (p_quident uid)
in (

let uu____2438 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (prefix2 uu____2437 uu____2438)))
end
| uu____2439 -> begin
(p_atomicPattern p)
end))
and p_atomicPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, t) -> begin
(

let uu____2443 = (

let uu____2446 = (

let uu____2447 = (unparen t)
in uu____2447.FStar_Parser_AST.tm)
in ((pat.FStar_Parser_AST.pat), (uu____2446)))
in (match (uu____2443) with
| (FStar_Parser_AST.PatVar (lid, aqual), FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t); FStar_Parser_AST.brange = uu____2452; FStar_Parser_AST.blevel = uu____2453; FStar_Parser_AST.aqual = uu____2454}, phi)) when (lid.FStar_Ident.idText = lid'.FStar_Ident.idText) -> begin
(

let uu____2458 = (

let uu____2459 = (p_ident lid)
in (p_refinement aqual uu____2459 t phi))
in (soft_parens_with_nesting uu____2458))
end
| (FStar_Parser_AST.PatWild, FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t); FStar_Parser_AST.brange = uu____2461; FStar_Parser_AST.blevel = uu____2462; FStar_Parser_AST.aqual = uu____2463}, phi)) -> begin
(

let uu____2465 = (p_refinement None FStar_Pprint.underscore t phi)
in (soft_parens_with_nesting uu____2465))
end
| uu____2466 -> begin
(

let uu____2469 = (

let uu____2470 = (p_tuplePattern pat)
in (

let uu____2471 = (

let uu____2472 = (FStar_Pprint.break_ (Prims.parse_int "0"))
in (

let uu____2473 = (

let uu____2474 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2474))
in (FStar_Pprint.op_Hat_Hat uu____2472 uu____2473)))
in (FStar_Pprint.op_Hat_Hat uu____2470 uu____2471)))
in (soft_parens_with_nesting uu____2469))
end))
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let uu____2477 = (separate_break_map FStar_Pprint.semi p_tuplePattern pats)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket uu____2477 FStar_Pprint.rbracket))
end
| FStar_Parser_AST.PatRecord (pats) -> begin
(

let p_recordFieldPat = (fun uu____2487 -> (match (uu____2487) with
| (lid, pat) -> begin
(

let uu____2492 = (p_qlident lid)
in (

let uu____2493 = (p_tuplePattern pat)
in (infix2 FStar_Pprint.equals uu____2492 uu____2493)))
end))
in (

let uu____2494 = (separate_break_map FStar_Pprint.semi p_recordFieldPat pats)
in (soft_braces_with_nesting uu____2494)))
end
| FStar_Parser_AST.PatTuple (pats, true) -> begin
(

let uu____2500 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (

let uu____2501 = (separate_break_map FStar_Pprint.comma p_constructorPattern pats)
in (

let uu____2502 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____2500 uu____2501 uu____2502))))
end
| FStar_Parser_AST.PatTvar (tv, arg_qualifier_opt) -> begin
(p_tvar tv)
end
| FStar_Parser_AST.PatOp (op) -> begin
(

let uu____2509 = (

let uu____2510 = (

let uu____2511 = (str op)
in (

let uu____2512 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat uu____2511 uu____2512)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2510))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2509))
end
| FStar_Parser_AST.PatWild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.PatConst (c) -> begin
(p_constant c)
end
| FStar_Parser_AST.PatVar (lid, aqual) -> begin
(

let uu____2518 = (FStar_Pprint.optional p_aqual aqual)
in (

let uu____2519 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat uu____2518 uu____2519)))
end
| FStar_Parser_AST.PatName (uid) -> begin
(p_quident uid)
end
| FStar_Parser_AST.PatOr (uu____2521) -> begin
(failwith "Inner or pattern !")
end
| (FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (_); FStar_Parser_AST.prange = _}, _)) | (FStar_Parser_AST.PatTuple (_, false)) -> begin
(

let uu____2529 = (p_tuplePattern p)
in (soft_parens_with_nesting uu____2529))
end
| uu____2530 -> begin
(

let uu____2531 = (

let uu____2532 = (FStar_Parser_AST.pat_to_string p)
in (FStar_Util.format1 "Invalid pattern %s" uu____2532))
in (failwith uu____2531))
end))
and p_binder : Prims.bool  ->  FStar_Parser_AST.binder  ->  FStar_Pprint.document = (fun is_atomic b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (lid) -> begin
(

let uu____2536 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (

let uu____2537 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat uu____2536 uu____2537)))
end
| FStar_Parser_AST.TVariable (lid) -> begin
(p_lident lid)
end
| FStar_Parser_AST.Annotated (lid, t) -> begin
(

let doc = (

let uu____2542 = (

let uu____2543 = (unparen t)
in uu____2543.FStar_Parser_AST.tm)
in (match (uu____2542) with
| FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t); FStar_Parser_AST.brange = uu____2546; FStar_Parser_AST.blevel = uu____2547; FStar_Parser_AST.aqual = uu____2548}, phi) when (lid.FStar_Ident.idText = lid'.FStar_Ident.idText) -> begin
(

let uu____2550 = (p_ident lid)
in (p_refinement b.FStar_Parser_AST.aqual uu____2550 t phi))
end
| uu____2551 -> begin
(

let uu____2552 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (

let uu____2553 = (

let uu____2554 = (p_lident lid)
in (

let uu____2555 = (

let uu____2556 = (

let uu____2557 = (FStar_Pprint.break_ (Prims.parse_int "0"))
in (

let uu____2558 = (p_tmFormula t)
in (FStar_Pprint.op_Hat_Hat uu____2557 uu____2558)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2556))
in (FStar_Pprint.op_Hat_Hat uu____2554 uu____2555)))
in (FStar_Pprint.op_Hat_Hat uu____2552 uu____2553)))
end))
in (match (is_atomic) with
| true -> begin
(

let uu____2559 = (

let uu____2560 = (FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2560))
in (FStar_Pprint.group uu____2559))
end
| uu____2561 -> begin
(FStar_Pprint.group doc)
end))
end
| FStar_Parser_AST.TAnnotated (uu____2562) -> begin
(failwith "Is this still used ?")
end
| FStar_Parser_AST.NoName (t) -> begin
(

let uu____2566 = (

let uu____2567 = (unparen t)
in uu____2567.FStar_Parser_AST.tm)
in (match (uu____2566) with
| FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t); FStar_Parser_AST.brange = uu____2569; FStar_Parser_AST.blevel = uu____2570; FStar_Parser_AST.aqual = uu____2571}, phi) -> begin
(match (is_atomic) with
| true -> begin
(

let uu____2573 = (

let uu____2574 = (

let uu____2575 = (p_refinement b.FStar_Parser_AST.aqual FStar_Pprint.underscore t phi)
in (FStar_Pprint.op_Hat_Hat uu____2575 FStar_Pprint.rparen))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2574))
in (FStar_Pprint.group uu____2573))
end
| uu____2576 -> begin
(

let uu____2577 = (p_refinement b.FStar_Parser_AST.aqual FStar_Pprint.underscore t phi)
in (FStar_Pprint.group uu____2577))
end)
end
| uu____2578 -> begin
(match (is_atomic) with
| true -> begin
(p_atomicTerm t)
end
| uu____2579 -> begin
(p_appTerm t)
end)
end))
end))
and p_refinement : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Pprint.document  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun aqual_opt binder t phi -> (

let uu____2585 = (FStar_Pprint.optional p_aqual aqual_opt)
in (

let uu____2586 = (

let uu____2587 = (

let uu____2588 = (

let uu____2589 = (p_appTerm t)
in (

let uu____2590 = (

let uu____2591 = (p_noSeqTerm phi)
in (soft_braces_with_nesting uu____2591))
in (FStar_Pprint.op_Hat_Hat uu____2589 uu____2590)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2588))
in (FStar_Pprint.op_Hat_Hat binder uu____2587))
in (FStar_Pprint.op_Hat_Hat uu____2585 uu____2586))))
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
| uu____2602 -> begin
(p_lident id)
end))
and p_term : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2604 = (

let uu____2605 = (unparen e)
in uu____2605.FStar_Parser_AST.tm)
in (match (uu____2604) with
| FStar_Parser_AST.Seq (e1, e2) -> begin
(

let uu____2608 = (

let uu____2609 = (

let uu____2610 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat uu____2610 FStar_Pprint.semi))
in (FStar_Pprint.group uu____2609))
in (

let uu____2611 = (p_term e2)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2608 uu____2611)))
end
| uu____2612 -> begin
(

let uu____2613 = (p_noSeqTerm e)
in (FStar_Pprint.group uu____2613))
end)))
and p_noSeqTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_noSeqTerm' e e.FStar_Parser_AST.range))
and p_noSeqTerm' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2616 = (

let uu____2617 = (unparen e)
in uu____2617.FStar_Parser_AST.tm)
in (match (uu____2616) with
| FStar_Parser_AST.Ascribed (e, t) -> begin
(

let uu____2620 = (

let uu____2621 = (p_tmIff e)
in (

let uu____2622 = (

let uu____2623 = (

let uu____2624 = (p_typ t)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____2624))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____2623))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2621 uu____2622)))
in (FStar_Pprint.group uu____2620))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::(e3)::[]) when (op = ".()<-") -> begin
(

let uu____2630 = (

let uu____2631 = (

let uu____2632 = (

let uu____2633 = (p_atomicTermNotQUident e1)
in (

let uu____2634 = (

let uu____2635 = (

let uu____2636 = (

let uu____2637 = (p_term e2)
in (soft_parens_with_nesting uu____2637))
in (

let uu____2638 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat uu____2636 uu____2638)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____2635))
in (FStar_Pprint.op_Hat_Hat uu____2633 uu____2634)))
in (FStar_Pprint.group uu____2632))
in (

let uu____2639 = (

let uu____2640 = (p_noSeqTerm e3)
in (jump2 uu____2640))
in (FStar_Pprint.op_Hat_Hat uu____2631 uu____2639)))
in (FStar_Pprint.group uu____2630))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::(e3)::[]) when (op = ".[]<-") -> begin
(

let uu____2646 = (

let uu____2647 = (

let uu____2648 = (

let uu____2649 = (p_atomicTermNotQUident e1)
in (

let uu____2650 = (

let uu____2651 = (

let uu____2652 = (

let uu____2653 = (p_term e2)
in (soft_brackets_with_nesting uu____2653))
in (

let uu____2654 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat uu____2652 uu____2654)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____2651))
in (FStar_Pprint.op_Hat_Hat uu____2649 uu____2650)))
in (FStar_Pprint.group uu____2648))
in (

let uu____2655 = (

let uu____2656 = (p_noSeqTerm e3)
in (jump2 uu____2656))
in (FStar_Pprint.op_Hat_Hat uu____2647 uu____2655)))
in (FStar_Pprint.group uu____2646))
end
| FStar_Parser_AST.Requires (e, wtf) -> begin
(

let uu____2662 = (

let uu____2663 = (str "requires")
in (

let uu____2664 = (p_typ e)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2663 uu____2664)))
in (FStar_Pprint.group uu____2662))
end
| FStar_Parser_AST.Ensures (e, wtf) -> begin
(

let uu____2670 = (

let uu____2671 = (str "ensures")
in (

let uu____2672 = (p_typ e)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2671 uu____2672)))
in (FStar_Pprint.group uu____2670))
end
| FStar_Parser_AST.Attributes (es) -> begin
(

let uu____2675 = (

let uu____2676 = (str "attributes")
in (

let uu____2677 = (FStar_Pprint.separate_map break1 p_atomicTerm es)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2676 uu____2677)))
in (FStar_Pprint.group uu____2675))
end
| FStar_Parser_AST.If (e1, e2, e3) -> begin
(

let uu____2681 = (is_unit e3)
in (match (uu____2681) with
| true -> begin
(

let uu____2682 = (

let uu____2683 = (

let uu____2684 = (str "if")
in (

let uu____2685 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat uu____2684 uu____2685)))
in (

let uu____2686 = (

let uu____2687 = (str "then")
in (

let uu____2688 = (p_noSeqTerm e2)
in (op_Hat_Slash_Plus_Hat uu____2687 uu____2688)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2683 uu____2686)))
in (FStar_Pprint.group uu____2682))
end
| uu____2689 -> begin
(

let e2_doc = (

let uu____2691 = (

let uu____2692 = (unparen e2)
in uu____2692.FStar_Parser_AST.tm)
in (match (uu____2691) with
| FStar_Parser_AST.If (uu____2693, uu____2694, e3) when (is_unit e3) -> begin
(

let uu____2696 = (p_noSeqTerm e2)
in (soft_parens_with_nesting uu____2696))
end
| uu____2697 -> begin
(p_noSeqTerm e2)
end))
in (

let uu____2698 = (

let uu____2699 = (

let uu____2700 = (str "if")
in (

let uu____2701 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat uu____2700 uu____2701)))
in (

let uu____2702 = (

let uu____2703 = (

let uu____2704 = (str "then")
in (op_Hat_Slash_Plus_Hat uu____2704 e2_doc))
in (

let uu____2705 = (

let uu____2706 = (str "else")
in (

let uu____2707 = (p_noSeqTerm e3)
in (op_Hat_Slash_Plus_Hat uu____2706 uu____2707)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2703 uu____2705)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2699 uu____2702)))
in (FStar_Pprint.group uu____2698)))
end))
end
| FStar_Parser_AST.TryWith (e, branches) -> begin
(

let uu____2720 = (

let uu____2721 = (

let uu____2722 = (str "try")
in (

let uu____2723 = (p_noSeqTerm e)
in (prefix2 uu____2722 uu____2723)))
in (

let uu____2724 = (

let uu____2725 = (str "with")
in (

let uu____2726 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2725 uu____2726)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2721 uu____2724)))
in (FStar_Pprint.group uu____2720))
end
| FStar_Parser_AST.Match (e, branches) -> begin
(

let uu____2743 = (

let uu____2744 = (

let uu____2745 = (str "match")
in (

let uu____2746 = (p_noSeqTerm e)
in (

let uu____2747 = (str "with")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____2745 uu____2746 uu____2747))))
in (

let uu____2748 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2744 uu____2748)))
in (FStar_Pprint.group uu____2743))
end
| FStar_Parser_AST.LetOpen (uid, e) -> begin
(

let uu____2755 = (

let uu____2756 = (

let uu____2757 = (str "let open")
in (

let uu____2758 = (p_quident uid)
in (

let uu____2759 = (str "in")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____2757 uu____2758 uu____2759))))
in (

let uu____2760 = (p_term e)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2756 uu____2760)))
in (FStar_Pprint.group uu____2755))
end
| FStar_Parser_AST.Let (q, lbs, e) -> begin
(

let let_doc = (

let uu____2771 = (str "let")
in (

let uu____2772 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat uu____2771 uu____2772)))
in (

let uu____2773 = (

let uu____2774 = (

let uu____2775 = (

let uu____2776 = (str "and")
in (precede_break_separate_map let_doc uu____2776 p_letbinding lbs))
in (

let uu____2779 = (str "in")
in (FStar_Pprint.op_Hat_Slash_Hat uu____2775 uu____2779)))
in (FStar_Pprint.group uu____2774))
in (

let uu____2780 = (p_term e)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2773 uu____2780))))
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, typ_opt); FStar_Parser_AST.prange = uu____2783})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, branches); FStar_Parser_AST.range = uu____2786; FStar_Parser_AST.level = uu____2787}) when (matches_var maybe_x x) -> begin
(

let uu____2801 = (

let uu____2802 = (str "function")
in (

let uu____2803 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2802 uu____2803)))
in (FStar_Pprint.group uu____2801))
end
| FStar_Parser_AST.Assign (id, e) -> begin
(

let uu____2810 = (

let uu____2811 = (p_lident id)
in (

let uu____2812 = (

let uu____2813 = (p_noSeqTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow uu____2813))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2811 uu____2812)))
in (FStar_Pprint.group uu____2810))
end
| uu____2814 -> begin
(p_typ e)
end)))
and p_typ : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_typ' e e.FStar_Parser_AST.range))
and p_typ' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2817 = (

let uu____2818 = (unparen e)
in uu____2818.FStar_Parser_AST.tm)
in (match (uu____2817) with
| (FStar_Parser_AST.QForall (bs, trigger, e1)) | (FStar_Parser_AST.QExists (bs, trigger, e1)) -> begin
(

let uu____2834 = (

let uu____2835 = (

let uu____2836 = (p_quantifier e)
in (FStar_Pprint.op_Hat_Hat uu____2836 FStar_Pprint.space))
in (

let uu____2837 = (p_binders true bs)
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") uu____2835 uu____2837 FStar_Pprint.dot)))
in (

let uu____2838 = (

let uu____2839 = (p_trigger trigger)
in (

let uu____2840 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat uu____2839 uu____2840)))
in (prefix2 uu____2834 uu____2838)))
end
| uu____2841 -> begin
(p_simpleTerm e)
end)))
and p_quantifier : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2843 = (

let uu____2844 = (unparen e)
in uu____2844.FStar_Parser_AST.tm)
in (match (uu____2843) with
| FStar_Parser_AST.QForall (uu____2845) -> begin
(str "forall")
end
| FStar_Parser_AST.QExists (uu____2852) -> begin
(str "exists")
end
| uu____2859 -> begin
(failwith "Imposible : p_quantifier called on a non-quantifier term")
end)))
and p_trigger : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun uu___122_2860 -> (match (uu___122_2860) with
| [] -> begin
FStar_Pprint.empty
end
| pats -> begin
(

let uu____2867 = (

let uu____2868 = (

let uu____2869 = (str "pattern")
in (

let uu____2870 = (

let uu____2871 = (

let uu____2872 = (p_disjunctivePats pats)
in (jump2 uu____2872))
in (

let uu____2873 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2871 uu____2873)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2869 uu____2870)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2868))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____2867))
end))
and p_disjunctivePats : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun pats -> (

let uu____2877 = (str "\\/")
in (FStar_Pprint.separate_map uu____2877 p_conjunctivePats pats)))
and p_conjunctivePats : FStar_Parser_AST.term Prims.list  ->  FStar_Pprint.document = (fun pats -> (

let uu____2881 = (FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats)
in (FStar_Pprint.group uu____2881)))
and p_simpleTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2883 = (

let uu____2884 = (unparen e)
in uu____2884.FStar_Parser_AST.tm)
in (match (uu____2883) with
| FStar_Parser_AST.Abs (pats, e) -> begin
(

let uu____2889 = (

let uu____2890 = (str "fun")
in (

let uu____2891 = (

let uu____2892 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2892 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat uu____2890 uu____2891)))
in (

let uu____2893 = (p_term e)
in (op_Hat_Slash_Plus_Hat uu____2889 uu____2893)))
end
| uu____2894 -> begin
(p_tmIff e)
end)))
and p_maybeFocusArrow : Prims.bool  ->  FStar_Pprint.document = (fun b -> (match (b) with
| true -> begin
(str "~>")
end
| uu____2896 -> begin
FStar_Pprint.rarrow
end))
and p_patternBranch : (FStar_Parser_AST.pattern * FStar_Parser_AST.term Prims.option * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun uu____2897 -> (match (uu____2897) with
| (pat, when_opt, e) -> begin
(

let maybe_paren = (

let uu____2910 = (

let uu____2911 = (unparen e)
in uu____2911.FStar_Parser_AST.tm)
in (match (uu____2910) with
| (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) -> begin
soft_begin_end_with_nesting
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____2917); FStar_Parser_AST.prange = uu____2918})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, uu____2920); FStar_Parser_AST.range = uu____2921; FStar_Parser_AST.level = uu____2922}) when (matches_var maybe_x x) -> begin
soft_begin_end_with_nesting
end
| uu____2936 -> begin
(fun x -> x)
end))
in (

let uu____2938 = (

let uu____2939 = (

let uu____2940 = (

let uu____2941 = (

let uu____2942 = (

let uu____2943 = (p_disjunctivePattern pat)
in (

let uu____2944 = (

let uu____2945 = (p_maybeWhen when_opt)
in (FStar_Pprint.op_Hat_Hat uu____2945 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat uu____2943 uu____2944)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2942))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____2941))
in (FStar_Pprint.group uu____2940))
in (

let uu____2946 = (

let uu____2947 = (p_term e)
in (maybe_paren uu____2947))
in (op_Hat_Slash_Plus_Hat uu____2939 uu____2946)))
in (FStar_Pprint.group uu____2938)))
end))
and p_maybeWhen : FStar_Parser_AST.term Prims.option  ->  FStar_Pprint.document = (fun uu___123_2948 -> (match (uu___123_2948) with
| None -> begin
FStar_Pprint.empty
end
| Some (e) -> begin
(

let uu____2951 = (str "when")
in (

let uu____2952 = (

let uu____2953 = (p_tmFormula e)
in (FStar_Pprint.op_Hat_Hat uu____2953 FStar_Pprint.space))
in (op_Hat_Slash_Plus_Hat uu____2951 uu____2952)))
end))
and p_tmIff : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2955 = (

let uu____2956 = (unparen e)
in uu____2956.FStar_Parser_AST.tm)
in (match (uu____2955) with
| FStar_Parser_AST.Op ("<==>", (e1)::(e2)::[]) -> begin
(

let uu____2960 = (str "<==>")
in (

let uu____2961 = (p_tmImplies e1)
in (

let uu____2962 = (p_tmIff e2)
in (infix0 uu____2960 uu____2961 uu____2962))))
end
| uu____2963 -> begin
(p_tmImplies e)
end)))
and p_tmImplies : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2965 = (

let uu____2966 = (unparen e)
in uu____2966.FStar_Parser_AST.tm)
in (match (uu____2965) with
| FStar_Parser_AST.Op ("==>", (e1)::(e2)::[]) -> begin
(

let uu____2970 = (str "==>")
in (

let uu____2971 = (p_tmArrow p_tmFormula e1)
in (

let uu____2972 = (p_tmImplies e2)
in (infix0 uu____2970 uu____2971 uu____2972))))
end
| uu____2973 -> begin
(p_tmArrow p_tmFormula e)
end)))
and p_tmArrow : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_Tm e -> (

let uu____2978 = (

let uu____2979 = (unparen e)
in uu____2979.FStar_Parser_AST.tm)
in (match (uu____2978) with
| FStar_Parser_AST.Product (bs, tgt) -> begin
(

let uu____2984 = (

let uu____2985 = (FStar_Pprint.concat_map (fun b -> (

let uu____2987 = (p_binder false b)
in (

let uu____2988 = (

let uu____2989 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2989))
in (FStar_Pprint.op_Hat_Hat uu____2987 uu____2988)))) bs)
in (

let uu____2990 = (p_tmArrow p_Tm tgt)
in (FStar_Pprint.op_Hat_Hat uu____2985 uu____2990)))
in (FStar_Pprint.group uu____2984))
end
| uu____2991 -> begin
(p_Tm e)
end)))
and p_tmFormula : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2993 = (

let uu____2994 = (unparen e)
in uu____2994.FStar_Parser_AST.tm)
in (match (uu____2993) with
| FStar_Parser_AST.Op ("\\/", (e1)::(e2)::[]) -> begin
(

let uu____2998 = (str "\\/")
in (

let uu____2999 = (p_tmFormula e1)
in (

let uu____3000 = (p_tmConjunction e2)
in (infix0 uu____2998 uu____2999 uu____3000))))
end
| uu____3001 -> begin
(p_tmConjunction e)
end)))
and p_tmConjunction : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3003 = (

let uu____3004 = (unparen e)
in uu____3004.FStar_Parser_AST.tm)
in (match (uu____3003) with
| FStar_Parser_AST.Op ("/\\", (e1)::(e2)::[]) -> begin
(

let uu____3008 = (str "/\\")
in (

let uu____3009 = (p_tmConjunction e1)
in (

let uu____3010 = (p_tmTuple e2)
in (infix0 uu____3008 uu____3009 uu____3010))))
end
| uu____3011 -> begin
(p_tmTuple e)
end)))
and p_tmTuple : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_tmTuple' e e.FStar_Parser_AST.range))
and p_tmTuple' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3014 = (

let uu____3015 = (unparen e)
in uu____3015.FStar_Parser_AST.tm)
in (match (uu____3014) with
| FStar_Parser_AST.Construct (lid, args) when (is_tuple_constructor lid) -> begin
(

let uu____3024 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map uu____3024 (fun uu____3027 -> (match (uu____3027) with
| (e, uu____3031) -> begin
(p_tmEq e)
end)) args))
end
| uu____3032 -> begin
(p_tmEq e)
end)))
and paren_if : Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun curr mine doc -> (match ((mine <= curr)) with
| true -> begin
doc
end
| uu____3036 -> begin
(

let uu____3037 = (

let uu____3038 = (FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3038))
in (FStar_Pprint.group uu____3037))
end))
and p_tmEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n = (max_level (FStar_List.append (((colon_equals ()))::((pipe_right ()))::[]) (operatorInfix0ad12 ())))
in (p_tmEq' n e)))
and p_tmEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (

let uu____3063 = (

let uu____3064 = (unparen e)
in uu____3064.FStar_Parser_AST.tm)
in (match (uu____3063) with
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (((is_operatorInfix0ad12 op) || (op = "=")) || (op = "|>")) -> begin
(

let uu____3069 = (levels op)
in (match (uu____3069) with
| (left, mine, right) -> begin
(

let uu____3076 = (

let uu____3077 = (str op)
in (

let uu____3078 = (p_tmEq' left e1)
in (

let uu____3079 = (p_tmEq' right e2)
in (infix0 uu____3077 uu____3078 uu____3079))))
in (paren_if curr mine uu____3076))
end))
end
| FStar_Parser_AST.Op (":=", (e1)::(e2)::[]) -> begin
(

let uu____3083 = (

let uu____3084 = (p_tmEq e1)
in (

let uu____3085 = (

let uu____3086 = (

let uu____3087 = (

let uu____3088 = (p_tmEq e2)
in (op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____3088))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3087))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3086))
in (FStar_Pprint.op_Hat_Hat uu____3084 uu____3085)))
in (FStar_Pprint.group uu____3083))
end
| uu____3089 -> begin
(p_tmNoEq e)
end)))
and p_tmNoEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n = (max_level (((colon_colon ()))::((amp ()))::((opinfix3 ()))::((opinfix4 ()))::[]))
in (p_tmNoEq' n e)))
and p_tmNoEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (

let uu____3119 = (

let uu____3120 = (unparen e)
in uu____3120.FStar_Parser_AST.tm)
in (match (uu____3119) with
| FStar_Parser_AST.Construct (lid, ((e1, uu____3123))::((e2, uu____3125))::[]) when ((FStar_Ident.lid_equals lid FStar_Syntax_Const.cons_lid) && (

let uu____3135 = (is_list e)
in (not (uu____3135)))) -> begin
(

let op = "::"
in (

let uu____3137 = (levels op)
in (match (uu____3137) with
| (left, mine, right) -> begin
(

let uu____3144 = (

let uu____3145 = (str op)
in (

let uu____3146 = (p_tmNoEq' left e1)
in (

let uu____3147 = (p_tmNoEq' right e2)
in (infix0 uu____3145 uu____3146 uu____3147))))
in (paren_if curr mine uu____3144))
end)))
end
| FStar_Parser_AST.Sum (binders, res) -> begin
(

let op = "&"
in (

let uu____3153 = (levels op)
in (match (uu____3153) with
| (left, mine, right) -> begin
(

let p_dsumfst = (fun b -> (

let uu____3164 = (p_binder false b)
in (

let uu____3165 = (

let uu____3166 = (

let uu____3167 = (str "&")
in (FStar_Pprint.op_Hat_Hat uu____3167 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3166))
in (FStar_Pprint.op_Hat_Hat uu____3164 uu____3165))))
in (

let uu____3168 = (

let uu____3169 = (FStar_Pprint.concat_map p_dsumfst binders)
in (

let uu____3170 = (p_tmNoEq' right res)
in (FStar_Pprint.op_Hat_Hat uu____3169 uu____3170)))
in (paren_if curr mine uu____3168)))
end)))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (is_operatorInfix34 op) -> begin
(

let uu____3175 = (levels op)
in (match (uu____3175) with
| (left, mine, right) -> begin
(

let uu____3182 = (

let uu____3183 = (str op)
in (

let uu____3184 = (p_tmNoEq' left e1)
in (

let uu____3185 = (p_tmNoEq' right e2)
in (infix0 uu____3183 uu____3184 uu____3185))))
in (paren_if curr mine uu____3182))
end))
end
| FStar_Parser_AST.Op ("-", (e)::[]) -> begin
(

let uu____3188 = (levels "-")
in (match (uu____3188) with
| (left, mine, right) -> begin
(

let uu____3195 = (p_tmNoEq' mine e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____3195))
end))
end
| FStar_Parser_AST.NamedTyp (lid, e) -> begin
(

let uu____3198 = (

let uu____3199 = (p_lidentOrUnderscore lid)
in (

let uu____3200 = (

let uu____3201 = (p_appTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____3201))
in (FStar_Pprint.op_Hat_Slash_Hat uu____3199 uu____3200)))
in (FStar_Pprint.group uu____3198))
end
| FStar_Parser_AST.Refine (b, phi) -> begin
(p_refinedBinder b phi)
end
| FStar_Parser_AST.Record (with_opt, record_fields) -> begin
(

let uu____3214 = (

let uu____3215 = (default_or_map FStar_Pprint.empty p_with_clause with_opt)
in (

let uu____3216 = (

let uu____3217 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (FStar_Pprint.separate_map uu____3217 p_simpleDef record_fields))
in (FStar_Pprint.op_Hat_Hat uu____3215 uu____3216)))
in (braces_with_nesting uu____3214))
end
| FStar_Parser_AST.Op ("~", (e)::[]) -> begin
(

let uu____3222 = (

let uu____3223 = (str "~")
in (

let uu____3224 = (p_atomicTerm e)
in (FStar_Pprint.op_Hat_Hat uu____3223 uu____3224)))
in (FStar_Pprint.group uu____3222))
end
| uu____3225 -> begin
(p_appTerm e)
end)))
and p_with_clause : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3227 = (p_appTerm e)
in (

let uu____3228 = (

let uu____3229 = (

let uu____3230 = (str "with")
in (FStar_Pprint.op_Hat_Hat uu____3230 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3229))
in (FStar_Pprint.op_Hat_Hat uu____3227 uu____3228))))
and p_refinedBinder : FStar_Parser_AST.binder  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun b phi -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (lid, t) -> begin
(

let uu____3235 = (

let uu____3236 = (p_lident lid)
in (p_refinement b.FStar_Parser_AST.aqual uu____3236 t phi))
in (soft_parens_with_nesting uu____3235))
end
| FStar_Parser_AST.TAnnotated (uu____3237) -> begin
(failwith "Is this still used ?")
end
| (FStar_Parser_AST.Variable (_)) | (FStar_Parser_AST.TVariable (_)) | (FStar_Parser_AST.NoName (_)) -> begin
(

let uu____3243 = (

let uu____3244 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" uu____3244))
in (failwith uu____3243))
end))
and p_simpleDef : (FStar_Ident.lid * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun uu____3245 -> (match (uu____3245) with
| (lid, e) -> begin
(

let uu____3250 = (

let uu____3251 = (p_qlident lid)
in (

let uu____3252 = (

let uu____3253 = (p_tmIff e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____3253))
in (FStar_Pprint.op_Hat_Slash_Hat uu____3251 uu____3252)))
in (FStar_Pprint.group uu____3250))
end))
and p_appTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3255 = (

let uu____3256 = (unparen e)
in uu____3256.FStar_Parser_AST.tm)
in (match (uu____3255) with
| FStar_Parser_AST.App (uu____3257) when (is_general_application e) -> begin
(

let uu____3261 = (head_and_args e)
in (match (uu____3261) with
| (head, args) -> begin
(

let uu____3275 = (

let uu____3281 = (FStar_ST.read should_print_fs_typ_app)
in (match (uu____3281) with
| true -> begin
(

let uu____3289 = (FStar_Util.take (fun uu____3300 -> (match (uu____3300) with
| (uu____3303, aq) -> begin
(aq = FStar_Parser_AST.FsTypApp)
end)) args)
in (match (uu____3289) with
| (fs_typ_args, args) -> begin
(

let uu____3324 = (

let uu____3325 = (p_indexingTerm head)
in (

let uu____3326 = (

let uu____3327 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (soft_surround_separate_map (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.empty FStar_Pprint.langle uu____3327 FStar_Pprint.rangle p_fsTypArg fs_typ_args))
in (FStar_Pprint.op_Hat_Hat uu____3325 uu____3326)))
in ((uu____3324), (args)))
end))
end
| uu____3333 -> begin
(

let uu____3334 = (p_indexingTerm head)
in ((uu____3334), (args)))
end))
in (match (uu____3275) with
| (head_doc, args) -> begin
(

let uu____3346 = (

let uu____3347 = (FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space)
in (soft_surround_separate_map (Prims.parse_int "2") (Prims.parse_int "0") head_doc uu____3347 break1 FStar_Pprint.empty p_argTerm args))
in (FStar_Pprint.group uu____3346))
end))
end))
end
| FStar_Parser_AST.Construct (lid, args) when ((is_general_construction e) && (not ((is_dtuple_constructor lid)))) -> begin
(match (args) with
| [] -> begin
(p_quident lid)
end
| (arg)::[] -> begin
(

let uu____3367 = (

let uu____3368 = (p_quident lid)
in (

let uu____3369 = (p_argTerm arg)
in (FStar_Pprint.op_Hat_Slash_Hat uu____3368 uu____3369)))
in (FStar_Pprint.group uu____3367))
end
| (hd)::tl -> begin
(

let uu____3379 = (

let uu____3380 = (

let uu____3381 = (

let uu____3382 = (p_quident lid)
in (

let uu____3383 = (p_argTerm hd)
in (prefix2 uu____3382 uu____3383)))
in (FStar_Pprint.group uu____3381))
in (

let uu____3384 = (

let uu____3385 = (FStar_Pprint.separate_map break1 p_argTerm tl)
in (jump2 uu____3385))
in (FStar_Pprint.op_Hat_Hat uu____3380 uu____3384)))
in (FStar_Pprint.group uu____3379))
end)
end
| uu____3388 -> begin
(p_indexingTerm e)
end)))
and p_argTerm : (FStar_Parser_AST.term * FStar_Parser_AST.imp)  ->  FStar_Pprint.document = (fun arg_imp -> (match (arg_imp) with
| ({FStar_Parser_AST.tm = FStar_Parser_AST.Uvar (uu____3392); FStar_Parser_AST.range = uu____3393; FStar_Parser_AST.level = uu____3394}, FStar_Parser_AST.UnivApp) -> begin
(p_univar (Prims.fst arg_imp))
end
| (u, FStar_Parser_AST.UnivApp) -> begin
(p_universe u)
end
| (e, FStar_Parser_AST.FsTypApp) -> begin
((FStar_Util.print_warning "Unexpected FsTypApp, output might not be formatted correctly.\n");
(

let uu____3398 = (p_indexingTerm e)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.langle uu____3398 FStar_Pprint.rangle));
)
end
| (e, FStar_Parser_AST.Hash) -> begin
(

let uu____3400 = (str "#")
in (

let uu____3401 = (p_indexingTerm e)
in (FStar_Pprint.op_Hat_Hat uu____3400 uu____3401)))
end
| (e, FStar_Parser_AST.Nothing) -> begin
(p_indexingTerm e)
end))
and p_fsTypArg : (FStar_Parser_AST.term * FStar_Parser_AST.imp)  ->  FStar_Pprint.document = (fun uu____3403 -> (match (uu____3403) with
| (e, uu____3407) -> begin
(p_indexingTerm e)
end))
and p_indexingTerm_aux : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun exit e -> (

let uu____3412 = (

let uu____3413 = (unparen e)
in uu____3413.FStar_Parser_AST.tm)
in (match (uu____3412) with
| FStar_Parser_AST.Op (".()", (e1)::(e2)::[]) -> begin
(

let uu____3417 = (

let uu____3418 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (

let uu____3419 = (

let uu____3420 = (

let uu____3421 = (p_term e2)
in (soft_parens_with_nesting uu____3421))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3420))
in (FStar_Pprint.op_Hat_Hat uu____3418 uu____3419)))
in (FStar_Pprint.group uu____3417))
end
| FStar_Parser_AST.Op (".[]", (e1)::(e2)::[]) -> begin
(

let uu____3425 = (

let uu____3426 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (

let uu____3427 = (

let uu____3428 = (

let uu____3429 = (p_term e2)
in (soft_brackets_with_nesting uu____3429))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3428))
in (FStar_Pprint.op_Hat_Hat uu____3426 uu____3427)))
in (FStar_Pprint.group uu____3425))
end
| uu____3430 -> begin
(exit e)
end)))
and p_indexingTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_indexingTerm_aux p_atomicTerm e))
and p_atomicTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3433 = (

let uu____3434 = (unparen e)
in uu____3434.FStar_Parser_AST.tm)
in (match (uu____3433) with
| FStar_Parser_AST.LetOpen (lid, e) -> begin
(

let uu____3437 = (p_quident lid)
in (

let uu____3438 = (

let uu____3439 = (

let uu____3440 = (p_term e)
in (soft_parens_with_nesting uu____3440))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3439))
in (FStar_Pprint.op_Hat_Hat uu____3437 uu____3438)))
end
| FStar_Parser_AST.Name (lid) -> begin
(p_quident lid)
end
| FStar_Parser_AST.Op (op, (e)::[]) when (is_general_prefix_op op) -> begin
(

let uu____3445 = (str op)
in (

let uu____3446 = (p_atomicTerm e)
in (FStar_Pprint.op_Hat_Hat uu____3445 uu____3446)))
end
| uu____3447 -> begin
(p_atomicTermNotQUident e)
end)))
and p_atomicTermNotQUident : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3449 = (

let uu____3450 = (unparen e)
in uu____3450.FStar_Parser_AST.tm)
in (match (uu____3449) with
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
(

let uu____3459 = (str op)
in (

let uu____3460 = (p_atomicTermNotQUident e)
in (FStar_Pprint.op_Hat_Hat uu____3459 uu____3460)))
end
| FStar_Parser_AST.Op (op, []) -> begin
(

let uu____3463 = (

let uu____3464 = (

let uu____3465 = (str op)
in (

let uu____3466 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat uu____3465 uu____3466)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3464))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3463))
end
| FStar_Parser_AST.Construct (lid, args) when (is_dtuple_constructor lid) -> begin
(

let uu____3475 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (

let uu____3476 = (

let uu____3477 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (

let uu____3478 = (FStar_List.map Prims.fst args)
in (FStar_Pprint.separate_map uu____3477 p_tmEq uu____3478)))
in (

let uu____3482 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____3475 uu____3476 uu____3482))))
end
| FStar_Parser_AST.Project (e, lid) -> begin
(

let uu____3485 = (

let uu____3486 = (p_atomicTermNotQUident e)
in (

let uu____3487 = (

let uu____3488 = (p_qlident lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3488))
in (FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0") uu____3486 uu____3487)))
in (FStar_Pprint.group uu____3485))
end
| uu____3489 -> begin
(p_projectionLHS e)
end)))
and p_projectionLHS : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3491 = (

let uu____3492 = (unparen e)
in uu____3492.FStar_Parser_AST.tm)
in (match (uu____3491) with
| FStar_Parser_AST.Var (lid) -> begin
(p_qlident lid)
end
| FStar_Parser_AST.Projector (constr_lid, field_lid) -> begin
(

let uu____3496 = (p_quident constr_lid)
in (

let uu____3497 = (

let uu____3498 = (

let uu____3499 = (p_lident field_lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3499))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____3498))
in (FStar_Pprint.op_Hat_Hat uu____3496 uu____3497)))
end
| FStar_Parser_AST.Discrim (constr_lid) -> begin
(

let uu____3501 = (p_quident constr_lid)
in (FStar_Pprint.op_Hat_Hat uu____3501 FStar_Pprint.qmark))
end
| FStar_Parser_AST.Paren (e) -> begin
(

let uu____3503 = (p_term e)
in (soft_parens_with_nesting uu____3503))
end
| uu____3504 when (is_array e) -> begin
(

let es = (extract_from_list e)
in (

let uu____3507 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar)
in (

let uu____3508 = (

let uu____3509 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (separate_map_or_flow uu____3509 p_noSeqTerm es))
in (

let uu____3510 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") uu____3507 uu____3508 uu____3510)))))
end
| uu____3511 when (is_list e) -> begin
(

let uu____3512 = (

let uu____3513 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (

let uu____3514 = (extract_from_list e)
in (separate_map_or_flow uu____3513 p_noSeqTerm uu____3514)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket uu____3512 FStar_Pprint.rbracket))
end
| uu____3516 when (is_lex_list e) -> begin
(

let uu____3517 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket)
in (

let uu____3518 = (

let uu____3519 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (

let uu____3520 = (extract_from_list e)
in (separate_map_or_flow uu____3519 p_noSeqTerm uu____3520)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____3517 uu____3518 FStar_Pprint.rbracket)))
end
| uu____3522 when (is_ref_set e) -> begin
(

let es = (extract_from_ref_set e)
in (

let uu____3525 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace)
in (

let uu____3526 = (

let uu____3527 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (separate_map_or_flow uu____3527 p_appTerm es))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") uu____3525 uu____3526 FStar_Pprint.rbrace))))
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Op (_)) | (FStar_Parser_AST.Tvar (_)) | (FStar_Parser_AST.Uvar (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) | (FStar_Parser_AST.Construct (_)) | (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.App (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.LetOpen (_)) | (FStar_Parser_AST.Seq (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Ascribed (_)) | (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Project (_)) | (FStar_Parser_AST.Product (_)) | (FStar_Parser_AST.Sum (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Refine (_)) | (FStar_Parser_AST.NamedTyp (_)) | (FStar_Parser_AST.Requires (_)) | (FStar_Parser_AST.Ensures (_)) | (FStar_Parser_AST.Assign (_)) | (FStar_Parser_AST.Attributes (_)) -> begin
(

let uu____3556 = (p_term e)
in (soft_parens_with_nesting uu____3556))
end
| FStar_Parser_AST.Labeled (uu____3557) -> begin
(failwith "Not valid in universe")
end)))
and p_constant : FStar_Const.sconst  ->  FStar_Pprint.document = (fun uu___126_3561 -> (match (uu___126_3561) with
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
(

let uu____3565 = (FStar_Pprint.doc_of_char x)
in (FStar_Pprint.squotes uu____3565))
end
| FStar_Const.Const_string (bytes, uu____3567) -> begin
(

let uu____3570 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes uu____3570))
end
| FStar_Const.Const_bytearray (bytes, uu____3572) -> begin
(

let uu____3575 = (

let uu____3576 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes uu____3576))
in (

let uu____3577 = (str "B")
in (FStar_Pprint.op_Hat_Hat uu____3575 uu____3577)))
end
| FStar_Const.Const_int (repr, sign_width_opt) -> begin
(

let signedness = (fun uu___124_3589 -> (match (uu___124_3589) with
| FStar_Const.Unsigned -> begin
(str "u")
end
| FStar_Const.Signed -> begin
FStar_Pprint.empty
end))
in (

let width = (fun uu___125_3593 -> (match (uu___125_3593) with
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

let ending = (default_or_map FStar_Pprint.empty (fun uu____3597 -> (match (uu____3597) with
| (s, w) -> begin
(

let uu____3602 = (signedness s)
in (

let uu____3603 = (width w)
in (FStar_Pprint.op_Hat_Hat uu____3602 uu____3603)))
end)) sign_width_opt)
in (

let uu____3604 = (str repr)
in (FStar_Pprint.op_Hat_Hat uu____3604 ending)))))
end
| FStar_Const.Const_range (r) -> begin
(

let uu____3606 = (FStar_Range.string_of_range r)
in (str uu____3606))
end
| FStar_Const.Const_reify -> begin
(str "reify")
end
| FStar_Const.Const_reflect (lid) -> begin
(

let uu____3608 = (p_quident lid)
in (

let uu____3609 = (

let uu____3610 = (

let uu____3611 = (str "reflect")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3611))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____3610))
in (FStar_Pprint.op_Hat_Hat uu____3608 uu____3609)))
end))
and p_universe : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (

let uu____3613 = (str "u#")
in (

let uu____3614 = (p_atomicUniverse u)
in (FStar_Pprint.op_Hat_Hat uu____3613 uu____3614))))
and p_universeFrom : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (

let uu____3616 = (

let uu____3617 = (unparen u)
in uu____3617.FStar_Parser_AST.tm)
in (match (uu____3616) with
| FStar_Parser_AST.Op ("+", (u1)::(u2)::[]) -> begin
(

let uu____3621 = (

let uu____3622 = (p_universeFrom u1)
in (

let uu____3623 = (

let uu____3624 = (p_universeFrom u2)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____3624))
in (FStar_Pprint.op_Hat_Slash_Hat uu____3622 uu____3623)))
in (FStar_Pprint.group uu____3621))
end
| FStar_Parser_AST.App (uu____3625) -> begin
(

let uu____3629 = (head_and_args u)
in (match (uu____3629) with
| (head, args) -> begin
(

let uu____3643 = (

let uu____3644 = (unparen head)
in uu____3644.FStar_Parser_AST.tm)
in (match (uu____3643) with
| FStar_Parser_AST.Var (maybe_max_lid) when (FStar_Ident.lid_equals maybe_max_lid FStar_Syntax_Const.max_lid) -> begin
(

let uu____3646 = (

let uu____3647 = (p_qlident FStar_Syntax_Const.max_lid)
in (

let uu____3648 = (FStar_Pprint.separate_map FStar_Pprint.space (fun uu____3651 -> (match (uu____3651) with
| (u, uu____3655) -> begin
(p_atomicUniverse u)
end)) args)
in (op_Hat_Slash_Plus_Hat uu____3647 uu____3648)))
in (FStar_Pprint.group uu____3646))
end
| uu____3656 -> begin
(

let uu____3657 = (

let uu____3658 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" uu____3658))
in (failwith uu____3657))
end))
end))
end
| uu____3659 -> begin
(p_atomicUniverse u)
end)))
and p_atomicUniverse : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (

let uu____3661 = (

let uu____3662 = (unparen u)
in uu____3662.FStar_Parser_AST.tm)
in (match (uu____3661) with
| FStar_Parser_AST.Wild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (r, sw)) -> begin
(p_constant (FStar_Const.Const_int (((r), (sw)))))
end
| FStar_Parser_AST.Uvar (uu____3674) -> begin
(p_univar u)
end
| FStar_Parser_AST.Paren (u) -> begin
(

let uu____3676 = (p_universeFrom u)
in (soft_parens_with_nesting uu____3676))
end
| (FStar_Parser_AST.Op ("+", (_)::(_)::[])) | (FStar_Parser_AST.App (_)) -> begin
(

let uu____3681 = (p_universeFrom u)
in (soft_parens_with_nesting uu____3681))
end
| uu____3682 -> begin
(

let uu____3683 = (

let uu____3684 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" uu____3684))
in (failwith uu____3683))
end)))
and p_univar : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (

let uu____3686 = (

let uu____3687 = (unparen u)
in uu____3687.FStar_Parser_AST.tm)
in (match (uu____3686) with
| FStar_Parser_AST.Uvar (id) -> begin
(str (FStar_Ident.text_of_id id))
end
| uu____3689 -> begin
(

let uu____3690 = (

let uu____3691 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Not a universe variable %s" uu____3691))
in (failwith uu____3690))
end)))


let term_to_document : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_term e))


let decl_to_document : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun e -> (p_decl e))


let modul_to_document : FStar_Parser_AST.modul  ->  FStar_Pprint.document = (fun m -> ((FStar_ST.write should_print_fs_typ_app false);
(

let res = (match (m) with
| (FStar_Parser_AST.Module (_, decls)) | (FStar_Parser_AST.Interface (_, decls, _)) -> begin
(

let uu____3713 = (FStar_All.pipe_right decls (FStar_List.map decl_to_document))
in (FStar_All.pipe_right uu____3713 (FStar_Pprint.separate FStar_Pprint.hardline)))
end)
in ((FStar_ST.write should_print_fs_typ_app false);
res;
));
))


let comments_to_document : (Prims.string * FStar_Range.range) Prims.list  ->  FStar_Pprint.document = (fun comments -> (FStar_Pprint.separate_map FStar_Pprint.hardline (fun uu____3732 -> (match (uu____3732) with
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

let uu____3779 = (match (ds) with
| ({FStar_Parser_AST.d = FStar_Parser_AST.Pragma (FStar_Parser_AST.LightOff); FStar_Parser_AST.drange = uu____3786; FStar_Parser_AST.doc = uu____3787; FStar_Parser_AST.quals = uu____3788; FStar_Parser_AST.attrs = uu____3789})::uu____3790 -> begin
(

let d0 = (FStar_List.hd ds)
in (

let uu____3794 = (

let uu____3796 = (

let uu____3798 = (FStar_List.tl ds)
in (d)::uu____3798)
in (d0)::uu____3796)
in ((uu____3794), (d0.FStar_Parser_AST.drange))))
end
| uu____3801 -> begin
(((d)::ds), (d.FStar_Parser_AST.drange))
end)
in (match (uu____3779) with
| (decls, first_range) -> begin
(

let extract_decl_range = (fun d -> d.FStar_Parser_AST.drange)
in ((FStar_ST.write comment_stack comments);
(

let initial_comment = (

let uu____3824 = (FStar_Range.start_of_range first_range)
in (place_comments_until_pos (Prims.parse_int "0") (Prims.parse_int "1") uu____3824 FStar_Pprint.empty))
in (

let doc = (separate_map_with_comments FStar_Pprint.empty FStar_Pprint.empty decl_to_document decls extract_decl_range)
in (

let comments = (FStar_ST.read comment_stack)
in ((FStar_ST.write comment_stack []);
(FStar_ST.write should_print_fs_typ_app false);
(

let uu____3846 = (FStar_Pprint.op_Hat_Hat initial_comment doc)
in ((uu____3846), (comments)));
))));
))
end))
end);
)))




