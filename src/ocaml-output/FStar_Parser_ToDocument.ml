
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


let token_to_string : (FStar_BaseTypes.char, Prims.string) FStar_Util.either  ->  Prims.string = (fun uu___114_577 -> (match (uu___114_577) with
| FStar_Util.Inl (c) -> begin
(Prims.strcat (FStar_Util.string_of_char c) ".*")
end
| FStar_Util.Inr (s) -> begin
s
end))


let matches_token : Prims.string  ->  (FStar_Char.char, Prims.string) FStar_Util.either  ->  Prims.bool = (fun s uu___115_589 -> (match (uu___115_589) with
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

let levels_from_associativity = (fun l uu___116_947 -> (match (uu___116_947) with
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

let uu____1807 = (

let uu____1808 = (FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc)
in (

let uu____1809 = (

let uu____1810 = (p_attributes d.FStar_Parser_AST.attrs)
in (

let uu____1811 = (

let uu____1812 = (p_qualifiers d.FStar_Parser_AST.quals)
in (

let uu____1813 = (

let uu____1814 = (p_rawDecl d)
in (FStar_Pprint.op_Hat_Hat (match ((d.FStar_Parser_AST.quals = [])) with
| true -> begin
FStar_Pprint.empty
end
| uu____1815 -> begin
break1
end) uu____1814))
in (FStar_Pprint.op_Hat_Hat uu____1812 uu____1813)))
in (FStar_Pprint.op_Hat_Hat uu____1810 uu____1811)))
in (FStar_Pprint.op_Hat_Hat uu____1808 uu____1809)))
in (FStar_Pprint.group uu____1807)))
and p_attributes : FStar_Parser_AST.attributes_  ->  FStar_Pprint.document = (fun attrs -> (

let uu____1817 = (

let uu____1818 = (str "@")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____1818))
in (

let uu____1819 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline)
in (soft_surround_separate_map (Prims.parse_int "0") (Prims.parse_int "2") FStar_Pprint.empty uu____1817 FStar_Pprint.space uu____1819 p_atomicTerm attrs))))
and p_fsdoc : FStar_Parser_AST.fsdoc  ->  FStar_Pprint.document = (fun uu____1820 -> (match (uu____1820) with
| (doc, kwd_args) -> begin
(

let kwd_args_doc = (match (kwd_args) with
| [] -> begin
FStar_Pprint.empty
end
| kwd_args -> begin
(

let process_kwd_arg = (fun uu____1841 -> (match (uu____1841) with
| (kwd, arg) -> begin
(

let uu____1846 = (str "@")
in (

let uu____1847 = (

let uu____1848 = (str kwd)
in (

let uu____1849 = (

let uu____1850 = (str arg)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1850))
in (FStar_Pprint.op_Hat_Hat uu____1848 uu____1849)))
in (FStar_Pprint.op_Hat_Hat uu____1846 uu____1847)))
end))
in (

let uu____1851 = (

let uu____1852 = (FStar_Pprint.separate_map FStar_Pprint.hardline process_kwd_arg kwd_args)
in (FStar_Pprint.op_Hat_Hat uu____1852 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____1851)))
end)
in (

let uu____1855 = (

let uu____1856 = (

let uu____1857 = (

let uu____1858 = (

let uu____1859 = (str doc)
in (

let uu____1860 = (

let uu____1861 = (

let uu____1862 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1862))
in (FStar_Pprint.op_Hat_Hat kwd_args_doc uu____1861))
in (FStar_Pprint.op_Hat_Hat uu____1859 uu____1860)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1858))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1857))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____1856))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____1855)))
end))
and p_rawDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Open (uid) -> begin
(

let uu____1865 = (

let uu____1866 = (str "open")
in (

let uu____1867 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat uu____1866 uu____1867)))
in (FStar_Pprint.group uu____1865))
end
| FStar_Parser_AST.Include (uid) -> begin
(

let uu____1869 = (

let uu____1870 = (str "include")
in (

let uu____1871 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat uu____1870 uu____1871)))
in (FStar_Pprint.group uu____1869))
end
| FStar_Parser_AST.ModuleAbbrev (uid1, uid2) -> begin
(

let uu____1874 = (

let uu____1875 = (str "module")
in (

let uu____1876 = (

let uu____1877 = (

let uu____1878 = (p_uident uid1)
in (

let uu____1879 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____1878 uu____1879)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1877))
in (FStar_Pprint.op_Hat_Hat uu____1875 uu____1876)))
in (

let uu____1880 = (p_quident uid2)
in (op_Hat_Slash_Plus_Hat uu____1874 uu____1880)))
end
| FStar_Parser_AST.TopLevelModule (uid) -> begin
(

let uu____1882 = (

let uu____1883 = (str "module")
in (

let uu____1884 = (

let uu____1885 = (p_quident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1885))
in (FStar_Pprint.op_Hat_Hat uu____1883 uu____1884)))
in (FStar_Pprint.group uu____1882))
end
| FStar_Parser_AST.Tycon (true, ((FStar_Parser_AST.TyconAbbrev (uid, tpars, None, t), None))::[]) -> begin
(

let effect_prefix_doc = (

let uu____1904 = (str "effect")
in (

let uu____1905 = (

let uu____1906 = (p_uident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1906))
in (FStar_Pprint.op_Hat_Hat uu____1904 uu____1905)))
in (

let uu____1907 = (

let uu____1908 = (p_typars tpars)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") effect_prefix_doc uu____1908 FStar_Pprint.equals))
in (

let uu____1909 = (p_typ t)
in (op_Hat_Slash_Plus_Hat uu____1907 uu____1909))))
end
| FStar_Parser_AST.Tycon (false, tcdefs) -> begin
(

let uu____1919 = (str "type")
in (

let uu____1920 = (str "and")
in (precede_break_separate_map uu____1919 uu____1920 p_fsdocTypeDeclPairs tcdefs)))
end
| FStar_Parser_AST.TopLevelLet (q, lbs) -> begin
(

let let_doc = (

let uu____1933 = (str "let")
in (

let uu____1934 = (

let uu____1935 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat uu____1935 FStar_Pprint.space))
in (FStar_Pprint.op_Hat_Hat uu____1933 uu____1934)))
in (

let uu____1936 = (

let uu____1937 = (str "and")
in (FStar_Pprint.op_Hat_Hat uu____1937 FStar_Pprint.space))
in (separate_map_with_comments let_doc uu____1936 p_letbinding lbs (fun uu____1940 -> (match (uu____1940) with
| (p, t) -> begin
(FStar_Range.union_ranges p.FStar_Parser_AST.prange t.FStar_Parser_AST.range)
end)))))
end
| FStar_Parser_AST.Val (lid, t) -> begin
(

let uu____1947 = (

let uu____1948 = (str "val")
in (

let uu____1949 = (

let uu____1950 = (

let uu____1951 = (p_lident lid)
in (

let uu____1952 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat uu____1951 uu____1952)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1950))
in (FStar_Pprint.op_Hat_Hat uu____1948 uu____1949)))
in (

let uu____1953 = (p_typ t)
in (op_Hat_Slash_Plus_Hat uu____1947 uu____1953)))
end
| FStar_Parser_AST.Assume (id, t) -> begin
(

let decl_keyword = (

let uu____1957 = (

let uu____1958 = (FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_All.pipe_right uu____1958 FStar_Util.is_upper))
in (match (uu____1957) with
| true -> begin
FStar_Pprint.empty
end
| uu____1959 -> begin
(

let uu____1960 = (str "val")
in (FStar_Pprint.op_Hat_Hat uu____1960 FStar_Pprint.space))
end))
in (

let uu____1961 = (

let uu____1962 = (

let uu____1963 = (p_ident id)
in (

let uu____1964 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat uu____1963 uu____1964)))
in (FStar_Pprint.op_Hat_Hat decl_keyword uu____1962))
in (

let uu____1965 = (p_typ t)
in (op_Hat_Slash_Plus_Hat uu____1961 uu____1965))))
end
| FStar_Parser_AST.Exception (uid, t_opt) -> begin
(

let uu____1970 = (str "exception")
in (

let uu____1971 = (

let uu____1972 = (

let uu____1973 = (p_uident uid)
in (

let uu____1974 = (FStar_Pprint.optional (fun t -> (

let uu____1976 = (str "of")
in (

let uu____1977 = (p_typ t)
in (op_Hat_Slash_Plus_Hat uu____1976 uu____1977)))) t_opt)
in (FStar_Pprint.op_Hat_Hat uu____1973 uu____1974)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1972))
in (FStar_Pprint.op_Hat_Hat uu____1970 uu____1971)))
end
| FStar_Parser_AST.NewEffect (ne) -> begin
(

let uu____1979 = (str "new_effect")
in (

let uu____1980 = (

let uu____1981 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1981))
in (FStar_Pprint.op_Hat_Hat uu____1979 uu____1980)))
end
| FStar_Parser_AST.SubEffect (se) -> begin
(

let uu____1983 = (str "sub_effect")
in (

let uu____1984 = (

let uu____1985 = (p_subEffect se)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1985))
in (FStar_Pprint.op_Hat_Hat uu____1983 uu____1984)))
end
| FStar_Parser_AST.NewEffectForFree (ne) -> begin
(

let uu____1987 = (str "new_effect_for_free")
in (

let uu____1988 = (

let uu____1989 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1989))
in (FStar_Pprint.op_Hat_Hat uu____1987 uu____1988)))
end
| FStar_Parser_AST.Pragma (p) -> begin
(p_pragma p)
end
| FStar_Parser_AST.Fsdoc (doc) -> begin
(

let uu____1992 = (p_fsdoc doc)
in (FStar_Pprint.op_Hat_Hat uu____1992 FStar_Pprint.hardline))
end
| FStar_Parser_AST.Main (uu____1993) -> begin
(failwith "*Main declaration* : Is that really still in use ??")
end
| FStar_Parser_AST.Tycon (true, uu____1994) -> begin
(failwith "Effect abbreviation is expected to be defined by an abbreviation")
end))
and p_pragma : FStar_Parser_AST.pragma  ->  FStar_Pprint.document = (fun uu___117_2003 -> (match (uu___117_2003) with
| FStar_Parser_AST.SetOptions (s) -> begin
(

let uu____2005 = (str "#set-options")
in (

let uu____2006 = (

let uu____2007 = (

let uu____2008 = (str s)
in (FStar_Pprint.dquotes uu____2008))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2007))
in (FStar_Pprint.op_Hat_Hat uu____2005 uu____2006)))
end
| FStar_Parser_AST.ResetOptions (s_opt) -> begin
(

let uu____2011 = (str "#reset-options")
in (

let uu____2012 = (FStar_Pprint.optional (fun s -> (

let uu____2014 = (

let uu____2015 = (str s)
in (FStar_Pprint.dquotes uu____2015))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2014))) s_opt)
in (FStar_Pprint.op_Hat_Hat uu____2011 uu____2012)))
end
| FStar_Parser_AST.LightOff -> begin
((FStar_ST.write should_print_fs_typ_app true);
(str "#light \"off\"");
)
end))
and p_typars : FStar_Parser_AST.binder Prims.list  ->  FStar_Pprint.document = (fun bs -> (p_binders true bs))
and p_fsdocTypeDeclPairs : (FStar_Parser_AST.tycon * FStar_Parser_AST.fsdoc Prims.option)  ->  FStar_Pprint.document = (fun uu____2021 -> (match (uu____2021) with
| (typedecl, fsdoc_opt) -> begin
(

let uu____2029 = (FStar_Pprint.optional p_fsdoc fsdoc_opt)
in (

let uu____2030 = (p_typeDecl typedecl)
in (FStar_Pprint.op_Hat_Hat uu____2029 uu____2030)))
end))
and p_typeDecl : FStar_Parser_AST.tycon  ->  FStar_Pprint.document = (fun uu___118_2031 -> (match (uu___118_2031) with
| FStar_Parser_AST.TyconAbstract (lid, bs, typ_opt) -> begin
(

let empty' = (fun uu____2042 -> FStar_Pprint.empty)
in (p_typeDeclPrefix lid bs typ_opt empty'))
end
| FStar_Parser_AST.TyconAbbrev (lid, bs, typ_opt, t) -> begin
(

let f = (fun uu____2054 -> (

let uu____2055 = (p_typ t)
in (prefix2 FStar_Pprint.equals uu____2055)))
in (p_typeDeclPrefix lid bs typ_opt f))
end
| FStar_Parser_AST.TyconRecord (lid, bs, typ_opt, record_field_decls) -> begin
(

let p_recordFieldAndComments = (fun uu____2081 -> (match (uu____2081) with
| (lid, t, doc_opt) -> begin
(

let uu____2091 = (FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range)
in (with_comment p_recordFieldDecl ((lid), (t), (doc_opt)) uu____2091))
end))
in (

let p_fields = (fun uu____2100 -> (

let uu____2101 = (

let uu____2102 = (

let uu____2103 = (

let uu____2104 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (FStar_Pprint.separate_map uu____2104 p_recordFieldAndComments record_field_decls))
in (braces_with_nesting uu____2103))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2102))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____2101)))
in (p_typeDeclPrefix lid bs typ_opt p_fields)))
end
| FStar_Parser_AST.TyconVariant (lid, bs, typ_opt, ct_decls) -> begin
(

let p_constructorBranchAndComments = (fun uu____2140 -> (match (uu____2140) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let range = (

let uu____2156 = (

let uu____2157 = (FStar_Util.map_opt t_opt (fun t -> t.FStar_Parser_AST.range))
in (FStar_Util.dflt uid.FStar_Ident.idRange uu____2157))
in (FStar_Range.extend_to_end_of_line uu____2156))
in (

let p_constructorBranch = (fun decl -> (

let uu____2176 = (

let uu____2177 = (

let uu____2178 = (p_constructorDecl decl)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2178))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____2177))
in (FStar_Pprint.group uu____2176)))
in (with_comment p_constructorBranch ((uid), (t_opt), (doc_opt), (use_of)) range)))
end))
in (

let datacon_doc = (fun uu____2190 -> (

let uu____2191 = (FStar_Pprint.separate_map break1 p_constructorBranchAndComments ct_decls)
in (FStar_Pprint.group uu____2191)))
in (p_typeDeclPrefix lid bs typ_opt (fun uu____2198 -> (

let uu____2199 = (datacon_doc ())
in (prefix2 FStar_Pprint.equals uu____2199))))))
end))
and p_typeDeclPrefix : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.knd Prims.option  ->  (Prims.unit  ->  FStar_Pprint.document)  ->  FStar_Pprint.document = (fun lid bs typ_opt cont -> (match (((bs = []) && (typ_opt = None))) with
| true -> begin
(

let uu____2210 = (p_ident lid)
in (

let uu____2211 = (

let uu____2212 = (cont ())
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2212))
in (FStar_Pprint.op_Hat_Hat uu____2210 uu____2211)))
end
| uu____2213 -> begin
(

let binders_doc = (

let uu____2215 = (p_typars bs)
in (

let uu____2216 = (FStar_Pprint.optional (fun t -> (

let uu____2218 = (

let uu____2219 = (

let uu____2220 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2220))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2219))
in (FStar_Pprint.op_Hat_Hat break1 uu____2218))) typ_opt)
in (FStar_Pprint.op_Hat_Hat uu____2215 uu____2216)))
in (

let uu____2221 = (p_ident lid)
in (

let uu____2222 = (cont ())
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____2221 binders_doc uu____2222))))
end))
and p_recordFieldDecl : (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc Prims.option)  ->  FStar_Pprint.document = (fun uu____2223 -> (match (uu____2223) with
| (lid, t, doc_opt) -> begin
(

let uu____2233 = (

let uu____2234 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (

let uu____2235 = (

let uu____2236 = (p_lident lid)
in (

let uu____2237 = (

let uu____2238 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2238))
in (FStar_Pprint.op_Hat_Hat uu____2236 uu____2237)))
in (FStar_Pprint.op_Hat_Hat uu____2234 uu____2235)))
in (FStar_Pprint.group uu____2233))
end))
and p_constructorDecl : (FStar_Ident.ident * FStar_Parser_AST.term Prims.option * FStar_Parser_AST.fsdoc Prims.option * Prims.bool)  ->  FStar_Pprint.document = (fun uu____2239 -> (match (uu____2239) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let sep = (match (use_of) with
| true -> begin
(str "of")
end
| uu____2255 -> begin
FStar_Pprint.colon
end)
in (

let uid_doc = (p_uident uid)
in (

let uu____2257 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (

let uu____2258 = (default_or_map uid_doc (fun t -> (

let uu____2260 = (

let uu____2261 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep)
in (FStar_Pprint.op_Hat_Hat uid_doc uu____2261))
in (

let uu____2262 = (p_typ t)
in (op_Hat_Slash_Plus_Hat uu____2260 uu____2262)))) t_opt)
in (FStar_Pprint.op_Hat_Hat uu____2257 uu____2258)))))
end))
and p_letbinding : (FStar_Parser_AST.pattern * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun uu____2263 -> (match (uu____2263) with
| (pat, e) -> begin
(

let pat_doc = (

let uu____2269 = (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, t) -> begin
(

let uu____2276 = (

let uu____2277 = (

let uu____2278 = (

let uu____2279 = (

let uu____2280 = (p_tmArrow p_tmNoEq t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2280))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2279))
in (FStar_Pprint.group uu____2278))
in (FStar_Pprint.op_Hat_Hat break1 uu____2277))
in ((pat), (uu____2276)))
end
| uu____2281 -> begin
((pat), (FStar_Pprint.empty))
end)
in (match (uu____2269) with
| (pat, ascr_doc) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____2285); FStar_Parser_AST.prange = uu____2286}, pats) -> begin
(

let uu____2292 = (p_lident x)
in (

let uu____2293 = (

let uu____2294 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Hat uu____2294 ascr_doc))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____2292 uu____2293 FStar_Pprint.equals)))
end
| uu____2295 -> begin
(

let uu____2296 = (

let uu____2297 = (p_tuplePattern pat)
in (

let uu____2298 = (FStar_Pprint.op_Hat_Slash_Hat ascr_doc FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____2297 uu____2298)))
in (FStar_Pprint.group uu____2296))
end)
end))
in (

let uu____2299 = (p_term e)
in (prefix2 pat_doc uu____2299)))
end))
and p_newEffect : FStar_Parser_AST.effect_decl  ->  FStar_Pprint.document = (fun uu___119_2300 -> (match (uu___119_2300) with
| FStar_Parser_AST.RedefineEffect (lid, bs, t) -> begin
(p_effectRedefinition lid bs t)
end
| FStar_Parser_AST.DefineEffect (lid, bs, t, eff_decls, action_decls) -> begin
(p_effectDefinition lid bs t eff_decls action_decls)
end))
and p_effectRedefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun uid bs t -> (

let uu____2321 = (p_uident uid)
in (

let uu____2322 = (p_binders true bs)
in (

let uu____2323 = (

let uu____2324 = (p_simpleTerm t)
in (prefix2 FStar_Pprint.equals uu____2324))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____2321 uu____2322 uu____2323)))))
and p_effectDefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun uid bs t eff_decls action_decls -> (

let uu____2333 = (

let uu____2334 = (

let uu____2335 = (

let uu____2336 = (p_uident uid)
in (

let uu____2337 = (p_binders true bs)
in (

let uu____2338 = (

let uu____2339 = (p_typ t)
in (prefix2 FStar_Pprint.colon uu____2339))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____2336 uu____2337 uu____2338))))
in (FStar_Pprint.group uu____2335))
in (

let uu____2340 = (

let uu____2341 = (

let uu____2342 = (str "with")
in (

let uu____2343 = (separate_break_map FStar_Pprint.semi p_effectDecl eff_decls)
in (prefix2 uu____2342 uu____2343)))
in (

let uu____2344 = (p_actionDecls action_decls)
in (FStar_Pprint.op_Hat_Hat uu____2341 uu____2344)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2334 uu____2340)))
in (braces_with_nesting uu____2333)))
and p_actionDecls : FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun uu___120_2345 -> (match (uu___120_2345) with
| [] -> begin
FStar_Pprint.empty
end
| l -> begin
(

let uu____2349 = (

let uu____2350 = (str "and actions")
in (

let uu____2351 = (separate_break_map FStar_Pprint.semi p_effectDecl l)
in (prefix2 uu____2350 uu____2351)))
in (FStar_Pprint.op_Hat_Hat break1 uu____2349))
end))
and p_effectDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (false, ((FStar_Parser_AST.TyconAbbrev (lid, [], None, e), None))::[]) -> begin
(

let uu____2368 = (

let uu____2369 = (p_lident lid)
in (

let uu____2370 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____2369 uu____2370)))
in (

let uu____2371 = (p_simpleTerm e)
in (prefix2 uu____2368 uu____2371)))
end
| uu____2372 -> begin
(

let uu____2373 = (

let uu____2374 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "Not a declaration of an effect member... or at least I hope so : %s" uu____2374))
in (failwith uu____2373))
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

let p_lift = (fun uu____2407 -> (match (uu____2407) with
| (kwd, t) -> begin
(

let uu____2412 = (

let uu____2413 = (str kwd)
in (

let uu____2414 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____2413 uu____2414)))
in (

let uu____2415 = (p_simpleTerm t)
in (prefix2 uu____2412 uu____2415)))
end))
in (separate_break_map FStar_Pprint.semi p_lift lifts)))
in (

let uu____2418 = (

let uu____2419 = (

let uu____2420 = (p_quident lift.FStar_Parser_AST.msource)
in (

let uu____2421 = (

let uu____2422 = (str "~>")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2422))
in (FStar_Pprint.op_Hat_Hat uu____2420 uu____2421)))
in (

let uu____2423 = (p_quident lift.FStar_Parser_AST.mdest)
in (prefix2 uu____2419 uu____2423)))
in (

let uu____2424 = (

let uu____2425 = (braces_with_nesting lift_op_doc)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2425))
in (FStar_Pprint.op_Hat_Hat uu____2418 uu____2424)))))
and p_qualifier : FStar_Parser_AST.qualifier  ->  FStar_Pprint.document = (fun uu___121_2426 -> (match (uu___121_2426) with
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

let uu____2428 = (FStar_Pprint.separate_map break1 p_qualifier qs)
in (FStar_Pprint.group uu____2428)))
and p_letqualifier : FStar_Parser_AST.let_qualifier  ->  FStar_Pprint.document = (fun uu___122_2429 -> (match (uu___122_2429) with
| FStar_Parser_AST.Rec -> begin
(

let uu____2430 = (str "rec")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2430))
end
| FStar_Parser_AST.Mutable -> begin
(

let uu____2431 = (str "mutable")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2431))
end
| FStar_Parser_AST.NoLetQualifier -> begin
FStar_Pprint.empty
end))
and p_aqual : FStar_Parser_AST.arg_qualifier  ->  FStar_Pprint.document = (fun uu___123_2432 -> (match (uu___123_2432) with
| FStar_Parser_AST.Implicit -> begin
(str "#")
end
| FStar_Parser_AST.Equality -> begin
(str "$")
end))
and p_disjunctivePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr (pats) -> begin
(

let uu____2436 = (

let uu____2437 = (

let uu____2438 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space)
in (FStar_Pprint.op_Hat_Hat break1 uu____2438))
in (FStar_Pprint.separate_map uu____2437 p_tuplePattern pats))
in (FStar_Pprint.group uu____2436))
end
| uu____2439 -> begin
(p_tuplePattern p)
end))
and p_tuplePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTuple (pats, false) -> begin
(

let uu____2444 = (

let uu____2445 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map uu____2445 p_constructorPattern pats))
in (FStar_Pprint.group uu____2444))
end
| uu____2446 -> begin
(p_constructorPattern p)
end))
and p_constructorPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (maybe_cons_lid); FStar_Parser_AST.prange = uu____2449}, (hd)::(tl)::[]) when (FStar_Ident.lid_equals maybe_cons_lid FStar_Syntax_Const.cons_lid) -> begin
(

let uu____2453 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon)
in (

let uu____2454 = (p_constructorPattern hd)
in (

let uu____2455 = (p_constructorPattern tl)
in (infix0 uu____2453 uu____2454 uu____2455))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (uid); FStar_Parser_AST.prange = uu____2457}, pats) -> begin
(

let uu____2461 = (p_quident uid)
in (

let uu____2462 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (prefix2 uu____2461 uu____2462)))
end
| uu____2463 -> begin
(p_atomicPattern p)
end))
and p_atomicPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, t) -> begin
(

let uu____2467 = (

let uu____2470 = (

let uu____2471 = (unparen t)
in uu____2471.FStar_Parser_AST.tm)
in ((pat.FStar_Parser_AST.pat), (uu____2470)))
in (match (uu____2467) with
| (FStar_Parser_AST.PatVar (lid, aqual), FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t); FStar_Parser_AST.brange = uu____2476; FStar_Parser_AST.blevel = uu____2477; FStar_Parser_AST.aqual = uu____2478}, phi)) when (lid.FStar_Ident.idText = lid'.FStar_Ident.idText) -> begin
(

let uu____2482 = (

let uu____2483 = (p_ident lid)
in (p_refinement aqual uu____2483 t phi))
in (soft_parens_with_nesting uu____2482))
end
| (FStar_Parser_AST.PatWild, FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t); FStar_Parser_AST.brange = uu____2485; FStar_Parser_AST.blevel = uu____2486; FStar_Parser_AST.aqual = uu____2487}, phi)) -> begin
(

let uu____2489 = (p_refinement None FStar_Pprint.underscore t phi)
in (soft_parens_with_nesting uu____2489))
end
| uu____2490 -> begin
(

let uu____2493 = (

let uu____2494 = (p_tuplePattern pat)
in (

let uu____2495 = (

let uu____2496 = (FStar_Pprint.break_ (Prims.parse_int "0"))
in (

let uu____2497 = (

let uu____2498 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2498))
in (FStar_Pprint.op_Hat_Hat uu____2496 uu____2497)))
in (FStar_Pprint.op_Hat_Hat uu____2494 uu____2495)))
in (soft_parens_with_nesting uu____2493))
end))
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let uu____2501 = (separate_break_map FStar_Pprint.semi p_tuplePattern pats)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket uu____2501 FStar_Pprint.rbracket))
end
| FStar_Parser_AST.PatRecord (pats) -> begin
(

let p_recordFieldPat = (fun uu____2511 -> (match (uu____2511) with
| (lid, pat) -> begin
(

let uu____2516 = (p_qlident lid)
in (

let uu____2517 = (p_tuplePattern pat)
in (infix2 FStar_Pprint.equals uu____2516 uu____2517)))
end))
in (

let uu____2518 = (separate_break_map FStar_Pprint.semi p_recordFieldPat pats)
in (soft_braces_with_nesting uu____2518)))
end
| FStar_Parser_AST.PatTuple (pats, true) -> begin
(

let uu____2524 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (

let uu____2525 = (separate_break_map FStar_Pprint.comma p_constructorPattern pats)
in (

let uu____2526 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____2524 uu____2525 uu____2526))))
end
| FStar_Parser_AST.PatTvar (tv, arg_qualifier_opt) -> begin
(p_tvar tv)
end
| FStar_Parser_AST.PatOp (op) -> begin
(

let uu____2533 = (

let uu____2534 = (

let uu____2535 = (str op)
in (

let uu____2536 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat uu____2535 uu____2536)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2534))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2533))
end
| FStar_Parser_AST.PatWild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.PatConst (c) -> begin
(p_constant c)
end
| FStar_Parser_AST.PatVar (lid, aqual) -> begin
(

let uu____2542 = (FStar_Pprint.optional p_aqual aqual)
in (

let uu____2543 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat uu____2542 uu____2543)))
end
| FStar_Parser_AST.PatName (uid) -> begin
(p_quident uid)
end
| FStar_Parser_AST.PatOr (uu____2545) -> begin
(failwith "Inner or pattern !")
end
| (FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (_); FStar_Parser_AST.prange = _}, _)) | (FStar_Parser_AST.PatTuple (_, false)) -> begin
(

let uu____2553 = (p_tuplePattern p)
in (soft_parens_with_nesting uu____2553))
end
| uu____2554 -> begin
(

let uu____2555 = (

let uu____2556 = (FStar_Parser_AST.pat_to_string p)
in (FStar_Util.format1 "Invalid pattern %s" uu____2556))
in (failwith uu____2555))
end))
and p_binder : Prims.bool  ->  FStar_Parser_AST.binder  ->  FStar_Pprint.document = (fun is_atomic b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (lid) -> begin
(

let uu____2560 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (

let uu____2561 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat uu____2560 uu____2561)))
end
| FStar_Parser_AST.TVariable (lid) -> begin
(p_lident lid)
end
| FStar_Parser_AST.Annotated (lid, t) -> begin
(

let doc = (

let uu____2566 = (

let uu____2567 = (unparen t)
in uu____2567.FStar_Parser_AST.tm)
in (match (uu____2566) with
| FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t); FStar_Parser_AST.brange = uu____2570; FStar_Parser_AST.blevel = uu____2571; FStar_Parser_AST.aqual = uu____2572}, phi) when (lid.FStar_Ident.idText = lid'.FStar_Ident.idText) -> begin
(

let uu____2574 = (p_ident lid)
in (p_refinement b.FStar_Parser_AST.aqual uu____2574 t phi))
end
| uu____2575 -> begin
(

let uu____2576 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (

let uu____2577 = (

let uu____2578 = (p_lident lid)
in (

let uu____2579 = (

let uu____2580 = (

let uu____2581 = (FStar_Pprint.break_ (Prims.parse_int "0"))
in (

let uu____2582 = (p_tmFormula t)
in (FStar_Pprint.op_Hat_Hat uu____2581 uu____2582)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2580))
in (FStar_Pprint.op_Hat_Hat uu____2578 uu____2579)))
in (FStar_Pprint.op_Hat_Hat uu____2576 uu____2577)))
end))
in (match (is_atomic) with
| true -> begin
(

let uu____2583 = (

let uu____2584 = (FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2584))
in (FStar_Pprint.group uu____2583))
end
| uu____2585 -> begin
(FStar_Pprint.group doc)
end))
end
| FStar_Parser_AST.TAnnotated (uu____2586) -> begin
(failwith "Is this still used ?")
end
| FStar_Parser_AST.NoName (t) -> begin
(

let uu____2590 = (

let uu____2591 = (unparen t)
in uu____2591.FStar_Parser_AST.tm)
in (match (uu____2590) with
| FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t); FStar_Parser_AST.brange = uu____2593; FStar_Parser_AST.blevel = uu____2594; FStar_Parser_AST.aqual = uu____2595}, phi) -> begin
(match (is_atomic) with
| true -> begin
(

let uu____2597 = (

let uu____2598 = (

let uu____2599 = (p_refinement b.FStar_Parser_AST.aqual FStar_Pprint.underscore t phi)
in (FStar_Pprint.op_Hat_Hat uu____2599 FStar_Pprint.rparen))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2598))
in (FStar_Pprint.group uu____2597))
end
| uu____2600 -> begin
(

let uu____2601 = (p_refinement b.FStar_Parser_AST.aqual FStar_Pprint.underscore t phi)
in (FStar_Pprint.group uu____2601))
end)
end
| uu____2602 -> begin
(match (is_atomic) with
| true -> begin
(p_atomicTerm t)
end
| uu____2603 -> begin
(p_appTerm t)
end)
end))
end))
and p_refinement : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Pprint.document  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun aqual_opt binder t phi -> (

let uu____2609 = (FStar_Pprint.optional p_aqual aqual_opt)
in (

let uu____2610 = (

let uu____2611 = (

let uu____2612 = (

let uu____2613 = (p_appTerm t)
in (

let uu____2614 = (

let uu____2615 = (p_noSeqTerm phi)
in (soft_braces_with_nesting uu____2615))
in (FStar_Pprint.op_Hat_Hat uu____2613 uu____2614)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2612))
in (FStar_Pprint.op_Hat_Hat binder uu____2611))
in (FStar_Pprint.op_Hat_Hat uu____2609 uu____2610))))
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
| uu____2626 -> begin
(p_lident id)
end))
and p_term : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2628 = (

let uu____2629 = (unparen e)
in uu____2629.FStar_Parser_AST.tm)
in (match (uu____2628) with
| FStar_Parser_AST.Seq (e1, e2) -> begin
(

let uu____2632 = (

let uu____2633 = (

let uu____2634 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat uu____2634 FStar_Pprint.semi))
in (FStar_Pprint.group uu____2633))
in (

let uu____2635 = (p_term e2)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2632 uu____2635)))
end
| uu____2636 -> begin
(

let uu____2637 = (p_noSeqTerm e)
in (FStar_Pprint.group uu____2637))
end)))
and p_noSeqTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_noSeqTerm' e e.FStar_Parser_AST.range))
and p_noSeqTerm' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2640 = (

let uu____2641 = (unparen e)
in uu____2641.FStar_Parser_AST.tm)
in (match (uu____2640) with
| FStar_Parser_AST.Ascribed (e, t) -> begin
(

let uu____2644 = (

let uu____2645 = (p_tmIff e)
in (

let uu____2646 = (

let uu____2647 = (

let uu____2648 = (p_typ t)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____2648))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____2647))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2645 uu____2646)))
in (FStar_Pprint.group uu____2644))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::(e3)::[]) when (op = ".()<-") -> begin
(

let uu____2654 = (

let uu____2655 = (

let uu____2656 = (

let uu____2657 = (p_atomicTermNotQUident e1)
in (

let uu____2658 = (

let uu____2659 = (

let uu____2660 = (

let uu____2661 = (p_term e2)
in (soft_parens_with_nesting uu____2661))
in (

let uu____2662 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat uu____2660 uu____2662)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____2659))
in (FStar_Pprint.op_Hat_Hat uu____2657 uu____2658)))
in (FStar_Pprint.group uu____2656))
in (

let uu____2663 = (

let uu____2664 = (p_noSeqTerm e3)
in (jump2 uu____2664))
in (FStar_Pprint.op_Hat_Hat uu____2655 uu____2663)))
in (FStar_Pprint.group uu____2654))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::(e3)::[]) when (op = ".[]<-") -> begin
(

let uu____2670 = (

let uu____2671 = (

let uu____2672 = (

let uu____2673 = (p_atomicTermNotQUident e1)
in (

let uu____2674 = (

let uu____2675 = (

let uu____2676 = (

let uu____2677 = (p_term e2)
in (soft_brackets_with_nesting uu____2677))
in (

let uu____2678 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat uu____2676 uu____2678)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____2675))
in (FStar_Pprint.op_Hat_Hat uu____2673 uu____2674)))
in (FStar_Pprint.group uu____2672))
in (

let uu____2679 = (

let uu____2680 = (p_noSeqTerm e3)
in (jump2 uu____2680))
in (FStar_Pprint.op_Hat_Hat uu____2671 uu____2679)))
in (FStar_Pprint.group uu____2670))
end
| FStar_Parser_AST.Requires (e, wtf) -> begin
(

let uu____2686 = (

let uu____2687 = (str "requires")
in (

let uu____2688 = (p_typ e)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2687 uu____2688)))
in (FStar_Pprint.group uu____2686))
end
| FStar_Parser_AST.Ensures (e, wtf) -> begin
(

let uu____2694 = (

let uu____2695 = (str "ensures")
in (

let uu____2696 = (p_typ e)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2695 uu____2696)))
in (FStar_Pprint.group uu____2694))
end
| FStar_Parser_AST.Attributes (es) -> begin
(

let uu____2699 = (

let uu____2700 = (str "attributes")
in (

let uu____2701 = (FStar_Pprint.separate_map break1 p_atomicTerm es)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2700 uu____2701)))
in (FStar_Pprint.group uu____2699))
end
| FStar_Parser_AST.If (e1, e2, e3) -> begin
(

let uu____2705 = (is_unit e3)
in (match (uu____2705) with
| true -> begin
(

let uu____2706 = (

let uu____2707 = (

let uu____2708 = (str "if")
in (

let uu____2709 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat uu____2708 uu____2709)))
in (

let uu____2710 = (

let uu____2711 = (str "then")
in (

let uu____2712 = (p_noSeqTerm e2)
in (op_Hat_Slash_Plus_Hat uu____2711 uu____2712)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2707 uu____2710)))
in (FStar_Pprint.group uu____2706))
end
| uu____2713 -> begin
(

let e2_doc = (

let uu____2715 = (

let uu____2716 = (unparen e2)
in uu____2716.FStar_Parser_AST.tm)
in (match (uu____2715) with
| FStar_Parser_AST.If (uu____2717, uu____2718, e3) when (is_unit e3) -> begin
(

let uu____2720 = (p_noSeqTerm e2)
in (soft_parens_with_nesting uu____2720))
end
| uu____2721 -> begin
(p_noSeqTerm e2)
end))
in (

let uu____2722 = (

let uu____2723 = (

let uu____2724 = (str "if")
in (

let uu____2725 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat uu____2724 uu____2725)))
in (

let uu____2726 = (

let uu____2727 = (

let uu____2728 = (str "then")
in (op_Hat_Slash_Plus_Hat uu____2728 e2_doc))
in (

let uu____2729 = (

let uu____2730 = (str "else")
in (

let uu____2731 = (p_noSeqTerm e3)
in (op_Hat_Slash_Plus_Hat uu____2730 uu____2731)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2727 uu____2729)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2723 uu____2726)))
in (FStar_Pprint.group uu____2722)))
end))
end
| FStar_Parser_AST.TryWith (e, branches) -> begin
(

let uu____2744 = (

let uu____2745 = (

let uu____2746 = (str "try")
in (

let uu____2747 = (p_noSeqTerm e)
in (prefix2 uu____2746 uu____2747)))
in (

let uu____2748 = (

let uu____2749 = (str "with")
in (

let uu____2750 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2749 uu____2750)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2745 uu____2748)))
in (FStar_Pprint.group uu____2744))
end
| FStar_Parser_AST.Match (e, branches) -> begin
(

let uu____2767 = (

let uu____2768 = (

let uu____2769 = (str "match")
in (

let uu____2770 = (p_noSeqTerm e)
in (

let uu____2771 = (str "with")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____2769 uu____2770 uu____2771))))
in (

let uu____2772 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2768 uu____2772)))
in (FStar_Pprint.group uu____2767))
end
| FStar_Parser_AST.LetOpen (uid, e) -> begin
(

let uu____2779 = (

let uu____2780 = (

let uu____2781 = (str "let open")
in (

let uu____2782 = (p_quident uid)
in (

let uu____2783 = (str "in")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____2781 uu____2782 uu____2783))))
in (

let uu____2784 = (p_term e)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2780 uu____2784)))
in (FStar_Pprint.group uu____2779))
end
| FStar_Parser_AST.Let (q, lbs, e) -> begin
(

let let_doc = (

let uu____2795 = (str "let")
in (

let uu____2796 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat uu____2795 uu____2796)))
in (

let uu____2797 = (

let uu____2798 = (

let uu____2799 = (

let uu____2800 = (str "and")
in (precede_break_separate_map let_doc uu____2800 p_letbinding lbs))
in (

let uu____2803 = (str "in")
in (FStar_Pprint.op_Hat_Slash_Hat uu____2799 uu____2803)))
in (FStar_Pprint.group uu____2798))
in (

let uu____2804 = (p_term e)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2797 uu____2804))))
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, typ_opt); FStar_Parser_AST.prange = uu____2807})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, branches); FStar_Parser_AST.range = uu____2810; FStar_Parser_AST.level = uu____2811}) when (matches_var maybe_x x) -> begin
(

let uu____2825 = (

let uu____2826 = (str "function")
in (

let uu____2827 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2826 uu____2827)))
in (FStar_Pprint.group uu____2825))
end
| FStar_Parser_AST.Assign (id, e) -> begin
(

let uu____2834 = (

let uu____2835 = (p_lident id)
in (

let uu____2836 = (

let uu____2837 = (p_noSeqTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow uu____2837))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2835 uu____2836)))
in (FStar_Pprint.group uu____2834))
end
| uu____2838 -> begin
(p_typ e)
end)))
and p_typ : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_typ' e e.FStar_Parser_AST.range))
and p_typ' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2841 = (

let uu____2842 = (unparen e)
in uu____2842.FStar_Parser_AST.tm)
in (match (uu____2841) with
| (FStar_Parser_AST.QForall (bs, trigger, e1)) | (FStar_Parser_AST.QExists (bs, trigger, e1)) -> begin
(

let uu____2858 = (

let uu____2859 = (

let uu____2860 = (p_quantifier e)
in (FStar_Pprint.op_Hat_Hat uu____2860 FStar_Pprint.space))
in (

let uu____2861 = (p_binders true bs)
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") uu____2859 uu____2861 FStar_Pprint.dot)))
in (

let uu____2862 = (

let uu____2863 = (p_trigger trigger)
in (

let uu____2864 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat uu____2863 uu____2864)))
in (prefix2 uu____2858 uu____2862)))
end
| uu____2865 -> begin
(p_simpleTerm e)
end)))
and p_quantifier : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2867 = (

let uu____2868 = (unparen e)
in uu____2868.FStar_Parser_AST.tm)
in (match (uu____2867) with
| FStar_Parser_AST.QForall (uu____2869) -> begin
(str "forall")
end
| FStar_Parser_AST.QExists (uu____2876) -> begin
(str "exists")
end
| uu____2883 -> begin
(failwith "Imposible : p_quantifier called on a non-quantifier term")
end)))
and p_trigger : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun uu___124_2884 -> (match (uu___124_2884) with
| [] -> begin
FStar_Pprint.empty
end
| pats -> begin
(

let uu____2891 = (

let uu____2892 = (

let uu____2893 = (str "pattern")
in (

let uu____2894 = (

let uu____2895 = (

let uu____2896 = (p_disjunctivePats pats)
in (jump2 uu____2896))
in (

let uu____2897 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2895 uu____2897)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2893 uu____2894)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2892))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____2891))
end))
and p_disjunctivePats : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun pats -> (

let uu____2901 = (str "\\/")
in (FStar_Pprint.separate_map uu____2901 p_conjunctivePats pats)))
and p_conjunctivePats : FStar_Parser_AST.term Prims.list  ->  FStar_Pprint.document = (fun pats -> (

let uu____2905 = (FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats)
in (FStar_Pprint.group uu____2905)))
and p_simpleTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2907 = (

let uu____2908 = (unparen e)
in uu____2908.FStar_Parser_AST.tm)
in (match (uu____2907) with
| FStar_Parser_AST.Abs (pats, e) -> begin
(

let uu____2913 = (

let uu____2914 = (str "fun")
in (

let uu____2915 = (

let uu____2916 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2916 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat uu____2914 uu____2915)))
in (

let uu____2917 = (p_term e)
in (op_Hat_Slash_Plus_Hat uu____2913 uu____2917)))
end
| uu____2918 -> begin
(p_tmIff e)
end)))
and p_maybeFocusArrow : Prims.bool  ->  FStar_Pprint.document = (fun b -> (match (b) with
| true -> begin
(str "~>")
end
| uu____2920 -> begin
FStar_Pprint.rarrow
end))
and p_patternBranch : (FStar_Parser_AST.pattern * FStar_Parser_AST.term Prims.option * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun uu____2921 -> (match (uu____2921) with
| (pat, when_opt, e) -> begin
(

let maybe_paren = (

let uu____2934 = (

let uu____2935 = (unparen e)
in uu____2935.FStar_Parser_AST.tm)
in (match (uu____2934) with
| (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) -> begin
soft_begin_end_with_nesting
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____2941); FStar_Parser_AST.prange = uu____2942})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, uu____2944); FStar_Parser_AST.range = uu____2945; FStar_Parser_AST.level = uu____2946}) when (matches_var maybe_x x) -> begin
soft_begin_end_with_nesting
end
| uu____2960 -> begin
(fun x -> x)
end))
in (

let uu____2962 = (

let uu____2963 = (

let uu____2964 = (

let uu____2965 = (

let uu____2966 = (

let uu____2967 = (p_disjunctivePattern pat)
in (

let uu____2968 = (

let uu____2969 = (p_maybeWhen when_opt)
in (FStar_Pprint.op_Hat_Hat uu____2969 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat uu____2967 uu____2968)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2966))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____2965))
in (FStar_Pprint.group uu____2964))
in (

let uu____2970 = (

let uu____2971 = (p_term e)
in (maybe_paren uu____2971))
in (op_Hat_Slash_Plus_Hat uu____2963 uu____2970)))
in (FStar_Pprint.group uu____2962)))
end))
and p_maybeWhen : FStar_Parser_AST.term Prims.option  ->  FStar_Pprint.document = (fun uu___125_2972 -> (match (uu___125_2972) with
| None -> begin
FStar_Pprint.empty
end
| Some (e) -> begin
(

let uu____2975 = (str "when")
in (

let uu____2976 = (

let uu____2977 = (p_tmFormula e)
in (FStar_Pprint.op_Hat_Hat uu____2977 FStar_Pprint.space))
in (op_Hat_Slash_Plus_Hat uu____2975 uu____2976)))
end))
and p_tmIff : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2979 = (

let uu____2980 = (unparen e)
in uu____2980.FStar_Parser_AST.tm)
in (match (uu____2979) with
| FStar_Parser_AST.Op ("<==>", (e1)::(e2)::[]) -> begin
(

let uu____2984 = (str "<==>")
in (

let uu____2985 = (p_tmImplies e1)
in (

let uu____2986 = (p_tmIff e2)
in (infix0 uu____2984 uu____2985 uu____2986))))
end
| uu____2987 -> begin
(p_tmImplies e)
end)))
and p_tmImplies : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2989 = (

let uu____2990 = (unparen e)
in uu____2990.FStar_Parser_AST.tm)
in (match (uu____2989) with
| FStar_Parser_AST.Op ("==>", (e1)::(e2)::[]) -> begin
(

let uu____2994 = (str "==>")
in (

let uu____2995 = (p_tmArrow p_tmFormula e1)
in (

let uu____2996 = (p_tmImplies e2)
in (infix0 uu____2994 uu____2995 uu____2996))))
end
| uu____2997 -> begin
(p_tmArrow p_tmFormula e)
end)))
and p_tmArrow : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_Tm e -> (

let uu____3002 = (

let uu____3003 = (unparen e)
in uu____3003.FStar_Parser_AST.tm)
in (match (uu____3002) with
| FStar_Parser_AST.Product (bs, tgt) -> begin
(

let uu____3008 = (

let uu____3009 = (FStar_Pprint.concat_map (fun b -> (

let uu____3011 = (p_binder false b)
in (

let uu____3012 = (

let uu____3013 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3013))
in (FStar_Pprint.op_Hat_Hat uu____3011 uu____3012)))) bs)
in (

let uu____3014 = (p_tmArrow p_Tm tgt)
in (FStar_Pprint.op_Hat_Hat uu____3009 uu____3014)))
in (FStar_Pprint.group uu____3008))
end
| uu____3015 -> begin
(p_Tm e)
end)))
and p_tmFormula : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3017 = (

let uu____3018 = (unparen e)
in uu____3018.FStar_Parser_AST.tm)
in (match (uu____3017) with
| FStar_Parser_AST.Op ("\\/", (e1)::(e2)::[]) -> begin
(

let uu____3022 = (str "\\/")
in (

let uu____3023 = (p_tmFormula e1)
in (

let uu____3024 = (p_tmConjunction e2)
in (infix0 uu____3022 uu____3023 uu____3024))))
end
| uu____3025 -> begin
(p_tmConjunction e)
end)))
and p_tmConjunction : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3027 = (

let uu____3028 = (unparen e)
in uu____3028.FStar_Parser_AST.tm)
in (match (uu____3027) with
| FStar_Parser_AST.Op ("/\\", (e1)::(e2)::[]) -> begin
(

let uu____3032 = (str "/\\")
in (

let uu____3033 = (p_tmConjunction e1)
in (

let uu____3034 = (p_tmTuple e2)
in (infix0 uu____3032 uu____3033 uu____3034))))
end
| uu____3035 -> begin
(p_tmTuple e)
end)))
and p_tmTuple : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_tmTuple' e e.FStar_Parser_AST.range))
and p_tmTuple' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3038 = (

let uu____3039 = (unparen e)
in uu____3039.FStar_Parser_AST.tm)
in (match (uu____3038) with
| FStar_Parser_AST.Construct (lid, args) when (is_tuple_constructor lid) -> begin
(

let uu____3048 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map uu____3048 (fun uu____3051 -> (match (uu____3051) with
| (e, uu____3055) -> begin
(p_tmEq e)
end)) args))
end
| uu____3056 -> begin
(p_tmEq e)
end)))
and paren_if : Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun curr mine doc -> (match ((mine <= curr)) with
| true -> begin
doc
end
| uu____3060 -> begin
(

let uu____3061 = (

let uu____3062 = (FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3062))
in (FStar_Pprint.group uu____3061))
end))
and p_tmEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n = (max_level (FStar_List.append (((colon_equals ()))::((pipe_right ()))::[]) (operatorInfix0ad12 ())))
in (p_tmEq' n e)))
and p_tmEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (

let uu____3087 = (

let uu____3088 = (unparen e)
in uu____3088.FStar_Parser_AST.tm)
in (match (uu____3087) with
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (((is_operatorInfix0ad12 op) || (op = "=")) || (op = "|>")) -> begin
(

let uu____3093 = (levels op)
in (match (uu____3093) with
| (left, mine, right) -> begin
(

let uu____3100 = (

let uu____3101 = (str op)
in (

let uu____3102 = (p_tmEq' left e1)
in (

let uu____3103 = (p_tmEq' right e2)
in (infix0 uu____3101 uu____3102 uu____3103))))
in (paren_if curr mine uu____3100))
end))
end
| FStar_Parser_AST.Op (":=", (e1)::(e2)::[]) -> begin
(

let uu____3107 = (

let uu____3108 = (p_tmEq e1)
in (

let uu____3109 = (

let uu____3110 = (

let uu____3111 = (

let uu____3112 = (p_tmEq e2)
in (op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____3112))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3111))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3110))
in (FStar_Pprint.op_Hat_Hat uu____3108 uu____3109)))
in (FStar_Pprint.group uu____3107))
end
| uu____3113 -> begin
(p_tmNoEq e)
end)))
and p_tmNoEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n = (max_level (((colon_colon ()))::((amp ()))::((opinfix3 ()))::((opinfix4 ()))::[]))
in (p_tmNoEq' n e)))
and p_tmNoEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (

let uu____3143 = (

let uu____3144 = (unparen e)
in uu____3144.FStar_Parser_AST.tm)
in (match (uu____3143) with
| FStar_Parser_AST.Construct (lid, ((e1, uu____3147))::((e2, uu____3149))::[]) when ((FStar_Ident.lid_equals lid FStar_Syntax_Const.cons_lid) && (

let uu____3159 = (is_list e)
in (not (uu____3159)))) -> begin
(

let op = "::"
in (

let uu____3161 = (levels op)
in (match (uu____3161) with
| (left, mine, right) -> begin
(

let uu____3168 = (

let uu____3169 = (str op)
in (

let uu____3170 = (p_tmNoEq' left e1)
in (

let uu____3171 = (p_tmNoEq' right e2)
in (infix0 uu____3169 uu____3170 uu____3171))))
in (paren_if curr mine uu____3168))
end)))
end
| FStar_Parser_AST.Sum (binders, res) -> begin
(

let op = "&"
in (

let uu____3177 = (levels op)
in (match (uu____3177) with
| (left, mine, right) -> begin
(

let p_dsumfst = (fun b -> (

let uu____3188 = (p_binder false b)
in (

let uu____3189 = (

let uu____3190 = (

let uu____3191 = (str "&")
in (FStar_Pprint.op_Hat_Hat uu____3191 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3190))
in (FStar_Pprint.op_Hat_Hat uu____3188 uu____3189))))
in (

let uu____3192 = (

let uu____3193 = (FStar_Pprint.concat_map p_dsumfst binders)
in (

let uu____3194 = (p_tmNoEq' right res)
in (FStar_Pprint.op_Hat_Hat uu____3193 uu____3194)))
in (paren_if curr mine uu____3192)))
end)))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (is_operatorInfix34 op) -> begin
(

let uu____3199 = (levels op)
in (match (uu____3199) with
| (left, mine, right) -> begin
(

let uu____3206 = (

let uu____3207 = (str op)
in (

let uu____3208 = (p_tmNoEq' left e1)
in (

let uu____3209 = (p_tmNoEq' right e2)
in (infix0 uu____3207 uu____3208 uu____3209))))
in (paren_if curr mine uu____3206))
end))
end
| FStar_Parser_AST.Op ("-", (e)::[]) -> begin
(

let uu____3212 = (levels "-")
in (match (uu____3212) with
| (left, mine, right) -> begin
(

let uu____3219 = (p_tmNoEq' mine e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____3219))
end))
end
| FStar_Parser_AST.NamedTyp (lid, e) -> begin
(

let uu____3222 = (

let uu____3223 = (p_lidentOrUnderscore lid)
in (

let uu____3224 = (

let uu____3225 = (p_appTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____3225))
in (FStar_Pprint.op_Hat_Slash_Hat uu____3223 uu____3224)))
in (FStar_Pprint.group uu____3222))
end
| FStar_Parser_AST.Refine (b, phi) -> begin
(p_refinedBinder b phi)
end
| FStar_Parser_AST.Record (with_opt, record_fields) -> begin
(

let uu____3238 = (

let uu____3239 = (default_or_map FStar_Pprint.empty p_with_clause with_opt)
in (

let uu____3240 = (

let uu____3241 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (FStar_Pprint.separate_map uu____3241 p_simpleDef record_fields))
in (FStar_Pprint.op_Hat_Hat uu____3239 uu____3240)))
in (braces_with_nesting uu____3238))
end
| FStar_Parser_AST.Op ("~", (e)::[]) -> begin
(

let uu____3246 = (

let uu____3247 = (str "~")
in (

let uu____3248 = (p_atomicTerm e)
in (FStar_Pprint.op_Hat_Hat uu____3247 uu____3248)))
in (FStar_Pprint.group uu____3246))
end
| uu____3249 -> begin
(p_appTerm e)
end)))
and p_with_clause : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3251 = (p_appTerm e)
in (

let uu____3252 = (

let uu____3253 = (

let uu____3254 = (str "with")
in (FStar_Pprint.op_Hat_Hat uu____3254 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3253))
in (FStar_Pprint.op_Hat_Hat uu____3251 uu____3252))))
and p_refinedBinder : FStar_Parser_AST.binder  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun b phi -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (lid, t) -> begin
(

let uu____3259 = (

let uu____3260 = (p_lident lid)
in (p_refinement b.FStar_Parser_AST.aqual uu____3260 t phi))
in (soft_parens_with_nesting uu____3259))
end
| FStar_Parser_AST.TAnnotated (uu____3261) -> begin
(failwith "Is this still used ?")
end
| (FStar_Parser_AST.Variable (_)) | (FStar_Parser_AST.TVariable (_)) | (FStar_Parser_AST.NoName (_)) -> begin
(

let uu____3267 = (

let uu____3268 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" uu____3268))
in (failwith uu____3267))
end))
and p_simpleDef : (FStar_Ident.lid * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun uu____3269 -> (match (uu____3269) with
| (lid, e) -> begin
(

let uu____3274 = (

let uu____3275 = (p_qlident lid)
in (

let uu____3276 = (

let uu____3277 = (p_tmIff e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____3277))
in (FStar_Pprint.op_Hat_Slash_Hat uu____3275 uu____3276)))
in (FStar_Pprint.group uu____3274))
end))
and p_appTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3279 = (

let uu____3280 = (unparen e)
in uu____3280.FStar_Parser_AST.tm)
in (match (uu____3279) with
| FStar_Parser_AST.App (uu____3281) when (is_general_application e) -> begin
(

let uu____3285 = (head_and_args e)
in (match (uu____3285) with
| (head, args) -> begin
(

let uu____3299 = (

let uu____3305 = (FStar_ST.read should_print_fs_typ_app)
in (match (uu____3305) with
| true -> begin
(

let uu____3313 = (FStar_Util.take (fun uu____3324 -> (match (uu____3324) with
| (uu____3327, aq) -> begin
(aq = FStar_Parser_AST.FsTypApp)
end)) args)
in (match (uu____3313) with
| (fs_typ_args, args) -> begin
(

let uu____3348 = (

let uu____3349 = (p_indexingTerm head)
in (

let uu____3350 = (

let uu____3351 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (soft_surround_separate_map (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.empty FStar_Pprint.langle uu____3351 FStar_Pprint.rangle p_fsTypArg fs_typ_args))
in (FStar_Pprint.op_Hat_Hat uu____3349 uu____3350)))
in ((uu____3348), (args)))
end))
end
| uu____3357 -> begin
(

let uu____3358 = (p_indexingTerm head)
in ((uu____3358), (args)))
end))
in (match (uu____3299) with
| (head_doc, args) -> begin
(

let uu____3370 = (

let uu____3371 = (FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space)
in (soft_surround_separate_map (Prims.parse_int "2") (Prims.parse_int "0") head_doc uu____3371 break1 FStar_Pprint.empty p_argTerm args))
in (FStar_Pprint.group uu____3370))
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

let uu____3391 = (

let uu____3392 = (p_quident lid)
in (

let uu____3393 = (p_argTerm arg)
in (FStar_Pprint.op_Hat_Slash_Hat uu____3392 uu____3393)))
in (FStar_Pprint.group uu____3391))
end
| (hd)::tl -> begin
(

let uu____3403 = (

let uu____3404 = (

let uu____3405 = (

let uu____3406 = (p_quident lid)
in (

let uu____3407 = (p_argTerm hd)
in (prefix2 uu____3406 uu____3407)))
in (FStar_Pprint.group uu____3405))
in (

let uu____3408 = (

let uu____3409 = (FStar_Pprint.separate_map break1 p_argTerm tl)
in (jump2 uu____3409))
in (FStar_Pprint.op_Hat_Hat uu____3404 uu____3408)))
in (FStar_Pprint.group uu____3403))
end)
end
| uu____3412 -> begin
(p_indexingTerm e)
end)))
and p_argTerm : (FStar_Parser_AST.term * FStar_Parser_AST.imp)  ->  FStar_Pprint.document = (fun arg_imp -> (match (arg_imp) with
| ({FStar_Parser_AST.tm = FStar_Parser_AST.Uvar (uu____3416); FStar_Parser_AST.range = uu____3417; FStar_Parser_AST.level = uu____3418}, FStar_Parser_AST.UnivApp) -> begin
(p_univar (Prims.fst arg_imp))
end
| (u, FStar_Parser_AST.UnivApp) -> begin
(p_universe u)
end
| (e, FStar_Parser_AST.FsTypApp) -> begin
((FStar_Util.print_warning "Unexpected FsTypApp, output might not be formatted correctly.\n");
(

let uu____3422 = (p_indexingTerm e)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.langle uu____3422 FStar_Pprint.rangle));
)
end
| (e, FStar_Parser_AST.Hash) -> begin
(

let uu____3424 = (str "#")
in (

let uu____3425 = (p_indexingTerm e)
in (FStar_Pprint.op_Hat_Hat uu____3424 uu____3425)))
end
| (e, FStar_Parser_AST.Nothing) -> begin
(p_indexingTerm e)
end))
and p_fsTypArg : (FStar_Parser_AST.term * FStar_Parser_AST.imp)  ->  FStar_Pprint.document = (fun uu____3427 -> (match (uu____3427) with
| (e, uu____3431) -> begin
(p_indexingTerm e)
end))
and p_indexingTerm_aux : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun exit e -> (

let uu____3436 = (

let uu____3437 = (unparen e)
in uu____3437.FStar_Parser_AST.tm)
in (match (uu____3436) with
| FStar_Parser_AST.Op (".()", (e1)::(e2)::[]) -> begin
(

let uu____3441 = (

let uu____3442 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (

let uu____3443 = (

let uu____3444 = (

let uu____3445 = (p_term e2)
in (soft_parens_with_nesting uu____3445))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3444))
in (FStar_Pprint.op_Hat_Hat uu____3442 uu____3443)))
in (FStar_Pprint.group uu____3441))
end
| FStar_Parser_AST.Op (".[]", (e1)::(e2)::[]) -> begin
(

let uu____3449 = (

let uu____3450 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (

let uu____3451 = (

let uu____3452 = (

let uu____3453 = (p_term e2)
in (soft_brackets_with_nesting uu____3453))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3452))
in (FStar_Pprint.op_Hat_Hat uu____3450 uu____3451)))
in (FStar_Pprint.group uu____3449))
end
| uu____3454 -> begin
(exit e)
end)))
and p_indexingTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_indexingTerm_aux p_atomicTerm e))
and p_atomicTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3457 = (

let uu____3458 = (unparen e)
in uu____3458.FStar_Parser_AST.tm)
in (match (uu____3457) with
| FStar_Parser_AST.LetOpen (lid, e) -> begin
(

let uu____3461 = (p_quident lid)
in (

let uu____3462 = (

let uu____3463 = (

let uu____3464 = (p_term e)
in (soft_parens_with_nesting uu____3464))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3463))
in (FStar_Pprint.op_Hat_Hat uu____3461 uu____3462)))
end
| FStar_Parser_AST.Name (lid) -> begin
(p_quident lid)
end
| FStar_Parser_AST.Op (op, (e)::[]) when (is_general_prefix_op op) -> begin
(

let uu____3469 = (str op)
in (

let uu____3470 = (p_atomicTerm e)
in (FStar_Pprint.op_Hat_Hat uu____3469 uu____3470)))
end
| uu____3471 -> begin
(p_atomicTermNotQUident e)
end)))
and p_atomicTermNotQUident : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3473 = (

let uu____3474 = (unparen e)
in uu____3474.FStar_Parser_AST.tm)
in (match (uu____3473) with
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

let uu____3483 = (str op)
in (

let uu____3484 = (p_atomicTermNotQUident e)
in (FStar_Pprint.op_Hat_Hat uu____3483 uu____3484)))
end
| FStar_Parser_AST.Op (op, []) -> begin
(

let uu____3487 = (

let uu____3488 = (

let uu____3489 = (str op)
in (

let uu____3490 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat uu____3489 uu____3490)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3488))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3487))
end
| FStar_Parser_AST.Construct (lid, args) when (is_dtuple_constructor lid) -> begin
(

let uu____3499 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (

let uu____3500 = (

let uu____3501 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (

let uu____3502 = (FStar_List.map Prims.fst args)
in (FStar_Pprint.separate_map uu____3501 p_tmEq uu____3502)))
in (

let uu____3506 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____3499 uu____3500 uu____3506))))
end
| FStar_Parser_AST.Project (e, lid) -> begin
(

let uu____3509 = (

let uu____3510 = (p_atomicTermNotQUident e)
in (

let uu____3511 = (

let uu____3512 = (p_qlident lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3512))
in (FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0") uu____3510 uu____3511)))
in (FStar_Pprint.group uu____3509))
end
| uu____3513 -> begin
(p_projectionLHS e)
end)))
and p_projectionLHS : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3515 = (

let uu____3516 = (unparen e)
in uu____3516.FStar_Parser_AST.tm)
in (match (uu____3515) with
| FStar_Parser_AST.Var (lid) -> begin
(p_qlident lid)
end
| FStar_Parser_AST.Projector (constr_lid, field_lid) -> begin
(

let uu____3520 = (p_quident constr_lid)
in (

let uu____3521 = (

let uu____3522 = (

let uu____3523 = (p_lident field_lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3523))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____3522))
in (FStar_Pprint.op_Hat_Hat uu____3520 uu____3521)))
end
| FStar_Parser_AST.Discrim (constr_lid) -> begin
(

let uu____3525 = (p_quident constr_lid)
in (FStar_Pprint.op_Hat_Hat uu____3525 FStar_Pprint.qmark))
end
| FStar_Parser_AST.Paren (e) -> begin
(

let uu____3527 = (p_term e)
in (soft_parens_with_nesting uu____3527))
end
| uu____3528 when (is_array e) -> begin
(

let es = (extract_from_list e)
in (

let uu____3531 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar)
in (

let uu____3532 = (

let uu____3533 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (separate_map_or_flow uu____3533 p_noSeqTerm es))
in (

let uu____3534 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") uu____3531 uu____3532 uu____3534)))))
end
| uu____3535 when (is_list e) -> begin
(

let uu____3536 = (

let uu____3537 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (

let uu____3538 = (extract_from_list e)
in (separate_map_or_flow uu____3537 p_noSeqTerm uu____3538)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket uu____3536 FStar_Pprint.rbracket))
end
| uu____3540 when (is_lex_list e) -> begin
(

let uu____3541 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket)
in (

let uu____3542 = (

let uu____3543 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (

let uu____3544 = (extract_from_list e)
in (separate_map_or_flow uu____3543 p_noSeqTerm uu____3544)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____3541 uu____3542 FStar_Pprint.rbracket)))
end
| uu____3546 when (is_ref_set e) -> begin
(

let es = (extract_from_ref_set e)
in (

let uu____3549 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace)
in (

let uu____3550 = (

let uu____3551 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (separate_map_or_flow uu____3551 p_appTerm es))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") uu____3549 uu____3550 FStar_Pprint.rbrace))))
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Op (_)) | (FStar_Parser_AST.Tvar (_)) | (FStar_Parser_AST.Uvar (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) | (FStar_Parser_AST.Construct (_)) | (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.App (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.LetOpen (_)) | (FStar_Parser_AST.Seq (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Ascribed (_)) | (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Project (_)) | (FStar_Parser_AST.Product (_)) | (FStar_Parser_AST.Sum (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Refine (_)) | (FStar_Parser_AST.NamedTyp (_)) | (FStar_Parser_AST.Requires (_)) | (FStar_Parser_AST.Ensures (_)) | (FStar_Parser_AST.Assign (_)) | (FStar_Parser_AST.Attributes (_)) -> begin
(

let uu____3580 = (p_term e)
in (soft_parens_with_nesting uu____3580))
end
| FStar_Parser_AST.Labeled (uu____3581) -> begin
(failwith "Not valid in universe")
end)))
and p_constant : FStar_Const.sconst  ->  FStar_Pprint.document = (fun uu___128_3585 -> (match (uu___128_3585) with
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

let uu____3589 = (FStar_Pprint.doc_of_char x)
in (FStar_Pprint.squotes uu____3589))
end
| FStar_Const.Const_string (bytes, uu____3591) -> begin
(

let uu____3594 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes uu____3594))
end
| FStar_Const.Const_bytearray (bytes, uu____3596) -> begin
(

let uu____3599 = (

let uu____3600 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes uu____3600))
in (

let uu____3601 = (str "B")
in (FStar_Pprint.op_Hat_Hat uu____3599 uu____3601)))
end
| FStar_Const.Const_int (repr, sign_width_opt) -> begin
(

let signedness = (fun uu___126_3613 -> (match (uu___126_3613) with
| FStar_Const.Unsigned -> begin
(str "u")
end
| FStar_Const.Signed -> begin
FStar_Pprint.empty
end))
in (

let width = (fun uu___127_3617 -> (match (uu___127_3617) with
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

let ending = (default_or_map FStar_Pprint.empty (fun uu____3621 -> (match (uu____3621) with
| (s, w) -> begin
(

let uu____3626 = (signedness s)
in (

let uu____3627 = (width w)
in (FStar_Pprint.op_Hat_Hat uu____3626 uu____3627)))
end)) sign_width_opt)
in (

let uu____3628 = (str repr)
in (FStar_Pprint.op_Hat_Hat uu____3628 ending)))))
end
| FStar_Const.Const_range (r) -> begin
(

let uu____3630 = (FStar_Range.string_of_range r)
in (str uu____3630))
end
| FStar_Const.Const_reify -> begin
(str "reify")
end
| FStar_Const.Const_reflect (lid) -> begin
(

let uu____3632 = (p_quident lid)
in (

let uu____3633 = (

let uu____3634 = (

let uu____3635 = (str "reflect")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3635))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____3634))
in (FStar_Pprint.op_Hat_Hat uu____3632 uu____3633)))
end))
and p_universe : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (

let uu____3637 = (str "u#")
in (

let uu____3638 = (p_atomicUniverse u)
in (FStar_Pprint.op_Hat_Hat uu____3637 uu____3638))))
and p_universeFrom : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (

let uu____3640 = (

let uu____3641 = (unparen u)
in uu____3641.FStar_Parser_AST.tm)
in (match (uu____3640) with
| FStar_Parser_AST.Op ("+", (u1)::(u2)::[]) -> begin
(

let uu____3645 = (

let uu____3646 = (p_universeFrom u1)
in (

let uu____3647 = (

let uu____3648 = (p_universeFrom u2)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____3648))
in (FStar_Pprint.op_Hat_Slash_Hat uu____3646 uu____3647)))
in (FStar_Pprint.group uu____3645))
end
| FStar_Parser_AST.App (uu____3649) -> begin
(

let uu____3653 = (head_and_args u)
in (match (uu____3653) with
| (head, args) -> begin
(

let uu____3667 = (

let uu____3668 = (unparen head)
in uu____3668.FStar_Parser_AST.tm)
in (match (uu____3667) with
| FStar_Parser_AST.Var (maybe_max_lid) when (FStar_Ident.lid_equals maybe_max_lid FStar_Syntax_Const.max_lid) -> begin
(

let uu____3670 = (

let uu____3671 = (p_qlident FStar_Syntax_Const.max_lid)
in (

let uu____3672 = (FStar_Pprint.separate_map FStar_Pprint.space (fun uu____3675 -> (match (uu____3675) with
| (u, uu____3679) -> begin
(p_atomicUniverse u)
end)) args)
in (op_Hat_Slash_Plus_Hat uu____3671 uu____3672)))
in (FStar_Pprint.group uu____3670))
end
| uu____3680 -> begin
(

let uu____3681 = (

let uu____3682 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" uu____3682))
in (failwith uu____3681))
end))
end))
end
| uu____3683 -> begin
(p_atomicUniverse u)
end)))
and p_atomicUniverse : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (

let uu____3685 = (

let uu____3686 = (unparen u)
in uu____3686.FStar_Parser_AST.tm)
in (match (uu____3685) with
| FStar_Parser_AST.Wild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (r, sw)) -> begin
(p_constant (FStar_Const.Const_int (((r), (sw)))))
end
| FStar_Parser_AST.Uvar (uu____3698) -> begin
(p_univar u)
end
| FStar_Parser_AST.Paren (u) -> begin
(

let uu____3700 = (p_universeFrom u)
in (soft_parens_with_nesting uu____3700))
end
| (FStar_Parser_AST.Op ("+", (_)::(_)::[])) | (FStar_Parser_AST.App (_)) -> begin
(

let uu____3705 = (p_universeFrom u)
in (soft_parens_with_nesting uu____3705))
end
| uu____3706 -> begin
(

let uu____3707 = (

let uu____3708 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" uu____3708))
in (failwith uu____3707))
end)))
and p_univar : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (

let uu____3710 = (

let uu____3711 = (unparen u)
in uu____3711.FStar_Parser_AST.tm)
in (match (uu____3710) with
| FStar_Parser_AST.Uvar (id) -> begin
(str (FStar_Ident.text_of_id id))
end
| uu____3713 -> begin
(

let uu____3714 = (

let uu____3715 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Not a universe variable %s" uu____3715))
in (failwith uu____3714))
end)))


let term_to_document : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_term e))


let decl_to_document : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun e -> (p_decl e))


let modul_to_document : FStar_Parser_AST.modul  ->  FStar_Pprint.document = (fun m -> ((FStar_ST.write should_print_fs_typ_app false);
(

let res = (match (m) with
| (FStar_Parser_AST.Module (_, decls)) | (FStar_Parser_AST.Interface (_, decls, _)) -> begin
(

let uu____3737 = (FStar_All.pipe_right decls (FStar_List.map decl_to_document))
in (FStar_All.pipe_right uu____3737 (FStar_Pprint.separate FStar_Pprint.hardline)))
end)
in ((FStar_ST.write should_print_fs_typ_app false);
res;
));
))


let comments_to_document : (Prims.string * FStar_Range.range) Prims.list  ->  FStar_Pprint.document = (fun comments -> (FStar_Pprint.separate_map FStar_Pprint.hardline (fun uu____3756 -> (match (uu____3756) with
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

let uu____3803 = (match (ds) with
| ({FStar_Parser_AST.d = FStar_Parser_AST.Pragma (FStar_Parser_AST.LightOff); FStar_Parser_AST.drange = uu____3810; FStar_Parser_AST.doc = uu____3811; FStar_Parser_AST.quals = uu____3812; FStar_Parser_AST.attrs = uu____3813})::uu____3814 -> begin
(

let d0 = (FStar_List.hd ds)
in (

let uu____3818 = (

let uu____3820 = (

let uu____3822 = (FStar_List.tl ds)
in (d)::uu____3822)
in (d0)::uu____3820)
in ((uu____3818), (d0.FStar_Parser_AST.drange))))
end
| uu____3825 -> begin
(((d)::ds), (d.FStar_Parser_AST.drange))
end)
in (match (uu____3803) with
| (decls, first_range) -> begin
(

let extract_decl_range = (fun d -> d.FStar_Parser_AST.drange)
in ((FStar_ST.write comment_stack comments);
(

let initial_comment = (

let uu____3848 = (FStar_Range.start_of_range first_range)
in (place_comments_until_pos (Prims.parse_int "0") (Prims.parse_int "1") uu____3848 FStar_Pprint.empty))
in (

let doc = (separate_map_with_comments FStar_Pprint.empty FStar_Pprint.empty decl_to_document decls extract_decl_range)
in (

let comments = (FStar_ST.read comment_stack)
in ((FStar_ST.write comment_stack []);
(FStar_ST.write should_print_fs_typ_app false);
(

let uu____3870 = (FStar_Pprint.op_Hat_Hat initial_comment doc)
in ((uu____3870), (comments)));
))));
))
end))
end);
)))




