
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
| FStar_Parser_AST.Paren (t1) -> begin
(unparen t1)
end
| uu____50 -> begin
t
end)
end)))


let str : Prims.string  ->  FStar_Pprint.document = (fun s -> (FStar_Pprint.doc_of_string s))


let default_or_map = (fun n1 f x -> (match (x) with
| None -> begin
n1
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


let soft_surround_separate_map = (fun n1 b void_ opening sep closing f xs -> (match ((xs = [])) with
| true -> begin
void_
end
| uu____298 -> begin
(

let uu____299 = (FStar_Pprint.separate_map sep f xs)
in (FStar_Pprint.soft_surround n1 b opening uu____299 closing))
end))


let doc_of_fsdoc : (Prims.string * (Prims.string * Prims.string) Prims.list)  ->  FStar_Pprint.document = (fun uu____307 -> (match (uu____307) with
| (comment, keywords1) -> begin
(

let uu____321 = (

let uu____322 = (

let uu____324 = (str comment)
in (

let uu____325 = (

let uu____327 = (

let uu____329 = (FStar_Pprint.separate_map FStar_Pprint.comma (fun uu____332 -> (match (uu____332) with
| (k, v1) -> begin
(

let uu____337 = (

let uu____339 = (str k)
in (

let uu____340 = (

let uu____342 = (

let uu____344 = (str v1)
in (uu____344)::[])
in (FStar_Pprint.rarrow)::uu____342)
in (uu____339)::uu____340))
in (FStar_Pprint.concat uu____337))
end)) keywords1)
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


let is_list_structure : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun cons_lid1 nil_lid1 -> (

let rec aux = (fun e -> (

let uu____377 = (

let uu____378 = (unparen e)
in uu____378.FStar_Parser_AST.tm)
in (match (uu____377) with
| FStar_Parser_AST.Construct (lid, []) -> begin
(FStar_Ident.lid_equals lid nil_lid1)
end
| FStar_Parser_AST.Construct (lid, (uu____386)::((e2, uu____388))::[]) -> begin
((FStar_Ident.lid_equals lid cons_lid1) && (aux e2))
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
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_singleton_lid); FStar_Parser_AST.range = uu____453; FStar_Parser_AST.level = uu____454}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_ref_lid); FStar_Parser_AST.range = uu____456; FStar_Parser_AST.level = uu____457}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____459; FStar_Parser_AST.level = uu____460}, FStar_Parser_AST.Nothing) -> begin
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
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (uu____477); FStar_Parser_AST.range = uu____478; FStar_Parser_AST.level = uu____479}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (uu____480); FStar_Parser_AST.range = uu____481; FStar_Parser_AST.level = uu____482}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____484; FStar_Parser_AST.level = uu____485}, FStar_Parser_AST.Nothing) -> begin
(e1)::[]
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

let rec aux = (fun e1 acc -> (

let uu____538 = (

let uu____539 = (unparen e1)
in uu____539.FStar_Parser_AST.tm)
in (match (uu____538) with
| FStar_Parser_AST.App (head1, arg, imp) -> begin
(aux head1 ((((arg), (imp)))::acc))
end
| uu____550 -> begin
((e1), (acc))
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


let token_to_string : (FStar_BaseTypes.char, Prims.string) FStar_Util.either  ->  Prims.string = (fun uu___128_577 -> (match (uu___128_577) with
| FStar_Util.Inl (c) -> begin
(Prims.strcat (FStar_Util.string_of_char c) ".*")
end
| FStar_Util.Inr (s) -> begin
s
end))


let matches_token : Prims.string  ->  (FStar_Char.char, Prims.string) FStar_Util.either  ->  Prims.bool = (fun s uu___129_589 -> (match (uu___129_589) with
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

let levels_from_associativity = (fun l uu___130_947 -> (match (uu___130_947) with
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
| (assoc1, tokens) -> begin
(((levels_from_associativity i assoc1)), (tokens))
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

let find_level_and_max = (fun n1 level -> (

let uu____1109 = (FStar_List.tryFind (fun uu____1127 -> (match (uu____1127) with
| (uu____1136, tokens) -> begin
(tokens = (Prims.snd level))
end)) level_table)
in (match (uu____1109) with
| Some ((uu____1156, l1, uu____1158), uu____1159) -> begin
(max n1 l1)
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

let comments1 = (match (has_lookahead) with
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

let uu____1417 = (FStar_Pprint.op_Hat_Hat comments1 printed_e)
in (FStar_Pprint.group uu____1417))))
end))))


let rec place_comments_until_pos : Prims.int  ->  Prims.int  ->  FStar_Range.pos  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun k lbegin pos_end doc1 -> (

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

let doc2 = (

let uu____1458 = (

let uu____1459 = (FStar_Pprint.repeat lnum FStar_Pprint.hardline)
in (

let uu____1460 = (str comment)
in (FStar_Pprint.op_Hat_Hat uu____1459 uu____1460)))
in (FStar_Pprint.op_Hat_Hat doc1 uu____1458))
in (

let uu____1461 = (

let uu____1462 = (FStar_Range.end_of_range crange)
in (FStar_Range.line_of_pos uu____1462))
in (place_comments_until_pos (Prims.parse_int "1") uu____1461 pos_end doc2))));
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
in (FStar_Pprint.op_Hat_Hat doc1 uu____1470)))
end)))


let separate_map_with_comments = (fun prefix1 sep f xs extract_range -> (

let fold_fun = (fun uu____1519 x -> (match (uu____1519) with
| (last_line, doc1) -> begin
(

let r = (extract_range x)
in (

let doc2 = (

let uu____1529 = (FStar_Range.start_of_range r)
in (place_comments_until_pos (Prims.parse_int "1") last_line uu____1529 doc1))
in (

let uu____1530 = (

let uu____1531 = (FStar_Range.end_of_range r)
in (FStar_Range.line_of_pos uu____1531))
in (

let uu____1532 = (

let uu____1533 = (

let uu____1534 = (f x)
in (FStar_Pprint.op_Hat_Hat sep uu____1534))
in (FStar_Pprint.op_Hat_Hat doc2 uu____1533))
in ((uu____1530), (uu____1532))))))
end))
in (

let uu____1535 = (

let uu____1539 = (FStar_List.hd xs)
in (

let uu____1540 = (FStar_List.tl xs)
in ((uu____1539), (uu____1540))))
in (match (uu____1535) with
| (x, xs1) -> begin
(

let init1 = (

let uu____1550 = (

let uu____1551 = (

let uu____1552 = (extract_range x)
in (FStar_Range.end_of_range uu____1552))
in (FStar_Range.line_of_pos uu____1551))
in (

let uu____1553 = (

let uu____1554 = (f x)
in (FStar_Pprint.op_Hat_Hat prefix1 uu____1554))
in ((uu____1550), (uu____1553))))
in (

let uu____1555 = (FStar_List.fold_left fold_fun init1 xs1)
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
and p_fsdoc : FStar_Syntax_Syntax.fsdoc  ->  FStar_Pprint.document = (fun uu____1814 -> (match (uu____1814) with
| (doc1, kwd_args) -> begin
(

let kwd_args_doc = (match (kwd_args) with
| [] -> begin
FStar_Pprint.empty
end
| kwd_args1 -> begin
(

let process_kwd_arg = (fun uu____1835 -> (match (uu____1835) with
| (kwd1, arg) -> begin
(

let uu____1840 = (str "@")
in (

let uu____1841 = (

let uu____1842 = (str kwd1)
in (

let uu____1843 = (

let uu____1844 = (str arg)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1844))
in (FStar_Pprint.op_Hat_Hat uu____1842 uu____1843)))
in (FStar_Pprint.op_Hat_Hat uu____1840 uu____1841)))
end))
in (

let uu____1845 = (

let uu____1846 = (FStar_Pprint.separate_map FStar_Pprint.hardline process_kwd_arg kwd_args1)
in (FStar_Pprint.op_Hat_Hat uu____1846 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____1845)))
end)
in (

let uu____1849 = (

let uu____1850 = (

let uu____1851 = (

let uu____1852 = (

let uu____1853 = (str doc1)
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
| FStar_Parser_AST.Fsdoc (doc1) -> begin
(

let uu____1982 = (p_fsdoc doc1)
in (FStar_Pprint.op_Hat_Hat uu____1982 FStar_Pprint.hardline))
end
| FStar_Parser_AST.Main (uu____1983) -> begin
(failwith "*Main declaration* : Is that really still in use ??")
end
| FStar_Parser_AST.Tycon (true, uu____1984) -> begin
(failwith "Effect abbreviation is expected to be defined by an abbreviation")
end))
and p_pragma : FStar_Parser_AST.pragma  ->  FStar_Pprint.document = (fun uu___131_1993 -> (match (uu___131_1993) with
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
and p_fsdocTypeDeclPairs : (FStar_Parser_AST.tycon * FStar_Syntax_Syntax.fsdoc Prims.option)  ->  FStar_Pprint.document = (fun uu____2011 -> (match (uu____2011) with
| (typedecl, fsdoc_opt) -> begin
(

let uu____2019 = (FStar_Pprint.optional p_fsdoc fsdoc_opt)
in (

let uu____2020 = (p_typeDecl typedecl)
in (FStar_Pprint.op_Hat_Hat uu____2019 uu____2020)))
end))
and p_typeDecl : FStar_Parser_AST.tycon  ->  FStar_Pprint.document = (fun uu___132_2021 -> (match (uu___132_2021) with
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
| (lid1, t, doc_opt) -> begin
(

let uu____2081 = (FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range)
in (with_comment p_recordFieldDecl ((lid1), (t), (doc_opt)) uu____2081))
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
and p_recordFieldDecl : (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Syntax_Syntax.fsdoc Prims.option)  ->  FStar_Pprint.document = (fun uu____2213 -> (match (uu____2213) with
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
and p_constructorDecl : (FStar_Ident.ident * FStar_Parser_AST.term Prims.option * FStar_Syntax_Syntax.fsdoc Prims.option * Prims.bool)  ->  FStar_Pprint.document = (fun uu____2229 -> (match (uu____2229) with
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

let uu____2248 = (

let uu____2249 = (FStar_Pprint.break_ (Prims.parse_int "0"))
in (

let uu____2250 = (default_or_map uid_doc (fun t -> (

let uu____2252 = (

let uu____2253 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep)
in (FStar_Pprint.op_Hat_Hat uid_doc uu____2253))
in (

let uu____2254 = (p_typ t)
in (op_Hat_Slash_Plus_Hat uu____2252 uu____2254)))) t_opt)
in (FStar_Pprint.op_Hat_Hat uu____2249 uu____2250)))
in (FStar_Pprint.op_Hat_Hat uu____2247 uu____2248)))))
end))
and p_letbinding : (FStar_Parser_AST.pattern * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun uu____2255 -> (match (uu____2255) with
| (pat, e) -> begin
(

let pat_doc = (

let uu____2261 = (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat1, t) -> begin
(

let uu____2268 = (

let uu____2269 = (

let uu____2270 = (

let uu____2271 = (

let uu____2272 = (p_tmArrow p_tmNoEq t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2272))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2271))
in (FStar_Pprint.group uu____2270))
in (FStar_Pprint.op_Hat_Hat break1 uu____2269))
in ((pat1), (uu____2268)))
end
| uu____2273 -> begin
((pat), (FStar_Pprint.empty))
end)
in (match (uu____2261) with
| (pat1, ascr_doc) -> begin
(match (pat1.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____2277); FStar_Parser_AST.prange = uu____2278}, pats) -> begin
(

let uu____2284 = (p_lident x)
in (

let uu____2285 = (

let uu____2286 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Hat uu____2286 ascr_doc))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____2284 uu____2285 FStar_Pprint.equals)))
end
| uu____2287 -> begin
(

let uu____2288 = (

let uu____2289 = (p_tuplePattern pat1)
in (

let uu____2290 = (FStar_Pprint.op_Hat_Slash_Hat ascr_doc FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____2289 uu____2290)))
in (FStar_Pprint.group uu____2288))
end)
end))
in (

let uu____2291 = (p_term e)
in (prefix2 pat_doc uu____2291)))
end))
and p_newEffect : FStar_Parser_AST.effect_decl  ->  FStar_Pprint.document = (fun uu___133_2292 -> (match (uu___133_2292) with
| FStar_Parser_AST.RedefineEffect (lid, bs, t) -> begin
(p_effectRedefinition lid bs t)
end
| FStar_Parser_AST.DefineEffect (lid, bs, t, eff_decls) -> begin
(p_effectDefinition lid bs t eff_decls)
end))
and p_effectRedefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun uid bs t -> (

let uu____2310 = (p_uident uid)
in (

let uu____2311 = (p_binders true bs)
in (

let uu____2312 = (

let uu____2313 = (p_simpleTerm t)
in (prefix2 FStar_Pprint.equals uu____2313))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____2310 uu____2311 uu____2312)))))
and p_effectDefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun uid bs t eff_decls -> (

let uu____2320 = (

let uu____2321 = (

let uu____2322 = (

let uu____2323 = (p_uident uid)
in (

let uu____2324 = (p_binders true bs)
in (

let uu____2325 = (

let uu____2326 = (p_typ t)
in (prefix2 FStar_Pprint.colon uu____2326))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____2323 uu____2324 uu____2325))))
in (FStar_Pprint.group uu____2322))
in (

let uu____2327 = (

let uu____2328 = (str "with")
in (

let uu____2329 = (separate_break_map FStar_Pprint.semi p_effectDecl eff_decls)
in (prefix2 uu____2328 uu____2329)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2321 uu____2327)))
in (braces_with_nesting uu____2320)))
and p_effectDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (false, ((FStar_Parser_AST.TyconAbbrev (lid, [], None, e), None))::[]) -> begin
(

let uu____2346 = (

let uu____2347 = (p_lident lid)
in (

let uu____2348 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____2347 uu____2348)))
in (

let uu____2349 = (p_simpleTerm e)
in (prefix2 uu____2346 uu____2349)))
end
| uu____2350 -> begin
(

let uu____2351 = (

let uu____2352 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "Not a declaration of an effect member... or at least I hope so : %s" uu____2352))
in (failwith uu____2351))
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

let p_lift = (fun uu____2385 -> (match (uu____2385) with
| (kwd1, t) -> begin
(

let uu____2390 = (

let uu____2391 = (str kwd1)
in (

let uu____2392 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____2391 uu____2392)))
in (

let uu____2393 = (p_simpleTerm t)
in (prefix2 uu____2390 uu____2393)))
end))
in (separate_break_map FStar_Pprint.semi p_lift lifts)))
in (

let uu____2396 = (

let uu____2397 = (

let uu____2398 = (p_quident lift.FStar_Parser_AST.msource)
in (

let uu____2399 = (

let uu____2400 = (str "~>")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2400))
in (FStar_Pprint.op_Hat_Hat uu____2398 uu____2399)))
in (

let uu____2401 = (p_quident lift.FStar_Parser_AST.mdest)
in (prefix2 uu____2397 uu____2401)))
in (

let uu____2402 = (

let uu____2403 = (braces_with_nesting lift_op_doc)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2403))
in (FStar_Pprint.op_Hat_Hat uu____2396 uu____2402)))))
and p_qualifier : FStar_Parser_AST.qualifier  ->  FStar_Pprint.document = (fun uu___134_2404 -> (match (uu___134_2404) with
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

let uu____2406 = (FStar_Pprint.separate_map break1 p_qualifier qs)
in (FStar_Pprint.group uu____2406)))
and p_letqualifier : FStar_Parser_AST.let_qualifier  ->  FStar_Pprint.document = (fun uu___135_2407 -> (match (uu___135_2407) with
| FStar_Parser_AST.Rec -> begin
(

let uu____2408 = (str "rec")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2408))
end
| FStar_Parser_AST.Mutable -> begin
(

let uu____2409 = (str "mutable")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2409))
end
| FStar_Parser_AST.NoLetQualifier -> begin
FStar_Pprint.empty
end))
and p_aqual : FStar_Parser_AST.arg_qualifier  ->  FStar_Pprint.document = (fun uu___136_2410 -> (match (uu___136_2410) with
| FStar_Parser_AST.Implicit -> begin
(str "#")
end
| FStar_Parser_AST.Equality -> begin
(str "$")
end))
and p_disjunctivePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr (pats) -> begin
(

let uu____2414 = (

let uu____2415 = (

let uu____2416 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space)
in (FStar_Pprint.op_Hat_Hat break1 uu____2416))
in (FStar_Pprint.separate_map uu____2415 p_tuplePattern pats))
in (FStar_Pprint.group uu____2414))
end
| uu____2417 -> begin
(p_tuplePattern p)
end))
and p_tuplePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTuple (pats, false) -> begin
(

let uu____2422 = (

let uu____2423 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map uu____2423 p_constructorPattern pats))
in (FStar_Pprint.group uu____2422))
end
| uu____2424 -> begin
(p_constructorPattern p)
end))
and p_constructorPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (maybe_cons_lid); FStar_Parser_AST.prange = uu____2427}, (hd1)::(tl1)::[]) when (FStar_Ident.lid_equals maybe_cons_lid FStar_Syntax_Const.cons_lid) -> begin
(

let uu____2431 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon)
in (

let uu____2432 = (p_constructorPattern hd1)
in (

let uu____2433 = (p_constructorPattern tl1)
in (infix0 uu____2431 uu____2432 uu____2433))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (uid); FStar_Parser_AST.prange = uu____2435}, pats) -> begin
(

let uu____2439 = (p_quident uid)
in (

let uu____2440 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (prefix2 uu____2439 uu____2440)))
end
| uu____2441 -> begin
(p_atomicPattern p)
end))
and p_atomicPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, t) -> begin
(

let uu____2445 = (

let uu____2448 = (

let uu____2449 = (unparen t)
in uu____2449.FStar_Parser_AST.tm)
in ((pat.FStar_Parser_AST.pat), (uu____2448)))
in (match (uu____2445) with
| (FStar_Parser_AST.PatVar (lid, aqual), FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t1); FStar_Parser_AST.brange = uu____2454; FStar_Parser_AST.blevel = uu____2455; FStar_Parser_AST.aqual = uu____2456}, phi)) when (lid.FStar_Ident.idText = lid'.FStar_Ident.idText) -> begin
(

let uu____2460 = (

let uu____2461 = (p_ident lid)
in (p_refinement aqual uu____2461 t1 phi))
in (soft_parens_with_nesting uu____2460))
end
| (FStar_Parser_AST.PatWild, FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t1); FStar_Parser_AST.brange = uu____2463; FStar_Parser_AST.blevel = uu____2464; FStar_Parser_AST.aqual = uu____2465}, phi)) -> begin
(

let uu____2467 = (p_refinement None FStar_Pprint.underscore t1 phi)
in (soft_parens_with_nesting uu____2467))
end
| uu____2468 -> begin
(

let uu____2471 = (

let uu____2472 = (p_tuplePattern pat)
in (

let uu____2473 = (

let uu____2474 = (FStar_Pprint.break_ (Prims.parse_int "0"))
in (

let uu____2475 = (

let uu____2476 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2476))
in (FStar_Pprint.op_Hat_Hat uu____2474 uu____2475)))
in (FStar_Pprint.op_Hat_Hat uu____2472 uu____2473)))
in (soft_parens_with_nesting uu____2471))
end))
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let uu____2479 = (separate_break_map FStar_Pprint.semi p_tuplePattern pats)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket uu____2479 FStar_Pprint.rbracket))
end
| FStar_Parser_AST.PatRecord (pats) -> begin
(

let p_recordFieldPat = (fun uu____2489 -> (match (uu____2489) with
| (lid, pat) -> begin
(

let uu____2494 = (p_qlident lid)
in (

let uu____2495 = (p_tuplePattern pat)
in (infix2 FStar_Pprint.equals uu____2494 uu____2495)))
end))
in (

let uu____2496 = (separate_break_map FStar_Pprint.semi p_recordFieldPat pats)
in (soft_braces_with_nesting uu____2496)))
end
| FStar_Parser_AST.PatTuple (pats, true) -> begin
(

let uu____2502 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (

let uu____2503 = (separate_break_map FStar_Pprint.comma p_constructorPattern pats)
in (

let uu____2504 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____2502 uu____2503 uu____2504))))
end
| FStar_Parser_AST.PatTvar (tv, arg_qualifier_opt) -> begin
(p_tvar tv)
end
| FStar_Parser_AST.PatOp (op) -> begin
(

let uu____2511 = (

let uu____2512 = (

let uu____2513 = (str op)
in (

let uu____2514 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat uu____2513 uu____2514)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2512))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2511))
end
| FStar_Parser_AST.PatWild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.PatConst (c) -> begin
(p_constant c)
end
| FStar_Parser_AST.PatVar (lid, aqual) -> begin
(

let uu____2520 = (FStar_Pprint.optional p_aqual aqual)
in (

let uu____2521 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat uu____2520 uu____2521)))
end
| FStar_Parser_AST.PatName (uid) -> begin
(p_quident uid)
end
| FStar_Parser_AST.PatOr (uu____2523) -> begin
(failwith "Inner or pattern !")
end
| (FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (_); FStar_Parser_AST.prange = _}, _)) | (FStar_Parser_AST.PatTuple (_, false)) -> begin
(

let uu____2531 = (p_tuplePattern p)
in (soft_parens_with_nesting uu____2531))
end
| uu____2532 -> begin
(

let uu____2533 = (

let uu____2534 = (FStar_Parser_AST.pat_to_string p)
in (FStar_Util.format1 "Invalid pattern %s" uu____2534))
in (failwith uu____2533))
end))
and p_binder : Prims.bool  ->  FStar_Parser_AST.binder  ->  FStar_Pprint.document = (fun is_atomic b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (lid) -> begin
(

let uu____2538 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (

let uu____2539 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat uu____2538 uu____2539)))
end
| FStar_Parser_AST.TVariable (lid) -> begin
(p_lident lid)
end
| FStar_Parser_AST.Annotated (lid, t) -> begin
(

let doc1 = (

let uu____2544 = (

let uu____2545 = (unparen t)
in uu____2545.FStar_Parser_AST.tm)
in (match (uu____2544) with
| FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t1); FStar_Parser_AST.brange = uu____2548; FStar_Parser_AST.blevel = uu____2549; FStar_Parser_AST.aqual = uu____2550}, phi) when (lid.FStar_Ident.idText = lid'.FStar_Ident.idText) -> begin
(

let uu____2552 = (p_ident lid)
in (p_refinement b.FStar_Parser_AST.aqual uu____2552 t1 phi))
end
| uu____2553 -> begin
(

let uu____2554 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (

let uu____2555 = (

let uu____2556 = (p_lident lid)
in (

let uu____2557 = (

let uu____2558 = (

let uu____2559 = (FStar_Pprint.break_ (Prims.parse_int "0"))
in (

let uu____2560 = (p_tmFormula t)
in (FStar_Pprint.op_Hat_Hat uu____2559 uu____2560)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2558))
in (FStar_Pprint.op_Hat_Hat uu____2556 uu____2557)))
in (FStar_Pprint.op_Hat_Hat uu____2554 uu____2555)))
end))
in (match (is_atomic) with
| true -> begin
(

let uu____2561 = (

let uu____2562 = (FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2562))
in (FStar_Pprint.group uu____2561))
end
| uu____2563 -> begin
(FStar_Pprint.group doc1)
end))
end
| FStar_Parser_AST.TAnnotated (uu____2564) -> begin
(failwith "Is this still used ?")
end
| FStar_Parser_AST.NoName (t) -> begin
(

let uu____2568 = (

let uu____2569 = (unparen t)
in uu____2569.FStar_Parser_AST.tm)
in (match (uu____2568) with
| FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t1); FStar_Parser_AST.brange = uu____2571; FStar_Parser_AST.blevel = uu____2572; FStar_Parser_AST.aqual = uu____2573}, phi) -> begin
(match (is_atomic) with
| true -> begin
(

let uu____2575 = (

let uu____2576 = (

let uu____2577 = (p_refinement b.FStar_Parser_AST.aqual FStar_Pprint.underscore t1 phi)
in (FStar_Pprint.op_Hat_Hat uu____2577 FStar_Pprint.rparen))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2576))
in (FStar_Pprint.group uu____2575))
end
| uu____2578 -> begin
(

let uu____2579 = (p_refinement b.FStar_Parser_AST.aqual FStar_Pprint.underscore t1 phi)
in (FStar_Pprint.group uu____2579))
end)
end
| uu____2580 -> begin
(match (is_atomic) with
| true -> begin
(p_atomicTerm t)
end
| uu____2581 -> begin
(p_appTerm t)
end)
end))
end))
and p_refinement : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Pprint.document  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun aqual_opt binder t phi -> (

let uu____2587 = (FStar_Pprint.optional p_aqual aqual_opt)
in (

let uu____2588 = (

let uu____2589 = (

let uu____2590 = (

let uu____2591 = (p_appTerm t)
in (

let uu____2592 = (

let uu____2593 = (p_noSeqTerm phi)
in (soft_braces_with_nesting uu____2593))
in (FStar_Pprint.op_Hat_Hat uu____2591 uu____2592)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2590))
in (FStar_Pprint.op_Hat_Hat binder uu____2589))
in (FStar_Pprint.op_Hat_Hat uu____2587 uu____2588))))
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
| uu____2604 -> begin
(p_lident id)
end))
and p_term : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2606 = (

let uu____2607 = (unparen e)
in uu____2607.FStar_Parser_AST.tm)
in (match (uu____2606) with
| FStar_Parser_AST.Seq (e1, e2) -> begin
(

let uu____2610 = (

let uu____2611 = (

let uu____2612 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat uu____2612 FStar_Pprint.semi))
in (FStar_Pprint.group uu____2611))
in (

let uu____2613 = (p_term e2)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2610 uu____2613)))
end
| uu____2614 -> begin
(

let uu____2615 = (p_noSeqTerm e)
in (FStar_Pprint.group uu____2615))
end)))
and p_noSeqTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_noSeqTerm' e e.FStar_Parser_AST.range))
and p_noSeqTerm' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2618 = (

let uu____2619 = (unparen e)
in uu____2619.FStar_Parser_AST.tm)
in (match (uu____2618) with
| FStar_Parser_AST.Ascribed (e1, t, None) -> begin
(

let uu____2623 = (

let uu____2624 = (p_tmIff e1)
in (

let uu____2625 = (

let uu____2626 = (

let uu____2627 = (p_typ t)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____2627))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____2626))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2624 uu____2625)))
in (FStar_Pprint.group uu____2623))
end
| FStar_Parser_AST.Ascribed (e1, t, Some (tac)) -> begin
(

let uu____2632 = (

let uu____2633 = (p_tmIff e1)
in (

let uu____2634 = (

let uu____2635 = (

let uu____2636 = (

let uu____2637 = (p_typ t)
in (

let uu____2638 = (

let uu____2639 = (str "by")
in (

let uu____2640 = (p_typ tac)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2639 uu____2640)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2637 uu____2638)))
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____2636))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____2635))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2633 uu____2634)))
in (FStar_Pprint.group uu____2632))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::(e3)::[]) when (op = ".()<-") -> begin
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
in (soft_parens_with_nesting uu____2653))
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
| FStar_Parser_AST.Op (op, (e1)::(e2)::(e3)::[]) when (op = ".[]<-") -> begin
(

let uu____2662 = (

let uu____2663 = (

let uu____2664 = (

let uu____2665 = (p_atomicTermNotQUident e1)
in (

let uu____2666 = (

let uu____2667 = (

let uu____2668 = (

let uu____2669 = (p_term e2)
in (soft_brackets_with_nesting uu____2669))
in (

let uu____2670 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat uu____2668 uu____2670)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____2667))
in (FStar_Pprint.op_Hat_Hat uu____2665 uu____2666)))
in (FStar_Pprint.group uu____2664))
in (

let uu____2671 = (

let uu____2672 = (p_noSeqTerm e3)
in (jump2 uu____2672))
in (FStar_Pprint.op_Hat_Hat uu____2663 uu____2671)))
in (FStar_Pprint.group uu____2662))
end
| FStar_Parser_AST.Requires (e1, wtf) -> begin
(

let uu____2678 = (

let uu____2679 = (str "requires")
in (

let uu____2680 = (p_typ e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2679 uu____2680)))
in (FStar_Pprint.group uu____2678))
end
| FStar_Parser_AST.Ensures (e1, wtf) -> begin
(

let uu____2686 = (

let uu____2687 = (str "ensures")
in (

let uu____2688 = (p_typ e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2687 uu____2688)))
in (FStar_Pprint.group uu____2686))
end
| FStar_Parser_AST.Attributes (es) -> begin
(

let uu____2691 = (

let uu____2692 = (str "attributes")
in (

let uu____2693 = (FStar_Pprint.separate_map break1 p_atomicTerm es)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2692 uu____2693)))
in (FStar_Pprint.group uu____2691))
end
| FStar_Parser_AST.If (e1, e2, e3) -> begin
(

let uu____2697 = (is_unit e3)
in (match (uu____2697) with
| true -> begin
(

let uu____2698 = (

let uu____2699 = (

let uu____2700 = (str "if")
in (

let uu____2701 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat uu____2700 uu____2701)))
in (

let uu____2702 = (

let uu____2703 = (str "then")
in (

let uu____2704 = (p_noSeqTerm e2)
in (op_Hat_Slash_Plus_Hat uu____2703 uu____2704)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2699 uu____2702)))
in (FStar_Pprint.group uu____2698))
end
| uu____2705 -> begin
(

let e2_doc = (

let uu____2707 = (

let uu____2708 = (unparen e2)
in uu____2708.FStar_Parser_AST.tm)
in (match (uu____2707) with
| FStar_Parser_AST.If (uu____2709, uu____2710, e31) when (is_unit e31) -> begin
(

let uu____2712 = (p_noSeqTerm e2)
in (soft_parens_with_nesting uu____2712))
end
| uu____2713 -> begin
(p_noSeqTerm e2)
end))
in (

let uu____2714 = (

let uu____2715 = (

let uu____2716 = (str "if")
in (

let uu____2717 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat uu____2716 uu____2717)))
in (

let uu____2718 = (

let uu____2719 = (

let uu____2720 = (str "then")
in (op_Hat_Slash_Plus_Hat uu____2720 e2_doc))
in (

let uu____2721 = (

let uu____2722 = (str "else")
in (

let uu____2723 = (p_noSeqTerm e3)
in (op_Hat_Slash_Plus_Hat uu____2722 uu____2723)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2719 uu____2721)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2715 uu____2718)))
in (FStar_Pprint.group uu____2714)))
end))
end
| FStar_Parser_AST.TryWith (e1, branches) -> begin
(

let uu____2736 = (

let uu____2737 = (

let uu____2738 = (str "try")
in (

let uu____2739 = (p_noSeqTerm e1)
in (prefix2 uu____2738 uu____2739)))
in (

let uu____2740 = (

let uu____2741 = (str "with")
in (

let uu____2742 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2741 uu____2742)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2737 uu____2740)))
in (FStar_Pprint.group uu____2736))
end
| FStar_Parser_AST.Match (e1, branches) -> begin
(

let uu____2759 = (

let uu____2760 = (

let uu____2761 = (str "match")
in (

let uu____2762 = (p_noSeqTerm e1)
in (

let uu____2763 = (str "with")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____2761 uu____2762 uu____2763))))
in (

let uu____2764 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2760 uu____2764)))
in (FStar_Pprint.group uu____2759))
end
| FStar_Parser_AST.LetOpen (uid, e1) -> begin
(

let uu____2771 = (

let uu____2772 = (

let uu____2773 = (str "let open")
in (

let uu____2774 = (p_quident uid)
in (

let uu____2775 = (str "in")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____2773 uu____2774 uu____2775))))
in (

let uu____2776 = (p_term e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2772 uu____2776)))
in (FStar_Pprint.group uu____2771))
end
| FStar_Parser_AST.Let (q, lbs, e1) -> begin
(

let let_doc = (

let uu____2787 = (str "let")
in (

let uu____2788 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat uu____2787 uu____2788)))
in (

let uu____2789 = (

let uu____2790 = (

let uu____2791 = (

let uu____2792 = (str "and")
in (precede_break_separate_map let_doc uu____2792 p_letbinding lbs))
in (

let uu____2795 = (str "in")
in (FStar_Pprint.op_Hat_Slash_Hat uu____2791 uu____2795)))
in (FStar_Pprint.group uu____2790))
in (

let uu____2796 = (p_term e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2789 uu____2796))))
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, typ_opt); FStar_Parser_AST.prange = uu____2799})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, branches); FStar_Parser_AST.range = uu____2802; FStar_Parser_AST.level = uu____2803}) when (matches_var maybe_x x) -> begin
(

let uu____2817 = (

let uu____2818 = (str "function")
in (

let uu____2819 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2818 uu____2819)))
in (FStar_Pprint.group uu____2817))
end
| FStar_Parser_AST.Assign (id, e1) -> begin
(

let uu____2826 = (

let uu____2827 = (p_lident id)
in (

let uu____2828 = (

let uu____2829 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow uu____2829))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2827 uu____2828)))
in (FStar_Pprint.group uu____2826))
end
| uu____2830 -> begin
(p_typ e)
end)))
and p_typ : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_typ' e e.FStar_Parser_AST.range))
and p_typ' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2833 = (

let uu____2834 = (unparen e)
in uu____2834.FStar_Parser_AST.tm)
in (match (uu____2833) with
| (FStar_Parser_AST.QForall (bs, trigger, e1)) | (FStar_Parser_AST.QExists (bs, trigger, e1)) -> begin
(

let uu____2850 = (

let uu____2851 = (

let uu____2852 = (p_quantifier e)
in (FStar_Pprint.op_Hat_Hat uu____2852 FStar_Pprint.space))
in (

let uu____2853 = (p_binders true bs)
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") uu____2851 uu____2853 FStar_Pprint.dot)))
in (

let uu____2854 = (

let uu____2855 = (p_trigger trigger)
in (

let uu____2856 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat uu____2855 uu____2856)))
in (prefix2 uu____2850 uu____2854)))
end
| uu____2857 -> begin
(p_simpleTerm e)
end)))
and p_quantifier : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2859 = (

let uu____2860 = (unparen e)
in uu____2860.FStar_Parser_AST.tm)
in (match (uu____2859) with
| FStar_Parser_AST.QForall (uu____2861) -> begin
(str "forall")
end
| FStar_Parser_AST.QExists (uu____2868) -> begin
(str "exists")
end
| uu____2875 -> begin
(failwith "Imposible : p_quantifier called on a non-quantifier term")
end)))
and p_trigger : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun uu___137_2876 -> (match (uu___137_2876) with
| [] -> begin
FStar_Pprint.empty
end
| pats -> begin
(

let uu____2883 = (

let uu____2884 = (

let uu____2885 = (str "pattern")
in (

let uu____2886 = (

let uu____2887 = (

let uu____2888 = (p_disjunctivePats pats)
in (jump2 uu____2888))
in (

let uu____2889 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2887 uu____2889)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2885 uu____2886)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2884))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____2883))
end))
and p_disjunctivePats : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun pats -> (

let uu____2893 = (str "\\/")
in (FStar_Pprint.separate_map uu____2893 p_conjunctivePats pats)))
and p_conjunctivePats : FStar_Parser_AST.term Prims.list  ->  FStar_Pprint.document = (fun pats -> (

let uu____2897 = (FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats)
in (FStar_Pprint.group uu____2897)))
and p_simpleTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2899 = (

let uu____2900 = (unparen e)
in uu____2900.FStar_Parser_AST.tm)
in (match (uu____2899) with
| FStar_Parser_AST.Abs (pats, e1) -> begin
(

let uu____2905 = (

let uu____2906 = (str "fun")
in (

let uu____2907 = (

let uu____2908 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2908 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat uu____2906 uu____2907)))
in (

let uu____2909 = (p_term e1)
in (op_Hat_Slash_Plus_Hat uu____2905 uu____2909)))
end
| uu____2910 -> begin
(p_tmIff e)
end)))
and p_maybeFocusArrow : Prims.bool  ->  FStar_Pprint.document = (fun b -> (match (b) with
| true -> begin
(str "~>")
end
| uu____2912 -> begin
FStar_Pprint.rarrow
end))
and p_patternBranch : (FStar_Parser_AST.pattern * FStar_Parser_AST.term Prims.option * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun uu____2913 -> (match (uu____2913) with
| (pat, when_opt, e) -> begin
(

let maybe_paren = (

let uu____2926 = (

let uu____2927 = (unparen e)
in uu____2927.FStar_Parser_AST.tm)
in (match (uu____2926) with
| (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) -> begin
soft_begin_end_with_nesting
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____2933); FStar_Parser_AST.prange = uu____2934})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, uu____2936); FStar_Parser_AST.range = uu____2937; FStar_Parser_AST.level = uu____2938}) when (matches_var maybe_x x) -> begin
soft_begin_end_with_nesting
end
| uu____2952 -> begin
(fun x -> x)
end))
in (

let uu____2954 = (

let uu____2955 = (

let uu____2956 = (

let uu____2957 = (

let uu____2958 = (

let uu____2959 = (p_disjunctivePattern pat)
in (

let uu____2960 = (

let uu____2961 = (p_maybeWhen when_opt)
in (FStar_Pprint.op_Hat_Hat uu____2961 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat uu____2959 uu____2960)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2958))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____2957))
in (FStar_Pprint.group uu____2956))
in (

let uu____2962 = (

let uu____2963 = (p_term e)
in (maybe_paren uu____2963))
in (op_Hat_Slash_Plus_Hat uu____2955 uu____2962)))
in (FStar_Pprint.group uu____2954)))
end))
and p_maybeWhen : FStar_Parser_AST.term Prims.option  ->  FStar_Pprint.document = (fun uu___138_2964 -> (match (uu___138_2964) with
| None -> begin
FStar_Pprint.empty
end
| Some (e) -> begin
(

let uu____2967 = (str "when")
in (

let uu____2968 = (

let uu____2969 = (p_tmFormula e)
in (FStar_Pprint.op_Hat_Hat uu____2969 FStar_Pprint.space))
in (op_Hat_Slash_Plus_Hat uu____2967 uu____2968)))
end))
and p_tmIff : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2971 = (

let uu____2972 = (unparen e)
in uu____2972.FStar_Parser_AST.tm)
in (match (uu____2971) with
| FStar_Parser_AST.Op ("<==>", (e1)::(e2)::[]) -> begin
(

let uu____2976 = (str "<==>")
in (

let uu____2977 = (p_tmImplies e1)
in (

let uu____2978 = (p_tmIff e2)
in (infix0 uu____2976 uu____2977 uu____2978))))
end
| uu____2979 -> begin
(p_tmImplies e)
end)))
and p_tmImplies : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2981 = (

let uu____2982 = (unparen e)
in uu____2982.FStar_Parser_AST.tm)
in (match (uu____2981) with
| FStar_Parser_AST.Op ("==>", (e1)::(e2)::[]) -> begin
(

let uu____2986 = (str "==>")
in (

let uu____2987 = (p_tmArrow p_tmFormula e1)
in (

let uu____2988 = (p_tmImplies e2)
in (infix0 uu____2986 uu____2987 uu____2988))))
end
| uu____2989 -> begin
(p_tmArrow p_tmFormula e)
end)))
and p_tmArrow : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_Tm e -> (

let uu____2994 = (

let uu____2995 = (unparen e)
in uu____2995.FStar_Parser_AST.tm)
in (match (uu____2994) with
| FStar_Parser_AST.Product (bs, tgt) -> begin
(

let uu____3000 = (

let uu____3001 = (FStar_Pprint.concat_map (fun b -> (

let uu____3003 = (p_binder false b)
in (

let uu____3004 = (

let uu____3005 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3005))
in (FStar_Pprint.op_Hat_Hat uu____3003 uu____3004)))) bs)
in (

let uu____3006 = (p_tmArrow p_Tm tgt)
in (FStar_Pprint.op_Hat_Hat uu____3001 uu____3006)))
in (FStar_Pprint.group uu____3000))
end
| uu____3007 -> begin
(p_Tm e)
end)))
and p_tmFormula : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3009 = (

let uu____3010 = (unparen e)
in uu____3010.FStar_Parser_AST.tm)
in (match (uu____3009) with
| FStar_Parser_AST.Op ("\\/", (e1)::(e2)::[]) -> begin
(

let uu____3014 = (str "\\/")
in (

let uu____3015 = (p_tmFormula e1)
in (

let uu____3016 = (p_tmConjunction e2)
in (infix0 uu____3014 uu____3015 uu____3016))))
end
| uu____3017 -> begin
(p_tmConjunction e)
end)))
and p_tmConjunction : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3019 = (

let uu____3020 = (unparen e)
in uu____3020.FStar_Parser_AST.tm)
in (match (uu____3019) with
| FStar_Parser_AST.Op ("/\\", (e1)::(e2)::[]) -> begin
(

let uu____3024 = (str "/\\")
in (

let uu____3025 = (p_tmConjunction e1)
in (

let uu____3026 = (p_tmTuple e2)
in (infix0 uu____3024 uu____3025 uu____3026))))
end
| uu____3027 -> begin
(p_tmTuple e)
end)))
and p_tmTuple : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_tmTuple' e e.FStar_Parser_AST.range))
and p_tmTuple' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3030 = (

let uu____3031 = (unparen e)
in uu____3031.FStar_Parser_AST.tm)
in (match (uu____3030) with
| FStar_Parser_AST.Construct (lid, args) when (is_tuple_constructor lid) -> begin
(

let uu____3040 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map uu____3040 (fun uu____3043 -> (match (uu____3043) with
| (e1, uu____3047) -> begin
(p_tmEq e1)
end)) args))
end
| uu____3048 -> begin
(p_tmEq e)
end)))
and paren_if : Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun curr mine doc1 -> (match ((mine <= curr)) with
| true -> begin
doc1
end
| uu____3052 -> begin
(

let uu____3053 = (

let uu____3054 = (FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3054))
in (FStar_Pprint.group uu____3053))
end))
and p_tmEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n1 = (max_level (FStar_List.append (((colon_equals ()))::((pipe_right ()))::[]) (operatorInfix0ad12 ())))
in (p_tmEq' n1 e)))
and p_tmEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (

let uu____3079 = (

let uu____3080 = (unparen e)
in uu____3080.FStar_Parser_AST.tm)
in (match (uu____3079) with
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (((is_operatorInfix0ad12 op) || (op = "=")) || (op = "|>")) -> begin
(

let uu____3085 = (levels op)
in (match (uu____3085) with
| (left1, mine, right1) -> begin
(

let uu____3092 = (

let uu____3093 = (str op)
in (

let uu____3094 = (p_tmEq' left1 e1)
in (

let uu____3095 = (p_tmEq' right1 e2)
in (infix0 uu____3093 uu____3094 uu____3095))))
in (paren_if curr mine uu____3092))
end))
end
| FStar_Parser_AST.Op (":=", (e1)::(e2)::[]) -> begin
(

let uu____3099 = (

let uu____3100 = (p_tmEq e1)
in (

let uu____3101 = (

let uu____3102 = (

let uu____3103 = (

let uu____3104 = (p_tmEq e2)
in (op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____3104))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3103))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3102))
in (FStar_Pprint.op_Hat_Hat uu____3100 uu____3101)))
in (FStar_Pprint.group uu____3099))
end
| uu____3105 -> begin
(p_tmNoEq e)
end)))
and p_tmNoEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n1 = (max_level (((colon_colon ()))::((amp ()))::((opinfix3 ()))::((opinfix4 ()))::[]))
in (p_tmNoEq' n1 e)))
and p_tmNoEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (

let uu____3135 = (

let uu____3136 = (unparen e)
in uu____3136.FStar_Parser_AST.tm)
in (match (uu____3135) with
| FStar_Parser_AST.Construct (lid, ((e1, uu____3139))::((e2, uu____3141))::[]) when ((FStar_Ident.lid_equals lid FStar_Syntax_Const.cons_lid) && (

let uu____3151 = (is_list e)
in (not (uu____3151)))) -> begin
(

let op = "::"
in (

let uu____3153 = (levels op)
in (match (uu____3153) with
| (left1, mine, right1) -> begin
(

let uu____3160 = (

let uu____3161 = (str op)
in (

let uu____3162 = (p_tmNoEq' left1 e1)
in (

let uu____3163 = (p_tmNoEq' right1 e2)
in (infix0 uu____3161 uu____3162 uu____3163))))
in (paren_if curr mine uu____3160))
end)))
end
| FStar_Parser_AST.Sum (binders, res) -> begin
(

let op = "&"
in (

let uu____3169 = (levels op)
in (match (uu____3169) with
| (left1, mine, right1) -> begin
(

let p_dsumfst = (fun b -> (

let uu____3180 = (p_binder false b)
in (

let uu____3181 = (

let uu____3182 = (

let uu____3183 = (str "&")
in (FStar_Pprint.op_Hat_Hat uu____3183 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3182))
in (FStar_Pprint.op_Hat_Hat uu____3180 uu____3181))))
in (

let uu____3184 = (

let uu____3185 = (FStar_Pprint.concat_map p_dsumfst binders)
in (

let uu____3186 = (p_tmNoEq' right1 res)
in (FStar_Pprint.op_Hat_Hat uu____3185 uu____3186)))
in (paren_if curr mine uu____3184)))
end)))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (is_operatorInfix34 op) -> begin
(

let uu____3191 = (levels op)
in (match (uu____3191) with
| (left1, mine, right1) -> begin
(

let uu____3198 = (

let uu____3199 = (str op)
in (

let uu____3200 = (p_tmNoEq' left1 e1)
in (

let uu____3201 = (p_tmNoEq' right1 e2)
in (infix0 uu____3199 uu____3200 uu____3201))))
in (paren_if curr mine uu____3198))
end))
end
| FStar_Parser_AST.Op ("-", (e1)::[]) -> begin
(

let uu____3204 = (levels "-")
in (match (uu____3204) with
| (left1, mine, right1) -> begin
(

let uu____3211 = (p_tmNoEq' mine e1)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____3211))
end))
end
| FStar_Parser_AST.NamedTyp (lid, e1) -> begin
(

let uu____3214 = (

let uu____3215 = (p_lidentOrUnderscore lid)
in (

let uu____3216 = (

let uu____3217 = (p_appTerm e1)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____3217))
in (FStar_Pprint.op_Hat_Slash_Hat uu____3215 uu____3216)))
in (FStar_Pprint.group uu____3214))
end
| FStar_Parser_AST.Refine (b, phi) -> begin
(p_refinedBinder b phi)
end
| FStar_Parser_AST.Record (with_opt, record_fields) -> begin
(

let uu____3230 = (

let uu____3231 = (default_or_map FStar_Pprint.empty p_with_clause with_opt)
in (

let uu____3232 = (

let uu____3233 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (FStar_Pprint.separate_map uu____3233 p_simpleDef record_fields))
in (FStar_Pprint.op_Hat_Hat uu____3231 uu____3232)))
in (braces_with_nesting uu____3230))
end
| FStar_Parser_AST.Op ("~", (e1)::[]) -> begin
(

let uu____3238 = (

let uu____3239 = (str "~")
in (

let uu____3240 = (p_atomicTerm e1)
in (FStar_Pprint.op_Hat_Hat uu____3239 uu____3240)))
in (FStar_Pprint.group uu____3238))
end
| uu____3241 -> begin
(p_appTerm e)
end)))
and p_with_clause : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3243 = (p_appTerm e)
in (

let uu____3244 = (

let uu____3245 = (

let uu____3246 = (str "with")
in (FStar_Pprint.op_Hat_Hat uu____3246 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3245))
in (FStar_Pprint.op_Hat_Hat uu____3243 uu____3244))))
and p_refinedBinder : FStar_Parser_AST.binder  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun b phi -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (lid, t) -> begin
(

let uu____3251 = (

let uu____3252 = (p_lident lid)
in (p_refinement b.FStar_Parser_AST.aqual uu____3252 t phi))
in (soft_parens_with_nesting uu____3251))
end
| FStar_Parser_AST.TAnnotated (uu____3253) -> begin
(failwith "Is this still used ?")
end
| (FStar_Parser_AST.Variable (_)) | (FStar_Parser_AST.TVariable (_)) | (FStar_Parser_AST.NoName (_)) -> begin
(

let uu____3259 = (

let uu____3260 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" uu____3260))
in (failwith uu____3259))
end))
and p_simpleDef : (FStar_Ident.lid * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun uu____3261 -> (match (uu____3261) with
| (lid, e) -> begin
(

let uu____3266 = (

let uu____3267 = (p_qlident lid)
in (

let uu____3268 = (

let uu____3269 = (p_tmIff e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____3269))
in (FStar_Pprint.op_Hat_Slash_Hat uu____3267 uu____3268)))
in (FStar_Pprint.group uu____3266))
end))
and p_appTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3271 = (

let uu____3272 = (unparen e)
in uu____3272.FStar_Parser_AST.tm)
in (match (uu____3271) with
| FStar_Parser_AST.App (uu____3273) when (is_general_application e) -> begin
(

let uu____3277 = (head_and_args e)
in (match (uu____3277) with
| (head1, args) -> begin
(

let uu____3291 = (

let uu____3297 = (FStar_ST.read should_print_fs_typ_app)
in (match (uu____3297) with
| true -> begin
(

let uu____3305 = (FStar_Util.take (fun uu____3316 -> (match (uu____3316) with
| (uu____3319, aq) -> begin
(aq = FStar_Parser_AST.FsTypApp)
end)) args)
in (match (uu____3305) with
| (fs_typ_args, args1) -> begin
(

let uu____3340 = (

let uu____3341 = (p_indexingTerm head1)
in (

let uu____3342 = (

let uu____3343 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (soft_surround_separate_map (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.empty FStar_Pprint.langle uu____3343 FStar_Pprint.rangle p_fsTypArg fs_typ_args))
in (FStar_Pprint.op_Hat_Hat uu____3341 uu____3342)))
in ((uu____3340), (args1)))
end))
end
| uu____3349 -> begin
(

let uu____3350 = (p_indexingTerm head1)
in ((uu____3350), (args)))
end))
in (match (uu____3291) with
| (head_doc, args1) -> begin
(

let uu____3362 = (

let uu____3363 = (FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space)
in (soft_surround_separate_map (Prims.parse_int "2") (Prims.parse_int "0") head_doc uu____3363 break1 FStar_Pprint.empty p_argTerm args1))
in (FStar_Pprint.group uu____3362))
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

let uu____3383 = (

let uu____3384 = (p_quident lid)
in (

let uu____3385 = (p_argTerm arg)
in (FStar_Pprint.op_Hat_Slash_Hat uu____3384 uu____3385)))
in (FStar_Pprint.group uu____3383))
end
| (hd1)::tl1 -> begin
(

let uu____3395 = (

let uu____3396 = (

let uu____3397 = (

let uu____3398 = (p_quident lid)
in (

let uu____3399 = (p_argTerm hd1)
in (prefix2 uu____3398 uu____3399)))
in (FStar_Pprint.group uu____3397))
in (

let uu____3400 = (

let uu____3401 = (FStar_Pprint.separate_map break1 p_argTerm tl1)
in (jump2 uu____3401))
in (FStar_Pprint.op_Hat_Hat uu____3396 uu____3400)))
in (FStar_Pprint.group uu____3395))
end)
end
| uu____3404 -> begin
(p_indexingTerm e)
end)))
and p_argTerm : (FStar_Parser_AST.term * FStar_Parser_AST.imp)  ->  FStar_Pprint.document = (fun arg_imp -> (match (arg_imp) with
| ({FStar_Parser_AST.tm = FStar_Parser_AST.Uvar (uu____3408); FStar_Parser_AST.range = uu____3409; FStar_Parser_AST.level = uu____3410}, FStar_Parser_AST.UnivApp) -> begin
(p_univar (Prims.fst arg_imp))
end
| (u, FStar_Parser_AST.UnivApp) -> begin
(p_universe u)
end
| (e, FStar_Parser_AST.FsTypApp) -> begin
((FStar_Util.print_warning "Unexpected FsTypApp, output might not be formatted correctly.\n");
(

let uu____3414 = (p_indexingTerm e)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.langle uu____3414 FStar_Pprint.rangle));
)
end
| (e, FStar_Parser_AST.Hash) -> begin
(

let uu____3416 = (str "#")
in (

let uu____3417 = (p_indexingTerm e)
in (FStar_Pprint.op_Hat_Hat uu____3416 uu____3417)))
end
| (e, FStar_Parser_AST.Nothing) -> begin
(p_indexingTerm e)
end))
and p_fsTypArg : (FStar_Parser_AST.term * FStar_Parser_AST.imp)  ->  FStar_Pprint.document = (fun uu____3419 -> (match (uu____3419) with
| (e, uu____3423) -> begin
(p_indexingTerm e)
end))
and p_indexingTerm_aux : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun exit1 e -> (

let uu____3428 = (

let uu____3429 = (unparen e)
in uu____3429.FStar_Parser_AST.tm)
in (match (uu____3428) with
| FStar_Parser_AST.Op (".()", (e1)::(e2)::[]) -> begin
(

let uu____3433 = (

let uu____3434 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (

let uu____3435 = (

let uu____3436 = (

let uu____3437 = (p_term e2)
in (soft_parens_with_nesting uu____3437))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3436))
in (FStar_Pprint.op_Hat_Hat uu____3434 uu____3435)))
in (FStar_Pprint.group uu____3433))
end
| FStar_Parser_AST.Op (".[]", (e1)::(e2)::[]) -> begin
(

let uu____3441 = (

let uu____3442 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (

let uu____3443 = (

let uu____3444 = (

let uu____3445 = (p_term e2)
in (soft_brackets_with_nesting uu____3445))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3444))
in (FStar_Pprint.op_Hat_Hat uu____3442 uu____3443)))
in (FStar_Pprint.group uu____3441))
end
| uu____3446 -> begin
(exit1 e)
end)))
and p_indexingTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_indexingTerm_aux p_atomicTerm e))
and p_atomicTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3449 = (

let uu____3450 = (unparen e)
in uu____3450.FStar_Parser_AST.tm)
in (match (uu____3449) with
| FStar_Parser_AST.LetOpen (lid, e1) -> begin
(

let uu____3453 = (p_quident lid)
in (

let uu____3454 = (

let uu____3455 = (

let uu____3456 = (p_term e1)
in (soft_parens_with_nesting uu____3456))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3455))
in (FStar_Pprint.op_Hat_Hat uu____3453 uu____3454)))
end
| FStar_Parser_AST.Name (lid) -> begin
(p_quident lid)
end
| FStar_Parser_AST.Op (op, (e1)::[]) when (is_general_prefix_op op) -> begin
(

let uu____3461 = (str op)
in (

let uu____3462 = (p_atomicTerm e1)
in (FStar_Pprint.op_Hat_Hat uu____3461 uu____3462)))
end
| uu____3463 -> begin
(p_atomicTermNotQUident e)
end)))
and p_atomicTermNotQUident : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3465 = (

let uu____3466 = (unparen e)
in uu____3466.FStar_Parser_AST.tm)
in (match (uu____3465) with
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
| FStar_Parser_AST.Op (op, (e1)::[]) when (is_general_prefix_op op) -> begin
(

let uu____3475 = (str op)
in (

let uu____3476 = (p_atomicTermNotQUident e1)
in (FStar_Pprint.op_Hat_Hat uu____3475 uu____3476)))
end
| FStar_Parser_AST.Op (op, []) -> begin
(

let uu____3479 = (

let uu____3480 = (

let uu____3481 = (str op)
in (

let uu____3482 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat uu____3481 uu____3482)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3480))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3479))
end
| FStar_Parser_AST.Construct (lid, args) when (is_dtuple_constructor lid) -> begin
(

let uu____3491 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (

let uu____3492 = (

let uu____3493 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (

let uu____3494 = (FStar_List.map Prims.fst args)
in (FStar_Pprint.separate_map uu____3493 p_tmEq uu____3494)))
in (

let uu____3498 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____3491 uu____3492 uu____3498))))
end
| FStar_Parser_AST.Project (e1, lid) -> begin
(

let uu____3501 = (

let uu____3502 = (p_atomicTermNotQUident e1)
in (

let uu____3503 = (

let uu____3504 = (p_qlident lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3504))
in (FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0") uu____3502 uu____3503)))
in (FStar_Pprint.group uu____3501))
end
| uu____3505 -> begin
(p_projectionLHS e)
end)))
and p_projectionLHS : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3507 = (

let uu____3508 = (unparen e)
in uu____3508.FStar_Parser_AST.tm)
in (match (uu____3507) with
| FStar_Parser_AST.Var (lid) -> begin
(p_qlident lid)
end
| FStar_Parser_AST.Projector (constr_lid, field_lid) -> begin
(

let uu____3512 = (p_quident constr_lid)
in (

let uu____3513 = (

let uu____3514 = (

let uu____3515 = (p_lident field_lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3515))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____3514))
in (FStar_Pprint.op_Hat_Hat uu____3512 uu____3513)))
end
| FStar_Parser_AST.Discrim (constr_lid) -> begin
(

let uu____3517 = (p_quident constr_lid)
in (FStar_Pprint.op_Hat_Hat uu____3517 FStar_Pprint.qmark))
end
| FStar_Parser_AST.Paren (e1) -> begin
(

let uu____3519 = (p_term e1)
in (soft_parens_with_nesting uu____3519))
end
| uu____3520 when (is_array e) -> begin
(

let es = (extract_from_list e)
in (

let uu____3523 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar)
in (

let uu____3524 = (

let uu____3525 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (separate_map_or_flow uu____3525 p_noSeqTerm es))
in (

let uu____3526 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") uu____3523 uu____3524 uu____3526)))))
end
| uu____3527 when (is_list e) -> begin
(

let uu____3528 = (

let uu____3529 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (

let uu____3530 = (extract_from_list e)
in (separate_map_or_flow uu____3529 p_noSeqTerm uu____3530)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket uu____3528 FStar_Pprint.rbracket))
end
| uu____3532 when (is_lex_list e) -> begin
(

let uu____3533 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket)
in (

let uu____3534 = (

let uu____3535 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (

let uu____3536 = (extract_from_list e)
in (separate_map_or_flow uu____3535 p_noSeqTerm uu____3536)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____3533 uu____3534 FStar_Pprint.rbracket)))
end
| uu____3538 when (is_ref_set e) -> begin
(

let es = (extract_from_ref_set e)
in (

let uu____3541 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace)
in (

let uu____3542 = (

let uu____3543 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (separate_map_or_flow uu____3543 p_appTerm es))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") uu____3541 uu____3542 FStar_Pprint.rbrace))))
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Op (_)) | (FStar_Parser_AST.Tvar (_)) | (FStar_Parser_AST.Uvar (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) | (FStar_Parser_AST.Construct (_)) | (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.App (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.LetOpen (_)) | (FStar_Parser_AST.Seq (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Ascribed (_)) | (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Project (_)) | (FStar_Parser_AST.Product (_)) | (FStar_Parser_AST.Sum (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Refine (_)) | (FStar_Parser_AST.NamedTyp (_)) | (FStar_Parser_AST.Requires (_)) | (FStar_Parser_AST.Ensures (_)) | (FStar_Parser_AST.Assign (_)) | (FStar_Parser_AST.Attributes (_)) -> begin
(

let uu____3572 = (p_term e)
in (soft_parens_with_nesting uu____3572))
end
| FStar_Parser_AST.Labeled (uu____3573) -> begin
(failwith "Not valid in universe")
end)))
and p_constant : FStar_Const.sconst  ->  FStar_Pprint.document = (fun uu___141_3577 -> (match (uu___141_3577) with
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

let uu____3581 = (FStar_Pprint.doc_of_char x)
in (FStar_Pprint.squotes uu____3581))
end
| FStar_Const.Const_string (bytes, uu____3583) -> begin
(

let uu____3586 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes uu____3586))
end
| FStar_Const.Const_bytearray (bytes, uu____3588) -> begin
(

let uu____3591 = (

let uu____3592 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes uu____3592))
in (

let uu____3593 = (str "B")
in (FStar_Pprint.op_Hat_Hat uu____3591 uu____3593)))
end
| FStar_Const.Const_int (repr, sign_width_opt) -> begin
(

let signedness = (fun uu___139_3605 -> (match (uu___139_3605) with
| FStar_Const.Unsigned -> begin
(str "u")
end
| FStar_Const.Signed -> begin
FStar_Pprint.empty
end))
in (

let width = (fun uu___140_3609 -> (match (uu___140_3609) with
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

let ending = (default_or_map FStar_Pprint.empty (fun uu____3613 -> (match (uu____3613) with
| (s, w) -> begin
(

let uu____3618 = (signedness s)
in (

let uu____3619 = (width w)
in (FStar_Pprint.op_Hat_Hat uu____3618 uu____3619)))
end)) sign_width_opt)
in (

let uu____3620 = (str repr)
in (FStar_Pprint.op_Hat_Hat uu____3620 ending)))))
end
| FStar_Const.Const_range (r) -> begin
(

let uu____3622 = (FStar_Range.string_of_range r)
in (str uu____3622))
end
| FStar_Const.Const_reify -> begin
(str "reify")
end
| FStar_Const.Const_reflect (lid) -> begin
(

let uu____3624 = (p_quident lid)
in (

let uu____3625 = (

let uu____3626 = (

let uu____3627 = (str "reflect")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3627))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____3626))
in (FStar_Pprint.op_Hat_Hat uu____3624 uu____3625)))
end))
and p_universe : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (

let uu____3629 = (str "u#")
in (

let uu____3630 = (p_atomicUniverse u)
in (FStar_Pprint.op_Hat_Hat uu____3629 uu____3630))))
and p_universeFrom : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (

let uu____3632 = (

let uu____3633 = (unparen u)
in uu____3633.FStar_Parser_AST.tm)
in (match (uu____3632) with
| FStar_Parser_AST.Op ("+", (u1)::(u2)::[]) -> begin
(

let uu____3637 = (

let uu____3638 = (p_universeFrom u1)
in (

let uu____3639 = (

let uu____3640 = (p_universeFrom u2)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____3640))
in (FStar_Pprint.op_Hat_Slash_Hat uu____3638 uu____3639)))
in (FStar_Pprint.group uu____3637))
end
| FStar_Parser_AST.App (uu____3641) -> begin
(

let uu____3645 = (head_and_args u)
in (match (uu____3645) with
| (head1, args) -> begin
(

let uu____3659 = (

let uu____3660 = (unparen head1)
in uu____3660.FStar_Parser_AST.tm)
in (match (uu____3659) with
| FStar_Parser_AST.Var (maybe_max_lid) when (FStar_Ident.lid_equals maybe_max_lid FStar_Syntax_Const.max_lid) -> begin
(

let uu____3662 = (

let uu____3663 = (p_qlident FStar_Syntax_Const.max_lid)
in (

let uu____3664 = (FStar_Pprint.separate_map FStar_Pprint.space (fun uu____3667 -> (match (uu____3667) with
| (u1, uu____3671) -> begin
(p_atomicUniverse u1)
end)) args)
in (op_Hat_Slash_Plus_Hat uu____3663 uu____3664)))
in (FStar_Pprint.group uu____3662))
end
| uu____3672 -> begin
(

let uu____3673 = (

let uu____3674 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" uu____3674))
in (failwith uu____3673))
end))
end))
end
| uu____3675 -> begin
(p_atomicUniverse u)
end)))
and p_atomicUniverse : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (

let uu____3677 = (

let uu____3678 = (unparen u)
in uu____3678.FStar_Parser_AST.tm)
in (match (uu____3677) with
| FStar_Parser_AST.Wild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (r, sw)) -> begin
(p_constant (FStar_Const.Const_int (((r), (sw)))))
end
| FStar_Parser_AST.Uvar (uu____3690) -> begin
(p_univar u)
end
| FStar_Parser_AST.Paren (u1) -> begin
(

let uu____3692 = (p_universeFrom u1)
in (soft_parens_with_nesting uu____3692))
end
| (FStar_Parser_AST.Op ("+", (_)::(_)::[])) | (FStar_Parser_AST.App (_)) -> begin
(

let uu____3697 = (p_universeFrom u)
in (soft_parens_with_nesting uu____3697))
end
| uu____3698 -> begin
(

let uu____3699 = (

let uu____3700 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" uu____3700))
in (failwith uu____3699))
end)))
and p_univar : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (

let uu____3702 = (

let uu____3703 = (unparen u)
in uu____3703.FStar_Parser_AST.tm)
in (match (uu____3702) with
| FStar_Parser_AST.Uvar (id) -> begin
(str (FStar_Ident.text_of_id id))
end
| uu____3705 -> begin
(

let uu____3706 = (

let uu____3707 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Not a universe variable %s" uu____3707))
in (failwith uu____3706))
end)))


let term_to_document : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_term e))


let decl_to_document : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun e -> (p_decl e))


let modul_to_document : FStar_Parser_AST.modul  ->  FStar_Pprint.document = (fun m -> ((FStar_ST.write should_print_fs_typ_app false);
(

let res = (match (m) with
| (FStar_Parser_AST.Module (_, decls)) | (FStar_Parser_AST.Interface (_, decls, _)) -> begin
(

let uu____3729 = (FStar_All.pipe_right decls (FStar_List.map decl_to_document))
in (FStar_All.pipe_right uu____3729 (FStar_Pprint.separate FStar_Pprint.hardline)))
end)
in ((FStar_ST.write should_print_fs_typ_app false);
res;
));
))


let comments_to_document : (Prims.string * FStar_Range.range) Prims.list  ->  FStar_Pprint.document = (fun comments -> (FStar_Pprint.separate_map FStar_Pprint.hardline (fun uu____3748 -> (match (uu____3748) with
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

let uu____3795 = (match (ds) with
| ({FStar_Parser_AST.d = FStar_Parser_AST.Pragma (FStar_Parser_AST.LightOff); FStar_Parser_AST.drange = uu____3802; FStar_Parser_AST.doc = uu____3803; FStar_Parser_AST.quals = uu____3804; FStar_Parser_AST.attrs = uu____3805})::uu____3806 -> begin
(

let d0 = (FStar_List.hd ds)
in (

let uu____3810 = (

let uu____3812 = (

let uu____3814 = (FStar_List.tl ds)
in (d)::uu____3814)
in (d0)::uu____3812)
in ((uu____3810), (d0.FStar_Parser_AST.drange))))
end
| uu____3817 -> begin
(((d)::ds), (d.FStar_Parser_AST.drange))
end)
in (match (uu____3795) with
| (decls1, first_range) -> begin
(

let extract_decl_range = (fun d1 -> d1.FStar_Parser_AST.drange)
in ((FStar_ST.write comment_stack comments);
(

let initial_comment = (

let uu____3840 = (FStar_Range.start_of_range first_range)
in (place_comments_until_pos (Prims.parse_int "0") (Prims.parse_int "1") uu____3840 FStar_Pprint.empty))
in (

let doc1 = (separate_map_with_comments FStar_Pprint.empty FStar_Pprint.empty decl_to_document decls1 extract_decl_range)
in (

let comments1 = (FStar_ST.read comment_stack)
in ((FStar_ST.write comment_stack []);
(FStar_ST.write should_print_fs_typ_app false);
(

let uu____3862 = (FStar_Pprint.op_Hat_Hat initial_comment doc1)
in ((uu____3862), (comments1)));
))));
))
end))
end);
)))




