
open Prims

let should_unparen : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref true)


let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (

let uu____7 = (

let uu____8 = (FStar_ST.read should_unparen)
in (not (uu____8)))
in (match (uu____7) with
| true -> begin
t
end
| uu____11 -> begin
(match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| uu____13 -> begin
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

let uu____95 = (

let uu____96 = (

let uu____97 = (FStar_Pprint.op_Hat_Hat sep break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____97))
in (FStar_Pprint.separate_map uu____96 f l))
in (FStar_Pprint.group uu____95)))


let precede_break_separate_map = (fun prec sep f l -> (

let uu____127 = (

let uu____128 = (FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space)
in (

let uu____129 = (

let uu____130 = (FStar_List.hd l)
in (FStar_All.pipe_right uu____130 f))
in (FStar_Pprint.precede uu____128 uu____129)))
in (

let uu____131 = (

let uu____132 = (FStar_List.tl l)
in (FStar_Pprint.concat_map (fun x -> (

let uu____135 = (

let uu____136 = (

let uu____137 = (f x)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____137))
in (FStar_Pprint.op_Hat_Hat sep uu____136))
in (FStar_Pprint.op_Hat_Hat break1 uu____135))) uu____132))
in (FStar_Pprint.op_Hat_Hat uu____127 uu____131))))


let concat_break_map = (fun f l -> (

let uu____157 = (FStar_Pprint.concat_map (fun x -> (

let uu____159 = (f x)
in (FStar_Pprint.op_Hat_Hat uu____159 break1))) l)
in (FStar_Pprint.group uu____157)))


let parens_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lparen contents FStar_Pprint.rparen))


let soft_parens_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lparen contents FStar_Pprint.rparen))


let braces_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbrace contents FStar_Pprint.rbrace))


let soft_braces_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbrace contents FStar_Pprint.rbrace))


let brackets_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbracket contents FStar_Pprint.rbracket))


let soft_brackets_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbracket contents FStar_Pprint.rbracket))


let soft_begin_end_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (

let uu____181 = (str "begin")
in (

let uu____182 = (str "end")
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") uu____181 contents uu____182))))


let separate_map_or_flow = (fun sep f l -> (match (((FStar_List.length l) < (Prims.parse_int "10"))) with
| true -> begin
(FStar_Pprint.separate_map sep f l)
end
| uu____210 -> begin
(FStar_Pprint.flow_map sep f l)
end))


let doc_of_fsdoc : (Prims.string * (Prims.string * Prims.string) Prims.list)  ->  FStar_Pprint.document = (fun uu____218 -> (match (uu____218) with
| (comment, keywords) -> begin
(

let uu____232 = (

let uu____233 = (

let uu____235 = (str comment)
in (

let uu____236 = (

let uu____238 = (

let uu____240 = (FStar_Pprint.separate_map FStar_Pprint.comma (fun uu____243 -> (match (uu____243) with
| (k, v) -> begin
(

let uu____248 = (

let uu____250 = (str k)
in (

let uu____251 = (

let uu____253 = (

let uu____255 = (str v)
in (uu____255)::[])
in (FStar_Pprint.rarrow)::uu____253)
in (uu____250)::uu____251))
in (FStar_Pprint.concat uu____248))
end)) keywords)
in (uu____240)::[])
in (FStar_Pprint.space)::uu____238)
in (uu____235)::uu____236))
in (FStar_Pprint.concat uu____233))
in (FStar_Pprint.group uu____232))
end))


let is_unit : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____259 = (

let uu____260 = (unparen e)
in uu____260.FStar_Parser_AST.tm)
in (match (uu____259) with
| FStar_Parser_AST.Const (FStar_Const.Const_unit) -> begin
true
end
| uu____261 -> begin
false
end)))


let matches_var : FStar_Parser_AST.term  ->  FStar_Ident.ident  ->  Prims.bool = (fun t x -> (

let uu____268 = (

let uu____269 = (unparen t)
in uu____269.FStar_Parser_AST.tm)
in (match (uu____268) with
| FStar_Parser_AST.Var (y) -> begin
(x.FStar_Ident.idText = (FStar_Ident.text_of_lid y))
end
| uu____271 -> begin
false
end)))


let is_tuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Syntax_Util.is_tuple_data_lid'


let is_dtuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Syntax_Util.is_dtuple_data_lid'


let is_list_structure : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun cons_lid nil_lid -> (

let rec aux = (fun e -> (

let uu____288 = (

let uu____289 = (unparen e)
in uu____289.FStar_Parser_AST.tm)
in (match (uu____288) with
| FStar_Parser_AST.Construct (lid, []) -> begin
(FStar_Ident.lid_equals lid nil_lid)
end
| FStar_Parser_AST.Construct (lid, (uu____297)::((e2, uu____299))::[]) -> begin
((FStar_Ident.lid_equals lid cons_lid) && (aux e2))
end
| uu____311 -> begin
false
end)))
in aux))


let is_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Syntax_Const.cons_lid FStar_Syntax_Const.nil_lid)


let is_lex_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Syntax_Const.lexcons_lid FStar_Syntax_Const.lextop_lid)


let rec extract_from_list : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (

let uu____320 = (

let uu____321 = (unparen e)
in uu____321.FStar_Parser_AST.tm)
in (match (uu____320) with
| FStar_Parser_AST.Construct (uu____323, []) -> begin
[]
end
| FStar_Parser_AST.Construct (uu____329, ((e1, FStar_Parser_AST.Nothing))::((e2, FStar_Parser_AST.Nothing))::[]) -> begin
(

let uu____341 = (extract_from_list e2)
in (e1)::uu____341)
end
| uu____343 -> begin
(

let uu____344 = (

let uu____345 = (FStar_Parser_AST.term_to_string e)
in (FStar_Util.format1 "Not a list %s" uu____345))
in (failwith uu____344))
end)))


let is_array : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____350 = (

let uu____351 = (unparen e)
in uu____351.FStar_Parser_AST.tm)
in (match (uu____350) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (lid); FStar_Parser_AST.range = uu____353; FStar_Parser_AST.level = uu____354}, l, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals lid FStar_Syntax_Const.array_mk_array_lid) && (is_list l))
end
| uu____356 -> begin
false
end)))


let rec is_ref_set : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____360 = (

let uu____361 = (unparen e)
in uu____361.FStar_Parser_AST.tm)
in (match (uu____360) with
| FStar_Parser_AST.Var (maybe_empty_lid) -> begin
(FStar_Ident.lid_equals maybe_empty_lid FStar_Syntax_Const.tset_empty)
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_singleton_lid); FStar_Parser_AST.range = uu____364; FStar_Parser_AST.level = uu____365}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_ref_lid); FStar_Parser_AST.range = uu____367; FStar_Parser_AST.level = uu____368}, e, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____370; FStar_Parser_AST.level = uu____371}, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals maybe_singleton_lid FStar_Syntax_Const.tset_singleton) && (FStar_Ident.lid_equals maybe_ref_lid FStar_Syntax_Const.heap_ref))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_union_lid); FStar_Parser_AST.range = uu____373; FStar_Parser_AST.level = uu____374}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____376; FStar_Parser_AST.level = uu____377}, e2, FStar_Parser_AST.Nothing) -> begin
(((FStar_Ident.lid_equals maybe_union_lid FStar_Syntax_Const.tset_union) && (is_ref_set e1)) && (is_ref_set e2))
end
| uu____379 -> begin
false
end)))


let rec extract_from_ref_set : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (

let uu____384 = (

let uu____385 = (unparen e)
in uu____385.FStar_Parser_AST.tm)
in (match (uu____384) with
| FStar_Parser_AST.Var (uu____387) -> begin
[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (uu____388); FStar_Parser_AST.range = uu____389; FStar_Parser_AST.level = uu____390}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (uu____391); FStar_Parser_AST.range = uu____392; FStar_Parser_AST.level = uu____393}, e, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____395; FStar_Parser_AST.level = uu____396}, FStar_Parser_AST.Nothing) -> begin
(e)::[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (uu____397); FStar_Parser_AST.range = uu____398; FStar_Parser_AST.level = uu____399}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____401; FStar_Parser_AST.level = uu____402}, e2, FStar_Parser_AST.Nothing) -> begin
(

let uu____404 = (extract_from_ref_set e1)
in (

let uu____406 = (extract_from_ref_set e2)
in (FStar_List.append uu____404 uu____406)))
end
| uu____408 -> begin
(

let uu____409 = (

let uu____410 = (FStar_Parser_AST.term_to_string e)
in (FStar_Util.format1 "Not a ref set %s" uu____410))
in (failwith uu____409))
end)))


let is_general_application : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____415 = ((is_array e) || (is_ref_set e))
in (not (uu____415))))


let is_general_construction : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____419 = ((is_list e) || (is_lex_list e))
in (not (uu____419))))


let is_general_prefix_op : Prims.string  ->  Prims.bool = (fun op -> (op <> "~"))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun e -> (

let rec aux = (fun e acc -> (

let uu____449 = (

let uu____450 = (unparen e)
in uu____450.FStar_Parser_AST.tm)
in (match (uu____449) with
| FStar_Parser_AST.App (head, arg, imp) -> begin
(aux head ((((arg), (imp)))::acc))
end
| uu____461 -> begin
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
| uu____470 -> begin
false
end))


let uu___is_Right : associativity  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Right -> begin
true
end
| uu____474 -> begin
false
end))


let uu___is_NonAssoc : associativity  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NonAssoc -> begin
true
end
| uu____478 -> begin
false
end))


type token =
(FStar_Char.char, Prims.string) FStar_Util.either


type associativity_level =
(associativity * token Prims.list)


let token_to_string : (FStar_BaseTypes.char, Prims.string) FStar_Util.either  ->  Prims.string = (fun uu___115_488 -> (match (uu___115_488) with
| FStar_Util.Inl (c) -> begin
(Prims.strcat (FStar_Util.string_of_char c) ".*")
end
| FStar_Util.Inr (s) -> begin
s
end))


let matches_token : Prims.string  ->  (FStar_Char.char, Prims.string) FStar_Util.either  ->  Prims.bool = (fun s uu___116_500 -> (match (uu___116_500) with
| FStar_Util.Inl (c) -> begin
(

let uu____504 = (FStar_String.get s (Prims.parse_int "0"))
in (uu____504 = c))
end
| FStar_Util.Inr (s') -> begin
(s = s')
end))


let matches_level = (fun s uu____522 -> (match (uu____522) with
| (assoc_levels, tokens) -> begin
(

let uu____536 = (FStar_List.tryFind (matches_token s) tokens)
in (uu____536 <> None))
end))


let opinfix4 = (fun uu____554 -> ((Right), ((FStar_Util.Inr ("**"))::[])))


let opinfix3 = (fun uu____569 -> ((Left), ((FStar_Util.Inl ('*'))::(FStar_Util.Inl ('/'))::(FStar_Util.Inl ('%'))::[])))


let opinfix2 = (fun uu____588 -> ((Left), ((FStar_Util.Inl ('+'))::(FStar_Util.Inl ('-'))::[])))


let minus_lvl = (fun uu____605 -> ((Left), ((FStar_Util.Inr ("-"))::[])))


let opinfix1 = (fun uu____620 -> ((Right), ((FStar_Util.Inl ('@'))::(FStar_Util.Inl ('^'))::[])))


let pipe_right = (fun uu____637 -> ((Left), ((FStar_Util.Inr ("|>"))::[])))


let opinfix0d = (fun uu____652 -> ((Left), ((FStar_Util.Inl ('$'))::[])))


let opinfix0c = (fun uu____667 -> ((Left), ((FStar_Util.Inl ('='))::(FStar_Util.Inl ('<'))::(FStar_Util.Inl ('>'))::[])))


let equal = (fun uu____686 -> ((Left), ((FStar_Util.Inr ("="))::[])))


let opinfix0b = (fun uu____701 -> ((Left), ((FStar_Util.Inl ('&'))::[])))


let opinfix0a = (fun uu____716 -> ((Left), ((FStar_Util.Inl ('|'))::[])))


let colon_equals = (fun uu____731 -> ((NonAssoc), ((FStar_Util.Inr (":="))::[])))


let amp = (fun uu____746 -> ((Right), ((FStar_Util.Inr ("&"))::[])))


let colon_colon = (fun uu____761 -> ((Right), ((FStar_Util.Inr ("::"))::[])))


let level_associativity_spec : (associativity * (FStar_Char.char, Prims.string) FStar_Util.either Prims.list) Prims.list = ((opinfix4 ()))::((opinfix3 ()))::((opinfix2 ()))::((opinfix1 ()))::((pipe_right ()))::((opinfix0d ()))::((opinfix0c ()))::((opinfix0b ()))::((opinfix0a ()))::((colon_equals ()))::((amp ()))::((colon_colon ()))::[]


let level_table : ((Prims.int * Prims.int * Prims.int) * (FStar_Char.char, Prims.string) FStar_Util.either Prims.list) Prims.list = (

let levels_from_associativity = (fun l uu___117_858 -> (match (uu___117_858) with
| Left -> begin
((l), (l), ((l - (Prims.parse_int "1"))))
end
| Right -> begin
(((l - (Prims.parse_int "1"))), (l), (l))
end
| NonAssoc -> begin
((l), (l), (l))
end))
in (FStar_List.mapi (fun i uu____876 -> (match (uu____876) with
| (assoc, tokens) -> begin
(((levels_from_associativity i assoc)), (tokens))
end)) level_associativity_spec))


let assign_levels : associativity_level Prims.list  ->  Prims.string  ->  (Prims.int * Prims.int * Prims.int) = (fun token_associativity_spec s -> (

let uu____918 = (FStar_List.tryFind (matches_level s) level_table)
in (match (uu____918) with
| Some (assoc_levels, uu____943) -> begin
assoc_levels
end
| uu____964 -> begin
(failwith (Prims.strcat "Unrecognized operator " s))
end)))


let max : Prims.int  ->  Prims.int  ->  Prims.int = (fun k1 k2 -> (match ((k1 > k2)) with
| true -> begin
k1
end
| uu____983 -> begin
k2
end))


let max_level = (fun l -> (

let find_level_and_max = (fun n level -> (

let uu____1020 = (FStar_List.tryFind (fun uu____1038 -> (match (uu____1038) with
| (uu____1047, tokens) -> begin
(tokens = (Prims.snd level))
end)) level_table)
in (match (uu____1020) with
| Some ((uu____1067, l, uu____1069), uu____1070) -> begin
(max n l)
end
| None -> begin
(

let uu____1096 = (

let uu____1097 = (

let uu____1098 = (FStar_List.map token_to_string (Prims.snd level))
in (FStar_String.concat "," uu____1098))
in (FStar_Util.format1 "Undefined associativity level %s" uu____1097))
in (failwith uu____1096))
end)))
in (FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l)))


let levels : Prims.string  ->  (Prims.int * Prims.int * Prims.int) = (assign_levels level_associativity_spec)


let operatorInfix0ad12 = (fun uu____1123 -> ((opinfix0a ()))::((opinfix0b ()))::((opinfix0c ()))::((opinfix0d ()))::((opinfix1 ()))::((opinfix2 ()))::[])


let is_operatorInfix0ad12 : Prims.string  ->  Prims.bool = (fun op -> (

let uu____1162 = (FStar_List.tryFind (matches_level op) (operatorInfix0ad12 ()))
in (uu____1162 <> None)))


let is_operatorInfix34 : Prims.string  ->  Prims.bool = (

let opinfix34 = ((opinfix3 ()))::((opinfix4 ()))::[]
in (fun op -> (

let uu____1210 = (FStar_List.tryFind (matches_level op) opinfix34)
in (uu____1210 <> None))))


let comment_stack : (Prims.string * FStar_Range.range) Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let with_comment = (fun printer tm tmrange -> (

let rec comments_before_pos = (fun acc print_pos lookahead_pos -> (

let uu____1278 = (FStar_ST.read comment_stack)
in (match (uu____1278) with
| [] -> begin
((acc), (false))
end
| ((comment, crange))::cs -> begin
(

let uu____1299 = (FStar_Range.range_before_pos crange print_pos)
in (match (uu____1299) with
| true -> begin
((FStar_ST.write comment_stack cs);
(

let uu____1308 = (

let uu____1309 = (

let uu____1310 = (str comment)
in (FStar_Pprint.op_Hat_Hat uu____1310 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat acc uu____1309))
in (comments_before_pos uu____1308 print_pos lookahead_pos));
)
end
| uu____1311 -> begin
(

let uu____1312 = (FStar_Range.range_before_pos crange lookahead_pos)
in ((acc), (uu____1312)))
end))
end)))
in (

let uu____1313 = (

let uu____1316 = (

let uu____1317 = (FStar_Range.start_of_range tmrange)
in (FStar_Range.end_of_line uu____1317))
in (

let uu____1318 = (FStar_Range.end_of_range tmrange)
in (comments_before_pos FStar_Pprint.empty uu____1316 uu____1318)))
in (match (uu____1313) with
| (comments, has_lookahead) -> begin
(

let printed_e = (printer tm)
in (

let comments = (match (has_lookahead) with
| true -> begin
(

let pos = (FStar_Range.end_of_range tmrange)
in (

let uu____1324 = (comments_before_pos comments pos pos)
in (Prims.fst uu____1324)))
end
| uu____1327 -> begin
comments
end)
in (

let uu____1328 = (FStar_Pprint.op_Hat_Hat comments printed_e)
in (FStar_Pprint.group uu____1328))))
end))))


let rec p_decl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (

let uu____1570 = (

let uu____1571 = (FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc)
in (

let uu____1572 = (

let uu____1573 = (p_attributes d.FStar_Parser_AST.attrs)
in (

let uu____1574 = (

let uu____1575 = (p_qualifiers d.FStar_Parser_AST.quals)
in (

let uu____1576 = (

let uu____1577 = (p_rawDecl d)
in (FStar_Pprint.op_Hat_Hat (match ((d.FStar_Parser_AST.quals = [])) with
| true -> begin
FStar_Pprint.empty
end
| uu____1578 -> begin
break1
end) uu____1577))
in (FStar_Pprint.op_Hat_Hat uu____1575 uu____1576)))
in (FStar_Pprint.op_Hat_Hat uu____1573 uu____1574)))
in (FStar_Pprint.op_Hat_Hat uu____1571 uu____1572)))
in (FStar_Pprint.group uu____1570)))
and p_attributes : FStar_Parser_AST.attributes_  ->  FStar_Pprint.document = (fun attrs -> (

let uu____1580 = (

let uu____1581 = (str "@")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____1581))
in (

let uu____1582 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline)
in (FStar_Pprint.surround_separate_map (Prims.parse_int "0") (Prims.parse_int "2") FStar_Pprint.empty uu____1580 FStar_Pprint.space uu____1582 p_atomicTerm attrs))))
and p_fsdoc : FStar_Parser_AST.fsdoc  ->  FStar_Pprint.document = (fun uu____1583 -> (match (uu____1583) with
| (doc, kwd_args) -> begin
(

let kwd_args_doc = (match (kwd_args) with
| [] -> begin
FStar_Pprint.empty
end
| kwd_args -> begin
(

let process_kwd_arg = (fun uu____1604 -> (match (uu____1604) with
| (kwd, arg) -> begin
(

let uu____1609 = (str "@")
in (

let uu____1610 = (

let uu____1611 = (str kwd)
in (

let uu____1612 = (

let uu____1613 = (str arg)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1613))
in (FStar_Pprint.op_Hat_Hat uu____1611 uu____1612)))
in (FStar_Pprint.op_Hat_Hat uu____1609 uu____1610)))
end))
in (

let uu____1614 = (

let uu____1615 = (FStar_Pprint.separate_map FStar_Pprint.hardline process_kwd_arg kwd_args)
in (FStar_Pprint.op_Hat_Hat uu____1615 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____1614)))
end)
in (

let uu____1618 = (

let uu____1619 = (

let uu____1620 = (

let uu____1621 = (

let uu____1622 = (str doc)
in (

let uu____1623 = (

let uu____1624 = (

let uu____1625 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1625))
in (FStar_Pprint.op_Hat_Hat kwd_args_doc uu____1624))
in (FStar_Pprint.op_Hat_Hat uu____1622 uu____1623)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1621))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1620))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____1619))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____1618)))
end))
and p_rawDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Open (uid) -> begin
(

let uu____1628 = (

let uu____1629 = (str "open")
in (

let uu____1630 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat uu____1629 uu____1630)))
in (FStar_Pprint.group uu____1628))
end
| FStar_Parser_AST.Include (uid) -> begin
(

let uu____1632 = (

let uu____1633 = (str "include")
in (

let uu____1634 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat uu____1633 uu____1634)))
in (FStar_Pprint.group uu____1632))
end
| FStar_Parser_AST.ModuleAbbrev (uid1, uid2) -> begin
(

let uu____1637 = (

let uu____1638 = (str "module")
in (

let uu____1639 = (

let uu____1640 = (

let uu____1641 = (p_uident uid1)
in (

let uu____1642 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____1641 uu____1642)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1640))
in (FStar_Pprint.op_Hat_Hat uu____1638 uu____1639)))
in (

let uu____1643 = (p_quident uid2)
in (op_Hat_Slash_Plus_Hat uu____1637 uu____1643)))
end
| FStar_Parser_AST.TopLevelModule (uid) -> begin
(

let uu____1645 = (

let uu____1646 = (str "module")
in (

let uu____1647 = (

let uu____1648 = (p_quident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1648))
in (FStar_Pprint.op_Hat_Hat uu____1646 uu____1647)))
in (FStar_Pprint.group uu____1645))
end
| FStar_Parser_AST.KindAbbrev (uu____1649) -> begin
(failwith "Deprecated, please stop throwing your old stuff at me !")
end
| FStar_Parser_AST.Tycon (true, ((FStar_Parser_AST.TyconAbbrev (uid, tpars, None, t), None))::[]) -> begin
(

let effect_prefix_doc = (

let uu____1672 = (str "effect")
in (

let uu____1673 = (

let uu____1674 = (p_uident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1674))
in (FStar_Pprint.op_Hat_Hat uu____1672 uu____1673)))
in (

let uu____1675 = (

let uu____1676 = (p_typars tpars)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") effect_prefix_doc uu____1676 FStar_Pprint.equals))
in (

let uu____1677 = (p_typ t)
in (op_Hat_Slash_Plus_Hat uu____1675 uu____1677))))
end
| FStar_Parser_AST.Tycon (false, tcdefs) -> begin
(

let uu____1687 = (str "type")
in (

let uu____1688 = (str "and")
in (precede_break_separate_map uu____1687 uu____1688 p_fsdocTypeDeclPairs tcdefs)))
end
| FStar_Parser_AST.TopLevelLet (q, lbs) -> begin
(

let let_doc = (

let uu____1701 = (str "let")
in (

let uu____1702 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat uu____1701 uu____1702)))
in (

let uu____1703 = (str "and")
in (precede_break_separate_map let_doc uu____1703 p_letbinding lbs)))
end
| FStar_Parser_AST.Val (lid, t) -> begin
(

let uu____1708 = (

let uu____1709 = (str "val")
in (

let uu____1710 = (

let uu____1711 = (

let uu____1712 = (p_lident lid)
in (

let uu____1713 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat uu____1712 uu____1713)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1711))
in (FStar_Pprint.op_Hat_Hat uu____1709 uu____1710)))
in (

let uu____1714 = (p_typ t)
in (op_Hat_Slash_Plus_Hat uu____1708 uu____1714)))
end
| FStar_Parser_AST.Assume (id, t) -> begin
(

let decl_keyword = (

let uu____1718 = (

let uu____1719 = (FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_All.pipe_right uu____1719 FStar_Util.is_upper))
in (match (uu____1718) with
| true -> begin
FStar_Pprint.empty
end
| uu____1720 -> begin
(

let uu____1721 = (str "val")
in (FStar_Pprint.op_Hat_Hat uu____1721 FStar_Pprint.space))
end))
in (

let uu____1722 = (

let uu____1723 = (

let uu____1724 = (p_ident id)
in (

let uu____1725 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat uu____1724 uu____1725)))
in (FStar_Pprint.op_Hat_Hat decl_keyword uu____1723))
in (

let uu____1726 = (p_typ t)
in (op_Hat_Slash_Plus_Hat uu____1722 uu____1726))))
end
| FStar_Parser_AST.Exception (uid, t_opt) -> begin
(

let uu____1731 = (str "exception")
in (

let uu____1732 = (

let uu____1733 = (

let uu____1734 = (p_uident uid)
in (

let uu____1735 = (FStar_Pprint.optional (fun t -> (

let uu____1737 = (str "of")
in (

let uu____1738 = (p_typ t)
in (op_Hat_Slash_Plus_Hat uu____1737 uu____1738)))) t_opt)
in (FStar_Pprint.op_Hat_Hat uu____1734 uu____1735)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1733))
in (FStar_Pprint.op_Hat_Hat uu____1731 uu____1732)))
end
| FStar_Parser_AST.NewEffect (ne) -> begin
(

let uu____1740 = (str "new_effect")
in (

let uu____1741 = (

let uu____1742 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1742))
in (FStar_Pprint.op_Hat_Hat uu____1740 uu____1741)))
end
| FStar_Parser_AST.SubEffect (se) -> begin
(

let uu____1744 = (str "sub_effect")
in (

let uu____1745 = (

let uu____1746 = (p_subEffect se)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1746))
in (FStar_Pprint.op_Hat_Hat uu____1744 uu____1745)))
end
| FStar_Parser_AST.NewEffectForFree (ne) -> begin
(

let uu____1748 = (str "new_effect_for_free")
in (

let uu____1749 = (

let uu____1750 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1750))
in (FStar_Pprint.op_Hat_Hat uu____1748 uu____1749)))
end
| FStar_Parser_AST.Pragma (p) -> begin
(p_pragma p)
end
| FStar_Parser_AST.Fsdoc (doc) -> begin
(

let uu____1753 = (p_fsdoc doc)
in (FStar_Pprint.op_Hat_Hat uu____1753 FStar_Pprint.hardline))
end
| FStar_Parser_AST.Main (uu____1754) -> begin
(failwith "*Main declaration* : Is that really still in use ??")
end
| FStar_Parser_AST.Tycon (true, uu____1755) -> begin
(failwith "Effect abbreviation is expected to be defined by an abbreviation")
end))
and p_pragma : FStar_Parser_AST.pragma  ->  FStar_Pprint.document = (fun uu___118_1764 -> (match (uu___118_1764) with
| FStar_Parser_AST.SetOptions (s) -> begin
(

let uu____1766 = (str "#set-options")
in (

let uu____1767 = (

let uu____1768 = (

let uu____1769 = (str s)
in (FStar_Pprint.dquotes uu____1769))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1768))
in (FStar_Pprint.op_Hat_Hat uu____1766 uu____1767)))
end
| FStar_Parser_AST.ResetOptions (s_opt) -> begin
(

let uu____1772 = (str "#reset-options")
in (

let uu____1773 = (FStar_Pprint.optional (fun s -> (

let uu____1775 = (

let uu____1776 = (str s)
in (FStar_Pprint.dquotes uu____1776))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1775))) s_opt)
in (FStar_Pprint.op_Hat_Hat uu____1772 uu____1773)))
end
| FStar_Parser_AST.LightOff -> begin
(str "#light \"off\"")
end))
and p_typars : FStar_Parser_AST.binder Prims.list  ->  FStar_Pprint.document = (fun bs -> (p_binders true bs))
and p_fsdocTypeDeclPairs : (FStar_Parser_AST.tycon * FStar_Parser_AST.fsdoc Prims.option)  ->  FStar_Pprint.document = (fun uu____1779 -> (match (uu____1779) with
| (typedecl, fsdoc_opt) -> begin
(

let uu____1787 = (FStar_Pprint.optional p_fsdoc fsdoc_opt)
in (

let uu____1788 = (p_typeDecl typedecl)
in (FStar_Pprint.op_Hat_Hat uu____1787 uu____1788)))
end))
and p_typeDecl : FStar_Parser_AST.tycon  ->  FStar_Pprint.document = (fun uu___119_1789 -> (match (uu___119_1789) with
| FStar_Parser_AST.TyconAbstract (lid, bs, typ_opt) -> begin
(

let empty' = (fun uu____1800 -> FStar_Pprint.empty)
in (p_typeDeclPrefix lid bs typ_opt empty'))
end
| FStar_Parser_AST.TyconAbbrev (lid, bs, typ_opt, t) -> begin
(

let f = (fun uu____1812 -> (

let uu____1813 = (p_typ t)
in (prefix2 FStar_Pprint.equals uu____1813)))
in (p_typeDeclPrefix lid bs typ_opt f))
end
| FStar_Parser_AST.TyconRecord (lid, bs, typ_opt, record_field_decls) -> begin
(

let p_recordFieldAndComments = (fun uu____1839 -> (match (uu____1839) with
| (lid, t, doc_opt) -> begin
(

let uu____1849 = (FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range)
in (with_comment p_recordFieldDecl ((lid), (t), (doc_opt)) uu____1849))
end))
in (

let p_fields = (fun uu____1858 -> (

let uu____1859 = (

let uu____1860 = (

let uu____1861 = (

let uu____1862 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (FStar_Pprint.separate_map uu____1862 p_recordFieldAndComments record_field_decls))
in (braces_with_nesting uu____1861))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1860))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____1859)))
in (p_typeDeclPrefix lid bs typ_opt p_fields)))
end
| FStar_Parser_AST.TyconVariant (lid, bs, typ_opt, ct_decls) -> begin
(

let p_constructorBranchAndComments = (fun uu____1898 -> (match (uu____1898) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let range = (

let uu____1914 = (

let uu____1915 = (FStar_Util.map_opt t_opt (fun t -> t.FStar_Parser_AST.range))
in (FStar_Util.dflt uid.FStar_Ident.idRange uu____1915))
in (FStar_Range.extend_to_end_of_line uu____1914))
in (

let p_constructorBranch = (fun decl -> (

let uu____1934 = (

let uu____1935 = (

let uu____1936 = (p_constructorDecl decl)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1936))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____1935))
in (FStar_Pprint.group uu____1934)))
in (with_comment p_constructorBranch ((uid), (t_opt), (doc_opt), (use_of)) range)))
end))
in (

let datacon_doc = (fun uu____1948 -> (

let uu____1949 = (FStar_Pprint.separate_map break1 p_constructorBranchAndComments ct_decls)
in (FStar_Pprint.group uu____1949)))
in (p_typeDeclPrefix lid bs typ_opt (fun uu____1956 -> (

let uu____1957 = (datacon_doc ())
in (prefix2 FStar_Pprint.equals uu____1957))))))
end))
and p_typeDeclPrefix : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.knd Prims.option  ->  (Prims.unit  ->  FStar_Pprint.document)  ->  FStar_Pprint.document = (fun lid bs typ_opt cont -> (match (((bs = []) && (typ_opt = None))) with
| true -> begin
(

let uu____1968 = (p_ident lid)
in (

let uu____1969 = (

let uu____1970 = (cont ())
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1970))
in (FStar_Pprint.op_Hat_Hat uu____1968 uu____1969)))
end
| uu____1971 -> begin
(

let binders_doc = (

let uu____1973 = (p_typars bs)
in (

let uu____1974 = (FStar_Pprint.optional (fun t -> (

let uu____1976 = (

let uu____1977 = (

let uu____1978 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1978))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____1977))
in (FStar_Pprint.op_Hat_Hat break1 uu____1976))) typ_opt)
in (FStar_Pprint.op_Hat_Hat uu____1973 uu____1974)))
in (

let uu____1979 = (p_ident lid)
in (

let uu____1980 = (cont ())
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____1979 binders_doc uu____1980))))
end))
and p_recordFieldDecl : (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc Prims.option)  ->  FStar_Pprint.document = (fun uu____1981 -> (match (uu____1981) with
| (lid, t, doc_opt) -> begin
(

let uu____1991 = (

let uu____1992 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (

let uu____1993 = (

let uu____1994 = (p_lident lid)
in (

let uu____1995 = (

let uu____1996 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____1996))
in (FStar_Pprint.op_Hat_Hat uu____1994 uu____1995)))
in (FStar_Pprint.op_Hat_Hat uu____1992 uu____1993)))
in (FStar_Pprint.group uu____1991))
end))
and p_constructorDecl : (FStar_Ident.ident * FStar_Parser_AST.term Prims.option * FStar_Parser_AST.fsdoc Prims.option * Prims.bool)  ->  FStar_Pprint.document = (fun uu____1997 -> (match (uu____1997) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let sep = (match (use_of) with
| true -> begin
(str "of")
end
| uu____2013 -> begin
FStar_Pprint.colon
end)
in (

let uid_doc = (p_uident uid)
in (

let uu____2015 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (

let uu____2016 = (default_or_map uid_doc (fun t -> (

let uu____2018 = (

let uu____2019 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep)
in (FStar_Pprint.op_Hat_Hat uid_doc uu____2019))
in (

let uu____2020 = (p_typ t)
in (op_Hat_Slash_Plus_Hat uu____2018 uu____2020)))) t_opt)
in (FStar_Pprint.op_Hat_Hat uu____2015 uu____2016)))))
end))
and p_letbinding : (FStar_Parser_AST.pattern * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun uu____2021 -> (match (uu____2021) with
| (pat, e) -> begin
(

let pat_doc = (

let uu____2027 = (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, t) -> begin
(

let uu____2034 = (

let uu____2035 = (

let uu____2036 = (

let uu____2037 = (

let uu____2038 = (p_tmArrow p_tmNoEq t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2038))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2037))
in (FStar_Pprint.group uu____2036))
in (FStar_Pprint.op_Hat_Hat break1 uu____2035))
in ((pat), (uu____2034)))
end
| uu____2039 -> begin
((pat), (FStar_Pprint.empty))
end)
in (match (uu____2027) with
| (pat, ascr_doc) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____2043); FStar_Parser_AST.prange = uu____2044}, pats) -> begin
(

let uu____2050 = (p_lident x)
in (

let uu____2051 = (

let uu____2052 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Hat uu____2052 ascr_doc))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____2050 uu____2051 FStar_Pprint.equals)))
end
| uu____2053 -> begin
(

let uu____2054 = (

let uu____2055 = (p_tuplePattern pat)
in (

let uu____2056 = (FStar_Pprint.op_Hat_Slash_Hat ascr_doc FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____2055 uu____2056)))
in (FStar_Pprint.group uu____2054))
end)
end))
in (

let uu____2057 = (p_term e)
in (prefix2 pat_doc uu____2057)))
end))
and p_newEffect : FStar_Parser_AST.effect_decl  ->  FStar_Pprint.document = (fun uu___120_2058 -> (match (uu___120_2058) with
| FStar_Parser_AST.RedefineEffect (lid, bs, t) -> begin
(p_effectRedefinition lid bs t)
end
| FStar_Parser_AST.DefineEffect (lid, bs, t, eff_decls, action_decls) -> begin
(p_effectDefinition lid bs t eff_decls action_decls)
end))
and p_effectRedefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun uid bs t -> (

let uu____2079 = (p_uident uid)
in (

let uu____2080 = (p_binders true bs)
in (

let uu____2081 = (

let uu____2082 = (p_simpleTerm t)
in (prefix2 FStar_Pprint.equals uu____2082))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____2079 uu____2080 uu____2081)))))
and p_effectDefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun uid bs t eff_decls action_decls -> (

let uu____2091 = (

let uu____2092 = (

let uu____2093 = (

let uu____2094 = (p_uident uid)
in (

let uu____2095 = (p_binders true bs)
in (

let uu____2096 = (

let uu____2097 = (p_typ t)
in (prefix2 FStar_Pprint.colon uu____2097))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____2094 uu____2095 uu____2096))))
in (FStar_Pprint.group uu____2093))
in (

let uu____2098 = (

let uu____2099 = (

let uu____2100 = (str "with")
in (

let uu____2101 = (separate_break_map FStar_Pprint.semi p_effectDecl eff_decls)
in (prefix2 uu____2100 uu____2101)))
in (

let uu____2102 = (p_actionDecls action_decls)
in (FStar_Pprint.op_Hat_Hat uu____2099 uu____2102)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2092 uu____2098)))
in (braces_with_nesting uu____2091)))
and p_actionDecls : FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun uu___121_2103 -> (match (uu___121_2103) with
| [] -> begin
FStar_Pprint.empty
end
| l -> begin
(

let uu____2107 = (

let uu____2108 = (str "and actions")
in (

let uu____2109 = (separate_break_map FStar_Pprint.semi p_effectDecl l)
in (prefix2 uu____2108 uu____2109)))
in (FStar_Pprint.op_Hat_Hat break1 uu____2107))
end))
and p_effectDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (false, ((FStar_Parser_AST.TyconAbbrev (lid, [], None, e), None))::[]) -> begin
(

let uu____2126 = (

let uu____2127 = (p_lident lid)
in (

let uu____2128 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____2127 uu____2128)))
in (

let uu____2129 = (p_simpleTerm e)
in (prefix2 uu____2126 uu____2129)))
end
| uu____2130 -> begin
(

let uu____2131 = (

let uu____2132 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "Not a declaration of an effect member... or at least I hope so : %s" uu____2132))
in (failwith uu____2131))
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

let p_lift = (fun uu____2165 -> (match (uu____2165) with
| (kwd, t) -> begin
(

let uu____2170 = (

let uu____2171 = (str kwd)
in (

let uu____2172 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____2171 uu____2172)))
in (

let uu____2173 = (p_simpleTerm t)
in (prefix2 uu____2170 uu____2173)))
end))
in (separate_break_map FStar_Pprint.semi p_lift lifts)))
in (

let uu____2176 = (

let uu____2177 = (

let uu____2178 = (p_quident lift.FStar_Parser_AST.msource)
in (

let uu____2179 = (

let uu____2180 = (str "~>")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2180))
in (FStar_Pprint.op_Hat_Hat uu____2178 uu____2179)))
in (

let uu____2181 = (p_quident lift.FStar_Parser_AST.mdest)
in (prefix2 uu____2177 uu____2181)))
in (

let uu____2182 = (

let uu____2183 = (braces_with_nesting lift_op_doc)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2183))
in (FStar_Pprint.op_Hat_Hat uu____2176 uu____2182)))))
and p_qualifier : FStar_Parser_AST.qualifier  ->  FStar_Pprint.document = (fun uu___122_2184 -> (match (uu___122_2184) with
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

let uu____2186 = (FStar_Pprint.separate_map break1 p_qualifier qs)
in (FStar_Pprint.group uu____2186)))
and p_letqualifier : FStar_Parser_AST.let_qualifier  ->  FStar_Pprint.document = (fun uu___123_2187 -> (match (uu___123_2187) with
| FStar_Parser_AST.Rec -> begin
(

let uu____2188 = (str "rec")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2188))
end
| FStar_Parser_AST.Mutable -> begin
(

let uu____2189 = (str "mutable")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2189))
end
| FStar_Parser_AST.NoLetQualifier -> begin
FStar_Pprint.empty
end))
and p_aqual : FStar_Parser_AST.arg_qualifier  ->  FStar_Pprint.document = (fun uu___124_2190 -> (match (uu___124_2190) with
| FStar_Parser_AST.Implicit -> begin
(str "#")
end
| FStar_Parser_AST.Equality -> begin
(str "$")
end))
and p_disjunctivePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr (pats) -> begin
(

let uu____2194 = (

let uu____2195 = (

let uu____2196 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space)
in (FStar_Pprint.op_Hat_Hat break1 uu____2196))
in (FStar_Pprint.separate_map uu____2195 p_tuplePattern pats))
in (FStar_Pprint.group uu____2194))
end
| uu____2197 -> begin
(p_tuplePattern p)
end))
and p_tuplePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTuple (pats, false) -> begin
(

let uu____2202 = (

let uu____2203 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map uu____2203 p_constructorPattern pats))
in (FStar_Pprint.group uu____2202))
end
| uu____2204 -> begin
(p_constructorPattern p)
end))
and p_constructorPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (maybe_cons_lid); FStar_Parser_AST.prange = uu____2207}, (hd)::(tl)::[]) when (FStar_Ident.lid_equals maybe_cons_lid FStar_Syntax_Const.cons_lid) -> begin
(

let uu____2211 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon)
in (

let uu____2212 = (p_constructorPattern hd)
in (

let uu____2213 = (p_constructorPattern tl)
in (infix0 uu____2211 uu____2212 uu____2213))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (uid); FStar_Parser_AST.prange = uu____2215}, pats) -> begin
(

let uu____2219 = (p_quident uid)
in (

let uu____2220 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (prefix2 uu____2219 uu____2220)))
end
| uu____2221 -> begin
(p_atomicPattern p)
end))
and p_atomicPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, t) -> begin
(

let uu____2225 = (

let uu____2228 = (

let uu____2229 = (unparen t)
in uu____2229.FStar_Parser_AST.tm)
in ((pat.FStar_Parser_AST.pat), (uu____2228)))
in (match (uu____2225) with
| (FStar_Parser_AST.PatVar (lid, aqual), FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t); FStar_Parser_AST.brange = uu____2234; FStar_Parser_AST.blevel = uu____2235; FStar_Parser_AST.aqual = uu____2236}, phi)) when (lid.FStar_Ident.idText = lid'.FStar_Ident.idText) -> begin
(

let uu____2240 = (

let uu____2241 = (p_ident lid)
in (p_refinement aqual uu____2241 t phi))
in (soft_parens_with_nesting uu____2240))
end
| (FStar_Parser_AST.PatWild, FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t); FStar_Parser_AST.brange = uu____2243; FStar_Parser_AST.blevel = uu____2244; FStar_Parser_AST.aqual = uu____2245}, phi)) -> begin
(

let uu____2247 = (p_refinement None FStar_Pprint.underscore t phi)
in (soft_parens_with_nesting uu____2247))
end
| uu____2248 -> begin
(

let uu____2251 = (

let uu____2252 = (p_tuplePattern pat)
in (

let uu____2253 = (

let uu____2254 = (FStar_Pprint.break_ (Prims.parse_int "0"))
in (

let uu____2255 = (

let uu____2256 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2256))
in (FStar_Pprint.op_Hat_Hat uu____2254 uu____2255)))
in (FStar_Pprint.op_Hat_Hat uu____2252 uu____2253)))
in (soft_parens_with_nesting uu____2251))
end))
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let uu____2259 = (separate_break_map FStar_Pprint.semi p_tuplePattern pats)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket uu____2259 FStar_Pprint.rbracket))
end
| FStar_Parser_AST.PatRecord (pats) -> begin
(

let p_recordFieldPat = (fun uu____2269 -> (match (uu____2269) with
| (lid, pat) -> begin
(

let uu____2274 = (p_qlident lid)
in (

let uu____2275 = (p_tuplePattern pat)
in (infix2 FStar_Pprint.equals uu____2274 uu____2275)))
end))
in (

let uu____2276 = (separate_break_map FStar_Pprint.semi p_recordFieldPat pats)
in (soft_braces_with_nesting uu____2276)))
end
| FStar_Parser_AST.PatTuple (pats, true) -> begin
(

let uu____2282 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (

let uu____2283 = (separate_break_map FStar_Pprint.comma p_constructorPattern pats)
in (

let uu____2284 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____2282 uu____2283 uu____2284))))
end
| FStar_Parser_AST.PatTvar (tv, arg_qualifier_opt) -> begin
(p_tvar tv)
end
| FStar_Parser_AST.PatOp (op) -> begin
(

let uu____2291 = (

let uu____2292 = (

let uu____2293 = (str op)
in (

let uu____2294 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat uu____2293 uu____2294)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2292))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2291))
end
| FStar_Parser_AST.PatWild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.PatConst (c) -> begin
(p_constant c)
end
| FStar_Parser_AST.PatVar (lid, aqual) -> begin
(

let uu____2300 = (FStar_Pprint.optional p_aqual aqual)
in (

let uu____2301 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat uu____2300 uu____2301)))
end
| FStar_Parser_AST.PatName (uid) -> begin
(p_quident uid)
end
| FStar_Parser_AST.PatOr (uu____2303) -> begin
(failwith "Inner or pattern !")
end
| (FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (_); FStar_Parser_AST.prange = _}, _)) | (FStar_Parser_AST.PatTuple (_, false)) -> begin
(

let uu____2311 = (p_tuplePattern p)
in (soft_parens_with_nesting uu____2311))
end
| uu____2312 -> begin
(

let uu____2313 = (

let uu____2314 = (FStar_Parser_AST.pat_to_string p)
in (FStar_Util.format1 "Invalid pattern %s" uu____2314))
in (failwith uu____2313))
end))
and p_binder : Prims.bool  ->  FStar_Parser_AST.binder  ->  FStar_Pprint.document = (fun is_atomic b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (lid) -> begin
(

let uu____2318 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (

let uu____2319 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat uu____2318 uu____2319)))
end
| FStar_Parser_AST.TVariable (lid) -> begin
(p_lident lid)
end
| FStar_Parser_AST.Annotated (lid, t) -> begin
(

let doc = (

let uu____2324 = (

let uu____2325 = (unparen t)
in uu____2325.FStar_Parser_AST.tm)
in (match (uu____2324) with
| FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t); FStar_Parser_AST.brange = uu____2328; FStar_Parser_AST.blevel = uu____2329; FStar_Parser_AST.aqual = uu____2330}, phi) when (lid.FStar_Ident.idText = lid'.FStar_Ident.idText) -> begin
(

let uu____2332 = (p_ident lid)
in (p_refinement b.FStar_Parser_AST.aqual uu____2332 t phi))
end
| uu____2333 -> begin
(

let uu____2334 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (

let uu____2335 = (

let uu____2336 = (p_lident lid)
in (

let uu____2337 = (

let uu____2338 = (

let uu____2339 = (FStar_Pprint.break_ (Prims.parse_int "0"))
in (

let uu____2340 = (p_tmFormula t)
in (FStar_Pprint.op_Hat_Hat uu____2339 uu____2340)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2338))
in (FStar_Pprint.op_Hat_Hat uu____2336 uu____2337)))
in (FStar_Pprint.op_Hat_Hat uu____2334 uu____2335)))
end))
in (match (is_atomic) with
| true -> begin
(

let uu____2341 = (

let uu____2342 = (FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2342))
in (FStar_Pprint.group uu____2341))
end
| uu____2343 -> begin
(FStar_Pprint.group doc)
end))
end
| FStar_Parser_AST.TAnnotated (uu____2344) -> begin
(failwith "Is this still used ?")
end
| FStar_Parser_AST.NoName (t) -> begin
(

let uu____2348 = (

let uu____2349 = (unparen t)
in uu____2349.FStar_Parser_AST.tm)
in (match (uu____2348) with
| FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t); FStar_Parser_AST.brange = uu____2351; FStar_Parser_AST.blevel = uu____2352; FStar_Parser_AST.aqual = uu____2353}, phi) -> begin
(match (is_atomic) with
| true -> begin
(

let uu____2355 = (

let uu____2356 = (

let uu____2357 = (p_refinement b.FStar_Parser_AST.aqual FStar_Pprint.underscore t phi)
in (FStar_Pprint.op_Hat_Hat uu____2357 FStar_Pprint.rparen))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2356))
in (FStar_Pprint.group uu____2355))
end
| uu____2358 -> begin
(

let uu____2359 = (p_refinement b.FStar_Parser_AST.aqual FStar_Pprint.underscore t phi)
in (FStar_Pprint.group uu____2359))
end)
end
| uu____2360 -> begin
(match (is_atomic) with
| true -> begin
(p_atomicTerm t)
end
| uu____2361 -> begin
(p_appTerm t)
end)
end))
end))
and p_refinement : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Pprint.document  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun aqual_opt binder t phi -> (

let uu____2367 = (FStar_Pprint.optional p_aqual aqual_opt)
in (

let uu____2368 = (

let uu____2369 = (

let uu____2370 = (

let uu____2371 = (p_appTerm t)
in (

let uu____2372 = (

let uu____2373 = (p_noSeqTerm phi)
in (soft_braces_with_nesting uu____2373))
in (FStar_Pprint.op_Hat_Hat uu____2371 uu____2372)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2370))
in (FStar_Pprint.op_Hat_Hat binder uu____2369))
in (FStar_Pprint.op_Hat_Hat uu____2367 uu____2368))))
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
| uu____2384 -> begin
(p_lident id)
end))
and p_term : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2386 = (

let uu____2387 = (unparen e)
in uu____2387.FStar_Parser_AST.tm)
in (match (uu____2386) with
| FStar_Parser_AST.Seq (e1, e2) -> begin
(

let uu____2390 = (

let uu____2391 = (

let uu____2392 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat uu____2392 FStar_Pprint.semi))
in (FStar_Pprint.group uu____2391))
in (

let uu____2393 = (p_term e2)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2390 uu____2393)))
end
| uu____2394 -> begin
(

let uu____2395 = (p_noSeqTerm e)
in (FStar_Pprint.group uu____2395))
end)))
and p_noSeqTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_noSeqTerm' e e.FStar_Parser_AST.range))
and p_noSeqTerm' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2398 = (

let uu____2399 = (unparen e)
in uu____2399.FStar_Parser_AST.tm)
in (match (uu____2398) with
| FStar_Parser_AST.Ascribed (e, t) -> begin
(

let uu____2402 = (

let uu____2403 = (p_tmIff e)
in (

let uu____2404 = (

let uu____2405 = (

let uu____2406 = (p_typ t)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____2406))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____2405))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2403 uu____2404)))
in (FStar_Pprint.group uu____2402))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::(e3)::[]) when (op = ".()<-") -> begin
(

let uu____2412 = (

let uu____2413 = (

let uu____2414 = (

let uu____2415 = (p_atomicTermNotQUident e1)
in (

let uu____2416 = (

let uu____2417 = (

let uu____2418 = (

let uu____2419 = (p_term e2)
in (soft_parens_with_nesting uu____2419))
in (

let uu____2420 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat uu____2418 uu____2420)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____2417))
in (FStar_Pprint.op_Hat_Hat uu____2415 uu____2416)))
in (FStar_Pprint.group uu____2414))
in (

let uu____2421 = (

let uu____2422 = (p_noSeqTerm e3)
in (jump2 uu____2422))
in (FStar_Pprint.op_Hat_Hat uu____2413 uu____2421)))
in (FStar_Pprint.group uu____2412))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::(e3)::[]) when (op = ".[]<-") -> begin
(

let uu____2428 = (

let uu____2429 = (

let uu____2430 = (

let uu____2431 = (p_atomicTermNotQUident e1)
in (

let uu____2432 = (

let uu____2433 = (

let uu____2434 = (

let uu____2435 = (p_term e2)
in (soft_brackets_with_nesting uu____2435))
in (

let uu____2436 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat uu____2434 uu____2436)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____2433))
in (FStar_Pprint.op_Hat_Hat uu____2431 uu____2432)))
in (FStar_Pprint.group uu____2430))
in (

let uu____2437 = (

let uu____2438 = (p_noSeqTerm e3)
in (jump2 uu____2438))
in (FStar_Pprint.op_Hat_Hat uu____2429 uu____2437)))
in (FStar_Pprint.group uu____2428))
end
| FStar_Parser_AST.Requires (e, wtf) -> begin
(

let uu____2444 = (

let uu____2445 = (str "requires")
in (

let uu____2446 = (p_typ e)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2445 uu____2446)))
in (FStar_Pprint.group uu____2444))
end
| FStar_Parser_AST.Ensures (e, wtf) -> begin
(

let uu____2452 = (

let uu____2453 = (str "ensures")
in (

let uu____2454 = (p_typ e)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2453 uu____2454)))
in (FStar_Pprint.group uu____2452))
end
| FStar_Parser_AST.Attributes (es) -> begin
(

let uu____2457 = (

let uu____2458 = (str "attributes")
in (

let uu____2459 = (FStar_Pprint.separate_map break1 p_atomicTerm es)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2458 uu____2459)))
in (FStar_Pprint.group uu____2457))
end
| FStar_Parser_AST.If (e1, e2, e3) -> begin
(

let uu____2463 = (is_unit e3)
in (match (uu____2463) with
| true -> begin
(

let uu____2464 = (

let uu____2465 = (

let uu____2466 = (str "if")
in (

let uu____2467 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat uu____2466 uu____2467)))
in (

let uu____2468 = (

let uu____2469 = (str "then")
in (

let uu____2470 = (p_noSeqTerm e2)
in (op_Hat_Slash_Plus_Hat uu____2469 uu____2470)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2465 uu____2468)))
in (FStar_Pprint.group uu____2464))
end
| uu____2471 -> begin
(

let e2_doc = (

let uu____2473 = (

let uu____2474 = (unparen e2)
in uu____2474.FStar_Parser_AST.tm)
in (match (uu____2473) with
| FStar_Parser_AST.If (uu____2475, uu____2476, e3) when (is_unit e3) -> begin
(

let uu____2478 = (p_noSeqTerm e2)
in (soft_parens_with_nesting uu____2478))
end
| uu____2479 -> begin
(p_noSeqTerm e2)
end))
in (

let uu____2480 = (

let uu____2481 = (

let uu____2482 = (str "if")
in (

let uu____2483 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat uu____2482 uu____2483)))
in (

let uu____2484 = (

let uu____2485 = (

let uu____2486 = (str "then")
in (op_Hat_Slash_Plus_Hat uu____2486 e2_doc))
in (

let uu____2487 = (

let uu____2488 = (str "else")
in (

let uu____2489 = (p_noSeqTerm e3)
in (op_Hat_Slash_Plus_Hat uu____2488 uu____2489)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2485 uu____2487)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2481 uu____2484)))
in (FStar_Pprint.group uu____2480)))
end))
end
| FStar_Parser_AST.TryWith (e, branches) -> begin
(

let uu____2502 = (

let uu____2503 = (

let uu____2504 = (str "try")
in (

let uu____2505 = (p_noSeqTerm e)
in (prefix2 uu____2504 uu____2505)))
in (

let uu____2506 = (

let uu____2507 = (str "with")
in (

let uu____2508 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2507 uu____2508)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2503 uu____2506)))
in (FStar_Pprint.group uu____2502))
end
| FStar_Parser_AST.Match (e, branches) -> begin
(

let uu____2525 = (

let uu____2526 = (

let uu____2527 = (str "match")
in (

let uu____2528 = (p_noSeqTerm e)
in (

let uu____2529 = (str "with")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____2527 uu____2528 uu____2529))))
in (

let uu____2530 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2526 uu____2530)))
in (FStar_Pprint.group uu____2525))
end
| FStar_Parser_AST.LetOpen (uid, e) -> begin
(

let uu____2537 = (

let uu____2538 = (

let uu____2539 = (str "let open")
in (

let uu____2540 = (p_quident uid)
in (

let uu____2541 = (str "in")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____2539 uu____2540 uu____2541))))
in (

let uu____2542 = (p_term e)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2538 uu____2542)))
in (FStar_Pprint.group uu____2537))
end
| FStar_Parser_AST.Let (q, lbs, e) -> begin
(

let let_doc = (

let uu____2553 = (str "let")
in (

let uu____2554 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat uu____2553 uu____2554)))
in (

let uu____2555 = (

let uu____2556 = (

let uu____2557 = (

let uu____2558 = (str "and")
in (precede_break_separate_map let_doc uu____2558 p_letbinding lbs))
in (

let uu____2561 = (str "in")
in (FStar_Pprint.op_Hat_Slash_Hat uu____2557 uu____2561)))
in (FStar_Pprint.group uu____2556))
in (

let uu____2562 = (p_term e)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2555 uu____2562))))
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, typ_opt); FStar_Parser_AST.prange = uu____2565})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, branches); FStar_Parser_AST.range = uu____2568; FStar_Parser_AST.level = uu____2569}) when (matches_var maybe_x x) -> begin
(

let uu____2583 = (

let uu____2584 = (str "function")
in (

let uu____2585 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2584 uu____2585)))
in (FStar_Pprint.group uu____2583))
end
| FStar_Parser_AST.Assign (id, e) -> begin
(

let uu____2592 = (

let uu____2593 = (p_lident id)
in (

let uu____2594 = (

let uu____2595 = (p_noSeqTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow uu____2595))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2593 uu____2594)))
in (FStar_Pprint.group uu____2592))
end
| uu____2596 -> begin
(p_typ e)
end)))
and p_typ : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_typ' e e.FStar_Parser_AST.range))
and p_typ' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2599 = (

let uu____2600 = (unparen e)
in uu____2600.FStar_Parser_AST.tm)
in (match (uu____2599) with
| (FStar_Parser_AST.QForall (bs, trigger, e1)) | (FStar_Parser_AST.QExists (bs, trigger, e1)) -> begin
(

let uu____2616 = (

let uu____2617 = (

let uu____2618 = (p_quantifier e)
in (FStar_Pprint.op_Hat_Hat uu____2618 FStar_Pprint.space))
in (

let uu____2619 = (p_binders true bs)
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") uu____2617 uu____2619 FStar_Pprint.dot)))
in (

let uu____2620 = (

let uu____2621 = (p_trigger trigger)
in (

let uu____2622 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat uu____2621 uu____2622)))
in (prefix2 uu____2616 uu____2620)))
end
| uu____2623 -> begin
(p_simpleTerm e)
end)))
and p_quantifier : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2625 = (

let uu____2626 = (unparen e)
in uu____2626.FStar_Parser_AST.tm)
in (match (uu____2625) with
| FStar_Parser_AST.QForall (uu____2627) -> begin
(str "forall")
end
| FStar_Parser_AST.QExists (uu____2634) -> begin
(str "exists")
end
| uu____2641 -> begin
(failwith "Imposible : p_quantifier called on a non-quantifier term")
end)))
and p_trigger : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun uu___125_2642 -> (match (uu___125_2642) with
| [] -> begin
FStar_Pprint.empty
end
| pats -> begin
(

let uu____2649 = (

let uu____2650 = (

let uu____2651 = (str "pattern")
in (

let uu____2652 = (

let uu____2653 = (

let uu____2654 = (p_disjunctivePats pats)
in (jump2 uu____2654))
in (

let uu____2655 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2653 uu____2655)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2651 uu____2652)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2650))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____2649))
end))
and p_disjunctivePats : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun pats -> (

let uu____2659 = (str "\\/")
in (FStar_Pprint.separate_map uu____2659 p_conjunctivePats pats)))
and p_conjunctivePats : FStar_Parser_AST.term Prims.list  ->  FStar_Pprint.document = (fun pats -> (

let uu____2663 = (FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats)
in (FStar_Pprint.group uu____2663)))
and p_simpleTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2665 = (

let uu____2666 = (unparen e)
in uu____2666.FStar_Parser_AST.tm)
in (match (uu____2665) with
| FStar_Parser_AST.Abs (pats, e) -> begin
(

let uu____2671 = (

let uu____2672 = (str "fun")
in (

let uu____2673 = (

let uu____2674 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2674 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat uu____2672 uu____2673)))
in (

let uu____2675 = (p_term e)
in (op_Hat_Slash_Plus_Hat uu____2671 uu____2675)))
end
| uu____2676 -> begin
(p_tmIff e)
end)))
and p_maybeFocusArrow : Prims.bool  ->  FStar_Pprint.document = (fun b -> (match (b) with
| true -> begin
(str "~>")
end
| uu____2678 -> begin
FStar_Pprint.rarrow
end))
and p_patternBranch : (FStar_Parser_AST.pattern * FStar_Parser_AST.term Prims.option * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun uu____2679 -> (match (uu____2679) with
| (pat, when_opt, e) -> begin
(

let maybe_paren = (

let uu____2692 = (

let uu____2693 = (unparen e)
in uu____2693.FStar_Parser_AST.tm)
in (match (uu____2692) with
| (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) -> begin
soft_begin_end_with_nesting
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____2699); FStar_Parser_AST.prange = uu____2700})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, uu____2702); FStar_Parser_AST.range = uu____2703; FStar_Parser_AST.level = uu____2704}) when (matches_var maybe_x x) -> begin
soft_begin_end_with_nesting
end
| uu____2718 -> begin
(fun x -> x)
end))
in (

let uu____2720 = (

let uu____2721 = (

let uu____2722 = (

let uu____2723 = (

let uu____2724 = (

let uu____2725 = (p_disjunctivePattern pat)
in (

let uu____2726 = (

let uu____2727 = (p_maybeWhen when_opt)
in (FStar_Pprint.op_Hat_Hat uu____2727 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat uu____2725 uu____2726)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2724))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____2723))
in (FStar_Pprint.group uu____2722))
in (

let uu____2728 = (

let uu____2729 = (p_term e)
in (maybe_paren uu____2729))
in (op_Hat_Slash_Plus_Hat uu____2721 uu____2728)))
in (FStar_Pprint.group uu____2720)))
end))
and p_maybeWhen : FStar_Parser_AST.term Prims.option  ->  FStar_Pprint.document = (fun uu___126_2730 -> (match (uu___126_2730) with
| None -> begin
FStar_Pprint.empty
end
| Some (e) -> begin
(

let uu____2733 = (str "when")
in (

let uu____2734 = (

let uu____2735 = (p_tmFormula e)
in (FStar_Pprint.op_Hat_Hat uu____2735 FStar_Pprint.space))
in (op_Hat_Slash_Plus_Hat uu____2733 uu____2734)))
end))
and p_tmIff : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2737 = (

let uu____2738 = (unparen e)
in uu____2738.FStar_Parser_AST.tm)
in (match (uu____2737) with
| FStar_Parser_AST.Op ("<==>", (e1)::(e2)::[]) -> begin
(

let uu____2742 = (str "<==>")
in (

let uu____2743 = (p_tmImplies e1)
in (

let uu____2744 = (p_tmIff e2)
in (infix0 uu____2742 uu____2743 uu____2744))))
end
| uu____2745 -> begin
(p_tmImplies e)
end)))
and p_tmImplies : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2747 = (

let uu____2748 = (unparen e)
in uu____2748.FStar_Parser_AST.tm)
in (match (uu____2747) with
| FStar_Parser_AST.Op ("==>", (e1)::(e2)::[]) -> begin
(

let uu____2752 = (str "==>")
in (

let uu____2753 = (p_tmArrow p_tmFormula e1)
in (

let uu____2754 = (p_tmImplies e2)
in (infix0 uu____2752 uu____2753 uu____2754))))
end
| uu____2755 -> begin
(p_tmArrow p_tmFormula e)
end)))
and p_tmArrow : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_Tm e -> (

let uu____2760 = (

let uu____2761 = (unparen e)
in uu____2761.FStar_Parser_AST.tm)
in (match (uu____2760) with
| FStar_Parser_AST.Product (bs, tgt) -> begin
(

let uu____2766 = (

let uu____2767 = (FStar_Pprint.concat_map (fun b -> (

let uu____2769 = (p_binder false b)
in (

let uu____2770 = (

let uu____2771 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2771))
in (FStar_Pprint.op_Hat_Hat uu____2769 uu____2770)))) bs)
in (

let uu____2772 = (p_tmArrow p_Tm tgt)
in (FStar_Pprint.op_Hat_Hat uu____2767 uu____2772)))
in (FStar_Pprint.group uu____2766))
end
| uu____2773 -> begin
(p_Tm e)
end)))
and p_tmFormula : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2775 = (

let uu____2776 = (unparen e)
in uu____2776.FStar_Parser_AST.tm)
in (match (uu____2775) with
| FStar_Parser_AST.Op ("\\/", (e1)::(e2)::[]) -> begin
(

let uu____2780 = (str "\\/")
in (

let uu____2781 = (p_tmFormula e1)
in (

let uu____2782 = (p_tmConjunction e2)
in (infix0 uu____2780 uu____2781 uu____2782))))
end
| uu____2783 -> begin
(p_tmConjunction e)
end)))
and p_tmConjunction : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2785 = (

let uu____2786 = (unparen e)
in uu____2786.FStar_Parser_AST.tm)
in (match (uu____2785) with
| FStar_Parser_AST.Op ("/\\", (e1)::(e2)::[]) -> begin
(

let uu____2790 = (str "/\\")
in (

let uu____2791 = (p_tmConjunction e1)
in (

let uu____2792 = (p_tmTuple e2)
in (infix0 uu____2790 uu____2791 uu____2792))))
end
| uu____2793 -> begin
(p_tmTuple e)
end)))
and p_tmTuple : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2795 = (

let uu____2796 = (unparen e)
in uu____2796.FStar_Parser_AST.tm)
in (match (uu____2795) with
| FStar_Parser_AST.Construct (lid, args) when (is_tuple_constructor lid) -> begin
(

let uu____2805 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map uu____2805 (fun uu____2808 -> (match (uu____2808) with
| (e, uu____2812) -> begin
(p_tmEq e)
end)) args))
end
| uu____2813 -> begin
(p_tmEq e)
end)))
and paren_if : Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun curr mine doc -> (match ((mine <= curr)) with
| true -> begin
doc
end
| uu____2817 -> begin
(

let uu____2818 = (

let uu____2819 = (FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2819))
in (FStar_Pprint.group uu____2818))
end))
and p_tmEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n = (max_level (FStar_List.append (((colon_equals ()))::((pipe_right ()))::[]) (operatorInfix0ad12 ())))
in (p_tmEq' n e)))
and p_tmEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (

let uu____2844 = (

let uu____2845 = (unparen e)
in uu____2845.FStar_Parser_AST.tm)
in (match (uu____2844) with
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (((is_operatorInfix0ad12 op) || (op = "=")) || (op = "|>")) -> begin
(

let uu____2850 = (levels op)
in (match (uu____2850) with
| (left, mine, right) -> begin
(

let uu____2857 = (

let uu____2858 = (str op)
in (

let uu____2859 = (p_tmEq' left e1)
in (

let uu____2860 = (p_tmEq' right e2)
in (infix0 uu____2858 uu____2859 uu____2860))))
in (paren_if curr mine uu____2857))
end))
end
| FStar_Parser_AST.Op (":=", (e1)::(e2)::[]) -> begin
(

let uu____2864 = (

let uu____2865 = (p_tmEq e1)
in (

let uu____2866 = (

let uu____2867 = (

let uu____2868 = (

let uu____2869 = (p_tmEq e2)
in (op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____2869))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2868))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2867))
in (FStar_Pprint.op_Hat_Hat uu____2865 uu____2866)))
in (FStar_Pprint.group uu____2864))
end
| uu____2870 -> begin
(p_tmNoEq e)
end)))
and p_tmNoEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n = (max_level (((colon_colon ()))::((amp ()))::((opinfix3 ()))::((opinfix4 ()))::[]))
in (p_tmNoEq' n e)))
and p_tmNoEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (

let uu____2900 = (

let uu____2901 = (unparen e)
in uu____2901.FStar_Parser_AST.tm)
in (match (uu____2900) with
| FStar_Parser_AST.Construct (lid, ((e1, uu____2904))::((e2, uu____2906))::[]) when ((FStar_Ident.lid_equals lid FStar_Syntax_Const.cons_lid) && (

let uu____2916 = (is_list e)
in (not (uu____2916)))) -> begin
(

let op = "::"
in (

let uu____2918 = (levels op)
in (match (uu____2918) with
| (left, mine, right) -> begin
(

let uu____2925 = (

let uu____2926 = (str op)
in (

let uu____2927 = (p_tmNoEq' left e1)
in (

let uu____2928 = (p_tmNoEq' right e2)
in (infix0 uu____2926 uu____2927 uu____2928))))
in (paren_if curr mine uu____2925))
end)))
end
| FStar_Parser_AST.Sum (binders, res) -> begin
(

let op = "&"
in (

let uu____2934 = (levels op)
in (match (uu____2934) with
| (left, mine, right) -> begin
(

let p_dsumfst = (fun b -> (

let uu____2945 = (p_binder false b)
in (

let uu____2946 = (

let uu____2947 = (

let uu____2948 = (str "&")
in (FStar_Pprint.op_Hat_Hat uu____2948 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2947))
in (FStar_Pprint.op_Hat_Hat uu____2945 uu____2946))))
in (

let uu____2949 = (

let uu____2950 = (FStar_Pprint.concat_map p_dsumfst binders)
in (

let uu____2951 = (p_tmNoEq' right res)
in (FStar_Pprint.op_Hat_Hat uu____2950 uu____2951)))
in (paren_if curr mine uu____2949)))
end)))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (is_operatorInfix34 op) -> begin
(

let uu____2956 = (levels op)
in (match (uu____2956) with
| (left, mine, right) -> begin
(

let uu____2963 = (

let uu____2964 = (str op)
in (

let uu____2965 = (p_tmNoEq' left e1)
in (

let uu____2966 = (p_tmNoEq' right e2)
in (infix0 uu____2964 uu____2965 uu____2966))))
in (paren_if curr mine uu____2963))
end))
end
| FStar_Parser_AST.Op ("-", (e)::[]) -> begin
(

let uu____2969 = (levels "-")
in (match (uu____2969) with
| (left, mine, right) -> begin
(

let uu____2976 = (p_tmNoEq' mine e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____2976))
end))
end
| FStar_Parser_AST.NamedTyp (lid, e) -> begin
(

let uu____2979 = (

let uu____2980 = (p_lidentOrUnderscore lid)
in (

let uu____2981 = (

let uu____2982 = (p_appTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____2982))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2980 uu____2981)))
in (FStar_Pprint.group uu____2979))
end
| FStar_Parser_AST.Refine (b, phi) -> begin
(p_refinedBinder b phi)
end
| FStar_Parser_AST.Record (with_opt, record_fields) -> begin
(

let uu____2995 = (

let uu____2996 = (default_or_map FStar_Pprint.empty p_with_clause with_opt)
in (

let uu____2997 = (

let uu____2998 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (FStar_Pprint.separate_map uu____2998 p_simpleDef record_fields))
in (FStar_Pprint.op_Hat_Hat uu____2996 uu____2997)))
in (braces_with_nesting uu____2995))
end
| FStar_Parser_AST.Op ("~", (e)::[]) -> begin
(

let uu____3003 = (

let uu____3004 = (str "~")
in (

let uu____3005 = (p_atomicTerm e)
in (FStar_Pprint.op_Hat_Hat uu____3004 uu____3005)))
in (FStar_Pprint.group uu____3003))
end
| uu____3006 -> begin
(p_appTerm e)
end)))
and p_with_clause : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3008 = (p_appTerm e)
in (

let uu____3009 = (

let uu____3010 = (

let uu____3011 = (str "with")
in (FStar_Pprint.op_Hat_Hat uu____3011 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3010))
in (FStar_Pprint.op_Hat_Hat uu____3008 uu____3009))))
and p_refinedBinder : FStar_Parser_AST.binder  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun b phi -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (lid, t) -> begin
(

let uu____3016 = (

let uu____3017 = (p_lident lid)
in (p_refinement b.FStar_Parser_AST.aqual uu____3017 t phi))
in (soft_parens_with_nesting uu____3016))
end
| FStar_Parser_AST.TAnnotated (uu____3018) -> begin
(failwith "Is this still used ?")
end
| (FStar_Parser_AST.Variable (_)) | (FStar_Parser_AST.TVariable (_)) | (FStar_Parser_AST.NoName (_)) -> begin
(

let uu____3024 = (

let uu____3025 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" uu____3025))
in (failwith uu____3024))
end))
and p_simpleDef : (FStar_Ident.lid * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun uu____3026 -> (match (uu____3026) with
| (lid, e) -> begin
(

let uu____3031 = (

let uu____3032 = (p_qlident lid)
in (

let uu____3033 = (

let uu____3034 = (p_tmIff e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____3034))
in (FStar_Pprint.op_Hat_Slash_Hat uu____3032 uu____3033)))
in (FStar_Pprint.group uu____3031))
end))
and p_appTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3036 = (

let uu____3037 = (unparen e)
in uu____3037.FStar_Parser_AST.tm)
in (match (uu____3036) with
| FStar_Parser_AST.App (uu____3038) when (is_general_application e) -> begin
(

let uu____3042 = (head_and_args e)
in (match (uu____3042) with
| (head, args) -> begin
(

let uu____3056 = (p_indexingTerm head)
in (

let uu____3057 = (FStar_Pprint.separate_map FStar_Pprint.space p_argTerm args)
in (op_Hat_Slash_Plus_Hat uu____3056 uu____3057)))
end))
end
| FStar_Parser_AST.Construct (lid, args) when ((is_general_construction e) && (not ((is_dtuple_constructor lid)))) -> begin
(match (args) with
| [] -> begin
(p_quident lid)
end
| (arg)::[] -> begin
(

let uu____3077 = (

let uu____3078 = (p_quident lid)
in (

let uu____3079 = (p_argTerm arg)
in (FStar_Pprint.op_Hat_Slash_Hat uu____3078 uu____3079)))
in (FStar_Pprint.group uu____3077))
end
| (hd)::tl -> begin
(

let uu____3089 = (

let uu____3090 = (

let uu____3091 = (

let uu____3092 = (p_quident lid)
in (

let uu____3093 = (p_argTerm hd)
in (FStar_Pprint.op_Hat_Slash_Hat uu____3092 uu____3093)))
in (FStar_Pprint.group uu____3091))
in (

let uu____3094 = (

let uu____3095 = (FStar_Pprint.separate_map break1 p_argTerm tl)
in (jump2 uu____3095))
in (FStar_Pprint.op_Hat_Hat uu____3090 uu____3094)))
in (FStar_Pprint.group uu____3089))
end)
end
| uu____3098 -> begin
(p_indexingTerm e)
end)))
and p_argTerm : (FStar_Parser_AST.term * FStar_Parser_AST.imp)  ->  FStar_Pprint.document = (fun arg_imp -> (match (arg_imp) with
| ({FStar_Parser_AST.tm = FStar_Parser_AST.Uvar (uu____3102); FStar_Parser_AST.range = uu____3103; FStar_Parser_AST.level = uu____3104}, FStar_Parser_AST.UnivApp) -> begin
(p_univar (Prims.fst arg_imp))
end
| (u, FStar_Parser_AST.UnivApp) -> begin
(p_universe u)
end
| (e, FStar_Parser_AST.FsTypApp) -> begin
(

let uu____3107 = (p_indexingTerm e)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.langle uu____3107 FStar_Pprint.rangle))
end
| (e, FStar_Parser_AST.Hash) -> begin
(

let uu____3109 = (str "#")
in (

let uu____3110 = (p_indexingTerm e)
in (FStar_Pprint.op_Hat_Hat uu____3109 uu____3110)))
end
| (e, FStar_Parser_AST.Nothing) -> begin
(p_indexingTerm e)
end))
and p_indexingTerm_aux : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun exit e -> (

let uu____3116 = (

let uu____3117 = (unparen e)
in uu____3117.FStar_Parser_AST.tm)
in (match (uu____3116) with
| FStar_Parser_AST.Op (".()", (e1)::(e2)::[]) -> begin
(

let uu____3121 = (

let uu____3122 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (

let uu____3123 = (

let uu____3124 = (

let uu____3125 = (p_term e2)
in (soft_parens_with_nesting uu____3125))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3124))
in (FStar_Pprint.op_Hat_Hat uu____3122 uu____3123)))
in (FStar_Pprint.group uu____3121))
end
| FStar_Parser_AST.Op (".[]", (e1)::(e2)::[]) -> begin
(

let uu____3129 = (

let uu____3130 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (

let uu____3131 = (

let uu____3132 = (

let uu____3133 = (p_term e2)
in (soft_brackets_with_nesting uu____3133))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3132))
in (FStar_Pprint.op_Hat_Hat uu____3130 uu____3131)))
in (FStar_Pprint.group uu____3129))
end
| uu____3134 -> begin
(exit e)
end)))
and p_indexingTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_indexingTerm_aux p_atomicTerm e))
and p_atomicTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3137 = (

let uu____3138 = (unparen e)
in uu____3138.FStar_Parser_AST.tm)
in (match (uu____3137) with
| FStar_Parser_AST.LetOpen (lid, e) -> begin
(

let uu____3141 = (p_quident lid)
in (

let uu____3142 = (

let uu____3143 = (

let uu____3144 = (p_term e)
in (soft_parens_with_nesting uu____3144))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3143))
in (FStar_Pprint.op_Hat_Hat uu____3141 uu____3142)))
end
| FStar_Parser_AST.Name (lid) -> begin
(p_quident lid)
end
| FStar_Parser_AST.Op (op, (e)::[]) when (is_general_prefix_op op) -> begin
(

let uu____3149 = (str op)
in (

let uu____3150 = (p_atomicTerm e)
in (FStar_Pprint.op_Hat_Hat uu____3149 uu____3150)))
end
| uu____3151 -> begin
(p_atomicTermNotQUident e)
end)))
and p_atomicTermNotQUident : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3153 = (

let uu____3154 = (unparen e)
in uu____3154.FStar_Parser_AST.tm)
in (match (uu____3153) with
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

let uu____3163 = (str op)
in (

let uu____3164 = (p_atomicTermNotQUident e)
in (FStar_Pprint.op_Hat_Hat uu____3163 uu____3164)))
end
| FStar_Parser_AST.Op (op, []) -> begin
(

let uu____3167 = (

let uu____3168 = (

let uu____3169 = (str op)
in (

let uu____3170 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat uu____3169 uu____3170)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3168))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3167))
end
| FStar_Parser_AST.Construct (lid, args) when (is_dtuple_constructor lid) -> begin
(

let uu____3179 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (

let uu____3180 = (

let uu____3181 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (

let uu____3182 = (FStar_List.map Prims.fst args)
in (FStar_Pprint.separate_map uu____3181 p_tmEq uu____3182)))
in (

let uu____3186 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____3179 uu____3180 uu____3186))))
end
| FStar_Parser_AST.Project (e, lid) -> begin
(

let uu____3189 = (

let uu____3190 = (p_atomicTermNotQUident e)
in (

let uu____3191 = (

let uu____3192 = (p_qlident lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3192))
in (FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0") uu____3190 uu____3191)))
in (FStar_Pprint.group uu____3189))
end
| uu____3193 -> begin
(p_projectionLHS e)
end)))
and p_projectionLHS : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3195 = (

let uu____3196 = (unparen e)
in uu____3196.FStar_Parser_AST.tm)
in (match (uu____3195) with
| FStar_Parser_AST.Var (lid) -> begin
(p_qlident lid)
end
| FStar_Parser_AST.Projector (constr_lid, field_lid) -> begin
(

let uu____3200 = (p_quident constr_lid)
in (

let uu____3201 = (

let uu____3202 = (

let uu____3203 = (p_lident field_lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3203))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____3202))
in (FStar_Pprint.op_Hat_Hat uu____3200 uu____3201)))
end
| FStar_Parser_AST.Discrim (constr_lid) -> begin
(

let uu____3205 = (p_quident constr_lid)
in (FStar_Pprint.op_Hat_Hat uu____3205 FStar_Pprint.qmark))
end
| FStar_Parser_AST.Paren (e) -> begin
(

let uu____3207 = (p_term e)
in (soft_parens_with_nesting uu____3207))
end
| uu____3208 when (is_array e) -> begin
(

let es = (extract_from_list e)
in (

let uu____3211 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar)
in (

let uu____3212 = (

let uu____3213 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (separate_map_or_flow uu____3213 p_noSeqTerm es))
in (

let uu____3214 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") uu____3211 uu____3212 uu____3214)))))
end
| uu____3215 when (is_list e) -> begin
(

let uu____3216 = (

let uu____3217 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (

let uu____3218 = (extract_from_list e)
in (separate_map_or_flow uu____3217 p_noSeqTerm uu____3218)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket uu____3216 FStar_Pprint.rbracket))
end
| uu____3220 when (is_lex_list e) -> begin
(

let uu____3221 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket)
in (

let uu____3222 = (

let uu____3223 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (

let uu____3224 = (extract_from_list e)
in (separate_map_or_flow uu____3223 p_noSeqTerm uu____3224)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____3221 uu____3222 FStar_Pprint.rbracket)))
end
| uu____3226 when (is_ref_set e) -> begin
(

let es = (extract_from_ref_set e)
in (

let uu____3229 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace)
in (

let uu____3230 = (

let uu____3231 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (separate_map_or_flow uu____3231 p_appTerm es))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") uu____3229 uu____3230 FStar_Pprint.rbrace))))
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Op (_)) | (FStar_Parser_AST.Tvar (_)) | (FStar_Parser_AST.Uvar (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) | (FStar_Parser_AST.Construct (_)) | (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.App (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.LetOpen (_)) | (FStar_Parser_AST.Seq (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Ascribed (_)) | (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Project (_)) | (FStar_Parser_AST.Product (_)) | (FStar_Parser_AST.Sum (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Refine (_)) | (FStar_Parser_AST.NamedTyp (_)) | (FStar_Parser_AST.Requires (_)) | (FStar_Parser_AST.Ensures (_)) | (FStar_Parser_AST.Assign (_)) | (FStar_Parser_AST.Attributes (_)) -> begin
(

let uu____3260 = (p_term e)
in (soft_parens_with_nesting uu____3260))
end
| FStar_Parser_AST.Labeled (uu____3261) -> begin
(failwith "Not valid in universe")
end)))
and p_constant : FStar_Const.sconst  ->  FStar_Pprint.document = (fun uu___129_3265 -> (match (uu___129_3265) with
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

let uu____3269 = (FStar_Pprint.doc_of_char x)
in (FStar_Pprint.squotes uu____3269))
end
| FStar_Const.Const_string (bytes, uu____3271) -> begin
(

let uu____3274 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes uu____3274))
end
| FStar_Const.Const_bytearray (bytes, uu____3276) -> begin
(

let uu____3279 = (

let uu____3280 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes uu____3280))
in (

let uu____3281 = (str "B")
in (FStar_Pprint.op_Hat_Hat uu____3279 uu____3281)))
end
| FStar_Const.Const_int (repr, sign_width_opt) -> begin
(

let signedness = (fun uu___127_3293 -> (match (uu___127_3293) with
| FStar_Const.Unsigned -> begin
(str "u")
end
| FStar_Const.Signed -> begin
FStar_Pprint.empty
end))
in (

let width = (fun uu___128_3297 -> (match (uu___128_3297) with
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

let ending = (default_or_map FStar_Pprint.empty (fun uu____3301 -> (match (uu____3301) with
| (s, w) -> begin
(

let uu____3306 = (signedness s)
in (

let uu____3307 = (width w)
in (FStar_Pprint.op_Hat_Hat uu____3306 uu____3307)))
end)) sign_width_opt)
in (

let uu____3308 = (str repr)
in (FStar_Pprint.op_Hat_Hat uu____3308 ending)))))
end
| FStar_Const.Const_range (r) -> begin
(

let uu____3310 = (FStar_Range.string_of_range r)
in (str uu____3310))
end
| FStar_Const.Const_reify -> begin
(str "reify")
end
| FStar_Const.Const_reflect (lid) -> begin
(

let uu____3312 = (p_quident lid)
in (

let uu____3313 = (

let uu____3314 = (

let uu____3315 = (str "reflect")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3315))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____3314))
in (FStar_Pprint.op_Hat_Hat uu____3312 uu____3313)))
end))
and p_universe : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (

let uu____3317 = (str "u#")
in (

let uu____3318 = (p_atomicUniverse u)
in (FStar_Pprint.op_Hat_Hat uu____3317 uu____3318))))
and p_universeFrom : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (

let uu____3320 = (

let uu____3321 = (unparen u)
in uu____3321.FStar_Parser_AST.tm)
in (match (uu____3320) with
| FStar_Parser_AST.Op ("+", (u1)::(u2)::[]) -> begin
(

let uu____3325 = (

let uu____3326 = (p_universeFrom u1)
in (

let uu____3327 = (

let uu____3328 = (p_universeFrom u2)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____3328))
in (FStar_Pprint.op_Hat_Slash_Hat uu____3326 uu____3327)))
in (FStar_Pprint.group uu____3325))
end
| FStar_Parser_AST.App (uu____3329) -> begin
(

let uu____3333 = (head_and_args u)
in (match (uu____3333) with
| (head, args) -> begin
(

let uu____3347 = (

let uu____3348 = (unparen head)
in uu____3348.FStar_Parser_AST.tm)
in (match (uu____3347) with
| FStar_Parser_AST.Var (maybe_max_lid) when (FStar_Ident.lid_equals maybe_max_lid FStar_Syntax_Const.max_lid) -> begin
(

let uu____3350 = (

let uu____3351 = (p_qlident FStar_Syntax_Const.max_lid)
in (

let uu____3352 = (FStar_Pprint.separate_map FStar_Pprint.space (fun uu____3355 -> (match (uu____3355) with
| (u, uu____3359) -> begin
(p_atomicUniverse u)
end)) args)
in (op_Hat_Slash_Plus_Hat uu____3351 uu____3352)))
in (FStar_Pprint.group uu____3350))
end
| uu____3360 -> begin
(

let uu____3361 = (

let uu____3362 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" uu____3362))
in (failwith uu____3361))
end))
end))
end
| uu____3363 -> begin
(p_atomicUniverse u)
end)))
and p_atomicUniverse : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (

let uu____3365 = (

let uu____3366 = (unparen u)
in uu____3366.FStar_Parser_AST.tm)
in (match (uu____3365) with
| FStar_Parser_AST.Wild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (r, sw)) -> begin
(p_constant (FStar_Const.Const_int (((r), (sw)))))
end
| FStar_Parser_AST.Uvar (uu____3378) -> begin
(p_univar u)
end
| FStar_Parser_AST.Paren (u) -> begin
(

let uu____3380 = (p_universeFrom u)
in (soft_parens_with_nesting uu____3380))
end
| (FStar_Parser_AST.Op ("+", (_)::(_)::[])) | (FStar_Parser_AST.App (_)) -> begin
(

let uu____3385 = (p_universeFrom u)
in (soft_parens_with_nesting uu____3385))
end
| uu____3386 -> begin
(

let uu____3387 = (

let uu____3388 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" uu____3388))
in (failwith uu____3387))
end)))
and p_univar : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (

let uu____3390 = (

let uu____3391 = (unparen u)
in uu____3391.FStar_Parser_AST.tm)
in (match (uu____3390) with
| FStar_Parser_AST.Uvar (id) -> begin
(str (FStar_Ident.text_of_id id))
end
| uu____3393 -> begin
(

let uu____3394 = (

let uu____3395 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Not a universe variable %s" uu____3395))
in (failwith uu____3394))
end)))


let term_to_document : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_term e))


let decl_to_document : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun e -> (p_decl e))


let modul_to_document : FStar_Parser_AST.modul  ->  FStar_Pprint.document = (fun m -> (match (m) with
| (FStar_Parser_AST.Module (_, decls)) | (FStar_Parser_AST.Interface (_, decls, _)) -> begin
(

let uu____3413 = (FStar_All.pipe_right decls (FStar_List.map decl_to_document))
in (FStar_All.pipe_right uu____3413 (FStar_Pprint.separate FStar_Pprint.hardline)))
end))


let comments_to_document : (Prims.string * FStar_Range.range) Prims.list  ->  FStar_Pprint.document = (fun comments -> (FStar_Pprint.separate_map FStar_Pprint.hardline (fun uu____3429 -> (match (uu____3429) with
| (comment, range) -> begin
(str comment)
end)) comments))


let modul_with_comments_to_document : FStar_Parser_AST.modul  ->  (Prims.string * FStar_Range.range) Prims.list  ->  (FStar_Pprint.document * (Prims.string * FStar_Range.range) Prims.list) = (fun m comments -> (

let rec aux = (fun uu____3468 decl -> (match (uu____3468) with
| (previous_range_end, comments, doc) -> begin
(

let current_range = (FStar_Range.extend_to_end_of_line decl.FStar_Parser_AST.drange)
in (

let max = (fun x y -> (match ((x < y)) with
| true -> begin
y
end
| uu____3499 -> begin
x
end))
in (

let rec process_preceding_comments = (fun doc last_line end_pos n uu___130_3523 -> (match (uu___130_3523) with
| ((comment, range))::comments when (

let uu____3540 = (FStar_Range.start_of_range range)
in (FStar_Range.pos_geq end_pos uu____3540)) -> begin
(

let l = (

let uu____3542 = (

let uu____3543 = (

let uu____3544 = (FStar_Range.start_of_range range)
in (FStar_Range.line_of_pos uu____3544))
in (uu____3543 - last_line))
in (max (Prims.parse_int "1") uu____3542))
in (

let doc = (

let uu____3546 = (

let uu____3547 = (FStar_Pprint.repeat l FStar_Pprint.hardline)
in (

let uu____3548 = (str comment)
in (FStar_Pprint.op_Hat_Hat uu____3547 uu____3548)))
in (FStar_Pprint.op_Hat_Hat doc uu____3546))
in (

let uu____3549 = (

let uu____3550 = (FStar_Range.end_of_range range)
in (FStar_Range.line_of_pos uu____3550))
in (process_preceding_comments doc uu____3549 end_pos (Prims.parse_int "1") comments))))
end
| comments -> begin
(

let l = (

let uu____3556 = (

let uu____3557 = (FStar_Range.line_of_pos end_pos)
in (uu____3557 - last_line))
in (max n uu____3556))
in (

let uu____3558 = (

let uu____3559 = (FStar_Pprint.repeat l FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat doc uu____3559))
in ((uu____3558), (comments))))
end))
in (

let uu____3563 = (

let uu____3569 = (FStar_Range.line_of_pos previous_range_end)
in (

let uu____3570 = (

let uu____3571 = (FStar_Range.start_of_range current_range)
in (FStar_Range.end_of_line uu____3571))
in (process_preceding_comments doc uu____3569 uu____3570 (Prims.parse_int "0") comments)))
in (match (uu____3563) with
| (doc, comments) -> begin
(

let uu____3586 = (FStar_Util.take (fun uu___131_3597 -> (match (uu___131_3597) with
| (uu____3600, range) -> begin
(FStar_Range.range_contains_range current_range range)
end)) comments)
in (match (uu____3586) with
| (inner_comments, comments) -> begin
((FStar_ST.write comment_stack inner_comments);
(

let doc = (

let uu____3629 = (decl_to_document decl)
in (FStar_Pprint.op_Hat_Hat doc uu____3629))
in (

let inner_comments_doc = (

let uu____3631 = (

let uu____3632 = (FStar_ST.read comment_stack)
in (uu____3632 = []))
in (match (uu____3631) with
| true -> begin
FStar_Pprint.empty
end
| uu____3646 -> begin
((

let uu____3648 = (

let uu____3649 = (

let uu____3651 = (FStar_ST.read comment_stack)
in (FStar_List.map Prims.fst uu____3651))
in (FStar_String.concat " ; " uu____3649))
in (FStar_Util.print1_warning "Leftover comments : %s\n" uu____3648));
(

let uu____3662 = (FStar_ST.read comment_stack)
in (comments_to_document uu____3662));
)
end))
in (

let uu____3671 = (FStar_Range.end_of_range decl.FStar_Parser_AST.drange)
in (

let uu____3672 = (FStar_Pprint.op_Hat_Hat doc inner_comments_doc)
in ((uu____3671), (comments), (uu____3672))))));
)
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
| (d)::uu____3696 -> begin
(

let uu____3698 = (FStar_List.fold_left aux ((FStar_Range.zeroPos), (comments), (FStar_Pprint.empty)) decls)
in (match (uu____3698) with
| (uu____3719, comments, doc) -> begin
((doc), (comments))
end))
end))))




