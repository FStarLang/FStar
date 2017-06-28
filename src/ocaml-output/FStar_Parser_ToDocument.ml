
open Prims
open FStar_Pervasives

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

let uu____50 = (

let uu____51 = (FStar_ST.read should_unparen)
in (not (uu____51)))
in (match (uu____50) with
| true -> begin
t
end
| uu____54 -> begin
(match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t1) -> begin
(unparen t1)
end
| uu____56 -> begin
t
end)
end)))


let str : Prims.string  ->  FStar_Pprint.document = (fun s -> (FStar_Pprint.doc_of_string s))


let default_or_map = (fun n1 f x -> (match (x) with
| FStar_Pervasives_Native.None -> begin
n1
end
| FStar_Pervasives_Native.Some (x') -> begin
(f x')
end))


let prefix2 : FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun prefix_ body -> (FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "1") prefix_ body))


let op_Hat_Slash_Plus_Hat : FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun prefix_ body -> (prefix2 prefix_ body))


let jump2 : FStar_Pprint.document  ->  FStar_Pprint.document = (fun body -> (FStar_Pprint.jump (Prims.parse_int "2") (Prims.parse_int "1") body))


let infix2 : FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (FStar_Pprint.infix (Prims.parse_int "2") (Prims.parse_int "1"))


let infix0 : FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (FStar_Pprint.infix (Prims.parse_int "0") (Prims.parse_int "1"))


let break1 : FStar_Pprint.document = (FStar_Pprint.break_ (Prims.parse_int "1"))


let separate_break_map = (fun sep f l -> (

let uu____159 = (

let uu____160 = (

let uu____161 = (FStar_Pprint.op_Hat_Hat sep break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____161))
in (FStar_Pprint.separate_map uu____160 f l))
in (FStar_Pprint.group uu____159)))


let precede_break_separate_map = (fun prec sep f l -> (

let uu____196 = (

let uu____197 = (FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space)
in (

let uu____198 = (

let uu____199 = (FStar_List.hd l)
in (FStar_All.pipe_right uu____199 f))
in (FStar_Pprint.precede uu____197 uu____198)))
in (

let uu____200 = (

let uu____201 = (FStar_List.tl l)
in (FStar_Pprint.concat_map (fun x -> (

let uu____206 = (

let uu____207 = (

let uu____208 = (f x)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____208))
in (FStar_Pprint.op_Hat_Hat sep uu____207))
in (FStar_Pprint.op_Hat_Hat break1 uu____206))) uu____201))
in (FStar_Pprint.op_Hat_Hat uu____196 uu____200))))


let concat_break_map = (fun f l -> (

let uu____231 = (FStar_Pprint.concat_map (fun x -> (

let uu____235 = (f x)
in (FStar_Pprint.op_Hat_Hat uu____235 break1))) l)
in (FStar_Pprint.group uu____231)))


let parens_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lparen contents FStar_Pprint.rparen))


let soft_parens_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lparen contents FStar_Pprint.rparen))


let braces_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbrace contents FStar_Pprint.rbrace))


let soft_braces_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbrace contents FStar_Pprint.rbrace))


let brackets_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbracket contents FStar_Pprint.rbracket))


let soft_brackets_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbracket contents FStar_Pprint.rbracket))


let soft_begin_end_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (

let uu____264 = (str "begin")
in (

let uu____265 = (str "end")
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") uu____264 contents uu____265))))


let separate_map_or_flow = (fun sep f l -> (match (((FStar_List.length l) < (Prims.parse_int "10"))) with
| true -> begin
(FStar_Pprint.separate_map sep f l)
end
| uu____300 -> begin
(FStar_Pprint.flow_map sep f l)
end))


let soft_surround_separate_map = (fun n1 b void_ opening sep closing f xs -> (match ((xs = [])) with
| true -> begin
void_
end
| uu____360 -> begin
(

let uu____361 = (FStar_Pprint.separate_map sep f xs)
in (FStar_Pprint.soft_surround n1 b opening uu____361 closing))
end))


let doc_of_fsdoc : (Prims.string * (Prims.string * Prims.string) Prims.list)  ->  FStar_Pprint.document = (fun uu____370 -> (match (uu____370) with
| (comment, keywords1) -> begin
(

let uu____384 = (

let uu____385 = (

let uu____387 = (str comment)
in (

let uu____388 = (

let uu____390 = (

let uu____392 = (FStar_Pprint.separate_map FStar_Pprint.comma (fun uu____399 -> (match (uu____399) with
| (k, v1) -> begin
(

let uu____404 = (

let uu____406 = (str k)
in (

let uu____407 = (

let uu____409 = (

let uu____411 = (str v1)
in (uu____411)::[])
in (FStar_Pprint.rarrow)::uu____409)
in (uu____406)::uu____407))
in (FStar_Pprint.concat uu____404))
end)) keywords1)
in (uu____392)::[])
in (FStar_Pprint.space)::uu____390)
in (uu____387)::uu____388))
in (FStar_Pprint.concat uu____385))
in (FStar_Pprint.group uu____384))
end))


let is_unit : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____416 = (

let uu____417 = (unparen e)
in uu____417.FStar_Parser_AST.tm)
in (match (uu____416) with
| FStar_Parser_AST.Const (FStar_Const.Const_unit) -> begin
true
end
| uu____418 -> begin
false
end)))


let matches_var : FStar_Parser_AST.term  ->  FStar_Ident.ident  ->  Prims.bool = (fun t x -> (

let uu____427 = (

let uu____428 = (unparen t)
in uu____428.FStar_Parser_AST.tm)
in (match (uu____427) with
| FStar_Parser_AST.Var (y) -> begin
(x.FStar_Ident.idText = (FStar_Ident.text_of_lid y))
end
| uu____430 -> begin
false
end)))


let is_tuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Parser_Const.is_tuple_data_lid'


let is_dtuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Parser_Const.is_dtuple_data_lid'


let is_list_structure : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun cons_lid1 nil_lid1 -> (

let rec aux = (fun e -> (

let uu____452 = (

let uu____453 = (unparen e)
in uu____453.FStar_Parser_AST.tm)
in (match (uu____452) with
| FStar_Parser_AST.Construct (lid, []) -> begin
(FStar_Ident.lid_equals lid nil_lid1)
end
| FStar_Parser_AST.Construct (lid, (uu____461)::((e2, uu____463))::[]) -> begin
((FStar_Ident.lid_equals lid cons_lid1) && (aux e2))
end
| uu____475 -> begin
false
end)))
in aux))


let is_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Parser_Const.cons_lid FStar_Parser_Const.nil_lid)


let is_lex_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Parser_Const.lexcons_lid FStar_Parser_Const.lextop_lid)


let rec extract_from_list : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (

let uu____487 = (

let uu____488 = (unparen e)
in uu____488.FStar_Parser_AST.tm)
in (match (uu____487) with
| FStar_Parser_AST.Construct (uu____490, []) -> begin
[]
end
| FStar_Parser_AST.Construct (uu____496, ((e1, FStar_Parser_AST.Nothing))::((e2, FStar_Parser_AST.Nothing))::[]) -> begin
(

let uu____508 = (extract_from_list e2)
in (e1)::uu____508)
end
| uu____510 -> begin
(

let uu____511 = (

let uu____512 = (FStar_Parser_AST.term_to_string e)
in (FStar_Util.format1 "Not a list %s" uu____512))
in (failwith uu____511))
end)))


let is_array : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____518 = (

let uu____519 = (unparen e)
in uu____519.FStar_Parser_AST.tm)
in (match (uu____518) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (lid); FStar_Parser_AST.range = uu____521; FStar_Parser_AST.level = uu____522}, l, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) && (is_list l))
end
| uu____524 -> begin
false
end)))


let rec is_ref_set : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____529 = (

let uu____530 = (unparen e)
in uu____530.FStar_Parser_AST.tm)
in (match (uu____529) with
| FStar_Parser_AST.Var (maybe_empty_lid) -> begin
(FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.tset_empty)
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_singleton_lid); FStar_Parser_AST.range = uu____533; FStar_Parser_AST.level = uu____534}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_ref_lid); FStar_Parser_AST.range = uu____536; FStar_Parser_AST.level = uu____537}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____539; FStar_Parser_AST.level = uu____540}, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals maybe_singleton_lid FStar_Parser_Const.tset_singleton) && (FStar_Ident.lid_equals maybe_ref_lid FStar_Parser_Const.heap_ref))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_union_lid); FStar_Parser_AST.range = uu____542; FStar_Parser_AST.level = uu____543}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____545; FStar_Parser_AST.level = uu____546}, e2, FStar_Parser_AST.Nothing) -> begin
(((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.tset_union) && (is_ref_set e1)) && (is_ref_set e2))
end
| uu____548 -> begin
false
end)))


let rec extract_from_ref_set : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (

let uu____554 = (

let uu____555 = (unparen e)
in uu____555.FStar_Parser_AST.tm)
in (match (uu____554) with
| FStar_Parser_AST.Var (uu____557) -> begin
[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (uu____558); FStar_Parser_AST.range = uu____559; FStar_Parser_AST.level = uu____560}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (uu____561); FStar_Parser_AST.range = uu____562; FStar_Parser_AST.level = uu____563}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____565; FStar_Parser_AST.level = uu____566}, FStar_Parser_AST.Nothing) -> begin
(e1)::[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (uu____567); FStar_Parser_AST.range = uu____568; FStar_Parser_AST.level = uu____569}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____571; FStar_Parser_AST.level = uu____572}, e2, FStar_Parser_AST.Nothing) -> begin
(

let uu____574 = (extract_from_ref_set e1)
in (

let uu____576 = (extract_from_ref_set e2)
in (FStar_List.append uu____574 uu____576)))
end
| uu____578 -> begin
(

let uu____579 = (

let uu____580 = (FStar_Parser_AST.term_to_string e)
in (FStar_Util.format1 "Not a ref set %s" uu____580))
in (failwith uu____579))
end)))


let is_general_application : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____586 = ((is_array e) || (is_ref_set e))
in (not (uu____586))))


let is_general_construction : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____591 = ((is_list e) || (is_lex_list e))
in (not (uu____591))))


let is_general_prefix_op : FStar_Ident.ident  ->  Prims.bool = (fun op -> (

let op_starting_char = (FStar_Util.char_at (FStar_Ident.text_of_id op) (Prims.parse_int "0"))
in (((op_starting_char = '!') || (op_starting_char = '?')) || ((op_starting_char = '~') && ((FStar_Ident.text_of_id op) <> "~")))))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun e -> (

let rec aux = (fun e1 acc -> (

let uu____624 = (

let uu____625 = (unparen e1)
in uu____625.FStar_Parser_AST.tm)
in (match (uu____624) with
| FStar_Parser_AST.App (head1, arg, imp) -> begin
(aux head1 ((((arg), (imp)))::acc))
end
| uu____636 -> begin
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
| uu____646 -> begin
false
end))


let uu___is_Right : associativity  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Right -> begin
true
end
| uu____651 -> begin
false
end))


let uu___is_NonAssoc : associativity  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NonAssoc -> begin
true
end
| uu____656 -> begin
false
end))


type token =
(FStar_Char.char, Prims.string) FStar_Util.either


type associativity_level =
(associativity * token Prims.list)


let token_to_string : (FStar_BaseTypes.char, Prims.string) FStar_Util.either  ->  Prims.string = (fun uu___93_667 -> (match (uu___93_667) with
| FStar_Util.Inl (c) -> begin
(Prims.strcat (FStar_Util.string_of_char c) ".*")
end
| FStar_Util.Inr (s) -> begin
s
end))


let matches_token : Prims.string  ->  (FStar_Char.char, Prims.string) FStar_Util.either  ->  Prims.bool = (fun s uu___94_681 -> (match (uu___94_681) with
| FStar_Util.Inl (c) -> begin
(

let uu____685 = (FStar_String.get s (Prims.parse_int "0"))
in (uu____685 = c))
end
| FStar_Util.Inr (s') -> begin
(s = s')
end))


let matches_level = (fun s uu____706 -> (match (uu____706) with
| (assoc_levels, tokens) -> begin
(

let uu____720 = (FStar_List.tryFind (matches_token s) tokens)
in (uu____720 <> FStar_Pervasives_Native.None))
end))


let opinfix4 = (fun uu____739 -> ((Right), ((FStar_Util.Inr ("**"))::[])))


let opinfix3 = (fun uu____755 -> ((Left), ((FStar_Util.Inl ('*'))::(FStar_Util.Inl ('/'))::(FStar_Util.Inl ('%'))::[])))


let opinfix2 = (fun uu____775 -> ((Left), ((FStar_Util.Inl ('+'))::(FStar_Util.Inl ('-'))::[])))


let minus_lvl = (fun uu____793 -> ((Left), ((FStar_Util.Inr ("-"))::[])))


let opinfix1 = (fun uu____809 -> ((Right), ((FStar_Util.Inl ('@'))::(FStar_Util.Inl ('^'))::[])))


let pipe_right = (fun uu____827 -> ((Left), ((FStar_Util.Inr ("|>"))::[])))


let opinfix0d = (fun uu____843 -> ((Left), ((FStar_Util.Inl ('$'))::[])))


let opinfix0c = (fun uu____859 -> ((Left), ((FStar_Util.Inl ('='))::(FStar_Util.Inl ('<'))::(FStar_Util.Inl ('>'))::[])))


let equal = (fun uu____879 -> ((Left), ((FStar_Util.Inr ("="))::[])))


let opinfix0b = (fun uu____895 -> ((Left), ((FStar_Util.Inl ('&'))::[])))


let opinfix0a = (fun uu____911 -> ((Left), ((FStar_Util.Inl ('|'))::[])))


let colon_equals = (fun uu____927 -> ((NonAssoc), ((FStar_Util.Inr (":="))::[])))


let amp = (fun uu____943 -> ((Right), ((FStar_Util.Inr ("&"))::[])))


let colon_colon = (fun uu____959 -> ((Right), ((FStar_Util.Inr ("::"))::[])))


let level_associativity_spec : (associativity * (FStar_Char.char, Prims.string) FStar_Util.either Prims.list) Prims.list = ((opinfix4 ()))::((opinfix3 ()))::((opinfix2 ()))::((opinfix1 ()))::((pipe_right ()))::((opinfix0d ()))::((opinfix0c ()))::((opinfix0b ()))::((opinfix0a ()))::((colon_equals ()))::((amp ()))::((colon_colon ()))::[]


let level_table : ((Prims.int * Prims.int * Prims.int) * (FStar_Char.char, Prims.string) FStar_Util.either Prims.list) Prims.list = (

let levels_from_associativity = (fun l uu___95_1056 -> (match (uu___95_1056) with
| Left -> begin
((l), (l), ((l - (Prims.parse_int "1"))))
end
| Right -> begin
(((l - (Prims.parse_int "1"))), (l), (l))
end
| NonAssoc -> begin
((l), (l), (l))
end))
in (FStar_List.mapi (fun i uu____1078 -> (match (uu____1078) with
| (assoc1, tokens) -> begin
(((levels_from_associativity i assoc1)), (tokens))
end)) level_associativity_spec))


let assign_levels : associativity_level Prims.list  ->  Prims.string  ->  (Prims.int * Prims.int * Prims.int) = (fun token_associativity_spec s -> (

let uu____1122 = (FStar_List.tryFind (matches_level s) level_table)
in (match (uu____1122) with
| FStar_Pervasives_Native.Some (assoc_levels, uu____1147) -> begin
assoc_levels
end
| uu____1168 -> begin
(failwith (Prims.strcat "Unrecognized operator " s))
end)))


let max : Prims.int  ->  Prims.int  ->  Prims.int = (fun k1 k2 -> (match ((k1 > k2)) with
| true -> begin
k1
end
| uu____1189 -> begin
k2
end))


let max_level = (fun l -> (

let find_level_and_max = (fun n1 level -> (

let uu____1228 = (FStar_List.tryFind (fun uu____1249 -> (match (uu____1249) with
| (uu____1258, tokens) -> begin
(tokens = (FStar_Pervasives_Native.snd level))
end)) level_table)
in (match (uu____1228) with
| FStar_Pervasives_Native.Some ((uu____1278, l1, uu____1280), uu____1281) -> begin
(max n1 l1)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____1307 = (

let uu____1308 = (

let uu____1309 = (FStar_List.map token_to_string (FStar_Pervasives_Native.snd level))
in (FStar_String.concat "," uu____1309))
in (FStar_Util.format1 "Undefined associativity level %s" uu____1308))
in (failwith uu____1307))
end)))
in (FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l)))


let levels : Prims.string  ->  (Prims.int * Prims.int * Prims.int) = (assign_levels level_associativity_spec)


let operatorInfix0ad12 = (fun uu____1336 -> ((opinfix0a ()))::((opinfix0b ()))::((opinfix0c ()))::((opinfix0d ()))::((opinfix1 ()))::((opinfix2 ()))::[])


let is_operatorInfix0ad12 : FStar_Ident.ident  ->  Prims.bool = (fun op -> (

let uu____1376 = (

let uu____1383 = (FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op))
in (FStar_List.tryFind uu____1383 (operatorInfix0ad12 ())))
in (uu____1376 <> FStar_Pervasives_Native.None)))


let is_operatorInfix34 : FStar_Ident.ident  ->  Prims.bool = (

let opinfix34 = ((opinfix3 ()))::((opinfix4 ()))::[]
in (fun op -> (

let uu____1440 = (

let uu____1447 = (FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op))
in (FStar_List.tryFind uu____1447 opinfix34))
in (uu____1440 <> FStar_Pervasives_Native.None))))


let handleable_args_length : FStar_Ident.ident  ->  Prims.int = (fun op -> (

let op_s = (FStar_Ident.text_of_id op)
in (

let uu____1483 = ((is_general_prefix_op op) || (FStar_List.mem op_s (("-")::("~")::[])))
in (match (uu____1483) with
| true -> begin
(Prims.parse_int "1")
end
| uu____1484 -> begin
(

let uu____1485 = (((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) || (FStar_List.mem op_s (("<==>")::("==>")::("\\/")::("/\\")::("=")::("|>")::(":=")::(".()")::(".[]")::[])))
in (match (uu____1485) with
| true -> begin
(Prims.parse_int "2")
end
| uu____1486 -> begin
(match ((FStar_List.mem op_s ((".()<-")::(".[]<-")::[]))) with
| true -> begin
(Prims.parse_int "3")
end
| uu____1487 -> begin
(Prims.parse_int "0")
end)
end))
end))))


let handleable_op = (fun op args -> (match ((FStar_List.length args)) with
| _0_27 when (_0_27 = (Prims.parse_int "0")) -> begin
true
end
| _0_28 when (_0_28 = (Prims.parse_int "1")) -> begin
((is_general_prefix_op op) || (FStar_List.mem (FStar_Ident.text_of_id op) (("-")::("~")::[])))
end
| _0_29 when (_0_29 = (Prims.parse_int "2")) -> begin
(((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) || (FStar_List.mem (FStar_Ident.text_of_id op) (("<==>")::("==>")::("\\/")::("/\\")::("=")::("|>")::(":=")::(".()")::(".[]")::[])))
end
| _0_30 when (_0_30 = (Prims.parse_int "3")) -> begin
(FStar_List.mem (FStar_Ident.text_of_id op) ((".()<-")::(".[]<-")::[]))
end
| uu____1507 -> begin
false
end))


let comment_stack : (Prims.string * FStar_Range.range) Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let with_comment = (fun printer tm tmrange -> (

let rec comments_before_pos = (fun acc print_pos lookahead_pos -> (

let uu____1557 = (FStar_ST.read comment_stack)
in (match (uu____1557) with
| [] -> begin
((acc), (false))
end
| ((comment, crange))::cs -> begin
(

let uu____1578 = (FStar_Range.range_before_pos crange print_pos)
in (match (uu____1578) with
| true -> begin
((FStar_ST.write comment_stack cs);
(

let uu____1587 = (

let uu____1588 = (

let uu____1589 = (str comment)
in (FStar_Pprint.op_Hat_Hat uu____1589 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat acc uu____1588))
in (comments_before_pos uu____1587 print_pos lookahead_pos));
)
end
| uu____1590 -> begin
(

let uu____1591 = (FStar_Range.range_before_pos crange lookahead_pos)
in ((acc), (uu____1591)))
end))
end)))
in (

let uu____1592 = (

let uu____1595 = (

let uu____1596 = (FStar_Range.start_of_range tmrange)
in (FStar_Range.end_of_line uu____1596))
in (

let uu____1597 = (FStar_Range.end_of_range tmrange)
in (comments_before_pos FStar_Pprint.empty uu____1595 uu____1597)))
in (match (uu____1592) with
| (comments, has_lookahead) -> begin
(

let printed_e = (printer tm)
in (

let comments1 = (match (has_lookahead) with
| true -> begin
(

let pos = (FStar_Range.end_of_range tmrange)
in (

let uu____1603 = (comments_before_pos comments pos pos)
in (FStar_Pervasives_Native.fst uu____1603)))
end
| uu____1606 -> begin
comments
end)
in (

let uu____1607 = (FStar_Pprint.op_Hat_Hat comments1 printed_e)
in (FStar_Pprint.group uu____1607))))
end))))


let rec place_comments_until_pos : Prims.int  ->  Prims.int  ->  FStar_Range.pos  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun k lbegin pos_end doc1 -> (

let uu____1624 = (FStar_ST.read comment_stack)
in (match (uu____1624) with
| ((comment, crange))::cs when (FStar_Range.range_before_pos crange pos_end) -> begin
((FStar_ST.write comment_stack cs);
(

let lnum = (

let uu____1648 = (

let uu____1649 = (

let uu____1650 = (FStar_Range.start_of_range crange)
in (FStar_Range.line_of_pos uu____1650))
in (uu____1649 - lbegin))
in (max k uu____1648))
in (

let doc2 = (

let uu____1652 = (

let uu____1653 = (FStar_Pprint.repeat lnum FStar_Pprint.hardline)
in (

let uu____1654 = (str comment)
in (FStar_Pprint.op_Hat_Hat uu____1653 uu____1654)))
in (FStar_Pprint.op_Hat_Hat doc1 uu____1652))
in (

let uu____1655 = (

let uu____1656 = (FStar_Range.end_of_range crange)
in (FStar_Range.line_of_pos uu____1656))
in (place_comments_until_pos (Prims.parse_int "1") uu____1655 pos_end doc2))));
)
end
| uu____1657 -> begin
(

let lnum = (

let uu____1662 = (

let uu____1663 = (FStar_Range.line_of_pos pos_end)
in (uu____1663 - lbegin))
in (max (Prims.parse_int "1") uu____1662))
in (

let uu____1664 = (FStar_Pprint.repeat lnum FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat doc1 uu____1664)))
end)))


let separate_map_with_comments = (fun prefix1 sep f xs extract_range -> (

let fold_fun = (fun uu____1719 x -> (match (uu____1719) with
| (last_line, doc1) -> begin
(

let r = (extract_range x)
in (

let doc2 = (

let uu____1729 = (FStar_Range.start_of_range r)
in (place_comments_until_pos (Prims.parse_int "1") last_line uu____1729 doc1))
in (

let uu____1730 = (

let uu____1731 = (FStar_Range.end_of_range r)
in (FStar_Range.line_of_pos uu____1731))
in (

let uu____1732 = (

let uu____1733 = (

let uu____1734 = (f x)
in (FStar_Pprint.op_Hat_Hat sep uu____1734))
in (FStar_Pprint.op_Hat_Hat doc2 uu____1733))
in ((uu____1730), (uu____1732))))))
end))
in (

let uu____1735 = (

let uu____1739 = (FStar_List.hd xs)
in (

let uu____1740 = (FStar_List.tl xs)
in ((uu____1739), (uu____1740))))
in (match (uu____1735) with
| (x, xs1) -> begin
(

let init1 = (

let uu____1750 = (

let uu____1751 = (

let uu____1752 = (extract_range x)
in (FStar_Range.end_of_range uu____1752))
in (FStar_Range.line_of_pos uu____1751))
in (

let uu____1753 = (

let uu____1754 = (f x)
in (FStar_Pprint.op_Hat_Hat prefix1 uu____1754))
in ((uu____1750), (uu____1753))))
in (

let uu____1755 = (FStar_List.fold_left fold_fun init1 xs1)
in (FStar_Pervasives_Native.snd uu____1755)))
end))))


let rec p_decl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (

let uu____1999 = (

let uu____2000 = (FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc)
in (

let uu____2001 = (

let uu____2002 = (p_attributes d.FStar_Parser_AST.attrs)
in (

let uu____2003 = (

let uu____2004 = (p_qualifiers d.FStar_Parser_AST.quals)
in (

let uu____2005 = (

let uu____2006 = (p_rawDecl d)
in (FStar_Pprint.op_Hat_Hat (match ((d.FStar_Parser_AST.quals = [])) with
| true -> begin
FStar_Pprint.empty
end
| uu____2007 -> begin
break1
end) uu____2006))
in (FStar_Pprint.op_Hat_Hat uu____2004 uu____2005)))
in (FStar_Pprint.op_Hat_Hat uu____2002 uu____2003)))
in (FStar_Pprint.op_Hat_Hat uu____2000 uu____2001)))
in (FStar_Pprint.group uu____1999)))
and p_attributes : FStar_Parser_AST.attributes_  ->  FStar_Pprint.document = (fun attrs -> (

let uu____2009 = (

let uu____2010 = (str "@")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____2010))
in (

let uu____2011 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline)
in (soft_surround_separate_map (Prims.parse_int "0") (Prims.parse_int "2") FStar_Pprint.empty uu____2009 FStar_Pprint.space uu____2011 p_atomicTerm attrs))))
and p_fsdoc : FStar_Parser_AST.fsdoc  ->  FStar_Pprint.document = (fun uu____2012 -> (match (uu____2012) with
| (doc1, kwd_args) -> begin
(

let kwd_args_doc = (match (kwd_args) with
| [] -> begin
FStar_Pprint.empty
end
| kwd_args1 -> begin
(

let process_kwd_arg = (fun uu____2033 -> (match (uu____2033) with
| (kwd1, arg) -> begin
(

let uu____2038 = (str "@")
in (

let uu____2039 = (

let uu____2040 = (str kwd1)
in (

let uu____2041 = (

let uu____2042 = (str arg)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2042))
in (FStar_Pprint.op_Hat_Hat uu____2040 uu____2041)))
in (FStar_Pprint.op_Hat_Hat uu____2038 uu____2039)))
end))
in (

let uu____2043 = (

let uu____2044 = (FStar_Pprint.separate_map FStar_Pprint.hardline process_kwd_arg kwd_args1)
in (FStar_Pprint.op_Hat_Hat uu____2044 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____2043)))
end)
in (

let uu____2047 = (

let uu____2048 = (

let uu____2049 = (

let uu____2050 = (

let uu____2051 = (str doc1)
in (

let uu____2052 = (

let uu____2053 = (

let uu____2054 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____2054))
in (FStar_Pprint.op_Hat_Hat kwd_args_doc uu____2053))
in (FStar_Pprint.op_Hat_Hat uu____2051 uu____2052)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____2050))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____2049))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2048))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____2047)))
end))
and p_rawDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Open (uid) -> begin
(

let uu____2057 = (

let uu____2058 = (str "open")
in (

let uu____2059 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2058 uu____2059)))
in (FStar_Pprint.group uu____2057))
end
| FStar_Parser_AST.Include (uid) -> begin
(

let uu____2061 = (

let uu____2062 = (str "include")
in (

let uu____2063 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2062 uu____2063)))
in (FStar_Pprint.group uu____2061))
end
| FStar_Parser_AST.ModuleAbbrev (uid1, uid2) -> begin
(

let uu____2066 = (

let uu____2067 = (str "module")
in (

let uu____2068 = (

let uu____2069 = (

let uu____2070 = (p_uident uid1)
in (

let uu____2071 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____2070 uu____2071)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2069))
in (FStar_Pprint.op_Hat_Hat uu____2067 uu____2068)))
in (

let uu____2072 = (p_quident uid2)
in (op_Hat_Slash_Plus_Hat uu____2066 uu____2072)))
end
| FStar_Parser_AST.TopLevelModule (uid) -> begin
(

let uu____2074 = (

let uu____2075 = (str "module")
in (

let uu____2076 = (

let uu____2077 = (p_quident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2077))
in (FStar_Pprint.op_Hat_Hat uu____2075 uu____2076)))
in (FStar_Pprint.group uu____2074))
end
| FStar_Parser_AST.Tycon (true, ((FStar_Parser_AST.TyconAbbrev (uid, tpars, FStar_Pervasives_Native.None, t), FStar_Pervasives_Native.None))::[]) -> begin
(

let effect_prefix_doc = (

let uu____2096 = (str "effect")
in (

let uu____2097 = (

let uu____2098 = (p_uident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2098))
in (FStar_Pprint.op_Hat_Hat uu____2096 uu____2097)))
in (

let uu____2099 = (

let uu____2100 = (p_typars tpars)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") effect_prefix_doc uu____2100 FStar_Pprint.equals))
in (

let uu____2101 = (p_typ t)
in (op_Hat_Slash_Plus_Hat uu____2099 uu____2101))))
end
| FStar_Parser_AST.Tycon (false, tcdefs) -> begin
(

let uu____2111 = (str "type")
in (

let uu____2112 = (str "and")
in (precede_break_separate_map uu____2111 uu____2112 p_fsdocTypeDeclPairs tcdefs)))
end
| FStar_Parser_AST.TopLevelLet (q, lbs) -> begin
(

let let_doc = (

let uu____2125 = (str "let")
in (

let uu____2126 = (

let uu____2127 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat uu____2127 FStar_Pprint.space))
in (FStar_Pprint.op_Hat_Hat uu____2125 uu____2126)))
in (

let uu____2128 = (

let uu____2129 = (str "and")
in (FStar_Pprint.op_Hat_Hat uu____2129 FStar_Pprint.space))
in (separate_map_with_comments let_doc uu____2128 p_letbinding lbs (fun uu____2135 -> (match (uu____2135) with
| (p, t) -> begin
(FStar_Range.union_ranges p.FStar_Parser_AST.prange t.FStar_Parser_AST.range)
end)))))
end
| FStar_Parser_AST.Val (lid, t) -> begin
(

let uu____2142 = (

let uu____2143 = (str "val")
in (

let uu____2144 = (

let uu____2145 = (

let uu____2146 = (p_lident lid)
in (

let uu____2147 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat uu____2146 uu____2147)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2145))
in (FStar_Pprint.op_Hat_Hat uu____2143 uu____2144)))
in (

let uu____2148 = (p_typ t)
in (op_Hat_Slash_Plus_Hat uu____2142 uu____2148)))
end
| FStar_Parser_AST.Assume (id, t) -> begin
(

let decl_keyword = (

let uu____2152 = (

let uu____2153 = (FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_All.pipe_right uu____2153 FStar_Util.is_upper))
in (match (uu____2152) with
| true -> begin
FStar_Pprint.empty
end
| uu____2154 -> begin
(

let uu____2155 = (str "val")
in (FStar_Pprint.op_Hat_Hat uu____2155 FStar_Pprint.space))
end))
in (

let uu____2156 = (

let uu____2157 = (

let uu____2158 = (p_ident id)
in (

let uu____2159 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat uu____2158 uu____2159)))
in (FStar_Pprint.op_Hat_Hat decl_keyword uu____2157))
in (

let uu____2160 = (p_typ t)
in (op_Hat_Slash_Plus_Hat uu____2156 uu____2160))))
end
| FStar_Parser_AST.Exception (uid, t_opt) -> begin
(

let uu____2165 = (str "exception")
in (

let uu____2166 = (

let uu____2167 = (

let uu____2168 = (p_uident uid)
in (

let uu____2169 = (FStar_Pprint.optional (fun t -> (

let uu____2174 = (str "of")
in (

let uu____2175 = (p_typ t)
in (op_Hat_Slash_Plus_Hat uu____2174 uu____2175)))) t_opt)
in (FStar_Pprint.op_Hat_Hat uu____2168 uu____2169)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2167))
in (FStar_Pprint.op_Hat_Hat uu____2165 uu____2166)))
end
| FStar_Parser_AST.NewEffect (ne) -> begin
(

let uu____2177 = (str "new_effect")
in (

let uu____2178 = (

let uu____2179 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2179))
in (FStar_Pprint.op_Hat_Hat uu____2177 uu____2178)))
end
| FStar_Parser_AST.SubEffect (se) -> begin
(

let uu____2181 = (str "sub_effect")
in (

let uu____2182 = (

let uu____2183 = (p_subEffect se)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2183))
in (FStar_Pprint.op_Hat_Hat uu____2181 uu____2182)))
end
| FStar_Parser_AST.Pragma (p) -> begin
(p_pragma p)
end
| FStar_Parser_AST.Fsdoc (doc1) -> begin
(

let uu____2186 = (p_fsdoc doc1)
in (FStar_Pprint.op_Hat_Hat uu____2186 FStar_Pprint.hardline))
end
| FStar_Parser_AST.Main (uu____2187) -> begin
(failwith "*Main declaration* : Is that really still in use ??")
end
| FStar_Parser_AST.Tycon (true, uu____2188) -> begin
(failwith "Effect abbreviation is expected to be defined by an abbreviation")
end))
and p_pragma : FStar_Parser_AST.pragma  ->  FStar_Pprint.document = (fun uu___96_2197 -> (match (uu___96_2197) with
| FStar_Parser_AST.SetOptions (s) -> begin
(

let uu____2199 = (str "#set-options")
in (

let uu____2200 = (

let uu____2201 = (

let uu____2202 = (str s)
in (FStar_Pprint.dquotes uu____2202))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2201))
in (FStar_Pprint.op_Hat_Hat uu____2199 uu____2200)))
end
| FStar_Parser_AST.ResetOptions (s_opt) -> begin
(

let uu____2205 = (str "#reset-options")
in (

let uu____2206 = (FStar_Pprint.optional (fun s -> (

let uu____2210 = (

let uu____2211 = (str s)
in (FStar_Pprint.dquotes uu____2211))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2210))) s_opt)
in (FStar_Pprint.op_Hat_Hat uu____2205 uu____2206)))
end
| FStar_Parser_AST.LightOff -> begin
((FStar_ST.write should_print_fs_typ_app true);
(str "#light \"off\"");
)
end))
and p_typars : FStar_Parser_AST.binder Prims.list  ->  FStar_Pprint.document = (fun bs -> (p_binders true bs))
and p_fsdocTypeDeclPairs : (FStar_Parser_AST.tycon * FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option)  ->  FStar_Pprint.document = (fun uu____2217 -> (match (uu____2217) with
| (typedecl, fsdoc_opt) -> begin
(

let uu____2225 = (FStar_Pprint.optional p_fsdoc fsdoc_opt)
in (

let uu____2226 = (p_typeDecl typedecl)
in (FStar_Pprint.op_Hat_Hat uu____2225 uu____2226)))
end))
and p_typeDecl : FStar_Parser_AST.tycon  ->  FStar_Pprint.document = (fun uu___97_2227 -> (match (uu___97_2227) with
| FStar_Parser_AST.TyconAbstract (lid, bs, typ_opt) -> begin
(

let empty' = (fun uu____2238 -> FStar_Pprint.empty)
in (p_typeDeclPrefix lid bs typ_opt empty'))
end
| FStar_Parser_AST.TyconAbbrev (lid, bs, typ_opt, t) -> begin
(

let f = (fun uu____2250 -> (

let uu____2251 = (p_typ t)
in (prefix2 FStar_Pprint.equals uu____2251)))
in (p_typeDeclPrefix lid bs typ_opt f))
end
| FStar_Parser_AST.TyconRecord (lid, bs, typ_opt, record_field_decls) -> begin
(

let p_recordFieldAndComments = (fun uu____2277 -> (match (uu____2277) with
| (lid1, t, doc_opt) -> begin
(

let uu____2287 = (FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range)
in (with_comment p_recordFieldDecl ((lid1), (t), (doc_opt)) uu____2287))
end))
in (

let p_fields = (fun uu____2296 -> (

let uu____2297 = (

let uu____2298 = (

let uu____2299 = (

let uu____2300 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (FStar_Pprint.separate_map uu____2300 p_recordFieldAndComments record_field_decls))
in (braces_with_nesting uu____2299))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2298))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____2297)))
in (p_typeDeclPrefix lid bs typ_opt p_fields)))
end
| FStar_Parser_AST.TyconVariant (lid, bs, typ_opt, ct_decls) -> begin
(

let p_constructorBranchAndComments = (fun uu____2336 -> (match (uu____2336) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let range = (

let uu____2352 = (

let uu____2353 = (FStar_Util.map_opt t_opt (fun t -> t.FStar_Parser_AST.range))
in (FStar_Util.dflt uid.FStar_Ident.idRange uu____2353))
in (FStar_Range.extend_to_end_of_line uu____2352))
in (

let p_constructorBranch = (fun decl -> (

let uu____2373 = (

let uu____2374 = (

let uu____2375 = (p_constructorDecl decl)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2375))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____2374))
in (FStar_Pprint.group uu____2373)))
in (with_comment p_constructorBranch ((uid), (t_opt), (doc_opt), (use_of)) range)))
end))
in (

let datacon_doc = (fun uu____2387 -> (

let uu____2388 = (FStar_Pprint.separate_map break1 p_constructorBranchAndComments ct_decls)
in (FStar_Pprint.group uu____2388)))
in (p_typeDeclPrefix lid bs typ_opt (fun uu____2397 -> (

let uu____2398 = (datacon_doc ())
in (prefix2 FStar_Pprint.equals uu____2398))))))
end))
and p_typeDeclPrefix : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.knd FStar_Pervasives_Native.option  ->  (Prims.unit  ->  FStar_Pprint.document)  ->  FStar_Pprint.document = (fun lid bs typ_opt cont -> (match (((bs = []) && (typ_opt = FStar_Pervasives_Native.None))) with
| true -> begin
(

let uu____2409 = (p_ident lid)
in (

let uu____2410 = (

let uu____2411 = (cont ())
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2411))
in (FStar_Pprint.op_Hat_Hat uu____2409 uu____2410)))
end
| uu____2412 -> begin
(

let binders_doc = (

let uu____2414 = (p_typars bs)
in (

let uu____2415 = (FStar_Pprint.optional (fun t -> (

let uu____2419 = (

let uu____2420 = (

let uu____2421 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2421))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2420))
in (FStar_Pprint.op_Hat_Hat break1 uu____2419))) typ_opt)
in (FStar_Pprint.op_Hat_Hat uu____2414 uu____2415)))
in (

let uu____2422 = (p_ident lid)
in (

let uu____2423 = (cont ())
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____2422 binders_doc uu____2423))))
end))
and p_recordFieldDecl : (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option)  ->  FStar_Pprint.document = (fun uu____2424 -> (match (uu____2424) with
| (lid, t, doc_opt) -> begin
(

let uu____2434 = (

let uu____2435 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (

let uu____2436 = (

let uu____2437 = (p_lident lid)
in (

let uu____2438 = (

let uu____2439 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2439))
in (FStar_Pprint.op_Hat_Hat uu____2437 uu____2438)))
in (FStar_Pprint.op_Hat_Hat uu____2435 uu____2436)))
in (FStar_Pprint.group uu____2434))
end))
and p_constructorDecl : (FStar_Ident.ident * FStar_Parser_AST.term FStar_Pervasives_Native.option * FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option * Prims.bool)  ->  FStar_Pprint.document = (fun uu____2440 -> (match (uu____2440) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let sep = (match (use_of) with
| true -> begin
(str "of")
end
| uu____2456 -> begin
FStar_Pprint.colon
end)
in (

let uid_doc = (p_uident uid)
in (

let uu____2458 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (

let uu____2459 = (

let uu____2460 = (FStar_Pprint.break_ (Prims.parse_int "0"))
in (

let uu____2461 = (default_or_map uid_doc (fun t -> (

let uu____2466 = (

let uu____2467 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep)
in (FStar_Pprint.op_Hat_Hat uid_doc uu____2467))
in (

let uu____2468 = (p_typ t)
in (op_Hat_Slash_Plus_Hat uu____2466 uu____2468)))) t_opt)
in (FStar_Pprint.op_Hat_Hat uu____2460 uu____2461)))
in (FStar_Pprint.op_Hat_Hat uu____2458 uu____2459)))))
end))
and p_letbinding : (FStar_Parser_AST.pattern * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun uu____2469 -> (match (uu____2469) with
| (pat, e) -> begin
(

let pat_doc = (

let uu____2475 = (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat1, t) -> begin
(

let uu____2482 = (

let uu____2483 = (

let uu____2484 = (

let uu____2485 = (

let uu____2486 = (p_tmArrow p_tmNoEq t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2486))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2485))
in (FStar_Pprint.group uu____2484))
in (FStar_Pprint.op_Hat_Hat break1 uu____2483))
in ((pat1), (uu____2482)))
end
| uu____2487 -> begin
((pat), (FStar_Pprint.empty))
end)
in (match (uu____2475) with
| (pat1, ascr_doc) -> begin
(match (pat1.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____2491); FStar_Parser_AST.prange = uu____2492}, pats) -> begin
(

let uu____2498 = (p_lident x)
in (

let uu____2499 = (

let uu____2500 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Hat uu____2500 ascr_doc))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____2498 uu____2499 FStar_Pprint.equals)))
end
| uu____2501 -> begin
(

let uu____2502 = (

let uu____2503 = (p_tuplePattern pat1)
in (

let uu____2504 = (FStar_Pprint.op_Hat_Slash_Hat ascr_doc FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____2503 uu____2504)))
in (FStar_Pprint.group uu____2502))
end)
end))
in (

let uu____2505 = (p_term e)
in (prefix2 pat_doc uu____2505)))
end))
and p_newEffect : FStar_Parser_AST.effect_decl  ->  FStar_Pprint.document = (fun uu___98_2506 -> (match (uu___98_2506) with
| FStar_Parser_AST.RedefineEffect (lid, bs, t) -> begin
(p_effectRedefinition lid bs t)
end
| FStar_Parser_AST.DefineEffect (lid, bs, t, eff_decls) -> begin
(p_effectDefinition lid bs t eff_decls)
end))
and p_effectRedefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun uid bs t -> (

let uu____2524 = (p_uident uid)
in (

let uu____2525 = (p_binders true bs)
in (

let uu____2526 = (

let uu____2527 = (p_simpleTerm t)
in (prefix2 FStar_Pprint.equals uu____2527))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____2524 uu____2525 uu____2526)))))
and p_effectDefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun uid bs t eff_decls -> (

let uu____2534 = (

let uu____2535 = (

let uu____2536 = (

let uu____2537 = (p_uident uid)
in (

let uu____2538 = (p_binders true bs)
in (

let uu____2539 = (

let uu____2540 = (p_typ t)
in (prefix2 FStar_Pprint.colon uu____2540))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____2537 uu____2538 uu____2539))))
in (FStar_Pprint.group uu____2536))
in (

let uu____2541 = (

let uu____2542 = (str "with")
in (

let uu____2543 = (separate_break_map FStar_Pprint.semi p_effectDecl eff_decls)
in (prefix2 uu____2542 uu____2543)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2535 uu____2541)))
in (braces_with_nesting uu____2534)))
and p_effectDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (false, ((FStar_Parser_AST.TyconAbbrev (lid, [], FStar_Pervasives_Native.None, e), FStar_Pervasives_Native.None))::[]) -> begin
(

let uu____2560 = (

let uu____2561 = (p_lident lid)
in (

let uu____2562 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____2561 uu____2562)))
in (

let uu____2563 = (p_simpleTerm e)
in (prefix2 uu____2560 uu____2563)))
end
| uu____2564 -> begin
(

let uu____2565 = (

let uu____2566 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "Not a declaration of an effect member... or at least I hope so : %s" uu____2566))
in (failwith uu____2565))
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

let p_lift = (fun uu____2599 -> (match (uu____2599) with
| (kwd1, t) -> begin
(

let uu____2604 = (

let uu____2605 = (str kwd1)
in (

let uu____2606 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____2605 uu____2606)))
in (

let uu____2607 = (p_simpleTerm t)
in (prefix2 uu____2604 uu____2607)))
end))
in (separate_break_map FStar_Pprint.semi p_lift lifts)))
in (

let uu____2610 = (

let uu____2611 = (

let uu____2612 = (p_quident lift.FStar_Parser_AST.msource)
in (

let uu____2613 = (

let uu____2614 = (str "~>")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2614))
in (FStar_Pprint.op_Hat_Hat uu____2612 uu____2613)))
in (

let uu____2615 = (p_quident lift.FStar_Parser_AST.mdest)
in (prefix2 uu____2611 uu____2615)))
in (

let uu____2616 = (

let uu____2617 = (braces_with_nesting lift_op_doc)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2617))
in (FStar_Pprint.op_Hat_Hat uu____2610 uu____2616)))))
and p_qualifier : FStar_Parser_AST.qualifier  ->  FStar_Pprint.document = (fun uu___99_2618 -> (match (uu___99_2618) with
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

let uu____2620 = (FStar_Pprint.separate_map break1 p_qualifier qs)
in (FStar_Pprint.group uu____2620)))
and p_letqualifier : FStar_Parser_AST.let_qualifier  ->  FStar_Pprint.document = (fun uu___100_2621 -> (match (uu___100_2621) with
| FStar_Parser_AST.Rec -> begin
(

let uu____2622 = (str "rec")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2622))
end
| FStar_Parser_AST.Mutable -> begin
(

let uu____2623 = (str "mutable")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2623))
end
| FStar_Parser_AST.NoLetQualifier -> begin
FStar_Pprint.empty
end))
and p_aqual : FStar_Parser_AST.arg_qualifier  ->  FStar_Pprint.document = (fun uu___101_2624 -> (match (uu___101_2624) with
| FStar_Parser_AST.Implicit -> begin
(str "#")
end
| FStar_Parser_AST.Equality -> begin
(str "$")
end))
and p_disjunctivePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr (pats) -> begin
(

let uu____2628 = (

let uu____2629 = (

let uu____2630 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space)
in (FStar_Pprint.op_Hat_Hat break1 uu____2630))
in (FStar_Pprint.separate_map uu____2629 p_tuplePattern pats))
in (FStar_Pprint.group uu____2628))
end
| uu____2631 -> begin
(p_tuplePattern p)
end))
and p_tuplePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTuple (pats, false) -> begin
(

let uu____2636 = (

let uu____2637 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map uu____2637 p_constructorPattern pats))
in (FStar_Pprint.group uu____2636))
end
| uu____2638 -> begin
(p_constructorPattern p)
end))
and p_constructorPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (maybe_cons_lid); FStar_Parser_AST.prange = uu____2641}, (hd1)::(tl1)::[]) when (FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid) -> begin
(

let uu____2645 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon)
in (

let uu____2646 = (p_constructorPattern hd1)
in (

let uu____2647 = (p_constructorPattern tl1)
in (infix0 uu____2645 uu____2646 uu____2647))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (uid); FStar_Parser_AST.prange = uu____2649}, pats) -> begin
(

let uu____2653 = (p_quident uid)
in (

let uu____2654 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (prefix2 uu____2653 uu____2654)))
end
| uu____2655 -> begin
(p_atomicPattern p)
end))
and p_atomicPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, t) -> begin
(

let uu____2659 = (

let uu____2662 = (

let uu____2663 = (unparen t)
in uu____2663.FStar_Parser_AST.tm)
in ((pat.FStar_Parser_AST.pat), (uu____2662)))
in (match (uu____2659) with
| (FStar_Parser_AST.PatVar (lid, aqual), FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t1); FStar_Parser_AST.brange = uu____2668; FStar_Parser_AST.blevel = uu____2669; FStar_Parser_AST.aqual = uu____2670}, phi)) when (lid.FStar_Ident.idText = lid'.FStar_Ident.idText) -> begin
(

let uu____2674 = (

let uu____2675 = (p_ident lid)
in (p_refinement aqual uu____2675 t1 phi))
in (soft_parens_with_nesting uu____2674))
end
| (FStar_Parser_AST.PatWild, FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t1); FStar_Parser_AST.brange = uu____2677; FStar_Parser_AST.blevel = uu____2678; FStar_Parser_AST.aqual = uu____2679}, phi)) -> begin
(

let uu____2681 = (p_refinement FStar_Pervasives_Native.None FStar_Pprint.underscore t1 phi)
in (soft_parens_with_nesting uu____2681))
end
| uu____2682 -> begin
(

let uu____2685 = (

let uu____2686 = (p_tuplePattern pat)
in (

let uu____2687 = (

let uu____2688 = (FStar_Pprint.break_ (Prims.parse_int "0"))
in (

let uu____2689 = (

let uu____2690 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2690))
in (FStar_Pprint.op_Hat_Hat uu____2688 uu____2689)))
in (FStar_Pprint.op_Hat_Hat uu____2686 uu____2687)))
in (soft_parens_with_nesting uu____2685))
end))
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let uu____2693 = (separate_break_map FStar_Pprint.semi p_tuplePattern pats)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket uu____2693 FStar_Pprint.rbracket))
end
| FStar_Parser_AST.PatRecord (pats) -> begin
(

let p_recordFieldPat = (fun uu____2703 -> (match (uu____2703) with
| (lid, pat) -> begin
(

let uu____2708 = (p_qlident lid)
in (

let uu____2709 = (p_tuplePattern pat)
in (infix2 FStar_Pprint.equals uu____2708 uu____2709)))
end))
in (

let uu____2710 = (separate_break_map FStar_Pprint.semi p_recordFieldPat pats)
in (soft_braces_with_nesting uu____2710)))
end
| FStar_Parser_AST.PatTuple (pats, true) -> begin
(

let uu____2716 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (

let uu____2717 = (separate_break_map FStar_Pprint.comma p_constructorPattern pats)
in (

let uu____2718 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____2716 uu____2717 uu____2718))))
end
| FStar_Parser_AST.PatTvar (tv, arg_qualifier_opt) -> begin
(p_tvar tv)
end
| FStar_Parser_AST.PatOp (op) -> begin
(

let uu____2726 = (

let uu____2727 = (

let uu____2728 = (str (FStar_Ident.text_of_id op))
in (

let uu____2729 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat uu____2728 uu____2729)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2727))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2726))
end
| FStar_Parser_AST.PatWild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.PatConst (c) -> begin
(p_constant c)
end
| FStar_Parser_AST.PatVar (lid, aqual) -> begin
(

let uu____2735 = (FStar_Pprint.optional p_aqual aqual)
in (

let uu____2736 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat uu____2735 uu____2736)))
end
| FStar_Parser_AST.PatName (uid) -> begin
(p_quident uid)
end
| FStar_Parser_AST.PatOr (uu____2738) -> begin
(failwith "Inner or pattern !")
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (uu____2740); FStar_Parser_AST.prange = uu____2741}, uu____2742) -> begin
(

let uu____2745 = (p_tuplePattern p)
in (soft_parens_with_nesting uu____2745))
end
| FStar_Parser_AST.PatTuple (uu____2746, false) -> begin
(

let uu____2749 = (p_tuplePattern p)
in (soft_parens_with_nesting uu____2749))
end
| uu____2750 -> begin
(

let uu____2751 = (

let uu____2752 = (FStar_Parser_AST.pat_to_string p)
in (FStar_Util.format1 "Invalid pattern %s" uu____2752))
in (failwith uu____2751))
end))
and p_binder : Prims.bool  ->  FStar_Parser_AST.binder  ->  FStar_Pprint.document = (fun is_atomic b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (lid) -> begin
(

let uu____2756 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (

let uu____2757 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat uu____2756 uu____2757)))
end
| FStar_Parser_AST.TVariable (lid) -> begin
(p_lident lid)
end
| FStar_Parser_AST.Annotated (lid, t) -> begin
(

let doc1 = (

let uu____2762 = (

let uu____2763 = (unparen t)
in uu____2763.FStar_Parser_AST.tm)
in (match (uu____2762) with
| FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t1); FStar_Parser_AST.brange = uu____2766; FStar_Parser_AST.blevel = uu____2767; FStar_Parser_AST.aqual = uu____2768}, phi) when (lid.FStar_Ident.idText = lid'.FStar_Ident.idText) -> begin
(

let uu____2770 = (p_ident lid)
in (p_refinement b.FStar_Parser_AST.aqual uu____2770 t1 phi))
end
| uu____2771 -> begin
(

let uu____2772 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (

let uu____2773 = (

let uu____2774 = (p_lident lid)
in (

let uu____2775 = (

let uu____2776 = (

let uu____2777 = (FStar_Pprint.break_ (Prims.parse_int "0"))
in (

let uu____2778 = (p_tmFormula t)
in (FStar_Pprint.op_Hat_Hat uu____2777 uu____2778)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2776))
in (FStar_Pprint.op_Hat_Hat uu____2774 uu____2775)))
in (FStar_Pprint.op_Hat_Hat uu____2772 uu____2773)))
end))
in (match (is_atomic) with
| true -> begin
(

let uu____2779 = (

let uu____2780 = (FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2780))
in (FStar_Pprint.group uu____2779))
end
| uu____2781 -> begin
(FStar_Pprint.group doc1)
end))
end
| FStar_Parser_AST.TAnnotated (uu____2782) -> begin
(failwith "Is this still used ?")
end
| FStar_Parser_AST.NoName (t) -> begin
(

let uu____2786 = (

let uu____2787 = (unparen t)
in uu____2787.FStar_Parser_AST.tm)
in (match (uu____2786) with
| FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t1); FStar_Parser_AST.brange = uu____2789; FStar_Parser_AST.blevel = uu____2790; FStar_Parser_AST.aqual = uu____2791}, phi) -> begin
(match (is_atomic) with
| true -> begin
(

let uu____2793 = (

let uu____2794 = (

let uu____2795 = (p_refinement b.FStar_Parser_AST.aqual FStar_Pprint.underscore t1 phi)
in (FStar_Pprint.op_Hat_Hat uu____2795 FStar_Pprint.rparen))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2794))
in (FStar_Pprint.group uu____2793))
end
| uu____2796 -> begin
(

let uu____2797 = (p_refinement b.FStar_Parser_AST.aqual FStar_Pprint.underscore t1 phi)
in (FStar_Pprint.group uu____2797))
end)
end
| uu____2798 -> begin
(match (is_atomic) with
| true -> begin
(p_atomicTerm t)
end
| uu____2799 -> begin
(p_appTerm t)
end)
end))
end))
and p_refinement : FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Pprint.document  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun aqual_opt binder t phi -> (

let uu____2805 = (FStar_Pprint.optional p_aqual aqual_opt)
in (

let uu____2806 = (

let uu____2807 = (

let uu____2808 = (

let uu____2809 = (p_appTerm t)
in (

let uu____2810 = (

let uu____2811 = (p_noSeqTerm phi)
in (soft_braces_with_nesting uu____2811))
in (FStar_Pprint.op_Hat_Hat uu____2809 uu____2810)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2808))
in (FStar_Pprint.op_Hat_Hat binder uu____2807))
in (FStar_Pprint.op_Hat_Hat uu____2805 uu____2806))))
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
| uu____2822 -> begin
(p_lident id)
end))
and p_term : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2824 = (

let uu____2825 = (unparen e)
in uu____2825.FStar_Parser_AST.tm)
in (match (uu____2824) with
| FStar_Parser_AST.Seq (e1, e2) -> begin
(

let uu____2828 = (

let uu____2829 = (

let uu____2830 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat uu____2830 FStar_Pprint.semi))
in (FStar_Pprint.group uu____2829))
in (

let uu____2831 = (p_term e2)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2828 uu____2831)))
end
| FStar_Parser_AST.Bind (x, e1, e2) -> begin
(

let uu____2835 = (

let uu____2836 = (

let uu____2837 = (

let uu____2838 = (p_lident x)
in (

let uu____2839 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.long_left_arrow)
in (FStar_Pprint.op_Hat_Hat uu____2838 uu____2839)))
in (

let uu____2840 = (

let uu____2841 = (p_noSeqTerm e1)
in (

let uu____2842 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.semi)
in (FStar_Pprint.op_Hat_Hat uu____2841 uu____2842)))
in (op_Hat_Slash_Plus_Hat uu____2837 uu____2840)))
in (FStar_Pprint.group uu____2836))
in (

let uu____2843 = (p_term e2)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2835 uu____2843)))
end
| uu____2844 -> begin
(

let uu____2845 = (p_noSeqTerm e)
in (FStar_Pprint.group uu____2845))
end)))
and p_noSeqTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_noSeqTerm' e e.FStar_Parser_AST.range))
and p_noSeqTerm' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2848 = (

let uu____2849 = (unparen e)
in uu____2849.FStar_Parser_AST.tm)
in (match (uu____2848) with
| FStar_Parser_AST.Ascribed (e1, t, FStar_Pervasives_Native.None) -> begin
(

let uu____2853 = (

let uu____2854 = (p_tmIff e1)
in (

let uu____2855 = (

let uu____2856 = (

let uu____2857 = (p_typ t)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____2857))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____2856))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2854 uu____2855)))
in (FStar_Pprint.group uu____2853))
end
| FStar_Parser_AST.Ascribed (e1, t, FStar_Pervasives_Native.Some (tac)) -> begin
(

let uu____2862 = (

let uu____2863 = (p_tmIff e1)
in (

let uu____2864 = (

let uu____2865 = (

let uu____2866 = (

let uu____2867 = (p_typ t)
in (

let uu____2868 = (

let uu____2869 = (str "by")
in (

let uu____2870 = (p_typ tac)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2869 uu____2870)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2867 uu____2868)))
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____2866))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____2865))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2863 uu____2864)))
in (FStar_Pprint.group uu____2862))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = ".()<-"; FStar_Ident.idRange = uu____2871}, (e1)::(e2)::(e3)::[]) -> begin
(

let uu____2876 = (

let uu____2877 = (

let uu____2878 = (

let uu____2879 = (p_atomicTermNotQUident e1)
in (

let uu____2880 = (

let uu____2881 = (

let uu____2882 = (

let uu____2883 = (p_term e2)
in (soft_parens_with_nesting uu____2883))
in (

let uu____2884 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat uu____2882 uu____2884)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____2881))
in (FStar_Pprint.op_Hat_Hat uu____2879 uu____2880)))
in (FStar_Pprint.group uu____2878))
in (

let uu____2885 = (

let uu____2886 = (p_noSeqTerm e3)
in (jump2 uu____2886))
in (FStar_Pprint.op_Hat_Hat uu____2877 uu____2885)))
in (FStar_Pprint.group uu____2876))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = ".[]<-"; FStar_Ident.idRange = uu____2887}, (e1)::(e2)::(e3)::[]) -> begin
(

let uu____2892 = (

let uu____2893 = (

let uu____2894 = (

let uu____2895 = (p_atomicTermNotQUident e1)
in (

let uu____2896 = (

let uu____2897 = (

let uu____2898 = (

let uu____2899 = (p_term e2)
in (soft_brackets_with_nesting uu____2899))
in (

let uu____2900 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat uu____2898 uu____2900)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____2897))
in (FStar_Pprint.op_Hat_Hat uu____2895 uu____2896)))
in (FStar_Pprint.group uu____2894))
in (

let uu____2901 = (

let uu____2902 = (p_noSeqTerm e3)
in (jump2 uu____2902))
in (FStar_Pprint.op_Hat_Hat uu____2893 uu____2901)))
in (FStar_Pprint.group uu____2892))
end
| FStar_Parser_AST.Requires (e1, wtf) -> begin
(

let uu____2909 = (

let uu____2910 = (str "requires")
in (

let uu____2911 = (p_typ e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2910 uu____2911)))
in (FStar_Pprint.group uu____2909))
end
| FStar_Parser_AST.Ensures (e1, wtf) -> begin
(

let uu____2918 = (

let uu____2919 = (str "ensures")
in (

let uu____2920 = (p_typ e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2919 uu____2920)))
in (FStar_Pprint.group uu____2918))
end
| FStar_Parser_AST.Attributes (es) -> begin
(

let uu____2923 = (

let uu____2924 = (str "attributes")
in (

let uu____2925 = (FStar_Pprint.separate_map break1 p_atomicTerm es)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2924 uu____2925)))
in (FStar_Pprint.group uu____2923))
end
| FStar_Parser_AST.If (e1, e2, e3) -> begin
(

let uu____2929 = (is_unit e3)
in (match (uu____2929) with
| true -> begin
(

let uu____2930 = (

let uu____2931 = (

let uu____2932 = (str "if")
in (

let uu____2933 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat uu____2932 uu____2933)))
in (

let uu____2934 = (

let uu____2935 = (str "then")
in (

let uu____2936 = (p_noSeqTerm e2)
in (op_Hat_Slash_Plus_Hat uu____2935 uu____2936)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2931 uu____2934)))
in (FStar_Pprint.group uu____2930))
end
| uu____2937 -> begin
(

let e2_doc = (

let uu____2939 = (

let uu____2940 = (unparen e2)
in uu____2940.FStar_Parser_AST.tm)
in (match (uu____2939) with
| FStar_Parser_AST.If (uu____2941, uu____2942, e31) when (is_unit e31) -> begin
(

let uu____2944 = (p_noSeqTerm e2)
in (soft_parens_with_nesting uu____2944))
end
| uu____2945 -> begin
(p_noSeqTerm e2)
end))
in (

let uu____2946 = (

let uu____2947 = (

let uu____2948 = (str "if")
in (

let uu____2949 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat uu____2948 uu____2949)))
in (

let uu____2950 = (

let uu____2951 = (

let uu____2952 = (str "then")
in (op_Hat_Slash_Plus_Hat uu____2952 e2_doc))
in (

let uu____2953 = (

let uu____2954 = (str "else")
in (

let uu____2955 = (p_noSeqTerm e3)
in (op_Hat_Slash_Plus_Hat uu____2954 uu____2955)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2951 uu____2953)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2947 uu____2950)))
in (FStar_Pprint.group uu____2946)))
end))
end
| FStar_Parser_AST.TryWith (e1, branches) -> begin
(

let uu____2968 = (

let uu____2969 = (

let uu____2970 = (str "try")
in (

let uu____2971 = (p_noSeqTerm e1)
in (prefix2 uu____2970 uu____2971)))
in (

let uu____2972 = (

let uu____2973 = (str "with")
in (

let uu____2974 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2973 uu____2974)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____2969 uu____2972)))
in (FStar_Pprint.group uu____2968))
end
| FStar_Parser_AST.Match (e1, branches) -> begin
(

let uu____2991 = (

let uu____2992 = (

let uu____2993 = (str "match")
in (

let uu____2994 = (p_noSeqTerm e1)
in (

let uu____2995 = (str "with")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____2993 uu____2994 uu____2995))))
in (

let uu____2996 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat uu____2992 uu____2996)))
in (FStar_Pprint.group uu____2991))
end
| FStar_Parser_AST.LetOpen (uid, e1) -> begin
(

let uu____3003 = (

let uu____3004 = (

let uu____3005 = (str "let open")
in (

let uu____3006 = (p_quident uid)
in (

let uu____3007 = (str "in")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____3005 uu____3006 uu____3007))))
in (

let uu____3008 = (p_term e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____3004 uu____3008)))
in (FStar_Pprint.group uu____3003))
end
| FStar_Parser_AST.Let (q, lbs, e1) -> begin
(

let let_doc = (

let uu____3019 = (str "let")
in (

let uu____3020 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat uu____3019 uu____3020)))
in (

let uu____3021 = (

let uu____3022 = (

let uu____3023 = (

let uu____3024 = (str "and")
in (precede_break_separate_map let_doc uu____3024 p_letbinding lbs))
in (

let uu____3027 = (str "in")
in (FStar_Pprint.op_Hat_Slash_Hat uu____3023 uu____3027)))
in (FStar_Pprint.group uu____3022))
in (

let uu____3028 = (p_term e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____3021 uu____3028))))
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, typ_opt); FStar_Parser_AST.prange = uu____3031})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, branches); FStar_Parser_AST.range = uu____3034; FStar_Parser_AST.level = uu____3035}) when (matches_var maybe_x x) -> begin
(

let uu____3049 = (

let uu____3050 = (str "function")
in (

let uu____3051 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat uu____3050 uu____3051)))
in (FStar_Pprint.group uu____3049))
end
| FStar_Parser_AST.Assign (id, e1) -> begin
(

let uu____3058 = (

let uu____3059 = (p_lident id)
in (

let uu____3060 = (

let uu____3061 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow uu____3061))
in (FStar_Pprint.op_Hat_Slash_Hat uu____3059 uu____3060)))
in (FStar_Pprint.group uu____3058))
end
| uu____3062 -> begin
(p_typ e)
end)))
and p_typ : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_typ' e e.FStar_Parser_AST.range))
and p_typ' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3065 = (

let uu____3066 = (unparen e)
in uu____3066.FStar_Parser_AST.tm)
in (match (uu____3065) with
| FStar_Parser_AST.QForall (bs, trigger, e1) -> begin
(

let uu____3076 = (

let uu____3077 = (

let uu____3078 = (p_quantifier e)
in (FStar_Pprint.op_Hat_Hat uu____3078 FStar_Pprint.space))
in (

let uu____3079 = (p_binders true bs)
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") uu____3077 uu____3079 FStar_Pprint.dot)))
in (

let uu____3080 = (

let uu____3081 = (p_trigger trigger)
in (

let uu____3082 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat uu____3081 uu____3082)))
in (prefix2 uu____3076 uu____3080)))
end
| FStar_Parser_AST.QExists (bs, trigger, e1) -> begin
(

let uu____3092 = (

let uu____3093 = (

let uu____3094 = (p_quantifier e)
in (FStar_Pprint.op_Hat_Hat uu____3094 FStar_Pprint.space))
in (

let uu____3095 = (p_binders true bs)
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") uu____3093 uu____3095 FStar_Pprint.dot)))
in (

let uu____3096 = (

let uu____3097 = (p_trigger trigger)
in (

let uu____3098 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat uu____3097 uu____3098)))
in (prefix2 uu____3092 uu____3096)))
end
| uu____3099 -> begin
(p_simpleTerm e)
end)))
and p_quantifier : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3101 = (

let uu____3102 = (unparen e)
in uu____3102.FStar_Parser_AST.tm)
in (match (uu____3101) with
| FStar_Parser_AST.QForall (uu____3103) -> begin
(str "forall")
end
| FStar_Parser_AST.QExists (uu____3110) -> begin
(str "exists")
end
| uu____3117 -> begin
(failwith "Imposible : p_quantifier called on a non-quantifier term")
end)))
and p_trigger : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun uu___102_3118 -> (match (uu___102_3118) with
| [] -> begin
FStar_Pprint.empty
end
| pats -> begin
(

let uu____3125 = (

let uu____3126 = (

let uu____3127 = (str "pattern")
in (

let uu____3128 = (

let uu____3129 = (

let uu____3130 = (p_disjunctivePats pats)
in (jump2 uu____3130))
in (

let uu____3131 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____3129 uu____3131)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____3127 uu____3128)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3126))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____3125))
end))
and p_disjunctivePats : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun pats -> (

let uu____3135 = (str "\\/")
in (FStar_Pprint.separate_map uu____3135 p_conjunctivePats pats)))
and p_conjunctivePats : FStar_Parser_AST.term Prims.list  ->  FStar_Pprint.document = (fun pats -> (

let uu____3139 = (FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats)
in (FStar_Pprint.group uu____3139)))
and p_simpleTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3141 = (

let uu____3142 = (unparen e)
in uu____3142.FStar_Parser_AST.tm)
in (match (uu____3141) with
| FStar_Parser_AST.Abs (pats, e1) -> begin
(

let uu____3147 = (

let uu____3148 = (str "fun")
in (

let uu____3149 = (

let uu____3150 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Slash_Hat uu____3150 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat uu____3148 uu____3149)))
in (

let uu____3151 = (p_term e1)
in (op_Hat_Slash_Plus_Hat uu____3147 uu____3151)))
end
| uu____3152 -> begin
(p_tmIff e)
end)))
and p_maybeFocusArrow : Prims.bool  ->  FStar_Pprint.document = (fun b -> (match (b) with
| true -> begin
(str "~>")
end
| uu____3154 -> begin
FStar_Pprint.rarrow
end))
and p_patternBranch : (FStar_Parser_AST.pattern * FStar_Parser_AST.term FStar_Pervasives_Native.option * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun uu____3155 -> (match (uu____3155) with
| (pat, when_opt, e) -> begin
(

let maybe_paren = (

let uu____3168 = (

let uu____3169 = (unparen e)
in uu____3169.FStar_Parser_AST.tm)
in (match (uu____3168) with
| FStar_Parser_AST.Match (uu____3172) -> begin
soft_begin_end_with_nesting
end
| FStar_Parser_AST.TryWith (uu____3180) -> begin
soft_begin_end_with_nesting
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____3189); FStar_Parser_AST.prange = uu____3190})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, uu____3192); FStar_Parser_AST.range = uu____3193; FStar_Parser_AST.level = uu____3194}) when (matches_var maybe_x x) -> begin
soft_begin_end_with_nesting
end
| uu____3208 -> begin
(fun x -> x)
end))
in (

let uu____3210 = (

let uu____3211 = (

let uu____3212 = (

let uu____3213 = (

let uu____3214 = (

let uu____3215 = (p_disjunctivePattern pat)
in (

let uu____3216 = (

let uu____3217 = (p_maybeWhen when_opt)
in (FStar_Pprint.op_Hat_Hat uu____3217 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat uu____3215 uu____3216)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3214))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____3213))
in (FStar_Pprint.group uu____3212))
in (

let uu____3218 = (

let uu____3219 = (p_term e)
in (maybe_paren uu____3219))
in (op_Hat_Slash_Plus_Hat uu____3211 uu____3218)))
in (FStar_Pprint.group uu____3210)))
end))
and p_maybeWhen : FStar_Parser_AST.term FStar_Pervasives_Native.option  ->  FStar_Pprint.document = (fun uu___103_3220 -> (match (uu___103_3220) with
| FStar_Pervasives_Native.None -> begin
FStar_Pprint.empty
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____3223 = (str "when")
in (

let uu____3224 = (

let uu____3225 = (p_tmFormula e)
in (FStar_Pprint.op_Hat_Hat uu____3225 FStar_Pprint.space))
in (op_Hat_Slash_Plus_Hat uu____3223 uu____3224)))
end))
and p_tmIff : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3227 = (

let uu____3228 = (unparen e)
in uu____3228.FStar_Parser_AST.tm)
in (match (uu____3227) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____3229}, (e1)::(e2)::[]) -> begin
(

let uu____3233 = (str "<==>")
in (

let uu____3234 = (p_tmImplies e1)
in (

let uu____3235 = (p_tmIff e2)
in (infix0 uu____3233 uu____3234 uu____3235))))
end
| uu____3236 -> begin
(p_tmImplies e)
end)))
and p_tmImplies : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3238 = (

let uu____3239 = (unparen e)
in uu____3239.FStar_Parser_AST.tm)
in (match (uu____3238) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____3240}, (e1)::(e2)::[]) -> begin
(

let uu____3244 = (str "==>")
in (

let uu____3245 = (p_tmArrow p_tmFormula e1)
in (

let uu____3246 = (p_tmImplies e2)
in (infix0 uu____3244 uu____3245 uu____3246))))
end
| uu____3247 -> begin
(p_tmArrow p_tmFormula e)
end)))
and p_tmArrow : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_Tm e -> (

let uu____3252 = (

let uu____3253 = (unparen e)
in uu____3253.FStar_Parser_AST.tm)
in (match (uu____3252) with
| FStar_Parser_AST.Product (bs, tgt) -> begin
(

let uu____3258 = (

let uu____3259 = (FStar_Pprint.concat_map (fun b -> (

let uu____3264 = (p_binder false b)
in (

let uu____3265 = (

let uu____3266 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3266))
in (FStar_Pprint.op_Hat_Hat uu____3264 uu____3265)))) bs)
in (

let uu____3267 = (p_tmArrow p_Tm tgt)
in (FStar_Pprint.op_Hat_Hat uu____3259 uu____3267)))
in (FStar_Pprint.group uu____3258))
end
| uu____3268 -> begin
(p_Tm e)
end)))
and p_tmFormula : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3270 = (

let uu____3271 = (unparen e)
in uu____3271.FStar_Parser_AST.tm)
in (match (uu____3270) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____3272}, (e1)::(e2)::[]) -> begin
(

let uu____3276 = (str "\\/")
in (

let uu____3277 = (p_tmFormula e1)
in (

let uu____3278 = (p_tmConjunction e2)
in (infix0 uu____3276 uu____3277 uu____3278))))
end
| uu____3279 -> begin
(p_tmConjunction e)
end)))
and p_tmConjunction : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3281 = (

let uu____3282 = (unparen e)
in uu____3282.FStar_Parser_AST.tm)
in (match (uu____3281) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____3283}, (e1)::(e2)::[]) -> begin
(

let uu____3287 = (str "/\\")
in (

let uu____3288 = (p_tmConjunction e1)
in (

let uu____3289 = (p_tmTuple e2)
in (infix0 uu____3287 uu____3288 uu____3289))))
end
| uu____3290 -> begin
(p_tmTuple e)
end)))
and p_tmTuple : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_tmTuple' e e.FStar_Parser_AST.range))
and p_tmTuple' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3293 = (

let uu____3294 = (unparen e)
in uu____3294.FStar_Parser_AST.tm)
in (match (uu____3293) with
| FStar_Parser_AST.Construct (lid, args) when (is_tuple_constructor lid) -> begin
(

let uu____3303 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map uu____3303 (fun uu____3309 -> (match (uu____3309) with
| (e1, uu____3313) -> begin
(p_tmEq e1)
end)) args))
end
| uu____3314 -> begin
(p_tmEq e)
end)))
and paren_if : Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun curr mine doc1 -> (match ((mine <= curr)) with
| true -> begin
doc1
end
| uu____3318 -> begin
(

let uu____3319 = (

let uu____3320 = (FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3320))
in (FStar_Pprint.group uu____3319))
end))
and p_tmEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n1 = (max_level (FStar_List.append (((colon_equals ()))::((pipe_right ()))::[]) (operatorInfix0ad12 ())))
in (p_tmEq' n1 e)))
and p_tmEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (

let uu____3345 = (

let uu____3346 = (unparen e)
in uu____3346.FStar_Parser_AST.tm)
in (match (uu____3345) with
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (((is_operatorInfix0ad12 op) || ((FStar_Ident.text_of_id op) = "=")) || ((FStar_Ident.text_of_id op) = "|>")) -> begin
(

let op1 = (FStar_Ident.text_of_id op)
in (

let uu____3352 = (levels op1)
in (match (uu____3352) with
| (left1, mine, right1) -> begin
(

let uu____3359 = (

let uu____3360 = (FStar_All.pipe_left str op1)
in (

let uu____3361 = (p_tmEq' left1 e1)
in (

let uu____3362 = (p_tmEq' right1 e2)
in (infix0 uu____3360 uu____3361 uu____3362))))
in (paren_if curr mine uu____3359))
end)))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____3363}, (e1)::(e2)::[]) -> begin
(

let uu____3367 = (

let uu____3368 = (p_tmEq e1)
in (

let uu____3369 = (

let uu____3370 = (

let uu____3371 = (

let uu____3372 = (p_tmEq e2)
in (op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____3372))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3371))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3370))
in (FStar_Pprint.op_Hat_Hat uu____3368 uu____3369)))
in (FStar_Pprint.group uu____3367))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____3373}, (e1)::[]) -> begin
(

let uu____3376 = (levels "-")
in (match (uu____3376) with
| (left1, mine, right1) -> begin
(

let uu____3383 = (p_tmEq' mine e1)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____3383))
end))
end
| uu____3384 -> begin
(p_tmNoEq e)
end)))
and p_tmNoEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n1 = (max_level (((colon_colon ()))::((amp ()))::((opinfix3 ()))::((opinfix4 ()))::[]))
in (p_tmNoEq' n1 e)))
and p_tmNoEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (

let uu____3414 = (

let uu____3415 = (unparen e)
in uu____3415.FStar_Parser_AST.tm)
in (match (uu____3414) with
| FStar_Parser_AST.Construct (lid, ((e1, uu____3418))::((e2, uu____3420))::[]) when ((FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) && (

let uu____3431 = (is_list e)
in (not (uu____3431)))) -> begin
(

let op = "::"
in (

let uu____3433 = (levels op)
in (match (uu____3433) with
| (left1, mine, right1) -> begin
(

let uu____3440 = (

let uu____3441 = (str op)
in (

let uu____3442 = (p_tmNoEq' left1 e1)
in (

let uu____3443 = (p_tmNoEq' right1 e2)
in (infix0 uu____3441 uu____3442 uu____3443))))
in (paren_if curr mine uu____3440))
end)))
end
| FStar_Parser_AST.Sum (binders, res) -> begin
(

let op = "&"
in (

let uu____3449 = (levels op)
in (match (uu____3449) with
| (left1, mine, right1) -> begin
(

let p_dsumfst = (fun b -> (

let uu____3460 = (p_binder false b)
in (

let uu____3461 = (

let uu____3462 = (

let uu____3463 = (str op)
in (FStar_Pprint.op_Hat_Hat uu____3463 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3462))
in (FStar_Pprint.op_Hat_Hat uu____3460 uu____3461))))
in (

let uu____3464 = (

let uu____3465 = (FStar_Pprint.concat_map p_dsumfst binders)
in (

let uu____3466 = (p_tmNoEq' right1 res)
in (FStar_Pprint.op_Hat_Hat uu____3465 uu____3466)))
in (paren_if curr mine uu____3464)))
end)))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (is_operatorInfix34 op) -> begin
(

let op1 = (FStar_Ident.text_of_id op)
in (

let uu____3472 = (levels op1)
in (match (uu____3472) with
| (left1, mine, right1) -> begin
(

let uu____3479 = (

let uu____3480 = (str op1)
in (

let uu____3481 = (p_tmNoEq' left1 e1)
in (

let uu____3482 = (p_tmNoEq' right1 e2)
in (infix0 uu____3480 uu____3481 uu____3482))))
in (paren_if curr mine uu____3479))
end)))
end
| FStar_Parser_AST.NamedTyp (lid, e1) -> begin
(

let uu____3485 = (

let uu____3486 = (p_lidentOrUnderscore lid)
in (

let uu____3487 = (

let uu____3488 = (p_appTerm e1)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____3488))
in (FStar_Pprint.op_Hat_Slash_Hat uu____3486 uu____3487)))
in (FStar_Pprint.group uu____3485))
end
| FStar_Parser_AST.Refine (b, phi) -> begin
(p_refinedBinder b phi)
end
| FStar_Parser_AST.Record (with_opt, record_fields) -> begin
(

let uu____3501 = (

let uu____3502 = (default_or_map FStar_Pprint.empty p_with_clause with_opt)
in (

let uu____3503 = (

let uu____3504 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (FStar_Pprint.separate_map uu____3504 p_simpleDef record_fields))
in (FStar_Pprint.op_Hat_Hat uu____3502 uu____3503)))
in (braces_with_nesting uu____3501))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____3507}, (e1)::[]) -> begin
(

let uu____3510 = (

let uu____3511 = (str "~")
in (

let uu____3512 = (p_atomicTerm e1)
in (FStar_Pprint.op_Hat_Hat uu____3511 uu____3512)))
in (FStar_Pprint.group uu____3510))
end
| uu____3513 -> begin
(p_appTerm e)
end)))
and p_with_clause : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3515 = (p_appTerm e)
in (

let uu____3516 = (

let uu____3517 = (

let uu____3518 = (str "with")
in (FStar_Pprint.op_Hat_Hat uu____3518 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3517))
in (FStar_Pprint.op_Hat_Hat uu____3515 uu____3516))))
and p_refinedBinder : FStar_Parser_AST.binder  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun b phi -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (lid, t) -> begin
(

let uu____3523 = (

let uu____3524 = (p_lident lid)
in (p_refinement b.FStar_Parser_AST.aqual uu____3524 t phi))
in (soft_parens_with_nesting uu____3523))
end
| FStar_Parser_AST.TAnnotated (uu____3525) -> begin
(failwith "Is this still used ?")
end
| FStar_Parser_AST.Variable (uu____3528) -> begin
(

let uu____3529 = (

let uu____3530 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" uu____3530))
in (failwith uu____3529))
end
| FStar_Parser_AST.TVariable (uu____3531) -> begin
(

let uu____3532 = (

let uu____3533 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" uu____3533))
in (failwith uu____3532))
end
| FStar_Parser_AST.NoName (uu____3534) -> begin
(

let uu____3535 = (

let uu____3536 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" uu____3536))
in (failwith uu____3535))
end))
and p_simpleDef : (FStar_Ident.lid * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun uu____3537 -> (match (uu____3537) with
| (lid, e) -> begin
(

let uu____3542 = (

let uu____3543 = (p_qlident lid)
in (

let uu____3544 = (

let uu____3545 = (p_tmIff e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____3545))
in (FStar_Pprint.op_Hat_Slash_Hat uu____3543 uu____3544)))
in (FStar_Pprint.group uu____3542))
end))
and p_appTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3547 = (

let uu____3548 = (unparen e)
in uu____3548.FStar_Parser_AST.tm)
in (match (uu____3547) with
| FStar_Parser_AST.App (uu____3549) when (is_general_application e) -> begin
(

let uu____3553 = (head_and_args e)
in (match (uu____3553) with
| (head1, args) -> begin
(

let uu____3567 = (

let uu____3573 = (FStar_ST.read should_print_fs_typ_app)
in (match (uu____3573) with
| true -> begin
(

let uu____3581 = (FStar_Util.take (fun uu____3595 -> (match (uu____3595) with
| (uu____3598, aq) -> begin
(aq = FStar_Parser_AST.FsTypApp)
end)) args)
in (match (uu____3581) with
| (fs_typ_args, args1) -> begin
(

let uu____3619 = (

let uu____3620 = (p_indexingTerm head1)
in (

let uu____3621 = (

let uu____3622 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (soft_surround_separate_map (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.empty FStar_Pprint.langle uu____3622 FStar_Pprint.rangle p_fsTypArg fs_typ_args))
in (FStar_Pprint.op_Hat_Hat uu____3620 uu____3621)))
in ((uu____3619), (args1)))
end))
end
| uu____3628 -> begin
(

let uu____3629 = (p_indexingTerm head1)
in ((uu____3629), (args)))
end))
in (match (uu____3567) with
| (head_doc, args1) -> begin
(

let uu____3641 = (

let uu____3642 = (FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space)
in (soft_surround_separate_map (Prims.parse_int "2") (Prims.parse_int "0") head_doc uu____3642 break1 FStar_Pprint.empty p_argTerm args1))
in (FStar_Pprint.group uu____3641))
end))
end))
end
| FStar_Parser_AST.Construct (lid, args) when ((is_general_construction e) && (

let uu____3654 = (is_dtuple_constructor lid)
in (not (uu____3654)))) -> begin
(match (args) with
| [] -> begin
(p_quident lid)
end
| (arg)::[] -> begin
(

let uu____3664 = (

let uu____3665 = (p_quident lid)
in (

let uu____3666 = (p_argTerm arg)
in (FStar_Pprint.op_Hat_Slash_Hat uu____3665 uu____3666)))
in (FStar_Pprint.group uu____3664))
end
| (hd1)::tl1 -> begin
(

let uu____3676 = (

let uu____3677 = (

let uu____3678 = (

let uu____3679 = (p_quident lid)
in (

let uu____3680 = (p_argTerm hd1)
in (prefix2 uu____3679 uu____3680)))
in (FStar_Pprint.group uu____3678))
in (

let uu____3681 = (

let uu____3682 = (FStar_Pprint.separate_map break1 p_argTerm tl1)
in (jump2 uu____3682))
in (FStar_Pprint.op_Hat_Hat uu____3677 uu____3681)))
in (FStar_Pprint.group uu____3676))
end)
end
| uu____3685 -> begin
(p_indexingTerm e)
end)))
and p_argTerm : (FStar_Parser_AST.term * FStar_Parser_AST.imp)  ->  FStar_Pprint.document = (fun arg_imp -> (match (arg_imp) with
| (u, FStar_Parser_AST.UnivApp) -> begin
(p_universe u)
end
| (e, FStar_Parser_AST.FsTypApp) -> begin
((FStar_Util.print_warning "Unexpected FsTypApp, output might not be formatted correctly.\n");
(

let uu____3692 = (p_indexingTerm e)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.langle uu____3692 FStar_Pprint.rangle));
)
end
| (e, FStar_Parser_AST.Hash) -> begin
(

let uu____3694 = (str "#")
in (

let uu____3695 = (p_indexingTerm e)
in (FStar_Pprint.op_Hat_Hat uu____3694 uu____3695)))
end
| (e, FStar_Parser_AST.Nothing) -> begin
(p_indexingTerm e)
end))
and p_fsTypArg : (FStar_Parser_AST.term * FStar_Parser_AST.imp)  ->  FStar_Pprint.document = (fun uu____3697 -> (match (uu____3697) with
| (e, uu____3701) -> begin
(p_indexingTerm e)
end))
and p_indexingTerm_aux : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun exit1 e -> (

let uu____3706 = (

let uu____3707 = (unparen e)
in uu____3707.FStar_Parser_AST.tm)
in (match (uu____3706) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____3708}, (e1)::(e2)::[]) -> begin
(

let uu____3712 = (

let uu____3713 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (

let uu____3714 = (

let uu____3715 = (

let uu____3716 = (p_term e2)
in (soft_parens_with_nesting uu____3716))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3715))
in (FStar_Pprint.op_Hat_Hat uu____3713 uu____3714)))
in (FStar_Pprint.group uu____3712))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____3717}, (e1)::(e2)::[]) -> begin
(

let uu____3721 = (

let uu____3722 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (

let uu____3723 = (

let uu____3724 = (

let uu____3725 = (p_term e2)
in (soft_brackets_with_nesting uu____3725))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3724))
in (FStar_Pprint.op_Hat_Hat uu____3722 uu____3723)))
in (FStar_Pprint.group uu____3721))
end
| uu____3726 -> begin
(exit1 e)
end)))
and p_indexingTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_indexingTerm_aux p_atomicTerm e))
and p_atomicTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3729 = (

let uu____3730 = (unparen e)
in uu____3730.FStar_Parser_AST.tm)
in (match (uu____3729) with
| FStar_Parser_AST.LetOpen (lid, e1) -> begin
(

let uu____3733 = (p_quident lid)
in (

let uu____3734 = (

let uu____3735 = (

let uu____3736 = (p_term e1)
in (soft_parens_with_nesting uu____3736))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3735))
in (FStar_Pprint.op_Hat_Hat uu____3733 uu____3734)))
end
| FStar_Parser_AST.Name (lid) -> begin
(p_quident lid)
end
| FStar_Parser_AST.Op (op, (e1)::[]) when (is_general_prefix_op op) -> begin
(

let uu____3741 = (str (FStar_Ident.text_of_id op))
in (

let uu____3742 = (p_atomicTerm e1)
in (FStar_Pprint.op_Hat_Hat uu____3741 uu____3742)))
end
| uu____3743 -> begin
(p_atomicTermNotQUident e)
end)))
and p_atomicTermNotQUident : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3745 = (

let uu____3746 = (unparen e)
in uu____3746.FStar_Parser_AST.tm)
in (match (uu____3745) with
| FStar_Parser_AST.Wild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.Var (lid) when (FStar_Ident.lid_equals lid FStar_Parser_Const.assert_lid) -> begin
(str "assert")
end
| FStar_Parser_AST.Tvar (tv) -> begin
(p_tvar tv)
end
| FStar_Parser_AST.Const (c) -> begin
(match (c) with
| FStar_Const.Const_char (x) when (x = '\n') -> begin
(str "0x0Az")
end
| uu____3751 -> begin
(p_constant c)
end)
end
| FStar_Parser_AST.Name (lid) when (FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid) -> begin
(str "True")
end
| FStar_Parser_AST.Name (lid) when (FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid) -> begin
(str "False")
end
| FStar_Parser_AST.Op (op, (e1)::[]) when (is_general_prefix_op op) -> begin
(

let uu____3757 = (str (FStar_Ident.text_of_id op))
in (

let uu____3758 = (p_atomicTermNotQUident e1)
in (FStar_Pprint.op_Hat_Hat uu____3757 uu____3758)))
end
| FStar_Parser_AST.Op (op, []) -> begin
(

let uu____3761 = (

let uu____3762 = (

let uu____3763 = (str (FStar_Ident.text_of_id op))
in (

let uu____3764 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat uu____3763 uu____3764)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3762))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3761))
end
| FStar_Parser_AST.Construct (lid, args) when (is_dtuple_constructor lid) -> begin
(

let uu____3773 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (

let uu____3774 = (

let uu____3775 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (

let uu____3776 = (FStar_List.map FStar_Pervasives_Native.fst args)
in (FStar_Pprint.separate_map uu____3775 p_tmEq uu____3776)))
in (

let uu____3780 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____3773 uu____3774 uu____3780))))
end
| FStar_Parser_AST.Project (e1, lid) -> begin
(

let uu____3783 = (

let uu____3784 = (p_atomicTermNotQUident e1)
in (

let uu____3785 = (

let uu____3786 = (p_qlident lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3786))
in (FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0") uu____3784 uu____3785)))
in (FStar_Pprint.group uu____3783))
end
| uu____3787 -> begin
(p_projectionLHS e)
end)))
and p_projectionLHS : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____3789 = (

let uu____3790 = (unparen e)
in uu____3790.FStar_Parser_AST.tm)
in (match (uu____3789) with
| FStar_Parser_AST.Var (lid) -> begin
(p_qlident lid)
end
| FStar_Parser_AST.Projector (constr_lid, field_lid) -> begin
(

let uu____3794 = (p_quident constr_lid)
in (

let uu____3795 = (

let uu____3796 = (

let uu____3797 = (p_lident field_lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3797))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____3796))
in (FStar_Pprint.op_Hat_Hat uu____3794 uu____3795)))
end
| FStar_Parser_AST.Discrim (constr_lid) -> begin
(

let uu____3799 = (p_quident constr_lid)
in (FStar_Pprint.op_Hat_Hat uu____3799 FStar_Pprint.qmark))
end
| FStar_Parser_AST.Paren (e1) -> begin
(

let uu____3801 = (p_term e1)
in (soft_parens_with_nesting uu____3801))
end
| uu____3802 when (is_array e) -> begin
(

let es = (extract_from_list e)
in (

let uu____3805 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar)
in (

let uu____3806 = (

let uu____3807 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (separate_map_or_flow uu____3807 p_noSeqTerm es))
in (

let uu____3808 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") uu____3805 uu____3806 uu____3808)))))
end
| uu____3809 when (is_list e) -> begin
(

let uu____3810 = (

let uu____3811 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (

let uu____3812 = (extract_from_list e)
in (separate_map_or_flow uu____3811 p_noSeqTerm uu____3812)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket uu____3810 FStar_Pprint.rbracket))
end
| uu____3814 when (is_lex_list e) -> begin
(

let uu____3815 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket)
in (

let uu____3816 = (

let uu____3817 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (

let uu____3818 = (extract_from_list e)
in (separate_map_or_flow uu____3817 p_noSeqTerm uu____3818)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____3815 uu____3816 FStar_Pprint.rbracket)))
end
| uu____3820 when (is_ref_set e) -> begin
(

let es = (extract_from_ref_set e)
in (

let uu____3823 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace)
in (

let uu____3824 = (

let uu____3825 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (separate_map_or_flow uu____3825 p_appTerm es))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") uu____3823 uu____3824 FStar_Pprint.rbrace))))
end
| FStar_Parser_AST.Labeled (e1, s, b) -> begin
(

let uu____3829 = (str (Prims.strcat "(*" (Prims.strcat s "*)")))
in (

let uu____3830 = (p_term e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____3829 uu____3830)))
end
| FStar_Parser_AST.Op (op, args) when (

let uu____3835 = (handleable_op op args)
in (not (uu____3835))) -> begin
(

let uu____3836 = (

let uu____3837 = (

let uu____3838 = (

let uu____3839 = (

let uu____3840 = (FStar_Util.string_of_int (FStar_List.length args))
in (Prims.strcat uu____3840 " arguments couldn\'t be handled by the pretty printer"))
in (Prims.strcat " with " uu____3839))
in (Prims.strcat (FStar_Ident.text_of_id op) uu____3838))
in (Prims.strcat "Operation " uu____3837))
in (failwith uu____3836))
end
| FStar_Parser_AST.Uvar (uu____3847) -> begin
(failwith "Unexpected universe variable out of universe context")
end
| FStar_Parser_AST.Wild -> begin
(

let uu____3848 = (p_term e)
in (soft_parens_with_nesting uu____3848))
end
| FStar_Parser_AST.Const (uu____3849) -> begin
(

let uu____3850 = (p_term e)
in (soft_parens_with_nesting uu____3850))
end
| FStar_Parser_AST.Op (uu____3851) -> begin
(

let uu____3855 = (p_term e)
in (soft_parens_with_nesting uu____3855))
end
| FStar_Parser_AST.Tvar (uu____3856) -> begin
(

let uu____3857 = (p_term e)
in (soft_parens_with_nesting uu____3857))
end
| FStar_Parser_AST.Var (uu____3858) -> begin
(

let uu____3859 = (p_term e)
in (soft_parens_with_nesting uu____3859))
end
| FStar_Parser_AST.Name (uu____3860) -> begin
(

let uu____3861 = (p_term e)
in (soft_parens_with_nesting uu____3861))
end
| FStar_Parser_AST.Construct (uu____3862) -> begin
(

let uu____3868 = (p_term e)
in (soft_parens_with_nesting uu____3868))
end
| FStar_Parser_AST.Abs (uu____3869) -> begin
(

let uu____3873 = (p_term e)
in (soft_parens_with_nesting uu____3873))
end
| FStar_Parser_AST.App (uu____3874) -> begin
(

let uu____3878 = (p_term e)
in (soft_parens_with_nesting uu____3878))
end
| FStar_Parser_AST.Let (uu____3879) -> begin
(

let uu____3886 = (p_term e)
in (soft_parens_with_nesting uu____3886))
end
| FStar_Parser_AST.LetOpen (uu____3887) -> begin
(

let uu____3890 = (p_term e)
in (soft_parens_with_nesting uu____3890))
end
| FStar_Parser_AST.Seq (uu____3891) -> begin
(

let uu____3894 = (p_term e)
in (soft_parens_with_nesting uu____3894))
end
| FStar_Parser_AST.Bind (uu____3895) -> begin
(

let uu____3899 = (p_term e)
in (soft_parens_with_nesting uu____3899))
end
| FStar_Parser_AST.If (uu____3900) -> begin
(

let uu____3904 = (p_term e)
in (soft_parens_with_nesting uu____3904))
end
| FStar_Parser_AST.Match (uu____3905) -> begin
(

let uu____3913 = (p_term e)
in (soft_parens_with_nesting uu____3913))
end
| FStar_Parser_AST.TryWith (uu____3914) -> begin
(

let uu____3922 = (p_term e)
in (soft_parens_with_nesting uu____3922))
end
| FStar_Parser_AST.Ascribed (uu____3923) -> begin
(

let uu____3928 = (p_term e)
in (soft_parens_with_nesting uu____3928))
end
| FStar_Parser_AST.Record (uu____3929) -> begin
(

let uu____3936 = (p_term e)
in (soft_parens_with_nesting uu____3936))
end
| FStar_Parser_AST.Project (uu____3937) -> begin
(

let uu____3940 = (p_term e)
in (soft_parens_with_nesting uu____3940))
end
| FStar_Parser_AST.Product (uu____3941) -> begin
(

let uu____3945 = (p_term e)
in (soft_parens_with_nesting uu____3945))
end
| FStar_Parser_AST.Sum (uu____3946) -> begin
(

let uu____3950 = (p_term e)
in (soft_parens_with_nesting uu____3950))
end
| FStar_Parser_AST.QForall (uu____3951) -> begin
(

let uu____3958 = (p_term e)
in (soft_parens_with_nesting uu____3958))
end
| FStar_Parser_AST.QExists (uu____3959) -> begin
(

let uu____3966 = (p_term e)
in (soft_parens_with_nesting uu____3966))
end
| FStar_Parser_AST.Refine (uu____3967) -> begin
(

let uu____3970 = (p_term e)
in (soft_parens_with_nesting uu____3970))
end
| FStar_Parser_AST.NamedTyp (uu____3971) -> begin
(

let uu____3974 = (p_term e)
in (soft_parens_with_nesting uu____3974))
end
| FStar_Parser_AST.Requires (uu____3975) -> begin
(

let uu____3979 = (p_term e)
in (soft_parens_with_nesting uu____3979))
end
| FStar_Parser_AST.Ensures (uu____3980) -> begin
(

let uu____3984 = (p_term e)
in (soft_parens_with_nesting uu____3984))
end
| FStar_Parser_AST.Assign (uu____3985) -> begin
(

let uu____3988 = (p_term e)
in (soft_parens_with_nesting uu____3988))
end
| FStar_Parser_AST.Attributes (uu____3989) -> begin
(

let uu____3991 = (p_term e)
in (soft_parens_with_nesting uu____3991))
end)))
and p_constant : FStar_Const.sconst  ->  FStar_Pprint.document = (fun uu___106_3992 -> (match (uu___106_3992) with
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

let uu____3996 = (FStar_Pprint.doc_of_char x)
in (FStar_Pprint.squotes uu____3996))
end
| FStar_Const.Const_string (bytes, uu____3998) -> begin
(

let uu____4001 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes uu____4001))
end
| FStar_Const.Const_bytearray (bytes, uu____4003) -> begin
(

let uu____4006 = (

let uu____4007 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes uu____4007))
in (

let uu____4008 = (str "B")
in (FStar_Pprint.op_Hat_Hat uu____4006 uu____4008)))
end
| FStar_Const.Const_int (repr, sign_width_opt) -> begin
(

let signedness = (fun uu___104_4020 -> (match (uu___104_4020) with
| FStar_Const.Unsigned -> begin
(str "u")
end
| FStar_Const.Signed -> begin
FStar_Pprint.empty
end))
in (

let width = (fun uu___105_4024 -> (match (uu___105_4024) with
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

let ending = (default_or_map FStar_Pprint.empty (fun uu____4033 -> (match (uu____4033) with
| (s, w) -> begin
(

let uu____4038 = (signedness s)
in (

let uu____4039 = (width w)
in (FStar_Pprint.op_Hat_Hat uu____4038 uu____4039)))
end)) sign_width_opt)
in (

let uu____4040 = (str repr)
in (FStar_Pprint.op_Hat_Hat uu____4040 ending)))))
end
| FStar_Const.Const_range (r) -> begin
(

let uu____4042 = (FStar_Range.string_of_range r)
in (str uu____4042))
end
| FStar_Const.Const_reify -> begin
(str "reify")
end
| FStar_Const.Const_reflect (lid) -> begin
(

let uu____4044 = (p_quident lid)
in (

let uu____4045 = (

let uu____4046 = (

let uu____4047 = (str "reflect")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4047))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____4046))
in (FStar_Pprint.op_Hat_Hat uu____4044 uu____4045)))
end))
and p_universe : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (

let uu____4049 = (str "u#")
in (

let uu____4050 = (p_atomicUniverse u)
in (FStar_Pprint.op_Hat_Hat uu____4049 uu____4050))))
and p_universeFrom : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (

let uu____4052 = (

let uu____4053 = (unparen u)
in uu____4053.FStar_Parser_AST.tm)
in (match (uu____4052) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____4054}, (u1)::(u2)::[]) -> begin
(

let uu____4058 = (

let uu____4059 = (p_universeFrom u1)
in (

let uu____4060 = (

let uu____4061 = (p_universeFrom u2)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____4061))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4059 uu____4060)))
in (FStar_Pprint.group uu____4058))
end
| FStar_Parser_AST.App (uu____4062) -> begin
(

let uu____4066 = (head_and_args u)
in (match (uu____4066) with
| (head1, args) -> begin
(

let uu____4080 = (

let uu____4081 = (unparen head1)
in uu____4081.FStar_Parser_AST.tm)
in (match (uu____4080) with
| FStar_Parser_AST.Var (maybe_max_lid) when (FStar_Ident.lid_equals maybe_max_lid FStar_Parser_Const.max_lid) -> begin
(

let uu____4083 = (

let uu____4084 = (p_qlident FStar_Parser_Const.max_lid)
in (

let uu____4085 = (FStar_Pprint.separate_map FStar_Pprint.space (fun uu____4091 -> (match (uu____4091) with
| (u1, uu____4095) -> begin
(p_atomicUniverse u1)
end)) args)
in (op_Hat_Slash_Plus_Hat uu____4084 uu____4085)))
in (FStar_Pprint.group uu____4083))
end
| uu____4096 -> begin
(

let uu____4097 = (

let uu____4098 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" uu____4098))
in (failwith uu____4097))
end))
end))
end
| uu____4099 -> begin
(p_atomicUniverse u)
end)))
and p_atomicUniverse : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (

let uu____4101 = (

let uu____4102 = (unparen u)
in uu____4102.FStar_Parser_AST.tm)
in (match (uu____4101) with
| FStar_Parser_AST.Wild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (r, sw)) -> begin
(p_constant (FStar_Const.Const_int (((r), (sw)))))
end
| FStar_Parser_AST.Uvar (id) -> begin
(str (FStar_Ident.text_of_id id))
end
| FStar_Parser_AST.Paren (u1) -> begin
(

let uu____4116 = (p_universeFrom u1)
in (soft_parens_with_nesting uu____4116))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____4117}, (uu____4118)::(uu____4119)::[]) -> begin
(

let uu____4121 = (p_universeFrom u)
in (soft_parens_with_nesting uu____4121))
end
| FStar_Parser_AST.App (uu____4122) -> begin
(

let uu____4126 = (p_universeFrom u)
in (soft_parens_with_nesting uu____4126))
end
| uu____4127 -> begin
(

let uu____4128 = (

let uu____4129 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" uu____4129))
in (failwith uu____4128))
end)))


let term_to_document : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_term e))


let decl_to_document : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun e -> (p_decl e))


let pat_to_document : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (p_disjunctivePattern p))


let binder_to_document : FStar_Parser_AST.binder  ->  FStar_Pprint.document = (fun b -> (p_binder true b))


let modul_to_document : FStar_Parser_AST.modul  ->  FStar_Pprint.document = (fun m -> ((FStar_ST.write should_print_fs_typ_app false);
(

let res = (match (m) with
| FStar_Parser_AST.Module (uu____4154, decls) -> begin
(

let uu____4158 = (FStar_All.pipe_right decls (FStar_List.map decl_to_document))
in (FStar_All.pipe_right uu____4158 (FStar_Pprint.separate FStar_Pprint.hardline)))
end
| FStar_Parser_AST.Interface (uu____4163, decls, uu____4165) -> begin
(

let uu____4168 = (FStar_All.pipe_right decls (FStar_List.map decl_to_document))
in (FStar_All.pipe_right uu____4168 (FStar_Pprint.separate FStar_Pprint.hardline)))
end)
in ((FStar_ST.write should_print_fs_typ_app false);
res;
));
))


let comments_to_document : (Prims.string * FStar_Range.range) Prims.list  ->  FStar_Pprint.document = (fun comments -> (FStar_Pprint.separate_map FStar_Pprint.hardline (fun uu____4191 -> (match (uu____4191) with
| (comment, range) -> begin
(str comment)
end)) comments))


let modul_with_comments_to_document : FStar_Parser_AST.modul  ->  (Prims.string * FStar_Range.range) Prims.list  ->  (FStar_Pprint.document * (Prims.string * FStar_Range.range) Prims.list) = (fun m comments -> (

let decls = (match (m) with
| FStar_Parser_AST.Module (uu____4218, decls) -> begin
decls
end
| FStar_Parser_AST.Interface (uu____4222, decls, uu____4224) -> begin
decls
end)
in ((FStar_ST.write should_print_fs_typ_app false);
(match (decls) with
| [] -> begin
((FStar_Pprint.empty), (comments))
end
| (d)::ds -> begin
(

let uu____4241 = (match (ds) with
| ({FStar_Parser_AST.d = FStar_Parser_AST.Pragma (FStar_Parser_AST.LightOff); FStar_Parser_AST.drange = uu____4248; FStar_Parser_AST.doc = uu____4249; FStar_Parser_AST.quals = uu____4250; FStar_Parser_AST.attrs = uu____4251})::uu____4252 -> begin
(

let d0 = (FStar_List.hd ds)
in (

let uu____4256 = (

let uu____4258 = (

let uu____4260 = (FStar_List.tl ds)
in (d)::uu____4260)
in (d0)::uu____4258)
in ((uu____4256), (d0.FStar_Parser_AST.drange))))
end
| uu____4263 -> begin
(((d)::ds), (d.FStar_Parser_AST.drange))
end)
in (match (uu____4241) with
| (decls1, first_range) -> begin
(

let extract_decl_range = (fun d1 -> d1.FStar_Parser_AST.drange)
in ((FStar_ST.write comment_stack comments);
(

let initial_comment = (

let uu____4286 = (FStar_Range.start_of_range first_range)
in (place_comments_until_pos (Prims.parse_int "0") (Prims.parse_int "1") uu____4286 FStar_Pprint.empty))
in (

let doc1 = (separate_map_with_comments FStar_Pprint.empty FStar_Pprint.empty decl_to_document decls1 extract_decl_range)
in (

let comments1 = (FStar_ST.read comment_stack)
in ((FStar_ST.write comment_stack []);
(FStar_ST.write should_print_fs_typ_app false);
(

let uu____4308 = (FStar_Pprint.op_Hat_Hat initial_comment doc1)
in ((uu____4308), (comments1)));
))));
))
end))
end);
)))




