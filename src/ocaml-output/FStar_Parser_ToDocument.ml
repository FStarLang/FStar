
open Prims
open FStar_Pervasives

let should_print_fs_typ_app : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let with_fs_typ_app : 'Auu____20 'Auu____21 . Prims.bool  ->  ('Auu____21  ->  'Auu____20)  ->  'Auu____21  ->  'Auu____20 = (fun b printer t -> (

let b0 = (FStar_ST.op_Bang should_print_fs_typ_app)
in ((FStar_ST.op_Colon_Equals should_print_fs_typ_app b);
(

let res = (printer t)
in ((FStar_ST.op_Colon_Equals should_print_fs_typ_app b0);
res;
));
)))


let should_unparen : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref true)


let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (

let uu____194 = (

let uu____195 = (FStar_ST.op_Bang should_unparen)
in (not (uu____195)))
in (match (uu____194) with
| true -> begin
t
end
| uu____242 -> begin
(match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t1) -> begin
(unparen t1)
end
| uu____244 -> begin
t
end)
end)))


let str : Prims.string  ->  FStar_Pprint.document = (fun s -> (FStar_Pprint.doc_of_string s))


let default_or_map : 'Auu____259 'Auu____260 . 'Auu____260  ->  ('Auu____259  ->  'Auu____260)  ->  'Auu____259 FStar_Pervasives_Native.option  ->  'Auu____260 = (fun n1 f x -> (match (x) with
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


let separate_break_map : 'Auu____329 . FStar_Pprint.document  ->  ('Auu____329  ->  FStar_Pprint.document)  ->  'Auu____329 Prims.list  ->  FStar_Pprint.document = (fun sep f l -> (

let uu____351 = (

let uu____352 = (

let uu____353 = (FStar_Pprint.op_Hat_Hat sep break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____353))
in (FStar_Pprint.separate_map uu____352 f l))
in (FStar_Pprint.group uu____351)))


let precede_break_separate_map : 'Auu____364 . FStar_Pprint.document  ->  FStar_Pprint.document  ->  ('Auu____364  ->  FStar_Pprint.document)  ->  'Auu____364 Prims.list  ->  FStar_Pprint.document = (fun prec sep f l -> (

let uu____390 = (

let uu____391 = (FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space)
in (

let uu____392 = (

let uu____393 = (FStar_List.hd l)
in (FStar_All.pipe_right uu____393 f))
in (FStar_Pprint.precede uu____391 uu____392)))
in (

let uu____394 = (

let uu____395 = (FStar_List.tl l)
in (FStar_Pprint.concat_map (fun x -> (

let uu____401 = (

let uu____402 = (

let uu____403 = (f x)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____403))
in (FStar_Pprint.op_Hat_Hat sep uu____402))
in (FStar_Pprint.op_Hat_Hat break1 uu____401))) uu____395))
in (FStar_Pprint.op_Hat_Hat uu____390 uu____394))))


let concat_break_map : 'Auu____410 . ('Auu____410  ->  FStar_Pprint.document)  ->  'Auu____410 Prims.list  ->  FStar_Pprint.document = (fun f l -> (

let uu____428 = (FStar_Pprint.concat_map (fun x -> (

let uu____432 = (f x)
in (FStar_Pprint.op_Hat_Hat uu____432 break1))) l)
in (FStar_Pprint.group uu____428)))


let parens_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lparen contents FStar_Pprint.rparen))


let soft_parens_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lparen contents FStar_Pprint.rparen))


let braces_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbrace contents FStar_Pprint.rbrace))


let soft_braces_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbrace contents FStar_Pprint.rbrace))


let brackets_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbracket contents FStar_Pprint.rbracket))


let soft_brackets_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbracket contents FStar_Pprint.rbracket))


let soft_begin_end_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (

let uu____461 = (str "begin")
in (

let uu____462 = (str "end")
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") uu____461 contents uu____462))))


let separate_map_or_flow : 'Auu____471 . FStar_Pprint.document  ->  ('Auu____471  ->  FStar_Pprint.document)  ->  'Auu____471 Prims.list  ->  FStar_Pprint.document = (fun sep f l -> (match (((FStar_List.length l) < (Prims.parse_int "10"))) with
| true -> begin
(FStar_Pprint.separate_map sep f l)
end
| uu____493 -> begin
(FStar_Pprint.flow_map sep f l)
end))


let soft_surround_separate_map : 'Auu____512 . Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  ('Auu____512  ->  FStar_Pprint.document)  ->  'Auu____512 Prims.list  ->  FStar_Pprint.document = (fun n1 b void_ opening sep closing f xs -> (match ((Prims.op_Equality xs [])) with
| true -> begin
void_
end
| uu____556 -> begin
(

let uu____557 = (FStar_Pprint.separate_map sep f xs)
in (FStar_Pprint.soft_surround n1 b opening uu____557 closing))
end))


let soft_surround_map_or_flow : 'Auu____576 . Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  ('Auu____576  ->  FStar_Pprint.document)  ->  'Auu____576 Prims.list  ->  FStar_Pprint.document = (fun n1 b void_ opening sep closing f xs -> (match ((Prims.op_Equality xs [])) with
| true -> begin
void_
end
| uu____620 -> begin
(

let uu____621 = (separate_map_or_flow sep f xs)
in (FStar_Pprint.soft_surround n1 b opening uu____621 closing))
end))


let doc_of_fsdoc : (Prims.string * (Prims.string * Prims.string) Prims.list)  ->  FStar_Pprint.document = (fun uu____635 -> (match (uu____635) with
| (comment, keywords) -> begin
(

let uu____660 = (

let uu____661 = (

let uu____664 = (str comment)
in (

let uu____665 = (

let uu____668 = (

let uu____671 = (FStar_Pprint.separate_map FStar_Pprint.comma (fun uu____680 -> (match (uu____680) with
| (k, v1) -> begin
(

let uu____687 = (

let uu____690 = (str k)
in (

let uu____691 = (

let uu____694 = (

let uu____697 = (str v1)
in (uu____697)::[])
in (FStar_Pprint.rarrow)::uu____694)
in (uu____690)::uu____691))
in (FStar_Pprint.concat uu____687))
end)) keywords)
in (uu____671)::[])
in (FStar_Pprint.space)::uu____668)
in (uu____664)::uu____665))
in (FStar_Pprint.concat uu____661))
in (FStar_Pprint.group uu____660))
end))


let is_unit : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____702 = (

let uu____703 = (unparen e)
in uu____703.FStar_Parser_AST.tm)
in (match (uu____702) with
| FStar_Parser_AST.Const (FStar_Const.Const_unit) -> begin
true
end
| uu____704 -> begin
false
end)))


let matches_var : FStar_Parser_AST.term  ->  FStar_Ident.ident  ->  Prims.bool = (fun t x -> (

let uu____713 = (

let uu____714 = (unparen t)
in uu____714.FStar_Parser_AST.tm)
in (match (uu____713) with
| FStar_Parser_AST.Var (y) -> begin
(Prims.op_Equality x.FStar_Ident.idText (FStar_Ident.text_of_lid y))
end
| uu____716 -> begin
false
end)))


let is_tuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Parser_Const.is_tuple_data_lid'


let is_dtuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Parser_Const.is_dtuple_data_lid'


let is_list_structure : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun cons_lid1 nil_lid1 -> (

let rec aux = (fun e -> (

let uu____738 = (

let uu____739 = (unparen e)
in uu____739.FStar_Parser_AST.tm)
in (match (uu____738) with
| FStar_Parser_AST.Construct (lid, []) -> begin
(FStar_Ident.lid_equals lid nil_lid1)
end
| FStar_Parser_AST.Construct (lid, (uu____752)::((e2, uu____754))::[]) -> begin
((FStar_Ident.lid_equals lid cons_lid1) && (aux e2))
end
| uu____777 -> begin
false
end)))
in aux))


let is_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Parser_Const.cons_lid FStar_Parser_Const.nil_lid)


let is_lex_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Parser_Const.lexcons_lid FStar_Parser_Const.lextop_lid)


let rec extract_from_list : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (

let uu____790 = (

let uu____791 = (unparen e)
in uu____791.FStar_Parser_AST.tm)
in (match (uu____790) with
| FStar_Parser_AST.Construct (uu____794, []) -> begin
[]
end
| FStar_Parser_AST.Construct (uu____805, ((e1, FStar_Parser_AST.Nothing))::((e2, FStar_Parser_AST.Nothing))::[]) -> begin
(

let uu____826 = (extract_from_list e2)
in (e1)::uu____826)
end
| uu____829 -> begin
(

let uu____830 = (

let uu____831 = (FStar_Parser_AST.term_to_string e)
in (FStar_Util.format1 "Not a list %s" uu____831))
in (failwith uu____830))
end)))


let is_array : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____838 = (

let uu____839 = (unparen e)
in uu____839.FStar_Parser_AST.tm)
in (match (uu____838) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (lid); FStar_Parser_AST.range = uu____841; FStar_Parser_AST.level = uu____842}, l, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) && (is_list l))
end
| uu____844 -> begin
false
end)))


let rec is_ref_set : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____849 = (

let uu____850 = (unparen e)
in uu____850.FStar_Parser_AST.tm)
in (match (uu____849) with
| FStar_Parser_AST.Var (maybe_empty_lid) -> begin
(FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty)
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_singleton_lid); FStar_Parser_AST.range = uu____853; FStar_Parser_AST.level = uu____854}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_addr_of_lid); FStar_Parser_AST.range = uu____856; FStar_Parser_AST.level = uu____857}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____859; FStar_Parser_AST.level = uu____860}, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals maybe_singleton_lid FStar_Parser_Const.set_singleton) && (FStar_Ident.lid_equals maybe_addr_of_lid FStar_Parser_Const.heap_addr_of_lid))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_union_lid); FStar_Parser_AST.range = uu____862; FStar_Parser_AST.level = uu____863}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____865; FStar_Parser_AST.level = uu____866}, e2, FStar_Parser_AST.Nothing) -> begin
(((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union) && (is_ref_set e1)) && (is_ref_set e2))
end
| uu____868 -> begin
false
end)))


let rec extract_from_ref_set : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (

let uu____875 = (

let uu____876 = (unparen e)
in uu____876.FStar_Parser_AST.tm)
in (match (uu____875) with
| FStar_Parser_AST.Var (uu____879) -> begin
[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (uu____880); FStar_Parser_AST.range = uu____881; FStar_Parser_AST.level = uu____882}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (uu____883); FStar_Parser_AST.range = uu____884; FStar_Parser_AST.level = uu____885}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____887; FStar_Parser_AST.level = uu____888}, FStar_Parser_AST.Nothing) -> begin
(e1)::[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (uu____889); FStar_Parser_AST.range = uu____890; FStar_Parser_AST.level = uu____891}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____893; FStar_Parser_AST.level = uu____894}, e2, FStar_Parser_AST.Nothing) -> begin
(

let uu____896 = (extract_from_ref_set e1)
in (

let uu____899 = (extract_from_ref_set e2)
in (FStar_List.append uu____896 uu____899)))
end
| uu____902 -> begin
(

let uu____903 = (

let uu____904 = (FStar_Parser_AST.term_to_string e)
in (FStar_Util.format1 "Not a ref set %s" uu____904))
in (failwith uu____903))
end)))


let is_general_application : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____911 = ((is_array e) || (is_ref_set e))
in (not (uu____911))))


let is_general_construction : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____916 = ((is_list e) || (is_lex_list e))
in (not (uu____916))))


let is_general_prefix_op : FStar_Ident.ident  ->  Prims.bool = (fun op -> (

let op_starting_char = (FStar_Util.char_at (FStar_Ident.text_of_id op) (Prims.parse_int "0"))
in (((Prims.op_Equality op_starting_char 33 (*!*)) || (Prims.op_Equality op_starting_char 63 (*?*))) || ((Prims.op_Equality op_starting_char 126 (*~*)) && (Prims.op_disEquality (FStar_Ident.text_of_id op) "~")))))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun e -> (

let rec aux = (fun e1 acc -> (

let uu____965 = (

let uu____966 = (unparen e1)
in uu____966.FStar_Parser_AST.tm)
in (match (uu____965) with
| FStar_Parser_AST.App (head1, arg, imp) -> begin
(aux head1 ((((arg), (imp)))::acc))
end
| uu____984 -> begin
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
| uu____999 -> begin
false
end))


let uu___is_Right : associativity  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Right -> begin
true
end
| uu____1004 -> begin
false
end))


let uu___is_NonAssoc : associativity  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NonAssoc -> begin
true
end
| uu____1009 -> begin
false
end))


type token =
(FStar_Char.char, Prims.string) FStar_Util.either


type associativity_level =
(associativity * token Prims.list)


let token_to_string : (FStar_BaseTypes.char, Prims.string) FStar_Util.either  ->  Prims.string = (fun uu___91_1027 -> (match (uu___91_1027) with
| FStar_Util.Inl (c) -> begin
(Prims.strcat (FStar_Util.string_of_char c) ".*")
end
| FStar_Util.Inr (s) -> begin
s
end))


let matches_token : Prims.string  ->  (FStar_Char.char, Prims.string) FStar_Util.either  ->  Prims.bool = (fun s uu___92_1045 -> (match (uu___92_1045) with
| FStar_Util.Inl (c) -> begin
(

let uu____1051 = (FStar_String.get s (Prims.parse_int "0"))
in (Prims.op_Equality uu____1051 c))
end
| FStar_Util.Inr (s') -> begin
(Prims.op_Equality s s')
end))


let matches_level : 'Auu____1059 . Prims.string  ->  ('Auu____1059 * (FStar_Char.char, Prims.string) FStar_Util.either Prims.list)  ->  Prims.bool = (fun s uu____1077 -> (match (uu____1077) with
| (assoc_levels, tokens) -> begin
(

let uu____1102 = (FStar_List.tryFind (matches_token s) tokens)
in (Prims.op_disEquality uu____1102 FStar_Pervasives_Native.None))
end))


let opinfix4 : 'Auu____1125 . Prims.unit  ->  (associativity * ('Auu____1125, Prims.string) FStar_Util.either Prims.list) = (fun uu____1136 -> ((Right), ((FStar_Util.Inr ("**"))::[])))


let opinfix3 : 'Auu____1153 . Prims.unit  ->  (associativity * (FStar_Char.char, 'Auu____1153) FStar_Util.either Prims.list) = (fun uu____1164 -> ((Left), ((FStar_Util.Inl (42 (***)))::(FStar_Util.Inl (47 (*/*)))::(FStar_Util.Inl (37 (*%*)))::[])))


let opinfix2 : 'Auu____1189 . Prims.unit  ->  (associativity * (FStar_Char.char, 'Auu____1189) FStar_Util.either Prims.list) = (fun uu____1200 -> ((Left), ((FStar_Util.Inl (43 (*+*)))::(FStar_Util.Inl (45 (*-*)))::[])))


let minus_lvl : 'Auu____1221 . Prims.unit  ->  (associativity * ('Auu____1221, Prims.string) FStar_Util.either Prims.list) = (fun uu____1232 -> ((Left), ((FStar_Util.Inr ("-"))::[])))


let opinfix1 : 'Auu____1249 . Prims.unit  ->  (associativity * (FStar_Char.char, 'Auu____1249) FStar_Util.either Prims.list) = (fun uu____1260 -> ((Right), ((FStar_Util.Inl (64 (*@*)))::(FStar_Util.Inl (94 (*^*)))::[])))


let pipe_right : 'Auu____1281 . Prims.unit  ->  (associativity * ('Auu____1281, Prims.string) FStar_Util.either Prims.list) = (fun uu____1292 -> ((Left), ((FStar_Util.Inr ("|>"))::[])))


let opinfix0d : 'Auu____1309 . Prims.unit  ->  (associativity * (FStar_Char.char, 'Auu____1309) FStar_Util.either Prims.list) = (fun uu____1320 -> ((Left), ((FStar_Util.Inl (36 (*$*)))::[])))


let opinfix0c : 'Auu____1337 . Prims.unit  ->  (associativity * (FStar_Char.char, 'Auu____1337) FStar_Util.either Prims.list) = (fun uu____1348 -> ((Left), ((FStar_Util.Inl (61 (*=*)))::(FStar_Util.Inl (60 (*<*)))::(FStar_Util.Inl (62 (*>*)))::[])))


let equal : 'Auu____1373 . Prims.unit  ->  (associativity * ('Auu____1373, Prims.string) FStar_Util.either Prims.list) = (fun uu____1384 -> ((Left), ((FStar_Util.Inr ("="))::[])))


let opinfix0b : 'Auu____1401 . Prims.unit  ->  (associativity * (FStar_Char.char, 'Auu____1401) FStar_Util.either Prims.list) = (fun uu____1412 -> ((Left), ((FStar_Util.Inl (38 (*&*)))::[])))


let opinfix0a : 'Auu____1429 . Prims.unit  ->  (associativity * (FStar_Char.char, 'Auu____1429) FStar_Util.either Prims.list) = (fun uu____1440 -> ((Left), ((FStar_Util.Inl (124 (*|*)))::[])))


let colon_equals : 'Auu____1457 . Prims.unit  ->  (associativity * ('Auu____1457, Prims.string) FStar_Util.either Prims.list) = (fun uu____1468 -> ((NonAssoc), ((FStar_Util.Inr (":="))::[])))


let amp : 'Auu____1485 . Prims.unit  ->  (associativity * ('Auu____1485, Prims.string) FStar_Util.either Prims.list) = (fun uu____1496 -> ((Right), ((FStar_Util.Inr ("&"))::[])))


let colon_colon : 'Auu____1513 . Prims.unit  ->  (associativity * ('Auu____1513, Prims.string) FStar_Util.either Prims.list) = (fun uu____1524 -> ((Right), ((FStar_Util.Inr ("::"))::[])))


let level_associativity_spec : (associativity * (FStar_Char.char, Prims.string) FStar_Util.either Prims.list) Prims.list = ((opinfix4 ()))::((opinfix3 ()))::((opinfix2 ()))::((opinfix1 ()))::((pipe_right ()))::((opinfix0d ()))::((opinfix0c ()))::((opinfix0b ()))::((opinfix0a ()))::((colon_equals ()))::((amp ()))::((colon_colon ()))::[]


let level_table : ((Prims.int * Prims.int * Prims.int) * (FStar_Char.char, Prims.string) FStar_Util.either Prims.list) Prims.list = (

let levels_from_associativity = (fun l uu___93_1711 -> (match (uu___93_1711) with
| Left -> begin
((l), (l), ((l - (Prims.parse_int "1"))))
end
| Right -> begin
(((l - (Prims.parse_int "1"))), (l), (l))
end
| NonAssoc -> begin
((l), (l), (l))
end))
in (FStar_List.mapi (fun i uu____1749 -> (match (uu____1749) with
| (assoc1, tokens) -> begin
(((levels_from_associativity i assoc1)), (tokens))
end)) level_associativity_spec))


let assign_levels : associativity_level Prims.list  ->  Prims.string  ->  (Prims.int * Prims.int * Prims.int) = (fun token_associativity_spec s -> (

let uu____1826 = (FStar_List.tryFind (matches_level s) level_table)
in (match (uu____1826) with
| FStar_Pervasives_Native.Some (assoc_levels, uu____1874) -> begin
assoc_levels
end
| uu____1915 -> begin
(failwith (Prims.strcat "Unrecognized operator " s))
end)))


let max : Prims.int  ->  Prims.int  ->  Prims.int = (fun k1 k2 -> (match ((k1 > k2)) with
| true -> begin
k1
end
| uu____1948 -> begin
k2
end))


let max_level : 'Auu____1953 . ('Auu____1953 * (FStar_Char.char, Prims.string) FStar_Util.either Prims.list) Prims.list  ->  Prims.int = (fun l -> (

let find_level_and_max = (fun n1 level -> (

let uu____2009 = (FStar_List.tryFind (fun uu____2047 -> (match (uu____2047) with
| (uu____2064, tokens) -> begin
(Prims.op_Equality tokens (FStar_Pervasives_Native.snd level))
end)) level_table)
in (match (uu____2009) with
| FStar_Pervasives_Native.Some ((uu____2102, l1, uu____2104), uu____2105) -> begin
(max n1 l1)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____2156 = (

let uu____2157 = (

let uu____2158 = (FStar_List.map token_to_string (FStar_Pervasives_Native.snd level))
in (FStar_String.concat "," uu____2158))
in (FStar_Util.format1 "Undefined associativity level %s" uu____2157))
in (failwith uu____2156))
end)))
in (FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l)))


let levels : Prims.string  ->  (Prims.int * Prims.int * Prims.int) = (assign_levels level_associativity_spec)


let operatorInfix0ad12 : 'Auu____2192 . Prims.unit  ->  (associativity * (FStar_Char.char, 'Auu____2192) FStar_Util.either Prims.list) Prims.list = (fun uu____2205 -> ((opinfix0a ()))::((opinfix0b ()))::((opinfix0c ()))::((opinfix0d ()))::((opinfix1 ()))::((opinfix2 ()))::[])


let is_operatorInfix0ad12 : FStar_Ident.ident  ->  Prims.bool = (fun op -> (

let uu____2280 = (

let uu____2293 = (FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op))
in (FStar_List.tryFind uu____2293 (operatorInfix0ad12 ())))
in (Prims.op_disEquality uu____2280 FStar_Pervasives_Native.None)))


let is_operatorInfix34 : FStar_Ident.ident  ->  Prims.bool = (

let opinfix34 = ((opinfix3 ()))::((opinfix4 ()))::[]
in (fun op -> (

let uu____2397 = (

let uu____2410 = (FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op))
in (FStar_List.tryFind uu____2410 opinfix34))
in (Prims.op_disEquality uu____2397 FStar_Pervasives_Native.None))))


let handleable_args_length : FStar_Ident.ident  ->  Prims.int = (fun op -> (

let op_s = (FStar_Ident.text_of_id op)
in (

let uu____2472 = ((is_general_prefix_op op) || (FStar_List.mem op_s (("-")::("~")::[])))
in (match (uu____2472) with
| true -> begin
(Prims.parse_int "1")
end
| uu____2473 -> begin
(

let uu____2474 = (((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) || (FStar_List.mem op_s (("<==>")::("==>")::("\\/")::("/\\")::("=")::("|>")::(":=")::(".()")::(".[]")::[])))
in (match (uu____2474) with
| true -> begin
(Prims.parse_int "2")
end
| uu____2475 -> begin
(match ((FStar_List.mem op_s ((".()<-")::(".[]<-")::[]))) with
| true -> begin
(Prims.parse_int "3")
end
| uu____2476 -> begin
(Prims.parse_int "0")
end)
end))
end))))


let handleable_op : 'Auu____2483 . FStar_Ident.ident  ->  'Auu____2483 Prims.list  ->  Prims.bool = (fun op args -> (match ((FStar_List.length args)) with
| _0_28 when (_0_28 = (Prims.parse_int "0")) -> begin
true
end
| _0_29 when (_0_29 = (Prims.parse_int "1")) -> begin
((is_general_prefix_op op) || (FStar_List.mem (FStar_Ident.text_of_id op) (("-")::("~")::[])))
end
| _0_30 when (_0_30 = (Prims.parse_int "2")) -> begin
(((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) || (FStar_List.mem (FStar_Ident.text_of_id op) (("<==>")::("==>")::("\\/")::("/\\")::("=")::("|>")::(":=")::(".()")::(".[]")::[])))
end
| _0_31 when (_0_31 = (Prims.parse_int "3")) -> begin
(FStar_List.mem (FStar_Ident.text_of_id op) ((".()<-")::(".[]<-")::[]))
end
| uu____2496 -> begin
false
end))


let comment_stack : (Prims.string * FStar_Range.range) Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let with_comment : 'Auu____2530 . ('Auu____2530  ->  FStar_Pprint.document)  ->  'Auu____2530  ->  FStar_Range.range  ->  FStar_Pprint.document = (fun printer tm tmrange -> (

let rec comments_before_pos = (fun acc print_pos lookahead_pos -> (

let uu____2562 = (FStar_ST.op_Bang comment_stack)
in (match (uu____2562) with
| [] -> begin
((acc), (false))
end
| ((comment, crange))::cs -> begin
(

let uu____2648 = (FStar_Range.range_before_pos crange print_pos)
in (match (uu____2648) with
| true -> begin
((FStar_ST.op_Colon_Equals comment_stack cs);
(

let uu____2712 = (

let uu____2713 = (

let uu____2714 = (str comment)
in (FStar_Pprint.op_Hat_Hat uu____2714 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat acc uu____2713))
in (comments_before_pos uu____2712 print_pos lookahead_pos));
)
end
| uu____2715 -> begin
(

let uu____2716 = (FStar_Range.range_before_pos crange lookahead_pos)
in ((acc), (uu____2716)))
end))
end)))
in (

let uu____2717 = (

let uu____2722 = (

let uu____2723 = (FStar_Range.start_of_range tmrange)
in (FStar_Range.end_of_line uu____2723))
in (

let uu____2724 = (FStar_Range.end_of_range tmrange)
in (comments_before_pos FStar_Pprint.empty uu____2722 uu____2724)))
in (match (uu____2717) with
| (comments, has_lookahead) -> begin
(

let printed_e = (printer tm)
in (

let comments1 = (match (has_lookahead) with
| true -> begin
(

let pos = (FStar_Range.end_of_range tmrange)
in (

let uu____2730 = (comments_before_pos comments pos pos)
in (FStar_Pervasives_Native.fst uu____2730)))
end
| uu____2735 -> begin
comments
end)
in (

let uu____2736 = (FStar_Pprint.op_Hat_Hat comments1 printed_e)
in (FStar_Pprint.group uu____2736))))
end))))


let rec place_comments_until_pos : Prims.int  ->  Prims.int  ->  FStar_Range.pos  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun k lbegin pos_end doc1 -> (

let uu____2753 = (FStar_ST.op_Bang comment_stack)
in (match (uu____2753) with
| ((comment, crange))::cs when (FStar_Range.range_before_pos crange pos_end) -> begin
((FStar_ST.op_Colon_Equals comment_stack cs);
(

let lnum = (

let uu____2891 = (

let uu____2892 = (

let uu____2893 = (FStar_Range.start_of_range crange)
in (FStar_Range.line_of_pos uu____2893))
in (uu____2892 - lbegin))
in (max k uu____2891))
in (

let doc2 = (

let uu____2895 = (

let uu____2896 = (FStar_Pprint.repeat lnum FStar_Pprint.hardline)
in (

let uu____2897 = (str comment)
in (FStar_Pprint.op_Hat_Hat uu____2896 uu____2897)))
in (FStar_Pprint.op_Hat_Hat doc1 uu____2895))
in (

let uu____2898 = (

let uu____2899 = (FStar_Range.end_of_range crange)
in (FStar_Range.line_of_pos uu____2899))
in (place_comments_until_pos (Prims.parse_int "1") uu____2898 pos_end doc2))));
)
end
| uu____2900 -> begin
(

let lnum = (

let uu____2908 = (

let uu____2909 = (FStar_Range.line_of_pos pos_end)
in (uu____2909 - lbegin))
in (max (Prims.parse_int "1") uu____2908))
in (

let uu____2910 = (FStar_Pprint.repeat lnum FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat doc1 uu____2910)))
end)))


let separate_map_with_comments : 'Auu____2923 . FStar_Pprint.document  ->  FStar_Pprint.document  ->  ('Auu____2923  ->  FStar_Pprint.document)  ->  'Auu____2923 Prims.list  ->  ('Auu____2923  ->  FStar_Range.range)  ->  FStar_Pprint.document = (fun prefix1 sep f xs extract_range -> (

let fold_fun = (fun uu____2971 x -> (match (uu____2971) with
| (last_line, doc1) -> begin
(

let r = (extract_range x)
in (

let doc2 = (

let uu____2985 = (FStar_Range.start_of_range r)
in (place_comments_until_pos (Prims.parse_int "1") last_line uu____2985 doc1))
in (

let uu____2986 = (

let uu____2987 = (FStar_Range.end_of_range r)
in (FStar_Range.line_of_pos uu____2987))
in (

let uu____2988 = (

let uu____2989 = (

let uu____2990 = (f x)
in (FStar_Pprint.op_Hat_Hat sep uu____2990))
in (FStar_Pprint.op_Hat_Hat doc2 uu____2989))
in ((uu____2986), (uu____2988))))))
end))
in (

let uu____2991 = (

let uu____2998 = (FStar_List.hd xs)
in (

let uu____2999 = (FStar_List.tl xs)
in ((uu____2998), (uu____2999))))
in (match (uu____2991) with
| (x, xs1) -> begin
(

let init1 = (

let uu____3015 = (

let uu____3016 = (

let uu____3017 = (extract_range x)
in (FStar_Range.end_of_range uu____3017))
in (FStar_Range.line_of_pos uu____3016))
in (

let uu____3018 = (

let uu____3019 = (f x)
in (FStar_Pprint.op_Hat_Hat prefix1 uu____3019))
in ((uu____3015), (uu____3018))))
in (

let uu____3020 = (FStar_List.fold_left fold_fun init1 xs1)
in (FStar_Pervasives_Native.snd uu____3020)))
end))))


let rec p_decl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (

let uu____3315 = (

let uu____3316 = (FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc)
in (

let uu____3317 = (

let uu____3318 = (p_attributes d.FStar_Parser_AST.attrs)
in (

let uu____3319 = (

let uu____3320 = (p_qualifiers d.FStar_Parser_AST.quals)
in (

let uu____3321 = (

let uu____3322 = (p_rawDecl d)
in (FStar_Pprint.op_Hat_Hat (match ((Prims.op_Equality d.FStar_Parser_AST.quals [])) with
| true -> begin
FStar_Pprint.empty
end
| uu____3323 -> begin
break1
end) uu____3322))
in (FStar_Pprint.op_Hat_Hat uu____3320 uu____3321)))
in (FStar_Pprint.op_Hat_Hat uu____3318 uu____3319)))
in (FStar_Pprint.op_Hat_Hat uu____3316 uu____3317)))
in (FStar_Pprint.group uu____3315)))
and p_attributes : FStar_Parser_AST.attributes_  ->  FStar_Pprint.document = (fun attrs -> (

let uu____3325 = (

let uu____3326 = (str "@")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3326))
in (

let uu____3327 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline)
in (soft_surround_map_or_flow (Prims.parse_int "0") (Prims.parse_int "2") FStar_Pprint.empty uu____3325 FStar_Pprint.space uu____3327 p_atomicTerm attrs))))
and p_fsdoc : FStar_Parser_AST.fsdoc  ->  FStar_Pprint.document = (fun uu____3328 -> (match (uu____3328) with
| (doc1, kwd_args) -> begin
(

let kwd_args_doc = (match (kwd_args) with
| [] -> begin
FStar_Pprint.empty
end
| kwd_args1 -> begin
(

let process_kwd_arg = (fun uu____3362 -> (match (uu____3362) with
| (kwd, arg) -> begin
(

let uu____3369 = (str "@")
in (

let uu____3370 = (

let uu____3371 = (str kwd)
in (

let uu____3372 = (

let uu____3373 = (str arg)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3373))
in (FStar_Pprint.op_Hat_Hat uu____3371 uu____3372)))
in (FStar_Pprint.op_Hat_Hat uu____3369 uu____3370)))
end))
in (

let uu____3374 = (

let uu____3375 = (FStar_Pprint.separate_map FStar_Pprint.hardline process_kwd_arg kwd_args1)
in (FStar_Pprint.op_Hat_Hat uu____3375 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3374)))
end)
in (

let uu____3380 = (

let uu____3381 = (

let uu____3382 = (

let uu____3383 = (

let uu____3384 = (str doc1)
in (

let uu____3385 = (

let uu____3386 = (

let uu____3387 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3387))
in (FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3386))
in (FStar_Pprint.op_Hat_Hat uu____3384 uu____3385)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3383))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3382))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3381))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3380)))
end))
and p_justSig : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (lid, t) -> begin
(

let uu____3391 = (

let uu____3392 = (str "val")
in (

let uu____3393 = (

let uu____3394 = (

let uu____3395 = (p_lident lid)
in (

let uu____3396 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat uu____3395 uu____3396)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3394))
in (FStar_Pprint.op_Hat_Hat uu____3392 uu____3393)))
in (

let uu____3397 = (p_typ t)
in (op_Hat_Slash_Plus_Hat uu____3391 uu____3397)))
end
| FStar_Parser_AST.TopLevelLet (uu____3398, lbs) -> begin
(FStar_Pprint.separate_map FStar_Pprint.hardline (fun lb -> (

let uu____3423 = (

let uu____3424 = (str "let")
in (

let uu____3425 = (p_letlhs lb)
in (FStar_Pprint.op_Hat_Slash_Hat uu____3424 uu____3425)))
in (FStar_Pprint.group uu____3423))) lbs)
end
| uu____3426 -> begin
FStar_Pprint.empty
end))
and p_rawDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Open (uid) -> begin
(

let uu____3429 = (

let uu____3430 = (str "open")
in (

let uu____3431 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat uu____3430 uu____3431)))
in (FStar_Pprint.group uu____3429))
end
| FStar_Parser_AST.Include (uid) -> begin
(

let uu____3433 = (

let uu____3434 = (str "include")
in (

let uu____3435 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat uu____3434 uu____3435)))
in (FStar_Pprint.group uu____3433))
end
| FStar_Parser_AST.ModuleAbbrev (uid1, uid2) -> begin
(

let uu____3438 = (

let uu____3439 = (str "module")
in (

let uu____3440 = (

let uu____3441 = (

let uu____3442 = (p_uident uid1)
in (

let uu____3443 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____3442 uu____3443)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3441))
in (FStar_Pprint.op_Hat_Hat uu____3439 uu____3440)))
in (

let uu____3444 = (p_quident uid2)
in (op_Hat_Slash_Plus_Hat uu____3438 uu____3444)))
end
| FStar_Parser_AST.TopLevelModule (uid) -> begin
(

let uu____3446 = (

let uu____3447 = (str "module")
in (

let uu____3448 = (

let uu____3449 = (p_quident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3449))
in (FStar_Pprint.op_Hat_Hat uu____3447 uu____3448)))
in (FStar_Pprint.group uu____3446))
end
| FStar_Parser_AST.Tycon (true, ((FStar_Parser_AST.TyconAbbrev (uid, tpars, FStar_Pervasives_Native.None, t), FStar_Pervasives_Native.None))::[]) -> begin
(

let effect_prefix_doc = (

let uu____3482 = (str "effect")
in (

let uu____3483 = (

let uu____3484 = (p_uident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3484))
in (FStar_Pprint.op_Hat_Hat uu____3482 uu____3483)))
in (

let uu____3485 = (

let uu____3486 = (p_typars tpars)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") effect_prefix_doc uu____3486 FStar_Pprint.equals))
in (

let uu____3487 = (p_typ t)
in (op_Hat_Slash_Plus_Hat uu____3485 uu____3487))))
end
| FStar_Parser_AST.Tycon (false, tcdefs) -> begin
(

let uu____3505 = (str "type")
in (

let uu____3506 = (str "and")
in (precede_break_separate_map uu____3505 uu____3506 p_fsdocTypeDeclPairs tcdefs)))
end
| FStar_Parser_AST.TopLevelLet (q, lbs) -> begin
(

let let_doc = (

let uu____3528 = (str "let")
in (

let uu____3529 = (

let uu____3530 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat uu____3530 FStar_Pprint.space))
in (FStar_Pprint.op_Hat_Hat uu____3528 uu____3529)))
in (

let uu____3531 = (

let uu____3532 = (str "and")
in (FStar_Pprint.op_Hat_Hat uu____3532 FStar_Pprint.space))
in (separate_map_with_comments let_doc uu____3531 p_letbinding lbs (fun uu____3540 -> (match (uu____3540) with
| (p, t) -> begin
(FStar_Range.union_ranges p.FStar_Parser_AST.prange t.FStar_Parser_AST.range)
end)))))
end
| FStar_Parser_AST.Val (lid, t) -> begin
(

let uu____3549 = (

let uu____3550 = (str "val")
in (

let uu____3551 = (

let uu____3552 = (

let uu____3553 = (p_lident lid)
in (

let uu____3554 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat uu____3553 uu____3554)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3552))
in (FStar_Pprint.op_Hat_Hat uu____3550 uu____3551)))
in (

let uu____3555 = (p_typ t)
in (op_Hat_Slash_Plus_Hat uu____3549 uu____3555)))
end
| FStar_Parser_AST.Assume (id, t) -> begin
(

let decl_keyword = (

let uu____3559 = (

let uu____3560 = (FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_All.pipe_right uu____3560 FStar_Util.is_upper))
in (match (uu____3559) with
| true -> begin
FStar_Pprint.empty
end
| uu____3561 -> begin
(

let uu____3562 = (str "val")
in (FStar_Pprint.op_Hat_Hat uu____3562 FStar_Pprint.space))
end))
in (

let uu____3563 = (

let uu____3564 = (

let uu____3565 = (p_ident id)
in (

let uu____3566 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat uu____3565 uu____3566)))
in (FStar_Pprint.op_Hat_Hat decl_keyword uu____3564))
in (

let uu____3567 = (p_typ t)
in (op_Hat_Slash_Plus_Hat uu____3563 uu____3567))))
end
| FStar_Parser_AST.Exception (uid, t_opt) -> begin
(

let uu____3574 = (str "exception")
in (

let uu____3575 = (

let uu____3576 = (

let uu____3577 = (p_uident uid)
in (

let uu____3578 = (FStar_Pprint.optional (fun t -> (

let uu____3583 = (str "of")
in (

let uu____3584 = (p_typ t)
in (op_Hat_Slash_Plus_Hat uu____3583 uu____3584)))) t_opt)
in (FStar_Pprint.op_Hat_Hat uu____3577 uu____3578)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3576))
in (FStar_Pprint.op_Hat_Hat uu____3574 uu____3575)))
end
| FStar_Parser_AST.NewEffect (ne) -> begin
(

let uu____3586 = (str "new_effect")
in (

let uu____3587 = (

let uu____3588 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3588))
in (FStar_Pprint.op_Hat_Hat uu____3586 uu____3587)))
end
| FStar_Parser_AST.SubEffect (se) -> begin
(

let uu____3590 = (str "sub_effect")
in (

let uu____3591 = (

let uu____3592 = (p_subEffect se)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3592))
in (FStar_Pprint.op_Hat_Hat uu____3590 uu____3591)))
end
| FStar_Parser_AST.Pragma (p) -> begin
(p_pragma p)
end
| FStar_Parser_AST.Fsdoc (doc1) -> begin
(

let uu____3595 = (p_fsdoc doc1)
in (FStar_Pprint.op_Hat_Hat uu____3595 FStar_Pprint.hardline))
end
| FStar_Parser_AST.Main (uu____3596) -> begin
(failwith "*Main declaration* : Is that really still in use ??")
end
| FStar_Parser_AST.Tycon (true, uu____3597) -> begin
(failwith "Effect abbreviation is expected to be defined by an abbreviation")
end))
and p_pragma : FStar_Parser_AST.pragma  ->  FStar_Pprint.document = (fun uu___94_3614 -> (match (uu___94_3614) with
| FStar_Parser_AST.SetOptions (s) -> begin
(

let uu____3616 = (str "#set-options")
in (

let uu____3617 = (

let uu____3618 = (

let uu____3619 = (str s)
in (FStar_Pprint.dquotes uu____3619))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3618))
in (FStar_Pprint.op_Hat_Hat uu____3616 uu____3617)))
end
| FStar_Parser_AST.ResetOptions (s_opt) -> begin
(

let uu____3623 = (str "#reset-options")
in (

let uu____3624 = (FStar_Pprint.optional (fun s -> (

let uu____3628 = (

let uu____3629 = (str s)
in (FStar_Pprint.dquotes uu____3629))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3628))) s_opt)
in (FStar_Pprint.op_Hat_Hat uu____3623 uu____3624)))
end
| FStar_Parser_AST.LightOff -> begin
((FStar_ST.op_Colon_Equals should_print_fs_typ_app true);
(str "#light \"off\"");
)
end))
and p_typars : FStar_Parser_AST.binder Prims.list  ->  FStar_Pprint.document = (fun bs -> (p_binders true bs))
and p_fsdocTypeDeclPairs : (FStar_Parser_AST.tycon * FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option)  ->  FStar_Pprint.document = (fun uu____3680 -> (match (uu____3680) with
| (typedecl, fsdoc_opt) -> begin
(

let uu____3693 = (FStar_Pprint.optional p_fsdoc fsdoc_opt)
in (

let uu____3694 = (p_typeDecl typedecl)
in (FStar_Pprint.op_Hat_Hat uu____3693 uu____3694)))
end))
and p_typeDecl : FStar_Parser_AST.tycon  ->  FStar_Pprint.document = (fun uu___95_3695 -> (match (uu___95_3695) with
| FStar_Parser_AST.TyconAbstract (lid, bs, typ_opt) -> begin
(

let empty' = (fun uu____3710 -> FStar_Pprint.empty)
in (p_typeDeclPrefix lid bs typ_opt empty'))
end
| FStar_Parser_AST.TyconAbbrev (lid, bs, typ_opt, t) -> begin
(

let f = (fun uu____3726 -> (

let uu____3727 = (p_typ t)
in (prefix2 FStar_Pprint.equals uu____3727)))
in (p_typeDeclPrefix lid bs typ_opt f))
end
| FStar_Parser_AST.TyconRecord (lid, bs, typ_opt, record_field_decls) -> begin
(

let p_recordFieldAndComments = (fun uu____3771 -> (match (uu____3771) with
| (lid1, t, doc_opt) -> begin
(

let uu____3787 = (FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range)
in (with_comment p_recordFieldDecl ((lid1), (t), (doc_opt)) uu____3787))
end))
in (

let p_fields = (fun uu____3801 -> (

let uu____3802 = (

let uu____3803 = (

let uu____3804 = (

let uu____3805 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (FStar_Pprint.separate_map uu____3805 p_recordFieldAndComments record_field_decls))
in (braces_with_nesting uu____3804))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3803))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____3802)))
in (p_typeDeclPrefix lid bs typ_opt p_fields)))
end
| FStar_Parser_AST.TyconVariant (lid, bs, typ_opt, ct_decls) -> begin
(

let p_constructorBranchAndComments = (fun uu____3869 -> (match (uu____3869) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let range = (

let uu____3895 = (

let uu____3896 = (FStar_Util.map_opt t_opt (fun t -> t.FStar_Parser_AST.range))
in (FStar_Util.dflt uid.FStar_Ident.idRange uu____3896))
in (FStar_Range.extend_to_end_of_line uu____3895))
in (

let p_constructorBranch = (fun decl -> (

let uu____3929 = (

let uu____3930 = (

let uu____3931 = (p_constructorDecl decl)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3931))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____3930))
in (FStar_Pprint.group uu____3929)))
in (with_comment p_constructorBranch ((uid), (t_opt), (doc_opt), (use_of)) range)))
end))
in (

let datacon_doc = (fun uu____3951 -> (

let uu____3952 = (FStar_Pprint.separate_map break1 p_constructorBranchAndComments ct_decls)
in (FStar_Pprint.group uu____3952)))
in (p_typeDeclPrefix lid bs typ_opt (fun uu____3967 -> (

let uu____3968 = (datacon_doc ())
in (prefix2 FStar_Pprint.equals uu____3968))))))
end))
and p_typeDeclPrefix : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.knd FStar_Pervasives_Native.option  ->  (Prims.unit  ->  FStar_Pprint.document)  ->  FStar_Pprint.document = (fun lid bs typ_opt cont -> (match (((Prims.op_Equality bs []) && (Prims.op_Equality typ_opt FStar_Pervasives_Native.None))) with
| true -> begin
(

let uu____3983 = (p_ident lid)
in (

let uu____3984 = (

let uu____3985 = (cont ())
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3985))
in (FStar_Pprint.op_Hat_Hat uu____3983 uu____3984)))
end
| uu____3986 -> begin
(

let binders_doc = (

let uu____3988 = (p_typars bs)
in (

let uu____3989 = (FStar_Pprint.optional (fun t -> (

let uu____3993 = (

let uu____3994 = (

let uu____3995 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3995))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3994))
in (FStar_Pprint.op_Hat_Hat break1 uu____3993))) typ_opt)
in (FStar_Pprint.op_Hat_Hat uu____3988 uu____3989)))
in (

let uu____3996 = (p_ident lid)
in (

let uu____3997 = (cont ())
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____3996 binders_doc uu____3997))))
end))
and p_recordFieldDecl : (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option)  ->  FStar_Pprint.document = (fun uu____3998 -> (match (uu____3998) with
| (lid, t, doc_opt) -> begin
(

let uu____4014 = (

let uu____4015 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (

let uu____4016 = (

let uu____4017 = (p_lident lid)
in (

let uu____4018 = (

let uu____4019 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4019))
in (FStar_Pprint.op_Hat_Hat uu____4017 uu____4018)))
in (FStar_Pprint.op_Hat_Hat uu____4015 uu____4016)))
in (FStar_Pprint.group uu____4014))
end))
and p_constructorDecl : (FStar_Ident.ident * FStar_Parser_AST.term FStar_Pervasives_Native.option * FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option * Prims.bool)  ->  FStar_Pprint.document = (fun uu____4020 -> (match (uu____4020) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let sep = (match (use_of) with
| true -> begin
(str "of")
end
| uu____4046 -> begin
FStar_Pprint.colon
end)
in (

let uid_doc = (p_uident uid)
in (

let uu____4048 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (

let uu____4049 = (

let uu____4050 = (FStar_Pprint.break_ (Prims.parse_int "0"))
in (

let uu____4051 = (default_or_map uid_doc (fun t -> (

let uu____4056 = (

let uu____4057 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep)
in (FStar_Pprint.op_Hat_Hat uid_doc uu____4057))
in (

let uu____4058 = (p_typ t)
in (op_Hat_Slash_Plus_Hat uu____4056 uu____4058)))) t_opt)
in (FStar_Pprint.op_Hat_Hat uu____4050 uu____4051)))
in (FStar_Pprint.op_Hat_Hat uu____4048 uu____4049)))))
end))
and p_letlhs : (FStar_Parser_AST.pattern * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun uu____4059 -> (match (uu____4059) with
| (pat, uu____4065) -> begin
(

let uu____4066 = (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat1, t) -> begin
(

let uu____4077 = (

let uu____4078 = (

let uu____4079 = (

let uu____4080 = (

let uu____4081 = (p_tmArrow p_tmNoEq t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4081))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4080))
in (FStar_Pprint.group uu____4079))
in (FStar_Pprint.op_Hat_Hat break1 uu____4078))
in ((pat1), (uu____4077)))
end
| uu____4082 -> begin
((pat), (FStar_Pprint.empty))
end)
in (match (uu____4066) with
| (pat1, ascr_doc) -> begin
(match (pat1.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____4086); FStar_Parser_AST.prange = uu____4087}, pats) -> begin
(

let uu____4097 = (

let uu____4098 = (p_lident x)
in (

let uu____4099 = (

let uu____4100 = (separate_map_or_flow break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Hat uu____4100 ascr_doc))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4098 uu____4099)))
in (FStar_Pprint.group uu____4097))
end
| uu____4101 -> begin
(

let uu____4102 = (

let uu____4103 = (p_tuplePattern pat1)
in (FStar_Pprint.op_Hat_Hat uu____4103 ascr_doc))
in (FStar_Pprint.group uu____4102))
end)
end))
end))
and p_letbinding : (FStar_Parser_AST.pattern * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun uu____4104 -> (match (uu____4104) with
| (pat, e) -> begin
(

let pat_doc = (p_letlhs ((pat), (e)))
in (

let uu____4112 = (

let uu____4113 = (FStar_Pprint.op_Hat_Slash_Hat pat_doc FStar_Pprint.equals)
in (FStar_Pprint.group uu____4113))
in (

let uu____4114 = (p_term e)
in (prefix2 uu____4112 uu____4114))))
end))
and p_newEffect : FStar_Parser_AST.effect_decl  ->  FStar_Pprint.document = (fun uu___96_4115 -> (match (uu___96_4115) with
| FStar_Parser_AST.RedefineEffect (lid, bs, t) -> begin
(p_effectRedefinition lid bs t)
end
| FStar_Parser_AST.DefineEffect (lid, bs, t, eff_decls) -> begin
(p_effectDefinition lid bs t eff_decls)
end))
and p_effectRedefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun uid bs t -> (

let uu____4140 = (p_uident uid)
in (

let uu____4141 = (p_binders true bs)
in (

let uu____4142 = (

let uu____4143 = (p_simpleTerm t)
in (prefix2 FStar_Pprint.equals uu____4143))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____4140 uu____4141 uu____4142)))))
and p_effectDefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun uid bs t eff_decls -> (

let uu____4152 = (

let uu____4153 = (

let uu____4154 = (

let uu____4155 = (p_uident uid)
in (

let uu____4156 = (p_binders true bs)
in (

let uu____4157 = (

let uu____4158 = (p_typ t)
in (prefix2 FStar_Pprint.colon uu____4158))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____4155 uu____4156 uu____4157))))
in (FStar_Pprint.group uu____4154))
in (

let uu____4159 = (

let uu____4160 = (str "with")
in (

let uu____4161 = (separate_break_map FStar_Pprint.semi p_effectDecl eff_decls)
in (prefix2 uu____4160 uu____4161)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4153 uu____4159)))
in (braces_with_nesting uu____4152)))
and p_effectDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (false, ((FStar_Parser_AST.TyconAbbrev (lid, [], FStar_Pervasives_Native.None, e), FStar_Pervasives_Native.None))::[]) -> begin
(

let uu____4191 = (

let uu____4192 = (p_lident lid)
in (

let uu____4193 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____4192 uu____4193)))
in (

let uu____4194 = (p_simpleTerm e)
in (prefix2 uu____4191 uu____4194)))
end
| uu____4195 -> begin
(

let uu____4196 = (

let uu____4197 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "Not a declaration of an effect member... or at least I hope so : %s" uu____4197))
in (failwith uu____4196))
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

let p_lift = (fun uu____4252 -> (match (uu____4252) with
| (kwd, t) -> begin
(

let uu____4259 = (

let uu____4260 = (str kwd)
in (

let uu____4261 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____4260 uu____4261)))
in (

let uu____4262 = (p_simpleTerm t)
in (prefix2 uu____4259 uu____4262)))
end))
in (separate_break_map FStar_Pprint.semi p_lift lifts)))
in (

let uu____4267 = (

let uu____4268 = (

let uu____4269 = (p_quident lift.FStar_Parser_AST.msource)
in (

let uu____4270 = (

let uu____4271 = (str "~>")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4271))
in (FStar_Pprint.op_Hat_Hat uu____4269 uu____4270)))
in (

let uu____4272 = (p_quident lift.FStar_Parser_AST.mdest)
in (prefix2 uu____4268 uu____4272)))
in (

let uu____4273 = (

let uu____4274 = (braces_with_nesting lift_op_doc)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4274))
in (FStar_Pprint.op_Hat_Hat uu____4267 uu____4273)))))
and p_qualifier : FStar_Parser_AST.qualifier  ->  FStar_Pprint.document = (fun uu___97_4275 -> (match (uu___97_4275) with
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

let uu____4277 = (FStar_Pprint.separate_map break1 p_qualifier qs)
in (FStar_Pprint.group uu____4277)))
and p_letqualifier : FStar_Parser_AST.let_qualifier  ->  FStar_Pprint.document = (fun uu___98_4278 -> (match (uu___98_4278) with
| FStar_Parser_AST.Rec -> begin
(

let uu____4279 = (str "rec")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4279))
end
| FStar_Parser_AST.Mutable -> begin
(

let uu____4280 = (str "mutable")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4280))
end
| FStar_Parser_AST.NoLetQualifier -> begin
FStar_Pprint.empty
end))
and p_aqual : FStar_Parser_AST.arg_qualifier  ->  FStar_Pprint.document = (fun uu___99_4281 -> (match (uu___99_4281) with
| FStar_Parser_AST.Implicit -> begin
(str "#")
end
| FStar_Parser_AST.Equality -> begin
(str "$")
end))
and p_disjunctivePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr (pats) -> begin
(

let uu____4286 = (

let uu____4287 = (

let uu____4288 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space)
in (FStar_Pprint.op_Hat_Hat break1 uu____4288))
in (FStar_Pprint.separate_map uu____4287 p_tuplePattern pats))
in (FStar_Pprint.group uu____4286))
end
| uu____4289 -> begin
(p_tuplePattern p)
end))
and p_tuplePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTuple (pats, false) -> begin
(

let uu____4296 = (

let uu____4297 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map uu____4297 p_constructorPattern pats))
in (FStar_Pprint.group uu____4296))
end
| uu____4298 -> begin
(p_constructorPattern p)
end))
and p_constructorPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (maybe_cons_lid); FStar_Parser_AST.prange = uu____4301}, (hd1)::(tl1)::[]) when (FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid) -> begin
(

let uu____4306 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon)
in (

let uu____4307 = (p_constructorPattern hd1)
in (

let uu____4308 = (p_constructorPattern tl1)
in (infix0 uu____4306 uu____4307 uu____4308))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (uid); FStar_Parser_AST.prange = uu____4310}, pats) -> begin
(

let uu____4316 = (p_quident uid)
in (

let uu____4317 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (prefix2 uu____4316 uu____4317)))
end
| uu____4318 -> begin
(p_atomicPattern p)
end))
and p_atomicPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, t) -> begin
(

let uu____4322 = (

let uu____4327 = (

let uu____4328 = (unparen t)
in uu____4328.FStar_Parser_AST.tm)
in ((pat.FStar_Parser_AST.pat), (uu____4327)))
in (match (uu____4322) with
| (FStar_Parser_AST.PatVar (lid, aqual), FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t1); FStar_Parser_AST.brange = uu____4333; FStar_Parser_AST.blevel = uu____4334; FStar_Parser_AST.aqual = uu____4335}, phi)) when (Prims.op_Equality lid.FStar_Ident.idText lid'.FStar_Ident.idText) -> begin
(

let uu____4341 = (

let uu____4342 = (p_ident lid)
in (p_refinement aqual uu____4342 t1 phi))
in (soft_parens_with_nesting uu____4341))
end
| (FStar_Parser_AST.PatWild, FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t1); FStar_Parser_AST.brange = uu____4344; FStar_Parser_AST.blevel = uu____4345; FStar_Parser_AST.aqual = uu____4346}, phi)) -> begin
(

let uu____4348 = (p_refinement FStar_Pervasives_Native.None FStar_Pprint.underscore t1 phi)
in (soft_parens_with_nesting uu____4348))
end
| uu____4349 -> begin
(

let uu____4354 = (

let uu____4355 = (p_tuplePattern pat)
in (

let uu____4356 = (

let uu____4357 = (FStar_Pprint.break_ (Prims.parse_int "0"))
in (

let uu____4358 = (

let uu____4359 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4359))
in (FStar_Pprint.op_Hat_Hat uu____4357 uu____4358)))
in (FStar_Pprint.op_Hat_Hat uu____4355 uu____4356)))
in (soft_parens_with_nesting uu____4354))
end))
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let uu____4363 = (separate_break_map FStar_Pprint.semi p_tuplePattern pats)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket uu____4363 FStar_Pprint.rbracket))
end
| FStar_Parser_AST.PatRecord (pats) -> begin
(

let p_recordFieldPat = (fun uu____4378 -> (match (uu____4378) with
| (lid, pat) -> begin
(

let uu____4385 = (p_qlident lid)
in (

let uu____4386 = (p_tuplePattern pat)
in (infix2 FStar_Pprint.equals uu____4385 uu____4386)))
end))
in (

let uu____4387 = (separate_break_map FStar_Pprint.semi p_recordFieldPat pats)
in (soft_braces_with_nesting uu____4387)))
end
| FStar_Parser_AST.PatTuple (pats, true) -> begin
(

let uu____4397 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (

let uu____4398 = (separate_break_map FStar_Pprint.comma p_constructorPattern pats)
in (

let uu____4399 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____4397 uu____4398 uu____4399))))
end
| FStar_Parser_AST.PatTvar (tv, arg_qualifier_opt) -> begin
(p_tvar tv)
end
| FStar_Parser_AST.PatOp (op) -> begin
(

let uu____4410 = (

let uu____4411 = (

let uu____4412 = (str (FStar_Ident.text_of_id op))
in (

let uu____4413 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat uu____4412 uu____4413)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4411))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4410))
end
| FStar_Parser_AST.PatWild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.PatConst (c) -> begin
(p_constant c)
end
| FStar_Parser_AST.PatVar (lid, aqual) -> begin
(

let uu____4421 = (FStar_Pprint.optional p_aqual aqual)
in (

let uu____4422 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat uu____4421 uu____4422)))
end
| FStar_Parser_AST.PatName (uid) -> begin
(p_quident uid)
end
| FStar_Parser_AST.PatOr (uu____4424) -> begin
(failwith "Inner or pattern !")
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (uu____4427); FStar_Parser_AST.prange = uu____4428}, uu____4429) -> begin
(

let uu____4434 = (p_tuplePattern p)
in (soft_parens_with_nesting uu____4434))
end
| FStar_Parser_AST.PatTuple (uu____4435, false) -> begin
(

let uu____4440 = (p_tuplePattern p)
in (soft_parens_with_nesting uu____4440))
end
| uu____4441 -> begin
(

let uu____4442 = (

let uu____4443 = (FStar_Parser_AST.pat_to_string p)
in (FStar_Util.format1 "Invalid pattern %s" uu____4443))
in (failwith uu____4442))
end))
and p_binder : Prims.bool  ->  FStar_Parser_AST.binder  ->  FStar_Pprint.document = (fun is_atomic b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (lid) -> begin
(

let uu____4447 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (

let uu____4448 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat uu____4447 uu____4448)))
end
| FStar_Parser_AST.TVariable (lid) -> begin
(p_lident lid)
end
| FStar_Parser_AST.Annotated (lid, t) -> begin
(

let doc1 = (

let uu____4453 = (

let uu____4454 = (unparen t)
in uu____4454.FStar_Parser_AST.tm)
in (match (uu____4453) with
| FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t1); FStar_Parser_AST.brange = uu____4457; FStar_Parser_AST.blevel = uu____4458; FStar_Parser_AST.aqual = uu____4459}, phi) when (Prims.op_Equality lid.FStar_Ident.idText lid'.FStar_Ident.idText) -> begin
(

let uu____4461 = (p_ident lid)
in (p_refinement b.FStar_Parser_AST.aqual uu____4461 t1 phi))
end
| uu____4462 -> begin
(

let uu____4463 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (

let uu____4464 = (

let uu____4465 = (p_lident lid)
in (

let uu____4466 = (

let uu____4467 = (

let uu____4468 = (FStar_Pprint.break_ (Prims.parse_int "0"))
in (

let uu____4469 = (p_tmFormula t)
in (FStar_Pprint.op_Hat_Hat uu____4468 uu____4469)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4467))
in (FStar_Pprint.op_Hat_Hat uu____4465 uu____4466)))
in (FStar_Pprint.op_Hat_Hat uu____4463 uu____4464)))
end))
in (match (is_atomic) with
| true -> begin
(

let uu____4470 = (

let uu____4471 = (FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4471))
in (FStar_Pprint.group uu____4470))
end
| uu____4472 -> begin
(FStar_Pprint.group doc1)
end))
end
| FStar_Parser_AST.TAnnotated (uu____4473) -> begin
(failwith "Is this still used ?")
end
| FStar_Parser_AST.NoName (t) -> begin
(

let uu____4479 = (

let uu____4480 = (unparen t)
in uu____4480.FStar_Parser_AST.tm)
in (match (uu____4479) with
| FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t1); FStar_Parser_AST.brange = uu____4482; FStar_Parser_AST.blevel = uu____4483; FStar_Parser_AST.aqual = uu____4484}, phi) -> begin
(match (is_atomic) with
| true -> begin
(

let uu____4486 = (

let uu____4487 = (

let uu____4488 = (p_refinement b.FStar_Parser_AST.aqual FStar_Pprint.underscore t1 phi)
in (FStar_Pprint.op_Hat_Hat uu____4488 FStar_Pprint.rparen))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4487))
in (FStar_Pprint.group uu____4486))
end
| uu____4489 -> begin
(

let uu____4490 = (p_refinement b.FStar_Parser_AST.aqual FStar_Pprint.underscore t1 phi)
in (FStar_Pprint.group uu____4490))
end)
end
| uu____4491 -> begin
(match (is_atomic) with
| true -> begin
(p_atomicTerm t)
end
| uu____4492 -> begin
(p_appTerm t)
end)
end))
end))
and p_refinement : FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Pprint.document  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun aqual_opt binder t phi -> (

let uu____4499 = (FStar_Pprint.optional p_aqual aqual_opt)
in (

let uu____4500 = (

let uu____4501 = (

let uu____4502 = (

let uu____4503 = (p_appTerm t)
in (

let uu____4504 = (

let uu____4505 = (p_noSeqTerm phi)
in (soft_braces_with_nesting uu____4505))
in (FStar_Pprint.op_Hat_Hat uu____4503 uu____4504)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4502))
in (FStar_Pprint.op_Hat_Hat binder uu____4501))
in (FStar_Pprint.op_Hat_Hat uu____4499 uu____4500))))
and p_binders : Prims.bool  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Pprint.document = (fun is_atomic bs -> (separate_map_or_flow break1 (p_binder is_atomic) bs))
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
| uu____4517 -> begin
(p_lident id)
end))
and p_term : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____4519 = (

let uu____4520 = (unparen e)
in uu____4520.FStar_Parser_AST.tm)
in (match (uu____4519) with
| FStar_Parser_AST.Seq (e1, e2) -> begin
(

let uu____4523 = (

let uu____4524 = (

let uu____4525 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat uu____4525 FStar_Pprint.semi))
in (FStar_Pprint.group uu____4524))
in (

let uu____4526 = (p_term e2)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4523 uu____4526)))
end
| FStar_Parser_AST.Bind (x, e1, e2) -> begin
(

let uu____4530 = (

let uu____4531 = (

let uu____4532 = (

let uu____4533 = (p_lident x)
in (

let uu____4534 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.long_left_arrow)
in (FStar_Pprint.op_Hat_Hat uu____4533 uu____4534)))
in (

let uu____4535 = (

let uu____4536 = (p_noSeqTerm e1)
in (

let uu____4537 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.semi)
in (FStar_Pprint.op_Hat_Hat uu____4536 uu____4537)))
in (op_Hat_Slash_Plus_Hat uu____4532 uu____4535)))
in (FStar_Pprint.group uu____4531))
in (

let uu____4538 = (p_term e2)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4530 uu____4538)))
end
| uu____4539 -> begin
(

let uu____4540 = (p_noSeqTerm e)
in (FStar_Pprint.group uu____4540))
end)))
and p_noSeqTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_noSeqTerm' e e.FStar_Parser_AST.range))
and p_noSeqTerm' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____4543 = (

let uu____4544 = (unparen e)
in uu____4544.FStar_Parser_AST.tm)
in (match (uu____4543) with
| FStar_Parser_AST.Ascribed (e1, t, FStar_Pervasives_Native.None) -> begin
(

let uu____4549 = (

let uu____4550 = (p_tmIff e1)
in (

let uu____4551 = (

let uu____4552 = (

let uu____4553 = (p_typ t)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4553))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4552))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4550 uu____4551)))
in (FStar_Pprint.group uu____4549))
end
| FStar_Parser_AST.Ascribed (e1, t, FStar_Pervasives_Native.Some (tac)) -> begin
(

let uu____4559 = (

let uu____4560 = (p_tmIff e1)
in (

let uu____4561 = (

let uu____4562 = (

let uu____4563 = (

let uu____4564 = (p_typ t)
in (

let uu____4565 = (

let uu____4566 = (str "by")
in (

let uu____4567 = (p_typ tac)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4566 uu____4567)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4564 uu____4565)))
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4563))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4562))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4560 uu____4561)))
in (FStar_Pprint.group uu____4559))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = ".()<-"; FStar_Ident.idRange = uu____4568}, (e1)::(e2)::(e3)::[]) -> begin
(

let uu____4574 = (

let uu____4575 = (

let uu____4576 = (

let uu____4577 = (p_atomicTermNotQUident e1)
in (

let uu____4578 = (

let uu____4579 = (

let uu____4580 = (

let uu____4581 = (p_term e2)
in (soft_parens_with_nesting uu____4581))
in (

let uu____4582 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat uu____4580 uu____4582)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4579))
in (FStar_Pprint.op_Hat_Hat uu____4577 uu____4578)))
in (FStar_Pprint.group uu____4576))
in (

let uu____4583 = (

let uu____4584 = (p_noSeqTerm e3)
in (jump2 uu____4584))
in (FStar_Pprint.op_Hat_Hat uu____4575 uu____4583)))
in (FStar_Pprint.group uu____4574))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = ".[]<-"; FStar_Ident.idRange = uu____4585}, (e1)::(e2)::(e3)::[]) -> begin
(

let uu____4591 = (

let uu____4592 = (

let uu____4593 = (

let uu____4594 = (p_atomicTermNotQUident e1)
in (

let uu____4595 = (

let uu____4596 = (

let uu____4597 = (

let uu____4598 = (p_term e2)
in (soft_brackets_with_nesting uu____4598))
in (

let uu____4599 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat uu____4597 uu____4599)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4596))
in (FStar_Pprint.op_Hat_Hat uu____4594 uu____4595)))
in (FStar_Pprint.group uu____4593))
in (

let uu____4600 = (

let uu____4601 = (p_noSeqTerm e3)
in (jump2 uu____4601))
in (FStar_Pprint.op_Hat_Hat uu____4592 uu____4600)))
in (FStar_Pprint.group uu____4591))
end
| FStar_Parser_AST.Requires (e1, wtf) -> begin
(

let uu____4611 = (

let uu____4612 = (str "requires")
in (

let uu____4613 = (p_typ e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4612 uu____4613)))
in (FStar_Pprint.group uu____4611))
end
| FStar_Parser_AST.Ensures (e1, wtf) -> begin
(

let uu____4623 = (

let uu____4624 = (str "ensures")
in (

let uu____4625 = (p_typ e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4624 uu____4625)))
in (FStar_Pprint.group uu____4623))
end
| FStar_Parser_AST.Attributes (es) -> begin
(

let uu____4629 = (

let uu____4630 = (str "attributes")
in (

let uu____4631 = (FStar_Pprint.separate_map break1 p_atomicTerm es)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4630 uu____4631)))
in (FStar_Pprint.group uu____4629))
end
| FStar_Parser_AST.If (e1, e2, e3) -> begin
(

let uu____4635 = (is_unit e3)
in (match (uu____4635) with
| true -> begin
(

let uu____4636 = (

let uu____4637 = (

let uu____4638 = (str "if")
in (

let uu____4639 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat uu____4638 uu____4639)))
in (

let uu____4640 = (

let uu____4641 = (str "then")
in (

let uu____4642 = (p_noSeqTerm e2)
in (op_Hat_Slash_Plus_Hat uu____4641 uu____4642)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4637 uu____4640)))
in (FStar_Pprint.group uu____4636))
end
| uu____4643 -> begin
(

let e2_doc = (

let uu____4645 = (

let uu____4646 = (unparen e2)
in uu____4646.FStar_Parser_AST.tm)
in (match (uu____4645) with
| FStar_Parser_AST.If (uu____4647, uu____4648, e31) when (is_unit e31) -> begin
(

let uu____4650 = (p_noSeqTerm e2)
in (soft_parens_with_nesting uu____4650))
end
| uu____4651 -> begin
(p_noSeqTerm e2)
end))
in (

let uu____4652 = (

let uu____4653 = (

let uu____4654 = (str "if")
in (

let uu____4655 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat uu____4654 uu____4655)))
in (

let uu____4656 = (

let uu____4657 = (

let uu____4658 = (str "then")
in (op_Hat_Slash_Plus_Hat uu____4658 e2_doc))
in (

let uu____4659 = (

let uu____4660 = (str "else")
in (

let uu____4661 = (p_noSeqTerm e3)
in (op_Hat_Slash_Plus_Hat uu____4660 uu____4661)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4657 uu____4659)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4653 uu____4656)))
in (FStar_Pprint.group uu____4652)))
end))
end
| FStar_Parser_AST.TryWith (e1, branches) -> begin
(

let uu____4684 = (

let uu____4685 = (

let uu____4686 = (str "try")
in (

let uu____4687 = (p_noSeqTerm e1)
in (prefix2 uu____4686 uu____4687)))
in (

let uu____4688 = (

let uu____4689 = (str "with")
in (

let uu____4690 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4689 uu____4690)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4685 uu____4688)))
in (FStar_Pprint.group uu____4684))
end
| FStar_Parser_AST.Match (e1, branches) -> begin
(

let uu____4721 = (

let uu____4722 = (

let uu____4723 = (str "match")
in (

let uu____4724 = (p_noSeqTerm e1)
in (

let uu____4725 = (str "with")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____4723 uu____4724 uu____4725))))
in (

let uu____4726 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4722 uu____4726)))
in (FStar_Pprint.group uu____4721))
end
| FStar_Parser_AST.LetOpen (uid, e1) -> begin
(

let uu____4737 = (

let uu____4738 = (

let uu____4739 = (str "let open")
in (

let uu____4740 = (p_quident uid)
in (

let uu____4741 = (str "in")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____4739 uu____4740 uu____4741))))
in (

let uu____4742 = (p_term e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4738 uu____4742)))
in (FStar_Pprint.group uu____4737))
end
| FStar_Parser_AST.Let (q, lbs, e1) -> begin
(

let let_doc = (

let uu____4759 = (str "let")
in (

let uu____4760 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat uu____4759 uu____4760)))
in (

let uu____4761 = (

let uu____4762 = (

let uu____4763 = (

let uu____4764 = (str "and")
in (precede_break_separate_map let_doc uu____4764 p_letbinding lbs))
in (

let uu____4769 = (str "in")
in (FStar_Pprint.op_Hat_Slash_Hat uu____4763 uu____4769)))
in (FStar_Pprint.group uu____4762))
in (

let uu____4770 = (p_term e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4761 uu____4770))))
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, typ_opt); FStar_Parser_AST.prange = uu____4773})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, branches); FStar_Parser_AST.range = uu____4776; FStar_Parser_AST.level = uu____4777}) when (matches_var maybe_x x) -> begin
(

let uu____4804 = (

let uu____4805 = (str "function")
in (

let uu____4806 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4805 uu____4806)))
in (FStar_Pprint.group uu____4804))
end
| FStar_Parser_AST.Assign (id, e1) -> begin
(

let uu____4817 = (

let uu____4818 = (p_lident id)
in (

let uu____4819 = (

let uu____4820 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow uu____4820))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4818 uu____4819)))
in (FStar_Pprint.group uu____4817))
end
| uu____4821 -> begin
(p_typ e)
end)))
and p_typ : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_typ' e e.FStar_Parser_AST.range))
and p_typ' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____4824 = (

let uu____4825 = (unparen e)
in uu____4825.FStar_Parser_AST.tm)
in (match (uu____4824) with
| FStar_Parser_AST.QForall (bs, trigger, e1) -> begin
(

let uu____4841 = (

let uu____4842 = (

let uu____4843 = (p_quantifier e)
in (FStar_Pprint.op_Hat_Hat uu____4843 FStar_Pprint.space))
in (

let uu____4844 = (p_binders true bs)
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") uu____4842 uu____4844 FStar_Pprint.dot)))
in (

let uu____4845 = (

let uu____4846 = (p_trigger trigger)
in (

let uu____4847 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat uu____4846 uu____4847)))
in (prefix2 uu____4841 uu____4845)))
end
| FStar_Parser_AST.QExists (bs, trigger, e1) -> begin
(

let uu____4863 = (

let uu____4864 = (

let uu____4865 = (p_quantifier e)
in (FStar_Pprint.op_Hat_Hat uu____4865 FStar_Pprint.space))
in (

let uu____4866 = (p_binders true bs)
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") uu____4864 uu____4866 FStar_Pprint.dot)))
in (

let uu____4867 = (

let uu____4868 = (p_trigger trigger)
in (

let uu____4869 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat uu____4868 uu____4869)))
in (prefix2 uu____4863 uu____4867)))
end
| uu____4870 -> begin
(p_simpleTerm e)
end)))
and p_quantifier : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____4872 = (

let uu____4873 = (unparen e)
in uu____4873.FStar_Parser_AST.tm)
in (match (uu____4872) with
| FStar_Parser_AST.QForall (uu____4874) -> begin
(str "forall")
end
| FStar_Parser_AST.QExists (uu____4887) -> begin
(str "exists")
end
| uu____4900 -> begin
(failwith "Imposible : p_quantifier called on a non-quantifier term")
end)))
and p_trigger : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun uu___100_4901 -> (match (uu___100_4901) with
| [] -> begin
FStar_Pprint.empty
end
| pats -> begin
(

let uu____4913 = (

let uu____4914 = (

let uu____4915 = (str "pattern")
in (

let uu____4916 = (

let uu____4917 = (

let uu____4918 = (p_disjunctivePats pats)
in (jump2 uu____4918))
in (

let uu____4919 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4917 uu____4919)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4915 uu____4916)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4914))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____4913))
end))
and p_disjunctivePats : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun pats -> (

let uu____4925 = (str "\\/")
in (FStar_Pprint.separate_map uu____4925 p_conjunctivePats pats)))
and p_conjunctivePats : FStar_Parser_AST.term Prims.list  ->  FStar_Pprint.document = (fun pats -> (

let uu____4931 = (FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats)
in (FStar_Pprint.group uu____4931)))
and p_simpleTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____4933 = (

let uu____4934 = (unparen e)
in uu____4934.FStar_Parser_AST.tm)
in (match (uu____4933) with
| FStar_Parser_AST.Abs (pats, e1) -> begin
(

let uu____4941 = (

let uu____4942 = (str "fun")
in (

let uu____4943 = (

let uu____4944 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4944 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat uu____4942 uu____4943)))
in (

let uu____4945 = (p_term e1)
in (op_Hat_Slash_Plus_Hat uu____4941 uu____4945)))
end
| uu____4946 -> begin
(p_tmIff e)
end)))
and p_maybeFocusArrow : Prims.bool  ->  FStar_Pprint.document = (fun b -> (match (b) with
| true -> begin
(str "~>")
end
| uu____4948 -> begin
FStar_Pprint.rarrow
end))
and p_patternBranch : (FStar_Parser_AST.pattern * FStar_Parser_AST.term FStar_Pervasives_Native.option * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun uu____4949 -> (match (uu____4949) with
| (pat, when_opt, e) -> begin
(

let maybe_paren = (

let uu____4968 = (

let uu____4969 = (unparen e)
in uu____4969.FStar_Parser_AST.tm)
in (match (uu____4968) with
| FStar_Parser_AST.Match (uu____4972) -> begin
soft_begin_end_with_nesting
end
| FStar_Parser_AST.TryWith (uu____4987) -> begin
soft_begin_end_with_nesting
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____5003); FStar_Parser_AST.prange = uu____5004})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, uu____5006); FStar_Parser_AST.range = uu____5007; FStar_Parser_AST.level = uu____5008}) when (matches_var maybe_x x) -> begin
soft_begin_end_with_nesting
end
| uu____5035 -> begin
(fun x -> x)
end))
in (

let uu____5037 = (

let uu____5038 = (

let uu____5039 = (

let uu____5040 = (

let uu____5041 = (

let uu____5042 = (p_disjunctivePattern pat)
in (

let uu____5043 = (

let uu____5044 = (p_maybeWhen when_opt)
in (FStar_Pprint.op_Hat_Hat uu____5044 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat uu____5042 uu____5043)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5041))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5040))
in (FStar_Pprint.group uu____5039))
in (

let uu____5045 = (

let uu____5046 = (p_term e)
in (maybe_paren uu____5046))
in (op_Hat_Slash_Plus_Hat uu____5038 uu____5045)))
in (FStar_Pprint.group uu____5037)))
end))
and p_maybeWhen : FStar_Parser_AST.term FStar_Pervasives_Native.option  ->  FStar_Pprint.document = (fun uu___101_5047 -> (match (uu___101_5047) with
| FStar_Pervasives_Native.None -> begin
FStar_Pprint.empty
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____5051 = (str "when")
in (

let uu____5052 = (

let uu____5053 = (p_tmFormula e)
in (FStar_Pprint.op_Hat_Hat uu____5053 FStar_Pprint.space))
in (op_Hat_Slash_Plus_Hat uu____5051 uu____5052)))
end))
and p_tmIff : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____5055 = (

let uu____5056 = (unparen e)
in uu____5056.FStar_Parser_AST.tm)
in (match (uu____5055) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5057}, (e1)::(e2)::[]) -> begin
(

let uu____5062 = (str "<==>")
in (

let uu____5063 = (p_tmImplies e1)
in (

let uu____5064 = (p_tmIff e2)
in (infix0 uu____5062 uu____5063 uu____5064))))
end
| uu____5065 -> begin
(p_tmImplies e)
end)))
and p_tmImplies : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____5067 = (

let uu____5068 = (unparen e)
in uu____5068.FStar_Parser_AST.tm)
in (match (uu____5067) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5069}, (e1)::(e2)::[]) -> begin
(

let uu____5074 = (str "==>")
in (

let uu____5075 = (p_tmArrow p_tmFormula e1)
in (

let uu____5076 = (p_tmImplies e2)
in (infix0 uu____5074 uu____5075 uu____5076))))
end
| uu____5077 -> begin
(p_tmArrow p_tmFormula e)
end)))
and p_tmArrow : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_Tm e -> (

let uu____5082 = (

let uu____5083 = (unparen e)
in uu____5083.FStar_Parser_AST.tm)
in (match (uu____5082) with
| FStar_Parser_AST.Product (bs, tgt) -> begin
(

let uu____5090 = (

let uu____5091 = (separate_map_or_flow FStar_Pprint.empty (fun b -> (

let uu____5096 = (p_binder false b)
in (

let uu____5097 = (

let uu____5098 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5098))
in (FStar_Pprint.op_Hat_Hat uu____5096 uu____5097)))) bs)
in (

let uu____5099 = (p_tmArrow p_Tm tgt)
in (FStar_Pprint.op_Hat_Hat uu____5091 uu____5099)))
in (FStar_Pprint.group uu____5090))
end
| uu____5100 -> begin
(p_Tm e)
end)))
and p_tmFormula : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____5102 = (

let uu____5103 = (unparen e)
in uu____5103.FStar_Parser_AST.tm)
in (match (uu____5102) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5104}, (e1)::(e2)::[]) -> begin
(

let uu____5109 = (str "\\/")
in (

let uu____5110 = (p_tmFormula e1)
in (

let uu____5111 = (p_tmConjunction e2)
in (infix0 uu____5109 uu____5110 uu____5111))))
end
| uu____5112 -> begin
(p_tmConjunction e)
end)))
and p_tmConjunction : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____5114 = (

let uu____5115 = (unparen e)
in uu____5115.FStar_Parser_AST.tm)
in (match (uu____5114) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5116}, (e1)::(e2)::[]) -> begin
(

let uu____5121 = (str "/\\")
in (

let uu____5122 = (p_tmConjunction e1)
in (

let uu____5123 = (p_tmTuple e2)
in (infix0 uu____5121 uu____5122 uu____5123))))
end
| uu____5124 -> begin
(p_tmTuple e)
end)))
and p_tmTuple : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_tmTuple' e e.FStar_Parser_AST.range))
and p_tmTuple' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____5127 = (

let uu____5128 = (unparen e)
in uu____5128.FStar_Parser_AST.tm)
in (match (uu____5127) with
| FStar_Parser_AST.Construct (lid, args) when (is_tuple_constructor lid) -> begin
(

let uu____5143 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map uu____5143 (fun uu____5151 -> (match (uu____5151) with
| (e1, uu____5157) -> begin
(p_tmEq e1)
end)) args))
end
| uu____5158 -> begin
(p_tmEq e)
end)))
and paren_if : Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun curr mine doc1 -> (match ((mine <= curr)) with
| true -> begin
doc1
end
| uu____5162 -> begin
(

let uu____5163 = (

let uu____5164 = (FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5164))
in (FStar_Pprint.group uu____5163))
end))
and p_tmEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n1 = (max_level (FStar_List.append (((colon_equals ()))::((pipe_right ()))::[]) (operatorInfix0ad12 ())))
in (p_tmEq' n1 e)))
and p_tmEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (

let uu____5209 = (

let uu____5210 = (unparen e)
in uu____5210.FStar_Parser_AST.tm)
in (match (uu____5209) with
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (((is_operatorInfix0ad12 op) || (Prims.op_Equality (FStar_Ident.text_of_id op) "=")) || (Prims.op_Equality (FStar_Ident.text_of_id op) "|>")) -> begin
(

let op1 = (FStar_Ident.text_of_id op)
in (

let uu____5217 = (levels op1)
in (match (uu____5217) with
| (left1, mine, right1) -> begin
(

let uu____5227 = (

let uu____5228 = (FStar_All.pipe_left str op1)
in (

let uu____5229 = (p_tmEq' left1 e1)
in (

let uu____5230 = (p_tmEq' right1 e2)
in (infix0 uu____5228 uu____5229 uu____5230))))
in (paren_if curr mine uu____5227))
end)))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5231}, (e1)::(e2)::[]) -> begin
(

let uu____5236 = (

let uu____5237 = (p_tmEq e1)
in (

let uu____5238 = (

let uu____5239 = (

let uu____5240 = (

let uu____5241 = (p_tmEq e2)
in (op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5241))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5240))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5239))
in (FStar_Pprint.op_Hat_Hat uu____5237 uu____5238)))
in (FStar_Pprint.group uu____5236))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5242}, (e1)::[]) -> begin
(

let uu____5246 = (levels "-")
in (match (uu____5246) with
| (left1, mine, right1) -> begin
(

let uu____5256 = (p_tmEq' mine e1)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5256))
end))
end
| uu____5257 -> begin
(p_tmNoEq e)
end)))
and p_tmNoEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n1 = (max_level (((colon_colon ()))::((amp ()))::((opinfix3 ()))::((opinfix4 ()))::[]))
in (p_tmNoEq' n1 e)))
and p_tmNoEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (

let uu____5312 = (

let uu____5313 = (unparen e)
in uu____5313.FStar_Parser_AST.tm)
in (match (uu____5312) with
| FStar_Parser_AST.Construct (lid, ((e1, uu____5316))::((e2, uu____5318))::[]) when ((FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) && (

let uu____5338 = (is_list e)
in (not (uu____5338)))) -> begin
(

let op = "::"
in (

let uu____5340 = (levels op)
in (match (uu____5340) with
| (left1, mine, right1) -> begin
(

let uu____5350 = (

let uu____5351 = (str op)
in (

let uu____5352 = (p_tmNoEq' left1 e1)
in (

let uu____5353 = (p_tmNoEq' right1 e2)
in (infix0 uu____5351 uu____5352 uu____5353))))
in (paren_if curr mine uu____5350))
end)))
end
| FStar_Parser_AST.Sum (binders, res) -> begin
(

let op = "&"
in (

let uu____5361 = (levels op)
in (match (uu____5361) with
| (left1, mine, right1) -> begin
(

let p_dsumfst = (fun b -> (

let uu____5375 = (p_binder false b)
in (

let uu____5376 = (

let uu____5377 = (

let uu____5378 = (str op)
in (FStar_Pprint.op_Hat_Hat uu____5378 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5377))
in (FStar_Pprint.op_Hat_Hat uu____5375 uu____5376))))
in (

let uu____5379 = (

let uu____5380 = (FStar_Pprint.concat_map p_dsumfst binders)
in (

let uu____5381 = (p_tmNoEq' right1 res)
in (FStar_Pprint.op_Hat_Hat uu____5380 uu____5381)))
in (paren_if curr mine uu____5379)))
end)))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (is_operatorInfix34 op) -> begin
(

let op1 = (FStar_Ident.text_of_id op)
in (

let uu____5388 = (levels op1)
in (match (uu____5388) with
| (left1, mine, right1) -> begin
(

let uu____5398 = (

let uu____5399 = (str op1)
in (

let uu____5400 = (p_tmNoEq' left1 e1)
in (

let uu____5401 = (p_tmNoEq' right1 e2)
in (infix0 uu____5399 uu____5400 uu____5401))))
in (paren_if curr mine uu____5398))
end)))
end
| FStar_Parser_AST.NamedTyp (lid, e1) -> begin
(

let uu____5404 = (

let uu____5405 = (p_lidentOrUnderscore lid)
in (

let uu____5406 = (

let uu____5407 = (p_appTerm e1)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5407))
in (FStar_Pprint.op_Hat_Slash_Hat uu____5405 uu____5406)))
in (FStar_Pprint.group uu____5404))
end
| FStar_Parser_AST.Refine (b, phi) -> begin
(p_refinedBinder b phi)
end
| FStar_Parser_AST.Record (with_opt, record_fields) -> begin
(

let uu____5428 = (

let uu____5429 = (default_or_map FStar_Pprint.empty p_with_clause with_opt)
in (

let uu____5430 = (

let uu____5431 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (FStar_Pprint.separate_map uu____5431 p_simpleDef record_fields))
in (FStar_Pprint.op_Hat_Hat uu____5429 uu____5430)))
in (braces_with_nesting uu____5428))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____5436}, (e1)::[]) -> begin
(

let uu____5440 = (

let uu____5441 = (str "~")
in (

let uu____5442 = (p_atomicTerm e1)
in (FStar_Pprint.op_Hat_Hat uu____5441 uu____5442)))
in (FStar_Pprint.group uu____5440))
end
| uu____5443 -> begin
(p_appTerm e)
end)))
and p_with_clause : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____5445 = (p_appTerm e)
in (

let uu____5446 = (

let uu____5447 = (

let uu____5448 = (str "with")
in (FStar_Pprint.op_Hat_Hat uu____5448 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5447))
in (FStar_Pprint.op_Hat_Hat uu____5445 uu____5446))))
and p_refinedBinder : FStar_Parser_AST.binder  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun b phi -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (lid, t) -> begin
(

let uu____5453 = (

let uu____5454 = (p_lident lid)
in (p_refinement b.FStar_Parser_AST.aqual uu____5454 t phi))
in (soft_parens_with_nesting uu____5453))
end
| FStar_Parser_AST.TAnnotated (uu____5455) -> begin
(failwith "Is this still used ?")
end
| FStar_Parser_AST.Variable (uu____5460) -> begin
(

let uu____5461 = (

let uu____5462 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" uu____5462))
in (failwith uu____5461))
end
| FStar_Parser_AST.TVariable (uu____5463) -> begin
(

let uu____5464 = (

let uu____5465 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" uu____5465))
in (failwith uu____5464))
end
| FStar_Parser_AST.NoName (uu____5466) -> begin
(

let uu____5467 = (

let uu____5468 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" uu____5468))
in (failwith uu____5467))
end))
and p_simpleDef : (FStar_Ident.lid * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun uu____5469 -> (match (uu____5469) with
| (lid, e) -> begin
(

let uu____5476 = (

let uu____5477 = (p_qlident lid)
in (

let uu____5478 = (

let uu____5479 = (p_tmIff e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____5479))
in (FStar_Pprint.op_Hat_Slash_Hat uu____5477 uu____5478)))
in (FStar_Pprint.group uu____5476))
end))
and p_appTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____5481 = (

let uu____5482 = (unparen e)
in uu____5482.FStar_Parser_AST.tm)
in (match (uu____5481) with
| FStar_Parser_AST.App (uu____5483) when (is_general_application e) -> begin
(

let uu____5490 = (head_and_args e)
in (match (uu____5490) with
| (head1, args) -> begin
(

let uu____5515 = (

let uu____5526 = (FStar_ST.op_Bang should_print_fs_typ_app)
in (match (uu____5526) with
| true -> begin
(

let uu____5583 = (FStar_Util.take (fun uu____5607 -> (match (uu____5607) with
| (uu____5612, aq) -> begin
(Prims.op_Equality aq FStar_Parser_AST.FsTypApp)
end)) args)
in (match (uu____5583) with
| (fs_typ_args, args1) -> begin
(

let uu____5650 = (

let uu____5651 = (p_indexingTerm head1)
in (

let uu____5652 = (

let uu____5653 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (soft_surround_map_or_flow (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.empty FStar_Pprint.langle uu____5653 FStar_Pprint.rangle p_fsTypArg fs_typ_args))
in (FStar_Pprint.op_Hat_Hat uu____5651 uu____5652)))
in ((uu____5650), (args1)))
end))
end
| uu____5664 -> begin
(

let uu____5665 = (p_indexingTerm head1)
in ((uu____5665), (args)))
end))
in (match (uu____5515) with
| (head_doc, args1) -> begin
(

let uu____5686 = (

let uu____5687 = (FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space)
in (soft_surround_map_or_flow (Prims.parse_int "2") (Prims.parse_int "0") head_doc uu____5687 break1 FStar_Pprint.empty p_argTerm args1))
in (FStar_Pprint.group uu____5686))
end))
end))
end
| FStar_Parser_AST.Construct (lid, args) when ((is_general_construction e) && (

let uu____5707 = (is_dtuple_constructor lid)
in (not (uu____5707)))) -> begin
(match (args) with
| [] -> begin
(p_quident lid)
end
| (arg)::[] -> begin
(

let uu____5725 = (

let uu____5726 = (p_quident lid)
in (

let uu____5727 = (p_argTerm arg)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5726 uu____5727)))
in (FStar_Pprint.group uu____5725))
end
| (hd1)::tl1 -> begin
(

let uu____5744 = (

let uu____5745 = (

let uu____5746 = (

let uu____5747 = (p_quident lid)
in (

let uu____5748 = (p_argTerm hd1)
in (prefix2 uu____5747 uu____5748)))
in (FStar_Pprint.group uu____5746))
in (

let uu____5749 = (

let uu____5750 = (FStar_Pprint.separate_map break1 p_argTerm tl1)
in (jump2 uu____5750))
in (FStar_Pprint.op_Hat_Hat uu____5745 uu____5749)))
in (FStar_Pprint.group uu____5744))
end)
end
| uu____5755 -> begin
(p_indexingTerm e)
end)))
and p_argTerm : (FStar_Parser_AST.term * FStar_Parser_AST.imp)  ->  FStar_Pprint.document = (fun arg_imp -> (match (arg_imp) with
| (u, FStar_Parser_AST.UnivApp) -> begin
(p_universe u)
end
| (e, FStar_Parser_AST.FsTypApp) -> begin
((FStar_Util.print_warning "Unexpected FsTypApp, output might not be formatted correctly.\n");
(

let uu____5764 = (p_indexingTerm e)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.langle uu____5764 FStar_Pprint.rangle));
)
end
| (e, FStar_Parser_AST.Hash) -> begin
(

let uu____5766 = (str "#")
in (

let uu____5767 = (p_indexingTerm e)
in (FStar_Pprint.op_Hat_Hat uu____5766 uu____5767)))
end
| (e, FStar_Parser_AST.Nothing) -> begin
(p_indexingTerm e)
end))
and p_fsTypArg : (FStar_Parser_AST.term * FStar_Parser_AST.imp)  ->  FStar_Pprint.document = (fun uu____5769 -> (match (uu____5769) with
| (e, uu____5775) -> begin
(p_indexingTerm e)
end))
and p_indexingTerm_aux : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun exit1 e -> (

let uu____5780 = (

let uu____5781 = (unparen e)
in uu____5781.FStar_Parser_AST.tm)
in (match (uu____5780) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____5782}, (e1)::(e2)::[]) -> begin
(

let uu____5787 = (

let uu____5788 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (

let uu____5789 = (

let uu____5790 = (

let uu____5791 = (p_term e2)
in (soft_parens_with_nesting uu____5791))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5790))
in (FStar_Pprint.op_Hat_Hat uu____5788 uu____5789)))
in (FStar_Pprint.group uu____5787))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____5792}, (e1)::(e2)::[]) -> begin
(

let uu____5797 = (

let uu____5798 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (

let uu____5799 = (

let uu____5800 = (

let uu____5801 = (p_term e2)
in (soft_brackets_with_nesting uu____5801))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5800))
in (FStar_Pprint.op_Hat_Hat uu____5798 uu____5799)))
in (FStar_Pprint.group uu____5797))
end
| uu____5802 -> begin
(exit1 e)
end)))
and p_indexingTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_indexingTerm_aux p_atomicTerm e))
and p_atomicTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____5805 = (

let uu____5806 = (unparen e)
in uu____5806.FStar_Parser_AST.tm)
in (match (uu____5805) with
| FStar_Parser_AST.LetOpen (lid, e1) -> begin
(

let uu____5809 = (p_quident lid)
in (

let uu____5810 = (

let uu____5811 = (

let uu____5812 = (p_term e1)
in (soft_parens_with_nesting uu____5812))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5811))
in (FStar_Pprint.op_Hat_Hat uu____5809 uu____5810)))
end
| FStar_Parser_AST.Name (lid) -> begin
(p_quident lid)
end
| FStar_Parser_AST.Op (op, (e1)::[]) when (is_general_prefix_op op) -> begin
(

let uu____5818 = (str (FStar_Ident.text_of_id op))
in (

let uu____5819 = (p_atomicTerm e1)
in (FStar_Pprint.op_Hat_Hat uu____5818 uu____5819)))
end
| uu____5820 -> begin
(p_atomicTermNotQUident e)
end)))
and p_atomicTermNotQUident : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____5822 = (

let uu____5823 = (unparen e)
in uu____5823.FStar_Parser_AST.tm)
in (match (uu____5822) with
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
| FStar_Const.Const_char (x) when (Prims.op_Equality x 10) -> begin
(str "0x0Az")
end
| uu____5828 -> begin
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

let uu____5835 = (str (FStar_Ident.text_of_id op))
in (

let uu____5836 = (p_atomicTermNotQUident e1)
in (FStar_Pprint.op_Hat_Hat uu____5835 uu____5836)))
end
| FStar_Parser_AST.Op (op, []) -> begin
(

let uu____5840 = (

let uu____5841 = (

let uu____5842 = (str (FStar_Ident.text_of_id op))
in (

let uu____5843 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat uu____5842 uu____5843)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5841))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5840))
end
| FStar_Parser_AST.Construct (lid, args) when (is_dtuple_constructor lid) -> begin
(

let uu____5858 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (

let uu____5859 = (

let uu____5860 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (

let uu____5861 = (FStar_List.map FStar_Pervasives_Native.fst args)
in (FStar_Pprint.separate_map uu____5860 p_tmEq uu____5861)))
in (

let uu____5868 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____5858 uu____5859 uu____5868))))
end
| FStar_Parser_AST.Project (e1, lid) -> begin
(

let uu____5871 = (

let uu____5872 = (p_atomicTermNotQUident e1)
in (

let uu____5873 = (

let uu____5874 = (p_qlident lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5874))
in (FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0") uu____5872 uu____5873)))
in (FStar_Pprint.group uu____5871))
end
| uu____5875 -> begin
(p_projectionLHS e)
end)))
and p_projectionLHS : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____5877 = (

let uu____5878 = (unparen e)
in uu____5878.FStar_Parser_AST.tm)
in (match (uu____5877) with
| FStar_Parser_AST.Var (lid) -> begin
(p_qlident lid)
end
| FStar_Parser_AST.Projector (constr_lid, field_lid) -> begin
(

let uu____5882 = (p_quident constr_lid)
in (

let uu____5883 = (

let uu____5884 = (

let uu____5885 = (p_lident field_lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5885))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____5884))
in (FStar_Pprint.op_Hat_Hat uu____5882 uu____5883)))
end
| FStar_Parser_AST.Discrim (constr_lid) -> begin
(

let uu____5887 = (p_quident constr_lid)
in (FStar_Pprint.op_Hat_Hat uu____5887 FStar_Pprint.qmark))
end
| FStar_Parser_AST.Paren (e1) -> begin
(

let uu____5889 = (p_term e1)
in (soft_parens_with_nesting uu____5889))
end
| uu____5890 when (is_array e) -> begin
(

let es = (extract_from_list e)
in (

let uu____5894 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar)
in (

let uu____5895 = (

let uu____5896 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (separate_map_or_flow uu____5896 p_noSeqTerm es))
in (

let uu____5897 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") uu____5894 uu____5895 uu____5897)))))
end
| uu____5898 when (is_list e) -> begin
(

let uu____5899 = (

let uu____5900 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (

let uu____5901 = (extract_from_list e)
in (separate_map_or_flow uu____5900 p_noSeqTerm uu____5901)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket uu____5899 FStar_Pprint.rbracket))
end
| uu____5904 when (is_lex_list e) -> begin
(

let uu____5905 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket)
in (

let uu____5906 = (

let uu____5907 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (

let uu____5908 = (extract_from_list e)
in (separate_map_or_flow uu____5907 p_noSeqTerm uu____5908)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____5905 uu____5906 FStar_Pprint.rbracket)))
end
| uu____5911 when (is_ref_set e) -> begin
(

let es = (extract_from_ref_set e)
in (

let uu____5915 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace)
in (

let uu____5916 = (

let uu____5917 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (separate_map_or_flow uu____5917 p_appTerm es))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") uu____5915 uu____5916 FStar_Pprint.rbrace))))
end
| FStar_Parser_AST.Labeled (e1, s, b) -> begin
(

let uu____5921 = (str (Prims.strcat "(*" (Prims.strcat s "*)")))
in (

let uu____5922 = (p_term e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5921 uu____5922)))
end
| FStar_Parser_AST.Op (op, args) when (

let uu____5929 = (handleable_op op args)
in (not (uu____5929))) -> begin
(

let uu____5930 = (

let uu____5931 = (

let uu____5932 = (

let uu____5933 = (

let uu____5934 = (FStar_Util.string_of_int (FStar_List.length args))
in (Prims.strcat uu____5934 " arguments couldn\'t be handled by the pretty printer"))
in (Prims.strcat " with " uu____5933))
in (Prims.strcat (FStar_Ident.text_of_id op) uu____5932))
in (Prims.strcat "Operation " uu____5931))
in (failwith uu____5930))
end
| FStar_Parser_AST.Uvar (uu____5935) -> begin
(failwith "Unexpected universe variable out of universe context")
end
| FStar_Parser_AST.Wild -> begin
(

let uu____5936 = (p_term e)
in (soft_parens_with_nesting uu____5936))
end
| FStar_Parser_AST.Const (uu____5937) -> begin
(

let uu____5938 = (p_term e)
in (soft_parens_with_nesting uu____5938))
end
| FStar_Parser_AST.Op (uu____5939) -> begin
(

let uu____5946 = (p_term e)
in (soft_parens_with_nesting uu____5946))
end
| FStar_Parser_AST.Tvar (uu____5947) -> begin
(

let uu____5948 = (p_term e)
in (soft_parens_with_nesting uu____5948))
end
| FStar_Parser_AST.Var (uu____5949) -> begin
(

let uu____5950 = (p_term e)
in (soft_parens_with_nesting uu____5950))
end
| FStar_Parser_AST.Name (uu____5951) -> begin
(

let uu____5952 = (p_term e)
in (soft_parens_with_nesting uu____5952))
end
| FStar_Parser_AST.Construct (uu____5953) -> begin
(

let uu____5964 = (p_term e)
in (soft_parens_with_nesting uu____5964))
end
| FStar_Parser_AST.Abs (uu____5965) -> begin
(

let uu____5972 = (p_term e)
in (soft_parens_with_nesting uu____5972))
end
| FStar_Parser_AST.App (uu____5973) -> begin
(

let uu____5980 = (p_term e)
in (soft_parens_with_nesting uu____5980))
end
| FStar_Parser_AST.Let (uu____5981) -> begin
(

let uu____5994 = (p_term e)
in (soft_parens_with_nesting uu____5994))
end
| FStar_Parser_AST.LetOpen (uu____5995) -> begin
(

let uu____6000 = (p_term e)
in (soft_parens_with_nesting uu____6000))
end
| FStar_Parser_AST.Seq (uu____6001) -> begin
(

let uu____6006 = (p_term e)
in (soft_parens_with_nesting uu____6006))
end
| FStar_Parser_AST.Bind (uu____6007) -> begin
(

let uu____6014 = (p_term e)
in (soft_parens_with_nesting uu____6014))
end
| FStar_Parser_AST.If (uu____6015) -> begin
(

let uu____6022 = (p_term e)
in (soft_parens_with_nesting uu____6022))
end
| FStar_Parser_AST.Match (uu____6023) -> begin
(

let uu____6038 = (p_term e)
in (soft_parens_with_nesting uu____6038))
end
| FStar_Parser_AST.TryWith (uu____6039) -> begin
(

let uu____6054 = (p_term e)
in (soft_parens_with_nesting uu____6054))
end
| FStar_Parser_AST.Ascribed (uu____6055) -> begin
(

let uu____6064 = (p_term e)
in (soft_parens_with_nesting uu____6064))
end
| FStar_Parser_AST.Record (uu____6065) -> begin
(

let uu____6078 = (p_term e)
in (soft_parens_with_nesting uu____6078))
end
| FStar_Parser_AST.Project (uu____6079) -> begin
(

let uu____6084 = (p_term e)
in (soft_parens_with_nesting uu____6084))
end
| FStar_Parser_AST.Product (uu____6085) -> begin
(

let uu____6092 = (p_term e)
in (soft_parens_with_nesting uu____6092))
end
| FStar_Parser_AST.Sum (uu____6093) -> begin
(

let uu____6100 = (p_term e)
in (soft_parens_with_nesting uu____6100))
end
| FStar_Parser_AST.QForall (uu____6101) -> begin
(

let uu____6114 = (p_term e)
in (soft_parens_with_nesting uu____6114))
end
| FStar_Parser_AST.QExists (uu____6115) -> begin
(

let uu____6128 = (p_term e)
in (soft_parens_with_nesting uu____6128))
end
| FStar_Parser_AST.Refine (uu____6129) -> begin
(

let uu____6134 = (p_term e)
in (soft_parens_with_nesting uu____6134))
end
| FStar_Parser_AST.NamedTyp (uu____6135) -> begin
(

let uu____6140 = (p_term e)
in (soft_parens_with_nesting uu____6140))
end
| FStar_Parser_AST.Requires (uu____6141) -> begin
(

let uu____6148 = (p_term e)
in (soft_parens_with_nesting uu____6148))
end
| FStar_Parser_AST.Ensures (uu____6149) -> begin
(

let uu____6156 = (p_term e)
in (soft_parens_with_nesting uu____6156))
end
| FStar_Parser_AST.Assign (uu____6157) -> begin
(

let uu____6162 = (p_term e)
in (soft_parens_with_nesting uu____6162))
end
| FStar_Parser_AST.Attributes (uu____6163) -> begin
(

let uu____6166 = (p_term e)
in (soft_parens_with_nesting uu____6166))
end)))
and p_constant : FStar_Const.sconst  ->  FStar_Pprint.document = (fun uu___104_6167 -> (match (uu___104_6167) with
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

let uu____6171 = (FStar_Pprint.doc_of_char x)
in (FStar_Pprint.squotes uu____6171))
end
| FStar_Const.Const_string (s, uu____6173) -> begin
(

let uu____6174 = (str s)
in (FStar_Pprint.dquotes uu____6174))
end
| FStar_Const.Const_bytearray (bytes, uu____6176) -> begin
(

let uu____6181 = (

let uu____6182 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes uu____6182))
in (

let uu____6183 = (str "B")
in (FStar_Pprint.op_Hat_Hat uu____6181 uu____6183)))
end
| FStar_Const.Const_int (repr, sign_width_opt) -> begin
(

let signedness = (fun uu___102_6201 -> (match (uu___102_6201) with
| FStar_Const.Unsigned -> begin
(str "u")
end
| FStar_Const.Signed -> begin
FStar_Pprint.empty
end))
in (

let width = (fun uu___103_6205 -> (match (uu___103_6205) with
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

let ending = (default_or_map FStar_Pprint.empty (fun uu____6216 -> (match (uu____6216) with
| (s, w) -> begin
(

let uu____6223 = (signedness s)
in (

let uu____6224 = (width w)
in (FStar_Pprint.op_Hat_Hat uu____6223 uu____6224)))
end)) sign_width_opt)
in (

let uu____6225 = (str repr)
in (FStar_Pprint.op_Hat_Hat uu____6225 ending)))))
end
| FStar_Const.Const_range (r) -> begin
(

let uu____6227 = (FStar_Range.string_of_range r)
in (str uu____6227))
end
| FStar_Const.Const_reify -> begin
(str "reify")
end
| FStar_Const.Const_reflect (lid) -> begin
(

let uu____6229 = (p_quident lid)
in (

let uu____6230 = (

let uu____6231 = (

let uu____6232 = (str "reflect")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6232))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6231))
in (FStar_Pprint.op_Hat_Hat uu____6229 uu____6230)))
end))
and p_universe : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (

let uu____6234 = (str "u#")
in (

let uu____6235 = (p_atomicUniverse u)
in (FStar_Pprint.op_Hat_Hat uu____6234 uu____6235))))
and p_universeFrom : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (

let uu____6237 = (

let uu____6238 = (unparen u)
in uu____6238.FStar_Parser_AST.tm)
in (match (uu____6237) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6239}, (u1)::(u2)::[]) -> begin
(

let uu____6244 = (

let uu____6245 = (p_universeFrom u1)
in (

let uu____6246 = (

let uu____6247 = (p_universeFrom u2)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6247))
in (FStar_Pprint.op_Hat_Slash_Hat uu____6245 uu____6246)))
in (FStar_Pprint.group uu____6244))
end
| FStar_Parser_AST.App (uu____6248) -> begin
(

let uu____6255 = (head_and_args u)
in (match (uu____6255) with
| (head1, args) -> begin
(

let uu____6280 = (

let uu____6281 = (unparen head1)
in uu____6281.FStar_Parser_AST.tm)
in (match (uu____6280) with
| FStar_Parser_AST.Var (maybe_max_lid) when (FStar_Ident.lid_equals maybe_max_lid FStar_Parser_Const.max_lid) -> begin
(

let uu____6283 = (

let uu____6284 = (p_qlident FStar_Parser_Const.max_lid)
in (

let uu____6285 = (FStar_Pprint.separate_map FStar_Pprint.space (fun uu____6293 -> (match (uu____6293) with
| (u1, uu____6299) -> begin
(p_atomicUniverse u1)
end)) args)
in (op_Hat_Slash_Plus_Hat uu____6284 uu____6285)))
in (FStar_Pprint.group uu____6283))
end
| uu____6300 -> begin
(

let uu____6301 = (

let uu____6302 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" uu____6302))
in (failwith uu____6301))
end))
end))
end
| uu____6303 -> begin
(p_atomicUniverse u)
end)))
and p_atomicUniverse : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (

let uu____6305 = (

let uu____6306 = (unparen u)
in uu____6306.FStar_Parser_AST.tm)
in (match (uu____6305) with
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

let uu____6329 = (p_universeFrom u1)
in (soft_parens_with_nesting uu____6329))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6330}, (uu____6331)::(uu____6332)::[]) -> begin
(

let uu____6335 = (p_universeFrom u)
in (soft_parens_with_nesting uu____6335))
end
| FStar_Parser_AST.App (uu____6336) -> begin
(

let uu____6343 = (p_universeFrom u)
in (soft_parens_with_nesting uu____6343))
end
| uu____6344 -> begin
(

let uu____6345 = (

let uu____6346 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" uu____6346))
in (failwith uu____6345))
end)))


let term_to_document : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_term e))


let signature_to_document : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun e -> (p_justSig e))


let decl_to_document : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun e -> (p_decl e))


let pat_to_document : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (p_disjunctivePattern p))


let binder_to_document : FStar_Parser_AST.binder  ->  FStar_Pprint.document = (fun b -> (p_binder true b))


let modul_to_document : FStar_Parser_AST.modul  ->  FStar_Pprint.document = (fun m -> ((FStar_ST.op_Colon_Equals should_print_fs_typ_app false);
(

let res = (match (m) with
| FStar_Parser_AST.Module (uu____6419, decls) -> begin
(

let uu____6425 = (FStar_All.pipe_right decls (FStar_List.map decl_to_document))
in (FStar_All.pipe_right uu____6425 (FStar_Pprint.separate FStar_Pprint.hardline)))
end
| FStar_Parser_AST.Interface (uu____6434, decls, uu____6436) -> begin
(

let uu____6441 = (FStar_All.pipe_right decls (FStar_List.map decl_to_document))
in (FStar_All.pipe_right uu____6441 (FStar_Pprint.separate FStar_Pprint.hardline)))
end)
in ((FStar_ST.op_Colon_Equals should_print_fs_typ_app false);
res;
));
))


let comments_to_document : (Prims.string * FStar_Range.range) Prims.list  ->  FStar_Pprint.document = (fun comments -> (FStar_Pprint.separate_map FStar_Pprint.hardline (fun uu____6520 -> (match (uu____6520) with
| (comment, range) -> begin
(str comment)
end)) comments))


let modul_with_comments_to_document : FStar_Parser_AST.modul  ->  (Prims.string * FStar_Range.range) Prims.list  ->  (FStar_Pprint.document * (Prims.string * FStar_Range.range) Prims.list) = (fun m comments -> (

let decls = (match (m) with
| FStar_Parser_AST.Module (uu____6562, decls) -> begin
decls
end
| FStar_Parser_AST.Interface (uu____6568, decls, uu____6570) -> begin
decls
end)
in ((FStar_ST.op_Colon_Equals should_print_fs_typ_app false);
(match (decls) with
| [] -> begin
((FStar_Pprint.empty), (comments))
end
| (d)::ds -> begin
(

let uu____6642 = (match (ds) with
| ({FStar_Parser_AST.d = FStar_Parser_AST.Pragma (FStar_Parser_AST.LightOff); FStar_Parser_AST.drange = uu____6655; FStar_Parser_AST.doc = uu____6656; FStar_Parser_AST.quals = uu____6657; FStar_Parser_AST.attrs = uu____6658})::uu____6659 -> begin
(

let d0 = (FStar_List.hd ds)
in (

let uu____6665 = (

let uu____6668 = (

let uu____6671 = (FStar_List.tl ds)
in (d)::uu____6671)
in (d0)::uu____6668)
in ((uu____6665), (d0.FStar_Parser_AST.drange))))
end
| uu____6676 -> begin
(((d)::ds), (d.FStar_Parser_AST.drange))
end)
in (match (uu____6642) with
| (decls1, first_range) -> begin
(

let extract_decl_range = (fun d1 -> d1.FStar_Parser_AST.drange)
in ((FStar_ST.op_Colon_Equals comment_stack comments);
(

let initial_comment = (

let uu____6761 = (FStar_Range.start_of_range first_range)
in (place_comments_until_pos (Prims.parse_int "0") (Prims.parse_int "1") uu____6761 FStar_Pprint.empty))
in (

let doc1 = (separate_map_with_comments FStar_Pprint.empty FStar_Pprint.empty decl_to_document decls1 extract_decl_range)
in (

let comments1 = (FStar_ST.op_Bang comment_stack)
in ((FStar_ST.op_Colon_Equals comment_stack []);
(FStar_ST.op_Colon_Equals should_print_fs_typ_app false);
(

let uu____6938 = (FStar_Pprint.op_Hat_Hat initial_comment doc1)
in ((uu____6938), (comments1)));
))));
))
end))
end);
)))




