
open Prims
open FStar_Pervasives

let should_print_fs_typ_app : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let unfold_tuples : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref true)


let with_fs_typ_app : 'Auu____37 'Auu____38 . Prims.bool  ->  ('Auu____37  ->  'Auu____38)  ->  'Auu____37  ->  'Auu____38 = (fun b printer t -> (

let b0 = (FStar_ST.op_Bang should_print_fs_typ_app)
in ((FStar_ST.op_Colon_Equals should_print_fs_typ_app b);
(

let res = (printer t)
in ((FStar_ST.op_Colon_Equals should_print_fs_typ_app b0);
res;
));
)))


let str : Prims.string  ->  FStar_Pprint.document = (fun s -> (FStar_Pprint.doc_of_string s))


let default_or_map : 'Auu____135 'Auu____136 . 'Auu____135  ->  ('Auu____136  ->  'Auu____135)  ->  'Auu____136 FStar_Pervasives_Native.option  ->  'Auu____135 = (fun n1 f x -> (match (x) with
| FStar_Pervasives_Native.None -> begin
n1
end
| FStar_Pervasives_Native.Some (x') -> begin
(f x')
end))


let prefix2 : FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun prefix_ body -> (FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "1") prefix_ body))


let prefix2_nonempty : FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun prefix_ body -> (match ((Prims.op_Equality body FStar_Pprint.empty)) with
| true -> begin
prefix_
end
| uu____182 -> begin
(prefix2 prefix_ body)
end))


let op_Hat_Slash_Plus_Hat : FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun prefix_ body -> (prefix2 prefix_ body))


let jump2 : FStar_Pprint.document  ->  FStar_Pprint.document = (fun body -> (FStar_Pprint.jump (Prims.parse_int "2") (Prims.parse_int "1") body))


let infix2 : FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (FStar_Pprint.infix (Prims.parse_int "2") (Prims.parse_int "1"))


let infix0 : FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (FStar_Pprint.infix (Prims.parse_int "0") (Prims.parse_int "1"))


let break1 : FStar_Pprint.document = (FStar_Pprint.break_ (Prims.parse_int "1"))


let separate_break_map : 'Auu____230 . FStar_Pprint.document  ->  ('Auu____230  ->  FStar_Pprint.document)  ->  'Auu____230 Prims.list  ->  FStar_Pprint.document = (fun sep f l -> (

let uu____255 = (

let uu____256 = (

let uu____257 = (FStar_Pprint.op_Hat_Hat sep break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____257))
in (FStar_Pprint.separate_map uu____256 f l))
in (FStar_Pprint.group uu____255)))


let precede_break_separate_map : 'Auu____268 . FStar_Pprint.document  ->  FStar_Pprint.document  ->  ('Auu____268  ->  FStar_Pprint.document)  ->  'Auu____268 Prims.list  ->  FStar_Pprint.document = (fun prec sep f l -> (

let uu____298 = (

let uu____299 = (FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space)
in (

let uu____300 = (

let uu____301 = (FStar_List.hd l)
in (FStar_All.pipe_right uu____301 f))
in (FStar_Pprint.precede uu____299 uu____300)))
in (

let uu____302 = (

let uu____303 = (FStar_List.tl l)
in (FStar_Pprint.concat_map (fun x -> (

let uu____309 = (

let uu____310 = (

let uu____311 = (f x)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____311))
in (FStar_Pprint.op_Hat_Hat sep uu____310))
in (FStar_Pprint.op_Hat_Hat break1 uu____309))) uu____303))
in (FStar_Pprint.op_Hat_Hat uu____298 uu____302))))


let concat_break_map : 'Auu____318 . ('Auu____318  ->  FStar_Pprint.document)  ->  'Auu____318 Prims.list  ->  FStar_Pprint.document = (fun f l -> (

let uu____338 = (FStar_Pprint.concat_map (fun x -> (

let uu____342 = (f x)
in (FStar_Pprint.op_Hat_Hat uu____342 break1))) l)
in (FStar_Pprint.group uu____338)))


let parens_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lparen contents FStar_Pprint.rparen))


let soft_parens_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lparen contents FStar_Pprint.rparen))


let braces_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbrace contents FStar_Pprint.rbrace))


let soft_braces_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbrace contents FStar_Pprint.rbrace))


let soft_braces_with_nesting_tight : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbrace contents FStar_Pprint.rbrace))


let brackets_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbracket contents FStar_Pprint.rbracket))


let soft_brackets_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbracket contents FStar_Pprint.rbracket))


let soft_begin_end_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (

let uu____383 = (str "begin")
in (

let uu____384 = (str "end")
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") uu____383 contents uu____384))))


let separate_map_last : 'Auu____393 . FStar_Pprint.document  ->  (Prims.bool  ->  'Auu____393  ->  FStar_Pprint.document)  ->  'Auu____393 Prims.list  ->  FStar_Pprint.document = (fun sep f es -> (

let l = (FStar_List.length es)
in (

let es1 = (FStar_List.mapi (fun i e -> (f (Prims.op_disEquality i (l - (Prims.parse_int "1"))) e)) es)
in (FStar_Pprint.separate sep es1))))


let separate_break_map_last : 'Auu____445 . FStar_Pprint.document  ->  (Prims.bool  ->  'Auu____445  ->  FStar_Pprint.document)  ->  'Auu____445 Prims.list  ->  FStar_Pprint.document = (fun sep f l -> (

let uu____475 = (

let uu____476 = (

let uu____477 = (FStar_Pprint.op_Hat_Hat sep break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____477))
in (separate_map_last uu____476 f l))
in (FStar_Pprint.group uu____475)))


let separate_map_or_flow : 'Auu____486 . FStar_Pprint.document  ->  ('Auu____486  ->  FStar_Pprint.document)  ->  'Auu____486 Prims.list  ->  FStar_Pprint.document = (fun sep f l -> (match (((FStar_List.length l) < (Prims.parse_int "10"))) with
| true -> begin
(FStar_Pprint.separate_map sep f l)
end
| uu____511 -> begin
(FStar_Pprint.flow_map sep f l)
end))


let flow_map_last : 'Auu____520 . FStar_Pprint.document  ->  (Prims.bool  ->  'Auu____520  ->  FStar_Pprint.document)  ->  'Auu____520 Prims.list  ->  FStar_Pprint.document = (fun sep f es -> (

let l = (FStar_List.length es)
in (

let es1 = (FStar_List.mapi (fun i e -> (f (Prims.op_disEquality i (l - (Prims.parse_int "1"))) e)) es)
in (FStar_Pprint.flow sep es1))))


let separate_map_or_flow_last : 'Auu____572 . FStar_Pprint.document  ->  (Prims.bool  ->  'Auu____572  ->  FStar_Pprint.document)  ->  'Auu____572 Prims.list  ->  FStar_Pprint.document = (fun sep f l -> (match (((FStar_List.length l) < (Prims.parse_int "10"))) with
| true -> begin
(separate_map_last sep f l)
end
| uu____602 -> begin
(flow_map_last sep f l)
end))


let separate_or_flow : FStar_Pprint.document  ->  FStar_Pprint.document Prims.list  ->  FStar_Pprint.document = (fun sep l -> (separate_map_or_flow sep FStar_Pervasives.id l))


let surround_maybe_empty : Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun n1 b doc1 doc2 doc3 -> (match ((Prims.op_Equality doc2 FStar_Pprint.empty)) with
| true -> begin
(

let uu____642 = (FStar_Pprint.op_Hat_Slash_Hat doc1 doc3)
in (FStar_Pprint.group uu____642))
end
| uu____643 -> begin
(FStar_Pprint.surround n1 b doc1 doc2 doc3)
end))


let soft_surround_separate_map : 'Auu____662 . Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  ('Auu____662  ->  FStar_Pprint.document)  ->  'Auu____662 Prims.list  ->  FStar_Pprint.document = (fun n1 b void_ opening sep closing f xs -> (match ((Prims.op_Equality xs [])) with
| true -> begin
void_
end
| uu____714 -> begin
(

let uu____715 = (FStar_Pprint.separate_map sep f xs)
in (FStar_Pprint.soft_surround n1 b opening uu____715 closing))
end))


let soft_surround_map_or_flow : 'Auu____734 . Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  ('Auu____734  ->  FStar_Pprint.document)  ->  'Auu____734 Prims.list  ->  FStar_Pprint.document = (fun n1 b void_ opening sep closing f xs -> (match ((Prims.op_Equality xs [])) with
| true -> begin
void_
end
| uu____786 -> begin
(

let uu____787 = (separate_map_or_flow sep f xs)
in (FStar_Pprint.soft_surround n1 b opening uu____787 closing))
end))


let doc_of_fsdoc : (Prims.string * (Prims.string * Prims.string) Prims.list)  ->  FStar_Pprint.document = (fun uu____802 -> (match (uu____802) with
| (comment, keywords) -> begin
(

let uu____827 = (

let uu____828 = (

let uu____831 = (str comment)
in (

let uu____832 = (

let uu____835 = (

let uu____838 = (FStar_Pprint.separate_map FStar_Pprint.comma (fun uu____847 -> (match (uu____847) with
| (k, v1) -> begin
(

let uu____854 = (

let uu____857 = (str k)
in (

let uu____858 = (

let uu____861 = (

let uu____864 = (str v1)
in (uu____864)::[])
in (FStar_Pprint.rarrow)::uu____861)
in (uu____857)::uu____858))
in (FStar_Pprint.concat uu____854))
end)) keywords)
in (uu____838)::[])
in (FStar_Pprint.space)::uu____835)
in (uu____831)::uu____832))
in (FStar_Pprint.concat uu____828))
in (FStar_Pprint.group uu____827))
end))


let is_unit : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Const (FStar_Const.Const_unit) -> begin
true
end
| uu____870 -> begin
false
end))


let matches_var : FStar_Parser_AST.term  ->  FStar_Ident.ident  ->  Prims.bool = (fun t x -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (y) -> begin
(

let uu____882 = (FStar_Ident.text_of_lid y)
in (Prims.op_Equality x.FStar_Ident.idText uu____882))
end
| uu____883 -> begin
false
end))


let is_tuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Parser_Const.is_tuple_data_lid'


let is_dtuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Parser_Const.is_dtuple_data_lid'


let is_list_structure : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun cons_lid1 nil_lid1 -> (

let rec aux = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (lid, []) -> begin
(FStar_Ident.lid_equals lid nil_lid1)
end
| FStar_Parser_AST.Construct (lid, (uu____925)::((e2, uu____927))::[]) -> begin
((FStar_Ident.lid_equals lid cons_lid1) && (aux e2))
end
| uu____950 -> begin
false
end))
in aux))


let is_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Parser_Const.cons_lid FStar_Parser_Const.nil_lid)


let is_lex_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Parser_Const.lexcons_lid FStar_Parser_Const.lextop_lid)


let rec extract_from_list : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (uu____968, []) -> begin
[]
end
| FStar_Parser_AST.Construct (uu____979, ((e1, FStar_Parser_AST.Nothing))::((e2, FStar_Parser_AST.Nothing))::[]) -> begin
(

let uu____1000 = (extract_from_list e2)
in (e1)::uu____1000)
end
| uu____1003 -> begin
(

let uu____1004 = (

let uu____1005 = (FStar_Parser_AST.term_to_string e)
in (FStar_Util.format1 "Not a list %s" uu____1005))
in (failwith uu____1004))
end))


let is_array : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (lid); FStar_Parser_AST.range = uu____1014; FStar_Parser_AST.level = uu____1015}, l, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) && (is_list l))
end
| uu____1017 -> begin
false
end))


let rec is_ref_set : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (maybe_empty_lid) -> begin
(FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty)
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_singleton_lid); FStar_Parser_AST.range = uu____1025; FStar_Parser_AST.level = uu____1026}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_addr_of_lid); FStar_Parser_AST.range = uu____1028; FStar_Parser_AST.level = uu____1029}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____1031; FStar_Parser_AST.level = uu____1032}, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals maybe_singleton_lid FStar_Parser_Const.set_singleton) && (FStar_Ident.lid_equals maybe_addr_of_lid FStar_Parser_Const.heap_addr_of_lid))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_union_lid); FStar_Parser_AST.range = uu____1034; FStar_Parser_AST.level = uu____1035}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____1037; FStar_Parser_AST.level = uu____1038}, e2, FStar_Parser_AST.Nothing) -> begin
(((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union) && (is_ref_set e1)) && (is_ref_set e2))
end
| uu____1040 -> begin
false
end))


let rec extract_from_ref_set : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (uu____1050) -> begin
[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (uu____1051); FStar_Parser_AST.range = uu____1052; FStar_Parser_AST.level = uu____1053}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (uu____1054); FStar_Parser_AST.range = uu____1055; FStar_Parser_AST.level = uu____1056}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____1058; FStar_Parser_AST.level = uu____1059}, FStar_Parser_AST.Nothing) -> begin
(e1)::[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (uu____1060); FStar_Parser_AST.range = uu____1061; FStar_Parser_AST.level = uu____1062}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____1064; FStar_Parser_AST.level = uu____1065}, e2, FStar_Parser_AST.Nothing) -> begin
(

let uu____1067 = (extract_from_ref_set e1)
in (

let uu____1070 = (extract_from_ref_set e2)
in (FStar_List.append uu____1067 uu____1070)))
end
| uu____1073 -> begin
(

let uu____1074 = (

let uu____1075 = (FStar_Parser_AST.term_to_string e)
in (FStar_Util.format1 "Not a ref set %s" uu____1075))
in (failwith uu____1074))
end))


let is_general_application : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____1083 = ((is_array e) || (is_ref_set e))
in (not (uu____1083))))


let is_general_construction : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____1089 = ((is_list e) || (is_lex_list e))
in (not (uu____1089))))


let is_general_prefix_op : FStar_Ident.ident  ->  Prims.bool = (fun op -> (

let op_starting_char = (

let uu____1097 = (FStar_Ident.text_of_id op)
in (FStar_Util.char_at uu____1097 (Prims.parse_int "0")))
in (((Prims.op_Equality op_starting_char 33 (*!*)) || (Prims.op_Equality op_starting_char 63 (*?*))) || ((Prims.op_Equality op_starting_char 126 (*~*)) && (

let uu____1105 = (FStar_Ident.text_of_id op)
in (Prims.op_disEquality uu____1105 "~"))))))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun e -> (

let rec aux = (fun e1 acc -> (match (e1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App (head1, arg, imp) -> begin
(aux head1 ((((arg), (imp)))::acc))
end
| uu____1171 -> begin
((e1), (acc))
end))
in (aux e [])))

type associativity =
| Left
| Right
| NonAssoc


let uu___is_Left : associativity  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Left -> begin
true
end
| uu____1187 -> begin
false
end))


let uu___is_Right : associativity  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Right -> begin
true
end
| uu____1193 -> begin
false
end))


let uu___is_NonAssoc : associativity  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NonAssoc -> begin
true
end
| uu____1199 -> begin
false
end))


type token =
(FStar_Char.char, Prims.string) FStar_Util.either


type associativity_level =
(associativity * token Prims.list)


let token_to_string : (FStar_BaseTypes.char, Prims.string) FStar_Util.either  ->  Prims.string = (fun uu___113_1220 -> (match (uu___113_1220) with
| FStar_Util.Inl (c) -> begin
(Prims.strcat (FStar_Util.string_of_char c) ".*")
end
| FStar_Util.Inr (s) -> begin
s
end))


let matches_token : Prims.string  ->  (FStar_Char.char, Prims.string) FStar_Util.either  ->  Prims.bool = (fun s uu___114_1245 -> (match (uu___114_1245) with
| FStar_Util.Inl (c) -> begin
(

let uu____1254 = (FStar_String.get s (Prims.parse_int "0"))
in (Prims.op_Equality uu____1254 c))
end
| FStar_Util.Inr (s') -> begin
(Prims.op_Equality s s')
end))


let matches_level : 'Auu____1265 . Prims.string  ->  ('Auu____1265 * (FStar_Char.char, Prims.string) FStar_Util.either Prims.list)  ->  Prims.bool = (fun s uu____1286 -> (match (uu____1286) with
| (assoc_levels, tokens) -> begin
(

let uu____1314 = (FStar_List.tryFind (matches_token s) tokens)
in (Prims.op_disEquality uu____1314 FStar_Pervasives_Native.None))
end))


let opinfix4 : associativity_level = ((Right), ((FStar_Util.Inr ("**"))::[]))


let opinfix3 : associativity_level = ((Left), ((FStar_Util.Inl (42 (***)))::(FStar_Util.Inl (47 (*/*)))::(FStar_Util.Inl (37 (*%*)))::[]))


let opinfix2 : associativity_level = ((Left), ((FStar_Util.Inl (43 (*+*)))::(FStar_Util.Inl (45 (*-*)))::[]))


let minus_lvl : associativity_level = ((Left), ((FStar_Util.Inr ("-"))::[]))


let opinfix1 : associativity_level = ((Right), ((FStar_Util.Inl (64 (*@*)))::(FStar_Util.Inl (94 (*^*)))::[]))


let pipe_right : associativity_level = ((Left), ((FStar_Util.Inr ("|>"))::[]))


let opinfix0d : associativity_level = ((Left), ((FStar_Util.Inl (36 (*$*)))::[]))


let opinfix0c : associativity_level = ((Left), ((FStar_Util.Inl (61 (*=*)))::(FStar_Util.Inl (60 (*<*)))::(FStar_Util.Inl (62 (*>*)))::[]))


let equal : associativity_level = ((Left), ((FStar_Util.Inr ("="))::[]))


let opinfix0b : associativity_level = ((Left), ((FStar_Util.Inl (38 (*&*)))::[]))


let opinfix0a : associativity_level = ((Left), ((FStar_Util.Inl (124 (*|*)))::[]))


let colon_equals : associativity_level = ((NonAssoc), ((FStar_Util.Inr (":="))::[]))


let amp : associativity_level = ((Right), ((FStar_Util.Inr ("&"))::[]))


let colon_colon : associativity_level = ((Right), ((FStar_Util.Inr ("::"))::[]))


let level_associativity_spec : associativity_level Prims.list = (opinfix4)::(opinfix3)::(opinfix2)::(opinfix1)::(pipe_right)::(opinfix0d)::(opinfix0c)::(opinfix0b)::(opinfix0a)::(colon_equals)::(amp)::(colon_colon)::[]


let level_table : ((Prims.int * Prims.int * Prims.int) * token Prims.list) Prims.list = (

let levels_from_associativity = (fun l uu___115_1432 -> (match (uu___115_1432) with
| Left -> begin
((l), (l), ((l - (Prims.parse_int "1"))))
end
| Right -> begin
(((l - (Prims.parse_int "1"))), (l), (l))
end
| NonAssoc -> begin
(((l - (Prims.parse_int "1"))), (l), ((l - (Prims.parse_int "1"))))
end))
in (FStar_List.mapi (fun i uu____1462 -> (match (uu____1462) with
| (assoc1, tokens) -> begin
(((levels_from_associativity i assoc1)), (tokens))
end)) level_associativity_spec))


let assign_levels : associativity_level Prims.list  ->  Prims.string  ->  (Prims.int * Prims.int * Prims.int) = (fun token_associativity_spec s -> (

let uu____1521 = (FStar_List.tryFind (matches_level s) level_table)
in (match (uu____1521) with
| FStar_Pervasives_Native.Some (assoc_levels, uu____1561) -> begin
assoc_levels
end
| uu____1590 -> begin
(failwith (Prims.strcat "Unrecognized operator " s))
end)))


let max : Prims.int  ->  Prims.int  ->  Prims.int = (fun k1 k2 -> (match ((k1 > k2)) with
| true -> begin
k1
end
| uu____1621 -> begin
k2
end))


let max_level : 'Auu____1626 . ('Auu____1626 * token Prims.list) Prims.list  ->  Prims.int = (fun l -> (

let find_level_and_max = (fun n1 level -> (

let uu____1671 = (FStar_List.tryFind (fun uu____1701 -> (match (uu____1701) with
| (uu____1714, tokens) -> begin
(Prims.op_Equality tokens (FStar_Pervasives_Native.snd level))
end)) level_table)
in (match (uu____1671) with
| FStar_Pervasives_Native.Some ((uu____1736, l1, uu____1738), uu____1739) -> begin
(max n1 l1)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____1774 = (

let uu____1775 = (

let uu____1776 = (FStar_List.map token_to_string (FStar_Pervasives_Native.snd level))
in (FStar_String.concat "," uu____1776))
in (FStar_Util.format1 "Undefined associativity level %s" uu____1775))
in (failwith uu____1774))
end)))
in (FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l)))


let levels : Prims.string  ->  (Prims.int * Prims.int * Prims.int) = (fun op -> (

let uu____1798 = (assign_levels level_associativity_spec op)
in (match (uu____1798) with
| (left1, mine, right1) -> begin
(match ((Prims.op_Equality op "*")) with
| true -> begin
(((left1 - (Prims.parse_int "1"))), (mine), (right1))
end
| uu____1820 -> begin
((left1), (mine), (right1))
end)
end)))


let operatorInfix0ad12 : associativity_level Prims.list = (opinfix0a)::(opinfix0b)::(opinfix0c)::(opinfix0d)::(opinfix1)::(opinfix2)::[]


let is_operatorInfix0ad12 : FStar_Ident.ident  ->  Prims.bool = (fun op -> (

let uu____1828 = (

let uu____1831 = (

let uu____1836 = (FStar_Ident.text_of_id op)
in (FStar_All.pipe_left matches_level uu____1836))
in (FStar_List.tryFind uu____1831 operatorInfix0ad12))
in (Prims.op_disEquality uu____1828 FStar_Pervasives_Native.None)))


let is_operatorInfix34 : FStar_Ident.ident  ->  Prims.bool = (

let opinfix34 = (opinfix3)::(opinfix4)::[]
in (fun op -> (

let uu____1894 = (

let uu____1908 = (

let uu____1924 = (FStar_Ident.text_of_id op)
in (FStar_All.pipe_left matches_level uu____1924))
in (FStar_List.tryFind uu____1908 opinfix34))
in (Prims.op_disEquality uu____1894 FStar_Pervasives_Native.None))))


let handleable_args_length : FStar_Ident.ident  ->  Prims.int = (fun op -> (

let op_s = (FStar_Ident.text_of_id op)
in (

let uu____1980 = ((is_general_prefix_op op) || (FStar_List.mem op_s (("-")::("~")::[])))
in (match (uu____1980) with
| true -> begin
(Prims.parse_int "1")
end
| uu____1981 -> begin
(

let uu____1982 = (((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) || (FStar_List.mem op_s (("<==>")::("==>")::("\\/")::("/\\")::("=")::("|>")::(":=")::(".()")::(".[]")::[])))
in (match (uu____1982) with
| true -> begin
(Prims.parse_int "2")
end
| uu____1983 -> begin
(match ((FStar_List.mem op_s ((".()<-")::(".[]<-")::[]))) with
| true -> begin
(Prims.parse_int "3")
end
| uu____1984 -> begin
(Prims.parse_int "0")
end)
end))
end))))


let handleable_op : 'Auu____1991 . FStar_Ident.ident  ->  'Auu____1991 Prims.list  ->  Prims.bool = (fun op args -> (match ((FStar_List.length args)) with
| _0_4 when (_0_4 = (Prims.parse_int "0")) -> begin
true
end
| _0_5 when (_0_5 = (Prims.parse_int "1")) -> begin
((is_general_prefix_op op) || (

let uu____2007 = (FStar_Ident.text_of_id op)
in (FStar_List.mem uu____2007 (("-")::("~")::[]))))
end
| _0_6 when (_0_6 = (Prims.parse_int "2")) -> begin
(((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) || (

let uu____2009 = (FStar_Ident.text_of_id op)
in (FStar_List.mem uu____2009 (("<==>")::("==>")::("\\/")::("/\\")::("=")::("|>")::(":=")::(".()")::(".[]")::[]))))
end
| _0_7 when (_0_7 = (Prims.parse_int "3")) -> begin
(

let uu____2010 = (FStar_Ident.text_of_id op)
in (FStar_List.mem uu____2010 ((".()<-")::(".[]<-")::[])))
end
| uu____2011 -> begin
false
end))


let comment_stack : (Prims.string * FStar_Range.range) Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let with_comment : 'Auu____2049 . ('Auu____2049  ->  FStar_Pprint.document)  ->  'Auu____2049  ->  FStar_Range.range  ->  FStar_Pprint.document = (fun printer tm tmrange -> (

let rec comments_before_pos = (fun acc print_pos lookahead_pos -> (

let uu____2090 = (FStar_ST.op_Bang comment_stack)
in (match (uu____2090) with
| [] -> begin
((acc), (false))
end
| ((comment, crange))::cs -> begin
(

let uu____2149 = (FStar_Range.range_before_pos crange print_pos)
in (match (uu____2149) with
| true -> begin
((FStar_ST.op_Colon_Equals comment_stack cs);
(

let uu____2186 = (

let uu____2187 = (

let uu____2188 = (str comment)
in (FStar_Pprint.op_Hat_Hat uu____2188 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat acc uu____2187))
in (comments_before_pos uu____2186 print_pos lookahead_pos));
)
end
| uu____2189 -> begin
(

let uu____2190 = (FStar_Range.range_before_pos crange lookahead_pos)
in ((acc), (uu____2190)))
end))
end)))
in (

let uu____2191 = (

let uu____2196 = (

let uu____2197 = (FStar_Range.start_of_range tmrange)
in (FStar_Range.end_of_line uu____2197))
in (

let uu____2198 = (FStar_Range.end_of_range tmrange)
in (comments_before_pos FStar_Pprint.empty uu____2196 uu____2198)))
in (match (uu____2191) with
| (comments, has_lookahead) -> begin
(

let printed_e = (printer tm)
in (

let comments1 = (match (has_lookahead) with
| true -> begin
(

let pos = (FStar_Range.end_of_range tmrange)
in (

let uu____2204 = (comments_before_pos comments pos pos)
in (FStar_Pervasives_Native.fst uu____2204)))
end
| uu____2209 -> begin
comments
end)
in (

let uu____2210 = (FStar_Pprint.op_Hat_Hat comments1 printed_e)
in (FStar_Pprint.group uu____2210))))
end))))


let rec place_comments_until_pos : Prims.int  ->  Prims.int  ->  FStar_Range.pos  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun k lbegin pos_end doc1 -> (

let uu____2231 = (FStar_ST.op_Bang comment_stack)
in (match (uu____2231) with
| ((comment, crange))::cs when (FStar_Range.range_before_pos crange pos_end) -> begin
((FStar_ST.op_Colon_Equals comment_stack cs);
(

let lnum = (

let uu____2315 = (

let uu____2316 = (

let uu____2317 = (FStar_Range.start_of_range crange)
in (FStar_Range.line_of_pos uu____2317))
in (uu____2316 - lbegin))
in (max k uu____2315))
in (

let lnum1 = (Prims.min (Prims.parse_int "2") lnum)
in (

let doc2 = (

let uu____2320 = (

let uu____2321 = (FStar_Pprint.repeat lnum1 FStar_Pprint.hardline)
in (

let uu____2322 = (str comment)
in (FStar_Pprint.op_Hat_Hat uu____2321 uu____2322)))
in (FStar_Pprint.op_Hat_Hat doc1 uu____2320))
in (

let uu____2323 = (

let uu____2324 = (FStar_Range.end_of_range crange)
in (FStar_Range.line_of_pos uu____2324))
in (place_comments_until_pos (Prims.parse_int "1") uu____2323 pos_end doc2)))));
)
end
| uu____2325 -> begin
(match ((Prims.op_Equality doc1 FStar_Pprint.empty)) with
| true -> begin
FStar_Pprint.empty
end
| uu____2332 -> begin
(

let lnum = (

let uu____2334 = (

let uu____2335 = (FStar_Range.line_of_pos pos_end)
in (uu____2335 - lbegin))
in (max (Prims.parse_int "1") uu____2334))
in (

let lnum1 = (Prims.min (Prims.parse_int "2") lnum)
in (

let uu____2337 = (FStar_Pprint.repeat lnum1 FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat doc1 uu____2337))))
end)
end)))


let separate_map_with_comments : 'Auu____2350 . FStar_Pprint.document  ->  FStar_Pprint.document  ->  ('Auu____2350  ->  FStar_Pprint.document)  ->  'Auu____2350 Prims.list  ->  ('Auu____2350  ->  FStar_Range.range)  ->  FStar_Pprint.document = (fun prefix1 sep f xs extract_range -> (

let fold_fun = (fun uu____2407 x -> (match (uu____2407) with
| (last_line, doc1) -> begin
(

let r = (extract_range x)
in (

let doc2 = (

let uu____2421 = (FStar_Range.start_of_range r)
in (place_comments_until_pos (Prims.parse_int "1") last_line uu____2421 doc1))
in (

let uu____2422 = (

let uu____2423 = (FStar_Range.end_of_range r)
in (FStar_Range.line_of_pos uu____2423))
in (

let uu____2424 = (

let uu____2425 = (

let uu____2426 = (f x)
in (FStar_Pprint.op_Hat_Hat sep uu____2426))
in (FStar_Pprint.op_Hat_Hat doc2 uu____2425))
in ((uu____2422), (uu____2424))))))
end))
in (

let uu____2427 = (

let uu____2434 = (FStar_List.hd xs)
in (

let uu____2435 = (FStar_List.tl xs)
in ((uu____2434), (uu____2435))))
in (match (uu____2427) with
| (x, xs1) -> begin
(

let init1 = (

let uu____2451 = (

let uu____2452 = (

let uu____2453 = (extract_range x)
in (FStar_Range.end_of_range uu____2453))
in (FStar_Range.line_of_pos uu____2452))
in (

let uu____2454 = (

let uu____2455 = (f x)
in (FStar_Pprint.op_Hat_Hat prefix1 uu____2455))
in ((uu____2451), (uu____2454))))
in (

let uu____2456 = (FStar_List.fold_left fold_fun init1 xs1)
in (FStar_Pervasives_Native.snd uu____2456)))
end))))


let separate_map_with_comments_kw : 'Auu____2479 'Auu____2480 . 'Auu____2479  ->  'Auu____2479  ->  ('Auu____2479  ->  'Auu____2480  ->  FStar_Pprint.document)  ->  'Auu____2480 Prims.list  ->  ('Auu____2480  ->  FStar_Range.range)  ->  FStar_Pprint.document = (fun prefix1 sep f xs extract_range -> (

let fold_fun = (fun uu____2542 x -> (match (uu____2542) with
| (last_line, doc1) -> begin
(

let r = (extract_range x)
in (

let doc2 = (

let uu____2556 = (FStar_Range.start_of_range r)
in (place_comments_until_pos (Prims.parse_int "1") last_line uu____2556 doc1))
in (

let uu____2557 = (

let uu____2558 = (FStar_Range.end_of_range r)
in (FStar_Range.line_of_pos uu____2558))
in (

let uu____2559 = (

let uu____2560 = (f sep x)
in (FStar_Pprint.op_Hat_Hat doc2 uu____2560))
in ((uu____2557), (uu____2559))))))
end))
in (

let uu____2561 = (

let uu____2568 = (FStar_List.hd xs)
in (

let uu____2569 = (FStar_List.tl xs)
in ((uu____2568), (uu____2569))))
in (match (uu____2561) with
| (x, xs1) -> begin
(

let init1 = (

let uu____2585 = (

let uu____2586 = (

let uu____2587 = (extract_range x)
in (FStar_Range.end_of_range uu____2587))
in (FStar_Range.line_of_pos uu____2586))
in (

let uu____2588 = (f prefix1 x)
in ((uu____2585), (uu____2588))))
in (

let uu____2589 = (FStar_List.fold_left fold_fun init1 xs1)
in (FStar_Pervasives_Native.snd uu____2589)))
end))))


let rec p_decl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (

let qualifiers = (match (((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d))) with
| ((FStar_Parser_AST.Assumption)::[], FStar_Parser_AST.Assume (id1, uu____3299)) -> begin
(

let uu____3302 = (

let uu____3303 = (FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_All.pipe_right uu____3303 FStar_Util.is_upper))
in (match (uu____3302) with
| true -> begin
(

let uu____3306 = (p_qualifier FStar_Parser_AST.Assumption)
in (FStar_Pprint.op_Hat_Hat uu____3306 FStar_Pprint.space))
end
| uu____3307 -> begin
(p_qualifiers d.FStar_Parser_AST.quals)
end))
end
| uu____3308 -> begin
(p_qualifiers d.FStar_Parser_AST.quals)
end)
in (

let uu____3315 = (FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc)
in (

let uu____3316 = (

let uu____3317 = (p_attributes d.FStar_Parser_AST.attrs)
in (

let uu____3318 = (

let uu____3319 = (p_rawDecl d)
in (FStar_Pprint.op_Hat_Hat qualifiers uu____3319))
in (FStar_Pprint.op_Hat_Hat uu____3317 uu____3318)))
in (FStar_Pprint.op_Hat_Hat uu____3315 uu____3316)))))
and p_attributes : FStar_Parser_AST.attributes_  ->  FStar_Pprint.document = (fun attrs -> (match (attrs) with
| [] -> begin
FStar_Pprint.empty
end
| uu____3321 -> begin
(

let uu____3322 = (

let uu____3323 = (str "@ ")
in (

let uu____3324 = (

let uu____3325 = (

let uu____3326 = (

let uu____3327 = (

let uu____3328 = (FStar_List.map p_atomicTerm attrs)
in (FStar_Pprint.flow break1 uu____3328))
in (FStar_Pprint.op_Hat_Hat uu____3327 FStar_Pprint.rbracket))
in (FStar_Pprint.align uu____3326))
in (FStar_Pprint.op_Hat_Hat uu____3325 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat uu____3323 uu____3324)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3322))
end))
and p_fsdoc : FStar_Parser_AST.fsdoc  ->  FStar_Pprint.document = (fun uu____3331 -> (match (uu____3331) with
| (doc1, kwd_args) -> begin
(

let kwd_args_doc = (match (kwd_args) with
| [] -> begin
FStar_Pprint.empty
end
| kwd_args1 -> begin
(

let process_kwd_arg = (fun uu____3367 -> (match (uu____3367) with
| (kwd, arg) -> begin
(

let uu____3374 = (str "@")
in (

let uu____3375 = (

let uu____3376 = (str kwd)
in (

let uu____3377 = (

let uu____3378 = (str arg)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3378))
in (FStar_Pprint.op_Hat_Hat uu____3376 uu____3377)))
in (FStar_Pprint.op_Hat_Hat uu____3374 uu____3375)))
end))
in (

let uu____3379 = (

let uu____3380 = (FStar_Pprint.separate_map FStar_Pprint.hardline process_kwd_arg kwd_args1)
in (FStar_Pprint.op_Hat_Hat uu____3380 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3379)))
end)
in (

let uu____3385 = (

let uu____3386 = (

let uu____3387 = (

let uu____3388 = (

let uu____3389 = (str doc1)
in (

let uu____3390 = (

let uu____3391 = (

let uu____3392 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3392))
in (FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3391))
in (FStar_Pprint.op_Hat_Hat uu____3389 uu____3390)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3388))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3387))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3386))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3385)))
end))
and p_justSig : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (lid, t) -> begin
(

let uu____3396 = (

let uu____3397 = (str "val")
in (

let uu____3398 = (

let uu____3399 = (

let uu____3400 = (p_lident lid)
in (

let uu____3401 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat uu____3400 uu____3401)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3399))
in (FStar_Pprint.op_Hat_Hat uu____3397 uu____3398)))
in (

let uu____3402 = (p_typ false false t)
in (FStar_Pprint.op_Hat_Hat uu____3396 uu____3402)))
end
| FStar_Parser_AST.TopLevelLet (uu____3403, lbs) -> begin
(FStar_Pprint.separate_map FStar_Pprint.hardline (fun lb -> (

let uu____3428 = (

let uu____3429 = (str "let")
in (p_letlhs uu____3429 lb))
in (FStar_Pprint.group uu____3428))) lbs)
end
| uu____3430 -> begin
FStar_Pprint.empty
end))
and p_list : (FStar_Ident.ident  ->  FStar_Pprint.document)  ->  FStar_Pprint.document  ->  FStar_Ident.ident Prims.list  ->  FStar_Pprint.document = (fun f sep l -> (

let rec p_list' = (fun uu___116_3445 -> (match (uu___116_3445) with
| [] -> begin
FStar_Pprint.empty
end
| (x)::[] -> begin
(f x)
end
| (x)::xs -> begin
(

let uu____3453 = (f x)
in (

let uu____3454 = (

let uu____3455 = (p_list' xs)
in (FStar_Pprint.op_Hat_Hat sep uu____3455))
in (FStar_Pprint.op_Hat_Hat uu____3453 uu____3454)))
end))
in (

let uu____3456 = (str "[")
in (

let uu____3457 = (

let uu____3458 = (p_list' l)
in (

let uu____3459 = (str "]")
in (FStar_Pprint.op_Hat_Hat uu____3458 uu____3459)))
in (FStar_Pprint.op_Hat_Hat uu____3456 uu____3457)))))
and p_rawDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Open (uid) -> begin
(

let uu____3462 = (

let uu____3463 = (str "open")
in (

let uu____3464 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat uu____3463 uu____3464)))
in (FStar_Pprint.group uu____3462))
end
| FStar_Parser_AST.Include (uid) -> begin
(

let uu____3466 = (

let uu____3467 = (str "include")
in (

let uu____3468 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat uu____3467 uu____3468)))
in (FStar_Pprint.group uu____3466))
end
| FStar_Parser_AST.ModuleAbbrev (uid1, uid2) -> begin
(

let uu____3471 = (

let uu____3472 = (str "module")
in (

let uu____3473 = (

let uu____3474 = (

let uu____3475 = (p_uident uid1)
in (

let uu____3476 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____3475 uu____3476)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3474))
in (FStar_Pprint.op_Hat_Hat uu____3472 uu____3473)))
in (

let uu____3477 = (p_quident uid2)
in (op_Hat_Slash_Plus_Hat uu____3471 uu____3477)))
end
| FStar_Parser_AST.TopLevelModule (uid) -> begin
(

let uu____3479 = (

let uu____3480 = (str "module")
in (

let uu____3481 = (

let uu____3482 = (p_quident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3482))
in (FStar_Pprint.op_Hat_Hat uu____3480 uu____3481)))
in (FStar_Pprint.group uu____3479))
end
| FStar_Parser_AST.Tycon (true, ((FStar_Parser_AST.TyconAbbrev (uid, tpars, FStar_Pervasives_Native.None, t), FStar_Pervasives_Native.None))::[]) -> begin
(

let effect_prefix_doc = (

let uu____3515 = (str "effect")
in (

let uu____3516 = (

let uu____3517 = (p_uident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3517))
in (FStar_Pprint.op_Hat_Hat uu____3515 uu____3516)))
in (

let uu____3518 = (

let uu____3519 = (p_typars tpars)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") effect_prefix_doc uu____3519 FStar_Pprint.equals))
in (

let uu____3520 = (p_typ false false t)
in (op_Hat_Slash_Plus_Hat uu____3518 uu____3520))))
end
| FStar_Parser_AST.Tycon (false, tcdefs) -> begin
(

let uu____3538 = (

let uu____3539 = (str "type")
in (

let uu____3540 = (FStar_List.hd tcdefs)
in (p_fsdocTypeDeclPairs uu____3539 uu____3540)))
in (

let uu____3553 = (

let uu____3554 = (FStar_List.tl tcdefs)
in (FStar_All.pipe_left (FStar_Pprint.concat_map (fun x -> (

let uu____3592 = (

let uu____3593 = (str "and")
in (p_fsdocTypeDeclPairs uu____3593 x))
in (FStar_Pprint.op_Hat_Hat break1 uu____3592)))) uu____3554))
in (FStar_Pprint.op_Hat_Hat uu____3538 uu____3553)))
end
| FStar_Parser_AST.TopLevelLet (q, lbs) -> begin
(

let let_doc = (

let uu____3609 = (str "let")
in (

let uu____3610 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat uu____3609 uu____3610)))
in (

let uu____3611 = (str "and")
in (separate_map_with_comments_kw let_doc uu____3611 p_letbinding lbs (fun uu____3619 -> (match (uu____3619) with
| (p, t) -> begin
(FStar_Range.union_ranges p.FStar_Parser_AST.prange t.FStar_Parser_AST.range)
end)))))
end
| FStar_Parser_AST.Val (lid, t) -> begin
(

let uu____3628 = (str "val")
in (

let uu____3629 = (

let uu____3630 = (

let uu____3631 = (p_lident lid)
in (

let uu____3632 = (

let uu____3633 = (

let uu____3634 = (

let uu____3635 = (p_typ false false t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3635))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3634))
in (FStar_Pprint.group uu____3633))
in (FStar_Pprint.op_Hat_Hat uu____3631 uu____3632)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3630))
in (FStar_Pprint.op_Hat_Hat uu____3628 uu____3629)))
end
| FStar_Parser_AST.Assume (id1, t) -> begin
(

let decl_keyword = (

let uu____3639 = (

let uu____3640 = (FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_All.pipe_right uu____3640 FStar_Util.is_upper))
in (match (uu____3639) with
| true -> begin
FStar_Pprint.empty
end
| uu____3643 -> begin
(

let uu____3644 = (str "val")
in (FStar_Pprint.op_Hat_Hat uu____3644 FStar_Pprint.space))
end))
in (

let uu____3645 = (

let uu____3646 = (p_ident id1)
in (

let uu____3647 = (

let uu____3648 = (

let uu____3649 = (

let uu____3650 = (p_typ false false t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3650))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3649))
in (FStar_Pprint.group uu____3648))
in (FStar_Pprint.op_Hat_Hat uu____3646 uu____3647)))
in (FStar_Pprint.op_Hat_Hat decl_keyword uu____3645)))
end
| FStar_Parser_AST.Exception (uid, t_opt) -> begin
(

let uu____3657 = (str "exception")
in (

let uu____3658 = (

let uu____3659 = (

let uu____3660 = (p_uident uid)
in (

let uu____3661 = (FStar_Pprint.optional (fun t -> (

let uu____3665 = (

let uu____3666 = (str "of")
in (

let uu____3667 = (p_typ false false t)
in (op_Hat_Slash_Plus_Hat uu____3666 uu____3667)))
in (FStar_Pprint.op_Hat_Hat break1 uu____3665))) t_opt)
in (FStar_Pprint.op_Hat_Hat uu____3660 uu____3661)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3659))
in (FStar_Pprint.op_Hat_Hat uu____3657 uu____3658)))
end
| FStar_Parser_AST.NewEffect (ne) -> begin
(

let uu____3669 = (str "new_effect")
in (

let uu____3670 = (

let uu____3671 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3671))
in (FStar_Pprint.op_Hat_Hat uu____3669 uu____3670)))
end
| FStar_Parser_AST.SubEffect (se) -> begin
(

let uu____3673 = (str "sub_effect")
in (

let uu____3674 = (

let uu____3675 = (p_subEffect se)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3675))
in (FStar_Pprint.op_Hat_Hat uu____3673 uu____3674)))
end
| FStar_Parser_AST.Pragma (p) -> begin
(p_pragma p)
end
| FStar_Parser_AST.Fsdoc (doc1) -> begin
(

let uu____3678 = (p_fsdoc doc1)
in (FStar_Pprint.op_Hat_Hat uu____3678 FStar_Pprint.hardline))
end
| FStar_Parser_AST.Main (uu____3679) -> begin
(failwith "*Main declaration* : Is that really still in use ??")
end
| FStar_Parser_AST.Tycon (true, uu____3680) -> begin
(failwith "Effect abbreviation is expected to be defined by an abbreviation")
end
| FStar_Parser_AST.Splice (ids, t) -> begin
(

let uu____3703 = (str "%splice")
in (

let uu____3704 = (

let uu____3705 = (

let uu____3706 = (str ";")
in (p_list p_uident uu____3706 ids))
in (

let uu____3707 = (

let uu____3708 = (p_term false false t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3708))
in (FStar_Pprint.op_Hat_Hat uu____3705 uu____3707)))
in (FStar_Pprint.op_Hat_Hat uu____3703 uu____3704)))
end))
and p_pragma : FStar_Parser_AST.pragma  ->  FStar_Pprint.document = (fun uu___117_3709 -> (match (uu___117_3709) with
| FStar_Parser_AST.SetOptions (s) -> begin
(

let uu____3711 = (str "#set-options")
in (

let uu____3712 = (

let uu____3713 = (

let uu____3714 = (str s)
in (FStar_Pprint.dquotes uu____3714))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3713))
in (FStar_Pprint.op_Hat_Hat uu____3711 uu____3712)))
end
| FStar_Parser_AST.ResetOptions (s_opt) -> begin
(

let uu____3718 = (str "#reset-options")
in (

let uu____3719 = (FStar_Pprint.optional (fun s -> (

let uu____3723 = (

let uu____3724 = (str s)
in (FStar_Pprint.dquotes uu____3724))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3723))) s_opt)
in (FStar_Pprint.op_Hat_Hat uu____3718 uu____3719)))
end
| FStar_Parser_AST.PushOptions (s_opt) -> begin
(

let uu____3728 = (str "#push-options")
in (

let uu____3729 = (FStar_Pprint.optional (fun s -> (

let uu____3733 = (

let uu____3734 = (str s)
in (FStar_Pprint.dquotes uu____3734))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3733))) s_opt)
in (FStar_Pprint.op_Hat_Hat uu____3728 uu____3729)))
end
| FStar_Parser_AST.PopOptions -> begin
(str "#pop-options")
end
| FStar_Parser_AST.LightOff -> begin
((FStar_ST.op_Colon_Equals should_print_fs_typ_app true);
(str "#light \"off\"");
)
end))
and p_typars : FStar_Parser_AST.binder Prims.list  ->  FStar_Pprint.document = (fun bs -> (p_binders true bs))
and p_fsdocTypeDeclPairs : FStar_Pprint.document  ->  (FStar_Parser_AST.tycon * FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option)  ->  FStar_Pprint.document = (fun kw uu____3759 -> (match (uu____3759) with
| (typedecl, fsdoc_opt) -> begin
(

let uu____3772 = (p_typeDecl ((kw), (fsdoc_opt)) typedecl)
in (match (uu____3772) with
| (decl, body) -> begin
(

let uu____3790 = (body ())
in (FStar_Pprint.op_Hat_Hat decl uu____3790))
end))
end))
and p_typeDecl : (FStar_Pprint.document * FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option)  ->  FStar_Parser_AST.tycon  ->  (FStar_Pprint.document * (unit  ->  FStar_Pprint.document)) = (fun pre uu___118_3792 -> (match (uu___118_3792) with
| FStar_Parser_AST.TyconAbstract (lid, bs, typ_opt) -> begin
(

let empty' = (fun uu____3822 -> FStar_Pprint.empty)
in (

let uu____3823 = (p_typeDeclPrefix pre false lid bs typ_opt)
in ((uu____3823), (empty'))))
end
| FStar_Parser_AST.TyconAbbrev (lid, bs, typ_opt, t) -> begin
(

let f = (fun uu____3844 -> (

let uu____3845 = (p_typ false false t)
in (jump2 uu____3845)))
in (

let uu____3846 = (p_typeDeclPrefix pre true lid bs typ_opt)
in ((uu____3846), (f))))
end
| FStar_Parser_AST.TyconRecord (lid, bs, typ_opt, record_field_decls) -> begin
(

let p_recordFieldAndComments = (fun ps uu____3900 -> (match (uu____3900) with
| (lid1, t, doc_opt) -> begin
(

let uu____3916 = (FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range)
in (with_comment (p_recordFieldDecl ps) ((lid1), (t), (doc_opt)) uu____3916))
end))
in (

let p_fields = (fun uu____3932 -> (

let uu____3933 = (

let uu____3934 = (

let uu____3935 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (separate_map_last uu____3935 p_recordFieldAndComments record_field_decls))
in (braces_with_nesting uu____3934))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3933)))
in (

let uu____3944 = (p_typeDeclPrefix pre true lid bs typ_opt)
in ((uu____3944), (p_fields)))))
end
| FStar_Parser_AST.TyconVariant (lid, bs, typ_opt, ct_decls) -> begin
(

let p_constructorBranchAndComments = (fun uu____4005 -> (match (uu____4005) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let range = (

let uu____4031 = (

let uu____4032 = (FStar_Util.map_opt t_opt (fun t -> t.FStar_Parser_AST.range))
in (FStar_Util.dflt uid.FStar_Ident.idRange uu____4032))
in (FStar_Range.extend_to_end_of_line uu____4031))
in (with_comment p_constructorBranch ((uid), (t_opt), (doc_opt), (use_of)) range))
end))
in (

let datacon_doc = (fun uu____4058 -> (FStar_Pprint.separate_map FStar_Pprint.hardline p_constructorBranchAndComments ct_decls))
in (

let uu____4071 = (p_typeDeclPrefix pre true lid bs typ_opt)
in ((uu____4071), ((fun uu____4077 -> (

let uu____4078 = (datacon_doc ())
in (jump2 uu____4078))))))))
end))
and p_typeDeclPrefix : (FStar_Pprint.document * FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option)  ->  Prims.bool  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.knd FStar_Pervasives_Native.option  ->  FStar_Pprint.document = (fun uu____4079 eq1 lid bs typ_opt -> (match (uu____4079) with
| (kw, fsdoc_opt) -> begin
(

let maybe_with_fsdoc = (fun cont -> (

let lid_doc = (p_ident lid)
in (

let kw_lid = (

let uu____4113 = (FStar_Pprint.op_Hat_Slash_Hat kw lid_doc)
in (FStar_Pprint.group uu____4113))
in (match (fsdoc_opt) with
| FStar_Pervasives_Native.None -> begin
(cont kw_lid)
end
| FStar_Pervasives_Native.Some (fsdoc) -> begin
(

let uu____4115 = (

let uu____4118 = (

let uu____4121 = (p_fsdoc fsdoc)
in (

let uu____4122 = (

let uu____4125 = (cont lid_doc)
in (uu____4125)::[])
in (uu____4121)::uu____4122))
in (kw)::uu____4118)
in (FStar_Pprint.separate FStar_Pprint.hardline uu____4115))
end))))
in (

let typ = (

let maybe_eq = (match (eq1) with
| true -> begin
FStar_Pprint.equals
end
| uu____4128 -> begin
FStar_Pprint.empty
end)
in (match (typ_opt) with
| FStar_Pervasives_Native.None -> begin
maybe_eq
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____4130 = (

let uu____4131 = (

let uu____4132 = (p_typ false false t)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4132 maybe_eq))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4131))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4130))
end))
in (match ((Prims.op_Equality bs [])) with
| true -> begin
(maybe_with_fsdoc (fun n1 -> (prefix2 n1 typ)))
end
| uu____4138 -> begin
(

let binders = (p_binders_list true bs)
in (maybe_with_fsdoc (fun n1 -> (

let uu____4147 = (

let uu____4148 = (FStar_Pprint.flow break1 binders)
in (prefix2 n1 uu____4148))
in (prefix2 uu____4147 typ)))))
end)))
end))
and p_recordFieldDecl : Prims.bool  ->  (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option)  ->  FStar_Pprint.document = (fun ps uu____4150 -> (match (uu____4150) with
| (lid, t, doc_opt) -> begin
(

let uu____4166 = (

let uu____4167 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (

let uu____4168 = (

let uu____4169 = (p_lident lid)
in (

let uu____4170 = (

let uu____4171 = (p_typ ps false t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4171))
in (FStar_Pprint.op_Hat_Hat uu____4169 uu____4170)))
in (FStar_Pprint.op_Hat_Hat uu____4167 uu____4168)))
in (FStar_Pprint.group uu____4166))
end))
and p_constructorBranch : (FStar_Ident.ident * FStar_Parser_AST.term FStar_Pervasives_Native.option * FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option * Prims.bool)  ->  FStar_Pprint.document = (fun uu____4172 -> (match (uu____4172) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let sep = (match (use_of) with
| true -> begin
(str "of")
end
| uu____4198 -> begin
FStar_Pprint.colon
end)
in (

let uid_doc = (

let uu____4200 = (

let uu____4201 = (

let uu____4202 = (p_uident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4202))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4201))
in (FStar_Pprint.group uu____4200))
in (

let uu____4203 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (

let uu____4204 = (default_or_map uid_doc (fun t -> (

let uu____4208 = (

let uu____4209 = (

let uu____4210 = (

let uu____4211 = (

let uu____4212 = (p_typ false false t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4212))
in (FStar_Pprint.op_Hat_Hat sep uu____4211))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4210))
in (FStar_Pprint.op_Hat_Hat uid_doc uu____4209))
in (FStar_Pprint.group uu____4208))) t_opt)
in (FStar_Pprint.op_Hat_Hat uu____4203 uu____4204)))))
end))
and p_letlhs : FStar_Pprint.document  ->  (FStar_Parser_AST.pattern * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun kw uu____4214 -> (match (uu____4214) with
| (pat, uu____4220) -> begin
(

let uu____4221 = (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat1, (t, FStar_Pervasives_Native.None)) -> begin
(

let uu____4240 = (

let uu____4241 = (

let uu____4242 = (

let uu____4243 = (p_tmArrow p_tmNoEq t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4243))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4242))
in (FStar_Pprint.group uu____4241))
in ((pat1), (uu____4240)))
end
| FStar_Parser_AST.PatAscribed (pat1, (t, FStar_Pervasives_Native.Some (tac))) -> begin
(

let uu____4255 = (

let uu____4256 = (

let uu____4257 = (

let uu____4258 = (

let uu____4259 = (p_tmArrow p_tmNoEq t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4259))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4258))
in (FStar_Pprint.group uu____4257))
in (

let uu____4260 = (

let uu____4261 = (

let uu____4262 = (str "by")
in (

let uu____4263 = (

let uu____4264 = (p_atomicTerm tac)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4264))
in (FStar_Pprint.op_Hat_Hat uu____4262 uu____4263)))
in (FStar_Pprint.group uu____4261))
in (FStar_Pprint.op_Hat_Hat uu____4256 uu____4260)))
in ((pat1), (uu____4255)))
end
| uu____4265 -> begin
((pat), (FStar_Pprint.empty))
end)
in (match (uu____4221) with
| (pat1, ascr_doc) -> begin
(match (pat1.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____4269); FStar_Parser_AST.prange = uu____4270}, pats) -> begin
(

let uu____4280 = (

let uu____4281 = (

let uu____4282 = (

let uu____4283 = (p_lident x)
in (FStar_Pprint.op_Hat_Slash_Hat kw uu____4283))
in (FStar_Pprint.group uu____4282))
in (

let uu____4284 = (FStar_Pprint.flow_map break1 p_atomicPattern pats)
in (prefix2 uu____4281 uu____4284)))
in (prefix2_nonempty uu____4280 ascr_doc))
end
| uu____4285 -> begin
(

let uu____4286 = (

let uu____4287 = (

let uu____4288 = (

let uu____4289 = (p_tuplePattern pat1)
in (FStar_Pprint.op_Hat_Slash_Hat kw uu____4289))
in (FStar_Pprint.group uu____4288))
in (FStar_Pprint.op_Hat_Hat uu____4287 ascr_doc))
in (FStar_Pprint.group uu____4286))
end)
end))
end))
and p_letbinding : FStar_Pprint.document  ->  (FStar_Parser_AST.pattern * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun kw uu____4291 -> (match (uu____4291) with
| (pat, e) -> begin
(

let doc_pat = (p_letlhs kw ((pat), (e)))
in (

let doc_expr = (p_term false false e)
in (

let uu____4300 = (

let uu____4301 = (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals doc_expr)
in (FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____4301))
in (

let uu____4302 = (

let uu____4303 = (

let uu____4304 = (

let uu____4305 = (

let uu____4306 = (jump2 doc_expr)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____4306))
in (FStar_Pprint.group uu____4305))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4304))
in (FStar_Pprint.op_Hat_Hat doc_pat uu____4303))
in (FStar_Pprint.ifflat uu____4300 uu____4302)))))
end))
and p_newEffect : FStar_Parser_AST.effect_decl  ->  FStar_Pprint.document = (fun uu___119_4307 -> (match (uu___119_4307) with
| FStar_Parser_AST.RedefineEffect (lid, bs, t) -> begin
(p_effectRedefinition lid bs t)
end
| FStar_Parser_AST.DefineEffect (lid, bs, t, eff_decls) -> begin
(p_effectDefinition lid bs t eff_decls)
end))
and p_effectRedefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun uid bs t -> (

let uu____4332 = (p_uident uid)
in (

let uu____4333 = (p_binders true bs)
in (

let uu____4334 = (

let uu____4335 = (p_simpleTerm false false t)
in (prefix2 FStar_Pprint.equals uu____4335))
in (surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1") uu____4332 uu____4333 uu____4334)))))
and p_effectDefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun uid bs t eff_decls -> (

let binders = (p_binders true bs)
in (

let uu____4345 = (

let uu____4346 = (

let uu____4347 = (

let uu____4348 = (p_uident uid)
in (

let uu____4349 = (p_binders true bs)
in (

let uu____4350 = (

let uu____4351 = (p_typ false false t)
in (prefix2 FStar_Pprint.colon uu____4351))
in (surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1") uu____4348 uu____4349 uu____4350))))
in (FStar_Pprint.group uu____4347))
in (

let uu____4352 = (

let uu____4353 = (str "with")
in (

let uu____4354 = (

let uu____4355 = (

let uu____4356 = (

let uu____4357 = (

let uu____4358 = (

let uu____4359 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi FStar_Pprint.space)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4359))
in (separate_map_last uu____4358 p_effectDecl eff_decls))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4357))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4356))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4355))
in (FStar_Pprint.op_Hat_Hat uu____4353 uu____4354)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4346 uu____4352)))
in (braces_with_nesting uu____4345))))
and p_effectDecl : Prims.bool  ->  FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun ps d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (false, ((FStar_Parser_AST.TyconAbbrev (lid, [], FStar_Pervasives_Native.None, e), FStar_Pervasives_Native.None))::[]) -> begin
(

let uu____4390 = (

let uu____4391 = (p_lident lid)
in (

let uu____4392 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____4391 uu____4392)))
in (

let uu____4393 = (p_simpleTerm ps false e)
in (prefix2 uu____4390 uu____4393)))
end
| uu____4394 -> begin
(

let uu____4395 = (

let uu____4396 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "Not a declaration of an effect member... or at least I hope so : %s" uu____4396))
in (failwith uu____4395))
end))
and p_subEffect : FStar_Parser_AST.lift  ->  FStar_Pprint.document = (fun lift -> (

let lift_op_doc = (

let lifts = (match (lift.FStar_Parser_AST.lift_op) with
| FStar_Parser_AST.NonReifiableLift (t) -> begin
((("lift_wp"), (t)))::[]
end
| FStar_Parser_AST.ReifiableLift (t1, t2) -> begin
((("lift_wp"), (t1)))::((("lift"), (t2)))::[]
end
| FStar_Parser_AST.LiftForFree (t) -> begin
((("lift"), (t)))::[]
end)
in (

let p_lift = (fun ps uu____4458 -> (match (uu____4458) with
| (kwd, t) -> begin
(

let uu____4465 = (

let uu____4466 = (str kwd)
in (

let uu____4467 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____4466 uu____4467)))
in (

let uu____4468 = (p_simpleTerm ps false t)
in (prefix2 uu____4465 uu____4468)))
end))
in (separate_break_map_last FStar_Pprint.semi p_lift lifts)))
in (

let uu____4473 = (

let uu____4474 = (

let uu____4475 = (p_quident lift.FStar_Parser_AST.msource)
in (

let uu____4476 = (

let uu____4477 = (str "~>")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4477))
in (FStar_Pprint.op_Hat_Hat uu____4475 uu____4476)))
in (

let uu____4478 = (p_quident lift.FStar_Parser_AST.mdest)
in (prefix2 uu____4474 uu____4478)))
in (

let uu____4479 = (

let uu____4480 = (braces_with_nesting lift_op_doc)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4480))
in (FStar_Pprint.op_Hat_Hat uu____4473 uu____4479)))))
and p_qualifier : FStar_Parser_AST.qualifier  ->  FStar_Pprint.document = (fun uu___120_4481 -> (match (uu___120_4481) with
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
and p_qualifiers : FStar_Parser_AST.qualifiers  ->  FStar_Pprint.document = (fun qs -> (match (qs) with
| [] -> begin
FStar_Pprint.empty
end
| uu____4483 -> begin
(

let uu____4484 = (

let uu____4485 = (FStar_List.map p_qualifier qs)
in (FStar_Pprint.flow break1 uu____4485))
in (FStar_Pprint.op_Hat_Hat uu____4484 FStar_Pprint.hardline))
end))
and p_letqualifier : FStar_Parser_AST.let_qualifier  ->  FStar_Pprint.document = (fun uu___121_4488 -> (match (uu___121_4488) with
| FStar_Parser_AST.Rec -> begin
(

let uu____4489 = (str "rec")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4489))
end
| FStar_Parser_AST.Mutable -> begin
(

let uu____4490 = (str "mutable")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4490))
end
| FStar_Parser_AST.NoLetQualifier -> begin
FStar_Pprint.empty
end))
and p_aqual : FStar_Parser_AST.arg_qualifier  ->  FStar_Pprint.document = (fun uu___122_4491 -> (match (uu___122_4491) with
| FStar_Parser_AST.Implicit -> begin
(str "#")
end
| FStar_Parser_AST.Equality -> begin
(str "$")
end
| FStar_Parser_AST.Meta (t) -> begin
(

let uu____4493 = (str "#[")
in (

let uu____4494 = (

let uu____4495 = (p_term false false t)
in (

let uu____4496 = (str "]")
in (FStar_Pprint.op_Hat_Hat uu____4495 uu____4496)))
in (FStar_Pprint.op_Hat_Hat uu____4493 uu____4494)))
end))
and p_disjunctivePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr (pats) -> begin
(

let uu____4501 = (

let uu____4502 = (

let uu____4503 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space)
in (FStar_Pprint.op_Hat_Hat break1 uu____4503))
in (FStar_Pprint.separate_map uu____4502 p_tuplePattern pats))
in (FStar_Pprint.group uu____4501))
end
| uu____4504 -> begin
(p_tuplePattern p)
end))
and p_tuplePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTuple (pats, false) -> begin
(

let uu____4511 = (

let uu____4512 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map uu____4512 p_constructorPattern pats))
in (FStar_Pprint.group uu____4511))
end
| uu____4513 -> begin
(p_constructorPattern p)
end))
and p_constructorPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (maybe_cons_lid); FStar_Parser_AST.prange = uu____4516}, (hd1)::(tl1)::[]) when (FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid) -> begin
(

let uu____4521 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon)
in (

let uu____4522 = (p_constructorPattern hd1)
in (

let uu____4523 = (p_constructorPattern tl1)
in (infix0 uu____4521 uu____4522 uu____4523))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (uid); FStar_Parser_AST.prange = uu____4525}, pats) -> begin
(

let uu____4531 = (p_quident uid)
in (

let uu____4532 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (prefix2 uu____4531 uu____4532)))
end
| uu____4533 -> begin
(p_atomicPattern p)
end))
and p_atomicPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, (t, FStar_Pervasives_Native.None)) -> begin
(match (((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm))) with
| (FStar_Parser_AST.PatVar (lid, aqual), FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t1); FStar_Parser_AST.brange = uu____4549; FStar_Parser_AST.blevel = uu____4550; FStar_Parser_AST.aqual = uu____4551}, phi)) when (Prims.op_Equality lid.FStar_Ident.idText lid'.FStar_Ident.idText) -> begin
(

let uu____4559 = (

let uu____4560 = (p_ident lid)
in (p_refinement aqual uu____4560 t1 phi))
in (soft_parens_with_nesting uu____4559))
end
| (FStar_Parser_AST.PatWild, FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t1); FStar_Parser_AST.brange = uu____4562; FStar_Parser_AST.blevel = uu____4563; FStar_Parser_AST.aqual = uu____4564}, phi)) -> begin
(

let uu____4568 = (p_refinement FStar_Pervasives_Native.None FStar_Pprint.underscore t1 phi)
in (soft_parens_with_nesting uu____4568))
end
| uu____4569 -> begin
(

let uu____4574 = (

let uu____4575 = (p_tuplePattern pat)
in (

let uu____4576 = (

let uu____4577 = (p_tmEqNoRefinement t)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4577))
in (FStar_Pprint.op_Hat_Hat uu____4575 uu____4576)))
in (soft_parens_with_nesting uu____4574))
end)
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let uu____4581 = (separate_break_map FStar_Pprint.semi p_tuplePattern pats)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket uu____4581 FStar_Pprint.rbracket))
end
| FStar_Parser_AST.PatRecord (pats) -> begin
(

let p_recordFieldPat = (fun uu____4598 -> (match (uu____4598) with
| (lid, pat) -> begin
(

let uu____4605 = (p_qlident lid)
in (

let uu____4606 = (p_tuplePattern pat)
in (infix2 FStar_Pprint.equals uu____4605 uu____4606)))
end))
in (

let uu____4607 = (separate_break_map FStar_Pprint.semi p_recordFieldPat pats)
in (soft_braces_with_nesting uu____4607)))
end
| FStar_Parser_AST.PatTuple (pats, true) -> begin
(

let uu____4617 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (

let uu____4618 = (separate_break_map FStar_Pprint.comma p_constructorPattern pats)
in (

let uu____4619 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____4617 uu____4618 uu____4619))))
end
| FStar_Parser_AST.PatTvar (tv, arg_qualifier_opt) -> begin
(p_tvar tv)
end
| FStar_Parser_AST.PatOp (op) -> begin
(

let uu____4628 = (

let uu____4629 = (

let uu____4630 = (

let uu____4631 = (FStar_Ident.text_of_id op)
in (str uu____4631))
in (

let uu____4632 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat uu____4630 uu____4632)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4629))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4628))
end
| FStar_Parser_AST.PatWild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.PatConst (c) -> begin
(p_constant c)
end
| FStar_Parser_AST.PatVar (lid, aqual) -> begin
(

let uu____4640 = (FStar_Pprint.optional p_aqual aqual)
in (

let uu____4641 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat uu____4640 uu____4641)))
end
| FStar_Parser_AST.PatName (uid) -> begin
(p_quident uid)
end
| FStar_Parser_AST.PatOr (uu____4643) -> begin
(failwith "Inner or pattern !")
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (uu____4646); FStar_Parser_AST.prange = uu____4647}, uu____4648) -> begin
(

let uu____4653 = (p_tuplePattern p)
in (soft_parens_with_nesting uu____4653))
end
| FStar_Parser_AST.PatTuple (uu____4654, false) -> begin
(

let uu____4659 = (p_tuplePattern p)
in (soft_parens_with_nesting uu____4659))
end
| uu____4660 -> begin
(

let uu____4661 = (

let uu____4662 = (FStar_Parser_AST.pat_to_string p)
in (FStar_Util.format1 "Invalid pattern %s" uu____4662))
in (failwith uu____4661))
end))
and is_typ_tuple : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____4664}, uu____4665) -> begin
true
end
| uu____4670 -> begin
false
end))
and p_binder : Prims.bool  ->  FStar_Parser_AST.binder  ->  FStar_Pprint.document = (fun is_atomic b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (lid) -> begin
(

let uu____4674 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (

let uu____4675 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat uu____4674 uu____4675)))
end
| FStar_Parser_AST.TVariable (lid) -> begin
(p_lident lid)
end
| FStar_Parser_AST.Annotated (lid, t) -> begin
(

let doc1 = (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t1); FStar_Parser_AST.brange = uu____4682; FStar_Parser_AST.blevel = uu____4683; FStar_Parser_AST.aqual = uu____4684}, phi) when (Prims.op_Equality lid.FStar_Ident.idText lid'.FStar_Ident.idText) -> begin
(

let uu____4688 = (p_lident lid)
in (p_refinement b.FStar_Parser_AST.aqual uu____4688 t1 phi))
end
| uu____4689 -> begin
(

let t' = (

let uu____4691 = (is_typ_tuple t)
in (match (uu____4691) with
| true -> begin
(

let uu____4692 = (p_tmFormula t)
in (soft_parens_with_nesting uu____4692))
end
| uu____4693 -> begin
(p_tmFormula t)
end))
in (

let uu____4694 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (

let uu____4695 = (

let uu____4696 = (p_lident lid)
in (

let uu____4697 = (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon t')
in (FStar_Pprint.op_Hat_Hat uu____4696 uu____4697)))
in (FStar_Pprint.op_Hat_Hat uu____4694 uu____4695))))
end)
in (match (is_atomic) with
| true -> begin
(

let uu____4698 = (

let uu____4699 = (FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4699))
in (FStar_Pprint.group uu____4698))
end
| uu____4700 -> begin
(FStar_Pprint.group doc1)
end))
end
| FStar_Parser_AST.TAnnotated (uu____4701) -> begin
(failwith "Is this still used ?")
end
| FStar_Parser_AST.NoName (t) -> begin
(match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t1); FStar_Parser_AST.brange = uu____4708; FStar_Parser_AST.blevel = uu____4709; FStar_Parser_AST.aqual = uu____4710}, phi) -> begin
(match (is_atomic) with
| true -> begin
(

let uu____4714 = (

let uu____4715 = (

let uu____4716 = (p_refinement b.FStar_Parser_AST.aqual FStar_Pprint.underscore t1 phi)
in (FStar_Pprint.op_Hat_Hat uu____4716 FStar_Pprint.rparen))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4715))
in (FStar_Pprint.group uu____4714))
end
| uu____4717 -> begin
(

let uu____4718 = (p_refinement b.FStar_Parser_AST.aqual FStar_Pprint.underscore t1 phi)
in (FStar_Pprint.group uu____4718))
end)
end
| uu____4719 -> begin
(match (is_atomic) with
| true -> begin
(p_atomicTerm t)
end
| uu____4720 -> begin
(p_appTerm t)
end)
end)
end))
and p_refinement : FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Pprint.document  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun aqual_opt binder t phi -> (

let is_t_atomic = (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (uu____4728) -> begin
false
end
| FStar_Parser_AST.App (uu____4739) -> begin
false
end
| FStar_Parser_AST.Op (uu____4746) -> begin
false
end
| uu____4753 -> begin
true
end)
in (

let phi1 = (p_noSeqTerm false false phi)
in (

let jump_break = (match (is_t_atomic) with
| true -> begin
(Prims.parse_int "0")
end
| uu____4756 -> begin
(Prims.parse_int "1")
end)
in (

let uu____4757 = (

let uu____4758 = (FStar_Pprint.optional p_aqual aqual_opt)
in (

let uu____4759 = (FStar_Pprint.op_Hat_Hat binder FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat uu____4758 uu____4759)))
in (

let uu____4760 = (

let uu____4761 = (p_appTerm t)
in (

let uu____4762 = (

let uu____4763 = (

let uu____4764 = (

let uu____4765 = (soft_braces_with_nesting_tight phi1)
in (

let uu____4766 = (soft_braces_with_nesting phi1)
in (FStar_Pprint.ifflat uu____4765 uu____4766)))
in (FStar_Pprint.group uu____4764))
in (FStar_Pprint.jump (Prims.parse_int "2") jump_break uu____4763))
in (FStar_Pprint.op_Hat_Hat uu____4761 uu____4762)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4757 uu____4760)))))))
and p_binders_list : Prims.bool  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Pprint.document Prims.list = (fun is_atomic bs -> (FStar_List.map (p_binder is_atomic) bs))
and p_binders : Prims.bool  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Pprint.document = (fun is_atomic bs -> (

let uu____4777 = (p_binders_list is_atomic bs)
in (separate_or_flow break1 uu____4777)))
and text_of_id_or_underscore : FStar_Ident.ident  ->  FStar_Pprint.document = (fun lid -> (match ((FStar_Util.starts_with lid.FStar_Ident.idText FStar_Ident.reserved_prefix)) with
| true -> begin
FStar_Pprint.underscore
end
| uu____4781 -> begin
(

let uu____4782 = (FStar_Ident.text_of_id lid)
in (str uu____4782))
end))
and text_of_lid_or_underscore : FStar_Ident.lident  ->  FStar_Pprint.document = (fun lid -> (match ((FStar_Util.starts_with lid.FStar_Ident.ident.FStar_Ident.idText FStar_Ident.reserved_prefix)) with
| true -> begin
FStar_Pprint.underscore
end
| uu____4784 -> begin
(

let uu____4785 = (FStar_Ident.text_of_lid lid)
in (str uu____4785))
end))
and p_qlident : FStar_Ident.lid  ->  FStar_Pprint.document = (fun lid -> (text_of_lid_or_underscore lid))
and p_quident : FStar_Ident.lid  ->  FStar_Pprint.document = (fun lid -> (text_of_lid_or_underscore lid))
and p_ident : FStar_Ident.ident  ->  FStar_Pprint.document = (fun lid -> (text_of_id_or_underscore lid))
and p_lident : FStar_Ident.ident  ->  FStar_Pprint.document = (fun lid -> (text_of_id_or_underscore lid))
and p_uident : FStar_Ident.ident  ->  FStar_Pprint.document = (fun lid -> (text_of_id_or_underscore lid))
and p_tvar : FStar_Ident.ident  ->  FStar_Pprint.document = (fun lid -> (text_of_id_or_underscore lid))
and paren_if : Prims.bool  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun b -> (match (b) with
| true -> begin
soft_parens_with_nesting
end
| uu____4796 -> begin
(fun x -> x)
end))
and p_term : Prims.bool  ->  Prims.bool  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun ps pb e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Seq (e1, e2) -> begin
(

let uu____4803 = (

let uu____4804 = (

let uu____4805 = (p_noSeqTerm true false e1)
in (FStar_Pprint.op_Hat_Hat uu____4805 FStar_Pprint.semi))
in (FStar_Pprint.group uu____4804))
in (

let uu____4806 = (p_term ps pb e2)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4803 uu____4806)))
end
| FStar_Parser_AST.Bind (x, e1, e2) -> begin
(

let uu____4810 = (

let uu____4811 = (

let uu____4812 = (

let uu____4813 = (p_lident x)
in (

let uu____4814 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.long_left_arrow)
in (FStar_Pprint.op_Hat_Hat uu____4813 uu____4814)))
in (

let uu____4815 = (

let uu____4816 = (p_noSeqTerm true false e1)
in (

let uu____4817 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.semi)
in (FStar_Pprint.op_Hat_Hat uu____4816 uu____4817)))
in (op_Hat_Slash_Plus_Hat uu____4812 uu____4815)))
in (FStar_Pprint.group uu____4811))
in (

let uu____4818 = (p_term ps pb e2)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4810 uu____4818)))
end
| uu____4819 -> begin
(

let uu____4820 = (p_noSeqTerm ps pb e)
in (FStar_Pprint.group uu____4820))
end))
and p_noSeqTerm : Prims.bool  ->  Prims.bool  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun ps pb e -> (with_comment (p_noSeqTerm' ps pb) e e.FStar_Parser_AST.range))
and p_noSeqTerm' : Prims.bool  ->  Prims.bool  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun ps pb e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Ascribed (e1, t, FStar_Pervasives_Native.None) -> begin
(

let uu____4831 = (

let uu____4832 = (p_tmIff e1)
in (

let uu____4833 = (

let uu____4834 = (

let uu____4835 = (p_typ ps pb t)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4835))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4834))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4832 uu____4833)))
in (FStar_Pprint.group uu____4831))
end
| FStar_Parser_AST.Ascribed (e1, t, FStar_Pervasives_Native.Some (tac)) -> begin
(

let uu____4841 = (

let uu____4842 = (p_tmIff e1)
in (

let uu____4843 = (

let uu____4844 = (

let uu____4845 = (

let uu____4846 = (p_typ false false t)
in (

let uu____4847 = (

let uu____4848 = (str "by")
in (

let uu____4849 = (p_typ ps pb tac)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4848 uu____4849)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4846 uu____4847)))
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4845))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4844))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4842 uu____4843)))
in (FStar_Pprint.group uu____4841))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = ".()<-"; FStar_Ident.idRange = uu____4850}, (e1)::(e2)::(e3)::[]) -> begin
(

let uu____4856 = (

let uu____4857 = (

let uu____4858 = (

let uu____4859 = (p_atomicTermNotQUident e1)
in (

let uu____4860 = (

let uu____4861 = (

let uu____4862 = (

let uu____4863 = (p_term false false e2)
in (soft_parens_with_nesting uu____4863))
in (

let uu____4864 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat uu____4862 uu____4864)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4861))
in (FStar_Pprint.op_Hat_Hat uu____4859 uu____4860)))
in (FStar_Pprint.group uu____4858))
in (

let uu____4865 = (

let uu____4866 = (p_noSeqTerm ps pb e3)
in (jump2 uu____4866))
in (FStar_Pprint.op_Hat_Hat uu____4857 uu____4865)))
in (FStar_Pprint.group uu____4856))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = ".[]<-"; FStar_Ident.idRange = uu____4867}, (e1)::(e2)::(e3)::[]) -> begin
(

let uu____4873 = (

let uu____4874 = (

let uu____4875 = (

let uu____4876 = (p_atomicTermNotQUident e1)
in (

let uu____4877 = (

let uu____4878 = (

let uu____4879 = (

let uu____4880 = (p_term false false e2)
in (soft_brackets_with_nesting uu____4880))
in (

let uu____4881 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat uu____4879 uu____4881)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4878))
in (FStar_Pprint.op_Hat_Hat uu____4876 uu____4877)))
in (FStar_Pprint.group uu____4875))
in (

let uu____4882 = (

let uu____4883 = (p_noSeqTerm ps pb e3)
in (jump2 uu____4883))
in (FStar_Pprint.op_Hat_Hat uu____4874 uu____4882)))
in (FStar_Pprint.group uu____4873))
end
| FStar_Parser_AST.Requires (e1, wtf) -> begin
(

let uu____4891 = (

let uu____4892 = (str "requires")
in (

let uu____4893 = (p_typ ps pb e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4892 uu____4893)))
in (FStar_Pprint.group uu____4891))
end
| FStar_Parser_AST.Ensures (e1, wtf) -> begin
(

let uu____4901 = (

let uu____4902 = (str "ensures")
in (

let uu____4903 = (p_typ ps pb e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4902 uu____4903)))
in (FStar_Pprint.group uu____4901))
end
| FStar_Parser_AST.Attributes (es) -> begin
(

let uu____4907 = (

let uu____4908 = (str "attributes")
in (

let uu____4909 = (FStar_Pprint.separate_map break1 p_atomicTerm es)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4908 uu____4909)))
in (FStar_Pprint.group uu____4907))
end
| FStar_Parser_AST.If (e1, e2, e3) -> begin
(match ((is_unit e3)) with
| true -> begin
(

let uu____4913 = (

let uu____4914 = (

let uu____4915 = (str "if")
in (

let uu____4916 = (p_noSeqTerm false false e1)
in (op_Hat_Slash_Plus_Hat uu____4915 uu____4916)))
in (

let uu____4917 = (

let uu____4918 = (str "then")
in (

let uu____4919 = (p_noSeqTerm ps pb e2)
in (op_Hat_Slash_Plus_Hat uu____4918 uu____4919)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4914 uu____4917)))
in (FStar_Pprint.group uu____4913))
end
| uu____4920 -> begin
(

let e2_doc = (match (e2.FStar_Parser_AST.tm) with
| FStar_Parser_AST.If (uu____4922, uu____4923, e31) when (is_unit e31) -> begin
(

let uu____4925 = (p_noSeqTerm false false e2)
in (soft_parens_with_nesting uu____4925))
end
| uu____4926 -> begin
(p_noSeqTerm false false e2)
end)
in (

let uu____4927 = (

let uu____4928 = (

let uu____4929 = (str "if")
in (

let uu____4930 = (p_noSeqTerm false false e1)
in (op_Hat_Slash_Plus_Hat uu____4929 uu____4930)))
in (

let uu____4931 = (

let uu____4932 = (

let uu____4933 = (str "then")
in (op_Hat_Slash_Plus_Hat uu____4933 e2_doc))
in (

let uu____4934 = (

let uu____4935 = (str "else")
in (

let uu____4936 = (p_noSeqTerm ps pb e3)
in (op_Hat_Slash_Plus_Hat uu____4935 uu____4936)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4932 uu____4934)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4928 uu____4931)))
in (FStar_Pprint.group uu____4927)))
end)
end
| FStar_Parser_AST.TryWith (e1, branches) -> begin
(

let uu____4959 = (

let uu____4960 = (

let uu____4961 = (

let uu____4962 = (str "try")
in (

let uu____4963 = (p_noSeqTerm false false e1)
in (prefix2 uu____4962 uu____4963)))
in (

let uu____4964 = (

let uu____4965 = (str "with")
in (

let uu____4966 = (separate_map_last FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4965 uu____4966)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4961 uu____4964)))
in (FStar_Pprint.group uu____4960))
in (

let uu____4975 = (paren_if (ps || pb))
in (uu____4975 uu____4959)))
end
| FStar_Parser_AST.Match (e1, branches) -> begin
(

let uu____5002 = (

let uu____5003 = (

let uu____5004 = (

let uu____5005 = (str "match")
in (

let uu____5006 = (p_noSeqTerm false false e1)
in (

let uu____5007 = (str "with")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____5005 uu____5006 uu____5007))))
in (

let uu____5008 = (separate_map_last FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5004 uu____5008)))
in (FStar_Pprint.group uu____5003))
in (

let uu____5017 = (paren_if (ps || pb))
in (uu____5017 uu____5002)))
end
| FStar_Parser_AST.LetOpen (uid, e1) -> begin
(

let uu____5024 = (

let uu____5025 = (

let uu____5026 = (

let uu____5027 = (str "let open")
in (

let uu____5028 = (p_quident uid)
in (

let uu____5029 = (str "in")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____5027 uu____5028 uu____5029))))
in (

let uu____5030 = (p_term false pb e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5026 uu____5030)))
in (FStar_Pprint.group uu____5025))
in (

let uu____5031 = (paren_if ps)
in (uu____5031 uu____5024)))
end
| FStar_Parser_AST.Let (q, lbs, e1) -> begin
(

let p_lb = (fun q1 uu____5095 is_last -> (match (uu____5095) with
| (a, (pat, e2)) -> begin
(

let attrs = (p_attrs_opt a)
in (

let doc_let_or_and = (match (q1) with
| FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec) -> begin
(

let uu____5128 = (

let uu____5129 = (str "let")
in (

let uu____5130 = (str "rec")
in (FStar_Pprint.op_Hat_Slash_Hat uu____5129 uu____5130)))
in (FStar_Pprint.group uu____5128))
end
| FStar_Pervasives_Native.Some (FStar_Parser_AST.NoLetQualifier) -> begin
(str "let")
end
| uu____5131 -> begin
(str "and")
end)
in (

let doc_pat = (p_letlhs doc_let_or_and ((pat), (e2)))
in (

let doc_expr = (p_term false false e2)
in (

let uu____5136 = (match (is_last) with
| true -> begin
(

let uu____5137 = (FStar_Pprint.flow break1 ((doc_pat)::(FStar_Pprint.equals)::[]))
in (

let uu____5138 = (str "in")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____5137 doc_expr uu____5138)))
end
| uu____5139 -> begin
(

let uu____5140 = (FStar_Pprint.flow break1 ((doc_pat)::(FStar_Pprint.equals)::(doc_expr)::[]))
in (FStar_Pprint.hang (Prims.parse_int "2") uu____5140))
end)
in (FStar_Pprint.op_Hat_Hat attrs uu____5136))))))
end))
in (

let l = (FStar_List.length lbs)
in (

let lbs_docs = (FStar_List.mapi (fun i lb -> (match ((Prims.op_Equality i (Prims.parse_int "0"))) with
| true -> begin
(

let uu____5186 = (p_lb (FStar_Pervasives_Native.Some (q)) lb (Prims.op_Equality i (l - (Prims.parse_int "1"))))
in (FStar_Pprint.group uu____5186))
end
| uu____5193 -> begin
(

let uu____5194 = (p_lb FStar_Pervasives_Native.None lb (Prims.op_Equality i (l - (Prims.parse_int "1"))))
in (FStar_Pprint.group uu____5194))
end)) lbs)
in (

let lbs_doc = (

let uu____5202 = (FStar_Pprint.separate break1 lbs_docs)
in (FStar_Pprint.group uu____5202))
in (

let uu____5203 = (

let uu____5204 = (

let uu____5205 = (

let uu____5206 = (p_term false pb e1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5206))
in (FStar_Pprint.op_Hat_Hat lbs_doc uu____5205))
in (FStar_Pprint.group uu____5204))
in (

let uu____5207 = (paren_if ps)
in (uu____5207 uu____5203)))))))
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, typ_opt); FStar_Parser_AST.prange = uu____5214})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, branches); FStar_Parser_AST.range = uu____5217; FStar_Parser_AST.level = uu____5218}) when (matches_var maybe_x x) -> begin
(

let uu____5245 = (

let uu____5246 = (

let uu____5247 = (str "function")
in (

let uu____5248 = (separate_map_last FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5247 uu____5248)))
in (FStar_Pprint.group uu____5246))
in (

let uu____5257 = (paren_if (ps || pb))
in (uu____5257 uu____5245)))
end
| FStar_Parser_AST.Quote (e1, FStar_Parser_AST.Dynamic) -> begin
(

let uu____5263 = (

let uu____5264 = (str "quote")
in (

let uu____5265 = (p_noSeqTerm ps pb e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5264 uu____5265)))
in (FStar_Pprint.group uu____5263))
end
| FStar_Parser_AST.Quote (e1, FStar_Parser_AST.Static) -> begin
(

let uu____5267 = (

let uu____5268 = (str "`")
in (

let uu____5269 = (p_noSeqTerm ps pb e1)
in (FStar_Pprint.op_Hat_Hat uu____5268 uu____5269)))
in (FStar_Pprint.group uu____5267))
end
| FStar_Parser_AST.VQuote (e1) -> begin
(

let uu____5271 = (

let uu____5272 = (str "`%")
in (

let uu____5273 = (p_noSeqTerm ps pb e1)
in (FStar_Pprint.op_Hat_Hat uu____5272 uu____5273)))
in (FStar_Pprint.group uu____5271))
end
| FStar_Parser_AST.Antiquote (false, e1) -> begin
(

let uu____5275 = (

let uu____5276 = (str "`#")
in (

let uu____5277 = (p_noSeqTerm ps pb e1)
in (FStar_Pprint.op_Hat_Hat uu____5276 uu____5277)))
in (FStar_Pprint.group uu____5275))
end
| FStar_Parser_AST.Antiquote (true, e1) -> begin
(

let uu____5279 = (

let uu____5280 = (str "`@")
in (

let uu____5281 = (p_noSeqTerm ps pb e1)
in (FStar_Pprint.op_Hat_Hat uu____5280 uu____5281)))
in (FStar_Pprint.group uu____5279))
end
| uu____5282 -> begin
(p_typ ps pb e)
end))
and p_attrs_opt : FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option  ->  FStar_Pprint.document = (fun uu___123_5283 -> (match (uu___123_5283) with
| FStar_Pervasives_Native.None -> begin
FStar_Pprint.empty
end
| FStar_Pervasives_Native.Some (terms) -> begin
(

let uu____5295 = (

let uu____5296 = (str "[@")
in (

let uu____5297 = (

let uu____5298 = (FStar_Pprint.separate_map break1 p_atomicTerm terms)
in (

let uu____5299 = (str "]")
in (FStar_Pprint.op_Hat_Slash_Hat uu____5298 uu____5299)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____5296 uu____5297)))
in (FStar_Pprint.group uu____5295))
end))
and p_typ : Prims.bool  ->  Prims.bool  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun ps pb e -> (with_comment (p_typ' ps pb) e e.FStar_Parser_AST.range))
and p_typ' : Prims.bool  ->  Prims.bool  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun ps pb e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.QForall (bs, trigger, e1) -> begin
(

let binders_doc = (p_binders true bs)
in (

let term_doc = (p_noSeqTerm ps pb e1)
in (match (trigger) with
| [] -> begin
(

let uu____5325 = (

let uu____5326 = (

let uu____5327 = (p_quantifier e)
in (FStar_Pprint.op_Hat_Hat uu____5327 FStar_Pprint.space))
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") uu____5326 binders_doc FStar_Pprint.dot))
in (prefix2 uu____5325 term_doc))
end
| pats -> begin
(

let uu____5333 = (

let uu____5334 = (

let uu____5335 = (

let uu____5336 = (

let uu____5337 = (p_quantifier e)
in (FStar_Pprint.op_Hat_Hat uu____5337 FStar_Pprint.space))
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") uu____5336 binders_doc FStar_Pprint.dot))
in (

let uu____5338 = (p_trigger trigger)
in (prefix2 uu____5335 uu____5338)))
in (FStar_Pprint.group uu____5334))
in (prefix2 uu____5333 term_doc))
end)))
end
| FStar_Parser_AST.QExists (bs, trigger, e1) -> begin
(

let binders_doc = (p_binders true bs)
in (

let term_doc = (p_noSeqTerm ps pb e1)
in (match (trigger) with
| [] -> begin
(

let uu____5358 = (

let uu____5359 = (

let uu____5360 = (p_quantifier e)
in (FStar_Pprint.op_Hat_Hat uu____5360 FStar_Pprint.space))
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") uu____5359 binders_doc FStar_Pprint.dot))
in (prefix2 uu____5358 term_doc))
end
| pats -> begin
(

let uu____5366 = (

let uu____5367 = (

let uu____5368 = (

let uu____5369 = (

let uu____5370 = (p_quantifier e)
in (FStar_Pprint.op_Hat_Hat uu____5370 FStar_Pprint.space))
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") uu____5369 binders_doc FStar_Pprint.dot))
in (

let uu____5371 = (p_trigger trigger)
in (prefix2 uu____5368 uu____5371)))
in (FStar_Pprint.group uu____5367))
in (prefix2 uu____5366 term_doc))
end)))
end
| uu____5372 -> begin
(p_simpleTerm ps pb e)
end))
and p_quantifier : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.QForall (uu____5374) -> begin
(str "forall")
end
| FStar_Parser_AST.QExists (uu____5387) -> begin
(str "exists")
end
| uu____5400 -> begin
(failwith "Imposible : p_quantifier called on a non-quantifier term")
end))
and p_trigger : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun uu___124_5401 -> (match (uu___124_5401) with
| [] -> begin
FStar_Pprint.empty
end
| pats -> begin
(

let uu____5413 = (

let uu____5414 = (

let uu____5415 = (

let uu____5416 = (str "pattern")
in (

let uu____5417 = (

let uu____5418 = (

let uu____5419 = (p_disjunctivePats pats)
in (FStar_Pprint.jump (Prims.parse_int "2") (Prims.parse_int "0") uu____5419))
in (FStar_Pprint.op_Hat_Hat uu____5418 FStar_Pprint.rbrace))
in (FStar_Pprint.op_Hat_Slash_Hat uu____5416 uu____5417)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5415))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____5414))
in (FStar_Pprint.group uu____5413))
end))
and p_disjunctivePats : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun pats -> (

let uu____5425 = (str "\\/")
in (FStar_Pprint.separate_map uu____5425 p_conjunctivePats pats)))
and p_conjunctivePats : FStar_Parser_AST.term Prims.list  ->  FStar_Pprint.document = (fun pats -> (

let uu____5431 = (

let uu____5432 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (FStar_Pprint.separate_map uu____5432 p_appTerm pats))
in (FStar_Pprint.group uu____5431)))
and p_simpleTerm : Prims.bool  ->  Prims.bool  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun ps pb e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Abs (pats, e1) -> begin
(

let uu____5442 = (

let uu____5443 = (

let uu____5444 = (str "fun")
in (

let uu____5445 = (

let uu____5446 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5446 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat uu____5444 uu____5445)))
in (

let uu____5447 = (p_term false pb e1)
in (op_Hat_Slash_Plus_Hat uu____5443 uu____5447)))
in (

let uu____5448 = (paren_if ps)
in (uu____5448 uu____5442)))
end
| uu____5453 -> begin
(p_tmIff e)
end))
and p_maybeFocusArrow : Prims.bool  ->  FStar_Pprint.document = (fun b -> (match (b) with
| true -> begin
(str "~>")
end
| uu____5455 -> begin
FStar_Pprint.rarrow
end))
and p_patternBranch : Prims.bool  ->  (FStar_Parser_AST.pattern * FStar_Parser_AST.term FStar_Pervasives_Native.option * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun pb uu____5457 -> (match (uu____5457) with
| (pat, when_opt, e) -> begin
(

let one_pattern_branch = (fun p -> (

let branch = (match (when_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5480 = (

let uu____5481 = (

let uu____5482 = (

let uu____5483 = (p_tuplePattern p)
in (

let uu____5484 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rarrow)
in (FStar_Pprint.op_Hat_Hat uu____5483 uu____5484)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5482))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5481))
in (FStar_Pprint.group uu____5480))
end
| FStar_Pervasives_Native.Some (f) -> begin
(

let uu____5486 = (

let uu____5487 = (

let uu____5488 = (

let uu____5489 = (

let uu____5490 = (

let uu____5491 = (p_tuplePattern p)
in (

let uu____5492 = (str "when")
in (FStar_Pprint.op_Hat_Slash_Hat uu____5491 uu____5492)))
in (FStar_Pprint.group uu____5490))
in (

let uu____5493 = (

let uu____5494 = (

let uu____5497 = (p_tmFormula f)
in (uu____5497)::(FStar_Pprint.rarrow)::[])
in (FStar_Pprint.flow break1 uu____5494))
in (FStar_Pprint.op_Hat_Slash_Hat uu____5489 uu____5493)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5488))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5487))
in (FStar_Pprint.hang (Prims.parse_int "2") uu____5486))
end)
in (

let uu____5498 = (

let uu____5499 = (p_term false pb e)
in (op_Hat_Slash_Plus_Hat branch uu____5499))
in (FStar_Pprint.group uu____5498))))
in (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr (pats) -> begin
(match ((FStar_List.rev pats)) with
| (hd1)::tl1 -> begin
(

let last_pat_branch = (one_pattern_branch hd1)
in (

let uu____5508 = (

let uu____5509 = (

let uu____5510 = (

let uu____5511 = (

let uu____5512 = (

let uu____5513 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space)
in (FStar_Pprint.op_Hat_Hat break1 uu____5513))
in (FStar_Pprint.separate_map uu____5512 p_tuplePattern (FStar_List.rev tl1)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____5511 last_pat_branch))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5510))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5509))
in (FStar_Pprint.group uu____5508)))
end
| [] -> begin
(failwith "Impossible: disjunctive pattern can\'t be empty")
end)
end
| uu____5514 -> begin
(one_pattern_branch pat)
end))
end))
and p_tmIff : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5516}, (e1)::(e2)::[]) -> begin
(

let uu____5521 = (str "<==>")
in (

let uu____5522 = (p_tmImplies e1)
in (

let uu____5523 = (p_tmIff e2)
in (infix0 uu____5521 uu____5522 uu____5523))))
end
| uu____5524 -> begin
(p_tmImplies e)
end))
and p_tmImplies : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5526}, (e1)::(e2)::[]) -> begin
(

let uu____5531 = (str "==>")
in (

let uu____5532 = (p_tmArrow p_tmFormula e1)
in (

let uu____5533 = (p_tmImplies e2)
in (infix0 uu____5531 uu____5532 uu____5533))))
end
| uu____5534 -> begin
(p_tmArrow p_tmFormula e)
end))
and p_tmArrow : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_Tm e -> (

let terms = (p_tmArrow' p_Tm e)
in (

let uu____5542 = (FStar_List.splitAt ((FStar_List.length terms) - (Prims.parse_int "1")) terms)
in (match (uu____5542) with
| (terms', last1) -> begin
(

let last_op = (match (((FStar_List.length terms) > (Prims.parse_int "1"))) with
| true -> begin
(FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rarrow)
end
| uu____5562 -> begin
FStar_Pprint.empty
end)
in (match ((FStar_List.length terms)) with
| _0_8 when (_0_8 = (Prims.parse_int "1")) -> begin
(FStar_List.hd terms)
end
| uu____5563 -> begin
(

let uu____5564 = (

let uu____5565 = (

let uu____5566 = (

let uu____5567 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5567))
in (FStar_Pprint.separate uu____5566 terms))
in (

let uu____5568 = (

let uu____5569 = (

let uu____5570 = (

let uu____5571 = (

let uu____5572 = (

let uu____5573 = (

let uu____5574 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5574))
in (FStar_Pprint.separate uu____5573 terms'))
in (FStar_Pprint.op_Hat_Hat uu____5572 last_op))
in (

let uu____5575 = (

let uu____5576 = (

let uu____5577 = (

let uu____5578 = (

let uu____5579 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5579))
in (FStar_Pprint.separate uu____5578 terms'))
in (FStar_Pprint.op_Hat_Hat uu____5577 last_op))
in (jump2 uu____5576))
in (FStar_Pprint.ifflat uu____5571 uu____5575)))
in (FStar_Pprint.group uu____5570))
in (

let uu____5580 = (FStar_List.hd last1)
in (prefix2 uu____5569 uu____5580)))
in (FStar_Pprint.ifflat uu____5565 uu____5568)))
in (FStar_Pprint.group uu____5564))
end))
end))))
and p_tmArrow' : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document Prims.list = (fun p_Tm e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Product (bs, tgt) -> begin
(

let uu____5593 = (FStar_List.map (fun b -> (p_binder false b)) bs)
in (

let uu____5598 = (p_tmArrow' p_Tm tgt)
in (FStar_List.append uu____5593 uu____5598)))
end
| uu____5601 -> begin
(

let uu____5602 = (p_Tm e)
in (uu____5602)::[])
end))
and p_tmFormula : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let conj = (

let uu____5605 = (

let uu____5606 = (str "/\\")
in (FStar_Pprint.op_Hat_Hat uu____5606 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5605))
in (

let disj = (

let uu____5608 = (

let uu____5609 = (str "\\/")
in (FStar_Pprint.op_Hat_Hat uu____5609 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5608))
in (

let formula = (p_tmDisjunction e)
in (FStar_Pprint.flow_map disj (fun d -> (FStar_Pprint.flow_map conj (fun x -> (FStar_Pprint.group x)) d)) formula)))))
and p_tmDisjunction : FStar_Parser_AST.term  ->  FStar_Pprint.document Prims.list Prims.list = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5628}, (e1)::(e2)::[]) -> begin
(

let uu____5633 = (p_tmDisjunction e1)
in (

let uu____5638 = (

let uu____5643 = (p_tmConjunction e2)
in (uu____5643)::[])
in (FStar_List.append uu____5633 uu____5638)))
end
| uu____5652 -> begin
(

let uu____5653 = (p_tmConjunction e)
in (uu____5653)::[])
end))
and p_tmConjunction : FStar_Parser_AST.term  ->  FStar_Pprint.document Prims.list = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5663}, (e1)::(e2)::[]) -> begin
(

let uu____5668 = (p_tmConjunction e1)
in (

let uu____5671 = (

let uu____5674 = (p_tmTuple e2)
in (uu____5674)::[])
in (FStar_List.append uu____5668 uu____5671)))
end
| uu____5675 -> begin
(

let uu____5676 = (p_tmTuple e)
in (uu____5676)::[])
end))
and p_tmTuple : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_tmTuple' e e.FStar_Parser_AST.range))
and p_tmTuple' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (lid, args) when (is_tuple_constructor lid) -> begin
(

let uu____5693 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map uu____5693 (fun uu____5701 -> (match (uu____5701) with
| (e1, uu____5707) -> begin
(p_tmEq e1)
end)) args))
end
| uu____5708 -> begin
(p_tmEq e)
end))
and paren_if_gt : Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun curr mine doc1 -> (match ((mine <= curr)) with
| true -> begin
doc1
end
| uu____5712 -> begin
(

let uu____5713 = (

let uu____5714 = (FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5714))
in (FStar_Pprint.group uu____5713))
end))
and p_tmEqWith : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_X e -> (

let n1 = (max_level (FStar_List.append ((colon_equals)::(pipe_right)::[]) operatorInfix0ad12))
in (p_tmEqWith' p_X n1 e)))
and p_tmEqWith' : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_X curr e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (((is_operatorInfix0ad12 op) || (

let uu____5731 = (FStar_Ident.text_of_id op)
in (Prims.op_Equality uu____5731 "="))) || (

let uu____5733 = (FStar_Ident.text_of_id op)
in (Prims.op_Equality uu____5733 "|>"))) -> begin
(

let op1 = (FStar_Ident.text_of_id op)
in (

let uu____5735 = (levels op1)
in (match (uu____5735) with
| (left1, mine, right1) -> begin
(

let uu____5745 = (

let uu____5746 = (FStar_All.pipe_left str op1)
in (

let uu____5747 = (p_tmEqWith' p_X left1 e1)
in (

let uu____5748 = (p_tmEqWith' p_X right1 e2)
in (infix0 uu____5746 uu____5747 uu____5748))))
in (paren_if_gt curr mine uu____5745))
end)))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5749}, (e1)::(e2)::[]) -> begin
(

let uu____5754 = (

let uu____5755 = (p_tmEqWith p_X e1)
in (

let uu____5756 = (

let uu____5757 = (

let uu____5758 = (

let uu____5759 = (p_tmEqWith p_X e2)
in (op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5759))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5758))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5757))
in (FStar_Pprint.op_Hat_Hat uu____5755 uu____5756)))
in (FStar_Pprint.group uu____5754))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5760}, (e1)::[]) -> begin
(

let uu____5764 = (levels "-")
in (match (uu____5764) with
| (left1, mine, right1) -> begin
(

let uu____5774 = (p_tmEqWith' p_X mine e1)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5774))
end))
end
| uu____5775 -> begin
(p_tmNoEqWith p_X e)
end))
and p_tmNoEqWith : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_X e -> (

let n1 = (max_level ((colon_colon)::(amp)::(opinfix3)::(opinfix4)::[]))
in (p_tmNoEqWith' false p_X n1 e)))
and p_tmNoEqWith' : Prims.bool  ->  (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun inside_tuple p_X curr e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (lid, ((e1, uu____5819))::((e2, uu____5821))::[]) when ((FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) && (

let uu____5841 = (is_list e)
in (not (uu____5841)))) -> begin
(

let op = "::"
in (

let uu____5843 = (levels op)
in (match (uu____5843) with
| (left1, mine, right1) -> begin
(

let uu____5853 = (

let uu____5854 = (str op)
in (

let uu____5855 = (p_tmNoEqWith' false p_X left1 e1)
in (

let uu____5856 = (p_tmNoEqWith' false p_X right1 e2)
in (infix0 uu____5854 uu____5855 uu____5856))))
in (paren_if_gt curr mine uu____5853))
end)))
end
| FStar_Parser_AST.Sum (binders, res) -> begin
(

let op = "&"
in (

let uu____5864 = (levels op)
in (match (uu____5864) with
| (left1, mine, right1) -> begin
(

let p_dsumfst = (fun b -> (

let uu____5880 = (p_binder false b)
in (

let uu____5881 = (

let uu____5882 = (

let uu____5883 = (str op)
in (FStar_Pprint.op_Hat_Hat uu____5883 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5882))
in (FStar_Pprint.op_Hat_Hat uu____5880 uu____5881))))
in (

let uu____5884 = (

let uu____5885 = (FStar_Pprint.concat_map p_dsumfst binders)
in (

let uu____5886 = (p_tmNoEqWith' false p_X right1 res)
in (FStar_Pprint.op_Hat_Hat uu____5885 uu____5886)))
in (paren_if_gt curr mine uu____5884)))
end)))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____5887}, (e1)::(e2)::[]) when (FStar_ST.op_Bang unfold_tuples) -> begin
(

let op = "*"
in (

let uu____5912 = (levels op)
in (match (uu____5912) with
| (left1, mine, right1) -> begin
(match (inside_tuple) with
| true -> begin
(

let uu____5922 = (str op)
in (

let uu____5923 = (p_tmNoEqWith' true p_X left1 e1)
in (

let uu____5924 = (p_tmNoEqWith' true p_X right1 e2)
in (infix0 uu____5922 uu____5923 uu____5924))))
end
| uu____5925 -> begin
(

let uu____5926 = (

let uu____5927 = (str op)
in (

let uu____5928 = (p_tmNoEqWith' true p_X left1 e1)
in (

let uu____5929 = (p_tmNoEqWith' true p_X right1 e2)
in (infix0 uu____5927 uu____5928 uu____5929))))
in (paren_if_gt curr mine uu____5926))
end)
end)))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (is_operatorInfix34 op) -> begin
(

let op1 = (FStar_Ident.text_of_id op)
in (

let uu____5936 = (levels op1)
in (match (uu____5936) with
| (left1, mine, right1) -> begin
(

let uu____5946 = (

let uu____5947 = (str op1)
in (

let uu____5948 = (p_tmNoEqWith' false p_X left1 e1)
in (

let uu____5949 = (p_tmNoEqWith' false p_X right1 e2)
in (infix0 uu____5947 uu____5948 uu____5949))))
in (paren_if_gt curr mine uu____5946))
end)))
end
| FStar_Parser_AST.Record (with_opt, record_fields) -> begin
(

let uu____5968 = (

let uu____5969 = (default_or_map FStar_Pprint.empty p_with_clause with_opt)
in (

let uu____5970 = (

let uu____5971 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (separate_map_last uu____5971 p_simpleDef record_fields))
in (FStar_Pprint.op_Hat_Hat uu____5969 uu____5970)))
in (braces_with_nesting uu____5968))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____5976}, (e1)::[]) -> begin
(

let uu____5980 = (

let uu____5981 = (str "~")
in (

let uu____5982 = (p_atomicTerm e1)
in (FStar_Pprint.op_Hat_Hat uu____5981 uu____5982)))
in (FStar_Pprint.group uu____5980))
end
| FStar_Parser_AST.Paren (p) when inside_tuple -> begin
(match (p.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____5984}, (e1)::(e2)::[]) -> begin
(

let op = "*"
in (

let uu____5990 = (levels op)
in (match (uu____5990) with
| (left1, mine, right1) -> begin
(

let uu____6000 = (

let uu____6001 = (str op)
in (

let uu____6002 = (p_tmNoEqWith' true p_X left1 e1)
in (

let uu____6003 = (p_tmNoEqWith' true p_X right1 e2)
in (infix0 uu____6001 uu____6002 uu____6003))))
in (paren_if_gt curr mine uu____6000))
end)))
end
| uu____6004 -> begin
(p_X e)
end)
end
| uu____6005 -> begin
(p_X e)
end))
and p_tmEqNoRefinement : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_tmEqWith p_appTerm e))
and p_tmEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_tmEqWith p_tmRefinement e))
and p_tmNoEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_tmNoEqWith p_tmRefinement e))
and p_tmRefinement : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.NamedTyp (lid, e1) -> begin
(

let uu____6012 = (

let uu____6013 = (p_lident lid)
in (

let uu____6014 = (

let uu____6015 = (p_appTerm e1)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6015))
in (FStar_Pprint.op_Hat_Slash_Hat uu____6013 uu____6014)))
in (FStar_Pprint.group uu____6012))
end
| FStar_Parser_AST.Refine (b, phi) -> begin
(p_refinedBinder b phi)
end
| uu____6018 -> begin
(p_appTerm e)
end))
and p_with_clause : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____6020 = (p_appTerm e)
in (

let uu____6021 = (

let uu____6022 = (

let uu____6023 = (str "with")
in (FStar_Pprint.op_Hat_Hat uu____6023 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6022))
in (FStar_Pprint.op_Hat_Hat uu____6020 uu____6021))))
and p_refinedBinder : FStar_Parser_AST.binder  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun b phi -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (lid, t) -> begin
(

let uu____6028 = (p_lident lid)
in (p_refinement b.FStar_Parser_AST.aqual uu____6028 t phi))
end
| FStar_Parser_AST.TAnnotated (uu____6029) -> begin
(failwith "Is this still used ?")
end
| FStar_Parser_AST.Variable (uu____6034) -> begin
(

let uu____6035 = (

let uu____6036 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" uu____6036))
in (failwith uu____6035))
end
| FStar_Parser_AST.TVariable (uu____6037) -> begin
(

let uu____6038 = (

let uu____6039 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" uu____6039))
in (failwith uu____6038))
end
| FStar_Parser_AST.NoName (uu____6040) -> begin
(

let uu____6041 = (

let uu____6042 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" uu____6042))
in (failwith uu____6041))
end))
and p_simpleDef : Prims.bool  ->  (FStar_Ident.lid * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun ps uu____6044 -> (match (uu____6044) with
| (lid, e) -> begin
(

let uu____6051 = (

let uu____6052 = (p_qlident lid)
in (

let uu____6053 = (

let uu____6054 = (p_noSeqTerm ps false e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____6054))
in (FStar_Pprint.op_Hat_Slash_Hat uu____6052 uu____6053)))
in (FStar_Pprint.group uu____6051))
end))
and p_appTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App (uu____6056) when (is_general_application e) -> begin
(

let uu____6063 = (head_and_args e)
in (match (uu____6063) with
| (head1, args) -> begin
(

let uu____6088 = (

let uu____6099 = (FStar_ST.op_Bang should_print_fs_typ_app)
in (match (uu____6099) with
| true -> begin
(

let uu____6129 = (FStar_Util.take (fun uu____6153 -> (match (uu____6153) with
| (uu____6158, aq) -> begin
(Prims.op_Equality aq FStar_Parser_AST.FsTypApp)
end)) args)
in (match (uu____6129) with
| (fs_typ_args, args1) -> begin
(

let uu____6196 = (

let uu____6197 = (p_indexingTerm head1)
in (

let uu____6198 = (

let uu____6199 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (soft_surround_map_or_flow (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.empty FStar_Pprint.langle uu____6199 FStar_Pprint.rangle p_fsTypArg fs_typ_args))
in (FStar_Pprint.op_Hat_Hat uu____6197 uu____6198)))
in ((uu____6196), (args1)))
end))
end
| uu____6210 -> begin
(

let uu____6211 = (p_indexingTerm head1)
in ((uu____6211), (args)))
end))
in (match (uu____6088) with
| (head_doc, args1) -> begin
(

let uu____6232 = (

let uu____6233 = (FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space)
in (soft_surround_map_or_flow (Prims.parse_int "2") (Prims.parse_int "0") head_doc uu____6233 break1 FStar_Pprint.empty p_argTerm args1))
in (FStar_Pprint.group uu____6232))
end))
end))
end
| FStar_Parser_AST.Construct (lid, args) when ((is_general_construction e) && (

let uu____6253 = (is_dtuple_constructor lid)
in (not (uu____6253)))) -> begin
(match (args) with
| [] -> begin
(p_quident lid)
end
| (arg)::[] -> begin
(

let uu____6271 = (

let uu____6272 = (p_quident lid)
in (

let uu____6273 = (p_argTerm arg)
in (FStar_Pprint.op_Hat_Slash_Hat uu____6272 uu____6273)))
in (FStar_Pprint.group uu____6271))
end
| (hd1)::tl1 -> begin
(

let uu____6290 = (

let uu____6291 = (

let uu____6292 = (

let uu____6293 = (p_quident lid)
in (

let uu____6294 = (p_argTerm hd1)
in (prefix2 uu____6293 uu____6294)))
in (FStar_Pprint.group uu____6292))
in (

let uu____6295 = (

let uu____6296 = (FStar_Pprint.separate_map break1 p_argTerm tl1)
in (jump2 uu____6296))
in (FStar_Pprint.op_Hat_Hat uu____6291 uu____6295)))
in (FStar_Pprint.group uu____6290))
end)
end
| uu____6301 -> begin
(p_indexingTerm e)
end))
and p_argTerm : (FStar_Parser_AST.term * FStar_Parser_AST.imp)  ->  FStar_Pprint.document = (fun arg_imp -> (match (arg_imp) with
| (u, FStar_Parser_AST.UnivApp) -> begin
(p_universe u)
end
| (e, FStar_Parser_AST.FsTypApp) -> begin
((FStar_Errors.log_issue e.FStar_Parser_AST.range ((FStar_Errors.Warning_UnexpectedFsTypApp), ("Unexpected FsTypApp, output might not be formatted correctly.")));
(

let uu____6310 = (p_indexingTerm e)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.langle uu____6310 FStar_Pprint.rangle));
)
end
| (e, FStar_Parser_AST.Hash) -> begin
(

let uu____6312 = (str "#")
in (

let uu____6313 = (p_indexingTerm e)
in (FStar_Pprint.op_Hat_Hat uu____6312 uu____6313)))
end
| (e, FStar_Parser_AST.HashBrace (t)) -> begin
(

let uu____6316 = (str "#[")
in (

let uu____6317 = (

let uu____6318 = (p_indexingTerm t)
in (

let uu____6319 = (

let uu____6320 = (str "]")
in (

let uu____6321 = (p_indexingTerm e)
in (FStar_Pprint.op_Hat_Hat uu____6320 uu____6321)))
in (FStar_Pprint.op_Hat_Hat uu____6318 uu____6319)))
in (FStar_Pprint.op_Hat_Hat uu____6316 uu____6317)))
end
| (e, FStar_Parser_AST.Nothing) -> begin
(p_indexingTerm e)
end))
and p_fsTypArg : (FStar_Parser_AST.term * FStar_Parser_AST.imp)  ->  FStar_Pprint.document = (fun uu____6323 -> (match (uu____6323) with
| (e, uu____6329) -> begin
(p_indexingTerm e)
end))
and p_indexingTerm_aux : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun exit1 e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____6334}, (e1)::(e2)::[]) -> begin
(

let uu____6339 = (

let uu____6340 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (

let uu____6341 = (

let uu____6342 = (

let uu____6343 = (p_term false false e2)
in (soft_parens_with_nesting uu____6343))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6342))
in (FStar_Pprint.op_Hat_Hat uu____6340 uu____6341)))
in (FStar_Pprint.group uu____6339))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____6344}, (e1)::(e2)::[]) -> begin
(

let uu____6349 = (

let uu____6350 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (

let uu____6351 = (

let uu____6352 = (

let uu____6353 = (p_term false false e2)
in (soft_brackets_with_nesting uu____6353))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6352))
in (FStar_Pprint.op_Hat_Hat uu____6350 uu____6351)))
in (FStar_Pprint.group uu____6349))
end
| uu____6354 -> begin
(exit1 e)
end))
and p_indexingTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_indexingTerm_aux p_atomicTerm e))
and p_atomicTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.LetOpen (lid, e1) -> begin
(

let uu____6359 = (p_quident lid)
in (

let uu____6360 = (

let uu____6361 = (

let uu____6362 = (p_term false false e1)
in (soft_parens_with_nesting uu____6362))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6361))
in (FStar_Pprint.op_Hat_Hat uu____6359 uu____6360)))
end
| FStar_Parser_AST.Name (lid) -> begin
(p_quident lid)
end
| FStar_Parser_AST.Op (op, (e1)::[]) when (is_general_prefix_op op) -> begin
(

let uu____6368 = (

let uu____6369 = (FStar_Ident.text_of_id op)
in (str uu____6369))
in (

let uu____6370 = (p_atomicTerm e1)
in (FStar_Pprint.op_Hat_Hat uu____6368 uu____6370)))
end
| uu____6371 -> begin
(p_atomicTermNotQUident e)
end))
and p_atomicTermNotQUident : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
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
| uu____6380 -> begin
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

let uu____6387 = (

let uu____6388 = (FStar_Ident.text_of_id op)
in (str uu____6388))
in (

let uu____6389 = (p_atomicTermNotQUident e1)
in (FStar_Pprint.op_Hat_Hat uu____6387 uu____6389)))
end
| FStar_Parser_AST.Op (op, []) -> begin
(

let uu____6393 = (

let uu____6394 = (

let uu____6395 = (

let uu____6396 = (FStar_Ident.text_of_id op)
in (str uu____6396))
in (

let uu____6397 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat uu____6395 uu____6397)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6394))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6393))
end
| FStar_Parser_AST.Construct (lid, args) when (is_dtuple_constructor lid) -> begin
(

let uu____6412 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (

let uu____6413 = (

let uu____6414 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (

let uu____6415 = (FStar_List.map FStar_Pervasives_Native.fst args)
in (FStar_Pprint.separate_map uu____6414 p_tmEq uu____6415)))
in (

let uu____6422 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____6412 uu____6413 uu____6422))))
end
| FStar_Parser_AST.Project (e1, lid) -> begin
(

let uu____6425 = (

let uu____6426 = (p_atomicTermNotQUident e1)
in (

let uu____6427 = (

let uu____6428 = (p_qlident lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6428))
in (FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0") uu____6426 uu____6427)))
in (FStar_Pprint.group uu____6425))
end
| uu____6429 -> begin
(p_projectionLHS e)
end))
and p_projectionLHS : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (lid) -> begin
(p_qlident lid)
end
| FStar_Parser_AST.Projector (constr_lid, field_lid) -> begin
(

let uu____6434 = (p_quident constr_lid)
in (

let uu____6435 = (

let uu____6436 = (

let uu____6437 = (p_lident field_lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6437))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6436))
in (FStar_Pprint.op_Hat_Hat uu____6434 uu____6435)))
end
| FStar_Parser_AST.Discrim (constr_lid) -> begin
(

let uu____6439 = (p_quident constr_lid)
in (FStar_Pprint.op_Hat_Hat uu____6439 FStar_Pprint.qmark))
end
| FStar_Parser_AST.Paren (e1) -> begin
(

let uu____6441 = (p_term false false e1)
in (soft_parens_with_nesting uu____6441))
end
| uu____6442 when (is_array e) -> begin
(

let es = (extract_from_list e)
in (

let uu____6446 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar)
in (

let uu____6447 = (

let uu____6448 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (separate_map_or_flow_last uu____6448 (fun ps -> (p_noSeqTerm ps false)) es))
in (

let uu____6451 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") uu____6446 uu____6447 uu____6451)))))
end
| uu____6452 when (is_list e) -> begin
(

let uu____6453 = (

let uu____6454 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (

let uu____6455 = (extract_from_list e)
in (separate_map_or_flow_last uu____6454 (fun ps -> (p_noSeqTerm ps false)) uu____6455)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket uu____6453 FStar_Pprint.rbracket))
end
| uu____6460 when (is_lex_list e) -> begin
(

let uu____6461 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket)
in (

let uu____6462 = (

let uu____6463 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (

let uu____6464 = (extract_from_list e)
in (separate_map_or_flow_last uu____6463 (fun ps -> (p_noSeqTerm ps false)) uu____6464)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____6461 uu____6462 FStar_Pprint.rbracket)))
end
| uu____6469 when (is_ref_set e) -> begin
(

let es = (extract_from_ref_set e)
in (

let uu____6473 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace)
in (

let uu____6474 = (

let uu____6475 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (separate_map_or_flow uu____6475 p_appTerm es))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") uu____6473 uu____6474 FStar_Pprint.rbrace))))
end
| FStar_Parser_AST.Labeled (e1, s, b) -> begin
(

let uu____6479 = (str (Prims.strcat "(*" (Prims.strcat s "*)")))
in (

let uu____6480 = (p_term false false e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____6479 uu____6480)))
end
| FStar_Parser_AST.Op (op, args) when (

let uu____6487 = (handleable_op op args)
in (not (uu____6487))) -> begin
(

let uu____6488 = (

let uu____6489 = (

let uu____6490 = (FStar_Ident.text_of_id op)
in (

let uu____6491 = (

let uu____6492 = (

let uu____6493 = (FStar_Util.string_of_int (FStar_List.length args))
in (Prims.strcat uu____6493 " arguments couldn\'t be handled by the pretty printer"))
in (Prims.strcat " with " uu____6492))
in (Prims.strcat uu____6490 uu____6491)))
in (Prims.strcat "Operation " uu____6489))
in (failwith uu____6488))
end
| FStar_Parser_AST.Uvar (id1) -> begin
(

let uu____6495 = (str "u#")
in (

let uu____6496 = (str id1.FStar_Ident.idText)
in (FStar_Pprint.op_Hat_Hat uu____6495 uu____6496)))
end
| FStar_Parser_AST.Wild -> begin
(

let uu____6497 = (p_term false false e)
in (soft_parens_with_nesting uu____6497))
end
| FStar_Parser_AST.Const (uu____6498) -> begin
(

let uu____6499 = (p_term false false e)
in (soft_parens_with_nesting uu____6499))
end
| FStar_Parser_AST.Op (uu____6500) -> begin
(

let uu____6507 = (p_term false false e)
in (soft_parens_with_nesting uu____6507))
end
| FStar_Parser_AST.Tvar (uu____6508) -> begin
(

let uu____6509 = (p_term false false e)
in (soft_parens_with_nesting uu____6509))
end
| FStar_Parser_AST.Var (uu____6510) -> begin
(

let uu____6511 = (p_term false false e)
in (soft_parens_with_nesting uu____6511))
end
| FStar_Parser_AST.Name (uu____6512) -> begin
(

let uu____6513 = (p_term false false e)
in (soft_parens_with_nesting uu____6513))
end
| FStar_Parser_AST.Construct (uu____6514) -> begin
(

let uu____6525 = (p_term false false e)
in (soft_parens_with_nesting uu____6525))
end
| FStar_Parser_AST.Abs (uu____6526) -> begin
(

let uu____6533 = (p_term false false e)
in (soft_parens_with_nesting uu____6533))
end
| FStar_Parser_AST.App (uu____6534) -> begin
(

let uu____6541 = (p_term false false e)
in (soft_parens_with_nesting uu____6541))
end
| FStar_Parser_AST.Let (uu____6542) -> begin
(

let uu____6563 = (p_term false false e)
in (soft_parens_with_nesting uu____6563))
end
| FStar_Parser_AST.LetOpen (uu____6564) -> begin
(

let uu____6569 = (p_term false false e)
in (soft_parens_with_nesting uu____6569))
end
| FStar_Parser_AST.Seq (uu____6570) -> begin
(

let uu____6575 = (p_term false false e)
in (soft_parens_with_nesting uu____6575))
end
| FStar_Parser_AST.Bind (uu____6576) -> begin
(

let uu____6583 = (p_term false false e)
in (soft_parens_with_nesting uu____6583))
end
| FStar_Parser_AST.If (uu____6584) -> begin
(

let uu____6591 = (p_term false false e)
in (soft_parens_with_nesting uu____6591))
end
| FStar_Parser_AST.Match (uu____6592) -> begin
(

let uu____6607 = (p_term false false e)
in (soft_parens_with_nesting uu____6607))
end
| FStar_Parser_AST.TryWith (uu____6608) -> begin
(

let uu____6623 = (p_term false false e)
in (soft_parens_with_nesting uu____6623))
end
| FStar_Parser_AST.Ascribed (uu____6624) -> begin
(

let uu____6633 = (p_term false false e)
in (soft_parens_with_nesting uu____6633))
end
| FStar_Parser_AST.Record (uu____6634) -> begin
(

let uu____6647 = (p_term false false e)
in (soft_parens_with_nesting uu____6647))
end
| FStar_Parser_AST.Project (uu____6648) -> begin
(

let uu____6653 = (p_term false false e)
in (soft_parens_with_nesting uu____6653))
end
| FStar_Parser_AST.Product (uu____6654) -> begin
(

let uu____6661 = (p_term false false e)
in (soft_parens_with_nesting uu____6661))
end
| FStar_Parser_AST.Sum (uu____6662) -> begin
(

let uu____6669 = (p_term false false e)
in (soft_parens_with_nesting uu____6669))
end
| FStar_Parser_AST.QForall (uu____6670) -> begin
(

let uu____6683 = (p_term false false e)
in (soft_parens_with_nesting uu____6683))
end
| FStar_Parser_AST.QExists (uu____6684) -> begin
(

let uu____6697 = (p_term false false e)
in (soft_parens_with_nesting uu____6697))
end
| FStar_Parser_AST.Refine (uu____6698) -> begin
(

let uu____6703 = (p_term false false e)
in (soft_parens_with_nesting uu____6703))
end
| FStar_Parser_AST.NamedTyp (uu____6704) -> begin
(

let uu____6709 = (p_term false false e)
in (soft_parens_with_nesting uu____6709))
end
| FStar_Parser_AST.Requires (uu____6710) -> begin
(

let uu____6717 = (p_term false false e)
in (soft_parens_with_nesting uu____6717))
end
| FStar_Parser_AST.Ensures (uu____6718) -> begin
(

let uu____6725 = (p_term false false e)
in (soft_parens_with_nesting uu____6725))
end
| FStar_Parser_AST.Attributes (uu____6726) -> begin
(

let uu____6729 = (p_term false false e)
in (soft_parens_with_nesting uu____6729))
end
| FStar_Parser_AST.Quote (uu____6730) -> begin
(

let uu____6735 = (p_term false false e)
in (soft_parens_with_nesting uu____6735))
end
| FStar_Parser_AST.VQuote (uu____6736) -> begin
(

let uu____6737 = (p_term false false e)
in (soft_parens_with_nesting uu____6737))
end
| FStar_Parser_AST.Antiquote (uu____6738) -> begin
(

let uu____6743 = (p_term false false e)
in (soft_parens_with_nesting uu____6743))
end))
and p_constant : FStar_Const.sconst  ->  FStar_Pprint.document = (fun uu___127_6744 -> (match (uu___127_6744) with
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
(FStar_Pprint.doc_of_char x)
end
| FStar_Const.Const_string (s, uu____6750) -> begin
(

let uu____6751 = (str s)
in (FStar_Pprint.dquotes uu____6751))
end
| FStar_Const.Const_bytearray (bytes, uu____6753) -> begin
(

let uu____6760 = (

let uu____6761 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes uu____6761))
in (

let uu____6762 = (str "B")
in (FStar_Pprint.op_Hat_Hat uu____6760 uu____6762)))
end
| FStar_Const.Const_int (repr, sign_width_opt) -> begin
(

let signedness = (fun uu___125_6782 -> (match (uu___125_6782) with
| FStar_Const.Unsigned -> begin
(str "u")
end
| FStar_Const.Signed -> begin
FStar_Pprint.empty
end))
in (

let width = (fun uu___126_6788 -> (match (uu___126_6788) with
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

let ending = (default_or_map FStar_Pprint.empty (fun uu____6799 -> (match (uu____6799) with
| (s, w) -> begin
(

let uu____6806 = (signedness s)
in (

let uu____6807 = (width w)
in (FStar_Pprint.op_Hat_Hat uu____6806 uu____6807)))
end)) sign_width_opt)
in (

let uu____6808 = (str repr)
in (FStar_Pprint.op_Hat_Hat uu____6808 ending)))))
end
| FStar_Const.Const_range_of -> begin
(str "range_of")
end
| FStar_Const.Const_set_range_of -> begin
(str "set_range_of")
end
| FStar_Const.Const_range (r) -> begin
(

let uu____6810 = (FStar_Range.string_of_range r)
in (str uu____6810))
end
| FStar_Const.Const_reify -> begin
(str "reify")
end
| FStar_Const.Const_reflect (lid) -> begin
(

let uu____6812 = (p_quident lid)
in (

let uu____6813 = (

let uu____6814 = (

let uu____6815 = (str "reflect")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6815))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6814))
in (FStar_Pprint.op_Hat_Hat uu____6812 uu____6813)))
end))
and p_universe : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (

let uu____6817 = (str "u#")
in (

let uu____6818 = (p_atomicUniverse u)
in (FStar_Pprint.op_Hat_Hat uu____6817 uu____6818))))
and p_universeFrom : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match (u.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6820}, (u1)::(u2)::[]) -> begin
(

let uu____6825 = (

let uu____6826 = (p_universeFrom u1)
in (

let uu____6827 = (

let uu____6828 = (p_universeFrom u2)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6828))
in (FStar_Pprint.op_Hat_Slash_Hat uu____6826 uu____6827)))
in (FStar_Pprint.group uu____6825))
end
| FStar_Parser_AST.App (uu____6829) -> begin
(

let uu____6836 = (head_and_args u)
in (match (uu____6836) with
| (head1, args) -> begin
(match (head1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (maybe_max_lid) when (FStar_Ident.lid_equals maybe_max_lid FStar_Parser_Const.max_lid) -> begin
(

let uu____6862 = (

let uu____6863 = (p_qlident FStar_Parser_Const.max_lid)
in (

let uu____6864 = (FStar_Pprint.separate_map FStar_Pprint.space (fun uu____6872 -> (match (uu____6872) with
| (u1, uu____6878) -> begin
(p_atomicUniverse u1)
end)) args)
in (op_Hat_Slash_Plus_Hat uu____6863 uu____6864)))
in (FStar_Pprint.group uu____6862))
end
| uu____6879 -> begin
(

let uu____6880 = (

let uu____6881 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" uu____6881))
in (failwith uu____6880))
end)
end))
end
| uu____6882 -> begin
(p_atomicUniverse u)
end))
and p_atomicUniverse : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match (u.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Wild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (r, sw)) -> begin
(p_constant (FStar_Const.Const_int (((r), (sw)))))
end
| FStar_Parser_AST.Uvar (id1) -> begin
(

let uu____6905 = (FStar_Ident.text_of_id id1)
in (str uu____6905))
end
| FStar_Parser_AST.Paren (u1) -> begin
(

let uu____6907 = (p_universeFrom u1)
in (soft_parens_with_nesting uu____6907))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6908}, (uu____6909)::(uu____6910)::[]) -> begin
(

let uu____6913 = (p_universeFrom u)
in (soft_parens_with_nesting uu____6913))
end
| FStar_Parser_AST.App (uu____6914) -> begin
(

let uu____6921 = (p_universeFrom u)
in (soft_parens_with_nesting uu____6921))
end
| uu____6922 -> begin
(

let uu____6923 = (

let uu____6924 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" uu____6924))
in (failwith uu____6923))
end))


let term_to_document : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> ((FStar_ST.op_Colon_Equals unfold_tuples false);
(p_term false false e);
))


let signature_to_document : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun e -> (p_justSig e))


let decl_to_document : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun e -> (p_decl e))


let pat_to_document : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (p_disjunctivePattern p))


let binder_to_document : FStar_Parser_AST.binder  ->  FStar_Pprint.document = (fun b -> (p_binder true b))


let modul_to_document : FStar_Parser_AST.modul  ->  FStar_Pprint.document = (fun m -> ((FStar_ST.op_Colon_Equals should_print_fs_typ_app false);
(

let res = (match (m) with
| FStar_Parser_AST.Module (uu____6996, decls) -> begin
(

let uu____7002 = (FStar_All.pipe_right decls (FStar_List.map decl_to_document))
in (FStar_All.pipe_right uu____7002 (FStar_Pprint.separate FStar_Pprint.hardline)))
end
| FStar_Parser_AST.Interface (uu____7011, decls, uu____7013) -> begin
(

let uu____7018 = (FStar_All.pipe_right decls (FStar_List.map decl_to_document))
in (FStar_All.pipe_right uu____7018 (FStar_Pprint.separate FStar_Pprint.hardline)))
end)
in ((FStar_ST.op_Colon_Equals should_print_fs_typ_app false);
res;
));
))


let comments_to_document : (Prims.string * FStar_Range.range) Prims.list  ->  FStar_Pprint.document = (fun comments -> (FStar_Pprint.separate_map FStar_Pprint.hardline (fun uu____7071 -> (match (uu____7071) with
| (comment, range) -> begin
(str comment)
end)) comments))


let modul_with_comments_to_document : FStar_Parser_AST.modul  ->  (Prims.string * FStar_Range.range) Prims.list  ->  (FStar_Pprint.document * (Prims.string * FStar_Range.range) Prims.list) = (fun m comments -> (

let decls = (match (m) with
| FStar_Parser_AST.Module (uu____7115, decls) -> begin
decls
end
| FStar_Parser_AST.Interface (uu____7121, decls, uu____7123) -> begin
decls
end)
in ((FStar_ST.op_Colon_Equals should_print_fs_typ_app false);
(match (decls) with
| [] -> begin
((FStar_Pprint.empty), (comments))
end
| (d)::ds -> begin
(

let uu____7168 = (match (ds) with
| ({FStar_Parser_AST.d = FStar_Parser_AST.Pragma (FStar_Parser_AST.LightOff); FStar_Parser_AST.drange = uu____7181; FStar_Parser_AST.doc = uu____7182; FStar_Parser_AST.quals = uu____7183; FStar_Parser_AST.attrs = uu____7184})::uu____7185 -> begin
(

let d0 = (FStar_List.hd ds)
in (

let uu____7191 = (

let uu____7194 = (

let uu____7197 = (FStar_List.tl ds)
in (d)::uu____7197)
in (d0)::uu____7194)
in ((uu____7191), (d0.FStar_Parser_AST.drange))))
end
| uu____7202 -> begin
(((d)::ds), (d.FStar_Parser_AST.drange))
end)
in (match (uu____7168) with
| (decls1, first_range) -> begin
(

let extract_decl_range = (fun d1 -> d1.FStar_Parser_AST.drange)
in ((FStar_ST.op_Colon_Equals comment_stack comments);
(

let initial_comment = (

let uu____7262 = (FStar_Range.start_of_range first_range)
in (place_comments_until_pos (Prims.parse_int "0") (Prims.parse_int "1") uu____7262 FStar_Pprint.empty))
in (

let doc1 = (separate_map_with_comments FStar_Pprint.empty FStar_Pprint.empty decl_to_document decls1 extract_decl_range)
in (

let comments1 = (FStar_ST.op_Bang comment_stack)
in ((FStar_ST.op_Colon_Equals comment_stack []);
(FStar_ST.op_Colon_Equals should_print_fs_typ_app false);
(

let uu____7358 = (FStar_Pprint.op_Hat_Hat initial_comment doc1)
in ((uu____7358), (comments1)));
))));
))
end))
end);
)))




