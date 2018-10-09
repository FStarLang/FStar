
open Prims
open FStar_Pervasives

let should_print_fs_typ_app : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let all_explicit : (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  Prims.bool = (fun args -> (FStar_Util.for_all (fun uu___110_37 -> (match (uu___110_37) with
| (uu____42, FStar_Parser_AST.Nothing) -> begin
true
end
| uu____43 -> begin
false
end)) args))


let unfold_tuples : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref true)


let with_fs_typ_app : 'Auu____71 'Auu____72 . Prims.bool  ->  ('Auu____71  ->  'Auu____72)  ->  'Auu____71  ->  'Auu____72 = (fun b printer t -> (

let b0 = (FStar_ST.op_Bang should_print_fs_typ_app)
in ((FStar_ST.op_Colon_Equals should_print_fs_typ_app b);
(

let res = (printer t)
in ((FStar_ST.op_Colon_Equals should_print_fs_typ_app b0);
res;
));
)))


let str : Prims.string  ->  FStar_Pprint.document = (fun s -> (FStar_Pprint.doc_of_string s))


let default_or_map : 'Auu____169 'Auu____170 . 'Auu____169  ->  ('Auu____170  ->  'Auu____169)  ->  'Auu____170 FStar_Pervasives_Native.option  ->  'Auu____169 = (fun n1 f x -> (match (x) with
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
| uu____216 -> begin
(prefix2 prefix_ body)
end))


let op_Hat_Slash_Plus_Hat : FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun prefix_ body -> (prefix2 prefix_ body))


let jump2 : FStar_Pprint.document  ->  FStar_Pprint.document = (fun body -> (FStar_Pprint.jump (Prims.parse_int "2") (Prims.parse_int "1") body))


let infix2 : FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (FStar_Pprint.infix (Prims.parse_int "2") (Prims.parse_int "1"))


let infix0 : FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (FStar_Pprint.infix (Prims.parse_int "0") (Prims.parse_int "1"))


let break1 : FStar_Pprint.document = (FStar_Pprint.break_ (Prims.parse_int "1"))


let separate_break_map : 'Auu____264 . FStar_Pprint.document  ->  ('Auu____264  ->  FStar_Pprint.document)  ->  'Auu____264 Prims.list  ->  FStar_Pprint.document = (fun sep f l -> (

let uu____289 = (

let uu____290 = (

let uu____291 = (FStar_Pprint.op_Hat_Hat sep break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____291))
in (FStar_Pprint.separate_map uu____290 f l))
in (FStar_Pprint.group uu____289)))


let precede_break_separate_map : 'Auu____302 . FStar_Pprint.document  ->  FStar_Pprint.document  ->  ('Auu____302  ->  FStar_Pprint.document)  ->  'Auu____302 Prims.list  ->  FStar_Pprint.document = (fun prec sep f l -> (

let uu____332 = (

let uu____333 = (FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space)
in (

let uu____334 = (

let uu____335 = (FStar_List.hd l)
in (FStar_All.pipe_right uu____335 f))
in (FStar_Pprint.precede uu____333 uu____334)))
in (

let uu____336 = (

let uu____337 = (FStar_List.tl l)
in (FStar_Pprint.concat_map (fun x -> (

let uu____343 = (

let uu____344 = (

let uu____345 = (f x)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____345))
in (FStar_Pprint.op_Hat_Hat sep uu____344))
in (FStar_Pprint.op_Hat_Hat break1 uu____343))) uu____337))
in (FStar_Pprint.op_Hat_Hat uu____332 uu____336))))


let concat_break_map : 'Auu____352 . ('Auu____352  ->  FStar_Pprint.document)  ->  'Auu____352 Prims.list  ->  FStar_Pprint.document = (fun f l -> (

let uu____372 = (FStar_Pprint.concat_map (fun x -> (

let uu____376 = (f x)
in (FStar_Pprint.op_Hat_Hat uu____376 break1))) l)
in (FStar_Pprint.group uu____372)))


let parens_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lparen contents FStar_Pprint.rparen))


let soft_parens_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lparen contents FStar_Pprint.rparen))


let braces_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbrace contents FStar_Pprint.rbrace))


let soft_braces_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbrace contents FStar_Pprint.rbrace))


let soft_braces_with_nesting_tight : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbrace contents FStar_Pprint.rbrace))


let brackets_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbracket contents FStar_Pprint.rbracket))


let soft_brackets_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbracket contents FStar_Pprint.rbracket))


let soft_begin_end_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (

let uu____417 = (str "begin")
in (

let uu____418 = (str "end")
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") uu____417 contents uu____418))))


let separate_map_last : 'Auu____427 . FStar_Pprint.document  ->  (Prims.bool  ->  'Auu____427  ->  FStar_Pprint.document)  ->  'Auu____427 Prims.list  ->  FStar_Pprint.document = (fun sep f es -> (

let l = (FStar_List.length es)
in (

let es1 = (FStar_List.mapi (fun i e -> (f (Prims.op_disEquality i (l - (Prims.parse_int "1"))) e)) es)
in (FStar_Pprint.separate sep es1))))


let separate_break_map_last : 'Auu____479 . FStar_Pprint.document  ->  (Prims.bool  ->  'Auu____479  ->  FStar_Pprint.document)  ->  'Auu____479 Prims.list  ->  FStar_Pprint.document = (fun sep f l -> (

let uu____509 = (

let uu____510 = (

let uu____511 = (FStar_Pprint.op_Hat_Hat sep break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____511))
in (separate_map_last uu____510 f l))
in (FStar_Pprint.group uu____509)))


let separate_map_or_flow : 'Auu____520 . FStar_Pprint.document  ->  ('Auu____520  ->  FStar_Pprint.document)  ->  'Auu____520 Prims.list  ->  FStar_Pprint.document = (fun sep f l -> (match (((FStar_List.length l) < (Prims.parse_int "10"))) with
| true -> begin
(FStar_Pprint.separate_map sep f l)
end
| uu____545 -> begin
(FStar_Pprint.flow_map sep f l)
end))


let flow_map_last : 'Auu____554 . FStar_Pprint.document  ->  (Prims.bool  ->  'Auu____554  ->  FStar_Pprint.document)  ->  'Auu____554 Prims.list  ->  FStar_Pprint.document = (fun sep f es -> (

let l = (FStar_List.length es)
in (

let es1 = (FStar_List.mapi (fun i e -> (f (Prims.op_disEquality i (l - (Prims.parse_int "1"))) e)) es)
in (FStar_Pprint.flow sep es1))))


let separate_map_or_flow_last : 'Auu____606 . FStar_Pprint.document  ->  (Prims.bool  ->  'Auu____606  ->  FStar_Pprint.document)  ->  'Auu____606 Prims.list  ->  FStar_Pprint.document = (fun sep f l -> (match (((FStar_List.length l) < (Prims.parse_int "10"))) with
| true -> begin
(separate_map_last sep f l)
end
| uu____636 -> begin
(flow_map_last sep f l)
end))


let separate_or_flow : FStar_Pprint.document  ->  FStar_Pprint.document Prims.list  ->  FStar_Pprint.document = (fun sep l -> (separate_map_or_flow sep FStar_Pervasives.id l))


let surround_maybe_empty : Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun n1 b doc1 doc2 doc3 -> (match ((Prims.op_Equality doc2 FStar_Pprint.empty)) with
| true -> begin
(

let uu____676 = (FStar_Pprint.op_Hat_Slash_Hat doc1 doc3)
in (FStar_Pprint.group uu____676))
end
| uu____677 -> begin
(FStar_Pprint.surround n1 b doc1 doc2 doc3)
end))


let soft_surround_separate_map : 'Auu____696 . Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  ('Auu____696  ->  FStar_Pprint.document)  ->  'Auu____696 Prims.list  ->  FStar_Pprint.document = (fun n1 b void_ opening sep closing f xs -> (match ((Prims.op_Equality xs [])) with
| true -> begin
void_
end
| uu____748 -> begin
(

let uu____749 = (FStar_Pprint.separate_map sep f xs)
in (FStar_Pprint.soft_surround n1 b opening uu____749 closing))
end))


let soft_surround_map_or_flow : 'Auu____768 . Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  ('Auu____768  ->  FStar_Pprint.document)  ->  'Auu____768 Prims.list  ->  FStar_Pprint.document = (fun n1 b void_ opening sep closing f xs -> (match ((Prims.op_Equality xs [])) with
| true -> begin
void_
end
| uu____820 -> begin
(

let uu____821 = (separate_map_or_flow sep f xs)
in (FStar_Pprint.soft_surround n1 b opening uu____821 closing))
end))


let doc_of_fsdoc : (Prims.string * (Prims.string * Prims.string) Prims.list)  ->  FStar_Pprint.document = (fun uu____836 -> (match (uu____836) with
| (comment, keywords) -> begin
(

let uu____861 = (

let uu____862 = (

let uu____865 = (str comment)
in (

let uu____866 = (

let uu____869 = (

let uu____872 = (FStar_Pprint.separate_map FStar_Pprint.comma (fun uu____881 -> (match (uu____881) with
| (k, v1) -> begin
(

let uu____888 = (

let uu____891 = (str k)
in (

let uu____892 = (

let uu____895 = (

let uu____898 = (str v1)
in (uu____898)::[])
in (FStar_Pprint.rarrow)::uu____895)
in (uu____891)::uu____892))
in (FStar_Pprint.concat uu____888))
end)) keywords)
in (uu____872)::[])
in (FStar_Pprint.space)::uu____869)
in (uu____865)::uu____866))
in (FStar_Pprint.concat uu____862))
in (FStar_Pprint.group uu____861))
end))


let is_unit : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Const (FStar_Const.Const_unit) -> begin
true
end
| uu____904 -> begin
false
end))


let matches_var : FStar_Parser_AST.term  ->  FStar_Ident.ident  ->  Prims.bool = (fun t x -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (y) -> begin
(

let uu____916 = (FStar_Ident.text_of_lid y)
in (Prims.op_Equality x.FStar_Ident.idText uu____916))
end
| uu____917 -> begin
false
end))


let is_tuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Parser_Const.is_tuple_data_lid'


let is_dtuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Parser_Const.is_dtuple_data_lid'


let is_list_structure : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun cons_lid1 nil_lid1 -> (

let rec aux = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (lid, []) -> begin
(FStar_Ident.lid_equals lid nil_lid1)
end
| FStar_Parser_AST.Construct (lid, (uu____959)::((e2, uu____961))::[]) -> begin
((FStar_Ident.lid_equals lid cons_lid1) && (aux e2))
end
| uu____984 -> begin
false
end))
in aux))


let is_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Parser_Const.cons_lid FStar_Parser_Const.nil_lid)


let is_lex_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Parser_Const.lexcons_lid FStar_Parser_Const.lextop_lid)


let rec extract_from_list : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (uu____1002, []) -> begin
[]
end
| FStar_Parser_AST.Construct (uu____1013, ((e1, FStar_Parser_AST.Nothing))::((e2, FStar_Parser_AST.Nothing))::[]) -> begin
(

let uu____1034 = (extract_from_list e2)
in (e1)::uu____1034)
end
| uu____1037 -> begin
(

let uu____1038 = (

let uu____1039 = (FStar_Parser_AST.term_to_string e)
in (FStar_Util.format1 "Not a list %s" uu____1039))
in (failwith uu____1038))
end))


let is_array : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (lid); FStar_Parser_AST.range = uu____1048; FStar_Parser_AST.level = uu____1049}, l, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) && (is_list l))
end
| uu____1051 -> begin
false
end))


let rec is_ref_set : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (maybe_empty_lid) -> begin
(FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty)
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_singleton_lid); FStar_Parser_AST.range = uu____1059; FStar_Parser_AST.level = uu____1060}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_addr_of_lid); FStar_Parser_AST.range = uu____1062; FStar_Parser_AST.level = uu____1063}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____1065; FStar_Parser_AST.level = uu____1066}, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals maybe_singleton_lid FStar_Parser_Const.set_singleton) && (FStar_Ident.lid_equals maybe_addr_of_lid FStar_Parser_Const.heap_addr_of_lid))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_union_lid); FStar_Parser_AST.range = uu____1068; FStar_Parser_AST.level = uu____1069}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____1071; FStar_Parser_AST.level = uu____1072}, e2, FStar_Parser_AST.Nothing) -> begin
(((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union) && (is_ref_set e1)) && (is_ref_set e2))
end
| uu____1074 -> begin
false
end))


let rec extract_from_ref_set : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (uu____1084) -> begin
[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (uu____1085); FStar_Parser_AST.range = uu____1086; FStar_Parser_AST.level = uu____1087}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (uu____1088); FStar_Parser_AST.range = uu____1089; FStar_Parser_AST.level = uu____1090}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____1092; FStar_Parser_AST.level = uu____1093}, FStar_Parser_AST.Nothing) -> begin
(e1)::[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (uu____1094); FStar_Parser_AST.range = uu____1095; FStar_Parser_AST.level = uu____1096}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____1098; FStar_Parser_AST.level = uu____1099}, e2, FStar_Parser_AST.Nothing) -> begin
(

let uu____1101 = (extract_from_ref_set e1)
in (

let uu____1104 = (extract_from_ref_set e2)
in (FStar_List.append uu____1101 uu____1104)))
end
| uu____1107 -> begin
(

let uu____1108 = (

let uu____1109 = (FStar_Parser_AST.term_to_string e)
in (FStar_Util.format1 "Not a ref set %s" uu____1109))
in (failwith uu____1108))
end))


let is_general_application : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____1117 = ((is_array e) || (is_ref_set e))
in (not (uu____1117))))


let is_general_construction : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____1123 = ((is_list e) || (is_lex_list e))
in (not (uu____1123))))


let is_general_prefix_op : FStar_Ident.ident  ->  Prims.bool = (fun op -> (

let op_starting_char = (

let uu____1131 = (FStar_Ident.text_of_id op)
in (FStar_Util.char_at uu____1131 (Prims.parse_int "0")))
in (((Prims.op_Equality op_starting_char 33 (*!*)) || (Prims.op_Equality op_starting_char 63 (*?*))) || ((Prims.op_Equality op_starting_char 126 (*~*)) && (

let uu____1139 = (FStar_Ident.text_of_id op)
in (Prims.op_disEquality uu____1139 "~"))))))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun e -> (

let rec aux = (fun e1 acc -> (match (e1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App (head1, arg, imp) -> begin
(aux head1 ((((arg), (imp)))::acc))
end
| uu____1205 -> begin
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
| uu____1221 -> begin
false
end))


let uu___is_Right : associativity  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Right -> begin
true
end
| uu____1227 -> begin
false
end))


let uu___is_NonAssoc : associativity  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NonAssoc -> begin
true
end
| uu____1233 -> begin
false
end))


type token =
(FStar_Char.char, Prims.string) FStar_Util.either


type associativity_level =
(associativity * token Prims.list)


let token_to_string : (FStar_BaseTypes.char, Prims.string) FStar_Util.either  ->  Prims.string = (fun uu___111_1254 -> (match (uu___111_1254) with
| FStar_Util.Inl (c) -> begin
(Prims.strcat (FStar_Util.string_of_char c) ".*")
end
| FStar_Util.Inr (s) -> begin
s
end))


let matches_token : Prims.string  ->  (FStar_Char.char, Prims.string) FStar_Util.either  ->  Prims.bool = (fun s uu___112_1279 -> (match (uu___112_1279) with
| FStar_Util.Inl (c) -> begin
(

let uu____1288 = (FStar_String.get s (Prims.parse_int "0"))
in (Prims.op_Equality uu____1288 c))
end
| FStar_Util.Inr (s') -> begin
(Prims.op_Equality s s')
end))


let matches_level : 'Auu____1299 . Prims.string  ->  ('Auu____1299 * (FStar_Char.char, Prims.string) FStar_Util.either Prims.list)  ->  Prims.bool = (fun s uu____1320 -> (match (uu____1320) with
| (assoc_levels, tokens) -> begin
(

let uu____1348 = (FStar_List.tryFind (matches_token s) tokens)
in (Prims.op_disEquality uu____1348 FStar_Pervasives_Native.None))
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

let levels_from_associativity = (fun l uu___113_1466 -> (match (uu___113_1466) with
| Left -> begin
((l), (l), ((l - (Prims.parse_int "1"))))
end
| Right -> begin
(((l - (Prims.parse_int "1"))), (l), (l))
end
| NonAssoc -> begin
(((l - (Prims.parse_int "1"))), (l), ((l - (Prims.parse_int "1"))))
end))
in (FStar_List.mapi (fun i uu____1496 -> (match (uu____1496) with
| (assoc1, tokens) -> begin
(((levels_from_associativity i assoc1)), (tokens))
end)) level_associativity_spec))


let assign_levels : associativity_level Prims.list  ->  Prims.string  ->  (Prims.int * Prims.int * Prims.int) = (fun token_associativity_spec s -> (

let uu____1555 = (FStar_List.tryFind (matches_level s) level_table)
in (match (uu____1555) with
| FStar_Pervasives_Native.Some (assoc_levels, uu____1595) -> begin
assoc_levels
end
| uu____1624 -> begin
(failwith (Prims.strcat "Unrecognized operator " s))
end)))


let max : Prims.int  ->  Prims.int  ->  Prims.int = (fun k1 k2 -> (match ((k1 > k2)) with
| true -> begin
k1
end
| uu____1655 -> begin
k2
end))


let max_level : 'Auu____1660 . ('Auu____1660 * token Prims.list) Prims.list  ->  Prims.int = (fun l -> (

let find_level_and_max = (fun n1 level -> (

let uu____1705 = (FStar_List.tryFind (fun uu____1735 -> (match (uu____1735) with
| (uu____1748, tokens) -> begin
(Prims.op_Equality tokens (FStar_Pervasives_Native.snd level))
end)) level_table)
in (match (uu____1705) with
| FStar_Pervasives_Native.Some ((uu____1770, l1, uu____1772), uu____1773) -> begin
(max n1 l1)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____1808 = (

let uu____1809 = (

let uu____1810 = (FStar_List.map token_to_string (FStar_Pervasives_Native.snd level))
in (FStar_String.concat "," uu____1810))
in (FStar_Util.format1 "Undefined associativity level %s" uu____1809))
in (failwith uu____1808))
end)))
in (FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l)))


let levels : Prims.string  ->  (Prims.int * Prims.int * Prims.int) = (fun op -> (

let uu____1832 = (assign_levels level_associativity_spec op)
in (match (uu____1832) with
| (left1, mine, right1) -> begin
(match ((Prims.op_Equality op "*")) with
| true -> begin
(((left1 - (Prims.parse_int "1"))), (mine), (right1))
end
| uu____1854 -> begin
((left1), (mine), (right1))
end)
end)))


let operatorInfix0ad12 : associativity_level Prims.list = (opinfix0a)::(opinfix0b)::(opinfix0c)::(opinfix0d)::(opinfix1)::(opinfix2)::[]


let is_operatorInfix0ad12 : FStar_Ident.ident  ->  Prims.bool = (fun op -> (

let uu____1862 = (

let uu____1865 = (

let uu____1870 = (FStar_Ident.text_of_id op)
in (FStar_All.pipe_left matches_level uu____1870))
in (FStar_List.tryFind uu____1865 operatorInfix0ad12))
in (Prims.op_disEquality uu____1862 FStar_Pervasives_Native.None)))


let is_operatorInfix34 : FStar_Ident.ident  ->  Prims.bool = (

let opinfix34 = (opinfix3)::(opinfix4)::[]
in (fun op -> (

let uu____1928 = (

let uu____1942 = (

let uu____1958 = (FStar_Ident.text_of_id op)
in (FStar_All.pipe_left matches_level uu____1958))
in (FStar_List.tryFind uu____1942 opinfix34))
in (Prims.op_disEquality uu____1928 FStar_Pervasives_Native.None))))


let handleable_args_length : FStar_Ident.ident  ->  Prims.int = (fun op -> (

let op_s = (FStar_Ident.text_of_id op)
in (

let uu____2014 = ((is_general_prefix_op op) || (FStar_List.mem op_s (("-")::("~")::[])))
in (match (uu____2014) with
| true -> begin
(Prims.parse_int "1")
end
| uu____2015 -> begin
(

let uu____2016 = (((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) || (FStar_List.mem op_s (("<==>")::("==>")::("\\/")::("/\\")::("=")::("|>")::(":=")::(".()")::(".[]")::[])))
in (match (uu____2016) with
| true -> begin
(Prims.parse_int "2")
end
| uu____2017 -> begin
(match ((FStar_List.mem op_s ((".()<-")::(".[]<-")::[]))) with
| true -> begin
(Prims.parse_int "3")
end
| uu____2018 -> begin
(Prims.parse_int "0")
end)
end))
end))))


let handleable_op : 'Auu____2025 . FStar_Ident.ident  ->  'Auu____2025 Prims.list  ->  Prims.bool = (fun op args -> (match ((FStar_List.length args)) with
| _0_1 when (_0_1 = (Prims.parse_int "0")) -> begin
true
end
| _0_2 when (_0_2 = (Prims.parse_int "1")) -> begin
((is_general_prefix_op op) || (

let uu____2041 = (FStar_Ident.text_of_id op)
in (FStar_List.mem uu____2041 (("-")::("~")::[]))))
end
| _0_3 when (_0_3 = (Prims.parse_int "2")) -> begin
(((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) || (

let uu____2043 = (FStar_Ident.text_of_id op)
in (FStar_List.mem uu____2043 (("<==>")::("==>")::("\\/")::("/\\")::("=")::("|>")::(":=")::(".()")::(".[]")::[]))))
end
| _0_4 when (_0_4 = (Prims.parse_int "3")) -> begin
(

let uu____2044 = (FStar_Ident.text_of_id op)
in (FStar_List.mem uu____2044 ((".()<-")::(".[]<-")::[])))
end
| uu____2045 -> begin
false
end))


let comment_stack : (Prims.string * FStar_Range.range) Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let with_comment : 'Auu____2083 . ('Auu____2083  ->  FStar_Pprint.document)  ->  'Auu____2083  ->  FStar_Range.range  ->  FStar_Pprint.document = (fun printer tm tmrange -> (

let rec comments_before_pos = (fun acc print_pos lookahead_pos -> (

let uu____2124 = (FStar_ST.op_Bang comment_stack)
in (match (uu____2124) with
| [] -> begin
((acc), (false))
end
| ((comment, crange))::cs -> begin
(

let uu____2183 = (FStar_Range.range_before_pos crange print_pos)
in (match (uu____2183) with
| true -> begin
((FStar_ST.op_Colon_Equals comment_stack cs);
(

let uu____2220 = (

let uu____2221 = (

let uu____2222 = (str comment)
in (FStar_Pprint.op_Hat_Hat uu____2222 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat acc uu____2221))
in (comments_before_pos uu____2220 print_pos lookahead_pos));
)
end
| uu____2223 -> begin
(

let uu____2224 = (FStar_Range.range_before_pos crange lookahead_pos)
in ((acc), (uu____2224)))
end))
end)))
in (

let uu____2225 = (

let uu____2230 = (

let uu____2231 = (FStar_Range.start_of_range tmrange)
in (FStar_Range.end_of_line uu____2231))
in (

let uu____2232 = (FStar_Range.end_of_range tmrange)
in (comments_before_pos FStar_Pprint.empty uu____2230 uu____2232)))
in (match (uu____2225) with
| (comments, has_lookahead) -> begin
(

let printed_e = (printer tm)
in (

let comments1 = (match (has_lookahead) with
| true -> begin
(

let pos = (FStar_Range.end_of_range tmrange)
in (

let uu____2238 = (comments_before_pos comments pos pos)
in (FStar_Pervasives_Native.fst uu____2238)))
end
| uu____2243 -> begin
comments
end)
in (

let uu____2244 = (FStar_Pprint.op_Hat_Hat comments1 printed_e)
in (FStar_Pprint.group uu____2244))))
end))))


let rec place_comments_until_pos : Prims.int  ->  Prims.int  ->  FStar_Range.pos  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun k lbegin pos_end doc1 -> (

let uu____2265 = (FStar_ST.op_Bang comment_stack)
in (match (uu____2265) with
| ((comment, crange))::cs when (FStar_Range.range_before_pos crange pos_end) -> begin
((FStar_ST.op_Colon_Equals comment_stack cs);
(

let lnum = (

let uu____2349 = (

let uu____2350 = (

let uu____2351 = (FStar_Range.start_of_range crange)
in (FStar_Range.line_of_pos uu____2351))
in (uu____2350 - lbegin))
in (max k uu____2349))
in (

let lnum1 = (Prims.min (Prims.parse_int "2") lnum)
in (

let doc2 = (

let uu____2354 = (

let uu____2355 = (FStar_Pprint.repeat lnum1 FStar_Pprint.hardline)
in (

let uu____2356 = (str comment)
in (FStar_Pprint.op_Hat_Hat uu____2355 uu____2356)))
in (FStar_Pprint.op_Hat_Hat doc1 uu____2354))
in (

let uu____2357 = (

let uu____2358 = (FStar_Range.end_of_range crange)
in (FStar_Range.line_of_pos uu____2358))
in (place_comments_until_pos (Prims.parse_int "1") uu____2357 pos_end doc2)))));
)
end
| uu____2359 -> begin
(match ((Prims.op_Equality doc1 FStar_Pprint.empty)) with
| true -> begin
FStar_Pprint.empty
end
| uu____2366 -> begin
(

let lnum = (

let uu____2368 = (

let uu____2369 = (FStar_Range.line_of_pos pos_end)
in (uu____2369 - lbegin))
in (max (Prims.parse_int "1") uu____2368))
in (

let lnum1 = (Prims.min (Prims.parse_int "2") lnum)
in (

let uu____2371 = (FStar_Pprint.repeat lnum1 FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat doc1 uu____2371))))
end)
end)))


let separate_map_with_comments : 'Auu____2384 . FStar_Pprint.document  ->  FStar_Pprint.document  ->  ('Auu____2384  ->  FStar_Pprint.document)  ->  'Auu____2384 Prims.list  ->  ('Auu____2384  ->  FStar_Range.range)  ->  FStar_Pprint.document = (fun prefix1 sep f xs extract_range -> (

let fold_fun = (fun uu____2441 x -> (match (uu____2441) with
| (last_line, doc1) -> begin
(

let r = (extract_range x)
in (

let doc2 = (

let uu____2455 = (FStar_Range.start_of_range r)
in (place_comments_until_pos (Prims.parse_int "1") last_line uu____2455 doc1))
in (

let uu____2456 = (

let uu____2457 = (FStar_Range.end_of_range r)
in (FStar_Range.line_of_pos uu____2457))
in (

let uu____2458 = (

let uu____2459 = (

let uu____2460 = (f x)
in (FStar_Pprint.op_Hat_Hat sep uu____2460))
in (FStar_Pprint.op_Hat_Hat doc2 uu____2459))
in ((uu____2456), (uu____2458))))))
end))
in (

let uu____2461 = (

let uu____2468 = (FStar_List.hd xs)
in (

let uu____2469 = (FStar_List.tl xs)
in ((uu____2468), (uu____2469))))
in (match (uu____2461) with
| (x, xs1) -> begin
(

let init1 = (

let uu____2485 = (

let uu____2486 = (

let uu____2487 = (extract_range x)
in (FStar_Range.end_of_range uu____2487))
in (FStar_Range.line_of_pos uu____2486))
in (

let uu____2488 = (

let uu____2489 = (f x)
in (FStar_Pprint.op_Hat_Hat prefix1 uu____2489))
in ((uu____2485), (uu____2488))))
in (

let uu____2490 = (FStar_List.fold_left fold_fun init1 xs1)
in (FStar_Pervasives_Native.snd uu____2490)))
end))))


let separate_map_with_comments_kw : 'Auu____2513 'Auu____2514 . 'Auu____2513  ->  'Auu____2513  ->  ('Auu____2513  ->  'Auu____2514  ->  FStar_Pprint.document)  ->  'Auu____2514 Prims.list  ->  ('Auu____2514  ->  FStar_Range.range)  ->  FStar_Pprint.document = (fun prefix1 sep f xs extract_range -> (

let fold_fun = (fun uu____2576 x -> (match (uu____2576) with
| (last_line, doc1) -> begin
(

let r = (extract_range x)
in (

let doc2 = (

let uu____2590 = (FStar_Range.start_of_range r)
in (place_comments_until_pos (Prims.parse_int "1") last_line uu____2590 doc1))
in (

let uu____2591 = (

let uu____2592 = (FStar_Range.end_of_range r)
in (FStar_Range.line_of_pos uu____2592))
in (

let uu____2593 = (

let uu____2594 = (f sep x)
in (FStar_Pprint.op_Hat_Hat doc2 uu____2594))
in ((uu____2591), (uu____2593))))))
end))
in (

let uu____2595 = (

let uu____2602 = (FStar_List.hd xs)
in (

let uu____2603 = (FStar_List.tl xs)
in ((uu____2602), (uu____2603))))
in (match (uu____2595) with
| (x, xs1) -> begin
(

let init1 = (

let uu____2619 = (

let uu____2620 = (

let uu____2621 = (extract_range x)
in (FStar_Range.end_of_range uu____2621))
in (FStar_Range.line_of_pos uu____2620))
in (

let uu____2622 = (f prefix1 x)
in ((uu____2619), (uu____2622))))
in (

let uu____2623 = (FStar_List.fold_left fold_fun init1 xs1)
in (FStar_Pervasives_Native.snd uu____2623)))
end))))


let rec p_decl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (

let qualifiers = (match (((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d))) with
| ((FStar_Parser_AST.Assumption)::[], FStar_Parser_AST.Assume (id1, uu____3333)) -> begin
(

let uu____3336 = (

let uu____3337 = (FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_All.pipe_right uu____3337 FStar_Util.is_upper))
in (match (uu____3336) with
| true -> begin
(

let uu____3340 = (p_qualifier FStar_Parser_AST.Assumption)
in (FStar_Pprint.op_Hat_Hat uu____3340 FStar_Pprint.space))
end
| uu____3341 -> begin
(p_qualifiers d.FStar_Parser_AST.quals)
end))
end
| uu____3342 -> begin
(p_qualifiers d.FStar_Parser_AST.quals)
end)
in (

let uu____3349 = (FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc)
in (

let uu____3350 = (

let uu____3351 = (p_attributes d.FStar_Parser_AST.attrs)
in (

let uu____3352 = (

let uu____3353 = (p_rawDecl d)
in (FStar_Pprint.op_Hat_Hat qualifiers uu____3353))
in (FStar_Pprint.op_Hat_Hat uu____3351 uu____3352)))
in (FStar_Pprint.op_Hat_Hat uu____3349 uu____3350)))))
and p_attributes : FStar_Parser_AST.attributes_  ->  FStar_Pprint.document = (fun attrs -> (match (attrs) with
| [] -> begin
FStar_Pprint.empty
end
| uu____3355 -> begin
(

let uu____3356 = (

let uu____3357 = (str "@ ")
in (

let uu____3358 = (

let uu____3359 = (

let uu____3360 = (

let uu____3361 = (

let uu____3362 = (FStar_List.map p_atomicTerm attrs)
in (FStar_Pprint.flow break1 uu____3362))
in (FStar_Pprint.op_Hat_Hat uu____3361 FStar_Pprint.rbracket))
in (FStar_Pprint.align uu____3360))
in (FStar_Pprint.op_Hat_Hat uu____3359 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat uu____3357 uu____3358)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3356))
end))
and p_fsdoc : FStar_Parser_AST.fsdoc  ->  FStar_Pprint.document = (fun uu____3365 -> (match (uu____3365) with
| (doc1, kwd_args) -> begin
(

let kwd_args_doc = (match (kwd_args) with
| [] -> begin
FStar_Pprint.empty
end
| kwd_args1 -> begin
(

let process_kwd_arg = (fun uu____3401 -> (match (uu____3401) with
| (kwd, arg) -> begin
(

let uu____3408 = (str "@")
in (

let uu____3409 = (

let uu____3410 = (str kwd)
in (

let uu____3411 = (

let uu____3412 = (str arg)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3412))
in (FStar_Pprint.op_Hat_Hat uu____3410 uu____3411)))
in (FStar_Pprint.op_Hat_Hat uu____3408 uu____3409)))
end))
in (

let uu____3413 = (

let uu____3414 = (FStar_Pprint.separate_map FStar_Pprint.hardline process_kwd_arg kwd_args1)
in (FStar_Pprint.op_Hat_Hat uu____3414 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3413)))
end)
in (

let uu____3419 = (

let uu____3420 = (

let uu____3421 = (

let uu____3422 = (

let uu____3423 = (str doc1)
in (

let uu____3424 = (

let uu____3425 = (

let uu____3426 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3426))
in (FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3425))
in (FStar_Pprint.op_Hat_Hat uu____3423 uu____3424)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3422))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3421))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3420))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3419)))
end))
and p_justSig : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (lid, t) -> begin
(

let uu____3430 = (

let uu____3431 = (str "val")
in (

let uu____3432 = (

let uu____3433 = (

let uu____3434 = (p_lident lid)
in (

let uu____3435 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat uu____3434 uu____3435)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3433))
in (FStar_Pprint.op_Hat_Hat uu____3431 uu____3432)))
in (

let uu____3436 = (p_typ false false t)
in (FStar_Pprint.op_Hat_Hat uu____3430 uu____3436)))
end
| FStar_Parser_AST.TopLevelLet (uu____3437, lbs) -> begin
(FStar_Pprint.separate_map FStar_Pprint.hardline (fun lb -> (

let uu____3462 = (

let uu____3463 = (str "let")
in (p_letlhs uu____3463 lb))
in (FStar_Pprint.group uu____3462))) lbs)
end
| uu____3464 -> begin
FStar_Pprint.empty
end))
and p_list : (FStar_Ident.ident  ->  FStar_Pprint.document)  ->  FStar_Pprint.document  ->  FStar_Ident.ident Prims.list  ->  FStar_Pprint.document = (fun f sep l -> (

let rec p_list' = (fun uu___114_3479 -> (match (uu___114_3479) with
| [] -> begin
FStar_Pprint.empty
end
| (x)::[] -> begin
(f x)
end
| (x)::xs -> begin
(

let uu____3487 = (f x)
in (

let uu____3488 = (

let uu____3489 = (p_list' xs)
in (FStar_Pprint.op_Hat_Hat sep uu____3489))
in (FStar_Pprint.op_Hat_Hat uu____3487 uu____3488)))
end))
in (

let uu____3490 = (str "[")
in (

let uu____3491 = (

let uu____3492 = (p_list' l)
in (

let uu____3493 = (str "]")
in (FStar_Pprint.op_Hat_Hat uu____3492 uu____3493)))
in (FStar_Pprint.op_Hat_Hat uu____3490 uu____3491)))))
and p_rawDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Open (uid) -> begin
(

let uu____3496 = (

let uu____3497 = (str "open")
in (

let uu____3498 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat uu____3497 uu____3498)))
in (FStar_Pprint.group uu____3496))
end
| FStar_Parser_AST.Include (uid) -> begin
(

let uu____3500 = (

let uu____3501 = (str "include")
in (

let uu____3502 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat uu____3501 uu____3502)))
in (FStar_Pprint.group uu____3500))
end
| FStar_Parser_AST.Friend (uid) -> begin
(

let uu____3504 = (

let uu____3505 = (str "friend")
in (

let uu____3506 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat uu____3505 uu____3506)))
in (FStar_Pprint.group uu____3504))
end
| FStar_Parser_AST.ModuleAbbrev (uid1, uid2) -> begin
(

let uu____3509 = (

let uu____3510 = (str "module")
in (

let uu____3511 = (

let uu____3512 = (

let uu____3513 = (p_uident uid1)
in (

let uu____3514 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____3513 uu____3514)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3512))
in (FStar_Pprint.op_Hat_Hat uu____3510 uu____3511)))
in (

let uu____3515 = (p_quident uid2)
in (op_Hat_Slash_Plus_Hat uu____3509 uu____3515)))
end
| FStar_Parser_AST.TopLevelModule (uid) -> begin
(

let uu____3517 = (

let uu____3518 = (str "module")
in (

let uu____3519 = (

let uu____3520 = (p_quident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3520))
in (FStar_Pprint.op_Hat_Hat uu____3518 uu____3519)))
in (FStar_Pprint.group uu____3517))
end
| FStar_Parser_AST.Tycon (true, uu____3521, ((FStar_Parser_AST.TyconAbbrev (uid, tpars, FStar_Pervasives_Native.None, t), FStar_Pervasives_Native.None))::[]) -> begin
(

let effect_prefix_doc = (

let uu____3554 = (str "effect")
in (

let uu____3555 = (

let uu____3556 = (p_uident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3556))
in (FStar_Pprint.op_Hat_Hat uu____3554 uu____3555)))
in (

let uu____3557 = (

let uu____3558 = (p_typars tpars)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") effect_prefix_doc uu____3558 FStar_Pprint.equals))
in (

let uu____3559 = (p_typ false false t)
in (op_Hat_Slash_Plus_Hat uu____3557 uu____3559))))
end
| FStar_Parser_AST.Tycon (false, tc, tcdefs) -> begin
(

let s = (match (tc) with
| true -> begin
(str "class")
end
| uu____3579 -> begin
(str "type")
end)
in (

let uu____3580 = (

let uu____3581 = (FStar_List.hd tcdefs)
in (p_fsdocTypeDeclPairs s uu____3581))
in (

let uu____3594 = (

let uu____3595 = (FStar_List.tl tcdefs)
in (FStar_All.pipe_left (FStar_Pprint.concat_map (fun x -> (

let uu____3633 = (

let uu____3634 = (str "and")
in (p_fsdocTypeDeclPairs uu____3634 x))
in (FStar_Pprint.op_Hat_Hat break1 uu____3633)))) uu____3595))
in (FStar_Pprint.op_Hat_Hat uu____3580 uu____3594))))
end
| FStar_Parser_AST.TopLevelLet (q, lbs) -> begin
(

let let_doc = (

let uu____3650 = (str "let")
in (

let uu____3651 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat uu____3650 uu____3651)))
in (

let uu____3652 = (str "and")
in (separate_map_with_comments_kw let_doc uu____3652 p_letbinding lbs (fun uu____3660 -> (match (uu____3660) with
| (p, t) -> begin
(FStar_Range.union_ranges p.FStar_Parser_AST.prange t.FStar_Parser_AST.range)
end)))))
end
| FStar_Parser_AST.Val (lid, t) -> begin
(

let uu____3669 = (str "val")
in (

let uu____3670 = (

let uu____3671 = (

let uu____3672 = (p_lident lid)
in (

let uu____3673 = (

let uu____3674 = (

let uu____3675 = (

let uu____3676 = (p_typ false false t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3676))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3675))
in (FStar_Pprint.group uu____3674))
in (FStar_Pprint.op_Hat_Hat uu____3672 uu____3673)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3671))
in (FStar_Pprint.op_Hat_Hat uu____3669 uu____3670)))
end
| FStar_Parser_AST.Assume (id1, t) -> begin
(

let decl_keyword = (

let uu____3680 = (

let uu____3681 = (FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_All.pipe_right uu____3681 FStar_Util.is_upper))
in (match (uu____3680) with
| true -> begin
FStar_Pprint.empty
end
| uu____3684 -> begin
(

let uu____3685 = (str "val")
in (FStar_Pprint.op_Hat_Hat uu____3685 FStar_Pprint.space))
end))
in (

let uu____3686 = (

let uu____3687 = (p_ident id1)
in (

let uu____3688 = (

let uu____3689 = (

let uu____3690 = (

let uu____3691 = (p_typ false false t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3691))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3690))
in (FStar_Pprint.group uu____3689))
in (FStar_Pprint.op_Hat_Hat uu____3687 uu____3688)))
in (FStar_Pprint.op_Hat_Hat decl_keyword uu____3686)))
end
| FStar_Parser_AST.Exception (uid, t_opt) -> begin
(

let uu____3698 = (str "exception")
in (

let uu____3699 = (

let uu____3700 = (

let uu____3701 = (p_uident uid)
in (

let uu____3702 = (FStar_Pprint.optional (fun t -> (

let uu____3706 = (

let uu____3707 = (str "of")
in (

let uu____3708 = (p_typ false false t)
in (op_Hat_Slash_Plus_Hat uu____3707 uu____3708)))
in (FStar_Pprint.op_Hat_Hat break1 uu____3706))) t_opt)
in (FStar_Pprint.op_Hat_Hat uu____3701 uu____3702)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3700))
in (FStar_Pprint.op_Hat_Hat uu____3698 uu____3699)))
end
| FStar_Parser_AST.NewEffect (ne) -> begin
(

let uu____3710 = (str "new_effect")
in (

let uu____3711 = (

let uu____3712 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3712))
in (FStar_Pprint.op_Hat_Hat uu____3710 uu____3711)))
end
| FStar_Parser_AST.SubEffect (se) -> begin
(

let uu____3714 = (str "sub_effect")
in (

let uu____3715 = (

let uu____3716 = (p_subEffect se)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3716))
in (FStar_Pprint.op_Hat_Hat uu____3714 uu____3715)))
end
| FStar_Parser_AST.Pragma (p) -> begin
(p_pragma p)
end
| FStar_Parser_AST.Fsdoc (doc1) -> begin
(

let uu____3719 = (p_fsdoc doc1)
in (FStar_Pprint.op_Hat_Hat uu____3719 FStar_Pprint.hardline))
end
| FStar_Parser_AST.Main (uu____3720) -> begin
(failwith "*Main declaration* : Is that really still in use ??")
end
| FStar_Parser_AST.Tycon (true, uu____3721, uu____3722) -> begin
(failwith "Effect abbreviation is expected to be defined by an abbreviation")
end
| FStar_Parser_AST.Splice (ids, t) -> begin
(

let uu____3745 = (str "%splice")
in (

let uu____3746 = (

let uu____3747 = (

let uu____3748 = (str ";")
in (p_list p_uident uu____3748 ids))
in (

let uu____3749 = (

let uu____3750 = (p_term false false t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3750))
in (FStar_Pprint.op_Hat_Hat uu____3747 uu____3749)))
in (FStar_Pprint.op_Hat_Hat uu____3745 uu____3746)))
end))
and p_pragma : FStar_Parser_AST.pragma  ->  FStar_Pprint.document = (fun uu___115_3751 -> (match (uu___115_3751) with
| FStar_Parser_AST.SetOptions (s) -> begin
(

let uu____3753 = (str "#set-options")
in (

let uu____3754 = (

let uu____3755 = (

let uu____3756 = (str s)
in (FStar_Pprint.dquotes uu____3756))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3755))
in (FStar_Pprint.op_Hat_Hat uu____3753 uu____3754)))
end
| FStar_Parser_AST.ResetOptions (s_opt) -> begin
(

let uu____3760 = (str "#reset-options")
in (

let uu____3761 = (FStar_Pprint.optional (fun s -> (

let uu____3765 = (

let uu____3766 = (str s)
in (FStar_Pprint.dquotes uu____3766))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3765))) s_opt)
in (FStar_Pprint.op_Hat_Hat uu____3760 uu____3761)))
end
| FStar_Parser_AST.PushOptions (s_opt) -> begin
(

let uu____3770 = (str "#push-options")
in (

let uu____3771 = (FStar_Pprint.optional (fun s -> (

let uu____3775 = (

let uu____3776 = (str s)
in (FStar_Pprint.dquotes uu____3776))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3775))) s_opt)
in (FStar_Pprint.op_Hat_Hat uu____3770 uu____3771)))
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
and p_fsdocTypeDeclPairs : FStar_Pprint.document  ->  (FStar_Parser_AST.tycon * FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option)  ->  FStar_Pprint.document = (fun kw uu____3801 -> (match (uu____3801) with
| (typedecl, fsdoc_opt) -> begin
(

let uu____3814 = (p_typeDecl ((kw), (fsdoc_opt)) typedecl)
in (match (uu____3814) with
| (decl, body) -> begin
(

let uu____3832 = (body ())
in (FStar_Pprint.op_Hat_Hat decl uu____3832))
end))
end))
and p_typeDecl : (FStar_Pprint.document * FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option)  ->  FStar_Parser_AST.tycon  ->  (FStar_Pprint.document * (unit  ->  FStar_Pprint.document)) = (fun pre uu___116_3834 -> (match (uu___116_3834) with
| FStar_Parser_AST.TyconAbstract (lid, bs, typ_opt) -> begin
(

let empty' = (fun uu____3864 -> FStar_Pprint.empty)
in (

let uu____3865 = (p_typeDeclPrefix pre false lid bs typ_opt)
in ((uu____3865), (empty'))))
end
| FStar_Parser_AST.TyconAbbrev (lid, bs, typ_opt, t) -> begin
(

let f = (fun uu____3886 -> (

let uu____3887 = (p_typ false false t)
in (jump2 uu____3887)))
in (

let uu____3888 = (p_typeDeclPrefix pre true lid bs typ_opt)
in ((uu____3888), (f))))
end
| FStar_Parser_AST.TyconRecord (lid, bs, typ_opt, record_field_decls) -> begin
(

let p_recordFieldAndComments = (fun ps uu____3942 -> (match (uu____3942) with
| (lid1, t, doc_opt) -> begin
(

let uu____3958 = (FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range)
in (with_comment (p_recordFieldDecl ps) ((lid1), (t), (doc_opt)) uu____3958))
end))
in (

let p_fields = (fun uu____3974 -> (

let uu____3975 = (

let uu____3976 = (

let uu____3977 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (separate_map_last uu____3977 p_recordFieldAndComments record_field_decls))
in (braces_with_nesting uu____3976))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3975)))
in (

let uu____3986 = (p_typeDeclPrefix pre true lid bs typ_opt)
in ((uu____3986), (p_fields)))))
end
| FStar_Parser_AST.TyconVariant (lid, bs, typ_opt, ct_decls) -> begin
(

let p_constructorBranchAndComments = (fun uu____4047 -> (match (uu____4047) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let range = (

let uu____4073 = (

let uu____4074 = (FStar_Util.map_opt t_opt (fun t -> t.FStar_Parser_AST.range))
in (FStar_Util.dflt uid.FStar_Ident.idRange uu____4074))
in (FStar_Range.extend_to_end_of_line uu____4073))
in (with_comment p_constructorBranch ((uid), (t_opt), (doc_opt), (use_of)) range))
end))
in (

let datacon_doc = (fun uu____4100 -> (FStar_Pprint.separate_map FStar_Pprint.hardline p_constructorBranchAndComments ct_decls))
in (

let uu____4113 = (p_typeDeclPrefix pre true lid bs typ_opt)
in ((uu____4113), ((fun uu____4119 -> (

let uu____4120 = (datacon_doc ())
in (jump2 uu____4120))))))))
end))
and p_typeDeclPrefix : (FStar_Pprint.document * FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option)  ->  Prims.bool  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.knd FStar_Pervasives_Native.option  ->  FStar_Pprint.document = (fun uu____4121 eq1 lid bs typ_opt -> (match (uu____4121) with
| (kw, fsdoc_opt) -> begin
(

let maybe_with_fsdoc = (fun cont -> (

let lid_doc = (p_ident lid)
in (

let kw_lid = (

let uu____4155 = (FStar_Pprint.op_Hat_Slash_Hat kw lid_doc)
in (FStar_Pprint.group uu____4155))
in (match (fsdoc_opt) with
| FStar_Pervasives_Native.None -> begin
(cont kw_lid)
end
| FStar_Pervasives_Native.Some (fsdoc) -> begin
(

let uu____4157 = (

let uu____4160 = (

let uu____4163 = (p_fsdoc fsdoc)
in (

let uu____4164 = (

let uu____4167 = (cont lid_doc)
in (uu____4167)::[])
in (uu____4163)::uu____4164))
in (kw)::uu____4160)
in (FStar_Pprint.separate FStar_Pprint.hardline uu____4157))
end))))
in (

let typ = (

let maybe_eq = (match (eq1) with
| true -> begin
FStar_Pprint.equals
end
| uu____4170 -> begin
FStar_Pprint.empty
end)
in (match (typ_opt) with
| FStar_Pervasives_Native.None -> begin
maybe_eq
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____4172 = (

let uu____4173 = (

let uu____4174 = (p_typ false false t)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4174 maybe_eq))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4173))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4172))
end))
in (match ((Prims.op_Equality bs [])) with
| true -> begin
(maybe_with_fsdoc (fun n1 -> (prefix2 n1 typ)))
end
| uu____4180 -> begin
(

let binders = (p_binders_list true bs)
in (maybe_with_fsdoc (fun n1 -> (

let uu____4189 = (

let uu____4190 = (FStar_Pprint.flow break1 binders)
in (prefix2 n1 uu____4190))
in (prefix2 uu____4189 typ)))))
end)))
end))
and p_recordFieldDecl : Prims.bool  ->  (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option)  ->  FStar_Pprint.document = (fun ps uu____4192 -> (match (uu____4192) with
| (lid, t, doc_opt) -> begin
(

let uu____4208 = (

let uu____4209 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (

let uu____4210 = (

let uu____4211 = (p_lident lid)
in (

let uu____4212 = (

let uu____4213 = (p_typ ps false t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4213))
in (FStar_Pprint.op_Hat_Hat uu____4211 uu____4212)))
in (FStar_Pprint.op_Hat_Hat uu____4209 uu____4210)))
in (FStar_Pprint.group uu____4208))
end))
and p_constructorBranch : (FStar_Ident.ident * FStar_Parser_AST.term FStar_Pervasives_Native.option * FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option * Prims.bool)  ->  FStar_Pprint.document = (fun uu____4214 -> (match (uu____4214) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let sep = (match (use_of) with
| true -> begin
(str "of")
end
| uu____4240 -> begin
FStar_Pprint.colon
end)
in (

let uid_doc = (

let uu____4242 = (

let uu____4243 = (

let uu____4244 = (p_uident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4244))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4243))
in (FStar_Pprint.group uu____4242))
in (

let uu____4245 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (

let uu____4246 = (default_or_map uid_doc (fun t -> (

let uu____4250 = (

let uu____4251 = (

let uu____4252 = (

let uu____4253 = (

let uu____4254 = (p_typ false false t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4254))
in (FStar_Pprint.op_Hat_Hat sep uu____4253))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4252))
in (FStar_Pprint.op_Hat_Hat uid_doc uu____4251))
in (FStar_Pprint.group uu____4250))) t_opt)
in (FStar_Pprint.op_Hat_Hat uu____4245 uu____4246)))))
end))
and p_letlhs : FStar_Pprint.document  ->  (FStar_Parser_AST.pattern * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun kw uu____4256 -> (match (uu____4256) with
| (pat, uu____4262) -> begin
(

let uu____4263 = (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat1, (t, FStar_Pervasives_Native.None)) -> begin
(

let uu____4282 = (

let uu____4283 = (

let uu____4284 = (

let uu____4285 = (p_tmArrow p_tmNoEq t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4285))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4284))
in (FStar_Pprint.group uu____4283))
in ((pat1), (uu____4282)))
end
| FStar_Parser_AST.PatAscribed (pat1, (t, FStar_Pervasives_Native.Some (tac))) -> begin
(

let uu____4297 = (

let uu____4298 = (

let uu____4299 = (

let uu____4300 = (

let uu____4301 = (p_tmArrow p_tmNoEq t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4301))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4300))
in (FStar_Pprint.group uu____4299))
in (

let uu____4302 = (

let uu____4303 = (

let uu____4304 = (str "by")
in (

let uu____4305 = (

let uu____4306 = (p_atomicTerm tac)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4306))
in (FStar_Pprint.op_Hat_Hat uu____4304 uu____4305)))
in (FStar_Pprint.group uu____4303))
in (FStar_Pprint.op_Hat_Hat uu____4298 uu____4302)))
in ((pat1), (uu____4297)))
end
| uu____4307 -> begin
((pat), (FStar_Pprint.empty))
end)
in (match (uu____4263) with
| (pat1, ascr_doc) -> begin
(match (pat1.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____4311); FStar_Parser_AST.prange = uu____4312}, pats) -> begin
(

let uu____4322 = (

let uu____4323 = (

let uu____4324 = (

let uu____4325 = (p_lident x)
in (FStar_Pprint.op_Hat_Slash_Hat kw uu____4325))
in (FStar_Pprint.group uu____4324))
in (

let uu____4326 = (FStar_Pprint.flow_map break1 p_atomicPattern pats)
in (prefix2 uu____4323 uu____4326)))
in (prefix2_nonempty uu____4322 ascr_doc))
end
| uu____4327 -> begin
(

let uu____4328 = (

let uu____4329 = (

let uu____4330 = (

let uu____4331 = (p_tuplePattern pat1)
in (FStar_Pprint.op_Hat_Slash_Hat kw uu____4331))
in (FStar_Pprint.group uu____4330))
in (FStar_Pprint.op_Hat_Hat uu____4329 ascr_doc))
in (FStar_Pprint.group uu____4328))
end)
end))
end))
and p_letbinding : FStar_Pprint.document  ->  (FStar_Parser_AST.pattern * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun kw uu____4333 -> (match (uu____4333) with
| (pat, e) -> begin
(

let doc_pat = (p_letlhs kw ((pat), (e)))
in (

let doc_expr = (p_term false false e)
in (

let uu____4342 = (

let uu____4343 = (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals doc_expr)
in (FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____4343))
in (

let uu____4344 = (

let uu____4345 = (

let uu____4346 = (

let uu____4347 = (

let uu____4348 = (jump2 doc_expr)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____4348))
in (FStar_Pprint.group uu____4347))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4346))
in (FStar_Pprint.op_Hat_Hat doc_pat uu____4345))
in (FStar_Pprint.ifflat uu____4342 uu____4344)))))
end))
and p_newEffect : FStar_Parser_AST.effect_decl  ->  FStar_Pprint.document = (fun uu___117_4349 -> (match (uu___117_4349) with
| FStar_Parser_AST.RedefineEffect (lid, bs, t) -> begin
(p_effectRedefinition lid bs t)
end
| FStar_Parser_AST.DefineEffect (lid, bs, t, eff_decls) -> begin
(p_effectDefinition lid bs t eff_decls)
end))
and p_effectRedefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun uid bs t -> (

let uu____4374 = (p_uident uid)
in (

let uu____4375 = (p_binders true bs)
in (

let uu____4376 = (

let uu____4377 = (p_simpleTerm false false t)
in (prefix2 FStar_Pprint.equals uu____4377))
in (surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1") uu____4374 uu____4375 uu____4376)))))
and p_effectDefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun uid bs t eff_decls -> (

let binders = (p_binders true bs)
in (

let uu____4387 = (

let uu____4388 = (

let uu____4389 = (

let uu____4390 = (p_uident uid)
in (

let uu____4391 = (p_binders true bs)
in (

let uu____4392 = (

let uu____4393 = (p_typ false false t)
in (prefix2 FStar_Pprint.colon uu____4393))
in (surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1") uu____4390 uu____4391 uu____4392))))
in (FStar_Pprint.group uu____4389))
in (

let uu____4394 = (

let uu____4395 = (str "with")
in (

let uu____4396 = (

let uu____4397 = (

let uu____4398 = (

let uu____4399 = (

let uu____4400 = (

let uu____4401 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi FStar_Pprint.space)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4401))
in (separate_map_last uu____4400 p_effectDecl eff_decls))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4399))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4398))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4397))
in (FStar_Pprint.op_Hat_Hat uu____4395 uu____4396)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4388 uu____4394)))
in (braces_with_nesting uu____4387))))
and p_effectDecl : Prims.bool  ->  FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun ps d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (false, uu____4404, ((FStar_Parser_AST.TyconAbbrev (lid, [], FStar_Pervasives_Native.None, e), FStar_Pervasives_Native.None))::[]) -> begin
(

let uu____4433 = (

let uu____4434 = (p_lident lid)
in (

let uu____4435 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____4434 uu____4435)))
in (

let uu____4436 = (p_simpleTerm ps false e)
in (prefix2 uu____4433 uu____4436)))
end
| uu____4437 -> begin
(

let uu____4438 = (

let uu____4439 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "Not a declaration of an effect member... or at least I hope so : %s" uu____4439))
in (failwith uu____4438))
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

let p_lift = (fun ps uu____4501 -> (match (uu____4501) with
| (kwd, t) -> begin
(

let uu____4508 = (

let uu____4509 = (str kwd)
in (

let uu____4510 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____4509 uu____4510)))
in (

let uu____4511 = (p_simpleTerm ps false t)
in (prefix2 uu____4508 uu____4511)))
end))
in (separate_break_map_last FStar_Pprint.semi p_lift lifts)))
in (

let uu____4516 = (

let uu____4517 = (

let uu____4518 = (p_quident lift.FStar_Parser_AST.msource)
in (

let uu____4519 = (

let uu____4520 = (str "~>")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4520))
in (FStar_Pprint.op_Hat_Hat uu____4518 uu____4519)))
in (

let uu____4521 = (p_quident lift.FStar_Parser_AST.mdest)
in (prefix2 uu____4517 uu____4521)))
in (

let uu____4522 = (

let uu____4523 = (braces_with_nesting lift_op_doc)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4523))
in (FStar_Pprint.op_Hat_Hat uu____4516 uu____4522)))))
and p_qualifier : FStar_Parser_AST.qualifier  ->  FStar_Pprint.document = (fun uu___118_4524 -> (match (uu___118_4524) with
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
| uu____4526 -> begin
(

let uu____4527 = (

let uu____4528 = (FStar_List.map p_qualifier qs)
in (FStar_Pprint.flow break1 uu____4528))
in (FStar_Pprint.op_Hat_Hat uu____4527 FStar_Pprint.hardline))
end))
and p_letqualifier : FStar_Parser_AST.let_qualifier  ->  FStar_Pprint.document = (fun uu___119_4531 -> (match (uu___119_4531) with
| FStar_Parser_AST.Rec -> begin
(

let uu____4532 = (str "rec")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4532))
end
| FStar_Parser_AST.NoLetQualifier -> begin
FStar_Pprint.empty
end))
and p_aqual : FStar_Parser_AST.arg_qualifier  ->  FStar_Pprint.document = (fun uu___120_4533 -> (match (uu___120_4533) with
| FStar_Parser_AST.Implicit -> begin
(str "#")
end
| FStar_Parser_AST.Equality -> begin
(str "$")
end
| FStar_Parser_AST.Meta (t) -> begin
(

let uu____4535 = (str "#[")
in (

let uu____4536 = (

let uu____4537 = (p_term false false t)
in (

let uu____4538 = (str "]")
in (FStar_Pprint.op_Hat_Hat uu____4537 uu____4538)))
in (FStar_Pprint.op_Hat_Hat uu____4535 uu____4536)))
end))
and p_disjunctivePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr (pats) -> begin
(

let uu____4543 = (

let uu____4544 = (

let uu____4545 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space)
in (FStar_Pprint.op_Hat_Hat break1 uu____4545))
in (FStar_Pprint.separate_map uu____4544 p_tuplePattern pats))
in (FStar_Pprint.group uu____4543))
end
| uu____4546 -> begin
(p_tuplePattern p)
end))
and p_tuplePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTuple (pats, false) -> begin
(

let uu____4553 = (

let uu____4554 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map uu____4554 p_constructorPattern pats))
in (FStar_Pprint.group uu____4553))
end
| uu____4555 -> begin
(p_constructorPattern p)
end))
and p_constructorPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (maybe_cons_lid); FStar_Parser_AST.prange = uu____4558}, (hd1)::(tl1)::[]) when (FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid) -> begin
(

let uu____4563 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon)
in (

let uu____4564 = (p_constructorPattern hd1)
in (

let uu____4565 = (p_constructorPattern tl1)
in (infix0 uu____4563 uu____4564 uu____4565))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (uid); FStar_Parser_AST.prange = uu____4567}, pats) -> begin
(

let uu____4573 = (p_quident uid)
in (

let uu____4574 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (prefix2 uu____4573 uu____4574)))
end
| uu____4575 -> begin
(p_atomicPattern p)
end))
and p_atomicPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, (t, FStar_Pervasives_Native.None)) -> begin
(match (((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm))) with
| (FStar_Parser_AST.PatVar (lid, aqual), FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t1); FStar_Parser_AST.brange = uu____4591; FStar_Parser_AST.blevel = uu____4592; FStar_Parser_AST.aqual = uu____4593}, phi)) when (Prims.op_Equality lid.FStar_Ident.idText lid'.FStar_Ident.idText) -> begin
(

let uu____4601 = (

let uu____4602 = (p_ident lid)
in (p_refinement aqual uu____4602 t1 phi))
in (soft_parens_with_nesting uu____4601))
end
| (FStar_Parser_AST.PatWild (aqual), FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t1); FStar_Parser_AST.brange = uu____4605; FStar_Parser_AST.blevel = uu____4606; FStar_Parser_AST.aqual = uu____4607}, phi)) -> begin
(

let uu____4613 = (p_refinement aqual FStar_Pprint.underscore t1 phi)
in (soft_parens_with_nesting uu____4613))
end
| uu____4614 -> begin
(

let uu____4619 = (

let uu____4620 = (p_tuplePattern pat)
in (

let uu____4621 = (

let uu____4622 = (p_tmEqNoRefinement t)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4622))
in (FStar_Pprint.op_Hat_Hat uu____4620 uu____4621)))
in (soft_parens_with_nesting uu____4619))
end)
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let uu____4626 = (separate_break_map FStar_Pprint.semi p_tuplePattern pats)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket uu____4626 FStar_Pprint.rbracket))
end
| FStar_Parser_AST.PatRecord (pats) -> begin
(

let p_recordFieldPat = (fun uu____4643 -> (match (uu____4643) with
| (lid, pat) -> begin
(

let uu____4650 = (p_qlident lid)
in (

let uu____4651 = (p_tuplePattern pat)
in (infix2 FStar_Pprint.equals uu____4650 uu____4651)))
end))
in (

let uu____4652 = (separate_break_map FStar_Pprint.semi p_recordFieldPat pats)
in (soft_braces_with_nesting uu____4652)))
end
| FStar_Parser_AST.PatTuple (pats, true) -> begin
(

let uu____4662 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (

let uu____4663 = (separate_break_map FStar_Pprint.comma p_constructorPattern pats)
in (

let uu____4664 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____4662 uu____4663 uu____4664))))
end
| FStar_Parser_AST.PatTvar (tv, arg_qualifier_opt) -> begin
(p_tvar tv)
end
| FStar_Parser_AST.PatOp (op) -> begin
(

let uu____4673 = (

let uu____4674 = (

let uu____4675 = (

let uu____4676 = (FStar_Ident.text_of_id op)
in (str uu____4676))
in (

let uu____4677 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat uu____4675 uu____4677)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4674))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4673))
end
| FStar_Parser_AST.PatWild (aqual) -> begin
(

let uu____4681 = (FStar_Pprint.optional p_aqual aqual)
in (FStar_Pprint.op_Hat_Hat uu____4681 FStar_Pprint.underscore))
end
| FStar_Parser_AST.PatConst (c) -> begin
(p_constant c)
end
| FStar_Parser_AST.PatVar (lid, aqual) -> begin
(

let uu____4689 = (FStar_Pprint.optional p_aqual aqual)
in (

let uu____4690 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat uu____4689 uu____4690)))
end
| FStar_Parser_AST.PatName (uid) -> begin
(p_quident uid)
end
| FStar_Parser_AST.PatOr (uu____4692) -> begin
(failwith "Inner or pattern !")
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (uu____4695); FStar_Parser_AST.prange = uu____4696}, uu____4697) -> begin
(

let uu____4702 = (p_tuplePattern p)
in (soft_parens_with_nesting uu____4702))
end
| FStar_Parser_AST.PatTuple (uu____4703, false) -> begin
(

let uu____4708 = (p_tuplePattern p)
in (soft_parens_with_nesting uu____4708))
end
| uu____4709 -> begin
(

let uu____4710 = (

let uu____4711 = (FStar_Parser_AST.pat_to_string p)
in (FStar_Util.format1 "Invalid pattern %s" uu____4711))
in (failwith uu____4710))
end))
and is_typ_tuple : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____4713}, uu____4714) -> begin
true
end
| uu____4719 -> begin
false
end))
and p_binder : Prims.bool  ->  FStar_Parser_AST.binder  ->  FStar_Pprint.document = (fun is_atomic b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (lid) -> begin
(

let uu____4723 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (

let uu____4724 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat uu____4723 uu____4724)))
end
| FStar_Parser_AST.TVariable (lid) -> begin
(p_lident lid)
end
| FStar_Parser_AST.Annotated (lid, t) -> begin
(

let doc1 = (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t1); FStar_Parser_AST.brange = uu____4731; FStar_Parser_AST.blevel = uu____4732; FStar_Parser_AST.aqual = uu____4733}, phi) when (Prims.op_Equality lid.FStar_Ident.idText lid'.FStar_Ident.idText) -> begin
(

let uu____4737 = (p_lident lid)
in (p_refinement b.FStar_Parser_AST.aqual uu____4737 t1 phi))
end
| uu____4738 -> begin
(

let t' = (

let uu____4740 = (is_typ_tuple t)
in (match (uu____4740) with
| true -> begin
(

let uu____4741 = (p_tmFormula t)
in (soft_parens_with_nesting uu____4741))
end
| uu____4742 -> begin
(p_tmFormula t)
end))
in (

let uu____4743 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (

let uu____4744 = (

let uu____4745 = (p_lident lid)
in (

let uu____4746 = (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon t')
in (FStar_Pprint.op_Hat_Hat uu____4745 uu____4746)))
in (FStar_Pprint.op_Hat_Hat uu____4743 uu____4744))))
end)
in (match (is_atomic) with
| true -> begin
(

let uu____4747 = (

let uu____4748 = (FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4748))
in (FStar_Pprint.group uu____4747))
end
| uu____4749 -> begin
(FStar_Pprint.group doc1)
end))
end
| FStar_Parser_AST.TAnnotated (uu____4750) -> begin
(failwith "Is this still used ?")
end
| FStar_Parser_AST.NoName (t) -> begin
(match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t1); FStar_Parser_AST.brange = uu____4757; FStar_Parser_AST.blevel = uu____4758; FStar_Parser_AST.aqual = uu____4759}, phi) -> begin
(match (is_atomic) with
| true -> begin
(

let uu____4763 = (

let uu____4764 = (

let uu____4765 = (p_refinement b.FStar_Parser_AST.aqual FStar_Pprint.underscore t1 phi)
in (FStar_Pprint.op_Hat_Hat uu____4765 FStar_Pprint.rparen))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4764))
in (FStar_Pprint.group uu____4763))
end
| uu____4766 -> begin
(

let uu____4767 = (p_refinement b.FStar_Parser_AST.aqual FStar_Pprint.underscore t1 phi)
in (FStar_Pprint.group uu____4767))
end)
end
| uu____4768 -> begin
(match (is_atomic) with
| true -> begin
(p_atomicTerm t)
end
| uu____4769 -> begin
(p_appTerm t)
end)
end)
end))
and p_refinement : FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Pprint.document  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun aqual_opt binder t phi -> (

let is_t_atomic = (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (uu____4777) -> begin
false
end
| FStar_Parser_AST.App (uu____4788) -> begin
false
end
| FStar_Parser_AST.Op (uu____4795) -> begin
false
end
| uu____4802 -> begin
true
end)
in (

let phi1 = (p_noSeqTerm false false phi)
in (

let jump_break = (match (is_t_atomic) with
| true -> begin
(Prims.parse_int "0")
end
| uu____4805 -> begin
(Prims.parse_int "1")
end)
in (

let uu____4806 = (

let uu____4807 = (FStar_Pprint.optional p_aqual aqual_opt)
in (

let uu____4808 = (FStar_Pprint.op_Hat_Hat binder FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat uu____4807 uu____4808)))
in (

let uu____4809 = (

let uu____4810 = (p_appTerm t)
in (

let uu____4811 = (

let uu____4812 = (

let uu____4813 = (

let uu____4814 = (soft_braces_with_nesting_tight phi1)
in (

let uu____4815 = (soft_braces_with_nesting phi1)
in (FStar_Pprint.ifflat uu____4814 uu____4815)))
in (FStar_Pprint.group uu____4813))
in (FStar_Pprint.jump (Prims.parse_int "2") jump_break uu____4812))
in (FStar_Pprint.op_Hat_Hat uu____4810 uu____4811)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4806 uu____4809)))))))
and p_binders_list : Prims.bool  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Pprint.document Prims.list = (fun is_atomic bs -> (FStar_List.map (p_binder is_atomic) bs))
and p_binders : Prims.bool  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Pprint.document = (fun is_atomic bs -> (

let uu____4826 = (p_binders_list is_atomic bs)
in (separate_or_flow break1 uu____4826)))
and text_of_id_or_underscore : FStar_Ident.ident  ->  FStar_Pprint.document = (fun lid -> (

let uu____4830 = ((FStar_Util.starts_with lid.FStar_Ident.idText FStar_Ident.reserved_prefix) && (

let uu____4832 = (FStar_Options.print_real_names ())
in (not (uu____4832))))
in (match (uu____4830) with
| true -> begin
FStar_Pprint.underscore
end
| uu____4833 -> begin
(

let uu____4834 = (FStar_Ident.text_of_id lid)
in (str uu____4834))
end)))
and text_of_lid_or_underscore : FStar_Ident.lident  ->  FStar_Pprint.document = (fun lid -> (

let uu____4836 = ((FStar_Util.starts_with lid.FStar_Ident.ident.FStar_Ident.idText FStar_Ident.reserved_prefix) && (

let uu____4838 = (FStar_Options.print_real_names ())
in (not (uu____4838))))
in (match (uu____4836) with
| true -> begin
FStar_Pprint.underscore
end
| uu____4839 -> begin
(

let uu____4840 = (FStar_Ident.text_of_lid lid)
in (str uu____4840))
end)))
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
| uu____4851 -> begin
(fun x -> x)
end))
and p_term : Prims.bool  ->  Prims.bool  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun ps pb e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Seq (e1, e2) -> begin
(

let uu____4858 = (

let uu____4859 = (

let uu____4860 = (p_noSeqTerm true false e1)
in (FStar_Pprint.op_Hat_Hat uu____4860 FStar_Pprint.semi))
in (FStar_Pprint.group uu____4859))
in (

let uu____4861 = (p_term ps pb e2)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4858 uu____4861)))
end
| FStar_Parser_AST.Bind (x, e1, e2) -> begin
(

let uu____4865 = (

let uu____4866 = (

let uu____4867 = (

let uu____4868 = (p_lident x)
in (

let uu____4869 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.long_left_arrow)
in (FStar_Pprint.op_Hat_Hat uu____4868 uu____4869)))
in (

let uu____4870 = (

let uu____4871 = (p_noSeqTerm true false e1)
in (

let uu____4872 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.semi)
in (FStar_Pprint.op_Hat_Hat uu____4871 uu____4872)))
in (op_Hat_Slash_Plus_Hat uu____4867 uu____4870)))
in (FStar_Pprint.group uu____4866))
in (

let uu____4873 = (p_term ps pb e2)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4865 uu____4873)))
end
| uu____4874 -> begin
(

let uu____4875 = (p_noSeqTerm ps pb e)
in (FStar_Pprint.group uu____4875))
end))
and p_noSeqTerm : Prims.bool  ->  Prims.bool  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun ps pb e -> (with_comment (p_noSeqTerm' ps pb) e e.FStar_Parser_AST.range))
and p_noSeqTerm' : Prims.bool  ->  Prims.bool  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun ps pb e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Ascribed (e1, t, FStar_Pervasives_Native.None) -> begin
(

let uu____4886 = (

let uu____4887 = (p_tmIff e1)
in (

let uu____4888 = (

let uu____4889 = (

let uu____4890 = (p_typ ps pb t)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4890))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4889))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4887 uu____4888)))
in (FStar_Pprint.group uu____4886))
end
| FStar_Parser_AST.Ascribed (e1, t, FStar_Pervasives_Native.Some (tac)) -> begin
(

let uu____4896 = (

let uu____4897 = (p_tmIff e1)
in (

let uu____4898 = (

let uu____4899 = (

let uu____4900 = (

let uu____4901 = (p_typ false false t)
in (

let uu____4902 = (

let uu____4903 = (str "by")
in (

let uu____4904 = (p_typ ps pb tac)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4903 uu____4904)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4901 uu____4902)))
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4900))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4899))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4897 uu____4898)))
in (FStar_Pprint.group uu____4896))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = ".()<-"; FStar_Ident.idRange = uu____4905}, (e1)::(e2)::(e3)::[]) -> begin
(

let uu____4911 = (

let uu____4912 = (

let uu____4913 = (

let uu____4914 = (p_atomicTermNotQUident e1)
in (

let uu____4915 = (

let uu____4916 = (

let uu____4917 = (

let uu____4918 = (p_term false false e2)
in (soft_parens_with_nesting uu____4918))
in (

let uu____4919 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat uu____4917 uu____4919)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4916))
in (FStar_Pprint.op_Hat_Hat uu____4914 uu____4915)))
in (FStar_Pprint.group uu____4913))
in (

let uu____4920 = (

let uu____4921 = (p_noSeqTerm ps pb e3)
in (jump2 uu____4921))
in (FStar_Pprint.op_Hat_Hat uu____4912 uu____4920)))
in (FStar_Pprint.group uu____4911))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = ".[]<-"; FStar_Ident.idRange = uu____4922}, (e1)::(e2)::(e3)::[]) -> begin
(

let uu____4928 = (

let uu____4929 = (

let uu____4930 = (

let uu____4931 = (p_atomicTermNotQUident e1)
in (

let uu____4932 = (

let uu____4933 = (

let uu____4934 = (

let uu____4935 = (p_term false false e2)
in (soft_brackets_with_nesting uu____4935))
in (

let uu____4936 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat uu____4934 uu____4936)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4933))
in (FStar_Pprint.op_Hat_Hat uu____4931 uu____4932)))
in (FStar_Pprint.group uu____4930))
in (

let uu____4937 = (

let uu____4938 = (p_noSeqTerm ps pb e3)
in (jump2 uu____4938))
in (FStar_Pprint.op_Hat_Hat uu____4929 uu____4937)))
in (FStar_Pprint.group uu____4928))
end
| FStar_Parser_AST.Requires (e1, wtf) -> begin
(

let uu____4946 = (

let uu____4947 = (str "requires")
in (

let uu____4948 = (p_typ ps pb e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4947 uu____4948)))
in (FStar_Pprint.group uu____4946))
end
| FStar_Parser_AST.Ensures (e1, wtf) -> begin
(

let uu____4956 = (

let uu____4957 = (str "ensures")
in (

let uu____4958 = (p_typ ps pb e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4957 uu____4958)))
in (FStar_Pprint.group uu____4956))
end
| FStar_Parser_AST.Attributes (es) -> begin
(

let uu____4962 = (

let uu____4963 = (str "attributes")
in (

let uu____4964 = (FStar_Pprint.separate_map break1 p_atomicTerm es)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4963 uu____4964)))
in (FStar_Pprint.group uu____4962))
end
| FStar_Parser_AST.If (e1, e2, e3) -> begin
(match ((is_unit e3)) with
| true -> begin
(

let uu____4968 = (

let uu____4969 = (

let uu____4970 = (str "if")
in (

let uu____4971 = (p_noSeqTerm false false e1)
in (op_Hat_Slash_Plus_Hat uu____4970 uu____4971)))
in (

let uu____4972 = (

let uu____4973 = (str "then")
in (

let uu____4974 = (p_noSeqTerm ps pb e2)
in (op_Hat_Slash_Plus_Hat uu____4973 uu____4974)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4969 uu____4972)))
in (FStar_Pprint.group uu____4968))
end
| uu____4975 -> begin
(

let e2_doc = (match (e2.FStar_Parser_AST.tm) with
| FStar_Parser_AST.If (uu____4977, uu____4978, e31) when (is_unit e31) -> begin
(

let uu____4980 = (p_noSeqTerm false false e2)
in (soft_parens_with_nesting uu____4980))
end
| uu____4981 -> begin
(p_noSeqTerm false false e2)
end)
in (

let uu____4982 = (

let uu____4983 = (

let uu____4984 = (str "if")
in (

let uu____4985 = (p_noSeqTerm false false e1)
in (op_Hat_Slash_Plus_Hat uu____4984 uu____4985)))
in (

let uu____4986 = (

let uu____4987 = (

let uu____4988 = (str "then")
in (op_Hat_Slash_Plus_Hat uu____4988 e2_doc))
in (

let uu____4989 = (

let uu____4990 = (str "else")
in (

let uu____4991 = (p_noSeqTerm ps pb e3)
in (op_Hat_Slash_Plus_Hat uu____4990 uu____4991)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4987 uu____4989)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4983 uu____4986)))
in (FStar_Pprint.group uu____4982)))
end)
end
| FStar_Parser_AST.TryWith (e1, branches) -> begin
(

let uu____5014 = (

let uu____5015 = (

let uu____5016 = (

let uu____5017 = (str "try")
in (

let uu____5018 = (p_noSeqTerm false false e1)
in (prefix2 uu____5017 uu____5018)))
in (

let uu____5019 = (

let uu____5020 = (str "with")
in (

let uu____5021 = (separate_map_last FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5020 uu____5021)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____5016 uu____5019)))
in (FStar_Pprint.group uu____5015))
in (

let uu____5030 = (paren_if (ps || pb))
in (uu____5030 uu____5014)))
end
| FStar_Parser_AST.Match (e1, branches) -> begin
(

let uu____5057 = (

let uu____5058 = (

let uu____5059 = (

let uu____5060 = (str "match")
in (

let uu____5061 = (p_noSeqTerm false false e1)
in (

let uu____5062 = (str "with")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____5060 uu____5061 uu____5062))))
in (

let uu____5063 = (separate_map_last FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5059 uu____5063)))
in (FStar_Pprint.group uu____5058))
in (

let uu____5072 = (paren_if (ps || pb))
in (uu____5072 uu____5057)))
end
| FStar_Parser_AST.LetOpen (uid, e1) -> begin
(

let uu____5079 = (

let uu____5080 = (

let uu____5081 = (

let uu____5082 = (str "let open")
in (

let uu____5083 = (p_quident uid)
in (

let uu____5084 = (str "in")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____5082 uu____5083 uu____5084))))
in (

let uu____5085 = (p_term false pb e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5081 uu____5085)))
in (FStar_Pprint.group uu____5080))
in (

let uu____5086 = (paren_if ps)
in (uu____5086 uu____5079)))
end
| FStar_Parser_AST.Let (q, lbs, e1) -> begin
(

let p_lb = (fun q1 uu____5150 is_last -> (match (uu____5150) with
| (a, (pat, e2)) -> begin
(

let attrs = (p_attrs_opt a)
in (

let doc_let_or_and = (match (q1) with
| FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec) -> begin
(

let uu____5183 = (

let uu____5184 = (str "let")
in (

let uu____5185 = (str "rec")
in (FStar_Pprint.op_Hat_Slash_Hat uu____5184 uu____5185)))
in (FStar_Pprint.group uu____5183))
end
| FStar_Pervasives_Native.Some (FStar_Parser_AST.NoLetQualifier) -> begin
(str "let")
end
| uu____5186 -> begin
(str "and")
end)
in (

let doc_pat = (p_letlhs doc_let_or_and ((pat), (e2)))
in (

let doc_expr = (p_term false false e2)
in (

let uu____5191 = (match (is_last) with
| true -> begin
(

let uu____5192 = (FStar_Pprint.flow break1 ((doc_pat)::(FStar_Pprint.equals)::[]))
in (

let uu____5193 = (str "in")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____5192 doc_expr uu____5193)))
end
| uu____5194 -> begin
(

let uu____5195 = (FStar_Pprint.flow break1 ((doc_pat)::(FStar_Pprint.equals)::(doc_expr)::[]))
in (FStar_Pprint.hang (Prims.parse_int "2") uu____5195))
end)
in (FStar_Pprint.op_Hat_Hat attrs uu____5191))))))
end))
in (

let l = (FStar_List.length lbs)
in (

let lbs_docs = (FStar_List.mapi (fun i lb -> (match ((Prims.op_Equality i (Prims.parse_int "0"))) with
| true -> begin
(

let uu____5241 = (p_lb (FStar_Pervasives_Native.Some (q)) lb (Prims.op_Equality i (l - (Prims.parse_int "1"))))
in (FStar_Pprint.group uu____5241))
end
| uu____5248 -> begin
(

let uu____5249 = (p_lb FStar_Pervasives_Native.None lb (Prims.op_Equality i (l - (Prims.parse_int "1"))))
in (FStar_Pprint.group uu____5249))
end)) lbs)
in (

let lbs_doc = (

let uu____5257 = (FStar_Pprint.separate break1 lbs_docs)
in (FStar_Pprint.group uu____5257))
in (

let uu____5258 = (

let uu____5259 = (

let uu____5260 = (

let uu____5261 = (p_term false pb e1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5261))
in (FStar_Pprint.op_Hat_Hat lbs_doc uu____5260))
in (FStar_Pprint.group uu____5259))
in (

let uu____5262 = (paren_if ps)
in (uu____5262 uu____5258)))))))
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, typ_opt); FStar_Parser_AST.prange = uu____5269})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, branches); FStar_Parser_AST.range = uu____5272; FStar_Parser_AST.level = uu____5273}) when (matches_var maybe_x x) -> begin
(

let uu____5300 = (

let uu____5301 = (

let uu____5302 = (str "function")
in (

let uu____5303 = (separate_map_last FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5302 uu____5303)))
in (FStar_Pprint.group uu____5301))
in (

let uu____5312 = (paren_if (ps || pb))
in (uu____5312 uu____5300)))
end
| FStar_Parser_AST.Quote (e1, FStar_Parser_AST.Dynamic) -> begin
(

let uu____5318 = (

let uu____5319 = (str "quote")
in (

let uu____5320 = (p_noSeqTerm ps pb e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5319 uu____5320)))
in (FStar_Pprint.group uu____5318))
end
| FStar_Parser_AST.Quote (e1, FStar_Parser_AST.Static) -> begin
(

let uu____5322 = (

let uu____5323 = (str "`")
in (

let uu____5324 = (p_noSeqTerm ps pb e1)
in (FStar_Pprint.op_Hat_Hat uu____5323 uu____5324)))
in (FStar_Pprint.group uu____5322))
end
| FStar_Parser_AST.VQuote (e1) -> begin
(

let uu____5326 = (

let uu____5327 = (str "`%")
in (

let uu____5328 = (p_noSeqTerm ps pb e1)
in (FStar_Pprint.op_Hat_Hat uu____5327 uu____5328)))
in (FStar_Pprint.group uu____5326))
end
| FStar_Parser_AST.Antiquote ({FStar_Parser_AST.tm = FStar_Parser_AST.Quote (e1, FStar_Parser_AST.Dynamic); FStar_Parser_AST.range = uu____5330; FStar_Parser_AST.level = uu____5331}) -> begin
(

let uu____5332 = (

let uu____5333 = (str "`@")
in (

let uu____5334 = (p_noSeqTerm ps pb e1)
in (FStar_Pprint.op_Hat_Hat uu____5333 uu____5334)))
in (FStar_Pprint.group uu____5332))
end
| FStar_Parser_AST.Antiquote (e1) -> begin
(

let uu____5336 = (

let uu____5337 = (str "`#")
in (

let uu____5338 = (p_noSeqTerm ps pb e1)
in (FStar_Pprint.op_Hat_Hat uu____5337 uu____5338)))
in (FStar_Pprint.group uu____5336))
end
| uu____5339 -> begin
(p_typ ps pb e)
end))
and p_attrs_opt : FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option  ->  FStar_Pprint.document = (fun uu___121_5340 -> (match (uu___121_5340) with
| FStar_Pervasives_Native.None -> begin
FStar_Pprint.empty
end
| FStar_Pervasives_Native.Some (terms) -> begin
(

let uu____5352 = (

let uu____5353 = (str "[@")
in (

let uu____5354 = (

let uu____5355 = (FStar_Pprint.separate_map break1 p_atomicTerm terms)
in (

let uu____5356 = (str "]")
in (FStar_Pprint.op_Hat_Slash_Hat uu____5355 uu____5356)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____5353 uu____5354)))
in (FStar_Pprint.group uu____5352))
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

let uu____5382 = (

let uu____5383 = (

let uu____5384 = (p_quantifier e)
in (FStar_Pprint.op_Hat_Hat uu____5384 FStar_Pprint.space))
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") uu____5383 binders_doc FStar_Pprint.dot))
in (prefix2 uu____5382 term_doc))
end
| pats -> begin
(

let uu____5390 = (

let uu____5391 = (

let uu____5392 = (

let uu____5393 = (

let uu____5394 = (p_quantifier e)
in (FStar_Pprint.op_Hat_Hat uu____5394 FStar_Pprint.space))
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") uu____5393 binders_doc FStar_Pprint.dot))
in (

let uu____5395 = (p_trigger trigger)
in (prefix2 uu____5392 uu____5395)))
in (FStar_Pprint.group uu____5391))
in (prefix2 uu____5390 term_doc))
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

let uu____5415 = (

let uu____5416 = (

let uu____5417 = (p_quantifier e)
in (FStar_Pprint.op_Hat_Hat uu____5417 FStar_Pprint.space))
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") uu____5416 binders_doc FStar_Pprint.dot))
in (prefix2 uu____5415 term_doc))
end
| pats -> begin
(

let uu____5423 = (

let uu____5424 = (

let uu____5425 = (

let uu____5426 = (

let uu____5427 = (p_quantifier e)
in (FStar_Pprint.op_Hat_Hat uu____5427 FStar_Pprint.space))
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") uu____5426 binders_doc FStar_Pprint.dot))
in (

let uu____5428 = (p_trigger trigger)
in (prefix2 uu____5425 uu____5428)))
in (FStar_Pprint.group uu____5424))
in (prefix2 uu____5423 term_doc))
end)))
end
| uu____5429 -> begin
(p_simpleTerm ps pb e)
end))
and p_quantifier : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.QForall (uu____5431) -> begin
(str "forall")
end
| FStar_Parser_AST.QExists (uu____5444) -> begin
(str "exists")
end
| uu____5457 -> begin
(failwith "Imposible : p_quantifier called on a non-quantifier term")
end))
and p_trigger : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun uu___122_5458 -> (match (uu___122_5458) with
| [] -> begin
FStar_Pprint.empty
end
| pats -> begin
(

let uu____5470 = (

let uu____5471 = (

let uu____5472 = (

let uu____5473 = (str "pattern")
in (

let uu____5474 = (

let uu____5475 = (

let uu____5476 = (p_disjunctivePats pats)
in (FStar_Pprint.jump (Prims.parse_int "2") (Prims.parse_int "0") uu____5476))
in (FStar_Pprint.op_Hat_Hat uu____5475 FStar_Pprint.rbrace))
in (FStar_Pprint.op_Hat_Slash_Hat uu____5473 uu____5474)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5472))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____5471))
in (FStar_Pprint.group uu____5470))
end))
and p_disjunctivePats : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun pats -> (

let uu____5482 = (str "\\/")
in (FStar_Pprint.separate_map uu____5482 p_conjunctivePats pats)))
and p_conjunctivePats : FStar_Parser_AST.term Prims.list  ->  FStar_Pprint.document = (fun pats -> (

let uu____5488 = (

let uu____5489 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (FStar_Pprint.separate_map uu____5489 p_appTerm pats))
in (FStar_Pprint.group uu____5488)))
and p_simpleTerm : Prims.bool  ->  Prims.bool  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun ps pb e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Abs (pats, e1) -> begin
(

let uu____5499 = (

let uu____5500 = (

let uu____5501 = (str "fun")
in (

let uu____5502 = (

let uu____5503 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5503 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat uu____5501 uu____5502)))
in (

let uu____5504 = (p_term false pb e1)
in (op_Hat_Slash_Plus_Hat uu____5500 uu____5504)))
in (

let uu____5505 = (paren_if ps)
in (uu____5505 uu____5499)))
end
| uu____5510 -> begin
(p_tmIff e)
end))
and p_maybeFocusArrow : Prims.bool  ->  FStar_Pprint.document = (fun b -> (match (b) with
| true -> begin
(str "~>")
end
| uu____5512 -> begin
FStar_Pprint.rarrow
end))
and p_patternBranch : Prims.bool  ->  (FStar_Parser_AST.pattern * FStar_Parser_AST.term FStar_Pervasives_Native.option * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun pb uu____5514 -> (match (uu____5514) with
| (pat, when_opt, e) -> begin
(

let one_pattern_branch = (fun p -> (

let branch = (match (when_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5537 = (

let uu____5538 = (

let uu____5539 = (

let uu____5540 = (p_tuplePattern p)
in (

let uu____5541 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rarrow)
in (FStar_Pprint.op_Hat_Hat uu____5540 uu____5541)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5539))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5538))
in (FStar_Pprint.group uu____5537))
end
| FStar_Pervasives_Native.Some (f) -> begin
(

let uu____5543 = (

let uu____5544 = (

let uu____5545 = (

let uu____5546 = (

let uu____5547 = (

let uu____5548 = (p_tuplePattern p)
in (

let uu____5549 = (str "when")
in (FStar_Pprint.op_Hat_Slash_Hat uu____5548 uu____5549)))
in (FStar_Pprint.group uu____5547))
in (

let uu____5550 = (

let uu____5551 = (

let uu____5554 = (p_tmFormula f)
in (uu____5554)::(FStar_Pprint.rarrow)::[])
in (FStar_Pprint.flow break1 uu____5551))
in (FStar_Pprint.op_Hat_Slash_Hat uu____5546 uu____5550)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5545))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5544))
in (FStar_Pprint.hang (Prims.parse_int "2") uu____5543))
end)
in (

let uu____5555 = (

let uu____5556 = (p_term false pb e)
in (op_Hat_Slash_Plus_Hat branch uu____5556))
in (FStar_Pprint.group uu____5555))))
in (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr (pats) -> begin
(match ((FStar_List.rev pats)) with
| (hd1)::tl1 -> begin
(

let last_pat_branch = (one_pattern_branch hd1)
in (

let uu____5565 = (

let uu____5566 = (

let uu____5567 = (

let uu____5568 = (

let uu____5569 = (

let uu____5570 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space)
in (FStar_Pprint.op_Hat_Hat break1 uu____5570))
in (FStar_Pprint.separate_map uu____5569 p_tuplePattern (FStar_List.rev tl1)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____5568 last_pat_branch))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5567))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5566))
in (FStar_Pprint.group uu____5565)))
end
| [] -> begin
(failwith "Impossible: disjunctive pattern can\'t be empty")
end)
end
| uu____5571 -> begin
(one_pattern_branch pat)
end))
end))
and p_tmIff : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5573}, (e1)::(e2)::[]) -> begin
(

let uu____5578 = (str "<==>")
in (

let uu____5579 = (p_tmImplies e1)
in (

let uu____5580 = (p_tmIff e2)
in (infix0 uu____5578 uu____5579 uu____5580))))
end
| uu____5581 -> begin
(p_tmImplies e)
end))
and p_tmImplies : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5583}, (e1)::(e2)::[]) -> begin
(

let uu____5588 = (str "==>")
in (

let uu____5589 = (p_tmArrow p_tmFormula e1)
in (

let uu____5590 = (p_tmImplies e2)
in (infix0 uu____5588 uu____5589 uu____5590))))
end
| uu____5591 -> begin
(p_tmArrow p_tmFormula e)
end))
and p_tmArrow : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_Tm e -> (

let terms = (p_tmArrow' p_Tm e)
in (

let uu____5599 = (FStar_List.splitAt ((FStar_List.length terms) - (Prims.parse_int "1")) terms)
in (match (uu____5599) with
| (terms', last1) -> begin
(

let last_op = (match (((FStar_List.length terms) > (Prims.parse_int "1"))) with
| true -> begin
(FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rarrow)
end
| uu____5619 -> begin
FStar_Pprint.empty
end)
in (match ((FStar_List.length terms)) with
| _0_5 when (_0_5 = (Prims.parse_int "1")) -> begin
(FStar_List.hd terms)
end
| uu____5620 -> begin
(

let uu____5621 = (

let uu____5622 = (

let uu____5623 = (

let uu____5624 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5624))
in (FStar_Pprint.separate uu____5623 terms))
in (

let uu____5625 = (

let uu____5626 = (

let uu____5627 = (

let uu____5628 = (

let uu____5629 = (

let uu____5630 = (

let uu____5631 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5631))
in (FStar_Pprint.separate uu____5630 terms'))
in (FStar_Pprint.op_Hat_Hat uu____5629 last_op))
in (

let uu____5632 = (

let uu____5633 = (

let uu____5634 = (

let uu____5635 = (

let uu____5636 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5636))
in (FStar_Pprint.separate uu____5635 terms'))
in (FStar_Pprint.op_Hat_Hat uu____5634 last_op))
in (jump2 uu____5633))
in (FStar_Pprint.ifflat uu____5628 uu____5632)))
in (FStar_Pprint.group uu____5627))
in (

let uu____5637 = (FStar_List.hd last1)
in (prefix2 uu____5626 uu____5637)))
in (FStar_Pprint.ifflat uu____5622 uu____5625)))
in (FStar_Pprint.group uu____5621))
end))
end))))
and p_tmArrow' : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document Prims.list = (fun p_Tm e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Product (bs, tgt) -> begin
(

let uu____5650 = (FStar_List.map (fun b -> (p_binder false b)) bs)
in (

let uu____5655 = (p_tmArrow' p_Tm tgt)
in (FStar_List.append uu____5650 uu____5655)))
end
| uu____5658 -> begin
(

let uu____5659 = (p_Tm e)
in (uu____5659)::[])
end))
and p_tmFormula : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let conj = (

let uu____5662 = (

let uu____5663 = (str "/\\")
in (FStar_Pprint.op_Hat_Hat uu____5663 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5662))
in (

let disj = (

let uu____5665 = (

let uu____5666 = (str "\\/")
in (FStar_Pprint.op_Hat_Hat uu____5666 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5665))
in (

let formula = (p_tmDisjunction e)
in (FStar_Pprint.flow_map disj (fun d -> (FStar_Pprint.flow_map conj (fun x -> (FStar_Pprint.group x)) d)) formula)))))
and p_tmDisjunction : FStar_Parser_AST.term  ->  FStar_Pprint.document Prims.list Prims.list = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5685}, (e1)::(e2)::[]) -> begin
(

let uu____5690 = (p_tmDisjunction e1)
in (

let uu____5695 = (

let uu____5700 = (p_tmConjunction e2)
in (uu____5700)::[])
in (FStar_List.append uu____5690 uu____5695)))
end
| uu____5709 -> begin
(

let uu____5710 = (p_tmConjunction e)
in (uu____5710)::[])
end))
and p_tmConjunction : FStar_Parser_AST.term  ->  FStar_Pprint.document Prims.list = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5720}, (e1)::(e2)::[]) -> begin
(

let uu____5725 = (p_tmConjunction e1)
in (

let uu____5728 = (

let uu____5731 = (p_tmTuple e2)
in (uu____5731)::[])
in (FStar_List.append uu____5725 uu____5728)))
end
| uu____5732 -> begin
(

let uu____5733 = (p_tmTuple e)
in (uu____5733)::[])
end))
and p_tmTuple : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_tmTuple' e e.FStar_Parser_AST.range))
and p_tmTuple' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (lid, args) when ((is_tuple_constructor lid) && (all_explicit args)) -> begin
(

let uu____5750 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map uu____5750 (fun uu____5758 -> (match (uu____5758) with
| (e1, uu____5764) -> begin
(p_tmEq e1)
end)) args))
end
| uu____5765 -> begin
(p_tmEq e)
end))
and paren_if_gt : Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun curr mine doc1 -> (match ((mine <= curr)) with
| true -> begin
doc1
end
| uu____5769 -> begin
(

let uu____5770 = (

let uu____5771 = (FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5771))
in (FStar_Pprint.group uu____5770))
end))
and p_tmEqWith : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_X e -> (

let n1 = (max_level (FStar_List.append ((colon_equals)::(pipe_right)::[]) operatorInfix0ad12))
in (p_tmEqWith' p_X n1 e)))
and p_tmEqWith' : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_X curr e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (((is_operatorInfix0ad12 op) || (

let uu____5788 = (FStar_Ident.text_of_id op)
in (Prims.op_Equality uu____5788 "="))) || (

let uu____5790 = (FStar_Ident.text_of_id op)
in (Prims.op_Equality uu____5790 "|>"))) -> begin
(

let op1 = (FStar_Ident.text_of_id op)
in (

let uu____5792 = (levels op1)
in (match (uu____5792) with
| (left1, mine, right1) -> begin
(

let uu____5802 = (

let uu____5803 = (FStar_All.pipe_left str op1)
in (

let uu____5804 = (p_tmEqWith' p_X left1 e1)
in (

let uu____5805 = (p_tmEqWith' p_X right1 e2)
in (infix0 uu____5803 uu____5804 uu____5805))))
in (paren_if_gt curr mine uu____5802))
end)))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5806}, (e1)::(e2)::[]) -> begin
(

let uu____5811 = (

let uu____5812 = (p_tmEqWith p_X e1)
in (

let uu____5813 = (

let uu____5814 = (

let uu____5815 = (

let uu____5816 = (p_tmEqWith p_X e2)
in (op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5816))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5815))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5814))
in (FStar_Pprint.op_Hat_Hat uu____5812 uu____5813)))
in (FStar_Pprint.group uu____5811))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5817}, (e1)::[]) -> begin
(

let uu____5821 = (levels "-")
in (match (uu____5821) with
| (left1, mine, right1) -> begin
(

let uu____5831 = (p_tmEqWith' p_X mine e1)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5831))
end))
end
| uu____5832 -> begin
(p_tmNoEqWith p_X e)
end))
and p_tmNoEqWith : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_X e -> (

let n1 = (max_level ((colon_colon)::(amp)::(opinfix3)::(opinfix4)::[]))
in (p_tmNoEqWith' false p_X n1 e)))
and p_tmNoEqWith' : Prims.bool  ->  (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun inside_tuple p_X curr e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (lid, ((e1, uu____5876))::((e2, uu____5878))::[]) when ((FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) && (

let uu____5898 = (is_list e)
in (not (uu____5898)))) -> begin
(

let op = "::"
in (

let uu____5900 = (levels op)
in (match (uu____5900) with
| (left1, mine, right1) -> begin
(

let uu____5910 = (

let uu____5911 = (str op)
in (

let uu____5912 = (p_tmNoEqWith' false p_X left1 e1)
in (

let uu____5913 = (p_tmNoEqWith' false p_X right1 e2)
in (infix0 uu____5911 uu____5912 uu____5913))))
in (paren_if_gt curr mine uu____5910))
end)))
end
| FStar_Parser_AST.Sum (binders, res) -> begin
(

let op = "&"
in (

let uu____5929 = (levels op)
in (match (uu____5929) with
| (left1, mine, right1) -> begin
(

let p_dsumfst = (fun bt -> (match (bt) with
| FStar_Util.Inl (b) -> begin
(

let uu____5954 = (p_binder false b)
in (

let uu____5955 = (

let uu____5956 = (

let uu____5957 = (str op)
in (FStar_Pprint.op_Hat_Hat uu____5957 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5956))
in (FStar_Pprint.op_Hat_Hat uu____5954 uu____5955)))
end
| FStar_Util.Inr (t) -> begin
(

let uu____5959 = (p_tmNoEqWith' false p_X left1 t)
in (

let uu____5960 = (

let uu____5961 = (

let uu____5962 = (str op)
in (FStar_Pprint.op_Hat_Hat uu____5962 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5961))
in (FStar_Pprint.op_Hat_Hat uu____5959 uu____5960)))
end))
in (

let uu____5963 = (

let uu____5964 = (FStar_Pprint.concat_map p_dsumfst binders)
in (

let uu____5969 = (p_tmNoEqWith' false p_X right1 res)
in (FStar_Pprint.op_Hat_Hat uu____5964 uu____5969)))
in (paren_if_gt curr mine uu____5963)))
end)))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____5970}, (e1)::(e2)::[]) when (FStar_ST.op_Bang unfold_tuples) -> begin
(

let op = "*"
in (

let uu____5995 = (levels op)
in (match (uu____5995) with
| (left1, mine, right1) -> begin
(match (inside_tuple) with
| true -> begin
(

let uu____6005 = (str op)
in (

let uu____6006 = (p_tmNoEqWith' true p_X left1 e1)
in (

let uu____6007 = (p_tmNoEqWith' true p_X right1 e2)
in (infix0 uu____6005 uu____6006 uu____6007))))
end
| uu____6008 -> begin
(

let uu____6009 = (

let uu____6010 = (str op)
in (

let uu____6011 = (p_tmNoEqWith' true p_X left1 e1)
in (

let uu____6012 = (p_tmNoEqWith' true p_X right1 e2)
in (infix0 uu____6010 uu____6011 uu____6012))))
in (paren_if_gt curr mine uu____6009))
end)
end)))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (is_operatorInfix34 op) -> begin
(

let op1 = (FStar_Ident.text_of_id op)
in (

let uu____6019 = (levels op1)
in (match (uu____6019) with
| (left1, mine, right1) -> begin
(

let uu____6029 = (

let uu____6030 = (str op1)
in (

let uu____6031 = (p_tmNoEqWith' false p_X left1 e1)
in (

let uu____6032 = (p_tmNoEqWith' false p_X right1 e2)
in (infix0 uu____6030 uu____6031 uu____6032))))
in (paren_if_gt curr mine uu____6029))
end)))
end
| FStar_Parser_AST.Record (with_opt, record_fields) -> begin
(

let uu____6051 = (

let uu____6052 = (default_or_map FStar_Pprint.empty p_with_clause with_opt)
in (

let uu____6053 = (

let uu____6054 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (separate_map_last uu____6054 p_simpleDef record_fields))
in (FStar_Pprint.op_Hat_Hat uu____6052 uu____6053)))
in (braces_with_nesting uu____6051))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____6059}, (e1)::[]) -> begin
(

let uu____6063 = (

let uu____6064 = (str "~")
in (

let uu____6065 = (p_atomicTerm e1)
in (FStar_Pprint.op_Hat_Hat uu____6064 uu____6065)))
in (FStar_Pprint.group uu____6063))
end
| FStar_Parser_AST.Paren (p) when inside_tuple -> begin
(match (p.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____6067}, (e1)::(e2)::[]) -> begin
(

let op = "*"
in (

let uu____6073 = (levels op)
in (match (uu____6073) with
| (left1, mine, right1) -> begin
(

let uu____6083 = (

let uu____6084 = (str op)
in (

let uu____6085 = (p_tmNoEqWith' true p_X left1 e1)
in (

let uu____6086 = (p_tmNoEqWith' true p_X right1 e2)
in (infix0 uu____6084 uu____6085 uu____6086))))
in (paren_if_gt curr mine uu____6083))
end)))
end
| uu____6087 -> begin
(p_X e)
end)
end
| uu____6088 -> begin
(p_X e)
end))
and p_tmEqNoRefinement : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_tmEqWith p_appTerm e))
and p_tmEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_tmEqWith p_tmRefinement e))
and p_tmNoEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_tmNoEqWith p_tmRefinement e))
and p_tmRefinement : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.NamedTyp (lid, e1) -> begin
(

let uu____6095 = (

let uu____6096 = (p_lident lid)
in (

let uu____6097 = (

let uu____6098 = (p_appTerm e1)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6098))
in (FStar_Pprint.op_Hat_Slash_Hat uu____6096 uu____6097)))
in (FStar_Pprint.group uu____6095))
end
| FStar_Parser_AST.Refine (b, phi) -> begin
(p_refinedBinder b phi)
end
| uu____6101 -> begin
(p_appTerm e)
end))
and p_with_clause : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____6103 = (p_appTerm e)
in (

let uu____6104 = (

let uu____6105 = (

let uu____6106 = (str "with")
in (FStar_Pprint.op_Hat_Hat uu____6106 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6105))
in (FStar_Pprint.op_Hat_Hat uu____6103 uu____6104))))
and p_refinedBinder : FStar_Parser_AST.binder  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun b phi -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (lid, t) -> begin
(

let uu____6111 = (p_lident lid)
in (p_refinement b.FStar_Parser_AST.aqual uu____6111 t phi))
end
| FStar_Parser_AST.TAnnotated (uu____6112) -> begin
(failwith "Is this still used ?")
end
| FStar_Parser_AST.Variable (uu____6117) -> begin
(

let uu____6118 = (

let uu____6119 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" uu____6119))
in (failwith uu____6118))
end
| FStar_Parser_AST.TVariable (uu____6120) -> begin
(

let uu____6121 = (

let uu____6122 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" uu____6122))
in (failwith uu____6121))
end
| FStar_Parser_AST.NoName (uu____6123) -> begin
(

let uu____6124 = (

let uu____6125 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" uu____6125))
in (failwith uu____6124))
end))
and p_simpleDef : Prims.bool  ->  (FStar_Ident.lid * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun ps uu____6127 -> (match (uu____6127) with
| (lid, e) -> begin
(

let uu____6134 = (

let uu____6135 = (p_qlident lid)
in (

let uu____6136 = (

let uu____6137 = (p_noSeqTerm ps false e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____6137))
in (FStar_Pprint.op_Hat_Slash_Hat uu____6135 uu____6136)))
in (FStar_Pprint.group uu____6134))
end))
and p_appTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App (uu____6139) when (is_general_application e) -> begin
(

let uu____6146 = (head_and_args e)
in (match (uu____6146) with
| (head1, args) -> begin
(

let uu____6171 = (

let uu____6182 = (FStar_ST.op_Bang should_print_fs_typ_app)
in (match (uu____6182) with
| true -> begin
(

let uu____6212 = (FStar_Util.take (fun uu____6236 -> (match (uu____6236) with
| (uu____6241, aq) -> begin
(Prims.op_Equality aq FStar_Parser_AST.FsTypApp)
end)) args)
in (match (uu____6212) with
| (fs_typ_args, args1) -> begin
(

let uu____6279 = (

let uu____6280 = (p_indexingTerm head1)
in (

let uu____6281 = (

let uu____6282 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (soft_surround_map_or_flow (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.empty FStar_Pprint.langle uu____6282 FStar_Pprint.rangle p_fsTypArg fs_typ_args))
in (FStar_Pprint.op_Hat_Hat uu____6280 uu____6281)))
in ((uu____6279), (args1)))
end))
end
| uu____6293 -> begin
(

let uu____6294 = (p_indexingTerm head1)
in ((uu____6294), (args)))
end))
in (match (uu____6171) with
| (head_doc, args1) -> begin
(

let uu____6315 = (

let uu____6316 = (FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space)
in (soft_surround_map_or_flow (Prims.parse_int "2") (Prims.parse_int "0") head_doc uu____6316 break1 FStar_Pprint.empty p_argTerm args1))
in (FStar_Pprint.group uu____6315))
end))
end))
end
| FStar_Parser_AST.Construct (lid, args) when ((is_general_construction e) && (

let uu____6336 = (is_dtuple_constructor lid)
in (not (uu____6336)))) -> begin
(match (args) with
| [] -> begin
(p_quident lid)
end
| (arg)::[] -> begin
(

let uu____6354 = (

let uu____6355 = (p_quident lid)
in (

let uu____6356 = (p_argTerm arg)
in (FStar_Pprint.op_Hat_Slash_Hat uu____6355 uu____6356)))
in (FStar_Pprint.group uu____6354))
end
| (hd1)::tl1 -> begin
(

let uu____6373 = (

let uu____6374 = (

let uu____6375 = (

let uu____6376 = (p_quident lid)
in (

let uu____6377 = (p_argTerm hd1)
in (prefix2 uu____6376 uu____6377)))
in (FStar_Pprint.group uu____6375))
in (

let uu____6378 = (

let uu____6379 = (FStar_Pprint.separate_map break1 p_argTerm tl1)
in (jump2 uu____6379))
in (FStar_Pprint.op_Hat_Hat uu____6374 uu____6378)))
in (FStar_Pprint.group uu____6373))
end)
end
| uu____6384 -> begin
(p_indexingTerm e)
end))
and p_argTerm : (FStar_Parser_AST.term * FStar_Parser_AST.imp)  ->  FStar_Pprint.document = (fun arg_imp -> (match (arg_imp) with
| (u, FStar_Parser_AST.UnivApp) -> begin
(p_universe u)
end
| (e, FStar_Parser_AST.FsTypApp) -> begin
((FStar_Errors.log_issue e.FStar_Parser_AST.range ((FStar_Errors.Warning_UnexpectedFsTypApp), ("Unexpected FsTypApp, output might not be formatted correctly.")));
(

let uu____6393 = (p_indexingTerm e)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.langle uu____6393 FStar_Pprint.rangle));
)
end
| (e, FStar_Parser_AST.Hash) -> begin
(

let uu____6395 = (str "#")
in (

let uu____6396 = (p_indexingTerm e)
in (FStar_Pprint.op_Hat_Hat uu____6395 uu____6396)))
end
| (e, FStar_Parser_AST.HashBrace (t)) -> begin
(

let uu____6399 = (str "#[")
in (

let uu____6400 = (

let uu____6401 = (p_indexingTerm t)
in (

let uu____6402 = (

let uu____6403 = (str "]")
in (

let uu____6404 = (p_indexingTerm e)
in (FStar_Pprint.op_Hat_Hat uu____6403 uu____6404)))
in (FStar_Pprint.op_Hat_Hat uu____6401 uu____6402)))
in (FStar_Pprint.op_Hat_Hat uu____6399 uu____6400)))
end
| (e, FStar_Parser_AST.Nothing) -> begin
(p_indexingTerm e)
end))
and p_fsTypArg : (FStar_Parser_AST.term * FStar_Parser_AST.imp)  ->  FStar_Pprint.document = (fun uu____6406 -> (match (uu____6406) with
| (e, uu____6412) -> begin
(p_indexingTerm e)
end))
and p_indexingTerm_aux : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun exit1 e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____6417}, (e1)::(e2)::[]) -> begin
(

let uu____6422 = (

let uu____6423 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (

let uu____6424 = (

let uu____6425 = (

let uu____6426 = (p_term false false e2)
in (soft_parens_with_nesting uu____6426))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6425))
in (FStar_Pprint.op_Hat_Hat uu____6423 uu____6424)))
in (FStar_Pprint.group uu____6422))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____6427}, (e1)::(e2)::[]) -> begin
(

let uu____6432 = (

let uu____6433 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (

let uu____6434 = (

let uu____6435 = (

let uu____6436 = (p_term false false e2)
in (soft_brackets_with_nesting uu____6436))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6435))
in (FStar_Pprint.op_Hat_Hat uu____6433 uu____6434)))
in (FStar_Pprint.group uu____6432))
end
| uu____6437 -> begin
(exit1 e)
end))
and p_indexingTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_indexingTerm_aux p_atomicTerm e))
and p_atomicTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.LetOpen (lid, e1) -> begin
(

let uu____6442 = (p_quident lid)
in (

let uu____6443 = (

let uu____6444 = (

let uu____6445 = (p_term false false e1)
in (soft_parens_with_nesting uu____6445))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6444))
in (FStar_Pprint.op_Hat_Hat uu____6442 uu____6443)))
end
| FStar_Parser_AST.Name (lid) -> begin
(p_quident lid)
end
| FStar_Parser_AST.Op (op, (e1)::[]) when (is_general_prefix_op op) -> begin
(

let uu____6451 = (

let uu____6452 = (FStar_Ident.text_of_id op)
in (str uu____6452))
in (

let uu____6453 = (p_atomicTerm e1)
in (FStar_Pprint.op_Hat_Hat uu____6451 uu____6453)))
end
| uu____6454 -> begin
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
| uu____6463 -> begin
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

let uu____6470 = (

let uu____6471 = (FStar_Ident.text_of_id op)
in (str uu____6471))
in (

let uu____6472 = (p_atomicTermNotQUident e1)
in (FStar_Pprint.op_Hat_Hat uu____6470 uu____6472)))
end
| FStar_Parser_AST.Op (op, []) -> begin
(

let uu____6476 = (

let uu____6477 = (

let uu____6478 = (

let uu____6479 = (FStar_Ident.text_of_id op)
in (str uu____6479))
in (

let uu____6480 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat uu____6478 uu____6480)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6477))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6476))
end
| FStar_Parser_AST.Construct (lid, args) when (is_dtuple_constructor lid) -> begin
(

let uu____6495 = (all_explicit args)
in (match (uu____6495) with
| true -> begin
(

let uu____6496 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (

let uu____6497 = (

let uu____6498 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (

let uu____6499 = (FStar_List.map FStar_Pervasives_Native.fst args)
in (FStar_Pprint.separate_map uu____6498 p_tmEq uu____6499)))
in (

let uu____6506 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____6496 uu____6497 uu____6506))))
end
| uu____6507 -> begin
(match (args) with
| [] -> begin
(p_quident lid)
end
| (arg)::[] -> begin
(

let uu____6525 = (

let uu____6526 = (p_quident lid)
in (

let uu____6527 = (p_argTerm arg)
in (FStar_Pprint.op_Hat_Slash_Hat uu____6526 uu____6527)))
in (FStar_Pprint.group uu____6525))
end
| (hd1)::tl1 -> begin
(

let uu____6544 = (

let uu____6545 = (

let uu____6546 = (

let uu____6547 = (p_quident lid)
in (

let uu____6548 = (p_argTerm hd1)
in (prefix2 uu____6547 uu____6548)))
in (FStar_Pprint.group uu____6546))
in (

let uu____6549 = (

let uu____6550 = (FStar_Pprint.separate_map break1 p_argTerm tl1)
in (jump2 uu____6550))
in (FStar_Pprint.op_Hat_Hat uu____6545 uu____6549)))
in (FStar_Pprint.group uu____6544))
end)
end))
end
| FStar_Parser_AST.Project (e1, lid) -> begin
(

let uu____6557 = (

let uu____6558 = (p_atomicTermNotQUident e1)
in (

let uu____6559 = (

let uu____6560 = (p_qlident lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6560))
in (FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0") uu____6558 uu____6559)))
in (FStar_Pprint.group uu____6557))
end
| uu____6561 -> begin
(p_projectionLHS e)
end))
and p_projectionLHS : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (lid) -> begin
(p_qlident lid)
end
| FStar_Parser_AST.Projector (constr_lid, field_lid) -> begin
(

let uu____6566 = (p_quident constr_lid)
in (

let uu____6567 = (

let uu____6568 = (

let uu____6569 = (p_lident field_lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6569))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6568))
in (FStar_Pprint.op_Hat_Hat uu____6566 uu____6567)))
end
| FStar_Parser_AST.Discrim (constr_lid) -> begin
(

let uu____6571 = (p_quident constr_lid)
in (FStar_Pprint.op_Hat_Hat uu____6571 FStar_Pprint.qmark))
end
| FStar_Parser_AST.Paren (e1) -> begin
(

let uu____6573 = (p_term false false e1)
in (soft_parens_with_nesting uu____6573))
end
| uu____6574 when (is_array e) -> begin
(

let es = (extract_from_list e)
in (

let uu____6578 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar)
in (

let uu____6579 = (

let uu____6580 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (separate_map_or_flow_last uu____6580 (fun ps -> (p_noSeqTerm ps false)) es))
in (

let uu____6583 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") uu____6578 uu____6579 uu____6583)))))
end
| uu____6584 when (is_list e) -> begin
(

let uu____6585 = (

let uu____6586 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (

let uu____6587 = (extract_from_list e)
in (separate_map_or_flow_last uu____6586 (fun ps -> (p_noSeqTerm ps false)) uu____6587)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket uu____6585 FStar_Pprint.rbracket))
end
| uu____6592 when (is_lex_list e) -> begin
(

let uu____6593 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket)
in (

let uu____6594 = (

let uu____6595 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (

let uu____6596 = (extract_from_list e)
in (separate_map_or_flow_last uu____6595 (fun ps -> (p_noSeqTerm ps false)) uu____6596)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____6593 uu____6594 FStar_Pprint.rbracket)))
end
| uu____6601 when (is_ref_set e) -> begin
(

let es = (extract_from_ref_set e)
in (

let uu____6605 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace)
in (

let uu____6606 = (

let uu____6607 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (separate_map_or_flow uu____6607 p_appTerm es))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") uu____6605 uu____6606 FStar_Pprint.rbrace))))
end
| FStar_Parser_AST.Labeled (e1, s, b) -> begin
(

let uu____6611 = (str (Prims.strcat "(*" (Prims.strcat s "*)")))
in (

let uu____6612 = (p_term false false e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____6611 uu____6612)))
end
| FStar_Parser_AST.Op (op, args) when (

let uu____6619 = (handleable_op op args)
in (not (uu____6619))) -> begin
(

let uu____6620 = (

let uu____6621 = (

let uu____6622 = (FStar_Ident.text_of_id op)
in (

let uu____6623 = (

let uu____6624 = (

let uu____6625 = (FStar_Util.string_of_int (FStar_List.length args))
in (Prims.strcat uu____6625 " arguments couldn\'t be handled by the pretty printer"))
in (Prims.strcat " with " uu____6624))
in (Prims.strcat uu____6622 uu____6623)))
in (Prims.strcat "Operation " uu____6621))
in (failwith uu____6620))
end
| FStar_Parser_AST.Uvar (id1) -> begin
(

let uu____6627 = (str "u#")
in (

let uu____6628 = (str id1.FStar_Ident.idText)
in (FStar_Pprint.op_Hat_Hat uu____6627 uu____6628)))
end
| FStar_Parser_AST.Wild -> begin
(

let uu____6629 = (p_term false false e)
in (soft_parens_with_nesting uu____6629))
end
| FStar_Parser_AST.Const (uu____6630) -> begin
(

let uu____6631 = (p_term false false e)
in (soft_parens_with_nesting uu____6631))
end
| FStar_Parser_AST.Op (uu____6632) -> begin
(

let uu____6639 = (p_term false false e)
in (soft_parens_with_nesting uu____6639))
end
| FStar_Parser_AST.Tvar (uu____6640) -> begin
(

let uu____6641 = (p_term false false e)
in (soft_parens_with_nesting uu____6641))
end
| FStar_Parser_AST.Var (uu____6642) -> begin
(

let uu____6643 = (p_term false false e)
in (soft_parens_with_nesting uu____6643))
end
| FStar_Parser_AST.Name (uu____6644) -> begin
(

let uu____6645 = (p_term false false e)
in (soft_parens_with_nesting uu____6645))
end
| FStar_Parser_AST.Construct (uu____6646) -> begin
(

let uu____6657 = (p_term false false e)
in (soft_parens_with_nesting uu____6657))
end
| FStar_Parser_AST.Abs (uu____6658) -> begin
(

let uu____6665 = (p_term false false e)
in (soft_parens_with_nesting uu____6665))
end
| FStar_Parser_AST.App (uu____6666) -> begin
(

let uu____6673 = (p_term false false e)
in (soft_parens_with_nesting uu____6673))
end
| FStar_Parser_AST.Let (uu____6674) -> begin
(

let uu____6695 = (p_term false false e)
in (soft_parens_with_nesting uu____6695))
end
| FStar_Parser_AST.LetOpen (uu____6696) -> begin
(

let uu____6701 = (p_term false false e)
in (soft_parens_with_nesting uu____6701))
end
| FStar_Parser_AST.Seq (uu____6702) -> begin
(

let uu____6707 = (p_term false false e)
in (soft_parens_with_nesting uu____6707))
end
| FStar_Parser_AST.Bind (uu____6708) -> begin
(

let uu____6715 = (p_term false false e)
in (soft_parens_with_nesting uu____6715))
end
| FStar_Parser_AST.If (uu____6716) -> begin
(

let uu____6723 = (p_term false false e)
in (soft_parens_with_nesting uu____6723))
end
| FStar_Parser_AST.Match (uu____6724) -> begin
(

let uu____6739 = (p_term false false e)
in (soft_parens_with_nesting uu____6739))
end
| FStar_Parser_AST.TryWith (uu____6740) -> begin
(

let uu____6755 = (p_term false false e)
in (soft_parens_with_nesting uu____6755))
end
| FStar_Parser_AST.Ascribed (uu____6756) -> begin
(

let uu____6765 = (p_term false false e)
in (soft_parens_with_nesting uu____6765))
end
| FStar_Parser_AST.Record (uu____6766) -> begin
(

let uu____6779 = (p_term false false e)
in (soft_parens_with_nesting uu____6779))
end
| FStar_Parser_AST.Project (uu____6780) -> begin
(

let uu____6785 = (p_term false false e)
in (soft_parens_with_nesting uu____6785))
end
| FStar_Parser_AST.Product (uu____6786) -> begin
(

let uu____6793 = (p_term false false e)
in (soft_parens_with_nesting uu____6793))
end
| FStar_Parser_AST.Sum (uu____6794) -> begin
(

let uu____6805 = (p_term false false e)
in (soft_parens_with_nesting uu____6805))
end
| FStar_Parser_AST.QForall (uu____6806) -> begin
(

let uu____6819 = (p_term false false e)
in (soft_parens_with_nesting uu____6819))
end
| FStar_Parser_AST.QExists (uu____6820) -> begin
(

let uu____6833 = (p_term false false e)
in (soft_parens_with_nesting uu____6833))
end
| FStar_Parser_AST.Refine (uu____6834) -> begin
(

let uu____6839 = (p_term false false e)
in (soft_parens_with_nesting uu____6839))
end
| FStar_Parser_AST.NamedTyp (uu____6840) -> begin
(

let uu____6845 = (p_term false false e)
in (soft_parens_with_nesting uu____6845))
end
| FStar_Parser_AST.Requires (uu____6846) -> begin
(

let uu____6853 = (p_term false false e)
in (soft_parens_with_nesting uu____6853))
end
| FStar_Parser_AST.Ensures (uu____6854) -> begin
(

let uu____6861 = (p_term false false e)
in (soft_parens_with_nesting uu____6861))
end
| FStar_Parser_AST.Attributes (uu____6862) -> begin
(

let uu____6865 = (p_term false false e)
in (soft_parens_with_nesting uu____6865))
end
| FStar_Parser_AST.Quote (uu____6866) -> begin
(

let uu____6871 = (p_term false false e)
in (soft_parens_with_nesting uu____6871))
end
| FStar_Parser_AST.VQuote (uu____6872) -> begin
(

let uu____6873 = (p_term false false e)
in (soft_parens_with_nesting uu____6873))
end
| FStar_Parser_AST.Antiquote (uu____6874) -> begin
(

let uu____6875 = (p_term false false e)
in (soft_parens_with_nesting uu____6875))
end))
and p_constant : FStar_Const.sconst  ->  FStar_Pprint.document = (fun uu___125_6876 -> (match (uu___125_6876) with
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
| FStar_Const.Const_string (s, uu____6882) -> begin
(

let uu____6883 = (str s)
in (FStar_Pprint.dquotes uu____6883))
end
| FStar_Const.Const_bytearray (bytes, uu____6885) -> begin
(

let uu____6890 = (

let uu____6891 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes uu____6891))
in (

let uu____6892 = (str "B")
in (FStar_Pprint.op_Hat_Hat uu____6890 uu____6892)))
end
| FStar_Const.Const_int (repr, sign_width_opt) -> begin
(

let signedness = (fun uu___123_6912 -> (match (uu___123_6912) with
| FStar_Const.Unsigned -> begin
(str "u")
end
| FStar_Const.Signed -> begin
FStar_Pprint.empty
end))
in (

let width = (fun uu___124_6918 -> (match (uu___124_6918) with
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

let ending = (default_or_map FStar_Pprint.empty (fun uu____6929 -> (match (uu____6929) with
| (s, w) -> begin
(

let uu____6936 = (signedness s)
in (

let uu____6937 = (width w)
in (FStar_Pprint.op_Hat_Hat uu____6936 uu____6937)))
end)) sign_width_opt)
in (

let uu____6938 = (str repr)
in (FStar_Pprint.op_Hat_Hat uu____6938 ending)))))
end
| FStar_Const.Const_range_of -> begin
(str "range_of")
end
| FStar_Const.Const_set_range_of -> begin
(str "set_range_of")
end
| FStar_Const.Const_range (r) -> begin
(

let uu____6940 = (FStar_Range.string_of_range r)
in (str uu____6940))
end
| FStar_Const.Const_reify -> begin
(str "reify")
end
| FStar_Const.Const_reflect (lid) -> begin
(

let uu____6942 = (p_quident lid)
in (

let uu____6943 = (

let uu____6944 = (

let uu____6945 = (str "reflect")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6945))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6944))
in (FStar_Pprint.op_Hat_Hat uu____6942 uu____6943)))
end))
and p_universe : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (

let uu____6947 = (str "u#")
in (

let uu____6948 = (p_atomicUniverse u)
in (FStar_Pprint.op_Hat_Hat uu____6947 uu____6948))))
and p_universeFrom : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match (u.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6950}, (u1)::(u2)::[]) -> begin
(

let uu____6955 = (

let uu____6956 = (p_universeFrom u1)
in (

let uu____6957 = (

let uu____6958 = (p_universeFrom u2)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6958))
in (FStar_Pprint.op_Hat_Slash_Hat uu____6956 uu____6957)))
in (FStar_Pprint.group uu____6955))
end
| FStar_Parser_AST.App (uu____6959) -> begin
(

let uu____6966 = (head_and_args u)
in (match (uu____6966) with
| (head1, args) -> begin
(match (head1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (maybe_max_lid) when (FStar_Ident.lid_equals maybe_max_lid FStar_Parser_Const.max_lid) -> begin
(

let uu____6992 = (

let uu____6993 = (p_qlident FStar_Parser_Const.max_lid)
in (

let uu____6994 = (FStar_Pprint.separate_map FStar_Pprint.space (fun uu____7002 -> (match (uu____7002) with
| (u1, uu____7008) -> begin
(p_atomicUniverse u1)
end)) args)
in (op_Hat_Slash_Plus_Hat uu____6993 uu____6994)))
in (FStar_Pprint.group uu____6992))
end
| uu____7009 -> begin
(

let uu____7010 = (

let uu____7011 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" uu____7011))
in (failwith uu____7010))
end)
end))
end
| uu____7012 -> begin
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

let uu____7035 = (FStar_Ident.text_of_id id1)
in (str uu____7035))
end
| FStar_Parser_AST.Paren (u1) -> begin
(

let uu____7037 = (p_universeFrom u1)
in (soft_parens_with_nesting uu____7037))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____7038}, (uu____7039)::(uu____7040)::[]) -> begin
(

let uu____7043 = (p_universeFrom u)
in (soft_parens_with_nesting uu____7043))
end
| FStar_Parser_AST.App (uu____7044) -> begin
(

let uu____7051 = (p_universeFrom u)
in (soft_parens_with_nesting uu____7051))
end
| uu____7052 -> begin
(

let uu____7053 = (

let uu____7054 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" uu____7054))
in (failwith uu____7053))
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
| FStar_Parser_AST.Module (uu____7126, decls) -> begin
(

let uu____7132 = (FStar_All.pipe_right decls (FStar_List.map decl_to_document))
in (FStar_All.pipe_right uu____7132 (FStar_Pprint.separate FStar_Pprint.hardline)))
end
| FStar_Parser_AST.Interface (uu____7141, decls, uu____7143) -> begin
(

let uu____7148 = (FStar_All.pipe_right decls (FStar_List.map decl_to_document))
in (FStar_All.pipe_right uu____7148 (FStar_Pprint.separate FStar_Pprint.hardline)))
end)
in ((FStar_ST.op_Colon_Equals should_print_fs_typ_app false);
res;
));
))


let comments_to_document : (Prims.string * FStar_Range.range) Prims.list  ->  FStar_Pprint.document = (fun comments -> (FStar_Pprint.separate_map FStar_Pprint.hardline (fun uu____7201 -> (match (uu____7201) with
| (comment, range) -> begin
(str comment)
end)) comments))


let modul_with_comments_to_document : FStar_Parser_AST.modul  ->  (Prims.string * FStar_Range.range) Prims.list  ->  (FStar_Pprint.document * (Prims.string * FStar_Range.range) Prims.list) = (fun m comments -> (

let decls = (match (m) with
| FStar_Parser_AST.Module (uu____7245, decls) -> begin
decls
end
| FStar_Parser_AST.Interface (uu____7251, decls, uu____7253) -> begin
decls
end)
in ((FStar_ST.op_Colon_Equals should_print_fs_typ_app false);
(match (decls) with
| [] -> begin
((FStar_Pprint.empty), (comments))
end
| (d)::ds -> begin
(

let uu____7298 = (match (ds) with
| ({FStar_Parser_AST.d = FStar_Parser_AST.Pragma (FStar_Parser_AST.LightOff); FStar_Parser_AST.drange = uu____7311; FStar_Parser_AST.doc = uu____7312; FStar_Parser_AST.quals = uu____7313; FStar_Parser_AST.attrs = uu____7314})::uu____7315 -> begin
(

let d0 = (FStar_List.hd ds)
in (

let uu____7321 = (

let uu____7324 = (

let uu____7327 = (FStar_List.tl ds)
in (d)::uu____7327)
in (d0)::uu____7324)
in ((uu____7321), (d0.FStar_Parser_AST.drange))))
end
| uu____7332 -> begin
(((d)::ds), (d.FStar_Parser_AST.drange))
end)
in (match (uu____7298) with
| (decls1, first_range) -> begin
(

let extract_decl_range = (fun d1 -> d1.FStar_Parser_AST.drange)
in ((FStar_ST.op_Colon_Equals comment_stack comments);
(

let initial_comment = (

let uu____7392 = (FStar_Range.start_of_range first_range)
in (place_comments_until_pos (Prims.parse_int "0") (Prims.parse_int "1") uu____7392 FStar_Pprint.empty))
in (

let doc1 = (separate_map_with_comments FStar_Pprint.empty FStar_Pprint.empty decl_to_document decls1 extract_decl_range)
in (

let comments1 = (FStar_ST.op_Bang comment_stack)
in ((FStar_ST.op_Colon_Equals comment_stack []);
(FStar_ST.op_Colon_Equals should_print_fs_typ_app false);
(

let uu____7488 = (FStar_Pprint.op_Hat_Hat initial_comment doc1)
in ((uu____7488), (comments1)));
))));
))
end))
end);
)))




