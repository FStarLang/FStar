
open Prims
open FStar_Pervasives

let should_print_fs_typ_app : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let with_fs_typ_app : 'Auu____48 'Auu____49 . Prims.bool  ->  ('Auu____48  ->  'Auu____49)  ->  'Auu____48  ->  'Auu____49 = (fun b printer t -> (

let b0 = (FStar_ST.op_Bang should_print_fs_typ_app)
in ((FStar_ST.op_Colon_Equals should_print_fs_typ_app b);
(

let res = (printer t)
in ((FStar_ST.op_Colon_Equals should_print_fs_typ_app b0);
res;
));
)))


let str : Prims.string  ->  FStar_Pprint.document = (fun s -> (FStar_Pprint.doc_of_string s))


let default_or_map : 'Auu____176 'Auu____177 . 'Auu____176  ->  ('Auu____177  ->  'Auu____176)  ->  'Auu____177 FStar_Pervasives_Native.option  ->  'Auu____176 = (fun n1 f x -> (match (x) with
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


let separate_break_map : 'Auu____260 . FStar_Pprint.document  ->  ('Auu____260  ->  FStar_Pprint.document)  ->  'Auu____260 Prims.list  ->  FStar_Pprint.document = (fun sep f l -> (

let uu____285 = (

let uu____286 = (

let uu____287 = (FStar_Pprint.op_Hat_Hat sep break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____287))
in (FStar_Pprint.separate_map uu____286 f l))
in (FStar_Pprint.group uu____285)))


let precede_break_separate_map : 'Auu____298 . FStar_Pprint.document  ->  FStar_Pprint.document  ->  ('Auu____298  ->  FStar_Pprint.document)  ->  'Auu____298 Prims.list  ->  FStar_Pprint.document = (fun prec sep f l -> (

let uu____328 = (

let uu____329 = (FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space)
in (

let uu____330 = (

let uu____331 = (FStar_List.hd l)
in (FStar_All.pipe_right uu____331 f))
in (FStar_Pprint.precede uu____329 uu____330)))
in (

let uu____332 = (

let uu____333 = (FStar_List.tl l)
in (FStar_Pprint.concat_map (fun x -> (

let uu____339 = (

let uu____340 = (

let uu____341 = (f x)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____341))
in (FStar_Pprint.op_Hat_Hat sep uu____340))
in (FStar_Pprint.op_Hat_Hat break1 uu____339))) uu____333))
in (FStar_Pprint.op_Hat_Hat uu____328 uu____332))))


let concat_break_map : 'Auu____348 . ('Auu____348  ->  FStar_Pprint.document)  ->  'Auu____348 Prims.list  ->  FStar_Pprint.document = (fun f l -> (

let uu____368 = (FStar_Pprint.concat_map (fun x -> (

let uu____372 = (f x)
in (FStar_Pprint.op_Hat_Hat uu____372 break1))) l)
in (FStar_Pprint.group uu____368)))


let parens_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lparen contents FStar_Pprint.rparen))


let soft_parens_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lparen contents FStar_Pprint.rparen))


let braces_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbrace contents FStar_Pprint.rbrace))


let soft_braces_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbrace contents FStar_Pprint.rbrace))


let brackets_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbracket contents FStar_Pprint.rbracket))


let soft_brackets_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbracket contents FStar_Pprint.rbracket))


let soft_begin_end_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (

let uu____408 = (str "begin")
in (

let uu____409 = (str "end")
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") uu____408 contents uu____409))))


let separate_map_last : 'Auu____418 . FStar_Pprint.document  ->  (Prims.bool  ->  'Auu____418  ->  FStar_Pprint.document)  ->  'Auu____418 Prims.list  ->  FStar_Pprint.document = (fun sep f es -> (

let l = (FStar_List.length es)
in (

let es1 = (FStar_List.mapi (fun i e -> (f (Prims.op_disEquality i (l - (Prims.parse_int "1"))) e)) es)
in (FStar_Pprint.separate sep es1))))


let separate_break_map_last : 'Auu____470 . FStar_Pprint.document  ->  (Prims.bool  ->  'Auu____470  ->  FStar_Pprint.document)  ->  'Auu____470 Prims.list  ->  FStar_Pprint.document = (fun sep f l -> (

let uu____500 = (

let uu____501 = (

let uu____502 = (FStar_Pprint.op_Hat_Hat sep break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____502))
in (separate_map_last uu____501 f l))
in (FStar_Pprint.group uu____500)))


let separate_map_or_flow : 'Auu____511 . FStar_Pprint.document  ->  ('Auu____511  ->  FStar_Pprint.document)  ->  'Auu____511 Prims.list  ->  FStar_Pprint.document = (fun sep f l -> (match (((FStar_List.length l) < (Prims.parse_int "10"))) with
| true -> begin
(FStar_Pprint.separate_map sep f l)
end
| uu____536 -> begin
(FStar_Pprint.flow_map sep f l)
end))


let flow_map_last : 'Auu____545 . FStar_Pprint.document  ->  (Prims.bool  ->  'Auu____545  ->  FStar_Pprint.document)  ->  'Auu____545 Prims.list  ->  FStar_Pprint.document = (fun sep f es -> (

let l = (FStar_List.length es)
in (

let es1 = (FStar_List.mapi (fun i e -> (f (Prims.op_disEquality i (l - (Prims.parse_int "1"))) e)) es)
in (FStar_Pprint.flow sep es1))))


let separate_map_or_flow_last : 'Auu____597 . FStar_Pprint.document  ->  (Prims.bool  ->  'Auu____597  ->  FStar_Pprint.document)  ->  'Auu____597 Prims.list  ->  FStar_Pprint.document = (fun sep f l -> (match (((FStar_List.length l) < (Prims.parse_int "10"))) with
| true -> begin
(separate_map_last sep f l)
end
| uu____627 -> begin
(flow_map_last sep f l)
end))


let soft_surround_separate_map : 'Auu____646 . Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  ('Auu____646  ->  FStar_Pprint.document)  ->  'Auu____646 Prims.list  ->  FStar_Pprint.document = (fun n1 b void_ opening sep closing f xs -> (match ((Prims.op_Equality xs [])) with
| true -> begin
void_
end
| uu____698 -> begin
(

let uu____699 = (FStar_Pprint.separate_map sep f xs)
in (FStar_Pprint.soft_surround n1 b opening uu____699 closing))
end))


let soft_surround_map_or_flow : 'Auu____718 . Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  ('Auu____718  ->  FStar_Pprint.document)  ->  'Auu____718 Prims.list  ->  FStar_Pprint.document = (fun n1 b void_ opening sep closing f xs -> (match ((Prims.op_Equality xs [])) with
| true -> begin
void_
end
| uu____770 -> begin
(

let uu____771 = (separate_map_or_flow sep f xs)
in (FStar_Pprint.soft_surround n1 b opening uu____771 closing))
end))


let doc_of_fsdoc : (Prims.string * (Prims.string * Prims.string) Prims.list)  ->  FStar_Pprint.document = (fun uu____786 -> (match (uu____786) with
| (comment, keywords) -> begin
(

let uu____811 = (

let uu____812 = (

let uu____815 = (str comment)
in (

let uu____816 = (

let uu____819 = (

let uu____822 = (FStar_Pprint.separate_map FStar_Pprint.comma (fun uu____831 -> (match (uu____831) with
| (k, v1) -> begin
(

let uu____838 = (

let uu____841 = (str k)
in (

let uu____842 = (

let uu____845 = (

let uu____848 = (str v1)
in (uu____848)::[])
in (FStar_Pprint.rarrow)::uu____845)
in (uu____841)::uu____842))
in (FStar_Pprint.concat uu____838))
end)) keywords)
in (uu____822)::[])
in (FStar_Pprint.space)::uu____819)
in (uu____815)::uu____816))
in (FStar_Pprint.concat uu____812))
in (FStar_Pprint.group uu____811))
end))


let is_unit : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Const (FStar_Const.Const_unit) -> begin
true
end
| uu____854 -> begin
false
end))


let matches_var : FStar_Parser_AST.term  ->  FStar_Ident.ident  ->  Prims.bool = (fun t x -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (y) -> begin
(

let uu____866 = (FStar_Ident.text_of_lid y)
in (Prims.op_Equality x.FStar_Ident.idText uu____866))
end
| uu____867 -> begin
false
end))


let is_tuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Parser_Const.is_tuple_data_lid'


let is_dtuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Parser_Const.is_dtuple_data_lid'


let is_list_structure : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun cons_lid1 nil_lid1 -> (

let rec aux = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (lid, []) -> begin
(FStar_Ident.lid_equals lid nil_lid1)
end
| FStar_Parser_AST.Construct (lid, (uu____909)::((e2, uu____911))::[]) -> begin
((FStar_Ident.lid_equals lid cons_lid1) && (aux e2))
end
| uu____934 -> begin
false
end))
in aux))


let is_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Parser_Const.cons_lid FStar_Parser_Const.nil_lid)


let is_lex_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Parser_Const.lexcons_lid FStar_Parser_Const.lextop_lid)


let rec extract_from_list : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (uu____952, []) -> begin
[]
end
| FStar_Parser_AST.Construct (uu____963, ((e1, FStar_Parser_AST.Nothing))::((e2, FStar_Parser_AST.Nothing))::[]) -> begin
(

let uu____984 = (extract_from_list e2)
in (e1)::uu____984)
end
| uu____987 -> begin
(

let uu____988 = (

let uu____989 = (FStar_Parser_AST.term_to_string e)
in (FStar_Util.format1 "Not a list %s" uu____989))
in (failwith uu____988))
end))


let is_array : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (lid); FStar_Parser_AST.range = uu____998; FStar_Parser_AST.level = uu____999}, l, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) && (is_list l))
end
| uu____1001 -> begin
false
end))


let rec is_ref_set : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (maybe_empty_lid) -> begin
(FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty)
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_singleton_lid); FStar_Parser_AST.range = uu____1009; FStar_Parser_AST.level = uu____1010}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_addr_of_lid); FStar_Parser_AST.range = uu____1012; FStar_Parser_AST.level = uu____1013}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____1015; FStar_Parser_AST.level = uu____1016}, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals maybe_singleton_lid FStar_Parser_Const.set_singleton) && (FStar_Ident.lid_equals maybe_addr_of_lid FStar_Parser_Const.heap_addr_of_lid))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_union_lid); FStar_Parser_AST.range = uu____1018; FStar_Parser_AST.level = uu____1019}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____1021; FStar_Parser_AST.level = uu____1022}, e2, FStar_Parser_AST.Nothing) -> begin
(((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union) && (is_ref_set e1)) && (is_ref_set e2))
end
| uu____1024 -> begin
false
end))


let rec extract_from_ref_set : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (uu____1034) -> begin
[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (uu____1035); FStar_Parser_AST.range = uu____1036; FStar_Parser_AST.level = uu____1037}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (uu____1038); FStar_Parser_AST.range = uu____1039; FStar_Parser_AST.level = uu____1040}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____1042; FStar_Parser_AST.level = uu____1043}, FStar_Parser_AST.Nothing) -> begin
(e1)::[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (uu____1044); FStar_Parser_AST.range = uu____1045; FStar_Parser_AST.level = uu____1046}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____1048; FStar_Parser_AST.level = uu____1049}, e2, FStar_Parser_AST.Nothing) -> begin
(

let uu____1051 = (extract_from_ref_set e1)
in (

let uu____1054 = (extract_from_ref_set e2)
in (FStar_List.append uu____1051 uu____1054)))
end
| uu____1057 -> begin
(

let uu____1058 = (

let uu____1059 = (FStar_Parser_AST.term_to_string e)
in (FStar_Util.format1 "Not a ref set %s" uu____1059))
in (failwith uu____1058))
end))


let is_general_application : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____1067 = ((is_array e) || (is_ref_set e))
in (not (uu____1067))))


let is_general_construction : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____1073 = ((is_list e) || (is_lex_list e))
in (not (uu____1073))))


let is_general_prefix_op : FStar_Ident.ident  ->  Prims.bool = (fun op -> (

let op_starting_char = (

let uu____1080 = (FStar_Ident.text_of_id op)
in (FStar_Util.char_at uu____1080 (Prims.parse_int "0")))
in (((Prims.op_Equality op_starting_char 33 (*!*)) || (Prims.op_Equality op_starting_char 63 (*?*))) || ((Prims.op_Equality op_starting_char 126 (*~*)) && (

let uu____1085 = (FStar_Ident.text_of_id op)
in (Prims.op_disEquality uu____1085 "~"))))))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun e -> (

let rec aux = (fun e1 acc -> (match (e1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App (head1, arg, imp) -> begin
(aux head1 ((((arg), (imp)))::acc))
end
| uu____1151 -> begin
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
| uu____1167 -> begin
false
end))


let uu___is_Right : associativity  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Right -> begin
true
end
| uu____1173 -> begin
false
end))


let uu___is_NonAssoc : associativity  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NonAssoc -> begin
true
end
| uu____1179 -> begin
false
end))


type token =
(FStar_Char.char, Prims.string) FStar_Util.either


type associativity_level =
(associativity * token Prims.list)


let token_to_string : (FStar_BaseTypes.char, Prims.string) FStar_Util.either  ->  Prims.string = (fun uu___57_1199 -> (match (uu___57_1199) with
| FStar_Util.Inl (c) -> begin
(Prims.strcat (FStar_Util.string_of_char c) ".*")
end
| FStar_Util.Inr (s) -> begin
s
end))


let matches_token : Prims.string  ->  (FStar_Char.char, Prims.string) FStar_Util.either  ->  Prims.bool = (fun s uu___58_1220 -> (match (uu___58_1220) with
| FStar_Util.Inl (c) -> begin
(

let uu____1229 = (FStar_String.get s (Prims.parse_int "0"))
in (Prims.op_Equality uu____1229 c))
end
| FStar_Util.Inr (s') -> begin
(Prims.op_Equality s s')
end))


let matches_level : 'Auu____1240 . Prims.string  ->  ('Auu____1240 * (FStar_Char.char, Prims.string) FStar_Util.either Prims.list)  ->  Prims.bool = (fun s uu____1261 -> (match (uu____1261) with
| (assoc_levels, tokens) -> begin
(

let uu____1289 = (FStar_List.tryFind (matches_token s) tokens)
in (Prims.op_disEquality uu____1289 FStar_Pervasives_Native.None))
end))


let opinfix4 : 'Auu____1316 . unit  ->  (associativity * ('Auu____1316, Prims.string) FStar_Util.either Prims.list) = (fun uu____1327 -> ((Right), ((FStar_Util.Inr ("**"))::[])))


let opinfix3 : 'Auu____1344 . unit  ->  (associativity * (FStar_Char.char, 'Auu____1344) FStar_Util.either Prims.list) = (fun uu____1356 -> ((Left), ((FStar_Util.Inl (42 (***)))::(FStar_Util.Inl (47 (*/*)))::(FStar_Util.Inl (37 (*%*)))::[])))


let opinfix2 : 'Auu____1392 . unit  ->  (associativity * (FStar_Char.char, 'Auu____1392) FStar_Util.either Prims.list) = (fun uu____1404 -> ((Left), ((FStar_Util.Inl (43 (*+*)))::(FStar_Util.Inl (45 (*-*)))::[])))


let minus_lvl : 'Auu____1433 . unit  ->  (associativity * ('Auu____1433, Prims.string) FStar_Util.either Prims.list) = (fun uu____1444 -> ((Left), ((FStar_Util.Inr ("-"))::[])))


let opinfix1 : 'Auu____1461 . unit  ->  (associativity * (FStar_Char.char, 'Auu____1461) FStar_Util.either Prims.list) = (fun uu____1473 -> ((Right), ((FStar_Util.Inl (64 (*@*)))::(FStar_Util.Inl (94 (*^*)))::[])))


let pipe_right : 'Auu____1502 . unit  ->  (associativity * ('Auu____1502, Prims.string) FStar_Util.either Prims.list) = (fun uu____1513 -> ((Left), ((FStar_Util.Inr ("|>"))::[])))


let opinfix0d : 'Auu____1530 . unit  ->  (associativity * (FStar_Char.char, 'Auu____1530) FStar_Util.either Prims.list) = (fun uu____1542 -> ((Left), ((FStar_Util.Inl (36 (*$*)))::[])))


let opinfix0c : 'Auu____1564 . unit  ->  (associativity * (FStar_Char.char, 'Auu____1564) FStar_Util.either Prims.list) = (fun uu____1576 -> ((Left), ((FStar_Util.Inl (61 (*=*)))::(FStar_Util.Inl (60 (*<*)))::(FStar_Util.Inl (62 (*>*)))::[])))


let equal : 'Auu____1612 . unit  ->  (associativity * ('Auu____1612, Prims.string) FStar_Util.either Prims.list) = (fun uu____1623 -> ((Left), ((FStar_Util.Inr ("="))::[])))


let opinfix0b : 'Auu____1640 . unit  ->  (associativity * (FStar_Char.char, 'Auu____1640) FStar_Util.either Prims.list) = (fun uu____1652 -> ((Left), ((FStar_Util.Inl (38 (*&*)))::[])))


let opinfix0a : 'Auu____1674 . unit  ->  (associativity * (FStar_Char.char, 'Auu____1674) FStar_Util.either Prims.list) = (fun uu____1686 -> ((Left), ((FStar_Util.Inl (124 (*|*)))::[])))


let colon_equals : 'Auu____1708 . unit  ->  (associativity * ('Auu____1708, Prims.string) FStar_Util.either Prims.list) = (fun uu____1719 -> ((NonAssoc), ((FStar_Util.Inr (":="))::[])))


let amp : 'Auu____1736 . unit  ->  (associativity * ('Auu____1736, Prims.string) FStar_Util.either Prims.list) = (fun uu____1747 -> ((Right), ((FStar_Util.Inr ("&"))::[])))


let colon_colon : 'Auu____1764 . unit  ->  (associativity * ('Auu____1764, Prims.string) FStar_Util.either Prims.list) = (fun uu____1775 -> ((Right), ((FStar_Util.Inr ("::"))::[])))


let level_associativity_spec : (associativity * (FStar_Char.char, Prims.string) FStar_Util.either Prims.list) Prims.list = ((opinfix4 ()))::((opinfix3 ()))::((opinfix2 ()))::((opinfix1 ()))::((pipe_right ()))::((opinfix0d ()))::((opinfix0c ()))::((opinfix0b ()))::((opinfix0a ()))::((colon_equals ()))::((amp ()))::((colon_colon ()))::[]


let level_table : ((Prims.int * Prims.int * Prims.int) * (FStar_Char.char, Prims.string) FStar_Util.either Prims.list) Prims.list = (

let levels_from_associativity = (fun l uu___59_1986 -> (match (uu___59_1986) with
| Left -> begin
((l), (l), ((l - (Prims.parse_int "1"))))
end
| Right -> begin
(((l - (Prims.parse_int "1"))), (l), (l))
end
| NonAssoc -> begin
(((l - (Prims.parse_int "1"))), (l), ((l - (Prims.parse_int "1"))))
end))
in (FStar_List.mapi (fun i uu____2026 -> (match (uu____2026) with
| (assoc1, tokens) -> begin
(((levels_from_associativity i assoc1)), (tokens))
end)) level_associativity_spec))


let assign_levels : associativity_level Prims.list  ->  Prims.string  ->  (Prims.int * Prims.int * Prims.int) = (fun token_associativity_spec s -> (

let uu____2110 = (FStar_List.tryFind (matches_level s) level_table)
in (match (uu____2110) with
| FStar_Pervasives_Native.Some (assoc_levels, uu____2160) -> begin
assoc_levels
end
| uu____2204 -> begin
(failwith (Prims.strcat "Unrecognized operator " s))
end)))


let max : Prims.int  ->  Prims.int  ->  Prims.int = (fun k1 k2 -> (match ((k1 > k2)) with
| true -> begin
k1
end
| uu____2240 -> begin
k2
end))


let max_level : 'Auu____2245 . ('Auu____2245 * (FStar_Char.char, Prims.string) FStar_Util.either Prims.list) Prims.list  ->  Prims.int = (fun l -> (

let find_level_and_max = (fun n1 level -> (

let uu____2310 = (FStar_List.tryFind (fun uu____2350 -> (match (uu____2350) with
| (uu____2368, tokens) -> begin
(Prims.op_Equality tokens (FStar_Pervasives_Native.snd level))
end)) level_table)
in (match (uu____2310) with
| FStar_Pervasives_Native.Some ((uu____2410, l1, uu____2412), uu____2413) -> begin
(max n1 l1)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____2468 = (

let uu____2469 = (

let uu____2470 = (FStar_List.map token_to_string (FStar_Pervasives_Native.snd level))
in (FStar_String.concat "," uu____2470))
in (FStar_Util.format1 "Undefined associativity level %s" uu____2469))
in (failwith uu____2468))
end)))
in (FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l)))


let levels : Prims.string  ->  (Prims.int * Prims.int * Prims.int) = (fun op -> (

let uu____2506 = (assign_levels level_associativity_spec op)
in (match (uu____2506) with
| (left1, mine, right1) -> begin
(match ((Prims.op_Equality op "*")) with
| true -> begin
(((left1 - (Prims.parse_int "1"))), (mine), (right1))
end
| uu____2528 -> begin
((left1), (mine), (right1))
end)
end)))


let operatorInfix0ad12 : 'Auu____2531 . unit  ->  (associativity * (FStar_Char.char, 'Auu____2531) FStar_Util.either Prims.list) Prims.list = (fun uu____2545 -> ((opinfix0a ()))::((opinfix0b ()))::((opinfix0c ()))::((opinfix0d ()))::((opinfix1 ()))::((opinfix2 ()))::[])


let is_operatorInfix0ad12 : FStar_Ident.ident  ->  Prims.bool = (fun op -> (

let uu____2628 = (

let uu____2642 = (

let uu____2658 = (FStar_Ident.text_of_id op)
in (FStar_All.pipe_left matches_level uu____2658))
in (FStar_List.tryFind uu____2642 (operatorInfix0ad12 ())))
in (Prims.op_disEquality uu____2628 FStar_Pervasives_Native.None)))


let is_operatorInfix34 : FStar_Ident.ident  ->  Prims.bool = (

let opinfix34 = ((opinfix3 ()))::((opinfix4 ()))::[]
in (fun op -> (

let uu____2761 = (

let uu____2775 = (

let uu____2791 = (FStar_Ident.text_of_id op)
in (FStar_All.pipe_left matches_level uu____2791))
in (FStar_List.tryFind uu____2775 opinfix34))
in (Prims.op_disEquality uu____2761 FStar_Pervasives_Native.None))))


let handleable_args_length : FStar_Ident.ident  ->  Prims.int = (fun op -> (

let op_s = (FStar_Ident.text_of_id op)
in (

let uu____2847 = ((is_general_prefix_op op) || (FStar_List.mem op_s (("-")::("~")::[])))
in (match (uu____2847) with
| true -> begin
(Prims.parse_int "1")
end
| uu____2848 -> begin
(

let uu____2849 = (((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) || (FStar_List.mem op_s (("<==>")::("==>")::("\\/")::("/\\")::("=")::("|>")::(":=")::(".()")::(".[]")::[])))
in (match (uu____2849) with
| true -> begin
(Prims.parse_int "2")
end
| uu____2850 -> begin
(match ((FStar_List.mem op_s ((".()<-")::(".[]<-")::[]))) with
| true -> begin
(Prims.parse_int "3")
end
| uu____2851 -> begin
(Prims.parse_int "0")
end)
end))
end))))


let handleable_op : 'Auu____2858 . FStar_Ident.ident  ->  'Auu____2858 Prims.list  ->  Prims.bool = (fun op args -> (match ((FStar_List.length args)) with
| _0_4 when (_0_4 = (Prims.parse_int "0")) -> begin
true
end
| _0_5 when (_0_5 = (Prims.parse_int "1")) -> begin
((is_general_prefix_op op) || (

let uu____2874 = (FStar_Ident.text_of_id op)
in (FStar_List.mem uu____2874 (("-")::("~")::[]))))
end
| _0_6 when (_0_6 = (Prims.parse_int "2")) -> begin
(((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) || (

let uu____2876 = (FStar_Ident.text_of_id op)
in (FStar_List.mem uu____2876 (("<==>")::("==>")::("\\/")::("/\\")::("=")::("|>")::(":=")::(".()")::(".[]")::[]))))
end
| _0_7 when (_0_7 = (Prims.parse_int "3")) -> begin
(

let uu____2877 = (FStar_Ident.text_of_id op)
in (FStar_List.mem uu____2877 ((".()<-")::(".[]<-")::[])))
end
| uu____2878 -> begin
false
end))


let comment_stack : (Prims.string * FStar_Range.range) Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let with_comment : 'Auu____2940 . ('Auu____2940  ->  FStar_Pprint.document)  ->  'Auu____2940  ->  FStar_Range.range  ->  FStar_Pprint.document = (fun printer tm tmrange -> (

let rec comments_before_pos = (fun acc print_pos lookahead_pos -> (

let uu____2981 = (FStar_ST.op_Bang comment_stack)
in (match (uu____2981) with
| [] -> begin
((acc), (false))
end
| ((comment, crange))::cs -> begin
(

let uu____3050 = (FStar_Range.range_before_pos crange print_pos)
in (match (uu____3050) with
| true -> begin
((FStar_ST.op_Colon_Equals comment_stack cs);
(

let uu____3097 = (

let uu____3098 = (

let uu____3099 = (str comment)
in (FStar_Pprint.op_Hat_Hat uu____3099 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat acc uu____3098))
in (comments_before_pos uu____3097 print_pos lookahead_pos));
)
end
| uu____3100 -> begin
(

let uu____3101 = (FStar_Range.range_before_pos crange lookahead_pos)
in ((acc), (uu____3101)))
end))
end)))
in (

let uu____3102 = (

let uu____3107 = (

let uu____3108 = (FStar_Range.start_of_range tmrange)
in (FStar_Range.end_of_line uu____3108))
in (

let uu____3109 = (FStar_Range.end_of_range tmrange)
in (comments_before_pos FStar_Pprint.empty uu____3107 uu____3109)))
in (match (uu____3102) with
| (comments, has_lookahead) -> begin
(

let printed_e = (printer tm)
in (

let comments1 = (match (has_lookahead) with
| true -> begin
(

let pos = (FStar_Range.end_of_range tmrange)
in (

let uu____3115 = (comments_before_pos comments pos pos)
in (FStar_Pervasives_Native.fst uu____3115)))
end
| uu____3120 -> begin
comments
end)
in (

let uu____3121 = (FStar_Pprint.op_Hat_Hat comments1 printed_e)
in (FStar_Pprint.group uu____3121))))
end))))


let rec place_comments_until_pos : Prims.int  ->  Prims.int  ->  FStar_Range.pos  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun k lbegin pos_end doc1 -> (

let uu____3142 = (FStar_ST.op_Bang comment_stack)
in (match (uu____3142) with
| ((comment, crange))::cs when (FStar_Range.range_before_pos crange pos_end) -> begin
((FStar_ST.op_Colon_Equals comment_stack cs);
(

let lnum = (

let uu____3246 = (

let uu____3247 = (

let uu____3248 = (FStar_Range.start_of_range crange)
in (FStar_Range.line_of_pos uu____3248))
in (uu____3247 - lbegin))
in (max k uu____3246))
in (

let doc2 = (

let uu____3250 = (

let uu____3251 = (FStar_Pprint.repeat lnum FStar_Pprint.hardline)
in (

let uu____3252 = (str comment)
in (FStar_Pprint.op_Hat_Hat uu____3251 uu____3252)))
in (FStar_Pprint.op_Hat_Hat doc1 uu____3250))
in (

let uu____3253 = (

let uu____3254 = (FStar_Range.end_of_range crange)
in (FStar_Range.line_of_pos uu____3254))
in (place_comments_until_pos (Prims.parse_int "1") uu____3253 pos_end doc2))));
)
end
| uu____3255 -> begin
(

let lnum = (

let uu____3263 = (

let uu____3264 = (FStar_Range.line_of_pos pos_end)
in (uu____3264 - lbegin))
in (max (Prims.parse_int "1") uu____3263))
in (

let uu____3265 = (FStar_Pprint.repeat lnum FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat doc1 uu____3265)))
end)))


let separate_map_with_comments : 'Auu____3278 . FStar_Pprint.document  ->  FStar_Pprint.document  ->  ('Auu____3278  ->  FStar_Pprint.document)  ->  'Auu____3278 Prims.list  ->  ('Auu____3278  ->  FStar_Range.range)  ->  FStar_Pprint.document = (fun prefix1 sep f xs extract_range -> (

let fold_fun = (fun uu____3335 x -> (match (uu____3335) with
| (last_line, doc1) -> begin
(

let r = (extract_range x)
in (

let doc2 = (

let uu____3349 = (FStar_Range.start_of_range r)
in (place_comments_until_pos (Prims.parse_int "1") last_line uu____3349 doc1))
in (

let uu____3350 = (

let uu____3351 = (FStar_Range.end_of_range r)
in (FStar_Range.line_of_pos uu____3351))
in (

let uu____3352 = (

let uu____3353 = (

let uu____3354 = (f x)
in (FStar_Pprint.op_Hat_Hat sep uu____3354))
in (FStar_Pprint.op_Hat_Hat doc2 uu____3353))
in ((uu____3350), (uu____3352))))))
end))
in (

let uu____3355 = (

let uu____3362 = (FStar_List.hd xs)
in (

let uu____3363 = (FStar_List.tl xs)
in ((uu____3362), (uu____3363))))
in (match (uu____3355) with
| (x, xs1) -> begin
(

let init1 = (

let uu____3379 = (

let uu____3380 = (

let uu____3381 = (extract_range x)
in (FStar_Range.end_of_range uu____3381))
in (FStar_Range.line_of_pos uu____3380))
in (

let uu____3382 = (

let uu____3383 = (f x)
in (FStar_Pprint.op_Hat_Hat prefix1 uu____3383))
in ((uu____3379), (uu____3382))))
in (

let uu____3384 = (FStar_List.fold_left fold_fun init1 xs1)
in (FStar_Pervasives_Native.snd uu____3384)))
end))))


let rec p_decl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (

let uu____4013 = (

let uu____4014 = (FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc)
in (

let uu____4015 = (

let uu____4016 = (p_attributes d.FStar_Parser_AST.attrs)
in (

let uu____4017 = (

let uu____4018 = (p_qualifiers d.FStar_Parser_AST.quals)
in (

let uu____4019 = (

let uu____4020 = (p_rawDecl d)
in (FStar_Pprint.op_Hat_Hat (match ((Prims.op_Equality d.FStar_Parser_AST.quals [])) with
| true -> begin
FStar_Pprint.empty
end
| uu____4021 -> begin
break1
end) uu____4020))
in (FStar_Pprint.op_Hat_Hat uu____4018 uu____4019)))
in (FStar_Pprint.op_Hat_Hat uu____4016 uu____4017)))
in (FStar_Pprint.op_Hat_Hat uu____4014 uu____4015)))
in (FStar_Pprint.group uu____4013)))
and p_attributes : FStar_Parser_AST.attributes_  ->  FStar_Pprint.document = (fun attrs -> (

let uu____4023 = (

let uu____4024 = (str "@")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____4024))
in (

let uu____4025 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline)
in (soft_surround_map_or_flow (Prims.parse_int "0") (Prims.parse_int "2") FStar_Pprint.empty uu____4023 FStar_Pprint.space uu____4025 p_atomicTerm attrs))))
and p_fsdoc : FStar_Parser_AST.fsdoc  ->  FStar_Pprint.document = (fun uu____4026 -> (match (uu____4026) with
| (doc1, kwd_args) -> begin
(

let kwd_args_doc = (match (kwd_args) with
| [] -> begin
FStar_Pprint.empty
end
| kwd_args1 -> begin
(

let process_kwd_arg = (fun uu____4062 -> (match (uu____4062) with
| (kwd, arg) -> begin
(

let uu____4069 = (str "@")
in (

let uu____4070 = (

let uu____4071 = (str kwd)
in (

let uu____4072 = (

let uu____4073 = (str arg)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4073))
in (FStar_Pprint.op_Hat_Hat uu____4071 uu____4072)))
in (FStar_Pprint.op_Hat_Hat uu____4069 uu____4070)))
end))
in (

let uu____4074 = (

let uu____4075 = (FStar_Pprint.separate_map FStar_Pprint.hardline process_kwd_arg kwd_args1)
in (FStar_Pprint.op_Hat_Hat uu____4075 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4074)))
end)
in (

let uu____4080 = (

let uu____4081 = (

let uu____4082 = (

let uu____4083 = (

let uu____4084 = (str doc1)
in (

let uu____4085 = (

let uu____4086 = (

let uu____4087 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____4087))
in (FStar_Pprint.op_Hat_Hat kwd_args_doc uu____4086))
in (FStar_Pprint.op_Hat_Hat uu____4084 uu____4085)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____4083))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____4082))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4081))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4080)))
end))
and p_justSig : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (lid, t) -> begin
(

let uu____4091 = (

let uu____4092 = (str "val")
in (

let uu____4093 = (

let uu____4094 = (

let uu____4095 = (p_lident lid)
in (

let uu____4096 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat uu____4095 uu____4096)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4094))
in (FStar_Pprint.op_Hat_Hat uu____4092 uu____4093)))
in (

let uu____4097 = (p_typ false false t)
in (op_Hat_Slash_Plus_Hat uu____4091 uu____4097)))
end
| FStar_Parser_AST.TopLevelLet (uu____4098, lbs) -> begin
(FStar_Pprint.separate_map FStar_Pprint.hardline (fun lb -> (

let uu____4123 = (

let uu____4124 = (str "let")
in (

let uu____4125 = (p_letlhs lb)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4124 uu____4125)))
in (FStar_Pprint.group uu____4123))) lbs)
end
| uu____4126 -> begin
FStar_Pprint.empty
end))
and p_list : (FStar_Ident.ident  ->  FStar_Pprint.document)  ->  FStar_Pprint.document  ->  FStar_Ident.ident Prims.list  ->  FStar_Pprint.document = (fun f sep l -> (

let rec p_list' = (fun uu___60_4141 -> (match (uu___60_4141) with
| [] -> begin
FStar_Pprint.empty
end
| (x)::[] -> begin
(f x)
end
| (x)::xs -> begin
(

let uu____4149 = (f x)
in (

let uu____4150 = (

let uu____4151 = (p_list' xs)
in (FStar_Pprint.op_Hat_Hat sep uu____4151))
in (FStar_Pprint.op_Hat_Hat uu____4149 uu____4150)))
end))
in (

let uu____4152 = (str "[")
in (

let uu____4153 = (

let uu____4154 = (p_list' l)
in (

let uu____4155 = (str "]")
in (FStar_Pprint.op_Hat_Hat uu____4154 uu____4155)))
in (FStar_Pprint.op_Hat_Hat uu____4152 uu____4153)))))
and p_rawDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Open (uid) -> begin
(

let uu____4158 = (

let uu____4159 = (str "open")
in (

let uu____4160 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4159 uu____4160)))
in (FStar_Pprint.group uu____4158))
end
| FStar_Parser_AST.Include (uid) -> begin
(

let uu____4162 = (

let uu____4163 = (str "include")
in (

let uu____4164 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4163 uu____4164)))
in (FStar_Pprint.group uu____4162))
end
| FStar_Parser_AST.ModuleAbbrev (uid1, uid2) -> begin
(

let uu____4167 = (

let uu____4168 = (str "module")
in (

let uu____4169 = (

let uu____4170 = (

let uu____4171 = (p_uident uid1)
in (

let uu____4172 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____4171 uu____4172)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4170))
in (FStar_Pprint.op_Hat_Hat uu____4168 uu____4169)))
in (

let uu____4173 = (p_quident uid2)
in (op_Hat_Slash_Plus_Hat uu____4167 uu____4173)))
end
| FStar_Parser_AST.TopLevelModule (uid) -> begin
(

let uu____4175 = (

let uu____4176 = (str "module")
in (

let uu____4177 = (

let uu____4178 = (p_quident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4178))
in (FStar_Pprint.op_Hat_Hat uu____4176 uu____4177)))
in (FStar_Pprint.group uu____4175))
end
| FStar_Parser_AST.Tycon (true, ((FStar_Parser_AST.TyconAbbrev (uid, tpars, FStar_Pervasives_Native.None, t), FStar_Pervasives_Native.None))::[]) -> begin
(

let effect_prefix_doc = (

let uu____4211 = (str "effect")
in (

let uu____4212 = (

let uu____4213 = (p_uident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4213))
in (FStar_Pprint.op_Hat_Hat uu____4211 uu____4212)))
in (

let uu____4214 = (

let uu____4215 = (p_typars tpars)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") effect_prefix_doc uu____4215 FStar_Pprint.equals))
in (

let uu____4216 = (p_typ false false t)
in (op_Hat_Slash_Plus_Hat uu____4214 uu____4216))))
end
| FStar_Parser_AST.Tycon (false, tcdefs) -> begin
(

let uu____4234 = (str "type")
in (

let uu____4235 = (str "and")
in (precede_break_separate_map uu____4234 uu____4235 p_fsdocTypeDeclPairs tcdefs)))
end
| FStar_Parser_AST.TopLevelLet (q, lbs) -> begin
(

let let_doc = (

let uu____4257 = (str "let")
in (

let uu____4258 = (

let uu____4259 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat uu____4259 FStar_Pprint.space))
in (FStar_Pprint.op_Hat_Hat uu____4257 uu____4258)))
in (

let uu____4260 = (

let uu____4261 = (str "and")
in (FStar_Pprint.op_Hat_Hat uu____4261 FStar_Pprint.space))
in (separate_map_with_comments let_doc uu____4260 p_letbinding lbs (fun uu____4269 -> (match (uu____4269) with
| (p, t) -> begin
(FStar_Range.union_ranges p.FStar_Parser_AST.prange t.FStar_Parser_AST.range)
end)))))
end
| FStar_Parser_AST.Val (lid, t) -> begin
(

let uu____4278 = (

let uu____4279 = (str "val")
in (

let uu____4280 = (

let uu____4281 = (

let uu____4282 = (p_lident lid)
in (

let uu____4283 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat uu____4282 uu____4283)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4281))
in (FStar_Pprint.op_Hat_Hat uu____4279 uu____4280)))
in (

let uu____4284 = (p_typ false false t)
in (op_Hat_Slash_Plus_Hat uu____4278 uu____4284)))
end
| FStar_Parser_AST.Assume (id1, t) -> begin
(

let decl_keyword = (

let uu____4288 = (

let uu____4289 = (FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_All.pipe_right uu____4289 FStar_Util.is_upper))
in (match (uu____4288) with
| true -> begin
FStar_Pprint.empty
end
| uu____4290 -> begin
(

let uu____4291 = (str "val")
in (FStar_Pprint.op_Hat_Hat uu____4291 FStar_Pprint.space))
end))
in (

let uu____4292 = (

let uu____4293 = (

let uu____4294 = (p_ident id1)
in (

let uu____4295 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat uu____4294 uu____4295)))
in (FStar_Pprint.op_Hat_Hat decl_keyword uu____4293))
in (

let uu____4296 = (p_typ false false t)
in (op_Hat_Slash_Plus_Hat uu____4292 uu____4296))))
end
| FStar_Parser_AST.Exception (uid, t_opt) -> begin
(

let uu____4303 = (str "exception")
in (

let uu____4304 = (

let uu____4305 = (

let uu____4306 = (p_uident uid)
in (

let uu____4307 = (FStar_Pprint.optional (fun t -> (

let uu____4311 = (

let uu____4312 = (str "of")
in (

let uu____4313 = (p_typ false false t)
in (op_Hat_Slash_Plus_Hat uu____4312 uu____4313)))
in (FStar_Pprint.op_Hat_Hat break1 uu____4311))) t_opt)
in (FStar_Pprint.op_Hat_Hat uu____4306 uu____4307)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4305))
in (FStar_Pprint.op_Hat_Hat uu____4303 uu____4304)))
end
| FStar_Parser_AST.NewEffect (ne) -> begin
(

let uu____4315 = (str "new_effect")
in (

let uu____4316 = (

let uu____4317 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4317))
in (FStar_Pprint.op_Hat_Hat uu____4315 uu____4316)))
end
| FStar_Parser_AST.SubEffect (se) -> begin
(

let uu____4319 = (str "sub_effect")
in (

let uu____4320 = (

let uu____4321 = (p_subEffect se)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4321))
in (FStar_Pprint.op_Hat_Hat uu____4319 uu____4320)))
end
| FStar_Parser_AST.Pragma (p) -> begin
(p_pragma p)
end
| FStar_Parser_AST.Fsdoc (doc1) -> begin
(

let uu____4324 = (p_fsdoc doc1)
in (FStar_Pprint.op_Hat_Hat uu____4324 FStar_Pprint.hardline))
end
| FStar_Parser_AST.Main (uu____4325) -> begin
(failwith "*Main declaration* : Is that really still in use ??")
end
| FStar_Parser_AST.Tycon (true, uu____4326) -> begin
(failwith "Effect abbreviation is expected to be defined by an abbreviation")
end
| FStar_Parser_AST.Splice (ids, t) -> begin
(

let uu____4349 = (str "%splice")
in (

let uu____4350 = (

let uu____4351 = (

let uu____4352 = (str ";")
in (p_list p_uident uu____4352 ids))
in (

let uu____4353 = (

let uu____4354 = (p_term false false t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4354))
in (FStar_Pprint.op_Hat_Hat uu____4351 uu____4353)))
in (FStar_Pprint.op_Hat_Hat uu____4349 uu____4350)))
end))
and p_pragma : FStar_Parser_AST.pragma  ->  FStar_Pprint.document = (fun uu___61_4355 -> (match (uu___61_4355) with
| FStar_Parser_AST.SetOptions (s) -> begin
(

let uu____4357 = (str "#set-options")
in (

let uu____4358 = (

let uu____4359 = (

let uu____4360 = (str s)
in (FStar_Pprint.dquotes uu____4360))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4359))
in (FStar_Pprint.op_Hat_Hat uu____4357 uu____4358)))
end
| FStar_Parser_AST.ResetOptions (s_opt) -> begin
(

let uu____4364 = (str "#reset-options")
in (

let uu____4365 = (FStar_Pprint.optional (fun s -> (

let uu____4369 = (

let uu____4370 = (str s)
in (FStar_Pprint.dquotes uu____4370))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4369))) s_opt)
in (FStar_Pprint.op_Hat_Hat uu____4364 uu____4365)))
end
| FStar_Parser_AST.LightOff -> begin
((FStar_ST.op_Colon_Equals should_print_fs_typ_app true);
(str "#light \"off\"");
)
end))
and p_typars : FStar_Parser_AST.binder Prims.list  ->  FStar_Pprint.document = (fun bs -> (p_binders true bs))
and p_fsdocTypeDeclPairs : (FStar_Parser_AST.tycon * FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option)  ->  FStar_Pprint.document = (fun uu____4404 -> (match (uu____4404) with
| (typedecl, fsdoc_opt) -> begin
(

let uu____4417 = (FStar_Pprint.optional p_fsdoc fsdoc_opt)
in (

let uu____4418 = (p_typeDecl typedecl)
in (FStar_Pprint.op_Hat_Hat uu____4417 uu____4418)))
end))
and p_typeDecl : FStar_Parser_AST.tycon  ->  FStar_Pprint.document = (fun uu___62_4419 -> (match (uu___62_4419) with
| FStar_Parser_AST.TyconAbstract (lid, bs, typ_opt) -> begin
(

let empty' = (fun uu____4436 -> FStar_Pprint.empty)
in (p_typeDeclPrefix lid bs typ_opt empty'))
end
| FStar_Parser_AST.TyconAbbrev (lid, bs, typ_opt, t) -> begin
(

let f = (fun uu____4454 -> (

let uu____4455 = (p_typ false false t)
in (prefix2 FStar_Pprint.equals uu____4455)))
in (p_typeDeclPrefix lid bs typ_opt f))
end
| FStar_Parser_AST.TyconRecord (lid, bs, typ_opt, record_field_decls) -> begin
(

let p_recordFieldAndComments = (fun ps uu____4506 -> (match (uu____4506) with
| (lid1, t, doc_opt) -> begin
(

let uu____4522 = (FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range)
in (with_comment (p_recordFieldDecl ps) ((lid1), (t), (doc_opt)) uu____4522))
end))
in (

let p_fields = (fun uu____4538 -> (

let uu____4539 = (

let uu____4540 = (

let uu____4541 = (

let uu____4542 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (separate_map_last uu____4542 p_recordFieldAndComments record_field_decls))
in (braces_with_nesting uu____4541))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4540))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____4539)))
in (p_typeDeclPrefix lid bs typ_opt p_fields)))
end
| FStar_Parser_AST.TyconVariant (lid, bs, typ_opt, ct_decls) -> begin
(

let p_constructorBranchAndComments = (fun uu____4608 -> (match (uu____4608) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let range = (

let uu____4634 = (

let uu____4635 = (FStar_Util.map_opt t_opt (fun t -> t.FStar_Parser_AST.range))
in (FStar_Util.dflt uid.FStar_Ident.idRange uu____4635))
in (FStar_Range.extend_to_end_of_line uu____4634))
in (

let p_constructorBranch = (fun decl -> (

let uu____4670 = (

let uu____4671 = (

let uu____4672 = (p_constructorDecl decl)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4672))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4671))
in (FStar_Pprint.group uu____4670)))
in (with_comment p_constructorBranch ((uid), (t_opt), (doc_opt), (use_of)) range)))
end))
in (

let datacon_doc = (fun uu____4694 -> (

let uu____4695 = (FStar_Pprint.separate_map break1 p_constructorBranchAndComments ct_decls)
in (FStar_Pprint.group uu____4695)))
in (p_typeDeclPrefix lid bs typ_opt (fun uu____4710 -> (

let uu____4711 = (datacon_doc ())
in (prefix2 FStar_Pprint.equals uu____4711))))))
end))
and p_typeDeclPrefix : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.knd FStar_Pervasives_Native.option  ->  (unit  ->  FStar_Pprint.document)  ->  FStar_Pprint.document = (fun lid bs typ_opt cont -> (match (((Prims.op_Equality bs []) && (Prims.op_Equality typ_opt FStar_Pervasives_Native.None))) with
| true -> begin
(

let uu____4726 = (p_ident lid)
in (

let uu____4727 = (

let uu____4728 = (cont ())
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4728))
in (FStar_Pprint.op_Hat_Hat uu____4726 uu____4727)))
end
| uu____4729 -> begin
(

let binders_doc = (

let uu____4731 = (p_typars bs)
in (

let uu____4732 = (FStar_Pprint.optional (fun t -> (

let uu____4736 = (

let uu____4737 = (

let uu____4738 = (p_typ false false t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4738))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4737))
in (FStar_Pprint.op_Hat_Hat break1 uu____4736))) typ_opt)
in (FStar_Pprint.op_Hat_Hat uu____4731 uu____4732)))
in (

let uu____4739 = (p_ident lid)
in (

let uu____4740 = (cont ())
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____4739 binders_doc uu____4740))))
end))
and p_recordFieldDecl : Prims.bool  ->  (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option)  ->  FStar_Pprint.document = (fun ps uu____4742 -> (match (uu____4742) with
| (lid, t, doc_opt) -> begin
(

let uu____4758 = (

let uu____4759 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (

let uu____4760 = (

let uu____4761 = (p_lident lid)
in (

let uu____4762 = (

let uu____4763 = (p_typ ps false t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4763))
in (FStar_Pprint.op_Hat_Hat uu____4761 uu____4762)))
in (FStar_Pprint.op_Hat_Hat uu____4759 uu____4760)))
in (FStar_Pprint.group uu____4758))
end))
and p_constructorDecl : (FStar_Ident.ident * FStar_Parser_AST.term FStar_Pervasives_Native.option * FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option * Prims.bool)  ->  FStar_Pprint.document = (fun uu____4764 -> (match (uu____4764) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let sep = (match (use_of) with
| true -> begin
(str "of")
end
| uu____4790 -> begin
FStar_Pprint.colon
end)
in (

let uid_doc = (p_uident uid)
in (

let uu____4792 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (

let uu____4793 = (

let uu____4794 = (FStar_Pprint.break_ (Prims.parse_int "0"))
in (

let uu____4795 = (default_or_map uid_doc (fun t -> (

let uu____4800 = (

let uu____4801 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep)
in (FStar_Pprint.op_Hat_Hat uid_doc uu____4801))
in (

let uu____4802 = (p_typ false false t)
in (op_Hat_Slash_Plus_Hat uu____4800 uu____4802)))) t_opt)
in (FStar_Pprint.op_Hat_Hat uu____4794 uu____4795)))
in (FStar_Pprint.op_Hat_Hat uu____4792 uu____4793)))))
end))
and p_letlhs : (FStar_Parser_AST.pattern * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun uu____4803 -> (match (uu____4803) with
| (pat, uu____4809) -> begin
(

let uu____4810 = (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat1, (t, FStar_Pervasives_Native.None)) -> begin
(

let uu____4829 = (

let uu____4830 = (

let uu____4831 = (

let uu____4832 = (

let uu____4833 = (p_tmArrow p_tmNoEq t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4833))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4832))
in (FStar_Pprint.group uu____4831))
in (FStar_Pprint.op_Hat_Hat break1 uu____4830))
in ((pat1), (uu____4829)))
end
| FStar_Parser_AST.PatAscribed (pat1, (t, FStar_Pervasives_Native.Some (tac))) -> begin
(

let uu____4845 = (

let uu____4846 = (

let uu____4847 = (

let uu____4848 = (

let uu____4849 = (

let uu____4850 = (p_tmArrow p_tmNoEq t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4850))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4849))
in (FStar_Pprint.group uu____4848))
in (

let uu____4851 = (

let uu____4852 = (

let uu____4853 = (str "by")
in (

let uu____4854 = (

let uu____4855 = (p_atomicTerm tac)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4855))
in (FStar_Pprint.op_Hat_Hat uu____4853 uu____4854)))
in (FStar_Pprint.group uu____4852))
in (FStar_Pprint.op_Hat_Hat uu____4847 uu____4851)))
in (FStar_Pprint.op_Hat_Hat break1 uu____4846))
in ((pat1), (uu____4845)))
end
| uu____4856 -> begin
((pat), (FStar_Pprint.empty))
end)
in (match (uu____4810) with
| (pat1, ascr_doc) -> begin
(match (pat1.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____4860); FStar_Parser_AST.prange = uu____4861}, pats) -> begin
(

let uu____4871 = (

let uu____4872 = (p_lident x)
in (

let uu____4873 = (

let uu____4874 = (separate_map_or_flow break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Hat uu____4874 ascr_doc))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4872 uu____4873)))
in (FStar_Pprint.group uu____4871))
end
| uu____4875 -> begin
(

let uu____4876 = (

let uu____4877 = (p_tuplePattern pat1)
in (FStar_Pprint.op_Hat_Hat uu____4877 ascr_doc))
in (FStar_Pprint.group uu____4876))
end)
end))
end))
and p_letbinding : (FStar_Parser_AST.pattern * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun uu____4878 -> (match (uu____4878) with
| (pat, e) -> begin
(

let pat_doc = (p_letlhs ((pat), (e)))
in (

let uu____4886 = (

let uu____4887 = (FStar_Pprint.op_Hat_Slash_Hat pat_doc FStar_Pprint.equals)
in (FStar_Pprint.group uu____4887))
in (

let uu____4888 = (p_term false false e)
in (prefix2 uu____4886 uu____4888))))
end))
and p_newEffect : FStar_Parser_AST.effect_decl  ->  FStar_Pprint.document = (fun uu___63_4889 -> (match (uu___63_4889) with
| FStar_Parser_AST.RedefineEffect (lid, bs, t) -> begin
(p_effectRedefinition lid bs t)
end
| FStar_Parser_AST.DefineEffect (lid, bs, t, eff_decls) -> begin
(p_effectDefinition lid bs t eff_decls)
end))
and p_effectRedefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun uid bs t -> (

let uu____4914 = (p_uident uid)
in (

let uu____4915 = (p_binders true bs)
in (

let uu____4916 = (

let uu____4917 = (p_simpleTerm false false t)
in (prefix2 FStar_Pprint.equals uu____4917))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____4914 uu____4915 uu____4916)))))
and p_effectDefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun uid bs t eff_decls -> (

let uu____4926 = (

let uu____4927 = (

let uu____4928 = (

let uu____4929 = (p_uident uid)
in (

let uu____4930 = (p_binders true bs)
in (

let uu____4931 = (

let uu____4932 = (p_typ false false t)
in (prefix2 FStar_Pprint.colon uu____4932))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____4929 uu____4930 uu____4931))))
in (FStar_Pprint.group uu____4928))
in (

let uu____4933 = (

let uu____4934 = (str "with")
in (

let uu____4935 = (separate_break_map_last FStar_Pprint.semi p_effectDecl eff_decls)
in (prefix2 uu____4934 uu____4935)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4927 uu____4933)))
in (braces_with_nesting uu____4926)))
and p_effectDecl : Prims.bool  ->  FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun ps d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (false, ((FStar_Parser_AST.TyconAbbrev (lid, [], FStar_Pervasives_Native.None, e), FStar_Pervasives_Native.None))::[]) -> begin
(

let uu____4966 = (

let uu____4967 = (p_lident lid)
in (

let uu____4968 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____4967 uu____4968)))
in (

let uu____4969 = (p_simpleTerm ps false e)
in (prefix2 uu____4966 uu____4969)))
end
| uu____4970 -> begin
(

let uu____4971 = (

let uu____4972 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "Not a declaration of an effect member... or at least I hope so : %s" uu____4972))
in (failwith uu____4971))
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

let p_lift = (fun ps uu____5034 -> (match (uu____5034) with
| (kwd, t) -> begin
(

let uu____5041 = (

let uu____5042 = (str kwd)
in (

let uu____5043 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____5042 uu____5043)))
in (

let uu____5044 = (p_simpleTerm ps false t)
in (prefix2 uu____5041 uu____5044)))
end))
in (separate_break_map_last FStar_Pprint.semi p_lift lifts)))
in (

let uu____5049 = (

let uu____5050 = (

let uu____5051 = (p_quident lift.FStar_Parser_AST.msource)
in (

let uu____5052 = (

let uu____5053 = (str "~>")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5053))
in (FStar_Pprint.op_Hat_Hat uu____5051 uu____5052)))
in (

let uu____5054 = (p_quident lift.FStar_Parser_AST.mdest)
in (prefix2 uu____5050 uu____5054)))
in (

let uu____5055 = (

let uu____5056 = (braces_with_nesting lift_op_doc)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5056))
in (FStar_Pprint.op_Hat_Hat uu____5049 uu____5055)))))
and p_qualifier : FStar_Parser_AST.qualifier  ->  FStar_Pprint.document = (fun uu___64_5057 -> (match (uu___64_5057) with
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

let uu____5059 = (FStar_Pprint.separate_map break1 p_qualifier qs)
in (FStar_Pprint.group uu____5059)))
and p_letqualifier : FStar_Parser_AST.let_qualifier  ->  FStar_Pprint.document = (fun uu___65_5060 -> (match (uu___65_5060) with
| FStar_Parser_AST.Rec -> begin
(

let uu____5061 = (str "rec")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5061))
end
| FStar_Parser_AST.Mutable -> begin
(

let uu____5062 = (str "mutable")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5062))
end
| FStar_Parser_AST.NoLetQualifier -> begin
FStar_Pprint.empty
end))
and p_aqual : FStar_Parser_AST.arg_qualifier  ->  FStar_Pprint.document = (fun uu___66_5063 -> (match (uu___66_5063) with
| FStar_Parser_AST.Implicit -> begin
(str "#")
end
| FStar_Parser_AST.Equality -> begin
(str "$")
end))
and p_disjunctivePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr (pats) -> begin
(

let uu____5068 = (

let uu____5069 = (

let uu____5070 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space)
in (FStar_Pprint.op_Hat_Hat break1 uu____5070))
in (FStar_Pprint.separate_map uu____5069 p_tuplePattern pats))
in (FStar_Pprint.group uu____5068))
end
| uu____5071 -> begin
(p_tuplePattern p)
end))
and p_tuplePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTuple (pats, false) -> begin
(

let uu____5078 = (

let uu____5079 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map uu____5079 p_constructorPattern pats))
in (FStar_Pprint.group uu____5078))
end
| uu____5080 -> begin
(p_constructorPattern p)
end))
and p_constructorPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (maybe_cons_lid); FStar_Parser_AST.prange = uu____5083}, (hd1)::(tl1)::[]) when (FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid) -> begin
(

let uu____5088 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon)
in (

let uu____5089 = (p_constructorPattern hd1)
in (

let uu____5090 = (p_constructorPattern tl1)
in (infix0 uu____5088 uu____5089 uu____5090))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (uid); FStar_Parser_AST.prange = uu____5092}, pats) -> begin
(

let uu____5098 = (p_quident uid)
in (

let uu____5099 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (prefix2 uu____5098 uu____5099)))
end
| uu____5100 -> begin
(p_atomicPattern p)
end))
and p_atomicPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, (t, FStar_Pervasives_Native.None)) -> begin
(match (((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm))) with
| (FStar_Parser_AST.PatVar (lid, aqual), FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t1); FStar_Parser_AST.brange = uu____5116; FStar_Parser_AST.blevel = uu____5117; FStar_Parser_AST.aqual = uu____5118}, phi)) when (Prims.op_Equality lid.FStar_Ident.idText lid'.FStar_Ident.idText) -> begin
(

let uu____5124 = (

let uu____5125 = (p_ident lid)
in (p_refinement aqual uu____5125 t1 phi))
in (soft_parens_with_nesting uu____5124))
end
| (FStar_Parser_AST.PatWild, FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t1); FStar_Parser_AST.brange = uu____5127; FStar_Parser_AST.blevel = uu____5128; FStar_Parser_AST.aqual = uu____5129}, phi)) -> begin
(

let uu____5131 = (p_refinement FStar_Pervasives_Native.None FStar_Pprint.underscore t1 phi)
in (soft_parens_with_nesting uu____5131))
end
| uu____5132 -> begin
(

let uu____5137 = (

let uu____5138 = (p_tuplePattern pat)
in (

let uu____5139 = (

let uu____5140 = (FStar_Pprint.break_ (Prims.parse_int "0"))
in (

let uu____5141 = (

let uu____5142 = (p_tmEqNoRefinement t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5142))
in (FStar_Pprint.op_Hat_Hat uu____5140 uu____5141)))
in (FStar_Pprint.op_Hat_Hat uu____5138 uu____5139)))
in (soft_parens_with_nesting uu____5137))
end)
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let uu____5146 = (separate_break_map FStar_Pprint.semi p_tuplePattern pats)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket uu____5146 FStar_Pprint.rbracket))
end
| FStar_Parser_AST.PatRecord (pats) -> begin
(

let p_recordFieldPat = (fun uu____5163 -> (match (uu____5163) with
| (lid, pat) -> begin
(

let uu____5170 = (p_qlident lid)
in (

let uu____5171 = (p_tuplePattern pat)
in (infix2 FStar_Pprint.equals uu____5170 uu____5171)))
end))
in (

let uu____5172 = (separate_break_map FStar_Pprint.semi p_recordFieldPat pats)
in (soft_braces_with_nesting uu____5172)))
end
| FStar_Parser_AST.PatTuple (pats, true) -> begin
(

let uu____5182 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (

let uu____5183 = (separate_break_map FStar_Pprint.comma p_constructorPattern pats)
in (

let uu____5184 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____5182 uu____5183 uu____5184))))
end
| FStar_Parser_AST.PatTvar (tv, arg_qualifier_opt) -> begin
(p_tvar tv)
end
| FStar_Parser_AST.PatOp (op) -> begin
(

let uu____5193 = (

let uu____5194 = (

let uu____5195 = (

let uu____5196 = (FStar_Ident.text_of_id op)
in (str uu____5196))
in (

let uu____5197 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat uu____5195 uu____5197)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5194))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5193))
end
| FStar_Parser_AST.PatWild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.PatConst (c) -> begin
(p_constant c)
end
| FStar_Parser_AST.PatVar (lid, aqual) -> begin
(

let uu____5205 = (FStar_Pprint.optional p_aqual aqual)
in (

let uu____5206 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat uu____5205 uu____5206)))
end
| FStar_Parser_AST.PatName (uid) -> begin
(p_quident uid)
end
| FStar_Parser_AST.PatOr (uu____5208) -> begin
(failwith "Inner or pattern !")
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (uu____5211); FStar_Parser_AST.prange = uu____5212}, uu____5213) -> begin
(

let uu____5218 = (p_tuplePattern p)
in (soft_parens_with_nesting uu____5218))
end
| FStar_Parser_AST.PatTuple (uu____5219, false) -> begin
(

let uu____5224 = (p_tuplePattern p)
in (soft_parens_with_nesting uu____5224))
end
| uu____5225 -> begin
(

let uu____5226 = (

let uu____5227 = (FStar_Parser_AST.pat_to_string p)
in (FStar_Util.format1 "Invalid pattern %s" uu____5227))
in (failwith uu____5226))
end))
and p_binder : Prims.bool  ->  FStar_Parser_AST.binder  ->  FStar_Pprint.document = (fun is_atomic b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (lid) -> begin
(

let uu____5231 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (

let uu____5232 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat uu____5231 uu____5232)))
end
| FStar_Parser_AST.TVariable (lid) -> begin
(p_lident lid)
end
| FStar_Parser_AST.Annotated (lid, t) -> begin
(

let doc1 = (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t1); FStar_Parser_AST.brange = uu____5239; FStar_Parser_AST.blevel = uu____5240; FStar_Parser_AST.aqual = uu____5241}, phi) when (Prims.op_Equality lid.FStar_Ident.idText lid'.FStar_Ident.idText) -> begin
(

let uu____5243 = (p_ident lid)
in (p_refinement b.FStar_Parser_AST.aqual uu____5243 t1 phi))
end
| uu____5244 -> begin
(

let uu____5245 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (

let uu____5246 = (

let uu____5247 = (p_lident lid)
in (

let uu____5248 = (

let uu____5249 = (

let uu____5250 = (FStar_Pprint.break_ (Prims.parse_int "0"))
in (

let uu____5251 = (p_tmFormula t)
in (FStar_Pprint.op_Hat_Hat uu____5250 uu____5251)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5249))
in (FStar_Pprint.op_Hat_Hat uu____5247 uu____5248)))
in (FStar_Pprint.op_Hat_Hat uu____5245 uu____5246)))
end)
in (match (is_atomic) with
| true -> begin
(

let uu____5252 = (

let uu____5253 = (FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5253))
in (FStar_Pprint.group uu____5252))
end
| uu____5254 -> begin
(FStar_Pprint.group doc1)
end))
end
| FStar_Parser_AST.TAnnotated (uu____5255) -> begin
(failwith "Is this still used ?")
end
| FStar_Parser_AST.NoName (t) -> begin
(match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t1); FStar_Parser_AST.brange = uu____5262; FStar_Parser_AST.blevel = uu____5263; FStar_Parser_AST.aqual = uu____5264}, phi) -> begin
(match (is_atomic) with
| true -> begin
(

let uu____5266 = (

let uu____5267 = (

let uu____5268 = (p_refinement b.FStar_Parser_AST.aqual FStar_Pprint.underscore t1 phi)
in (FStar_Pprint.op_Hat_Hat uu____5268 FStar_Pprint.rparen))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5267))
in (FStar_Pprint.group uu____5266))
end
| uu____5269 -> begin
(

let uu____5270 = (p_refinement b.FStar_Parser_AST.aqual FStar_Pprint.underscore t1 phi)
in (FStar_Pprint.group uu____5270))
end)
end
| uu____5271 -> begin
(match (is_atomic) with
| true -> begin
(p_atomicTerm t)
end
| uu____5272 -> begin
(p_appTerm t)
end)
end)
end))
and p_refinement : FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Pprint.document  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun aqual_opt binder t phi -> (

let uu____5279 = (FStar_Pprint.optional p_aqual aqual_opt)
in (

let uu____5280 = (

let uu____5281 = (

let uu____5282 = (

let uu____5283 = (p_appTerm t)
in (

let uu____5284 = (

let uu____5285 = (p_noSeqTerm false false phi)
in (soft_braces_with_nesting uu____5285))
in (FStar_Pprint.op_Hat_Hat uu____5283 uu____5284)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5282))
in (FStar_Pprint.op_Hat_Hat binder uu____5281))
in (FStar_Pprint.op_Hat_Hat uu____5279 uu____5280))))
and p_binders : Prims.bool  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Pprint.document = (fun is_atomic bs -> (separate_map_or_flow break1 (p_binder is_atomic) bs))
and p_qlident : FStar_Ident.lid  ->  FStar_Pprint.document = (fun lid -> (

let uu____5291 = (FStar_Ident.text_of_lid lid)
in (str uu____5291)))
and p_quident : FStar_Ident.lid  ->  FStar_Pprint.document = (fun lid -> (

let uu____5293 = (FStar_Ident.text_of_lid lid)
in (str uu____5293)))
and p_ident : FStar_Ident.ident  ->  FStar_Pprint.document = (fun lid -> (

let uu____5295 = (FStar_Ident.text_of_id lid)
in (str uu____5295)))
and p_lident : FStar_Ident.ident  ->  FStar_Pprint.document = (fun lid -> (

let uu____5297 = (FStar_Ident.text_of_id lid)
in (str uu____5297)))
and p_uident : FStar_Ident.ident  ->  FStar_Pprint.document = (fun lid -> (

let uu____5299 = (FStar_Ident.text_of_id lid)
in (str uu____5299)))
and p_tvar : FStar_Ident.ident  ->  FStar_Pprint.document = (fun lid -> (

let uu____5301 = (FStar_Ident.text_of_id lid)
in (str uu____5301)))
and p_lidentOrUnderscore : FStar_Ident.ident  ->  FStar_Pprint.document = (fun id1 -> (match ((FStar_Util.starts_with FStar_Ident.reserved_prefix id1.FStar_Ident.idText)) with
| true -> begin
FStar_Pprint.underscore
end
| uu____5303 -> begin
(p_lident id1)
end))
and paren_if : Prims.bool  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun b -> (match (b) with
| true -> begin
soft_parens_with_nesting
end
| uu____5308 -> begin
(fun x -> x)
end))
and p_term : Prims.bool  ->  Prims.bool  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun ps pb e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Seq (e1, e2) -> begin
(

let uu____5315 = (

let uu____5316 = (

let uu____5317 = (p_noSeqTerm true false e1)
in (FStar_Pprint.op_Hat_Hat uu____5317 FStar_Pprint.semi))
in (FStar_Pprint.group uu____5316))
in (

let uu____5318 = (p_term ps pb e2)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5315 uu____5318)))
end
| FStar_Parser_AST.Bind (x, e1, e2) -> begin
(

let uu____5322 = (

let uu____5323 = (

let uu____5324 = (

let uu____5325 = (p_lident x)
in (

let uu____5326 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.long_left_arrow)
in (FStar_Pprint.op_Hat_Hat uu____5325 uu____5326)))
in (

let uu____5327 = (

let uu____5328 = (p_noSeqTerm true false e1)
in (

let uu____5329 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.semi)
in (FStar_Pprint.op_Hat_Hat uu____5328 uu____5329)))
in (op_Hat_Slash_Plus_Hat uu____5324 uu____5327)))
in (FStar_Pprint.group uu____5323))
in (

let uu____5330 = (p_term ps pb e2)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5322 uu____5330)))
end
| uu____5331 -> begin
(

let uu____5332 = (p_noSeqTerm ps pb e)
in (FStar_Pprint.group uu____5332))
end))
and p_noSeqTerm : Prims.bool  ->  Prims.bool  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun ps pb e -> (with_comment (p_noSeqTerm' ps pb) e e.FStar_Parser_AST.range))
and p_noSeqTerm' : Prims.bool  ->  Prims.bool  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun ps pb e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Ascribed (e1, t, FStar_Pervasives_Native.None) -> begin
(

let uu____5343 = (

let uu____5344 = (p_tmIff e1)
in (

let uu____5345 = (

let uu____5346 = (

let uu____5347 = (p_typ ps pb t)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5347))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____5346))
in (FStar_Pprint.op_Hat_Slash_Hat uu____5344 uu____5345)))
in (FStar_Pprint.group uu____5343))
end
| FStar_Parser_AST.Ascribed (e1, t, FStar_Pervasives_Native.Some (tac)) -> begin
(

let uu____5353 = (

let uu____5354 = (p_tmIff e1)
in (

let uu____5355 = (

let uu____5356 = (

let uu____5357 = (

let uu____5358 = (p_typ false false t)
in (

let uu____5359 = (

let uu____5360 = (str "by")
in (

let uu____5361 = (p_typ ps pb tac)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5360 uu____5361)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____5358 uu____5359)))
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5357))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____5356))
in (FStar_Pprint.op_Hat_Slash_Hat uu____5354 uu____5355)))
in (FStar_Pprint.group uu____5353))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = ".()<-"; FStar_Ident.idRange = uu____5362}, (e1)::(e2)::(e3)::[]) -> begin
(

let uu____5368 = (

let uu____5369 = (

let uu____5370 = (

let uu____5371 = (p_atomicTermNotQUident e1)
in (

let uu____5372 = (

let uu____5373 = (

let uu____5374 = (

let uu____5375 = (p_term false false e2)
in (soft_parens_with_nesting uu____5375))
in (

let uu____5376 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat uu____5374 uu____5376)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5373))
in (FStar_Pprint.op_Hat_Hat uu____5371 uu____5372)))
in (FStar_Pprint.group uu____5370))
in (

let uu____5377 = (

let uu____5378 = (p_noSeqTerm ps pb e3)
in (jump2 uu____5378))
in (FStar_Pprint.op_Hat_Hat uu____5369 uu____5377)))
in (FStar_Pprint.group uu____5368))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = ".[]<-"; FStar_Ident.idRange = uu____5379}, (e1)::(e2)::(e3)::[]) -> begin
(

let uu____5385 = (

let uu____5386 = (

let uu____5387 = (

let uu____5388 = (p_atomicTermNotQUident e1)
in (

let uu____5389 = (

let uu____5390 = (

let uu____5391 = (

let uu____5392 = (p_term false false e2)
in (soft_brackets_with_nesting uu____5392))
in (

let uu____5393 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat uu____5391 uu____5393)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5390))
in (FStar_Pprint.op_Hat_Hat uu____5388 uu____5389)))
in (FStar_Pprint.group uu____5387))
in (

let uu____5394 = (

let uu____5395 = (p_noSeqTerm ps pb e3)
in (jump2 uu____5395))
in (FStar_Pprint.op_Hat_Hat uu____5386 uu____5394)))
in (FStar_Pprint.group uu____5385))
end
| FStar_Parser_AST.Requires (e1, wtf) -> begin
(

let uu____5403 = (

let uu____5404 = (str "requires")
in (

let uu____5405 = (p_typ ps pb e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5404 uu____5405)))
in (FStar_Pprint.group uu____5403))
end
| FStar_Parser_AST.Ensures (e1, wtf) -> begin
(

let uu____5413 = (

let uu____5414 = (str "ensures")
in (

let uu____5415 = (p_typ ps pb e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5414 uu____5415)))
in (FStar_Pprint.group uu____5413))
end
| FStar_Parser_AST.Attributes (es) -> begin
(

let uu____5419 = (

let uu____5420 = (str "attributes")
in (

let uu____5421 = (FStar_Pprint.separate_map break1 p_atomicTerm es)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5420 uu____5421)))
in (FStar_Pprint.group uu____5419))
end
| FStar_Parser_AST.If (e1, e2, e3) -> begin
(match ((is_unit e3)) with
| true -> begin
(

let uu____5425 = (

let uu____5426 = (

let uu____5427 = (str "if")
in (

let uu____5428 = (p_noSeqTerm false false e1)
in (op_Hat_Slash_Plus_Hat uu____5427 uu____5428)))
in (

let uu____5429 = (

let uu____5430 = (str "then")
in (

let uu____5431 = (p_noSeqTerm ps pb e2)
in (op_Hat_Slash_Plus_Hat uu____5430 uu____5431)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____5426 uu____5429)))
in (FStar_Pprint.group uu____5425))
end
| uu____5432 -> begin
(

let e2_doc = (match (e2.FStar_Parser_AST.tm) with
| FStar_Parser_AST.If (uu____5434, uu____5435, e31) when (is_unit e31) -> begin
(

let uu____5437 = (p_noSeqTerm false false e2)
in (soft_parens_with_nesting uu____5437))
end
| uu____5438 -> begin
(p_noSeqTerm false false e2)
end)
in (

let uu____5439 = (

let uu____5440 = (

let uu____5441 = (str "if")
in (

let uu____5442 = (p_noSeqTerm false false e1)
in (op_Hat_Slash_Plus_Hat uu____5441 uu____5442)))
in (

let uu____5443 = (

let uu____5444 = (

let uu____5445 = (str "then")
in (op_Hat_Slash_Plus_Hat uu____5445 e2_doc))
in (

let uu____5446 = (

let uu____5447 = (str "else")
in (

let uu____5448 = (p_noSeqTerm ps pb e3)
in (op_Hat_Slash_Plus_Hat uu____5447 uu____5448)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____5444 uu____5446)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____5440 uu____5443)))
in (FStar_Pprint.group uu____5439)))
end)
end
| FStar_Parser_AST.TryWith (e1, branches) -> begin
(

let uu____5471 = (

let uu____5472 = (

let uu____5473 = (

let uu____5474 = (str "try")
in (

let uu____5475 = (p_noSeqTerm false false e1)
in (prefix2 uu____5474 uu____5475)))
in (

let uu____5476 = (

let uu____5477 = (str "with")
in (

let uu____5478 = (separate_map_last FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5477 uu____5478)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____5473 uu____5476)))
in (FStar_Pprint.group uu____5472))
in (

let uu____5487 = (paren_if (ps || pb))
in (uu____5487 uu____5471)))
end
| FStar_Parser_AST.Match (e1, branches) -> begin
(

let uu____5514 = (

let uu____5515 = (

let uu____5516 = (

let uu____5517 = (str "match")
in (

let uu____5518 = (p_noSeqTerm false false e1)
in (

let uu____5519 = (str "with")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____5517 uu____5518 uu____5519))))
in (

let uu____5520 = (separate_map_last FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5516 uu____5520)))
in (FStar_Pprint.group uu____5515))
in (

let uu____5529 = (paren_if (ps || pb))
in (uu____5529 uu____5514)))
end
| FStar_Parser_AST.LetOpen (uid, e1) -> begin
(

let uu____5536 = (

let uu____5537 = (

let uu____5538 = (

let uu____5539 = (str "let open")
in (

let uu____5540 = (p_quident uid)
in (

let uu____5541 = (str "in")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____5539 uu____5540 uu____5541))))
in (

let uu____5542 = (p_term false pb e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5538 uu____5542)))
in (FStar_Pprint.group uu____5537))
in (

let uu____5543 = (paren_if ps)
in (uu____5543 uu____5536)))
end
| FStar_Parser_AST.Let (q, lbs, e1) -> begin
(

let p_lb = (fun q1 uu____5607 is_last -> (match (uu____5607) with
| (a, (pat, e2)) -> begin
(

let attrs = (p_attrs_opt a)
in (

let doc_let_or_and = (match (q1) with
| FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec) -> begin
(

let uu____5640 = (

let uu____5641 = (str "let")
in (

let uu____5642 = (str "rec")
in (FStar_Pprint.op_Hat_Slash_Hat uu____5641 uu____5642)))
in (FStar_Pprint.group uu____5640))
end
| FStar_Pervasives_Native.Some (FStar_Parser_AST.NoLetQualifier) -> begin
(str "let")
end
| uu____5643 -> begin
(str "and")
end)
in (

let doc_pat = (p_letlhs ((pat), (e2)))
in (

let doc_expr = (p_term false false e2)
in (

let uu____5648 = (match (is_last) with
| true -> begin
(

let uu____5649 = (

let uu____5650 = (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") doc_let_or_and doc_pat FStar_Pprint.equals)
in (

let uu____5651 = (str "in")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____5650 doc_expr uu____5651)))
in (FStar_Pprint.group uu____5649))
end
| uu____5652 -> begin
(

let uu____5653 = (

let uu____5654 = (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") doc_let_or_and doc_pat FStar_Pprint.equals)
in (FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "1") uu____5654 doc_expr))
in (FStar_Pprint.group uu____5653))
end)
in (FStar_Pprint.op_Hat_Hat attrs uu____5648))))))
end))
in (

let l = (FStar_List.length lbs)
in (

let lbs_docs = (FStar_List.mapi (fun i lb -> (match ((Prims.op_Equality i (Prims.parse_int "0"))) with
| true -> begin
(

let uu____5700 = (p_lb (FStar_Pervasives_Native.Some (q)) lb (Prims.op_Equality i (l - (Prims.parse_int "1"))))
in (FStar_Pprint.group uu____5700))
end
| uu____5707 -> begin
(

let uu____5708 = (p_lb FStar_Pervasives_Native.None lb (Prims.op_Equality i (l - (Prims.parse_int "1"))))
in (FStar_Pprint.group uu____5708))
end)) lbs)
in (

let lbs_doc = (

let uu____5716 = (FStar_Pprint.separate break1 lbs_docs)
in (FStar_Pprint.group uu____5716))
in (

let uu____5717 = (

let uu____5718 = (

let uu____5719 = (

let uu____5720 = (p_term false pb e1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5720))
in (FStar_Pprint.op_Hat_Hat lbs_doc uu____5719))
in (FStar_Pprint.group uu____5718))
in (

let uu____5721 = (paren_if ps)
in (uu____5721 uu____5717)))))))
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, typ_opt); FStar_Parser_AST.prange = uu____5728})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, branches); FStar_Parser_AST.range = uu____5731; FStar_Parser_AST.level = uu____5732}) when (matches_var maybe_x x) -> begin
(

let uu____5759 = (

let uu____5760 = (

let uu____5761 = (str "function")
in (

let uu____5762 = (separate_map_last FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5761 uu____5762)))
in (FStar_Pprint.group uu____5760))
in (

let uu____5771 = (paren_if (ps || pb))
in (uu____5771 uu____5759)))
end
| FStar_Parser_AST.Quote (e1, FStar_Parser_AST.Dynamic) -> begin
(

let uu____5777 = (

let uu____5778 = (str "quote")
in (

let uu____5779 = (p_noSeqTerm ps pb e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5778 uu____5779)))
in (FStar_Pprint.group uu____5777))
end
| FStar_Parser_AST.Quote (e1, FStar_Parser_AST.Static) -> begin
(

let uu____5781 = (

let uu____5782 = (str "`")
in (

let uu____5783 = (p_noSeqTerm ps pb e1)
in (FStar_Pprint.op_Hat_Hat uu____5782 uu____5783)))
in (FStar_Pprint.group uu____5781))
end
| FStar_Parser_AST.VQuote (e1) -> begin
(

let uu____5785 = (

let uu____5786 = (str "%`")
in (

let uu____5787 = (p_noSeqTerm ps pb e1)
in (FStar_Pprint.op_Hat_Hat uu____5786 uu____5787)))
in (FStar_Pprint.group uu____5785))
end
| FStar_Parser_AST.Antiquote (false, e1) -> begin
(

let uu____5789 = (

let uu____5790 = (str "`#")
in (

let uu____5791 = (p_noSeqTerm ps pb e1)
in (FStar_Pprint.op_Hat_Hat uu____5790 uu____5791)))
in (FStar_Pprint.group uu____5789))
end
| FStar_Parser_AST.Antiquote (true, e1) -> begin
(

let uu____5793 = (

let uu____5794 = (str "`@")
in (

let uu____5795 = (p_noSeqTerm ps pb e1)
in (FStar_Pprint.op_Hat_Hat uu____5794 uu____5795)))
in (FStar_Pprint.group uu____5793))
end
| uu____5796 -> begin
(p_typ ps pb e)
end))
and p_attrs_opt : FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option  ->  FStar_Pprint.document = (fun uu___67_5797 -> (match (uu___67_5797) with
| FStar_Pervasives_Native.None -> begin
FStar_Pprint.empty
end
| FStar_Pervasives_Native.Some (terms) -> begin
(

let uu____5809 = (

let uu____5810 = (

let uu____5811 = (str "[@")
in (

let uu____5812 = (

let uu____5813 = (FStar_Pprint.separate_map break1 p_atomicTerm terms)
in (

let uu____5814 = (str "]")
in (FStar_Pprint.op_Hat_Slash_Hat uu____5813 uu____5814)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____5811 uu____5812)))
in (FStar_Pprint.group uu____5810))
in (FStar_Pprint.op_Hat_Hat uu____5809 break1))
end))
and p_typ : Prims.bool  ->  Prims.bool  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun ps pb e -> (with_comment (p_typ' ps pb) e e.FStar_Parser_AST.range))
and p_typ' : Prims.bool  ->  Prims.bool  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun ps pb e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.QForall (bs, trigger, e1) -> begin
(

let uu____5836 = (

let uu____5837 = (

let uu____5838 = (p_quantifier e)
in (FStar_Pprint.op_Hat_Hat uu____5838 FStar_Pprint.space))
in (

let uu____5839 = (p_binders true bs)
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") uu____5837 uu____5839 FStar_Pprint.dot)))
in (

let uu____5840 = (

let uu____5841 = (p_trigger trigger)
in (

let uu____5842 = (p_noSeqTerm ps pb e1)
in (FStar_Pprint.op_Hat_Hat uu____5841 uu____5842)))
in (prefix2 uu____5836 uu____5840)))
end
| FStar_Parser_AST.QExists (bs, trigger, e1) -> begin
(

let uu____5858 = (

let uu____5859 = (

let uu____5860 = (p_quantifier e)
in (FStar_Pprint.op_Hat_Hat uu____5860 FStar_Pprint.space))
in (

let uu____5861 = (p_binders true bs)
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") uu____5859 uu____5861 FStar_Pprint.dot)))
in (

let uu____5862 = (

let uu____5863 = (p_trigger trigger)
in (

let uu____5864 = (p_noSeqTerm ps pb e1)
in (FStar_Pprint.op_Hat_Hat uu____5863 uu____5864)))
in (prefix2 uu____5858 uu____5862)))
end
| uu____5865 -> begin
(p_simpleTerm ps pb e)
end))
and p_quantifier : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.QForall (uu____5867) -> begin
(str "forall")
end
| FStar_Parser_AST.QExists (uu____5880) -> begin
(str "exists")
end
| uu____5893 -> begin
(failwith "Imposible : p_quantifier called on a non-quantifier term")
end))
and p_trigger : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun uu___68_5894 -> (match (uu___68_5894) with
| [] -> begin
FStar_Pprint.empty
end
| pats -> begin
(

let uu____5906 = (

let uu____5907 = (

let uu____5908 = (str "pattern")
in (

let uu____5909 = (

let uu____5910 = (

let uu____5911 = (p_disjunctivePats pats)
in (jump2 uu____5911))
in (

let uu____5912 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5910 uu____5912)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____5908 uu____5909)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5907))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____5906))
end))
and p_disjunctivePats : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun pats -> (

let uu____5918 = (str "\\/")
in (FStar_Pprint.separate_map uu____5918 p_conjunctivePats pats)))
and p_conjunctivePats : FStar_Parser_AST.term Prims.list  ->  FStar_Pprint.document = (fun pats -> (

let uu____5924 = (FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats)
in (FStar_Pprint.group uu____5924)))
and p_simpleTerm : Prims.bool  ->  Prims.bool  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun ps pb e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Abs (pats, e1) -> begin
(

let uu____5934 = (

let uu____5935 = (

let uu____5936 = (str "fun")
in (

let uu____5937 = (

let uu____5938 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5938 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat uu____5936 uu____5937)))
in (

let uu____5939 = (p_term false pb e1)
in (op_Hat_Slash_Plus_Hat uu____5935 uu____5939)))
in (

let uu____5940 = (paren_if ps)
in (uu____5940 uu____5934)))
end
| uu____5945 -> begin
(p_tmIff e)
end))
and p_maybeFocusArrow : Prims.bool  ->  FStar_Pprint.document = (fun b -> (match (b) with
| true -> begin
(str "~>")
end
| uu____5947 -> begin
FStar_Pprint.rarrow
end))
and p_patternBranch : Prims.bool  ->  (FStar_Parser_AST.pattern * FStar_Parser_AST.term FStar_Pervasives_Native.option * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun pb uu____5949 -> (match (uu____5949) with
| (pat, when_opt, e) -> begin
(

let uu____5965 = (

let uu____5966 = (

let uu____5967 = (

let uu____5968 = (

let uu____5969 = (

let uu____5970 = (p_disjunctivePattern pat)
in (

let uu____5971 = (

let uu____5972 = (p_maybeWhen when_opt)
in (FStar_Pprint.op_Hat_Hat uu____5972 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat uu____5970 uu____5971)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5969))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5968))
in (FStar_Pprint.group uu____5967))
in (

let uu____5973 = (p_term false pb e)
in (op_Hat_Slash_Plus_Hat uu____5966 uu____5973)))
in (FStar_Pprint.group uu____5965))
end))
and p_maybeWhen : FStar_Parser_AST.term FStar_Pervasives_Native.option  ->  FStar_Pprint.document = (fun uu___69_5974 -> (match (uu___69_5974) with
| FStar_Pervasives_Native.None -> begin
FStar_Pprint.empty
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____5978 = (str "when")
in (

let uu____5979 = (

let uu____5980 = (p_tmFormula e)
in (FStar_Pprint.op_Hat_Hat uu____5980 FStar_Pprint.space))
in (op_Hat_Slash_Plus_Hat uu____5978 uu____5979)))
end))
and p_tmIff : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5982}, (e1)::(e2)::[]) -> begin
(

let uu____5987 = (str "<==>")
in (

let uu____5988 = (p_tmImplies e1)
in (

let uu____5989 = (p_tmIff e2)
in (infix0 uu____5987 uu____5988 uu____5989))))
end
| uu____5990 -> begin
(p_tmImplies e)
end))
and p_tmImplies : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5992}, (e1)::(e2)::[]) -> begin
(

let uu____5997 = (str "==>")
in (

let uu____5998 = (p_tmArrow p_tmFormula e1)
in (

let uu____5999 = (p_tmImplies e2)
in (infix0 uu____5997 uu____5998 uu____5999))))
end
| uu____6000 -> begin
(p_tmArrow p_tmFormula e)
end))
and p_tmArrow : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_Tm e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Product (bs, tgt) -> begin
(

let uu____6011 = (

let uu____6012 = (separate_map_or_flow FStar_Pprint.empty (fun b -> (

let uu____6017 = (p_binder false b)
in (

let uu____6018 = (

let uu____6019 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6019))
in (FStar_Pprint.op_Hat_Hat uu____6017 uu____6018)))) bs)
in (

let uu____6020 = (p_tmArrow p_Tm tgt)
in (FStar_Pprint.op_Hat_Hat uu____6012 uu____6020)))
in (FStar_Pprint.group uu____6011))
end
| uu____6021 -> begin
(p_Tm e)
end))
and p_tmFormula : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____6023}, (e1)::(e2)::[]) -> begin
(

let uu____6028 = (str "\\/")
in (

let uu____6029 = (p_tmFormula e1)
in (

let uu____6030 = (p_tmConjunction e2)
in (infix0 uu____6028 uu____6029 uu____6030))))
end
| uu____6031 -> begin
(p_tmConjunction e)
end))
and p_tmConjunction : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____6033}, (e1)::(e2)::[]) -> begin
(

let uu____6038 = (str "/\\")
in (

let uu____6039 = (p_tmConjunction e1)
in (

let uu____6040 = (p_tmTuple e2)
in (infix0 uu____6038 uu____6039 uu____6040))))
end
| uu____6041 -> begin
(p_tmTuple e)
end))
and p_tmTuple : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_tmTuple' e e.FStar_Parser_AST.range))
and p_tmTuple' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (lid, args) when (is_tuple_constructor lid) -> begin
(

let uu____6058 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map uu____6058 (fun uu____6066 -> (match (uu____6066) with
| (e1, uu____6072) -> begin
(p_tmEq e1)
end)) args))
end
| uu____6073 -> begin
(p_tmEq e)
end))
and paren_if_gt : Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun curr mine doc1 -> (match ((mine <= curr)) with
| true -> begin
doc1
end
| uu____6077 -> begin
(

let uu____6078 = (

let uu____6079 = (FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6079))
in (FStar_Pprint.group uu____6078))
end))
and p_tmEqWith : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_X e -> (

let n1 = (max_level (FStar_List.append (((colon_equals ()))::((pipe_right ()))::[]) (operatorInfix0ad12 ())))
in (p_tmEqWith' p_X n1 e)))
and p_tmEqWith' : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_X curr e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (((is_operatorInfix0ad12 op) || (

let uu____6142 = (FStar_Ident.text_of_id op)
in (Prims.op_Equality uu____6142 "="))) || (

let uu____6144 = (FStar_Ident.text_of_id op)
in (Prims.op_Equality uu____6144 "|>"))) -> begin
(

let op1 = (FStar_Ident.text_of_id op)
in (

let uu____6146 = (levels op1)
in (match (uu____6146) with
| (left1, mine, right1) -> begin
(

let uu____6156 = (

let uu____6157 = (FStar_All.pipe_left str op1)
in (

let uu____6158 = (p_tmEqWith' p_X left1 e1)
in (

let uu____6159 = (p_tmEqWith' p_X right1 e2)
in (infix0 uu____6157 uu____6158 uu____6159))))
in (paren_if_gt curr mine uu____6156))
end)))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____6160}, (e1)::(e2)::[]) -> begin
(

let uu____6165 = (

let uu____6166 = (p_tmEqWith p_X e1)
in (

let uu____6167 = (

let uu____6168 = (

let uu____6169 = (

let uu____6170 = (p_tmEqWith p_X e2)
in (op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____6170))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6169))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6168))
in (FStar_Pprint.op_Hat_Hat uu____6166 uu____6167)))
in (FStar_Pprint.group uu____6165))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____6171}, (e1)::[]) -> begin
(

let uu____6175 = (levels "-")
in (match (uu____6175) with
| (left1, mine, right1) -> begin
(

let uu____6185 = (p_tmEqWith' p_X mine e1)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____6185))
end))
end
| uu____6186 -> begin
(p_tmNoEqWith p_X e)
end))
and p_tmNoEqWith : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_X e -> (

let n1 = (max_level (((colon_colon ()))::((amp ()))::((opinfix3 ()))::((opinfix4 ()))::[]))
in (p_tmNoEqWith' p_X n1 e)))
and p_tmNoEqWith' : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_X curr e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (lid, ((e1, uu____6257))::((e2, uu____6259))::[]) when ((FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) && (

let uu____6279 = (is_list e)
in (not (uu____6279)))) -> begin
(

let op = "::"
in (

let uu____6281 = (levels op)
in (match (uu____6281) with
| (left1, mine, right1) -> begin
(

let uu____6291 = (

let uu____6292 = (str op)
in (

let uu____6293 = (p_tmNoEqWith' p_X left1 e1)
in (

let uu____6294 = (p_tmNoEqWith' p_X right1 e2)
in (infix0 uu____6292 uu____6293 uu____6294))))
in (paren_if_gt curr mine uu____6291))
end)))
end
| FStar_Parser_AST.Sum (binders, res) -> begin
(

let op = "&"
in (

let uu____6302 = (levels op)
in (match (uu____6302) with
| (left1, mine, right1) -> begin
(

let p_dsumfst = (fun b -> (

let uu____6318 = (p_binder false b)
in (

let uu____6319 = (

let uu____6320 = (

let uu____6321 = (str op)
in (FStar_Pprint.op_Hat_Hat uu____6321 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6320))
in (FStar_Pprint.op_Hat_Hat uu____6318 uu____6319))))
in (

let uu____6322 = (

let uu____6323 = (FStar_Pprint.concat_map p_dsumfst binders)
in (

let uu____6324 = (p_tmNoEqWith' p_X right1 res)
in (FStar_Pprint.op_Hat_Hat uu____6323 uu____6324)))
in (paren_if_gt curr mine uu____6322)))
end)))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (is_operatorInfix34 op) -> begin
(

let op1 = (FStar_Ident.text_of_id op)
in (

let uu____6331 = (levels op1)
in (match (uu____6331) with
| (left1, mine, right1) -> begin
(

let uu____6341 = (

let uu____6342 = (str op1)
in (

let uu____6343 = (p_tmNoEqWith' p_X left1 e1)
in (

let uu____6344 = (p_tmNoEqWith' p_X right1 e2)
in (infix0 uu____6342 uu____6343 uu____6344))))
in (paren_if_gt curr mine uu____6341))
end)))
end
| FStar_Parser_AST.Record (with_opt, record_fields) -> begin
(

let uu____6363 = (

let uu____6364 = (default_or_map FStar_Pprint.empty p_with_clause with_opt)
in (

let uu____6365 = (

let uu____6366 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (separate_map_last uu____6366 p_simpleDef record_fields))
in (FStar_Pprint.op_Hat_Hat uu____6364 uu____6365)))
in (braces_with_nesting uu____6363))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____6371}, (e1)::[]) -> begin
(

let uu____6375 = (

let uu____6376 = (str "~")
in (

let uu____6377 = (p_atomicTerm e1)
in (FStar_Pprint.op_Hat_Hat uu____6376 uu____6377)))
in (FStar_Pprint.group uu____6375))
end
| uu____6378 -> begin
(p_X e)
end))
and p_tmEqNoRefinement : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_tmEqWith p_appTerm e))
and p_tmEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_tmEqWith p_tmRefinement e))
and p_tmNoEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_tmNoEqWith p_tmRefinement e))
and p_tmRefinement : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.NamedTyp (lid, e1) -> begin
(

let uu____6385 = (

let uu____6386 = (p_lidentOrUnderscore lid)
in (

let uu____6387 = (

let uu____6388 = (p_appTerm e1)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6388))
in (FStar_Pprint.op_Hat_Slash_Hat uu____6386 uu____6387)))
in (FStar_Pprint.group uu____6385))
end
| FStar_Parser_AST.Refine (b, phi) -> begin
(p_refinedBinder b phi)
end
| uu____6391 -> begin
(p_appTerm e)
end))
and p_with_clause : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____6393 = (p_appTerm e)
in (

let uu____6394 = (

let uu____6395 = (

let uu____6396 = (str "with")
in (FStar_Pprint.op_Hat_Hat uu____6396 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6395))
in (FStar_Pprint.op_Hat_Hat uu____6393 uu____6394))))
and p_refinedBinder : FStar_Parser_AST.binder  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun b phi -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (lid, t) -> begin
(

let uu____6401 = (

let uu____6402 = (p_lident lid)
in (p_refinement b.FStar_Parser_AST.aqual uu____6402 t phi))
in (soft_parens_with_nesting uu____6401))
end
| FStar_Parser_AST.TAnnotated (uu____6403) -> begin
(failwith "Is this still used ?")
end
| FStar_Parser_AST.Variable (uu____6408) -> begin
(

let uu____6409 = (

let uu____6410 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" uu____6410))
in (failwith uu____6409))
end
| FStar_Parser_AST.TVariable (uu____6411) -> begin
(

let uu____6412 = (

let uu____6413 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" uu____6413))
in (failwith uu____6412))
end
| FStar_Parser_AST.NoName (uu____6414) -> begin
(

let uu____6415 = (

let uu____6416 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" uu____6416))
in (failwith uu____6415))
end))
and p_simpleDef : Prims.bool  ->  (FStar_Ident.lid * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun ps uu____6418 -> (match (uu____6418) with
| (lid, e) -> begin
(

let uu____6425 = (

let uu____6426 = (p_qlident lid)
in (

let uu____6427 = (

let uu____6428 = (p_noSeqTerm ps false e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____6428))
in (FStar_Pprint.op_Hat_Slash_Hat uu____6426 uu____6427)))
in (FStar_Pprint.group uu____6425))
end))
and p_appTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App (uu____6430) when (is_general_application e) -> begin
(

let uu____6437 = (head_and_args e)
in (match (uu____6437) with
| (head1, args) -> begin
(

let uu____6462 = (

let uu____6473 = (FStar_ST.op_Bang should_print_fs_typ_app)
in (match (uu____6473) with
| true -> begin
(

let uu____6513 = (FStar_Util.take (fun uu____6537 -> (match (uu____6537) with
| (uu____6542, aq) -> begin
(Prims.op_Equality aq FStar_Parser_AST.FsTypApp)
end)) args)
in (match (uu____6513) with
| (fs_typ_args, args1) -> begin
(

let uu____6580 = (

let uu____6581 = (p_indexingTerm head1)
in (

let uu____6582 = (

let uu____6583 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (soft_surround_map_or_flow (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.empty FStar_Pprint.langle uu____6583 FStar_Pprint.rangle p_fsTypArg fs_typ_args))
in (FStar_Pprint.op_Hat_Hat uu____6581 uu____6582)))
in ((uu____6580), (args1)))
end))
end
| uu____6594 -> begin
(

let uu____6595 = (p_indexingTerm head1)
in ((uu____6595), (args)))
end))
in (match (uu____6462) with
| (head_doc, args1) -> begin
(

let uu____6616 = (

let uu____6617 = (FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space)
in (soft_surround_map_or_flow (Prims.parse_int "2") (Prims.parse_int "0") head_doc uu____6617 break1 FStar_Pprint.empty p_argTerm args1))
in (FStar_Pprint.group uu____6616))
end))
end))
end
| FStar_Parser_AST.Construct (lid, args) when ((is_general_construction e) && (

let uu____6637 = (is_dtuple_constructor lid)
in (not (uu____6637)))) -> begin
(match (args) with
| [] -> begin
(p_quident lid)
end
| (arg)::[] -> begin
(

let uu____6655 = (

let uu____6656 = (p_quident lid)
in (

let uu____6657 = (p_argTerm arg)
in (FStar_Pprint.op_Hat_Slash_Hat uu____6656 uu____6657)))
in (FStar_Pprint.group uu____6655))
end
| (hd1)::tl1 -> begin
(

let uu____6674 = (

let uu____6675 = (

let uu____6676 = (

let uu____6677 = (p_quident lid)
in (

let uu____6678 = (p_argTerm hd1)
in (prefix2 uu____6677 uu____6678)))
in (FStar_Pprint.group uu____6676))
in (

let uu____6679 = (

let uu____6680 = (FStar_Pprint.separate_map break1 p_argTerm tl1)
in (jump2 uu____6680))
in (FStar_Pprint.op_Hat_Hat uu____6675 uu____6679)))
in (FStar_Pprint.group uu____6674))
end)
end
| uu____6685 -> begin
(p_indexingTerm e)
end))
and p_argTerm : (FStar_Parser_AST.term * FStar_Parser_AST.imp)  ->  FStar_Pprint.document = (fun arg_imp -> (match (arg_imp) with
| (u, FStar_Parser_AST.UnivApp) -> begin
(p_universe u)
end
| (e, FStar_Parser_AST.FsTypApp) -> begin
((FStar_Errors.log_issue e.FStar_Parser_AST.range ((FStar_Errors.Warning_UnexpectedFsTypApp), ("Unexpected FsTypApp, output might not be formatted correctly.")));
(

let uu____6694 = (p_indexingTerm e)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.langle uu____6694 FStar_Pprint.rangle));
)
end
| (e, FStar_Parser_AST.Hash) -> begin
(

let uu____6696 = (str "#")
in (

let uu____6697 = (p_indexingTerm e)
in (FStar_Pprint.op_Hat_Hat uu____6696 uu____6697)))
end
| (e, FStar_Parser_AST.Nothing) -> begin
(p_indexingTerm e)
end))
and p_fsTypArg : (FStar_Parser_AST.term * FStar_Parser_AST.imp)  ->  FStar_Pprint.document = (fun uu____6699 -> (match (uu____6699) with
| (e, uu____6705) -> begin
(p_indexingTerm e)
end))
and p_indexingTerm_aux : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun exit1 e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____6710}, (e1)::(e2)::[]) -> begin
(

let uu____6715 = (

let uu____6716 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (

let uu____6717 = (

let uu____6718 = (

let uu____6719 = (p_term false false e2)
in (soft_parens_with_nesting uu____6719))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6718))
in (FStar_Pprint.op_Hat_Hat uu____6716 uu____6717)))
in (FStar_Pprint.group uu____6715))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____6720}, (e1)::(e2)::[]) -> begin
(

let uu____6725 = (

let uu____6726 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (

let uu____6727 = (

let uu____6728 = (

let uu____6729 = (p_term false false e2)
in (soft_brackets_with_nesting uu____6729))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6728))
in (FStar_Pprint.op_Hat_Hat uu____6726 uu____6727)))
in (FStar_Pprint.group uu____6725))
end
| uu____6730 -> begin
(exit1 e)
end))
and p_indexingTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_indexingTerm_aux p_atomicTerm e))
and p_atomicTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.LetOpen (lid, e1) -> begin
(

let uu____6735 = (p_quident lid)
in (

let uu____6736 = (

let uu____6737 = (

let uu____6738 = (p_term false false e1)
in (soft_parens_with_nesting uu____6738))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6737))
in (FStar_Pprint.op_Hat_Hat uu____6735 uu____6736)))
end
| FStar_Parser_AST.Name (lid) -> begin
(p_quident lid)
end
| FStar_Parser_AST.Op (op, (e1)::[]) when (is_general_prefix_op op) -> begin
(

let uu____6744 = (

let uu____6745 = (FStar_Ident.text_of_id op)
in (str uu____6745))
in (

let uu____6746 = (p_atomicTerm e1)
in (FStar_Pprint.op_Hat_Hat uu____6744 uu____6746)))
end
| uu____6747 -> begin
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
| uu____6754 -> begin
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

let uu____6761 = (

let uu____6762 = (FStar_Ident.text_of_id op)
in (str uu____6762))
in (

let uu____6763 = (p_atomicTermNotQUident e1)
in (FStar_Pprint.op_Hat_Hat uu____6761 uu____6763)))
end
| FStar_Parser_AST.Op (op, []) -> begin
(

let uu____6767 = (

let uu____6768 = (

let uu____6769 = (

let uu____6770 = (FStar_Ident.text_of_id op)
in (str uu____6770))
in (

let uu____6771 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat uu____6769 uu____6771)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6768))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6767))
end
| FStar_Parser_AST.Construct (lid, args) when (is_dtuple_constructor lid) -> begin
(

let uu____6786 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (

let uu____6787 = (

let uu____6788 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (

let uu____6789 = (FStar_List.map FStar_Pervasives_Native.fst args)
in (FStar_Pprint.separate_map uu____6788 p_tmEq uu____6789)))
in (

let uu____6796 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____6786 uu____6787 uu____6796))))
end
| FStar_Parser_AST.Project (e1, lid) -> begin
(

let uu____6799 = (

let uu____6800 = (p_atomicTermNotQUident e1)
in (

let uu____6801 = (

let uu____6802 = (p_qlident lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6802))
in (FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0") uu____6800 uu____6801)))
in (FStar_Pprint.group uu____6799))
end
| uu____6803 -> begin
(p_projectionLHS e)
end))
and p_projectionLHS : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (lid) -> begin
(p_qlident lid)
end
| FStar_Parser_AST.Projector (constr_lid, field_lid) -> begin
(

let uu____6808 = (p_quident constr_lid)
in (

let uu____6809 = (

let uu____6810 = (

let uu____6811 = (p_lident field_lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6811))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6810))
in (FStar_Pprint.op_Hat_Hat uu____6808 uu____6809)))
end
| FStar_Parser_AST.Discrim (constr_lid) -> begin
(

let uu____6813 = (p_quident constr_lid)
in (FStar_Pprint.op_Hat_Hat uu____6813 FStar_Pprint.qmark))
end
| FStar_Parser_AST.Paren (e1) -> begin
(

let uu____6815 = (p_term false false e1)
in (soft_parens_with_nesting uu____6815))
end
| uu____6816 when (is_array e) -> begin
(

let es = (extract_from_list e)
in (

let uu____6820 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar)
in (

let uu____6821 = (

let uu____6822 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (separate_map_or_flow_last uu____6822 (fun ps -> (p_noSeqTerm ps false)) es))
in (

let uu____6825 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") uu____6820 uu____6821 uu____6825)))))
end
| uu____6826 when (is_list e) -> begin
(

let uu____6827 = (

let uu____6828 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (

let uu____6829 = (extract_from_list e)
in (separate_map_or_flow_last uu____6828 (fun ps -> (p_noSeqTerm ps false)) uu____6829)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket uu____6827 FStar_Pprint.rbracket))
end
| uu____6834 when (is_lex_list e) -> begin
(

let uu____6835 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket)
in (

let uu____6836 = (

let uu____6837 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (

let uu____6838 = (extract_from_list e)
in (separate_map_or_flow_last uu____6837 (fun ps -> (p_noSeqTerm ps false)) uu____6838)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____6835 uu____6836 FStar_Pprint.rbracket)))
end
| uu____6843 when (is_ref_set e) -> begin
(

let es = (extract_from_ref_set e)
in (

let uu____6847 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace)
in (

let uu____6848 = (

let uu____6849 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (separate_map_or_flow uu____6849 p_appTerm es))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") uu____6847 uu____6848 FStar_Pprint.rbrace))))
end
| FStar_Parser_AST.Labeled (e1, s, b) -> begin
(

let uu____6853 = (str (Prims.strcat "(*" (Prims.strcat s "*)")))
in (

let uu____6854 = (p_term false false e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____6853 uu____6854)))
end
| FStar_Parser_AST.Op (op, args) when (

let uu____6861 = (handleable_op op args)
in (not (uu____6861))) -> begin
(

let uu____6862 = (

let uu____6863 = (

let uu____6864 = (FStar_Ident.text_of_id op)
in (

let uu____6865 = (

let uu____6866 = (

let uu____6867 = (FStar_Util.string_of_int (FStar_List.length args))
in (Prims.strcat uu____6867 " arguments couldn\'t be handled by the pretty printer"))
in (Prims.strcat " with " uu____6866))
in (Prims.strcat uu____6864 uu____6865)))
in (Prims.strcat "Operation " uu____6863))
in (failwith uu____6862))
end
| FStar_Parser_AST.Uvar (uu____6868) -> begin
(failwith "Unexpected universe variable out of universe context")
end
| FStar_Parser_AST.Wild -> begin
(

let uu____6869 = (p_term false false e)
in (soft_parens_with_nesting uu____6869))
end
| FStar_Parser_AST.Const (uu____6870) -> begin
(

let uu____6871 = (p_term false false e)
in (soft_parens_with_nesting uu____6871))
end
| FStar_Parser_AST.Op (uu____6872) -> begin
(

let uu____6879 = (p_term false false e)
in (soft_parens_with_nesting uu____6879))
end
| FStar_Parser_AST.Tvar (uu____6880) -> begin
(

let uu____6881 = (p_term false false e)
in (soft_parens_with_nesting uu____6881))
end
| FStar_Parser_AST.Var (uu____6882) -> begin
(

let uu____6883 = (p_term false false e)
in (soft_parens_with_nesting uu____6883))
end
| FStar_Parser_AST.Name (uu____6884) -> begin
(

let uu____6885 = (p_term false false e)
in (soft_parens_with_nesting uu____6885))
end
| FStar_Parser_AST.Construct (uu____6886) -> begin
(

let uu____6897 = (p_term false false e)
in (soft_parens_with_nesting uu____6897))
end
| FStar_Parser_AST.Abs (uu____6898) -> begin
(

let uu____6905 = (p_term false false e)
in (soft_parens_with_nesting uu____6905))
end
| FStar_Parser_AST.App (uu____6906) -> begin
(

let uu____6913 = (p_term false false e)
in (soft_parens_with_nesting uu____6913))
end
| FStar_Parser_AST.Let (uu____6914) -> begin
(

let uu____6935 = (p_term false false e)
in (soft_parens_with_nesting uu____6935))
end
| FStar_Parser_AST.LetOpen (uu____6936) -> begin
(

let uu____6941 = (p_term false false e)
in (soft_parens_with_nesting uu____6941))
end
| FStar_Parser_AST.Seq (uu____6942) -> begin
(

let uu____6947 = (p_term false false e)
in (soft_parens_with_nesting uu____6947))
end
| FStar_Parser_AST.Bind (uu____6948) -> begin
(

let uu____6955 = (p_term false false e)
in (soft_parens_with_nesting uu____6955))
end
| FStar_Parser_AST.If (uu____6956) -> begin
(

let uu____6963 = (p_term false false e)
in (soft_parens_with_nesting uu____6963))
end
| FStar_Parser_AST.Match (uu____6964) -> begin
(

let uu____6979 = (p_term false false e)
in (soft_parens_with_nesting uu____6979))
end
| FStar_Parser_AST.TryWith (uu____6980) -> begin
(

let uu____6995 = (p_term false false e)
in (soft_parens_with_nesting uu____6995))
end
| FStar_Parser_AST.Ascribed (uu____6996) -> begin
(

let uu____7005 = (p_term false false e)
in (soft_parens_with_nesting uu____7005))
end
| FStar_Parser_AST.Record (uu____7006) -> begin
(

let uu____7019 = (p_term false false e)
in (soft_parens_with_nesting uu____7019))
end
| FStar_Parser_AST.Project (uu____7020) -> begin
(

let uu____7025 = (p_term false false e)
in (soft_parens_with_nesting uu____7025))
end
| FStar_Parser_AST.Product (uu____7026) -> begin
(

let uu____7033 = (p_term false false e)
in (soft_parens_with_nesting uu____7033))
end
| FStar_Parser_AST.Sum (uu____7034) -> begin
(

let uu____7041 = (p_term false false e)
in (soft_parens_with_nesting uu____7041))
end
| FStar_Parser_AST.QForall (uu____7042) -> begin
(

let uu____7055 = (p_term false false e)
in (soft_parens_with_nesting uu____7055))
end
| FStar_Parser_AST.QExists (uu____7056) -> begin
(

let uu____7069 = (p_term false false e)
in (soft_parens_with_nesting uu____7069))
end
| FStar_Parser_AST.Refine (uu____7070) -> begin
(

let uu____7075 = (p_term false false e)
in (soft_parens_with_nesting uu____7075))
end
| FStar_Parser_AST.NamedTyp (uu____7076) -> begin
(

let uu____7081 = (p_term false false e)
in (soft_parens_with_nesting uu____7081))
end
| FStar_Parser_AST.Requires (uu____7082) -> begin
(

let uu____7089 = (p_term false false e)
in (soft_parens_with_nesting uu____7089))
end
| FStar_Parser_AST.Ensures (uu____7090) -> begin
(

let uu____7097 = (p_term false false e)
in (soft_parens_with_nesting uu____7097))
end
| FStar_Parser_AST.Attributes (uu____7098) -> begin
(

let uu____7101 = (p_term false false e)
in (soft_parens_with_nesting uu____7101))
end
| FStar_Parser_AST.Quote (uu____7102) -> begin
(

let uu____7107 = (p_term false false e)
in (soft_parens_with_nesting uu____7107))
end
| FStar_Parser_AST.VQuote (uu____7108) -> begin
(

let uu____7109 = (p_term false false e)
in (soft_parens_with_nesting uu____7109))
end
| FStar_Parser_AST.Antiquote (uu____7110) -> begin
(

let uu____7115 = (p_term false false e)
in (soft_parens_with_nesting uu____7115))
end))
and p_constant : FStar_Const.sconst  ->  FStar_Pprint.document = (fun uu___72_7116 -> (match (uu___72_7116) with
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

let uu____7120 = (FStar_Pprint.doc_of_char x)
in (FStar_Pprint.squotes uu____7120))
end
| FStar_Const.Const_string (s, uu____7122) -> begin
(

let uu____7123 = (str s)
in (FStar_Pprint.dquotes uu____7123))
end
| FStar_Const.Const_bytearray (bytes, uu____7125) -> begin
(

let uu____7130 = (

let uu____7131 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes uu____7131))
in (

let uu____7132 = (str "B")
in (FStar_Pprint.op_Hat_Hat uu____7130 uu____7132)))
end
| FStar_Const.Const_int (repr, sign_width_opt) -> begin
(

let signedness = (fun uu___70_7152 -> (match (uu___70_7152) with
| FStar_Const.Unsigned -> begin
(str "u")
end
| FStar_Const.Signed -> begin
FStar_Pprint.empty
end))
in (

let width = (fun uu___71_7158 -> (match (uu___71_7158) with
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

let ending = (default_or_map FStar_Pprint.empty (fun uu____7169 -> (match (uu____7169) with
| (s, w) -> begin
(

let uu____7176 = (signedness s)
in (

let uu____7177 = (width w)
in (FStar_Pprint.op_Hat_Hat uu____7176 uu____7177)))
end)) sign_width_opt)
in (

let uu____7178 = (str repr)
in (FStar_Pprint.op_Hat_Hat uu____7178 ending)))))
end
| FStar_Const.Const_range_of -> begin
(str "range_of")
end
| FStar_Const.Const_set_range_of -> begin
(str "set_range_of")
end
| FStar_Const.Const_range (r) -> begin
(

let uu____7180 = (FStar_Range.string_of_range r)
in (str uu____7180))
end
| FStar_Const.Const_reify -> begin
(str "reify")
end
| FStar_Const.Const_reflect (lid) -> begin
(

let uu____7182 = (p_quident lid)
in (

let uu____7183 = (

let uu____7184 = (

let uu____7185 = (str "reflect")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7185))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____7184))
in (FStar_Pprint.op_Hat_Hat uu____7182 uu____7183)))
end))
and p_universe : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (

let uu____7187 = (str "u#")
in (

let uu____7188 = (p_atomicUniverse u)
in (FStar_Pprint.op_Hat_Hat uu____7187 uu____7188))))
and p_universeFrom : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match (u.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____7190}, (u1)::(u2)::[]) -> begin
(

let uu____7195 = (

let uu____7196 = (p_universeFrom u1)
in (

let uu____7197 = (

let uu____7198 = (p_universeFrom u2)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____7198))
in (FStar_Pprint.op_Hat_Slash_Hat uu____7196 uu____7197)))
in (FStar_Pprint.group uu____7195))
end
| FStar_Parser_AST.App (uu____7199) -> begin
(

let uu____7206 = (head_and_args u)
in (match (uu____7206) with
| (head1, args) -> begin
(match (head1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (maybe_max_lid) when (FStar_Ident.lid_equals maybe_max_lid FStar_Parser_Const.max_lid) -> begin
(

let uu____7232 = (

let uu____7233 = (p_qlident FStar_Parser_Const.max_lid)
in (

let uu____7234 = (FStar_Pprint.separate_map FStar_Pprint.space (fun uu____7242 -> (match (uu____7242) with
| (u1, uu____7248) -> begin
(p_atomicUniverse u1)
end)) args)
in (op_Hat_Slash_Plus_Hat uu____7233 uu____7234)))
in (FStar_Pprint.group uu____7232))
end
| uu____7249 -> begin
(

let uu____7250 = (

let uu____7251 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" uu____7251))
in (failwith uu____7250))
end)
end))
end
| uu____7252 -> begin
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

let uu____7275 = (FStar_Ident.text_of_id id1)
in (str uu____7275))
end
| FStar_Parser_AST.Paren (u1) -> begin
(

let uu____7277 = (p_universeFrom u1)
in (soft_parens_with_nesting uu____7277))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____7278}, (uu____7279)::(uu____7280)::[]) -> begin
(

let uu____7283 = (p_universeFrom u)
in (soft_parens_with_nesting uu____7283))
end
| FStar_Parser_AST.App (uu____7284) -> begin
(

let uu____7291 = (p_universeFrom u)
in (soft_parens_with_nesting uu____7291))
end
| uu____7292 -> begin
(

let uu____7293 = (

let uu____7294 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" uu____7294))
in (failwith uu____7293))
end))


let term_to_document : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_term false false e))


let signature_to_document : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun e -> (p_justSig e))


let decl_to_document : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun e -> (p_decl e))


let pat_to_document : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (p_disjunctivePattern p))


let binder_to_document : FStar_Parser_AST.binder  ->  FStar_Pprint.document = (fun b -> (p_binder true b))


let modul_to_document : FStar_Parser_AST.modul  ->  FStar_Pprint.document = (fun m -> ((FStar_ST.op_Colon_Equals should_print_fs_typ_app false);
(

let res = (match (m) with
| FStar_Parser_AST.Module (uu____7356, decls) -> begin
(

let uu____7362 = (FStar_All.pipe_right decls (FStar_List.map decl_to_document))
in (FStar_All.pipe_right uu____7362 (FStar_Pprint.separate FStar_Pprint.hardline)))
end
| FStar_Parser_AST.Interface (uu____7371, decls, uu____7373) -> begin
(

let uu____7378 = (FStar_All.pipe_right decls (FStar_List.map decl_to_document))
in (FStar_All.pipe_right uu____7378 (FStar_Pprint.separate FStar_Pprint.hardline)))
end)
in ((FStar_ST.op_Colon_Equals should_print_fs_typ_app false);
res;
));
))


let comments_to_document : (Prims.string * FStar_Range.range) Prims.list  ->  FStar_Pprint.document = (fun comments -> (FStar_Pprint.separate_map FStar_Pprint.hardline (fun uu____7441 -> (match (uu____7441) with
| (comment, range) -> begin
(str comment)
end)) comments))


let modul_with_comments_to_document : FStar_Parser_AST.modul  ->  (Prims.string * FStar_Range.range) Prims.list  ->  (FStar_Pprint.document * (Prims.string * FStar_Range.range) Prims.list) = (fun m comments -> (

let decls = (match (m) with
| FStar_Parser_AST.Module (uu____7485, decls) -> begin
decls
end
| FStar_Parser_AST.Interface (uu____7491, decls, uu____7493) -> begin
decls
end)
in ((FStar_ST.op_Colon_Equals should_print_fs_typ_app false);
(match (decls) with
| [] -> begin
((FStar_Pprint.empty), (comments))
end
| (d)::ds -> begin
(

let uu____7548 = (match (ds) with
| ({FStar_Parser_AST.d = FStar_Parser_AST.Pragma (FStar_Parser_AST.LightOff); FStar_Parser_AST.drange = uu____7561; FStar_Parser_AST.doc = uu____7562; FStar_Parser_AST.quals = uu____7563; FStar_Parser_AST.attrs = uu____7564})::uu____7565 -> begin
(

let d0 = (FStar_List.hd ds)
in (

let uu____7571 = (

let uu____7574 = (

let uu____7577 = (FStar_List.tl ds)
in (d)::uu____7577)
in (d0)::uu____7574)
in ((uu____7571), (d0.FStar_Parser_AST.drange))))
end
| uu____7582 -> begin
(((d)::ds), (d.FStar_Parser_AST.drange))
end)
in (match (uu____7548) with
| (decls1, first_range) -> begin
(

let extract_decl_range = (fun d1 -> d1.FStar_Parser_AST.drange)
in ((FStar_ST.op_Colon_Equals comment_stack comments);
(

let initial_comment = (

let uu____7652 = (FStar_Range.start_of_range first_range)
in (place_comments_until_pos (Prims.parse_int "0") (Prims.parse_int "1") uu____7652 FStar_Pprint.empty))
in (

let doc1 = (separate_map_with_comments FStar_Pprint.empty FStar_Pprint.empty decl_to_document decls1 extract_decl_range)
in (

let comments1 = (FStar_ST.op_Bang comment_stack)
in ((FStar_ST.op_Colon_Equals comment_stack []);
(FStar_ST.op_Colon_Equals should_print_fs_typ_app false);
(

let uu____7778 = (FStar_Pprint.op_Hat_Hat initial_comment doc1)
in ((uu____7778), (comments1)));
))));
))
end))
end);
)))




