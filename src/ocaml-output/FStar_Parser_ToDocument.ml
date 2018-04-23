
open Prims
open FStar_Pervasives

let should_print_fs_typ_app : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let with_fs_typ_app : 'Auu____24 'Auu____25 . Prims.bool  ->  ('Auu____24  ->  'Auu____25)  ->  'Auu____24  ->  'Auu____25 = (fun b printer t -> (

let b0 = (FStar_ST.op_Bang should_print_fs_typ_app)
in ((FStar_ST.op_Colon_Equals should_print_fs_typ_app b);
(

let res = (printer t)
in ((FStar_ST.op_Colon_Equals should_print_fs_typ_app b0);
res;
));
)))


let str : Prims.string  ->  FStar_Pprint.document = (fun s -> (FStar_Pprint.doc_of_string s))


let default_or_map : 'Auu____134 'Auu____135 . 'Auu____134  ->  ('Auu____135  ->  'Auu____134)  ->  'Auu____135 FStar_Pervasives_Native.option  ->  'Auu____134 = (fun n1 f x -> (match (x) with
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


let separate_break_map : 'Auu____218 . FStar_Pprint.document  ->  ('Auu____218  ->  FStar_Pprint.document)  ->  'Auu____218 Prims.list  ->  FStar_Pprint.document = (fun sep f l -> (

let uu____243 = (

let uu____244 = (

let uu____245 = (FStar_Pprint.op_Hat_Hat sep break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____245))
in (FStar_Pprint.separate_map uu____244 f l))
in (FStar_Pprint.group uu____243)))


let precede_break_separate_map : 'Auu____256 . FStar_Pprint.document  ->  FStar_Pprint.document  ->  ('Auu____256  ->  FStar_Pprint.document)  ->  'Auu____256 Prims.list  ->  FStar_Pprint.document = (fun prec sep f l -> (

let uu____286 = (

let uu____287 = (FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space)
in (

let uu____288 = (

let uu____289 = (FStar_List.hd l)
in (FStar_All.pipe_right uu____289 f))
in (FStar_Pprint.precede uu____287 uu____288)))
in (

let uu____290 = (

let uu____291 = (FStar_List.tl l)
in (FStar_Pprint.concat_map (fun x -> (

let uu____297 = (

let uu____298 = (

let uu____299 = (f x)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____299))
in (FStar_Pprint.op_Hat_Hat sep uu____298))
in (FStar_Pprint.op_Hat_Hat break1 uu____297))) uu____291))
in (FStar_Pprint.op_Hat_Hat uu____286 uu____290))))


let concat_break_map : 'Auu____306 . ('Auu____306  ->  FStar_Pprint.document)  ->  'Auu____306 Prims.list  ->  FStar_Pprint.document = (fun f l -> (

let uu____326 = (FStar_Pprint.concat_map (fun x -> (

let uu____330 = (f x)
in (FStar_Pprint.op_Hat_Hat uu____330 break1))) l)
in (FStar_Pprint.group uu____326)))


let parens_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lparen contents FStar_Pprint.rparen))


let soft_parens_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lparen contents FStar_Pprint.rparen))


let braces_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbrace contents FStar_Pprint.rbrace))


let soft_braces_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbrace contents FStar_Pprint.rbrace))


let brackets_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbracket contents FStar_Pprint.rbracket))


let soft_brackets_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbracket contents FStar_Pprint.rbracket))


let soft_begin_end_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (

let uu____366 = (str "begin")
in (

let uu____367 = (str "end")
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") uu____366 contents uu____367))))


let separate_map_last : 'Auu____376 . FStar_Pprint.document  ->  (Prims.bool  ->  'Auu____376  ->  FStar_Pprint.document)  ->  'Auu____376 Prims.list  ->  FStar_Pprint.document = (fun sep f es -> (

let l = (FStar_List.length es)
in (

let es1 = (FStar_List.mapi (fun i e -> (f (Prims.op_disEquality i (l - (Prims.parse_int "1"))) e)) es)
in (FStar_Pprint.separate sep es1))))


let separate_break_map_last : 'Auu____428 . FStar_Pprint.document  ->  (Prims.bool  ->  'Auu____428  ->  FStar_Pprint.document)  ->  'Auu____428 Prims.list  ->  FStar_Pprint.document = (fun sep f l -> (

let uu____458 = (

let uu____459 = (

let uu____460 = (FStar_Pprint.op_Hat_Hat sep break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____460))
in (separate_map_last uu____459 f l))
in (FStar_Pprint.group uu____458)))


let separate_map_or_flow : 'Auu____469 . FStar_Pprint.document  ->  ('Auu____469  ->  FStar_Pprint.document)  ->  'Auu____469 Prims.list  ->  FStar_Pprint.document = (fun sep f l -> (match (((FStar_List.length l) < (Prims.parse_int "10"))) with
| true -> begin
(FStar_Pprint.separate_map sep f l)
end
| uu____494 -> begin
(FStar_Pprint.flow_map sep f l)
end))


let flow_map_last : 'Auu____503 . FStar_Pprint.document  ->  (Prims.bool  ->  'Auu____503  ->  FStar_Pprint.document)  ->  'Auu____503 Prims.list  ->  FStar_Pprint.document = (fun sep f es -> (

let l = (FStar_List.length es)
in (

let es1 = (FStar_List.mapi (fun i e -> (f (Prims.op_disEquality i (l - (Prims.parse_int "1"))) e)) es)
in (FStar_Pprint.flow sep es1))))


let separate_map_or_flow_last : 'Auu____555 . FStar_Pprint.document  ->  (Prims.bool  ->  'Auu____555  ->  FStar_Pprint.document)  ->  'Auu____555 Prims.list  ->  FStar_Pprint.document = (fun sep f l -> (match (((FStar_List.length l) < (Prims.parse_int "10"))) with
| true -> begin
(separate_map_last sep f l)
end
| uu____585 -> begin
(flow_map_last sep f l)
end))


let soft_surround_separate_map : 'Auu____604 . Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  ('Auu____604  ->  FStar_Pprint.document)  ->  'Auu____604 Prims.list  ->  FStar_Pprint.document = (fun n1 b void_ opening sep closing f xs -> (match ((Prims.op_Equality xs [])) with
| true -> begin
void_
end
| uu____656 -> begin
(

let uu____657 = (FStar_Pprint.separate_map sep f xs)
in (FStar_Pprint.soft_surround n1 b opening uu____657 closing))
end))


let soft_surround_map_or_flow : 'Auu____676 . Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  ('Auu____676  ->  FStar_Pprint.document)  ->  'Auu____676 Prims.list  ->  FStar_Pprint.document = (fun n1 b void_ opening sep closing f xs -> (match ((Prims.op_Equality xs [])) with
| true -> begin
void_
end
| uu____728 -> begin
(

let uu____729 = (separate_map_or_flow sep f xs)
in (FStar_Pprint.soft_surround n1 b opening uu____729 closing))
end))


let doc_of_fsdoc : (Prims.string * (Prims.string * Prims.string) Prims.list)  ->  FStar_Pprint.document = (fun uu____744 -> (match (uu____744) with
| (comment, keywords) -> begin
(

let uu____769 = (

let uu____770 = (

let uu____773 = (str comment)
in (

let uu____774 = (

let uu____777 = (

let uu____780 = (FStar_Pprint.separate_map FStar_Pprint.comma (fun uu____789 -> (match (uu____789) with
| (k, v1) -> begin
(

let uu____796 = (

let uu____799 = (str k)
in (

let uu____800 = (

let uu____803 = (

let uu____806 = (str v1)
in (uu____806)::[])
in (FStar_Pprint.rarrow)::uu____803)
in (uu____799)::uu____800))
in (FStar_Pprint.concat uu____796))
end)) keywords)
in (uu____780)::[])
in (FStar_Pprint.space)::uu____777)
in (uu____773)::uu____774))
in (FStar_Pprint.concat uu____770))
in (FStar_Pprint.group uu____769))
end))


let is_unit : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Const (FStar_Const.Const_unit) -> begin
true
end
| uu____812 -> begin
false
end))


let matches_var : FStar_Parser_AST.term  ->  FStar_Ident.ident  ->  Prims.bool = (fun t x -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (y) -> begin
(

let uu____824 = (FStar_Ident.text_of_lid y)
in (Prims.op_Equality x.FStar_Ident.idText uu____824))
end
| uu____825 -> begin
false
end))


let is_tuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Parser_Const.is_tuple_data_lid'


let is_dtuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Parser_Const.is_dtuple_data_lid'


let is_list_structure : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun cons_lid1 nil_lid1 -> (

let rec aux = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (lid, []) -> begin
(FStar_Ident.lid_equals lid nil_lid1)
end
| FStar_Parser_AST.Construct (lid, (uu____867)::((e2, uu____869))::[]) -> begin
((FStar_Ident.lid_equals lid cons_lid1) && (aux e2))
end
| uu____892 -> begin
false
end))
in aux))


let is_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Parser_Const.cons_lid FStar_Parser_Const.nil_lid)


let is_lex_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Parser_Const.lexcons_lid FStar_Parser_Const.lextop_lid)


let rec extract_from_list : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (uu____910, []) -> begin
[]
end
| FStar_Parser_AST.Construct (uu____921, ((e1, FStar_Parser_AST.Nothing))::((e2, FStar_Parser_AST.Nothing))::[]) -> begin
(

let uu____942 = (extract_from_list e2)
in (e1)::uu____942)
end
| uu____945 -> begin
(

let uu____946 = (

let uu____947 = (FStar_Parser_AST.term_to_string e)
in (FStar_Util.format1 "Not a list %s" uu____947))
in (failwith uu____946))
end))


let is_array : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (lid); FStar_Parser_AST.range = uu____956; FStar_Parser_AST.level = uu____957}, l, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) && (is_list l))
end
| uu____959 -> begin
false
end))


let rec is_ref_set : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (maybe_empty_lid) -> begin
(FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty)
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_singleton_lid); FStar_Parser_AST.range = uu____967; FStar_Parser_AST.level = uu____968}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_addr_of_lid); FStar_Parser_AST.range = uu____970; FStar_Parser_AST.level = uu____971}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____973; FStar_Parser_AST.level = uu____974}, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals maybe_singleton_lid FStar_Parser_Const.set_singleton) && (FStar_Ident.lid_equals maybe_addr_of_lid FStar_Parser_Const.heap_addr_of_lid))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_union_lid); FStar_Parser_AST.range = uu____976; FStar_Parser_AST.level = uu____977}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____979; FStar_Parser_AST.level = uu____980}, e2, FStar_Parser_AST.Nothing) -> begin
(((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union) && (is_ref_set e1)) && (is_ref_set e2))
end
| uu____982 -> begin
false
end))


let rec extract_from_ref_set : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (uu____992) -> begin
[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (uu____993); FStar_Parser_AST.range = uu____994; FStar_Parser_AST.level = uu____995}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (uu____996); FStar_Parser_AST.range = uu____997; FStar_Parser_AST.level = uu____998}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____1000; FStar_Parser_AST.level = uu____1001}, FStar_Parser_AST.Nothing) -> begin
(e1)::[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (uu____1002); FStar_Parser_AST.range = uu____1003; FStar_Parser_AST.level = uu____1004}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____1006; FStar_Parser_AST.level = uu____1007}, e2, FStar_Parser_AST.Nothing) -> begin
(

let uu____1009 = (extract_from_ref_set e1)
in (

let uu____1012 = (extract_from_ref_set e2)
in (FStar_List.append uu____1009 uu____1012)))
end
| uu____1015 -> begin
(

let uu____1016 = (

let uu____1017 = (FStar_Parser_AST.term_to_string e)
in (FStar_Util.format1 "Not a ref set %s" uu____1017))
in (failwith uu____1016))
end))


let is_general_application : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____1025 = ((is_array e) || (is_ref_set e))
in (not (uu____1025))))


let is_general_construction : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____1031 = ((is_list e) || (is_lex_list e))
in (not (uu____1031))))


let is_general_prefix_op : FStar_Ident.ident  ->  Prims.bool = (fun op -> (

let op_starting_char = (

let uu____1038 = (FStar_Ident.text_of_id op)
in (FStar_Util.char_at uu____1038 (Prims.parse_int "0")))
in (((Prims.op_Equality op_starting_char 33 (*!*)) || (Prims.op_Equality op_starting_char 63 (*?*))) || ((Prims.op_Equality op_starting_char 126 (*~*)) && (

let uu____1043 = (FStar_Ident.text_of_id op)
in (Prims.op_disEquality uu____1043 "~"))))))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun e -> (

let rec aux = (fun e1 acc -> (match (e1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App (head1, arg, imp) -> begin
(aux head1 ((((arg), (imp)))::acc))
end
| uu____1109 -> begin
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
| uu____1125 -> begin
false
end))


let uu___is_Right : associativity  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Right -> begin
true
end
| uu____1131 -> begin
false
end))


let uu___is_NonAssoc : associativity  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NonAssoc -> begin
true
end
| uu____1137 -> begin
false
end))


type token =
(FStar_Char.char, Prims.string) FStar_Util.either


type associativity_level =
(associativity * token Prims.list)


let token_to_string : (FStar_BaseTypes.char, Prims.string) FStar_Util.either  ->  Prims.string = (fun uu___54_1157 -> (match (uu___54_1157) with
| FStar_Util.Inl (c) -> begin
(Prims.strcat (FStar_Util.string_of_char c) ".*")
end
| FStar_Util.Inr (s) -> begin
s
end))


let matches_token : Prims.string  ->  (FStar_Char.char, Prims.string) FStar_Util.either  ->  Prims.bool = (fun s uu___55_1178 -> (match (uu___55_1178) with
| FStar_Util.Inl (c) -> begin
(

let uu____1187 = (FStar_String.get s (Prims.parse_int "0"))
in (Prims.op_Equality uu____1187 c))
end
| FStar_Util.Inr (s') -> begin
(Prims.op_Equality s s')
end))


let matches_level : 'Auu____1198 . Prims.string  ->  ('Auu____1198 * (FStar_Char.char, Prims.string) FStar_Util.either Prims.list)  ->  Prims.bool = (fun s uu____1219 -> (match (uu____1219) with
| (assoc_levels, tokens) -> begin
(

let uu____1247 = (FStar_List.tryFind (matches_token s) tokens)
in (Prims.op_disEquality uu____1247 FStar_Pervasives_Native.None))
end))


let opinfix4 : (associativity * token Prims.list) = ((Right), ((FStar_Util.Inr ("**"))::[]))


let opinfix3 : (associativity * token Prims.list) = ((Left), ((FStar_Util.Inl (42 (***)))::(FStar_Util.Inl (47 (*/*)))::(FStar_Util.Inl (37 (*%*)))::[]))


let opinfix2 : (associativity * token Prims.list) = ((Left), ((FStar_Util.Inl (43 (*+*)))::(FStar_Util.Inl (45 (*-*)))::[]))


let minus_lvl : (associativity * token Prims.list) = ((Left), ((FStar_Util.Inr ("-"))::[]))


let opinfix1 : (associativity * token Prims.list) = ((Right), ((FStar_Util.Inl (64 (*@*)))::(FStar_Util.Inl (94 (*^*)))::[]))


let pipe_right : (associativity * token Prims.list) = ((Left), ((FStar_Util.Inr ("|>"))::[]))


let opinfix0d : (associativity * token Prims.list) = ((Left), ((FStar_Util.Inl (36 (*$*)))::[]))


let opinfix0c : (associativity * token Prims.list) = ((Left), ((FStar_Util.Inl (61 (*=*)))::(FStar_Util.Inl (60 (*<*)))::(FStar_Util.Inl (62 (*>*)))::[]))


let equal : (associativity * token Prims.list) = ((Left), ((FStar_Util.Inr ("="))::[]))


let opinfix0b : (associativity * token Prims.list) = ((Left), ((FStar_Util.Inl (38 (*&*)))::[]))


let opinfix0a : (associativity * token Prims.list) = ((Left), ((FStar_Util.Inl (124 (*|*)))::[]))


let colon_equals : (associativity * token Prims.list) = ((NonAssoc), ((FStar_Util.Inr (":="))::[]))


let amp : (associativity * token Prims.list) = ((Right), ((FStar_Util.Inr ("&"))::[]))


let colon_colon : (associativity * token Prims.list) = ((Right), ((FStar_Util.Inr ("::"))::[]))


let level_associativity_spec : associativity_level Prims.list = (opinfix4)::(opinfix3)::(opinfix2)::(opinfix1)::(pipe_right)::(opinfix0d)::(opinfix0c)::(opinfix0b)::(opinfix0a)::(colon_equals)::(amp)::(colon_colon)::[]


let level_table : ((Prims.int * Prims.int * Prims.int) * token Prims.list) Prims.list = (

let levels_from_associativity = (fun l uu___56_1449 -> (match (uu___56_1449) with
| Left -> begin
((l), (l), ((l - (Prims.parse_int "1"))))
end
| Right -> begin
(((l - (Prims.parse_int "1"))), (l), (l))
end
| NonAssoc -> begin
(((l - (Prims.parse_int "1"))), (l), ((l - (Prims.parse_int "1"))))
end))
in (FStar_List.mapi (fun i uu____1479 -> (match (uu____1479) with
| (assoc1, tokens) -> begin
(((levels_from_associativity i assoc1)), (tokens))
end)) level_associativity_spec))


let assign_levels : associativity_level Prims.list  ->  Prims.string  ->  (Prims.int * Prims.int * Prims.int) = (fun token_associativity_spec s -> (

let uu____1538 = (FStar_List.tryFind (matches_level s) level_table)
in (match (uu____1538) with
| FStar_Pervasives_Native.Some (assoc_levels, uu____1578) -> begin
assoc_levels
end
| uu____1607 -> begin
(failwith (Prims.strcat "Unrecognized operator " s))
end)))


let max : Prims.int  ->  Prims.int  ->  Prims.int = (fun k1 k2 -> (match ((k1 > k2)) with
| true -> begin
k1
end
| uu____1638 -> begin
k2
end))


let max_level : 'Auu____1643 . ('Auu____1643 * token Prims.list) Prims.list  ->  Prims.int = (fun l -> (

let find_level_and_max = (fun n1 level -> (

let uu____1688 = (FStar_List.tryFind (fun uu____1718 -> (match (uu____1718) with
| (uu____1731, tokens) -> begin
(Prims.op_Equality tokens (FStar_Pervasives_Native.snd level))
end)) level_table)
in (match (uu____1688) with
| FStar_Pervasives_Native.Some ((uu____1753, l1, uu____1755), uu____1756) -> begin
(max n1 l1)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____1791 = (

let uu____1792 = (

let uu____1793 = (FStar_List.map token_to_string (FStar_Pervasives_Native.snd level))
in (FStar_String.concat "," uu____1793))
in (FStar_Util.format1 "Undefined associativity level %s" uu____1792))
in (failwith uu____1791))
end)))
in (FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l)))


let levels : Prims.string  ->  (Prims.int * Prims.int * Prims.int) = (fun op -> (

let uu____1815 = (assign_levels level_associativity_spec op)
in (match (uu____1815) with
| (left1, mine, right1) -> begin
(match ((Prims.op_Equality op "*")) with
| true -> begin
(((left1 - (Prims.parse_int "1"))), (mine), (right1))
end
| uu____1837 -> begin
((left1), (mine), (right1))
end)
end)))


let operatorInfix0ad12 : (associativity * token Prims.list) Prims.list = (opinfix0a)::(opinfix0b)::(opinfix0c)::(opinfix0d)::(opinfix1)::(opinfix2)::[]


let is_operatorInfix0ad12 : FStar_Ident.ident  ->  Prims.bool = (fun op -> (

let uu____1893 = (

let uu____1902 = (

let uu____1913 = (FStar_Ident.text_of_id op)
in (FStar_All.pipe_left matches_level uu____1913))
in (FStar_List.tryFind uu____1902 operatorInfix0ad12))
in (Prims.op_disEquality uu____1893 FStar_Pervasives_Native.None)))


let is_operatorInfix34 : FStar_Ident.ident  ->  Prims.bool = (

let opinfix34 = (opinfix3)::(opinfix4)::[]
in (fun op -> (

let uu____1995 = (

let uu____2009 = (

let uu____2025 = (FStar_Ident.text_of_id op)
in (FStar_All.pipe_left matches_level uu____2025))
in (FStar_List.tryFind uu____2009 opinfix34))
in (Prims.op_disEquality uu____1995 FStar_Pervasives_Native.None))))


let handleable_args_length : FStar_Ident.ident  ->  Prims.int = (fun op -> (

let op_s = (FStar_Ident.text_of_id op)
in (

let uu____2081 = ((is_general_prefix_op op) || (FStar_List.mem op_s (("-")::("~")::[])))
in (match (uu____2081) with
| true -> begin
(Prims.parse_int "1")
end
| uu____2082 -> begin
(

let uu____2083 = (((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) || (FStar_List.mem op_s (("<==>")::("==>")::("\\/")::("/\\")::("=")::("|>")::(":=")::(".()")::(".[]")::[])))
in (match (uu____2083) with
| true -> begin
(Prims.parse_int "2")
end
| uu____2084 -> begin
(match ((FStar_List.mem op_s ((".()<-")::(".[]<-")::[]))) with
| true -> begin
(Prims.parse_int "3")
end
| uu____2085 -> begin
(Prims.parse_int "0")
end)
end))
end))))


let handleable_op : 'Auu____2092 . FStar_Ident.ident  ->  'Auu____2092 Prims.list  ->  Prims.bool = (fun op args -> (match ((FStar_List.length args)) with
| _0_4 when (_0_4 = (Prims.parse_int "0")) -> begin
true
end
| _0_5 when (_0_5 = (Prims.parse_int "1")) -> begin
((is_general_prefix_op op) || (

let uu____2108 = (FStar_Ident.text_of_id op)
in (FStar_List.mem uu____2108 (("-")::("~")::[]))))
end
| _0_6 when (_0_6 = (Prims.parse_int "2")) -> begin
(((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) || (

let uu____2110 = (FStar_Ident.text_of_id op)
in (FStar_List.mem uu____2110 (("<==>")::("==>")::("\\/")::("/\\")::("=")::("|>")::(":=")::(".()")::(".[]")::[]))))
end
| _0_7 when (_0_7 = (Prims.parse_int "3")) -> begin
(

let uu____2111 = (FStar_Ident.text_of_id op)
in (FStar_List.mem uu____2111 ((".()<-")::(".[]<-")::[])))
end
| uu____2112 -> begin
false
end))


let comment_stack : (Prims.string * FStar_Range.range) Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let with_comment : 'Auu____2150 . ('Auu____2150  ->  FStar_Pprint.document)  ->  'Auu____2150  ->  FStar_Range.range  ->  FStar_Pprint.document = (fun printer tm tmrange -> (

let rec comments_before_pos = (fun acc print_pos lookahead_pos -> (

let uu____2191 = (FStar_ST.op_Bang comment_stack)
in (match (uu____2191) with
| [] -> begin
((acc), (false))
end
| ((comment, crange))::cs -> begin
(

let uu____2254 = (FStar_Range.range_before_pos crange print_pos)
in (match (uu____2254) with
| true -> begin
((FStar_ST.op_Colon_Equals comment_stack cs);
(

let uu____2295 = (

let uu____2296 = (

let uu____2297 = (str comment)
in (FStar_Pprint.op_Hat_Hat uu____2297 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat acc uu____2296))
in (comments_before_pos uu____2295 print_pos lookahead_pos));
)
end
| uu____2298 -> begin
(

let uu____2299 = (FStar_Range.range_before_pos crange lookahead_pos)
in ((acc), (uu____2299)))
end))
end)))
in (

let uu____2300 = (

let uu____2305 = (

let uu____2306 = (FStar_Range.start_of_range tmrange)
in (FStar_Range.end_of_line uu____2306))
in (

let uu____2307 = (FStar_Range.end_of_range tmrange)
in (comments_before_pos FStar_Pprint.empty uu____2305 uu____2307)))
in (match (uu____2300) with
| (comments, has_lookahead) -> begin
(

let printed_e = (printer tm)
in (

let comments1 = (match (has_lookahead) with
| true -> begin
(

let pos = (FStar_Range.end_of_range tmrange)
in (

let uu____2313 = (comments_before_pos comments pos pos)
in (FStar_Pervasives_Native.fst uu____2313)))
end
| uu____2318 -> begin
comments
end)
in (

let uu____2319 = (FStar_Pprint.op_Hat_Hat comments1 printed_e)
in (FStar_Pprint.group uu____2319))))
end))))


let rec place_comments_until_pos : Prims.int  ->  Prims.int  ->  FStar_Range.pos  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun k lbegin pos_end doc1 -> (

let uu____2340 = (FStar_ST.op_Bang comment_stack)
in (match (uu____2340) with
| ((comment, crange))::cs when (FStar_Range.range_before_pos crange pos_end) -> begin
((FStar_ST.op_Colon_Equals comment_stack cs);
(

let lnum = (

let uu____2432 = (

let uu____2433 = (

let uu____2434 = (FStar_Range.start_of_range crange)
in (FStar_Range.line_of_pos uu____2434))
in (uu____2433 - lbegin))
in (max k uu____2432))
in (

let doc2 = (

let uu____2436 = (

let uu____2437 = (FStar_Pprint.repeat lnum FStar_Pprint.hardline)
in (

let uu____2438 = (str comment)
in (FStar_Pprint.op_Hat_Hat uu____2437 uu____2438)))
in (FStar_Pprint.op_Hat_Hat doc1 uu____2436))
in (

let uu____2439 = (

let uu____2440 = (FStar_Range.end_of_range crange)
in (FStar_Range.line_of_pos uu____2440))
in (place_comments_until_pos (Prims.parse_int "1") uu____2439 pos_end doc2))));
)
end
| uu____2441 -> begin
(

let lnum = (

let uu____2449 = (

let uu____2450 = (FStar_Range.line_of_pos pos_end)
in (uu____2450 - lbegin))
in (max (Prims.parse_int "1") uu____2449))
in (

let uu____2451 = (FStar_Pprint.repeat lnum FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat doc1 uu____2451)))
end)))


let separate_map_with_comments : 'Auu____2464 . FStar_Pprint.document  ->  FStar_Pprint.document  ->  ('Auu____2464  ->  FStar_Pprint.document)  ->  'Auu____2464 Prims.list  ->  ('Auu____2464  ->  FStar_Range.range)  ->  FStar_Pprint.document = (fun prefix1 sep f xs extract_range -> (

let fold_fun = (fun uu____2521 x -> (match (uu____2521) with
| (last_line, doc1) -> begin
(

let r = (extract_range x)
in (

let doc2 = (

let uu____2535 = (FStar_Range.start_of_range r)
in (place_comments_until_pos (Prims.parse_int "1") last_line uu____2535 doc1))
in (

let uu____2536 = (

let uu____2537 = (FStar_Range.end_of_range r)
in (FStar_Range.line_of_pos uu____2537))
in (

let uu____2538 = (

let uu____2539 = (

let uu____2540 = (f x)
in (FStar_Pprint.op_Hat_Hat sep uu____2540))
in (FStar_Pprint.op_Hat_Hat doc2 uu____2539))
in ((uu____2536), (uu____2538))))))
end))
in (

let uu____2541 = (

let uu____2548 = (FStar_List.hd xs)
in (

let uu____2549 = (FStar_List.tl xs)
in ((uu____2548), (uu____2549))))
in (match (uu____2541) with
| (x, xs1) -> begin
(

let init1 = (

let uu____2565 = (

let uu____2566 = (

let uu____2567 = (extract_range x)
in (FStar_Range.end_of_range uu____2567))
in (FStar_Range.line_of_pos uu____2566))
in (

let uu____2568 = (

let uu____2569 = (f x)
in (FStar_Pprint.op_Hat_Hat prefix1 uu____2569))
in ((uu____2565), (uu____2568))))
in (

let uu____2570 = (FStar_List.fold_left fold_fun init1 xs1)
in (FStar_Pervasives_Native.snd uu____2570)))
end))))


let rec p_decl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (

let uu____3199 = (

let uu____3200 = (FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc)
in (

let uu____3201 = (

let uu____3202 = (p_attributes d.FStar_Parser_AST.attrs)
in (

let uu____3203 = (

let uu____3204 = (p_qualifiers d.FStar_Parser_AST.quals)
in (

let uu____3205 = (

let uu____3206 = (p_rawDecl d)
in (FStar_Pprint.op_Hat_Hat (match ((Prims.op_Equality d.FStar_Parser_AST.quals [])) with
| true -> begin
FStar_Pprint.empty
end
| uu____3207 -> begin
break1
end) uu____3206))
in (FStar_Pprint.op_Hat_Hat uu____3204 uu____3205)))
in (FStar_Pprint.op_Hat_Hat uu____3202 uu____3203)))
in (FStar_Pprint.op_Hat_Hat uu____3200 uu____3201)))
in (FStar_Pprint.group uu____3199)))
and p_attributes : FStar_Parser_AST.attributes_  ->  FStar_Pprint.document = (fun attrs -> (

let uu____3209 = (

let uu____3210 = (str "@")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3210))
in (

let uu____3211 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline)
in (soft_surround_map_or_flow (Prims.parse_int "0") (Prims.parse_int "2") FStar_Pprint.empty uu____3209 FStar_Pprint.space uu____3211 p_atomicTerm attrs))))
and p_fsdoc : FStar_Parser_AST.fsdoc  ->  FStar_Pprint.document = (fun uu____3212 -> (match (uu____3212) with
| (doc1, kwd_args) -> begin
(

let kwd_args_doc = (match (kwd_args) with
| [] -> begin
FStar_Pprint.empty
end
| kwd_args1 -> begin
(

let process_kwd_arg = (fun uu____3248 -> (match (uu____3248) with
| (kwd, arg) -> begin
(

let uu____3255 = (str "@")
in (

let uu____3256 = (

let uu____3257 = (str kwd)
in (

let uu____3258 = (

let uu____3259 = (str arg)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3259))
in (FStar_Pprint.op_Hat_Hat uu____3257 uu____3258)))
in (FStar_Pprint.op_Hat_Hat uu____3255 uu____3256)))
end))
in (

let uu____3260 = (

let uu____3261 = (FStar_Pprint.separate_map FStar_Pprint.hardline process_kwd_arg kwd_args1)
in (FStar_Pprint.op_Hat_Hat uu____3261 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3260)))
end)
in (

let uu____3266 = (

let uu____3267 = (

let uu____3268 = (

let uu____3269 = (

let uu____3270 = (str doc1)
in (

let uu____3271 = (

let uu____3272 = (

let uu____3273 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3273))
in (FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3272))
in (FStar_Pprint.op_Hat_Hat uu____3270 uu____3271)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3269))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3268))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3267))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3266)))
end))
and p_justSig : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (lid, t) -> begin
(

let uu____3277 = (

let uu____3278 = (str "val")
in (

let uu____3279 = (

let uu____3280 = (

let uu____3281 = (p_lident lid)
in (

let uu____3282 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat uu____3281 uu____3282)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3280))
in (FStar_Pprint.op_Hat_Hat uu____3278 uu____3279)))
in (

let uu____3283 = (p_typ false false t)
in (op_Hat_Slash_Plus_Hat uu____3277 uu____3283)))
end
| FStar_Parser_AST.TopLevelLet (uu____3284, lbs) -> begin
(FStar_Pprint.separate_map FStar_Pprint.hardline (fun lb -> (

let uu____3309 = (

let uu____3310 = (str "let")
in (

let uu____3311 = (p_letlhs lb)
in (FStar_Pprint.op_Hat_Slash_Hat uu____3310 uu____3311)))
in (FStar_Pprint.group uu____3309))) lbs)
end
| uu____3312 -> begin
FStar_Pprint.empty
end))
and p_list : (FStar_Ident.ident  ->  FStar_Pprint.document)  ->  FStar_Pprint.document  ->  FStar_Ident.ident Prims.list  ->  FStar_Pprint.document = (fun f sep l -> (

let rec p_list' = (fun uu___57_3327 -> (match (uu___57_3327) with
| [] -> begin
FStar_Pprint.empty
end
| (x)::[] -> begin
(f x)
end
| (x)::xs -> begin
(

let uu____3335 = (f x)
in (

let uu____3336 = (

let uu____3337 = (p_list' xs)
in (FStar_Pprint.op_Hat_Hat sep uu____3337))
in (FStar_Pprint.op_Hat_Hat uu____3335 uu____3336)))
end))
in (

let uu____3338 = (str "[")
in (

let uu____3339 = (

let uu____3340 = (p_list' l)
in (

let uu____3341 = (str "]")
in (FStar_Pprint.op_Hat_Hat uu____3340 uu____3341)))
in (FStar_Pprint.op_Hat_Hat uu____3338 uu____3339)))))
and p_rawDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Open (uid) -> begin
(

let uu____3344 = (

let uu____3345 = (str "open")
in (

let uu____3346 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat uu____3345 uu____3346)))
in (FStar_Pprint.group uu____3344))
end
| FStar_Parser_AST.Include (uid) -> begin
(

let uu____3348 = (

let uu____3349 = (str "include")
in (

let uu____3350 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat uu____3349 uu____3350)))
in (FStar_Pprint.group uu____3348))
end
| FStar_Parser_AST.ModuleAbbrev (uid1, uid2) -> begin
(

let uu____3353 = (

let uu____3354 = (str "module")
in (

let uu____3355 = (

let uu____3356 = (

let uu____3357 = (p_uident uid1)
in (

let uu____3358 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____3357 uu____3358)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3356))
in (FStar_Pprint.op_Hat_Hat uu____3354 uu____3355)))
in (

let uu____3359 = (p_quident uid2)
in (op_Hat_Slash_Plus_Hat uu____3353 uu____3359)))
end
| FStar_Parser_AST.TopLevelModule (uid) -> begin
(

let uu____3361 = (

let uu____3362 = (str "module")
in (

let uu____3363 = (

let uu____3364 = (p_quident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3364))
in (FStar_Pprint.op_Hat_Hat uu____3362 uu____3363)))
in (FStar_Pprint.group uu____3361))
end
| FStar_Parser_AST.Tycon (true, ((FStar_Parser_AST.TyconAbbrev (uid, tpars, FStar_Pervasives_Native.None, t), FStar_Pervasives_Native.None))::[]) -> begin
(

let effect_prefix_doc = (

let uu____3397 = (str "effect")
in (

let uu____3398 = (

let uu____3399 = (p_uident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3399))
in (FStar_Pprint.op_Hat_Hat uu____3397 uu____3398)))
in (

let uu____3400 = (

let uu____3401 = (p_typars tpars)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") effect_prefix_doc uu____3401 FStar_Pprint.equals))
in (

let uu____3402 = (p_typ false false t)
in (op_Hat_Slash_Plus_Hat uu____3400 uu____3402))))
end
| FStar_Parser_AST.Tycon (false, tcdefs) -> begin
(

let uu____3420 = (str "type")
in (

let uu____3421 = (str "and")
in (precede_break_separate_map uu____3420 uu____3421 p_fsdocTypeDeclPairs tcdefs)))
end
| FStar_Parser_AST.TopLevelLet (q, lbs) -> begin
(

let let_doc = (

let uu____3443 = (str "let")
in (

let uu____3444 = (

let uu____3445 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat uu____3445 FStar_Pprint.space))
in (FStar_Pprint.op_Hat_Hat uu____3443 uu____3444)))
in (

let uu____3446 = (

let uu____3447 = (str "and")
in (FStar_Pprint.op_Hat_Hat uu____3447 FStar_Pprint.space))
in (separate_map_with_comments let_doc uu____3446 p_letbinding lbs (fun uu____3455 -> (match (uu____3455) with
| (p, t) -> begin
(FStar_Range.union_ranges p.FStar_Parser_AST.prange t.FStar_Parser_AST.range)
end)))))
end
| FStar_Parser_AST.Val (lid, t) -> begin
(

let uu____3464 = (

let uu____3465 = (str "val")
in (

let uu____3466 = (

let uu____3467 = (

let uu____3468 = (p_lident lid)
in (

let uu____3469 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat uu____3468 uu____3469)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3467))
in (FStar_Pprint.op_Hat_Hat uu____3465 uu____3466)))
in (

let uu____3470 = (p_typ false false t)
in (op_Hat_Slash_Plus_Hat uu____3464 uu____3470)))
end
| FStar_Parser_AST.Assume (id1, t) -> begin
(

let decl_keyword = (

let uu____3474 = (

let uu____3475 = (FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_All.pipe_right uu____3475 FStar_Util.is_upper))
in (match (uu____3474) with
| true -> begin
FStar_Pprint.empty
end
| uu____3476 -> begin
(

let uu____3477 = (str "val")
in (FStar_Pprint.op_Hat_Hat uu____3477 FStar_Pprint.space))
end))
in (

let uu____3478 = (

let uu____3479 = (

let uu____3480 = (p_ident id1)
in (

let uu____3481 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat uu____3480 uu____3481)))
in (FStar_Pprint.op_Hat_Hat decl_keyword uu____3479))
in (

let uu____3482 = (p_typ false false t)
in (op_Hat_Slash_Plus_Hat uu____3478 uu____3482))))
end
| FStar_Parser_AST.Exception (uid, t_opt) -> begin
(

let uu____3489 = (str "exception")
in (

let uu____3490 = (

let uu____3491 = (

let uu____3492 = (p_uident uid)
in (

let uu____3493 = (FStar_Pprint.optional (fun t -> (

let uu____3497 = (

let uu____3498 = (str "of")
in (

let uu____3499 = (p_typ false false t)
in (op_Hat_Slash_Plus_Hat uu____3498 uu____3499)))
in (FStar_Pprint.op_Hat_Hat break1 uu____3497))) t_opt)
in (FStar_Pprint.op_Hat_Hat uu____3492 uu____3493)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3491))
in (FStar_Pprint.op_Hat_Hat uu____3489 uu____3490)))
end
| FStar_Parser_AST.NewEffect (ne) -> begin
(

let uu____3501 = (str "new_effect")
in (

let uu____3502 = (

let uu____3503 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3503))
in (FStar_Pprint.op_Hat_Hat uu____3501 uu____3502)))
end
| FStar_Parser_AST.SubEffect (se) -> begin
(

let uu____3505 = (str "sub_effect")
in (

let uu____3506 = (

let uu____3507 = (p_subEffect se)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3507))
in (FStar_Pprint.op_Hat_Hat uu____3505 uu____3506)))
end
| FStar_Parser_AST.Pragma (p) -> begin
(p_pragma p)
end
| FStar_Parser_AST.Fsdoc (doc1) -> begin
(

let uu____3510 = (p_fsdoc doc1)
in (FStar_Pprint.op_Hat_Hat uu____3510 FStar_Pprint.hardline))
end
| FStar_Parser_AST.Main (uu____3511) -> begin
(failwith "*Main declaration* : Is that really still in use ??")
end
| FStar_Parser_AST.Tycon (true, uu____3512) -> begin
(failwith "Effect abbreviation is expected to be defined by an abbreviation")
end
| FStar_Parser_AST.Splice (ids, t) -> begin
(

let uu____3535 = (str "%splice")
in (

let uu____3536 = (

let uu____3537 = (

let uu____3538 = (str ";")
in (p_list p_uident uu____3538 ids))
in (

let uu____3539 = (

let uu____3540 = (p_term false false t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3540))
in (FStar_Pprint.op_Hat_Hat uu____3537 uu____3539)))
in (FStar_Pprint.op_Hat_Hat uu____3535 uu____3536)))
end))
and p_pragma : FStar_Parser_AST.pragma  ->  FStar_Pprint.document = (fun uu___58_3541 -> (match (uu___58_3541) with
| FStar_Parser_AST.SetOptions (s) -> begin
(

let uu____3543 = (str "#set-options")
in (

let uu____3544 = (

let uu____3545 = (

let uu____3546 = (str s)
in (FStar_Pprint.dquotes uu____3546))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3545))
in (FStar_Pprint.op_Hat_Hat uu____3543 uu____3544)))
end
| FStar_Parser_AST.ResetOptions (s_opt) -> begin
(

let uu____3550 = (str "#reset-options")
in (

let uu____3551 = (FStar_Pprint.optional (fun s -> (

let uu____3555 = (

let uu____3556 = (str s)
in (FStar_Pprint.dquotes uu____3556))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3555))) s_opt)
in (FStar_Pprint.op_Hat_Hat uu____3550 uu____3551)))
end
| FStar_Parser_AST.LightOff -> begin
((FStar_ST.op_Colon_Equals should_print_fs_typ_app true);
(str "#light \"off\"");
)
end))
and p_typars : FStar_Parser_AST.binder Prims.list  ->  FStar_Pprint.document = (fun bs -> (p_binders true bs))
and p_fsdocTypeDeclPairs : (FStar_Parser_AST.tycon * FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option)  ->  FStar_Pprint.document = (fun uu____3584 -> (match (uu____3584) with
| (typedecl, fsdoc_opt) -> begin
(

let uu____3597 = (FStar_Pprint.optional p_fsdoc fsdoc_opt)
in (

let uu____3598 = (p_typeDecl typedecl)
in (FStar_Pprint.op_Hat_Hat uu____3597 uu____3598)))
end))
and p_typeDecl : FStar_Parser_AST.tycon  ->  FStar_Pprint.document = (fun uu___59_3599 -> (match (uu___59_3599) with
| FStar_Parser_AST.TyconAbstract (lid, bs, typ_opt) -> begin
(

let empty' = (fun uu____3616 -> FStar_Pprint.empty)
in (p_typeDeclPrefix lid bs typ_opt empty'))
end
| FStar_Parser_AST.TyconAbbrev (lid, bs, typ_opt, t) -> begin
(

let f = (fun uu____3634 -> (

let uu____3635 = (p_typ false false t)
in (prefix2 FStar_Pprint.equals uu____3635)))
in (p_typeDeclPrefix lid bs typ_opt f))
end
| FStar_Parser_AST.TyconRecord (lid, bs, typ_opt, record_field_decls) -> begin
(

let p_recordFieldAndComments = (fun ps uu____3686 -> (match (uu____3686) with
| (lid1, t, doc_opt) -> begin
(

let uu____3702 = (FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range)
in (with_comment (p_recordFieldDecl ps) ((lid1), (t), (doc_opt)) uu____3702))
end))
in (

let p_fields = (fun uu____3718 -> (

let uu____3719 = (

let uu____3720 = (

let uu____3721 = (

let uu____3722 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (separate_map_last uu____3722 p_recordFieldAndComments record_field_decls))
in (braces_with_nesting uu____3721))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3720))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____3719)))
in (p_typeDeclPrefix lid bs typ_opt p_fields)))
end
| FStar_Parser_AST.TyconVariant (lid, bs, typ_opt, ct_decls) -> begin
(

let p_constructorBranchAndComments = (fun uu____3788 -> (match (uu____3788) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let range = (

let uu____3814 = (

let uu____3815 = (FStar_Util.map_opt t_opt (fun t -> t.FStar_Parser_AST.range))
in (FStar_Util.dflt uid.FStar_Ident.idRange uu____3815))
in (FStar_Range.extend_to_end_of_line uu____3814))
in (

let p_constructorBranch = (fun decl -> (

let uu____3850 = (

let uu____3851 = (

let uu____3852 = (p_constructorDecl decl)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3852))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____3851))
in (FStar_Pprint.group uu____3850)))
in (with_comment p_constructorBranch ((uid), (t_opt), (doc_opt), (use_of)) range)))
end))
in (

let datacon_doc = (fun uu____3874 -> (

let uu____3875 = (FStar_Pprint.separate_map break1 p_constructorBranchAndComments ct_decls)
in (FStar_Pprint.group uu____3875)))
in (p_typeDeclPrefix lid bs typ_opt (fun uu____3890 -> (

let uu____3891 = (datacon_doc ())
in (prefix2 FStar_Pprint.equals uu____3891))))))
end))
and p_typeDeclPrefix : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.knd FStar_Pervasives_Native.option  ->  (unit  ->  FStar_Pprint.document)  ->  FStar_Pprint.document = (fun lid bs typ_opt cont -> (match (((Prims.op_Equality bs []) && (Prims.op_Equality typ_opt FStar_Pervasives_Native.None))) with
| true -> begin
(

let uu____3906 = (p_ident lid)
in (

let uu____3907 = (

let uu____3908 = (cont ())
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3908))
in (FStar_Pprint.op_Hat_Hat uu____3906 uu____3907)))
end
| uu____3909 -> begin
(

let binders_doc = (

let uu____3911 = (p_typars bs)
in (

let uu____3912 = (FStar_Pprint.optional (fun t -> (

let uu____3916 = (

let uu____3917 = (

let uu____3918 = (p_typ false false t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3918))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3917))
in (FStar_Pprint.op_Hat_Hat break1 uu____3916))) typ_opt)
in (FStar_Pprint.op_Hat_Hat uu____3911 uu____3912)))
in (

let uu____3919 = (p_ident lid)
in (

let uu____3920 = (cont ())
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____3919 binders_doc uu____3920))))
end))
and p_recordFieldDecl : Prims.bool  ->  (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option)  ->  FStar_Pprint.document = (fun ps uu____3922 -> (match (uu____3922) with
| (lid, t, doc_opt) -> begin
(

let uu____3938 = (

let uu____3939 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (

let uu____3940 = (

let uu____3941 = (p_lident lid)
in (

let uu____3942 = (

let uu____3943 = (p_typ ps false t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3943))
in (FStar_Pprint.op_Hat_Hat uu____3941 uu____3942)))
in (FStar_Pprint.op_Hat_Hat uu____3939 uu____3940)))
in (FStar_Pprint.group uu____3938))
end))
and p_constructorDecl : (FStar_Ident.ident * FStar_Parser_AST.term FStar_Pervasives_Native.option * FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option * Prims.bool)  ->  FStar_Pprint.document = (fun uu____3944 -> (match (uu____3944) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let sep = (match (use_of) with
| true -> begin
(str "of")
end
| uu____3970 -> begin
FStar_Pprint.colon
end)
in (

let uid_doc = (p_uident uid)
in (

let uu____3972 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (

let uu____3973 = (

let uu____3974 = (FStar_Pprint.break_ (Prims.parse_int "0"))
in (

let uu____3975 = (default_or_map uid_doc (fun t -> (

let uu____3980 = (

let uu____3981 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep)
in (FStar_Pprint.op_Hat_Hat uid_doc uu____3981))
in (

let uu____3982 = (p_typ false false t)
in (op_Hat_Slash_Plus_Hat uu____3980 uu____3982)))) t_opt)
in (FStar_Pprint.op_Hat_Hat uu____3974 uu____3975)))
in (FStar_Pprint.op_Hat_Hat uu____3972 uu____3973)))))
end))
and p_letlhs : (FStar_Parser_AST.pattern * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun uu____3983 -> (match (uu____3983) with
| (pat, uu____3989) -> begin
(

let uu____3990 = (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat1, (t, FStar_Pervasives_Native.None)) -> begin
(

let uu____4009 = (

let uu____4010 = (

let uu____4011 = (

let uu____4012 = (

let uu____4013 = (p_tmArrow p_tmNoEq t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4013))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4012))
in (FStar_Pprint.group uu____4011))
in (FStar_Pprint.op_Hat_Hat break1 uu____4010))
in ((pat1), (uu____4009)))
end
| FStar_Parser_AST.PatAscribed (pat1, (t, FStar_Pervasives_Native.Some (tac))) -> begin
(

let uu____4025 = (

let uu____4026 = (

let uu____4027 = (

let uu____4028 = (

let uu____4029 = (

let uu____4030 = (p_tmArrow p_tmNoEq t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4030))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4029))
in (FStar_Pprint.group uu____4028))
in (

let uu____4031 = (

let uu____4032 = (

let uu____4033 = (str "by")
in (

let uu____4034 = (

let uu____4035 = (p_atomicTerm tac)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4035))
in (FStar_Pprint.op_Hat_Hat uu____4033 uu____4034)))
in (FStar_Pprint.group uu____4032))
in (FStar_Pprint.op_Hat_Hat uu____4027 uu____4031)))
in (FStar_Pprint.op_Hat_Hat break1 uu____4026))
in ((pat1), (uu____4025)))
end
| uu____4036 -> begin
((pat), (FStar_Pprint.empty))
end)
in (match (uu____3990) with
| (pat1, ascr_doc) -> begin
(match (pat1.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____4040); FStar_Parser_AST.prange = uu____4041}, pats) -> begin
(

let uu____4051 = (

let uu____4052 = (p_lident x)
in (

let uu____4053 = (

let uu____4054 = (separate_map_or_flow break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Hat uu____4054 ascr_doc))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4052 uu____4053)))
in (FStar_Pprint.group uu____4051))
end
| uu____4055 -> begin
(

let uu____4056 = (

let uu____4057 = (p_tuplePattern pat1)
in (FStar_Pprint.op_Hat_Hat uu____4057 ascr_doc))
in (FStar_Pprint.group uu____4056))
end)
end))
end))
and p_letbinding : (FStar_Parser_AST.pattern * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun uu____4058 -> (match (uu____4058) with
| (pat, e) -> begin
(

let pat_doc = (p_letlhs ((pat), (e)))
in (

let uu____4066 = (

let uu____4067 = (FStar_Pprint.op_Hat_Slash_Hat pat_doc FStar_Pprint.equals)
in (FStar_Pprint.group uu____4067))
in (

let uu____4068 = (p_term false false e)
in (prefix2 uu____4066 uu____4068))))
end))
and p_newEffect : FStar_Parser_AST.effect_decl  ->  FStar_Pprint.document = (fun uu___60_4069 -> (match (uu___60_4069) with
| FStar_Parser_AST.RedefineEffect (lid, bs, t) -> begin
(p_effectRedefinition lid bs t)
end
| FStar_Parser_AST.DefineEffect (lid, bs, t, eff_decls) -> begin
(p_effectDefinition lid bs t eff_decls)
end))
and p_effectRedefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun uid bs t -> (

let uu____4094 = (p_uident uid)
in (

let uu____4095 = (p_binders true bs)
in (

let uu____4096 = (

let uu____4097 = (p_simpleTerm false false t)
in (prefix2 FStar_Pprint.equals uu____4097))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____4094 uu____4095 uu____4096)))))
and p_effectDefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun uid bs t eff_decls -> (

let uu____4106 = (

let uu____4107 = (

let uu____4108 = (

let uu____4109 = (p_uident uid)
in (

let uu____4110 = (p_binders true bs)
in (

let uu____4111 = (

let uu____4112 = (p_typ false false t)
in (prefix2 FStar_Pprint.colon uu____4112))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____4109 uu____4110 uu____4111))))
in (FStar_Pprint.group uu____4108))
in (

let uu____4113 = (

let uu____4114 = (str "with")
in (

let uu____4115 = (separate_break_map_last FStar_Pprint.semi p_effectDecl eff_decls)
in (prefix2 uu____4114 uu____4115)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4107 uu____4113)))
in (braces_with_nesting uu____4106)))
and p_effectDecl : Prims.bool  ->  FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun ps d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (false, ((FStar_Parser_AST.TyconAbbrev (lid, [], FStar_Pervasives_Native.None, e), FStar_Pervasives_Native.None))::[]) -> begin
(

let uu____4146 = (

let uu____4147 = (p_lident lid)
in (

let uu____4148 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____4147 uu____4148)))
in (

let uu____4149 = (p_simpleTerm ps false e)
in (prefix2 uu____4146 uu____4149)))
end
| uu____4150 -> begin
(

let uu____4151 = (

let uu____4152 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "Not a declaration of an effect member... or at least I hope so : %s" uu____4152))
in (failwith uu____4151))
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

let p_lift = (fun ps uu____4214 -> (match (uu____4214) with
| (kwd, t) -> begin
(

let uu____4221 = (

let uu____4222 = (str kwd)
in (

let uu____4223 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____4222 uu____4223)))
in (

let uu____4224 = (p_simpleTerm ps false t)
in (prefix2 uu____4221 uu____4224)))
end))
in (separate_break_map_last FStar_Pprint.semi p_lift lifts)))
in (

let uu____4229 = (

let uu____4230 = (

let uu____4231 = (p_quident lift.FStar_Parser_AST.msource)
in (

let uu____4232 = (

let uu____4233 = (str "~>")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4233))
in (FStar_Pprint.op_Hat_Hat uu____4231 uu____4232)))
in (

let uu____4234 = (p_quident lift.FStar_Parser_AST.mdest)
in (prefix2 uu____4230 uu____4234)))
in (

let uu____4235 = (

let uu____4236 = (braces_with_nesting lift_op_doc)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4236))
in (FStar_Pprint.op_Hat_Hat uu____4229 uu____4235)))))
and p_qualifier : FStar_Parser_AST.qualifier  ->  FStar_Pprint.document = (fun uu___61_4237 -> (match (uu___61_4237) with
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

let uu____4239 = (FStar_Pprint.separate_map break1 p_qualifier qs)
in (FStar_Pprint.group uu____4239)))
and p_letqualifier : FStar_Parser_AST.let_qualifier  ->  FStar_Pprint.document = (fun uu___62_4240 -> (match (uu___62_4240) with
| FStar_Parser_AST.Rec -> begin
(

let uu____4241 = (str "rec")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4241))
end
| FStar_Parser_AST.Mutable -> begin
(

let uu____4242 = (str "mutable")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4242))
end
| FStar_Parser_AST.NoLetQualifier -> begin
FStar_Pprint.empty
end))
and p_aqual : FStar_Parser_AST.arg_qualifier  ->  FStar_Pprint.document = (fun uu___63_4243 -> (match (uu___63_4243) with
| FStar_Parser_AST.Implicit -> begin
(str "#")
end
| FStar_Parser_AST.Equality -> begin
(str "$")
end))
and p_disjunctivePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr (pats) -> begin
(

let uu____4248 = (

let uu____4249 = (

let uu____4250 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space)
in (FStar_Pprint.op_Hat_Hat break1 uu____4250))
in (FStar_Pprint.separate_map uu____4249 p_tuplePattern pats))
in (FStar_Pprint.group uu____4248))
end
| uu____4251 -> begin
(p_tuplePattern p)
end))
and p_tuplePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTuple (pats, false) -> begin
(

let uu____4258 = (

let uu____4259 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map uu____4259 p_constructorPattern pats))
in (FStar_Pprint.group uu____4258))
end
| uu____4260 -> begin
(p_constructorPattern p)
end))
and p_constructorPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (maybe_cons_lid); FStar_Parser_AST.prange = uu____4263}, (hd1)::(tl1)::[]) when (FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid) -> begin
(

let uu____4268 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon)
in (

let uu____4269 = (p_constructorPattern hd1)
in (

let uu____4270 = (p_constructorPattern tl1)
in (infix0 uu____4268 uu____4269 uu____4270))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (uid); FStar_Parser_AST.prange = uu____4272}, pats) -> begin
(

let uu____4278 = (p_quident uid)
in (

let uu____4279 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (prefix2 uu____4278 uu____4279)))
end
| uu____4280 -> begin
(p_atomicPattern p)
end))
and p_atomicPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, (t, FStar_Pervasives_Native.None)) -> begin
(match (((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm))) with
| (FStar_Parser_AST.PatVar (lid, aqual), FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t1); FStar_Parser_AST.brange = uu____4296; FStar_Parser_AST.blevel = uu____4297; FStar_Parser_AST.aqual = uu____4298}, phi)) when (Prims.op_Equality lid.FStar_Ident.idText lid'.FStar_Ident.idText) -> begin
(

let uu____4304 = (

let uu____4305 = (p_ident lid)
in (p_refinement aqual uu____4305 t1 phi))
in (soft_parens_with_nesting uu____4304))
end
| (FStar_Parser_AST.PatWild, FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t1); FStar_Parser_AST.brange = uu____4307; FStar_Parser_AST.blevel = uu____4308; FStar_Parser_AST.aqual = uu____4309}, phi)) -> begin
(

let uu____4311 = (p_refinement FStar_Pervasives_Native.None FStar_Pprint.underscore t1 phi)
in (soft_parens_with_nesting uu____4311))
end
| uu____4312 -> begin
(

let uu____4317 = (

let uu____4318 = (p_tuplePattern pat)
in (

let uu____4319 = (

let uu____4320 = (FStar_Pprint.break_ (Prims.parse_int "0"))
in (

let uu____4321 = (

let uu____4322 = (p_tmEqNoRefinement t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4322))
in (FStar_Pprint.op_Hat_Hat uu____4320 uu____4321)))
in (FStar_Pprint.op_Hat_Hat uu____4318 uu____4319)))
in (soft_parens_with_nesting uu____4317))
end)
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let uu____4326 = (separate_break_map FStar_Pprint.semi p_tuplePattern pats)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket uu____4326 FStar_Pprint.rbracket))
end
| FStar_Parser_AST.PatRecord (pats) -> begin
(

let p_recordFieldPat = (fun uu____4343 -> (match (uu____4343) with
| (lid, pat) -> begin
(

let uu____4350 = (p_qlident lid)
in (

let uu____4351 = (p_tuplePattern pat)
in (infix2 FStar_Pprint.equals uu____4350 uu____4351)))
end))
in (

let uu____4352 = (separate_break_map FStar_Pprint.semi p_recordFieldPat pats)
in (soft_braces_with_nesting uu____4352)))
end
| FStar_Parser_AST.PatTuple (pats, true) -> begin
(

let uu____4362 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (

let uu____4363 = (separate_break_map FStar_Pprint.comma p_constructorPattern pats)
in (

let uu____4364 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____4362 uu____4363 uu____4364))))
end
| FStar_Parser_AST.PatTvar (tv, arg_qualifier_opt) -> begin
(p_tvar tv)
end
| FStar_Parser_AST.PatOp (op) -> begin
(

let uu____4373 = (

let uu____4374 = (

let uu____4375 = (

let uu____4376 = (FStar_Ident.text_of_id op)
in (str uu____4376))
in (

let uu____4377 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat uu____4375 uu____4377)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4374))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4373))
end
| FStar_Parser_AST.PatWild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.PatConst (c) -> begin
(p_constant c)
end
| FStar_Parser_AST.PatVar (lid, aqual) -> begin
(

let uu____4385 = (FStar_Pprint.optional p_aqual aqual)
in (

let uu____4386 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat uu____4385 uu____4386)))
end
| FStar_Parser_AST.PatName (uid) -> begin
(p_quident uid)
end
| FStar_Parser_AST.PatOr (uu____4388) -> begin
(failwith "Inner or pattern !")
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (uu____4391); FStar_Parser_AST.prange = uu____4392}, uu____4393) -> begin
(

let uu____4398 = (p_tuplePattern p)
in (soft_parens_with_nesting uu____4398))
end
| FStar_Parser_AST.PatTuple (uu____4399, false) -> begin
(

let uu____4404 = (p_tuplePattern p)
in (soft_parens_with_nesting uu____4404))
end
| uu____4405 -> begin
(

let uu____4406 = (

let uu____4407 = (FStar_Parser_AST.pat_to_string p)
in (FStar_Util.format1 "Invalid pattern %s" uu____4407))
in (failwith uu____4406))
end))
and p_binder : Prims.bool  ->  FStar_Parser_AST.binder  ->  FStar_Pprint.document = (fun is_atomic b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (lid) -> begin
(

let uu____4411 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (

let uu____4412 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat uu____4411 uu____4412)))
end
| FStar_Parser_AST.TVariable (lid) -> begin
(p_lident lid)
end
| FStar_Parser_AST.Annotated (lid, t) -> begin
(

let doc1 = (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t1); FStar_Parser_AST.brange = uu____4419; FStar_Parser_AST.blevel = uu____4420; FStar_Parser_AST.aqual = uu____4421}, phi) when (Prims.op_Equality lid.FStar_Ident.idText lid'.FStar_Ident.idText) -> begin
(

let uu____4423 = (p_ident lid)
in (p_refinement b.FStar_Parser_AST.aqual uu____4423 t1 phi))
end
| uu____4424 -> begin
(

let uu____4425 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (

let uu____4426 = (

let uu____4427 = (p_lident lid)
in (

let uu____4428 = (

let uu____4429 = (

let uu____4430 = (FStar_Pprint.break_ (Prims.parse_int "0"))
in (

let uu____4431 = (p_tmFormula t)
in (FStar_Pprint.op_Hat_Hat uu____4430 uu____4431)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4429))
in (FStar_Pprint.op_Hat_Hat uu____4427 uu____4428)))
in (FStar_Pprint.op_Hat_Hat uu____4425 uu____4426)))
end)
in (match (is_atomic) with
| true -> begin
(

let uu____4432 = (

let uu____4433 = (FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4433))
in (FStar_Pprint.group uu____4432))
end
| uu____4434 -> begin
(FStar_Pprint.group doc1)
end))
end
| FStar_Parser_AST.TAnnotated (uu____4435) -> begin
(failwith "Is this still used ?")
end
| FStar_Parser_AST.NoName (t) -> begin
(match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t1); FStar_Parser_AST.brange = uu____4442; FStar_Parser_AST.blevel = uu____4443; FStar_Parser_AST.aqual = uu____4444}, phi) -> begin
(match (is_atomic) with
| true -> begin
(

let uu____4446 = (

let uu____4447 = (

let uu____4448 = (p_refinement b.FStar_Parser_AST.aqual FStar_Pprint.underscore t1 phi)
in (FStar_Pprint.op_Hat_Hat uu____4448 FStar_Pprint.rparen))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4447))
in (FStar_Pprint.group uu____4446))
end
| uu____4449 -> begin
(

let uu____4450 = (p_refinement b.FStar_Parser_AST.aqual FStar_Pprint.underscore t1 phi)
in (FStar_Pprint.group uu____4450))
end)
end
| uu____4451 -> begin
(match (is_atomic) with
| true -> begin
(p_atomicTerm t)
end
| uu____4452 -> begin
(p_appTerm t)
end)
end)
end))
and p_refinement : FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Pprint.document  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun aqual_opt binder t phi -> (

let uu____4459 = (FStar_Pprint.optional p_aqual aqual_opt)
in (

let uu____4460 = (

let uu____4461 = (

let uu____4462 = (

let uu____4463 = (p_appTerm t)
in (

let uu____4464 = (

let uu____4465 = (p_noSeqTerm false false phi)
in (soft_braces_with_nesting uu____4465))
in (FStar_Pprint.op_Hat_Hat uu____4463 uu____4464)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4462))
in (FStar_Pprint.op_Hat_Hat binder uu____4461))
in (FStar_Pprint.op_Hat_Hat uu____4459 uu____4460))))
and p_binders : Prims.bool  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Pprint.document = (fun is_atomic bs -> (separate_map_or_flow break1 (p_binder is_atomic) bs))
and p_qlident : FStar_Ident.lid  ->  FStar_Pprint.document = (fun lid -> (

let uu____4471 = (FStar_Ident.text_of_lid lid)
in (str uu____4471)))
and p_quident : FStar_Ident.lid  ->  FStar_Pprint.document = (fun lid -> (

let uu____4473 = (FStar_Ident.text_of_lid lid)
in (str uu____4473)))
and p_ident : FStar_Ident.ident  ->  FStar_Pprint.document = (fun lid -> (

let uu____4475 = (FStar_Ident.text_of_id lid)
in (str uu____4475)))
and p_lident : FStar_Ident.ident  ->  FStar_Pprint.document = (fun lid -> (

let uu____4477 = (FStar_Ident.text_of_id lid)
in (str uu____4477)))
and p_uident : FStar_Ident.ident  ->  FStar_Pprint.document = (fun lid -> (

let uu____4479 = (FStar_Ident.text_of_id lid)
in (str uu____4479)))
and p_tvar : FStar_Ident.ident  ->  FStar_Pprint.document = (fun lid -> (

let uu____4481 = (FStar_Ident.text_of_id lid)
in (str uu____4481)))
and p_lidentOrUnderscore : FStar_Ident.ident  ->  FStar_Pprint.document = (fun id1 -> (match ((FStar_Util.starts_with FStar_Ident.reserved_prefix id1.FStar_Ident.idText)) with
| true -> begin
FStar_Pprint.underscore
end
| uu____4483 -> begin
(p_lident id1)
end))
and paren_if : Prims.bool  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun b -> (match (b) with
| true -> begin
soft_parens_with_nesting
end
| uu____4488 -> begin
(

let id1 = (fun x -> x)
in id1)
end))
and p_term : Prims.bool  ->  Prims.bool  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun ps pb e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Seq (e1, e2) -> begin
(

let uu____4500 = (

let uu____4501 = (

let uu____4502 = (p_noSeqTerm true false e1)
in (FStar_Pprint.op_Hat_Hat uu____4502 FStar_Pprint.semi))
in (FStar_Pprint.group uu____4501))
in (

let uu____4503 = (p_term ps pb e2)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4500 uu____4503)))
end
| FStar_Parser_AST.Bind (x, e1, e2) -> begin
(

let uu____4507 = (

let uu____4508 = (

let uu____4509 = (

let uu____4510 = (p_lident x)
in (

let uu____4511 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.long_left_arrow)
in (FStar_Pprint.op_Hat_Hat uu____4510 uu____4511)))
in (

let uu____4512 = (

let uu____4513 = (p_noSeqTerm true false e1)
in (

let uu____4514 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.semi)
in (FStar_Pprint.op_Hat_Hat uu____4513 uu____4514)))
in (op_Hat_Slash_Plus_Hat uu____4509 uu____4512)))
in (FStar_Pprint.group uu____4508))
in (

let uu____4515 = (p_term ps pb e2)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4507 uu____4515)))
end
| uu____4516 -> begin
(

let uu____4517 = (p_noSeqTerm ps pb e)
in (FStar_Pprint.group uu____4517))
end))
and p_noSeqTerm : Prims.bool  ->  Prims.bool  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun ps pb e -> (with_comment (p_noSeqTerm' ps pb) e e.FStar_Parser_AST.range))
and p_noSeqTerm' : Prims.bool  ->  Prims.bool  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun ps pb e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Ascribed (e1, t, FStar_Pervasives_Native.None) -> begin
(

let uu____4528 = (

let uu____4529 = (p_tmIff e1)
in (

let uu____4530 = (

let uu____4531 = (

let uu____4532 = (p_typ ps pb t)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4532))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4531))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4529 uu____4530)))
in (FStar_Pprint.group uu____4528))
end
| FStar_Parser_AST.Ascribed (e1, t, FStar_Pervasives_Native.Some (tac)) -> begin
(

let uu____4538 = (

let uu____4539 = (p_tmIff e1)
in (

let uu____4540 = (

let uu____4541 = (

let uu____4542 = (

let uu____4543 = (p_typ false false t)
in (

let uu____4544 = (

let uu____4545 = (str "by")
in (

let uu____4546 = (p_typ ps pb tac)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4545 uu____4546)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4543 uu____4544)))
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4542))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4541))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4539 uu____4540)))
in (FStar_Pprint.group uu____4538))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = ".()<-"; FStar_Ident.idRange = uu____4547}, (e1)::(e2)::(e3)::[]) -> begin
(

let uu____4553 = (

let uu____4554 = (

let uu____4555 = (

let uu____4556 = (p_atomicTermNotQUident e1)
in (

let uu____4557 = (

let uu____4558 = (

let uu____4559 = (

let uu____4560 = (p_term false false e2)
in (soft_parens_with_nesting uu____4560))
in (

let uu____4561 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat uu____4559 uu____4561)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4558))
in (FStar_Pprint.op_Hat_Hat uu____4556 uu____4557)))
in (FStar_Pprint.group uu____4555))
in (

let uu____4562 = (

let uu____4563 = (p_noSeqTerm ps pb e3)
in (jump2 uu____4563))
in (FStar_Pprint.op_Hat_Hat uu____4554 uu____4562)))
in (FStar_Pprint.group uu____4553))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = ".[]<-"; FStar_Ident.idRange = uu____4564}, (e1)::(e2)::(e3)::[]) -> begin
(

let uu____4570 = (

let uu____4571 = (

let uu____4572 = (

let uu____4573 = (p_atomicTermNotQUident e1)
in (

let uu____4574 = (

let uu____4575 = (

let uu____4576 = (

let uu____4577 = (p_term false false e2)
in (soft_brackets_with_nesting uu____4577))
in (

let uu____4578 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat uu____4576 uu____4578)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4575))
in (FStar_Pprint.op_Hat_Hat uu____4573 uu____4574)))
in (FStar_Pprint.group uu____4572))
in (

let uu____4579 = (

let uu____4580 = (p_noSeqTerm ps pb e3)
in (jump2 uu____4580))
in (FStar_Pprint.op_Hat_Hat uu____4571 uu____4579)))
in (FStar_Pprint.group uu____4570))
end
| FStar_Parser_AST.Requires (e1, wtf) -> begin
(

let uu____4588 = (

let uu____4589 = (str "requires")
in (

let uu____4590 = (p_typ ps pb e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4589 uu____4590)))
in (FStar_Pprint.group uu____4588))
end
| FStar_Parser_AST.Ensures (e1, wtf) -> begin
(

let uu____4598 = (

let uu____4599 = (str "ensures")
in (

let uu____4600 = (p_typ ps pb e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4599 uu____4600)))
in (FStar_Pprint.group uu____4598))
end
| FStar_Parser_AST.Attributes (es) -> begin
(

let uu____4604 = (

let uu____4605 = (str "attributes")
in (

let uu____4606 = (FStar_Pprint.separate_map break1 p_atomicTerm es)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4605 uu____4606)))
in (FStar_Pprint.group uu____4604))
end
| FStar_Parser_AST.If (e1, e2, e3) -> begin
(match ((is_unit e3)) with
| true -> begin
(

let uu____4610 = (

let uu____4611 = (

let uu____4612 = (str "if")
in (

let uu____4613 = (p_noSeqTerm false false e1)
in (op_Hat_Slash_Plus_Hat uu____4612 uu____4613)))
in (

let uu____4614 = (

let uu____4615 = (str "then")
in (

let uu____4616 = (p_noSeqTerm ps pb e2)
in (op_Hat_Slash_Plus_Hat uu____4615 uu____4616)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4611 uu____4614)))
in (FStar_Pprint.group uu____4610))
end
| uu____4617 -> begin
(

let e2_doc = (match (e2.FStar_Parser_AST.tm) with
| FStar_Parser_AST.If (uu____4619, uu____4620, e31) when (is_unit e31) -> begin
(

let uu____4622 = (p_noSeqTerm false false e2)
in (soft_parens_with_nesting uu____4622))
end
| uu____4623 -> begin
(p_noSeqTerm false false e2)
end)
in (

let uu____4624 = (

let uu____4625 = (

let uu____4626 = (str "if")
in (

let uu____4627 = (p_noSeqTerm false false e1)
in (op_Hat_Slash_Plus_Hat uu____4626 uu____4627)))
in (

let uu____4628 = (

let uu____4629 = (

let uu____4630 = (str "then")
in (op_Hat_Slash_Plus_Hat uu____4630 e2_doc))
in (

let uu____4631 = (

let uu____4632 = (str "else")
in (

let uu____4633 = (p_noSeqTerm ps pb e3)
in (op_Hat_Slash_Plus_Hat uu____4632 uu____4633)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4629 uu____4631)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4625 uu____4628)))
in (FStar_Pprint.group uu____4624)))
end)
end
| FStar_Parser_AST.TryWith (e1, branches) -> begin
(

let uu____4656 = (

let uu____4657 = (

let uu____4658 = (

let uu____4659 = (str "try")
in (

let uu____4660 = (p_noSeqTerm false false e1)
in (prefix2 uu____4659 uu____4660)))
in (

let uu____4661 = (

let uu____4662 = (str "with")
in (

let uu____4663 = (separate_map_last FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4662 uu____4663)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4658 uu____4661)))
in (FStar_Pprint.group uu____4657))
in (

let uu____4672 = (paren_if (ps || pb))
in (uu____4672 uu____4656)))
end
| FStar_Parser_AST.Match (e1, branches) -> begin
(

let uu____4699 = (

let uu____4700 = (

let uu____4701 = (

let uu____4702 = (str "match")
in (

let uu____4703 = (p_noSeqTerm false false e1)
in (

let uu____4704 = (str "with")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____4702 uu____4703 uu____4704))))
in (

let uu____4705 = (separate_map_last FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4701 uu____4705)))
in (FStar_Pprint.group uu____4700))
in (

let uu____4714 = (paren_if (ps || pb))
in (uu____4714 uu____4699)))
end
| FStar_Parser_AST.LetOpen (uid, e1) -> begin
(

let uu____4721 = (

let uu____4722 = (

let uu____4723 = (

let uu____4724 = (str "let open")
in (

let uu____4725 = (p_quident uid)
in (

let uu____4726 = (str "in")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____4724 uu____4725 uu____4726))))
in (

let uu____4727 = (p_term false pb e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4723 uu____4727)))
in (FStar_Pprint.group uu____4722))
in (

let uu____4728 = (paren_if ps)
in (uu____4728 uu____4721)))
end
| FStar_Parser_AST.Let (q, lbs, e1) -> begin
(

let p_lb = (fun q1 uu____4792 is_last -> (match (uu____4792) with
| (a, (pat, e2)) -> begin
(

let attrs = (p_attrs_opt a)
in (

let doc_let_or_and = (match (q1) with
| FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec) -> begin
(

let uu____4825 = (

let uu____4826 = (str "let")
in (

let uu____4827 = (str "rec")
in (FStar_Pprint.op_Hat_Slash_Hat uu____4826 uu____4827)))
in (FStar_Pprint.group uu____4825))
end
| FStar_Pervasives_Native.Some (FStar_Parser_AST.NoLetQualifier) -> begin
(str "let")
end
| uu____4828 -> begin
(str "and")
end)
in (

let doc_pat = (p_letlhs ((pat), (e2)))
in (

let doc_expr = (p_term false false e2)
in (

let uu____4833 = (match (is_last) with
| true -> begin
(

let uu____4834 = (

let uu____4835 = (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") doc_let_or_and doc_pat FStar_Pprint.equals)
in (

let uu____4836 = (str "in")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____4835 doc_expr uu____4836)))
in (FStar_Pprint.group uu____4834))
end
| uu____4837 -> begin
(

let uu____4838 = (

let uu____4839 = (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") doc_let_or_and doc_pat FStar_Pprint.equals)
in (FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "1") uu____4839 doc_expr))
in (FStar_Pprint.group uu____4838))
end)
in (FStar_Pprint.op_Hat_Hat attrs uu____4833))))))
end))
in (

let l = (FStar_List.length lbs)
in (

let lbs_docs = (FStar_List.mapi (fun i lb -> (match ((Prims.op_Equality i (Prims.parse_int "0"))) with
| true -> begin
(

let uu____4885 = (p_lb (FStar_Pervasives_Native.Some (q)) lb (Prims.op_Equality i (l - (Prims.parse_int "1"))))
in (FStar_Pprint.group uu____4885))
end
| uu____4892 -> begin
(

let uu____4893 = (p_lb FStar_Pervasives_Native.None lb (Prims.op_Equality i (l - (Prims.parse_int "1"))))
in (FStar_Pprint.group uu____4893))
end)) lbs)
in (

let lbs_doc = (

let uu____4901 = (FStar_Pprint.separate break1 lbs_docs)
in (FStar_Pprint.group uu____4901))
in (

let uu____4902 = (

let uu____4903 = (

let uu____4904 = (

let uu____4905 = (p_term false pb e1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4905))
in (FStar_Pprint.op_Hat_Hat lbs_doc uu____4904))
in (FStar_Pprint.group uu____4903))
in (

let uu____4906 = (paren_if ps)
in (uu____4906 uu____4902)))))))
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, typ_opt); FStar_Parser_AST.prange = uu____4913})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, branches); FStar_Parser_AST.range = uu____4916; FStar_Parser_AST.level = uu____4917}) when (matches_var maybe_x x) -> begin
(

let uu____4944 = (

let uu____4945 = (

let uu____4946 = (str "function")
in (

let uu____4947 = (separate_map_last FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4946 uu____4947)))
in (FStar_Pprint.group uu____4945))
in (

let uu____4956 = (paren_if (ps || pb))
in (uu____4956 uu____4944)))
end
| FStar_Parser_AST.Quote (e1, FStar_Parser_AST.Dynamic) -> begin
(

let uu____4962 = (

let uu____4963 = (str "quote")
in (

let uu____4964 = (p_noSeqTerm ps pb e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4963 uu____4964)))
in (FStar_Pprint.group uu____4962))
end
| FStar_Parser_AST.Quote (e1, FStar_Parser_AST.Static) -> begin
(

let uu____4966 = (

let uu____4967 = (str "`")
in (

let uu____4968 = (p_noSeqTerm ps pb e1)
in (FStar_Pprint.op_Hat_Hat uu____4967 uu____4968)))
in (FStar_Pprint.group uu____4966))
end
| FStar_Parser_AST.VQuote (e1) -> begin
(

let uu____4970 = (

let uu____4971 = (str "%`")
in (

let uu____4972 = (p_noSeqTerm ps pb e1)
in (FStar_Pprint.op_Hat_Hat uu____4971 uu____4972)))
in (FStar_Pprint.group uu____4970))
end
| FStar_Parser_AST.Antiquote (false, e1) -> begin
(

let uu____4974 = (

let uu____4975 = (str "`#")
in (

let uu____4976 = (p_noSeqTerm ps pb e1)
in (FStar_Pprint.op_Hat_Hat uu____4975 uu____4976)))
in (FStar_Pprint.group uu____4974))
end
| FStar_Parser_AST.Antiquote (true, e1) -> begin
(

let uu____4978 = (

let uu____4979 = (str "`@")
in (

let uu____4980 = (p_noSeqTerm ps pb e1)
in (FStar_Pprint.op_Hat_Hat uu____4979 uu____4980)))
in (FStar_Pprint.group uu____4978))
end
| uu____4981 -> begin
(p_typ ps pb e)
end))
and p_attrs_opt : FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option  ->  FStar_Pprint.document = (fun uu___64_4982 -> (match (uu___64_4982) with
| FStar_Pervasives_Native.None -> begin
FStar_Pprint.empty
end
| FStar_Pervasives_Native.Some (terms) -> begin
(

let uu____4994 = (

let uu____4995 = (

let uu____4996 = (str "[@")
in (

let uu____4997 = (

let uu____4998 = (FStar_Pprint.separate_map break1 p_atomicTerm terms)
in (

let uu____4999 = (str "]")
in (FStar_Pprint.op_Hat_Slash_Hat uu____4998 uu____4999)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4996 uu____4997)))
in (FStar_Pprint.group uu____4995))
in (FStar_Pprint.op_Hat_Hat uu____4994 break1))
end))
and p_typ : Prims.bool  ->  Prims.bool  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun ps pb e -> (with_comment (p_typ' ps pb) e e.FStar_Parser_AST.range))
and p_typ' : Prims.bool  ->  Prims.bool  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun ps pb e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.QForall (bs, trigger, e1) -> begin
(

let uu____5021 = (

let uu____5022 = (

let uu____5023 = (p_quantifier e)
in (FStar_Pprint.op_Hat_Hat uu____5023 FStar_Pprint.space))
in (

let uu____5024 = (p_binders true bs)
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") uu____5022 uu____5024 FStar_Pprint.dot)))
in (

let uu____5025 = (

let uu____5026 = (p_trigger trigger)
in (

let uu____5027 = (p_noSeqTerm ps pb e1)
in (FStar_Pprint.op_Hat_Hat uu____5026 uu____5027)))
in (prefix2 uu____5021 uu____5025)))
end
| FStar_Parser_AST.QExists (bs, trigger, e1) -> begin
(

let uu____5043 = (

let uu____5044 = (

let uu____5045 = (p_quantifier e)
in (FStar_Pprint.op_Hat_Hat uu____5045 FStar_Pprint.space))
in (

let uu____5046 = (p_binders true bs)
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") uu____5044 uu____5046 FStar_Pprint.dot)))
in (

let uu____5047 = (

let uu____5048 = (p_trigger trigger)
in (

let uu____5049 = (p_noSeqTerm ps pb e1)
in (FStar_Pprint.op_Hat_Hat uu____5048 uu____5049)))
in (prefix2 uu____5043 uu____5047)))
end
| uu____5050 -> begin
(p_simpleTerm ps pb e)
end))
and p_quantifier : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.QForall (uu____5052) -> begin
(str "forall")
end
| FStar_Parser_AST.QExists (uu____5065) -> begin
(str "exists")
end
| uu____5078 -> begin
(failwith "Imposible : p_quantifier called on a non-quantifier term")
end))
and p_trigger : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun uu___65_5079 -> (match (uu___65_5079) with
| [] -> begin
FStar_Pprint.empty
end
| pats -> begin
(

let uu____5091 = (

let uu____5092 = (

let uu____5093 = (str "pattern")
in (

let uu____5094 = (

let uu____5095 = (

let uu____5096 = (p_disjunctivePats pats)
in (jump2 uu____5096))
in (

let uu____5097 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5095 uu____5097)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____5093 uu____5094)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5092))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____5091))
end))
and p_disjunctivePats : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun pats -> (

let uu____5103 = (str "\\/")
in (FStar_Pprint.separate_map uu____5103 p_conjunctivePats pats)))
and p_conjunctivePats : FStar_Parser_AST.term Prims.list  ->  FStar_Pprint.document = (fun pats -> (

let uu____5109 = (FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats)
in (FStar_Pprint.group uu____5109)))
and p_simpleTerm : Prims.bool  ->  Prims.bool  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun ps pb e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Abs (pats, e1) -> begin
(

let uu____5119 = (

let uu____5120 = (

let uu____5121 = (str "fun")
in (

let uu____5122 = (

let uu____5123 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5123 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat uu____5121 uu____5122)))
in (

let uu____5124 = (p_term false pb e1)
in (op_Hat_Slash_Plus_Hat uu____5120 uu____5124)))
in (

let uu____5125 = (paren_if ps)
in (uu____5125 uu____5119)))
end
| uu____5130 -> begin
(p_tmIff e)
end))
and p_maybeFocusArrow : Prims.bool  ->  FStar_Pprint.document = (fun b -> (match (b) with
| true -> begin
(str "~>")
end
| uu____5132 -> begin
FStar_Pprint.rarrow
end))
and p_patternBranch : Prims.bool  ->  (FStar_Parser_AST.pattern * FStar_Parser_AST.term FStar_Pervasives_Native.option * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun pb uu____5134 -> (match (uu____5134) with
| (pat, when_opt, e) -> begin
(

let uu____5150 = (

let uu____5151 = (

let uu____5152 = (

let uu____5153 = (

let uu____5154 = (

let uu____5155 = (p_disjunctivePattern pat)
in (

let uu____5156 = (

let uu____5157 = (p_maybeWhen when_opt)
in (FStar_Pprint.op_Hat_Hat uu____5157 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat uu____5155 uu____5156)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5154))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5153))
in (FStar_Pprint.group uu____5152))
in (

let uu____5158 = (p_term false pb e)
in (op_Hat_Slash_Plus_Hat uu____5151 uu____5158)))
in (FStar_Pprint.group uu____5150))
end))
and p_maybeWhen : FStar_Parser_AST.term FStar_Pervasives_Native.option  ->  FStar_Pprint.document = (fun uu___66_5159 -> (match (uu___66_5159) with
| FStar_Pervasives_Native.None -> begin
FStar_Pprint.empty
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____5163 = (str "when")
in (

let uu____5164 = (

let uu____5165 = (p_tmFormula e)
in (FStar_Pprint.op_Hat_Hat uu____5165 FStar_Pprint.space))
in (op_Hat_Slash_Plus_Hat uu____5163 uu____5164)))
end))
and p_tmIff : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5167}, (e1)::(e2)::[]) -> begin
(

let uu____5172 = (str "<==>")
in (

let uu____5173 = (p_tmImplies e1)
in (

let uu____5174 = (p_tmIff e2)
in (infix0 uu____5172 uu____5173 uu____5174))))
end
| uu____5175 -> begin
(p_tmImplies e)
end))
and p_tmImplies : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5177}, (e1)::(e2)::[]) -> begin
(

let uu____5182 = (str "==>")
in (

let uu____5183 = (p_tmArrow p_tmFormula e1)
in (

let uu____5184 = (p_tmImplies e2)
in (infix0 uu____5182 uu____5183 uu____5184))))
end
| uu____5185 -> begin
(p_tmArrow p_tmFormula e)
end))
and p_tmArrow : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_Tm e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Product (bs, tgt) -> begin
(

let uu____5196 = (

let uu____5197 = (separate_map_or_flow FStar_Pprint.empty (fun b -> (

let uu____5202 = (p_binder false b)
in (

let uu____5203 = (

let uu____5204 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5204))
in (FStar_Pprint.op_Hat_Hat uu____5202 uu____5203)))) bs)
in (

let uu____5205 = (p_tmArrow p_Tm tgt)
in (FStar_Pprint.op_Hat_Hat uu____5197 uu____5205)))
in (FStar_Pprint.group uu____5196))
end
| uu____5206 -> begin
(p_Tm e)
end))
and p_tmFormula : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5208}, (e1)::(e2)::[]) -> begin
(

let uu____5213 = (str "\\/")
in (

let uu____5214 = (p_tmFormula e1)
in (

let uu____5215 = (p_tmConjunction e2)
in (infix0 uu____5213 uu____5214 uu____5215))))
end
| uu____5216 -> begin
(p_tmConjunction e)
end))
and p_tmConjunction : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5218}, (e1)::(e2)::[]) -> begin
(

let uu____5223 = (str "/\\")
in (

let uu____5224 = (p_tmConjunction e1)
in (

let uu____5225 = (p_tmTuple e2)
in (infix0 uu____5223 uu____5224 uu____5225))))
end
| uu____5226 -> begin
(p_tmTuple e)
end))
and p_tmTuple : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_tmTuple' e e.FStar_Parser_AST.range))
and p_tmTuple' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (lid, args) when (is_tuple_constructor lid) -> begin
(

let uu____5243 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map uu____5243 (fun uu____5251 -> (match (uu____5251) with
| (e1, uu____5257) -> begin
(p_tmEq e1)
end)) args))
end
| uu____5258 -> begin
(p_tmEq e)
end))
and paren_if_gt : Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun curr mine doc1 -> (match ((mine <= curr)) with
| true -> begin
doc1
end
| uu____5262 -> begin
(

let uu____5263 = (

let uu____5264 = (FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5264))
in (FStar_Pprint.group uu____5263))
end))
and p_tmEqWith : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_X e -> (

let n1 = (max_level (FStar_List.append ((colon_equals)::(pipe_right)::[]) operatorInfix0ad12))
in (p_tmEqWith' p_X n1 e)))
and p_tmEqWith' : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_X curr e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (((is_operatorInfix0ad12 op) || (

let uu____5305 = (FStar_Ident.text_of_id op)
in (Prims.op_Equality uu____5305 "="))) || (

let uu____5307 = (FStar_Ident.text_of_id op)
in (Prims.op_Equality uu____5307 "|>"))) -> begin
(

let op1 = (FStar_Ident.text_of_id op)
in (

let uu____5309 = (levels op1)
in (match (uu____5309) with
| (left1, mine, right1) -> begin
(

let uu____5319 = (

let uu____5320 = (FStar_All.pipe_left str op1)
in (

let uu____5321 = (p_tmEqWith' p_X left1 e1)
in (

let uu____5322 = (p_tmEqWith' p_X right1 e2)
in (infix0 uu____5320 uu____5321 uu____5322))))
in (paren_if_gt curr mine uu____5319))
end)))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5323}, (e1)::(e2)::[]) -> begin
(

let uu____5328 = (

let uu____5329 = (p_tmEqWith p_X e1)
in (

let uu____5330 = (

let uu____5331 = (

let uu____5332 = (

let uu____5333 = (p_tmEqWith p_X e2)
in (op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5333))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5332))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5331))
in (FStar_Pprint.op_Hat_Hat uu____5329 uu____5330)))
in (FStar_Pprint.group uu____5328))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5334}, (e1)::[]) -> begin
(

let uu____5338 = (levels "-")
in (match (uu____5338) with
| (left1, mine, right1) -> begin
(

let uu____5348 = (p_tmEqWith' p_X mine e1)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5348))
end))
end
| uu____5349 -> begin
(p_tmNoEqWith p_X e)
end))
and p_tmNoEqWith : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_X e -> (

let n1 = (max_level ((colon_colon)::(amp)::(opinfix3)::(opinfix4)::[]))
in (p_tmNoEqWith' p_X n1 e)))
and p_tmNoEqWith' : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_X curr e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (lid, ((e1, uu____5392))::((e2, uu____5394))::[]) when ((FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) && (

let uu____5414 = (is_list e)
in (not (uu____5414)))) -> begin
(

let op = "::"
in (

let uu____5416 = (levels op)
in (match (uu____5416) with
| (left1, mine, right1) -> begin
(

let uu____5426 = (

let uu____5427 = (str op)
in (

let uu____5428 = (p_tmNoEqWith' p_X left1 e1)
in (

let uu____5429 = (p_tmNoEqWith' p_X right1 e2)
in (infix0 uu____5427 uu____5428 uu____5429))))
in (paren_if_gt curr mine uu____5426))
end)))
end
| FStar_Parser_AST.Sum (binders, res) -> begin
(

let op = "&"
in (

let uu____5437 = (levels op)
in (match (uu____5437) with
| (left1, mine, right1) -> begin
(

let p_dsumfst = (fun b -> (

let uu____5453 = (p_binder false b)
in (

let uu____5454 = (

let uu____5455 = (

let uu____5456 = (str op)
in (FStar_Pprint.op_Hat_Hat uu____5456 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5455))
in (FStar_Pprint.op_Hat_Hat uu____5453 uu____5454))))
in (

let uu____5457 = (

let uu____5458 = (FStar_Pprint.concat_map p_dsumfst binders)
in (

let uu____5459 = (p_tmNoEqWith' p_X right1 res)
in (FStar_Pprint.op_Hat_Hat uu____5458 uu____5459)))
in (paren_if_gt curr mine uu____5457)))
end)))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (is_operatorInfix34 op) -> begin
(

let op1 = (FStar_Ident.text_of_id op)
in (

let uu____5466 = (levels op1)
in (match (uu____5466) with
| (left1, mine, right1) -> begin
(

let uu____5476 = (

let uu____5477 = (str op1)
in (

let uu____5478 = (p_tmNoEqWith' p_X left1 e1)
in (

let uu____5479 = (p_tmNoEqWith' p_X right1 e2)
in (infix0 uu____5477 uu____5478 uu____5479))))
in (paren_if_gt curr mine uu____5476))
end)))
end
| FStar_Parser_AST.Record (with_opt, record_fields) -> begin
(

let uu____5498 = (

let uu____5499 = (default_or_map FStar_Pprint.empty p_with_clause with_opt)
in (

let uu____5500 = (

let uu____5501 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (separate_map_last uu____5501 p_simpleDef record_fields))
in (FStar_Pprint.op_Hat_Hat uu____5499 uu____5500)))
in (braces_with_nesting uu____5498))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____5506}, (e1)::[]) -> begin
(

let uu____5510 = (

let uu____5511 = (str "~")
in (

let uu____5512 = (p_atomicTerm e1)
in (FStar_Pprint.op_Hat_Hat uu____5511 uu____5512)))
in (FStar_Pprint.group uu____5510))
end
| uu____5513 -> begin
(p_X e)
end))
and p_tmEqNoRefinement : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_tmEqWith p_appTerm e))
and p_tmEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_tmEqWith p_tmRefinement e))
and p_tmNoEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_tmNoEqWith p_tmRefinement e))
and p_tmRefinement : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.NamedTyp (lid, e1) -> begin
(

let uu____5520 = (

let uu____5521 = (p_lidentOrUnderscore lid)
in (

let uu____5522 = (

let uu____5523 = (p_appTerm e1)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5523))
in (FStar_Pprint.op_Hat_Slash_Hat uu____5521 uu____5522)))
in (FStar_Pprint.group uu____5520))
end
| FStar_Parser_AST.Refine (b, phi) -> begin
(p_refinedBinder b phi)
end
| uu____5526 -> begin
(p_appTerm e)
end))
and p_with_clause : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____5528 = (p_appTerm e)
in (

let uu____5529 = (

let uu____5530 = (

let uu____5531 = (str "with")
in (FStar_Pprint.op_Hat_Hat uu____5531 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5530))
in (FStar_Pprint.op_Hat_Hat uu____5528 uu____5529))))
and p_refinedBinder : FStar_Parser_AST.binder  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun b phi -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (lid, t) -> begin
(

let uu____5536 = (

let uu____5537 = (p_lident lid)
in (p_refinement b.FStar_Parser_AST.aqual uu____5537 t phi))
in (soft_parens_with_nesting uu____5536))
end
| FStar_Parser_AST.TAnnotated (uu____5538) -> begin
(failwith "Is this still used ?")
end
| FStar_Parser_AST.Variable (uu____5543) -> begin
(

let uu____5544 = (

let uu____5545 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" uu____5545))
in (failwith uu____5544))
end
| FStar_Parser_AST.TVariable (uu____5546) -> begin
(

let uu____5547 = (

let uu____5548 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" uu____5548))
in (failwith uu____5547))
end
| FStar_Parser_AST.NoName (uu____5549) -> begin
(

let uu____5550 = (

let uu____5551 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" uu____5551))
in (failwith uu____5550))
end))
and p_simpleDef : Prims.bool  ->  (FStar_Ident.lid * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun ps uu____5553 -> (match (uu____5553) with
| (lid, e) -> begin
(

let uu____5560 = (

let uu____5561 = (p_qlident lid)
in (

let uu____5562 = (

let uu____5563 = (p_noSeqTerm ps false e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____5563))
in (FStar_Pprint.op_Hat_Slash_Hat uu____5561 uu____5562)))
in (FStar_Pprint.group uu____5560))
end))
and p_appTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App (uu____5565) when (is_general_application e) -> begin
(

let uu____5572 = (head_and_args e)
in (match (uu____5572) with
| (head1, args) -> begin
(

let uu____5597 = (

let uu____5608 = (FStar_ST.op_Bang should_print_fs_typ_app)
in (match (uu____5608) with
| true -> begin
(

let uu____5642 = (FStar_Util.take (fun uu____5666 -> (match (uu____5666) with
| (uu____5671, aq) -> begin
(Prims.op_Equality aq FStar_Parser_AST.FsTypApp)
end)) args)
in (match (uu____5642) with
| (fs_typ_args, args1) -> begin
(

let uu____5709 = (

let uu____5710 = (p_indexingTerm head1)
in (

let uu____5711 = (

let uu____5712 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (soft_surround_map_or_flow (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.empty FStar_Pprint.langle uu____5712 FStar_Pprint.rangle p_fsTypArg fs_typ_args))
in (FStar_Pprint.op_Hat_Hat uu____5710 uu____5711)))
in ((uu____5709), (args1)))
end))
end
| uu____5723 -> begin
(

let uu____5724 = (p_indexingTerm head1)
in ((uu____5724), (args)))
end))
in (match (uu____5597) with
| (head_doc, args1) -> begin
(

let uu____5745 = (

let uu____5746 = (FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space)
in (soft_surround_map_or_flow (Prims.parse_int "2") (Prims.parse_int "0") head_doc uu____5746 break1 FStar_Pprint.empty p_argTerm args1))
in (FStar_Pprint.group uu____5745))
end))
end))
end
| FStar_Parser_AST.Construct (lid, args) when ((is_general_construction e) && (

let uu____5766 = (is_dtuple_constructor lid)
in (not (uu____5766)))) -> begin
(match (args) with
| [] -> begin
(p_quident lid)
end
| (arg)::[] -> begin
(

let uu____5784 = (

let uu____5785 = (p_quident lid)
in (

let uu____5786 = (p_argTerm arg)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5785 uu____5786)))
in (FStar_Pprint.group uu____5784))
end
| (hd1)::tl1 -> begin
(

let uu____5803 = (

let uu____5804 = (

let uu____5805 = (

let uu____5806 = (p_quident lid)
in (

let uu____5807 = (p_argTerm hd1)
in (prefix2 uu____5806 uu____5807)))
in (FStar_Pprint.group uu____5805))
in (

let uu____5808 = (

let uu____5809 = (FStar_Pprint.separate_map break1 p_argTerm tl1)
in (jump2 uu____5809))
in (FStar_Pprint.op_Hat_Hat uu____5804 uu____5808)))
in (FStar_Pprint.group uu____5803))
end)
end
| uu____5814 -> begin
(p_indexingTerm e)
end))
and p_argTerm : (FStar_Parser_AST.term * FStar_Parser_AST.imp)  ->  FStar_Pprint.document = (fun arg_imp -> (match (arg_imp) with
| (u, FStar_Parser_AST.UnivApp) -> begin
(p_universe u)
end
| (e, FStar_Parser_AST.FsTypApp) -> begin
((FStar_Errors.log_issue e.FStar_Parser_AST.range ((FStar_Errors.Warning_UnexpectedFsTypApp), ("Unexpected FsTypApp, output might not be formatted correctly.")));
(

let uu____5823 = (p_indexingTerm e)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.langle uu____5823 FStar_Pprint.rangle));
)
end
| (e, FStar_Parser_AST.Hash) -> begin
(

let uu____5825 = (str "#")
in (

let uu____5826 = (p_indexingTerm e)
in (FStar_Pprint.op_Hat_Hat uu____5825 uu____5826)))
end
| (e, FStar_Parser_AST.Nothing) -> begin
(p_indexingTerm e)
end))
and p_fsTypArg : (FStar_Parser_AST.term * FStar_Parser_AST.imp)  ->  FStar_Pprint.document = (fun uu____5828 -> (match (uu____5828) with
| (e, uu____5834) -> begin
(p_indexingTerm e)
end))
and p_indexingTerm_aux : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun exit1 e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____5839}, (e1)::(e2)::[]) -> begin
(

let uu____5844 = (

let uu____5845 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (

let uu____5846 = (

let uu____5847 = (

let uu____5848 = (p_term false false e2)
in (soft_parens_with_nesting uu____5848))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5847))
in (FStar_Pprint.op_Hat_Hat uu____5845 uu____5846)))
in (FStar_Pprint.group uu____5844))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____5849}, (e1)::(e2)::[]) -> begin
(

let uu____5854 = (

let uu____5855 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (

let uu____5856 = (

let uu____5857 = (

let uu____5858 = (p_term false false e2)
in (soft_brackets_with_nesting uu____5858))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5857))
in (FStar_Pprint.op_Hat_Hat uu____5855 uu____5856)))
in (FStar_Pprint.group uu____5854))
end
| uu____5859 -> begin
(exit1 e)
end))
and p_indexingTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_indexingTerm_aux p_atomicTerm e))
and p_atomicTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.LetOpen (lid, e1) -> begin
(

let uu____5864 = (p_quident lid)
in (

let uu____5865 = (

let uu____5866 = (

let uu____5867 = (p_term false false e1)
in (soft_parens_with_nesting uu____5867))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5866))
in (FStar_Pprint.op_Hat_Hat uu____5864 uu____5865)))
end
| FStar_Parser_AST.Name (lid) -> begin
(p_quident lid)
end
| FStar_Parser_AST.Op (op, (e1)::[]) when (is_general_prefix_op op) -> begin
(

let uu____5873 = (

let uu____5874 = (FStar_Ident.text_of_id op)
in (str uu____5874))
in (

let uu____5875 = (p_atomicTerm e1)
in (FStar_Pprint.op_Hat_Hat uu____5873 uu____5875)))
end
| uu____5876 -> begin
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
| uu____5883 -> begin
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

let uu____5890 = (

let uu____5891 = (FStar_Ident.text_of_id op)
in (str uu____5891))
in (

let uu____5892 = (p_atomicTermNotQUident e1)
in (FStar_Pprint.op_Hat_Hat uu____5890 uu____5892)))
end
| FStar_Parser_AST.Op (op, []) -> begin
(

let uu____5896 = (

let uu____5897 = (

let uu____5898 = (

let uu____5899 = (FStar_Ident.text_of_id op)
in (str uu____5899))
in (

let uu____5900 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat uu____5898 uu____5900)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5897))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5896))
end
| FStar_Parser_AST.Construct (lid, args) when (is_dtuple_constructor lid) -> begin
(

let uu____5915 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (

let uu____5916 = (

let uu____5917 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (

let uu____5918 = (FStar_List.map FStar_Pervasives_Native.fst args)
in (FStar_Pprint.separate_map uu____5917 p_tmEq uu____5918)))
in (

let uu____5925 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____5915 uu____5916 uu____5925))))
end
| FStar_Parser_AST.Project (e1, lid) -> begin
(

let uu____5928 = (

let uu____5929 = (p_atomicTermNotQUident e1)
in (

let uu____5930 = (

let uu____5931 = (p_qlident lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5931))
in (FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0") uu____5929 uu____5930)))
in (FStar_Pprint.group uu____5928))
end
| uu____5932 -> begin
(p_projectionLHS e)
end))
and p_projectionLHS : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (lid) -> begin
(p_qlident lid)
end
| FStar_Parser_AST.Projector (constr_lid, field_lid) -> begin
(

let uu____5937 = (p_quident constr_lid)
in (

let uu____5938 = (

let uu____5939 = (

let uu____5940 = (p_lident field_lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5940))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____5939))
in (FStar_Pprint.op_Hat_Hat uu____5937 uu____5938)))
end
| FStar_Parser_AST.Discrim (constr_lid) -> begin
(

let uu____5942 = (p_quident constr_lid)
in (FStar_Pprint.op_Hat_Hat uu____5942 FStar_Pprint.qmark))
end
| FStar_Parser_AST.Paren (e1) -> begin
(

let uu____5944 = (p_term false false e1)
in (soft_parens_with_nesting uu____5944))
end
| uu____5945 when (is_array e) -> begin
(

let es = (extract_from_list e)
in (

let uu____5949 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar)
in (

let uu____5950 = (

let uu____5951 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (separate_map_or_flow_last uu____5951 (fun ps -> (p_noSeqTerm ps false)) es))
in (

let uu____5954 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") uu____5949 uu____5950 uu____5954)))))
end
| uu____5955 when (is_list e) -> begin
(

let uu____5956 = (

let uu____5957 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (

let uu____5958 = (extract_from_list e)
in (separate_map_or_flow_last uu____5957 (fun ps -> (p_noSeqTerm ps false)) uu____5958)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket uu____5956 FStar_Pprint.rbracket))
end
| uu____5963 when (is_lex_list e) -> begin
(

let uu____5964 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket)
in (

let uu____5965 = (

let uu____5966 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (

let uu____5967 = (extract_from_list e)
in (separate_map_or_flow_last uu____5966 (fun ps -> (p_noSeqTerm ps false)) uu____5967)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____5964 uu____5965 FStar_Pprint.rbracket)))
end
| uu____5972 when (is_ref_set e) -> begin
(

let es = (extract_from_ref_set e)
in (

let uu____5976 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace)
in (

let uu____5977 = (

let uu____5978 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (separate_map_or_flow uu____5978 p_appTerm es))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") uu____5976 uu____5977 FStar_Pprint.rbrace))))
end
| FStar_Parser_AST.Labeled (e1, s, b) -> begin
(

let uu____5982 = (str (Prims.strcat "(*" (Prims.strcat s "*)")))
in (

let uu____5983 = (p_term false false e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5982 uu____5983)))
end
| FStar_Parser_AST.Op (op, args) when (

let uu____5990 = (handleable_op op args)
in (not (uu____5990))) -> begin
(

let uu____5991 = (

let uu____5992 = (

let uu____5993 = (FStar_Ident.text_of_id op)
in (

let uu____5994 = (

let uu____5995 = (

let uu____5996 = (FStar_Util.string_of_int (FStar_List.length args))
in (Prims.strcat uu____5996 " arguments couldn\'t be handled by the pretty printer"))
in (Prims.strcat " with " uu____5995))
in (Prims.strcat uu____5993 uu____5994)))
in (Prims.strcat "Operation " uu____5992))
in (failwith uu____5991))
end
| FStar_Parser_AST.Uvar (id1) -> begin
(

let uu____5998 = (str "u#")
in (

let uu____5999 = (str id1.FStar_Ident.idText)
in (FStar_Pprint.op_Hat_Hat uu____5998 uu____5999)))
end
| FStar_Parser_AST.Wild -> begin
(

let uu____6000 = (p_term false false e)
in (soft_parens_with_nesting uu____6000))
end
| FStar_Parser_AST.Const (uu____6001) -> begin
(

let uu____6002 = (p_term false false e)
in (soft_parens_with_nesting uu____6002))
end
| FStar_Parser_AST.Op (uu____6003) -> begin
(

let uu____6010 = (p_term false false e)
in (soft_parens_with_nesting uu____6010))
end
| FStar_Parser_AST.Tvar (uu____6011) -> begin
(

let uu____6012 = (p_term false false e)
in (soft_parens_with_nesting uu____6012))
end
| FStar_Parser_AST.Var (uu____6013) -> begin
(

let uu____6014 = (p_term false false e)
in (soft_parens_with_nesting uu____6014))
end
| FStar_Parser_AST.Name (uu____6015) -> begin
(

let uu____6016 = (p_term false false e)
in (soft_parens_with_nesting uu____6016))
end
| FStar_Parser_AST.Construct (uu____6017) -> begin
(

let uu____6028 = (p_term false false e)
in (soft_parens_with_nesting uu____6028))
end
| FStar_Parser_AST.Abs (uu____6029) -> begin
(

let uu____6036 = (p_term false false e)
in (soft_parens_with_nesting uu____6036))
end
| FStar_Parser_AST.App (uu____6037) -> begin
(

let uu____6044 = (p_term false false e)
in (soft_parens_with_nesting uu____6044))
end
| FStar_Parser_AST.Let (uu____6045) -> begin
(

let uu____6066 = (p_term false false e)
in (soft_parens_with_nesting uu____6066))
end
| FStar_Parser_AST.LetOpen (uu____6067) -> begin
(

let uu____6072 = (p_term false false e)
in (soft_parens_with_nesting uu____6072))
end
| FStar_Parser_AST.Seq (uu____6073) -> begin
(

let uu____6078 = (p_term false false e)
in (soft_parens_with_nesting uu____6078))
end
| FStar_Parser_AST.Bind (uu____6079) -> begin
(

let uu____6086 = (p_term false false e)
in (soft_parens_with_nesting uu____6086))
end
| FStar_Parser_AST.If (uu____6087) -> begin
(

let uu____6094 = (p_term false false e)
in (soft_parens_with_nesting uu____6094))
end
| FStar_Parser_AST.Match (uu____6095) -> begin
(

let uu____6110 = (p_term false false e)
in (soft_parens_with_nesting uu____6110))
end
| FStar_Parser_AST.TryWith (uu____6111) -> begin
(

let uu____6126 = (p_term false false e)
in (soft_parens_with_nesting uu____6126))
end
| FStar_Parser_AST.Ascribed (uu____6127) -> begin
(

let uu____6136 = (p_term false false e)
in (soft_parens_with_nesting uu____6136))
end
| FStar_Parser_AST.Record (uu____6137) -> begin
(

let uu____6150 = (p_term false false e)
in (soft_parens_with_nesting uu____6150))
end
| FStar_Parser_AST.Project (uu____6151) -> begin
(

let uu____6156 = (p_term false false e)
in (soft_parens_with_nesting uu____6156))
end
| FStar_Parser_AST.Product (uu____6157) -> begin
(

let uu____6164 = (p_term false false e)
in (soft_parens_with_nesting uu____6164))
end
| FStar_Parser_AST.Sum (uu____6165) -> begin
(

let uu____6172 = (p_term false false e)
in (soft_parens_with_nesting uu____6172))
end
| FStar_Parser_AST.QForall (uu____6173) -> begin
(

let uu____6186 = (p_term false false e)
in (soft_parens_with_nesting uu____6186))
end
| FStar_Parser_AST.QExists (uu____6187) -> begin
(

let uu____6200 = (p_term false false e)
in (soft_parens_with_nesting uu____6200))
end
| FStar_Parser_AST.Refine (uu____6201) -> begin
(

let uu____6206 = (p_term false false e)
in (soft_parens_with_nesting uu____6206))
end
| FStar_Parser_AST.NamedTyp (uu____6207) -> begin
(

let uu____6212 = (p_term false false e)
in (soft_parens_with_nesting uu____6212))
end
| FStar_Parser_AST.Requires (uu____6213) -> begin
(

let uu____6220 = (p_term false false e)
in (soft_parens_with_nesting uu____6220))
end
| FStar_Parser_AST.Ensures (uu____6221) -> begin
(

let uu____6228 = (p_term false false e)
in (soft_parens_with_nesting uu____6228))
end
| FStar_Parser_AST.Attributes (uu____6229) -> begin
(

let uu____6232 = (p_term false false e)
in (soft_parens_with_nesting uu____6232))
end
| FStar_Parser_AST.Quote (uu____6233) -> begin
(

let uu____6238 = (p_term false false e)
in (soft_parens_with_nesting uu____6238))
end
| FStar_Parser_AST.VQuote (uu____6239) -> begin
(

let uu____6240 = (p_term false false e)
in (soft_parens_with_nesting uu____6240))
end
| FStar_Parser_AST.Antiquote (uu____6241) -> begin
(

let uu____6246 = (p_term false false e)
in (soft_parens_with_nesting uu____6246))
end))
and p_constant : FStar_Const.sconst  ->  FStar_Pprint.document = (fun uu___69_6247 -> (match (uu___69_6247) with
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

let uu____6251 = (FStar_Pprint.doc_of_char x)
in (FStar_Pprint.squotes uu____6251))
end
| FStar_Const.Const_string (s, uu____6253) -> begin
(

let uu____6254 = (str s)
in (FStar_Pprint.dquotes uu____6254))
end
| FStar_Const.Const_bytearray (bytes, uu____6256) -> begin
(

let uu____6261 = (

let uu____6262 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes uu____6262))
in (

let uu____6263 = (str "B")
in (FStar_Pprint.op_Hat_Hat uu____6261 uu____6263)))
end
| FStar_Const.Const_int (repr, sign_width_opt) -> begin
(

let signedness = (fun uu___67_6283 -> (match (uu___67_6283) with
| FStar_Const.Unsigned -> begin
(str "u")
end
| FStar_Const.Signed -> begin
FStar_Pprint.empty
end))
in (

let width = (fun uu___68_6289 -> (match (uu___68_6289) with
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

let ending = (default_or_map FStar_Pprint.empty (fun uu____6300 -> (match (uu____6300) with
| (s, w) -> begin
(

let uu____6307 = (signedness s)
in (

let uu____6308 = (width w)
in (FStar_Pprint.op_Hat_Hat uu____6307 uu____6308)))
end)) sign_width_opt)
in (

let uu____6309 = (str repr)
in (FStar_Pprint.op_Hat_Hat uu____6309 ending)))))
end
| FStar_Const.Const_range_of -> begin
(str "range_of")
end
| FStar_Const.Const_set_range_of -> begin
(str "set_range_of")
end
| FStar_Const.Const_range (r) -> begin
(

let uu____6311 = (FStar_Range.string_of_range r)
in (str uu____6311))
end
| FStar_Const.Const_reify -> begin
(str "reify")
end
| FStar_Const.Const_reflect (lid) -> begin
(

let uu____6313 = (p_quident lid)
in (

let uu____6314 = (

let uu____6315 = (

let uu____6316 = (str "reflect")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6316))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6315))
in (FStar_Pprint.op_Hat_Hat uu____6313 uu____6314)))
end))
and p_universe : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (

let uu____6318 = (str "u#")
in (

let uu____6319 = (p_atomicUniverse u)
in (FStar_Pprint.op_Hat_Hat uu____6318 uu____6319))))
and p_universeFrom : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match (u.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6321}, (u1)::(u2)::[]) -> begin
(

let uu____6326 = (

let uu____6327 = (p_universeFrom u1)
in (

let uu____6328 = (

let uu____6329 = (p_universeFrom u2)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6329))
in (FStar_Pprint.op_Hat_Slash_Hat uu____6327 uu____6328)))
in (FStar_Pprint.group uu____6326))
end
| FStar_Parser_AST.App (uu____6330) -> begin
(

let uu____6337 = (head_and_args u)
in (match (uu____6337) with
| (head1, args) -> begin
(match (head1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (maybe_max_lid) when (FStar_Ident.lid_equals maybe_max_lid FStar_Parser_Const.max_lid) -> begin
(

let uu____6363 = (

let uu____6364 = (p_qlident FStar_Parser_Const.max_lid)
in (

let uu____6365 = (FStar_Pprint.separate_map FStar_Pprint.space (fun uu____6373 -> (match (uu____6373) with
| (u1, uu____6379) -> begin
(p_atomicUniverse u1)
end)) args)
in (op_Hat_Slash_Plus_Hat uu____6364 uu____6365)))
in (FStar_Pprint.group uu____6363))
end
| uu____6380 -> begin
(

let uu____6381 = (

let uu____6382 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" uu____6382))
in (failwith uu____6381))
end)
end))
end
| uu____6383 -> begin
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

let uu____6406 = (FStar_Ident.text_of_id id1)
in (str uu____6406))
end
| FStar_Parser_AST.Paren (u1) -> begin
(

let uu____6408 = (p_universeFrom u1)
in (soft_parens_with_nesting uu____6408))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6409}, (uu____6410)::(uu____6411)::[]) -> begin
(

let uu____6414 = (p_universeFrom u)
in (soft_parens_with_nesting uu____6414))
end
| FStar_Parser_AST.App (uu____6415) -> begin
(

let uu____6422 = (p_universeFrom u)
in (soft_parens_with_nesting uu____6422))
end
| uu____6423 -> begin
(

let uu____6424 = (

let uu____6425 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" uu____6425))
in (failwith uu____6424))
end))


let term_to_document : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_term false false e))


let signature_to_document : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun e -> (p_justSig e))


let decl_to_document : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun e -> (p_decl e))


let pat_to_document : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (p_disjunctivePattern p))


let binder_to_document : FStar_Parser_AST.binder  ->  FStar_Pprint.document = (fun b -> (p_binder true b))


let modul_to_document : FStar_Parser_AST.modul  ->  FStar_Pprint.document = (fun m -> ((FStar_ST.op_Colon_Equals should_print_fs_typ_app false);
(

let res = (match (m) with
| FStar_Parser_AST.Module (uu____6481, decls) -> begin
(

let uu____6487 = (FStar_All.pipe_right decls (FStar_List.map decl_to_document))
in (FStar_All.pipe_right uu____6487 (FStar_Pprint.separate FStar_Pprint.hardline)))
end
| FStar_Parser_AST.Interface (uu____6496, decls, uu____6498) -> begin
(

let uu____6503 = (FStar_All.pipe_right decls (FStar_List.map decl_to_document))
in (FStar_All.pipe_right uu____6503 (FStar_Pprint.separate FStar_Pprint.hardline)))
end)
in ((FStar_ST.op_Colon_Equals should_print_fs_typ_app false);
res;
));
))


let comments_to_document : (Prims.string * FStar_Range.range) Prims.list  ->  FStar_Pprint.document = (fun comments -> (FStar_Pprint.separate_map FStar_Pprint.hardline (fun uu____6560 -> (match (uu____6560) with
| (comment, range) -> begin
(str comment)
end)) comments))


let modul_with_comments_to_document : FStar_Parser_AST.modul  ->  (Prims.string * FStar_Range.range) Prims.list  ->  (FStar_Pprint.document * (Prims.string * FStar_Range.range) Prims.list) = (fun m comments -> (

let decls = (match (m) with
| FStar_Parser_AST.Module (uu____6604, decls) -> begin
decls
end
| FStar_Parser_AST.Interface (uu____6610, decls, uu____6612) -> begin
decls
end)
in ((FStar_ST.op_Colon_Equals should_print_fs_typ_app false);
(match (decls) with
| [] -> begin
((FStar_Pprint.empty), (comments))
end
| (d)::ds -> begin
(

let uu____6661 = (match (ds) with
| ({FStar_Parser_AST.d = FStar_Parser_AST.Pragma (FStar_Parser_AST.LightOff); FStar_Parser_AST.drange = uu____6674; FStar_Parser_AST.doc = uu____6675; FStar_Parser_AST.quals = uu____6676; FStar_Parser_AST.attrs = uu____6677})::uu____6678 -> begin
(

let d0 = (FStar_List.hd ds)
in (

let uu____6684 = (

let uu____6687 = (

let uu____6690 = (FStar_List.tl ds)
in (d)::uu____6690)
in (d0)::uu____6687)
in ((uu____6684), (d0.FStar_Parser_AST.drange))))
end
| uu____6695 -> begin
(((d)::ds), (d.FStar_Parser_AST.drange))
end)
in (match (uu____6661) with
| (decls1, first_range) -> begin
(

let extract_decl_range = (fun d1 -> d1.FStar_Parser_AST.drange)
in ((FStar_ST.op_Colon_Equals comment_stack comments);
(

let initial_comment = (

let uu____6759 = (FStar_Range.start_of_range first_range)
in (place_comments_until_pos (Prims.parse_int "0") (Prims.parse_int "1") uu____6759 FStar_Pprint.empty))
in (

let doc1 = (separate_map_with_comments FStar_Pprint.empty FStar_Pprint.empty decl_to_document decls1 extract_decl_range)
in (

let comments1 = (FStar_ST.op_Bang comment_stack)
in ((FStar_ST.op_Colon_Equals comment_stack []);
(FStar_ST.op_Colon_Equals should_print_fs_typ_app false);
(

let uu____6867 = (FStar_Pprint.op_Hat_Hat initial_comment doc1)
in ((uu____6867), (comments1)));
))));
))
end))
end);
)))




