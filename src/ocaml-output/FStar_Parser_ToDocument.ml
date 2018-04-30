
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

let uu____1046 = (FStar_Ident.text_of_id op)
in (Prims.op_disEquality uu____1046 "~"))))))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun e -> (

let rec aux = (fun e1 acc -> (match (e1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App (head1, arg, imp) -> begin
(aux head1 ((((arg), (imp)))::acc))
end
| uu____1112 -> begin
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
| uu____1128 -> begin
false
end))


let uu___is_Right : associativity  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Right -> begin
true
end
| uu____1134 -> begin
false
end))


let uu___is_NonAssoc : associativity  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NonAssoc -> begin
true
end
| uu____1140 -> begin
false
end))


type token =
(FStar_Char.char, Prims.string) FStar_Util.either


type associativity_level =
(associativity * token Prims.list)


let token_to_string : (FStar_BaseTypes.char, Prims.string) FStar_Util.either  ->  Prims.string = (fun uu___54_1160 -> (match (uu___54_1160) with
| FStar_Util.Inl (c) -> begin
(Prims.strcat (FStar_Util.string_of_char c) ".*")
end
| FStar_Util.Inr (s) -> begin
s
end))


let matches_token : Prims.string  ->  (FStar_Char.char, Prims.string) FStar_Util.either  ->  Prims.bool = (fun s uu___55_1181 -> (match (uu___55_1181) with
| FStar_Util.Inl (c) -> begin
(

let uu____1190 = (FStar_String.get s (Prims.parse_int "0"))
in (Prims.op_Equality uu____1190 c))
end
| FStar_Util.Inr (s') -> begin
(Prims.op_Equality s s')
end))


let matches_level : 'Auu____1201 . Prims.string  ->  ('Auu____1201 * (FStar_Char.char, Prims.string) FStar_Util.either Prims.list)  ->  Prims.bool = (fun s uu____1222 -> (match (uu____1222) with
| (assoc_levels, tokens) -> begin
(

let uu____1250 = (FStar_List.tryFind (matches_token s) tokens)
in (Prims.op_disEquality uu____1250 FStar_Pervasives_Native.None))
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

let levels_from_associativity = (fun l uu___56_1452 -> (match (uu___56_1452) with
| Left -> begin
((l), (l), ((l - (Prims.parse_int "1"))))
end
| Right -> begin
(((l - (Prims.parse_int "1"))), (l), (l))
end
| NonAssoc -> begin
(((l - (Prims.parse_int "1"))), (l), ((l - (Prims.parse_int "1"))))
end))
in (FStar_List.mapi (fun i uu____1482 -> (match (uu____1482) with
| (assoc1, tokens) -> begin
(((levels_from_associativity i assoc1)), (tokens))
end)) level_associativity_spec))


let assign_levels : associativity_level Prims.list  ->  Prims.string  ->  (Prims.int * Prims.int * Prims.int) = (fun token_associativity_spec s -> (

let uu____1541 = (FStar_List.tryFind (matches_level s) level_table)
in (match (uu____1541) with
| FStar_Pervasives_Native.Some (assoc_levels, uu____1581) -> begin
assoc_levels
end
| uu____1610 -> begin
(failwith (Prims.strcat "Unrecognized operator " s))
end)))


let max : Prims.int  ->  Prims.int  ->  Prims.int = (fun k1 k2 -> (match ((k1 > k2)) with
| true -> begin
k1
end
| uu____1641 -> begin
k2
end))


let max_level : 'Auu____1646 . ('Auu____1646 * token Prims.list) Prims.list  ->  Prims.int = (fun l -> (

let find_level_and_max = (fun n1 level -> (

let uu____1691 = (FStar_List.tryFind (fun uu____1721 -> (match (uu____1721) with
| (uu____1734, tokens) -> begin
(Prims.op_Equality tokens (FStar_Pervasives_Native.snd level))
end)) level_table)
in (match (uu____1691) with
| FStar_Pervasives_Native.Some ((uu____1756, l1, uu____1758), uu____1759) -> begin
(max n1 l1)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____1794 = (

let uu____1795 = (

let uu____1796 = (FStar_List.map token_to_string (FStar_Pervasives_Native.snd level))
in (FStar_String.concat "," uu____1796))
in (FStar_Util.format1 "Undefined associativity level %s" uu____1795))
in (failwith uu____1794))
end)))
in (FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l)))


let levels : Prims.string  ->  (Prims.int * Prims.int * Prims.int) = (fun op -> (

let uu____1818 = (assign_levels level_associativity_spec op)
in (match (uu____1818) with
| (left1, mine, right1) -> begin
(match ((Prims.op_Equality op "*")) with
| true -> begin
(((left1 - (Prims.parse_int "1"))), (mine), (right1))
end
| uu____1840 -> begin
((left1), (mine), (right1))
end)
end)))


let operatorInfix0ad12 : (associativity * token Prims.list) Prims.list = (opinfix0a)::(opinfix0b)::(opinfix0c)::(opinfix0d)::(opinfix1)::(opinfix2)::[]


let is_operatorInfix0ad12 : FStar_Ident.ident  ->  Prims.bool = (fun op -> (

let uu____1896 = (

let uu____1905 = (

let uu____1916 = (FStar_Ident.text_of_id op)
in (FStar_All.pipe_left matches_level uu____1916))
in (FStar_List.tryFind uu____1905 operatorInfix0ad12))
in (Prims.op_disEquality uu____1896 FStar_Pervasives_Native.None)))


let is_operatorInfix34 : FStar_Ident.ident  ->  Prims.bool = (

let opinfix34 = (opinfix3)::(opinfix4)::[]
in (fun op -> (

let uu____1998 = (

let uu____2012 = (

let uu____2028 = (FStar_Ident.text_of_id op)
in (FStar_All.pipe_left matches_level uu____2028))
in (FStar_List.tryFind uu____2012 opinfix34))
in (Prims.op_disEquality uu____1998 FStar_Pervasives_Native.None))))


let handleable_args_length : FStar_Ident.ident  ->  Prims.int = (fun op -> (

let op_s = (FStar_Ident.text_of_id op)
in (

let uu____2084 = ((is_general_prefix_op op) || (FStar_List.mem op_s (("-")::("~")::[])))
in (match (uu____2084) with
| true -> begin
(Prims.parse_int "1")
end
| uu____2085 -> begin
(

let uu____2086 = (((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) || (FStar_List.mem op_s (("<==>")::("==>")::("\\/")::("/\\")::("=")::("|>")::(":=")::(".()")::(".[]")::[])))
in (match (uu____2086) with
| true -> begin
(Prims.parse_int "2")
end
| uu____2087 -> begin
(match ((FStar_List.mem op_s ((".()<-")::(".[]<-")::[]))) with
| true -> begin
(Prims.parse_int "3")
end
| uu____2088 -> begin
(Prims.parse_int "0")
end)
end))
end))))


let handleable_op : 'Auu____2095 . FStar_Ident.ident  ->  'Auu____2095 Prims.list  ->  Prims.bool = (fun op args -> (match ((FStar_List.length args)) with
| _0_4 when (_0_4 = (Prims.parse_int "0")) -> begin
true
end
| _0_5 when (_0_5 = (Prims.parse_int "1")) -> begin
((is_general_prefix_op op) || (

let uu____2111 = (FStar_Ident.text_of_id op)
in (FStar_List.mem uu____2111 (("-")::("~")::[]))))
end
| _0_6 when (_0_6 = (Prims.parse_int "2")) -> begin
(((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) || (

let uu____2113 = (FStar_Ident.text_of_id op)
in (FStar_List.mem uu____2113 (("<==>")::("==>")::("\\/")::("/\\")::("=")::("|>")::(":=")::(".()")::(".[]")::[]))))
end
| _0_7 when (_0_7 = (Prims.parse_int "3")) -> begin
(

let uu____2114 = (FStar_Ident.text_of_id op)
in (FStar_List.mem uu____2114 ((".()<-")::(".[]<-")::[])))
end
| uu____2115 -> begin
false
end))


let comment_stack : (Prims.string * FStar_Range.range) Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let with_comment : 'Auu____2153 . ('Auu____2153  ->  FStar_Pprint.document)  ->  'Auu____2153  ->  FStar_Range.range  ->  FStar_Pprint.document = (fun printer tm tmrange -> (

let rec comments_before_pos = (fun acc print_pos lookahead_pos -> (

let uu____2194 = (FStar_ST.op_Bang comment_stack)
in (match (uu____2194) with
| [] -> begin
((acc), (false))
end
| ((comment, crange))::cs -> begin
(

let uu____2257 = (FStar_Range.range_before_pos crange print_pos)
in (match (uu____2257) with
| true -> begin
((FStar_ST.op_Colon_Equals comment_stack cs);
(

let uu____2298 = (

let uu____2299 = (

let uu____2300 = (str comment)
in (FStar_Pprint.op_Hat_Hat uu____2300 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat acc uu____2299))
in (comments_before_pos uu____2298 print_pos lookahead_pos));
)
end
| uu____2301 -> begin
(

let uu____2302 = (FStar_Range.range_before_pos crange lookahead_pos)
in ((acc), (uu____2302)))
end))
end)))
in (

let uu____2303 = (

let uu____2308 = (

let uu____2309 = (FStar_Range.start_of_range tmrange)
in (FStar_Range.end_of_line uu____2309))
in (

let uu____2310 = (FStar_Range.end_of_range tmrange)
in (comments_before_pos FStar_Pprint.empty uu____2308 uu____2310)))
in (match (uu____2303) with
| (comments, has_lookahead) -> begin
(

let printed_e = (printer tm)
in (

let comments1 = (match (has_lookahead) with
| true -> begin
(

let pos = (FStar_Range.end_of_range tmrange)
in (

let uu____2316 = (comments_before_pos comments pos pos)
in (FStar_Pervasives_Native.fst uu____2316)))
end
| uu____2321 -> begin
comments
end)
in (

let uu____2322 = (FStar_Pprint.op_Hat_Hat comments1 printed_e)
in (FStar_Pprint.group uu____2322))))
end))))


let rec place_comments_until_pos : Prims.int  ->  Prims.int  ->  FStar_Range.pos  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun k lbegin pos_end doc1 -> (

let uu____2343 = (FStar_ST.op_Bang comment_stack)
in (match (uu____2343) with
| ((comment, crange))::cs when (FStar_Range.range_before_pos crange pos_end) -> begin
((FStar_ST.op_Colon_Equals comment_stack cs);
(

let lnum = (

let uu____2435 = (

let uu____2436 = (

let uu____2437 = (FStar_Range.start_of_range crange)
in (FStar_Range.line_of_pos uu____2437))
in (uu____2436 - lbegin))
in (max k uu____2435))
in (

let doc2 = (

let uu____2439 = (

let uu____2440 = (FStar_Pprint.repeat lnum FStar_Pprint.hardline)
in (

let uu____2441 = (str comment)
in (FStar_Pprint.op_Hat_Hat uu____2440 uu____2441)))
in (FStar_Pprint.op_Hat_Hat doc1 uu____2439))
in (

let uu____2442 = (

let uu____2443 = (FStar_Range.end_of_range crange)
in (FStar_Range.line_of_pos uu____2443))
in (place_comments_until_pos (Prims.parse_int "1") uu____2442 pos_end doc2))));
)
end
| uu____2444 -> begin
(

let lnum = (

let uu____2452 = (

let uu____2453 = (FStar_Range.line_of_pos pos_end)
in (uu____2453 - lbegin))
in (max (Prims.parse_int "1") uu____2452))
in (

let uu____2454 = (FStar_Pprint.repeat lnum FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat doc1 uu____2454)))
end)))


let separate_map_with_comments : 'Auu____2467 . FStar_Pprint.document  ->  FStar_Pprint.document  ->  ('Auu____2467  ->  FStar_Pprint.document)  ->  'Auu____2467 Prims.list  ->  ('Auu____2467  ->  FStar_Range.range)  ->  FStar_Pprint.document = (fun prefix1 sep f xs extract_range -> (

let fold_fun = (fun uu____2524 x -> (match (uu____2524) with
| (last_line, doc1) -> begin
(

let r = (extract_range x)
in (

let doc2 = (

let uu____2538 = (FStar_Range.start_of_range r)
in (place_comments_until_pos (Prims.parse_int "1") last_line uu____2538 doc1))
in (

let uu____2539 = (

let uu____2540 = (FStar_Range.end_of_range r)
in (FStar_Range.line_of_pos uu____2540))
in (

let uu____2541 = (

let uu____2542 = (

let uu____2543 = (f x)
in (FStar_Pprint.op_Hat_Hat sep uu____2543))
in (FStar_Pprint.op_Hat_Hat doc2 uu____2542))
in ((uu____2539), (uu____2541))))))
end))
in (

let uu____2544 = (

let uu____2551 = (FStar_List.hd xs)
in (

let uu____2552 = (FStar_List.tl xs)
in ((uu____2551), (uu____2552))))
in (match (uu____2544) with
| (x, xs1) -> begin
(

let init1 = (

let uu____2568 = (

let uu____2569 = (

let uu____2570 = (extract_range x)
in (FStar_Range.end_of_range uu____2570))
in (FStar_Range.line_of_pos uu____2569))
in (

let uu____2571 = (

let uu____2572 = (f x)
in (FStar_Pprint.op_Hat_Hat prefix1 uu____2572))
in ((uu____2568), (uu____2571))))
in (

let uu____2573 = (FStar_List.fold_left fold_fun init1 xs1)
in (FStar_Pervasives_Native.snd uu____2573)))
end))))


let rec p_decl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (

let uu____3202 = (

let uu____3203 = (FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc)
in (

let uu____3204 = (

let uu____3205 = (p_attributes d.FStar_Parser_AST.attrs)
in (

let uu____3206 = (

let uu____3207 = (p_qualifiers d.FStar_Parser_AST.quals)
in (

let uu____3208 = (

let uu____3209 = (p_rawDecl d)
in (FStar_Pprint.op_Hat_Hat (match ((Prims.op_Equality d.FStar_Parser_AST.quals [])) with
| true -> begin
FStar_Pprint.empty
end
| uu____3212 -> begin
break1
end) uu____3209))
in (FStar_Pprint.op_Hat_Hat uu____3207 uu____3208)))
in (FStar_Pprint.op_Hat_Hat uu____3205 uu____3206)))
in (FStar_Pprint.op_Hat_Hat uu____3203 uu____3204)))
in (FStar_Pprint.group uu____3202)))
and p_attributes : FStar_Parser_AST.attributes_  ->  FStar_Pprint.document = (fun attrs -> (

let uu____3214 = (

let uu____3215 = (str "@")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3215))
in (

let uu____3216 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline)
in (soft_surround_map_or_flow (Prims.parse_int "0") (Prims.parse_int "2") FStar_Pprint.empty uu____3214 FStar_Pprint.space uu____3216 p_atomicTerm attrs))))
and p_fsdoc : FStar_Parser_AST.fsdoc  ->  FStar_Pprint.document = (fun uu____3217 -> (match (uu____3217) with
| (doc1, kwd_args) -> begin
(

let kwd_args_doc = (match (kwd_args) with
| [] -> begin
FStar_Pprint.empty
end
| kwd_args1 -> begin
(

let process_kwd_arg = (fun uu____3253 -> (match (uu____3253) with
| (kwd, arg) -> begin
(

let uu____3260 = (str "@")
in (

let uu____3261 = (

let uu____3262 = (str kwd)
in (

let uu____3263 = (

let uu____3264 = (str arg)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3264))
in (FStar_Pprint.op_Hat_Hat uu____3262 uu____3263)))
in (FStar_Pprint.op_Hat_Hat uu____3260 uu____3261)))
end))
in (

let uu____3265 = (

let uu____3266 = (FStar_Pprint.separate_map FStar_Pprint.hardline process_kwd_arg kwd_args1)
in (FStar_Pprint.op_Hat_Hat uu____3266 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3265)))
end)
in (

let uu____3271 = (

let uu____3272 = (

let uu____3273 = (

let uu____3274 = (

let uu____3275 = (str doc1)
in (

let uu____3276 = (

let uu____3277 = (

let uu____3278 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3278))
in (FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3277))
in (FStar_Pprint.op_Hat_Hat uu____3275 uu____3276)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3274))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3273))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3272))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3271)))
end))
and p_justSig : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (lid, t) -> begin
(

let uu____3282 = (

let uu____3283 = (str "val")
in (

let uu____3284 = (

let uu____3285 = (

let uu____3286 = (p_lident lid)
in (

let uu____3287 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat uu____3286 uu____3287)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3285))
in (FStar_Pprint.op_Hat_Hat uu____3283 uu____3284)))
in (

let uu____3288 = (p_typ false false t)
in (op_Hat_Slash_Plus_Hat uu____3282 uu____3288)))
end
| FStar_Parser_AST.TopLevelLet (uu____3289, lbs) -> begin
(FStar_Pprint.separate_map FStar_Pprint.hardline (fun lb -> (

let uu____3314 = (

let uu____3315 = (str "let")
in (

let uu____3316 = (p_letlhs lb)
in (FStar_Pprint.op_Hat_Slash_Hat uu____3315 uu____3316)))
in (FStar_Pprint.group uu____3314))) lbs)
end
| uu____3317 -> begin
FStar_Pprint.empty
end))
and p_list : (FStar_Ident.ident  ->  FStar_Pprint.document)  ->  FStar_Pprint.document  ->  FStar_Ident.ident Prims.list  ->  FStar_Pprint.document = (fun f sep l -> (

let rec p_list' = (fun uu___57_3332 -> (match (uu___57_3332) with
| [] -> begin
FStar_Pprint.empty
end
| (x)::[] -> begin
(f x)
end
| (x)::xs -> begin
(

let uu____3340 = (f x)
in (

let uu____3341 = (

let uu____3342 = (p_list' xs)
in (FStar_Pprint.op_Hat_Hat sep uu____3342))
in (FStar_Pprint.op_Hat_Hat uu____3340 uu____3341)))
end))
in (

let uu____3343 = (str "[")
in (

let uu____3344 = (

let uu____3345 = (p_list' l)
in (

let uu____3346 = (str "]")
in (FStar_Pprint.op_Hat_Hat uu____3345 uu____3346)))
in (FStar_Pprint.op_Hat_Hat uu____3343 uu____3344)))))
and p_rawDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Open (uid) -> begin
(

let uu____3349 = (

let uu____3350 = (str "open")
in (

let uu____3351 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat uu____3350 uu____3351)))
in (FStar_Pprint.group uu____3349))
end
| FStar_Parser_AST.Include (uid) -> begin
(

let uu____3353 = (

let uu____3354 = (str "include")
in (

let uu____3355 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat uu____3354 uu____3355)))
in (FStar_Pprint.group uu____3353))
end
| FStar_Parser_AST.ModuleAbbrev (uid1, uid2) -> begin
(

let uu____3358 = (

let uu____3359 = (str "module")
in (

let uu____3360 = (

let uu____3361 = (

let uu____3362 = (p_uident uid1)
in (

let uu____3363 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____3362 uu____3363)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3361))
in (FStar_Pprint.op_Hat_Hat uu____3359 uu____3360)))
in (

let uu____3364 = (p_quident uid2)
in (op_Hat_Slash_Plus_Hat uu____3358 uu____3364)))
end
| FStar_Parser_AST.TopLevelModule (uid) -> begin
(

let uu____3366 = (

let uu____3367 = (str "module")
in (

let uu____3368 = (

let uu____3369 = (p_quident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3369))
in (FStar_Pprint.op_Hat_Hat uu____3367 uu____3368)))
in (FStar_Pprint.group uu____3366))
end
| FStar_Parser_AST.Tycon (true, ((FStar_Parser_AST.TyconAbbrev (uid, tpars, FStar_Pervasives_Native.None, t), FStar_Pervasives_Native.None))::[]) -> begin
(

let effect_prefix_doc = (

let uu____3402 = (str "effect")
in (

let uu____3403 = (

let uu____3404 = (p_uident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3404))
in (FStar_Pprint.op_Hat_Hat uu____3402 uu____3403)))
in (

let uu____3405 = (

let uu____3406 = (p_typars tpars)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") effect_prefix_doc uu____3406 FStar_Pprint.equals))
in (

let uu____3407 = (p_typ false false t)
in (op_Hat_Slash_Plus_Hat uu____3405 uu____3407))))
end
| FStar_Parser_AST.Tycon (false, tcdefs) -> begin
(

let uu____3425 = (str "type")
in (

let uu____3426 = (str "and")
in (precede_break_separate_map uu____3425 uu____3426 p_fsdocTypeDeclPairs tcdefs)))
end
| FStar_Parser_AST.TopLevelLet (q, lbs) -> begin
(

let let_doc = (

let uu____3448 = (str "let")
in (

let uu____3449 = (

let uu____3450 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat uu____3450 FStar_Pprint.space))
in (FStar_Pprint.op_Hat_Hat uu____3448 uu____3449)))
in (

let uu____3451 = (

let uu____3452 = (str "and")
in (FStar_Pprint.op_Hat_Hat uu____3452 FStar_Pprint.space))
in (separate_map_with_comments let_doc uu____3451 p_letbinding lbs (fun uu____3460 -> (match (uu____3460) with
| (p, t) -> begin
(FStar_Range.union_ranges p.FStar_Parser_AST.prange t.FStar_Parser_AST.range)
end)))))
end
| FStar_Parser_AST.Val (lid, t) -> begin
(

let uu____3469 = (

let uu____3470 = (str "val")
in (

let uu____3471 = (

let uu____3472 = (

let uu____3473 = (p_lident lid)
in (

let uu____3474 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat uu____3473 uu____3474)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3472))
in (FStar_Pprint.op_Hat_Hat uu____3470 uu____3471)))
in (

let uu____3475 = (p_typ false false t)
in (op_Hat_Slash_Plus_Hat uu____3469 uu____3475)))
end
| FStar_Parser_AST.Assume (id1, t) -> begin
(

let decl_keyword = (

let uu____3479 = (

let uu____3480 = (FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_All.pipe_right uu____3480 FStar_Util.is_upper))
in (match (uu____3479) with
| true -> begin
FStar_Pprint.empty
end
| uu____3481 -> begin
(

let uu____3482 = (str "val")
in (FStar_Pprint.op_Hat_Hat uu____3482 FStar_Pprint.space))
end))
in (

let uu____3483 = (

let uu____3484 = (

let uu____3485 = (p_ident id1)
in (

let uu____3486 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat uu____3485 uu____3486)))
in (FStar_Pprint.op_Hat_Hat decl_keyword uu____3484))
in (

let uu____3487 = (p_typ false false t)
in (op_Hat_Slash_Plus_Hat uu____3483 uu____3487))))
end
| FStar_Parser_AST.Exception (uid, t_opt) -> begin
(

let uu____3494 = (str "exception")
in (

let uu____3495 = (

let uu____3496 = (

let uu____3497 = (p_uident uid)
in (

let uu____3498 = (FStar_Pprint.optional (fun t -> (

let uu____3502 = (

let uu____3503 = (str "of")
in (

let uu____3504 = (p_typ false false t)
in (op_Hat_Slash_Plus_Hat uu____3503 uu____3504)))
in (FStar_Pprint.op_Hat_Hat break1 uu____3502))) t_opt)
in (FStar_Pprint.op_Hat_Hat uu____3497 uu____3498)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3496))
in (FStar_Pprint.op_Hat_Hat uu____3494 uu____3495)))
end
| FStar_Parser_AST.NewEffect (ne) -> begin
(

let uu____3506 = (str "new_effect")
in (

let uu____3507 = (

let uu____3508 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3508))
in (FStar_Pprint.op_Hat_Hat uu____3506 uu____3507)))
end
| FStar_Parser_AST.SubEffect (se) -> begin
(

let uu____3510 = (str "sub_effect")
in (

let uu____3511 = (

let uu____3512 = (p_subEffect se)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3512))
in (FStar_Pprint.op_Hat_Hat uu____3510 uu____3511)))
end
| FStar_Parser_AST.Pragma (p) -> begin
(p_pragma p)
end
| FStar_Parser_AST.Fsdoc (doc1) -> begin
(

let uu____3515 = (p_fsdoc doc1)
in (FStar_Pprint.op_Hat_Hat uu____3515 FStar_Pprint.hardline))
end
| FStar_Parser_AST.Main (uu____3516) -> begin
(failwith "*Main declaration* : Is that really still in use ??")
end
| FStar_Parser_AST.Tycon (true, uu____3517) -> begin
(failwith "Effect abbreviation is expected to be defined by an abbreviation")
end
| FStar_Parser_AST.Splice (ids, t) -> begin
(

let uu____3540 = (str "%splice")
in (

let uu____3541 = (

let uu____3542 = (

let uu____3543 = (str ";")
in (p_list p_uident uu____3543 ids))
in (

let uu____3544 = (

let uu____3545 = (p_term false false t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3545))
in (FStar_Pprint.op_Hat_Hat uu____3542 uu____3544)))
in (FStar_Pprint.op_Hat_Hat uu____3540 uu____3541)))
end))
and p_pragma : FStar_Parser_AST.pragma  ->  FStar_Pprint.document = (fun uu___58_3546 -> (match (uu___58_3546) with
| FStar_Parser_AST.SetOptions (s) -> begin
(

let uu____3548 = (str "#set-options")
in (

let uu____3549 = (

let uu____3550 = (

let uu____3551 = (str s)
in (FStar_Pprint.dquotes uu____3551))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3550))
in (FStar_Pprint.op_Hat_Hat uu____3548 uu____3549)))
end
| FStar_Parser_AST.ResetOptions (s_opt) -> begin
(

let uu____3555 = (str "#reset-options")
in (

let uu____3556 = (FStar_Pprint.optional (fun s -> (

let uu____3560 = (

let uu____3561 = (str s)
in (FStar_Pprint.dquotes uu____3561))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3560))) s_opt)
in (FStar_Pprint.op_Hat_Hat uu____3555 uu____3556)))
end
| FStar_Parser_AST.LightOff -> begin
((FStar_ST.op_Colon_Equals should_print_fs_typ_app true);
(str "#light \"off\"");
)
end))
and p_typars : FStar_Parser_AST.binder Prims.list  ->  FStar_Pprint.document = (fun bs -> (p_binders true bs))
and p_fsdocTypeDeclPairs : (FStar_Parser_AST.tycon * FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option)  ->  FStar_Pprint.document = (fun uu____3589 -> (match (uu____3589) with
| (typedecl, fsdoc_opt) -> begin
(

let uu____3602 = (FStar_Pprint.optional p_fsdoc fsdoc_opt)
in (

let uu____3603 = (p_typeDecl typedecl)
in (FStar_Pprint.op_Hat_Hat uu____3602 uu____3603)))
end))
and p_typeDecl : FStar_Parser_AST.tycon  ->  FStar_Pprint.document = (fun uu___59_3604 -> (match (uu___59_3604) with
| FStar_Parser_AST.TyconAbstract (lid, bs, typ_opt) -> begin
(

let empty' = (fun uu____3621 -> FStar_Pprint.empty)
in (p_typeDeclPrefix lid bs typ_opt empty'))
end
| FStar_Parser_AST.TyconAbbrev (lid, bs, typ_opt, t) -> begin
(

let f = (fun uu____3639 -> (

let uu____3640 = (p_typ false false t)
in (prefix2 FStar_Pprint.equals uu____3640)))
in (p_typeDeclPrefix lid bs typ_opt f))
end
| FStar_Parser_AST.TyconRecord (lid, bs, typ_opt, record_field_decls) -> begin
(

let p_recordFieldAndComments = (fun ps uu____3691 -> (match (uu____3691) with
| (lid1, t, doc_opt) -> begin
(

let uu____3707 = (FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range)
in (with_comment (p_recordFieldDecl ps) ((lid1), (t), (doc_opt)) uu____3707))
end))
in (

let p_fields = (fun uu____3723 -> (

let uu____3724 = (

let uu____3725 = (

let uu____3726 = (

let uu____3727 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (separate_map_last uu____3727 p_recordFieldAndComments record_field_decls))
in (braces_with_nesting uu____3726))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3725))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____3724)))
in (p_typeDeclPrefix lid bs typ_opt p_fields)))
end
| FStar_Parser_AST.TyconVariant (lid, bs, typ_opt, ct_decls) -> begin
(

let p_constructorBranchAndComments = (fun uu____3793 -> (match (uu____3793) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let range = (

let uu____3819 = (

let uu____3820 = (FStar_Util.map_opt t_opt (fun t -> t.FStar_Parser_AST.range))
in (FStar_Util.dflt uid.FStar_Ident.idRange uu____3820))
in (FStar_Range.extend_to_end_of_line uu____3819))
in (

let p_constructorBranch = (fun decl -> (

let uu____3855 = (

let uu____3856 = (

let uu____3857 = (p_constructorDecl decl)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3857))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____3856))
in (FStar_Pprint.group uu____3855)))
in (with_comment p_constructorBranch ((uid), (t_opt), (doc_opt), (use_of)) range)))
end))
in (

let datacon_doc = (fun uu____3879 -> (

let uu____3880 = (FStar_Pprint.separate_map break1 p_constructorBranchAndComments ct_decls)
in (FStar_Pprint.group uu____3880)))
in (p_typeDeclPrefix lid bs typ_opt (fun uu____3895 -> (

let uu____3896 = (datacon_doc ())
in (prefix2 FStar_Pprint.equals uu____3896))))))
end))
and p_typeDeclPrefix : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.knd FStar_Pervasives_Native.option  ->  (unit  ->  FStar_Pprint.document)  ->  FStar_Pprint.document = (fun lid bs typ_opt cont -> (match (((Prims.op_Equality bs []) && (Prims.op_Equality typ_opt FStar_Pervasives_Native.None))) with
| true -> begin
(

let uu____3911 = (p_ident lid)
in (

let uu____3912 = (

let uu____3913 = (cont ())
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3913))
in (FStar_Pprint.op_Hat_Hat uu____3911 uu____3912)))
end
| uu____3914 -> begin
(

let binders_doc = (

let uu____3916 = (p_typars bs)
in (

let uu____3917 = (FStar_Pprint.optional (fun t -> (

let uu____3921 = (

let uu____3922 = (

let uu____3923 = (p_typ false false t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3923))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3922))
in (FStar_Pprint.op_Hat_Hat break1 uu____3921))) typ_opt)
in (FStar_Pprint.op_Hat_Hat uu____3916 uu____3917)))
in (

let uu____3924 = (p_ident lid)
in (

let uu____3925 = (cont ())
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____3924 binders_doc uu____3925))))
end))
and p_recordFieldDecl : Prims.bool  ->  (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option)  ->  FStar_Pprint.document = (fun ps uu____3927 -> (match (uu____3927) with
| (lid, t, doc_opt) -> begin
(

let uu____3943 = (

let uu____3944 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (

let uu____3945 = (

let uu____3946 = (p_lident lid)
in (

let uu____3947 = (

let uu____3948 = (p_typ ps false t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3948))
in (FStar_Pprint.op_Hat_Hat uu____3946 uu____3947)))
in (FStar_Pprint.op_Hat_Hat uu____3944 uu____3945)))
in (FStar_Pprint.group uu____3943))
end))
and p_constructorDecl : (FStar_Ident.ident * FStar_Parser_AST.term FStar_Pervasives_Native.option * FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option * Prims.bool)  ->  FStar_Pprint.document = (fun uu____3949 -> (match (uu____3949) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let sep = (match (use_of) with
| true -> begin
(str "of")
end
| uu____3975 -> begin
FStar_Pprint.colon
end)
in (

let uid_doc = (p_uident uid)
in (

let uu____3977 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (

let uu____3978 = (

let uu____3979 = (FStar_Pprint.break_ (Prims.parse_int "0"))
in (

let uu____3980 = (default_or_map uid_doc (fun t -> (

let uu____3985 = (

let uu____3986 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep)
in (FStar_Pprint.op_Hat_Hat uid_doc uu____3986))
in (

let uu____3987 = (p_typ false false t)
in (op_Hat_Slash_Plus_Hat uu____3985 uu____3987)))) t_opt)
in (FStar_Pprint.op_Hat_Hat uu____3979 uu____3980)))
in (FStar_Pprint.op_Hat_Hat uu____3977 uu____3978)))))
end))
and p_letlhs : (FStar_Parser_AST.pattern * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun uu____3988 -> (match (uu____3988) with
| (pat, uu____3994) -> begin
(

let uu____3995 = (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat1, (t, FStar_Pervasives_Native.None)) -> begin
(

let uu____4014 = (

let uu____4015 = (

let uu____4016 = (

let uu____4017 = (

let uu____4018 = (p_tmArrow p_tmNoEq t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4018))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4017))
in (FStar_Pprint.group uu____4016))
in (FStar_Pprint.op_Hat_Hat break1 uu____4015))
in ((pat1), (uu____4014)))
end
| FStar_Parser_AST.PatAscribed (pat1, (t, FStar_Pervasives_Native.Some (tac))) -> begin
(

let uu____4030 = (

let uu____4031 = (

let uu____4032 = (

let uu____4033 = (

let uu____4034 = (

let uu____4035 = (p_tmArrow p_tmNoEq t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4035))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4034))
in (FStar_Pprint.group uu____4033))
in (

let uu____4036 = (

let uu____4037 = (

let uu____4038 = (str "by")
in (

let uu____4039 = (

let uu____4040 = (p_atomicTerm tac)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4040))
in (FStar_Pprint.op_Hat_Hat uu____4038 uu____4039)))
in (FStar_Pprint.group uu____4037))
in (FStar_Pprint.op_Hat_Hat uu____4032 uu____4036)))
in (FStar_Pprint.op_Hat_Hat break1 uu____4031))
in ((pat1), (uu____4030)))
end
| uu____4041 -> begin
((pat), (FStar_Pprint.empty))
end)
in (match (uu____3995) with
| (pat1, ascr_doc) -> begin
(match (pat1.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____4045); FStar_Parser_AST.prange = uu____4046}, pats) -> begin
(

let uu____4056 = (

let uu____4057 = (p_lident x)
in (

let uu____4058 = (

let uu____4059 = (separate_map_or_flow break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Hat uu____4059 ascr_doc))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4057 uu____4058)))
in (FStar_Pprint.group uu____4056))
end
| uu____4060 -> begin
(

let uu____4061 = (

let uu____4062 = (p_tuplePattern pat1)
in (FStar_Pprint.op_Hat_Hat uu____4062 ascr_doc))
in (FStar_Pprint.group uu____4061))
end)
end))
end))
and p_letbinding : (FStar_Parser_AST.pattern * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun uu____4063 -> (match (uu____4063) with
| (pat, e) -> begin
(

let pat_doc = (p_letlhs ((pat), (e)))
in (

let uu____4071 = (

let uu____4072 = (FStar_Pprint.op_Hat_Slash_Hat pat_doc FStar_Pprint.equals)
in (FStar_Pprint.group uu____4072))
in (

let uu____4073 = (p_term false false e)
in (prefix2 uu____4071 uu____4073))))
end))
and p_newEffect : FStar_Parser_AST.effect_decl  ->  FStar_Pprint.document = (fun uu___60_4074 -> (match (uu___60_4074) with
| FStar_Parser_AST.RedefineEffect (lid, bs, t) -> begin
(p_effectRedefinition lid bs t)
end
| FStar_Parser_AST.DefineEffect (lid, bs, t, eff_decls) -> begin
(p_effectDefinition lid bs t eff_decls)
end))
and p_effectRedefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun uid bs t -> (

let uu____4099 = (p_uident uid)
in (

let uu____4100 = (p_binders true bs)
in (

let uu____4101 = (

let uu____4102 = (p_simpleTerm false false t)
in (prefix2 FStar_Pprint.equals uu____4102))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____4099 uu____4100 uu____4101)))))
and p_effectDefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun uid bs t eff_decls -> (

let uu____4111 = (

let uu____4112 = (

let uu____4113 = (

let uu____4114 = (p_uident uid)
in (

let uu____4115 = (p_binders true bs)
in (

let uu____4116 = (

let uu____4117 = (p_typ false false t)
in (prefix2 FStar_Pprint.colon uu____4117))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____4114 uu____4115 uu____4116))))
in (FStar_Pprint.group uu____4113))
in (

let uu____4118 = (

let uu____4119 = (str "with")
in (

let uu____4120 = (separate_break_map_last FStar_Pprint.semi p_effectDecl eff_decls)
in (prefix2 uu____4119 uu____4120)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4112 uu____4118)))
in (braces_with_nesting uu____4111)))
and p_effectDecl : Prims.bool  ->  FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun ps d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (false, ((FStar_Parser_AST.TyconAbbrev (lid, [], FStar_Pervasives_Native.None, e), FStar_Pervasives_Native.None))::[]) -> begin
(

let uu____4151 = (

let uu____4152 = (p_lident lid)
in (

let uu____4153 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____4152 uu____4153)))
in (

let uu____4154 = (p_simpleTerm ps false e)
in (prefix2 uu____4151 uu____4154)))
end
| uu____4155 -> begin
(

let uu____4156 = (

let uu____4157 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "Not a declaration of an effect member... or at least I hope so : %s" uu____4157))
in (failwith uu____4156))
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

let p_lift = (fun ps uu____4219 -> (match (uu____4219) with
| (kwd, t) -> begin
(

let uu____4226 = (

let uu____4227 = (str kwd)
in (

let uu____4228 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____4227 uu____4228)))
in (

let uu____4229 = (p_simpleTerm ps false t)
in (prefix2 uu____4226 uu____4229)))
end))
in (separate_break_map_last FStar_Pprint.semi p_lift lifts)))
in (

let uu____4234 = (

let uu____4235 = (

let uu____4236 = (p_quident lift.FStar_Parser_AST.msource)
in (

let uu____4237 = (

let uu____4238 = (str "~>")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4238))
in (FStar_Pprint.op_Hat_Hat uu____4236 uu____4237)))
in (

let uu____4239 = (p_quident lift.FStar_Parser_AST.mdest)
in (prefix2 uu____4235 uu____4239)))
in (

let uu____4240 = (

let uu____4241 = (braces_with_nesting lift_op_doc)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4241))
in (FStar_Pprint.op_Hat_Hat uu____4234 uu____4240)))))
and p_qualifier : FStar_Parser_AST.qualifier  ->  FStar_Pprint.document = (fun uu___61_4242 -> (match (uu___61_4242) with
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

let uu____4244 = (FStar_Pprint.separate_map break1 p_qualifier qs)
in (FStar_Pprint.group uu____4244)))
and p_letqualifier : FStar_Parser_AST.let_qualifier  ->  FStar_Pprint.document = (fun uu___62_4245 -> (match (uu___62_4245) with
| FStar_Parser_AST.Rec -> begin
(

let uu____4246 = (str "rec")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4246))
end
| FStar_Parser_AST.Mutable -> begin
(

let uu____4247 = (str "mutable")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4247))
end
| FStar_Parser_AST.NoLetQualifier -> begin
FStar_Pprint.empty
end))
and p_aqual : FStar_Parser_AST.arg_qualifier  ->  FStar_Pprint.document = (fun uu___63_4248 -> (match (uu___63_4248) with
| FStar_Parser_AST.Implicit -> begin
(str "#")
end
| FStar_Parser_AST.Equality -> begin
(str "$")
end))
and p_disjunctivePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr (pats) -> begin
(

let uu____4253 = (

let uu____4254 = (

let uu____4255 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space)
in (FStar_Pprint.op_Hat_Hat break1 uu____4255))
in (FStar_Pprint.separate_map uu____4254 p_tuplePattern pats))
in (FStar_Pprint.group uu____4253))
end
| uu____4256 -> begin
(p_tuplePattern p)
end))
and p_tuplePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTuple (pats, false) -> begin
(

let uu____4263 = (

let uu____4264 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map uu____4264 p_constructorPattern pats))
in (FStar_Pprint.group uu____4263))
end
| uu____4265 -> begin
(p_constructorPattern p)
end))
and p_constructorPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (maybe_cons_lid); FStar_Parser_AST.prange = uu____4268}, (hd1)::(tl1)::[]) when (FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid) -> begin
(

let uu____4273 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon)
in (

let uu____4274 = (p_constructorPattern hd1)
in (

let uu____4275 = (p_constructorPattern tl1)
in (infix0 uu____4273 uu____4274 uu____4275))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (uid); FStar_Parser_AST.prange = uu____4277}, pats) -> begin
(

let uu____4283 = (p_quident uid)
in (

let uu____4284 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (prefix2 uu____4283 uu____4284)))
end
| uu____4285 -> begin
(p_atomicPattern p)
end))
and p_atomicPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, (t, FStar_Pervasives_Native.None)) -> begin
(match (((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm))) with
| (FStar_Parser_AST.PatVar (lid, aqual), FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t1); FStar_Parser_AST.brange = uu____4301; FStar_Parser_AST.blevel = uu____4302; FStar_Parser_AST.aqual = uu____4303}, phi)) when (Prims.op_Equality lid.FStar_Ident.idText lid'.FStar_Ident.idText) -> begin
(

let uu____4309 = (

let uu____4310 = (p_ident lid)
in (p_refinement aqual uu____4310 t1 phi))
in (soft_parens_with_nesting uu____4309))
end
| (FStar_Parser_AST.PatWild, FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t1); FStar_Parser_AST.brange = uu____4312; FStar_Parser_AST.blevel = uu____4313; FStar_Parser_AST.aqual = uu____4314}, phi)) -> begin
(

let uu____4316 = (p_refinement FStar_Pervasives_Native.None FStar_Pprint.underscore t1 phi)
in (soft_parens_with_nesting uu____4316))
end
| uu____4317 -> begin
(

let uu____4322 = (

let uu____4323 = (p_tuplePattern pat)
in (

let uu____4324 = (

let uu____4325 = (FStar_Pprint.break_ (Prims.parse_int "0"))
in (

let uu____4326 = (

let uu____4327 = (p_tmEqNoRefinement t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4327))
in (FStar_Pprint.op_Hat_Hat uu____4325 uu____4326)))
in (FStar_Pprint.op_Hat_Hat uu____4323 uu____4324)))
in (soft_parens_with_nesting uu____4322))
end)
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let uu____4331 = (separate_break_map FStar_Pprint.semi p_tuplePattern pats)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket uu____4331 FStar_Pprint.rbracket))
end
| FStar_Parser_AST.PatRecord (pats) -> begin
(

let p_recordFieldPat = (fun uu____4348 -> (match (uu____4348) with
| (lid, pat) -> begin
(

let uu____4355 = (p_qlident lid)
in (

let uu____4356 = (p_tuplePattern pat)
in (infix2 FStar_Pprint.equals uu____4355 uu____4356)))
end))
in (

let uu____4357 = (separate_break_map FStar_Pprint.semi p_recordFieldPat pats)
in (soft_braces_with_nesting uu____4357)))
end
| FStar_Parser_AST.PatTuple (pats, true) -> begin
(

let uu____4367 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (

let uu____4368 = (separate_break_map FStar_Pprint.comma p_constructorPattern pats)
in (

let uu____4369 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____4367 uu____4368 uu____4369))))
end
| FStar_Parser_AST.PatTvar (tv, arg_qualifier_opt) -> begin
(p_tvar tv)
end
| FStar_Parser_AST.PatOp (op) -> begin
(

let uu____4378 = (

let uu____4379 = (

let uu____4380 = (

let uu____4381 = (FStar_Ident.text_of_id op)
in (str uu____4381))
in (

let uu____4382 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat uu____4380 uu____4382)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4379))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4378))
end
| FStar_Parser_AST.PatWild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.PatConst (c) -> begin
(p_constant c)
end
| FStar_Parser_AST.PatVar (lid, aqual) -> begin
(

let uu____4390 = (FStar_Pprint.optional p_aqual aqual)
in (

let uu____4391 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat uu____4390 uu____4391)))
end
| FStar_Parser_AST.PatName (uid) -> begin
(p_quident uid)
end
| FStar_Parser_AST.PatOr (uu____4393) -> begin
(failwith "Inner or pattern !")
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (uu____4396); FStar_Parser_AST.prange = uu____4397}, uu____4398) -> begin
(

let uu____4403 = (p_tuplePattern p)
in (soft_parens_with_nesting uu____4403))
end
| FStar_Parser_AST.PatTuple (uu____4404, false) -> begin
(

let uu____4409 = (p_tuplePattern p)
in (soft_parens_with_nesting uu____4409))
end
| uu____4410 -> begin
(

let uu____4411 = (

let uu____4412 = (FStar_Parser_AST.pat_to_string p)
in (FStar_Util.format1 "Invalid pattern %s" uu____4412))
in (failwith uu____4411))
end))
and p_binder : Prims.bool  ->  FStar_Parser_AST.binder  ->  FStar_Pprint.document = (fun is_atomic b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (lid) -> begin
(

let uu____4416 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (

let uu____4417 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat uu____4416 uu____4417)))
end
| FStar_Parser_AST.TVariable (lid) -> begin
(p_lident lid)
end
| FStar_Parser_AST.Annotated (lid, t) -> begin
(

let doc1 = (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t1); FStar_Parser_AST.brange = uu____4424; FStar_Parser_AST.blevel = uu____4425; FStar_Parser_AST.aqual = uu____4426}, phi) when (Prims.op_Equality lid.FStar_Ident.idText lid'.FStar_Ident.idText) -> begin
(

let uu____4428 = (p_ident lid)
in (p_refinement b.FStar_Parser_AST.aqual uu____4428 t1 phi))
end
| uu____4429 -> begin
(

let uu____4430 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (

let uu____4431 = (

let uu____4432 = (p_lident lid)
in (

let uu____4433 = (

let uu____4434 = (

let uu____4435 = (FStar_Pprint.break_ (Prims.parse_int "0"))
in (

let uu____4436 = (p_tmFormula t)
in (FStar_Pprint.op_Hat_Hat uu____4435 uu____4436)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4434))
in (FStar_Pprint.op_Hat_Hat uu____4432 uu____4433)))
in (FStar_Pprint.op_Hat_Hat uu____4430 uu____4431)))
end)
in (match (is_atomic) with
| true -> begin
(

let uu____4437 = (

let uu____4438 = (FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4438))
in (FStar_Pprint.group uu____4437))
end
| uu____4439 -> begin
(FStar_Pprint.group doc1)
end))
end
| FStar_Parser_AST.TAnnotated (uu____4440) -> begin
(failwith "Is this still used ?")
end
| FStar_Parser_AST.NoName (t) -> begin
(match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t1); FStar_Parser_AST.brange = uu____4447; FStar_Parser_AST.blevel = uu____4448; FStar_Parser_AST.aqual = uu____4449}, phi) -> begin
(match (is_atomic) with
| true -> begin
(

let uu____4451 = (

let uu____4452 = (

let uu____4453 = (p_refinement b.FStar_Parser_AST.aqual FStar_Pprint.underscore t1 phi)
in (FStar_Pprint.op_Hat_Hat uu____4453 FStar_Pprint.rparen))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4452))
in (FStar_Pprint.group uu____4451))
end
| uu____4454 -> begin
(

let uu____4455 = (p_refinement b.FStar_Parser_AST.aqual FStar_Pprint.underscore t1 phi)
in (FStar_Pprint.group uu____4455))
end)
end
| uu____4456 -> begin
(match (is_atomic) with
| true -> begin
(p_atomicTerm t)
end
| uu____4457 -> begin
(p_appTerm t)
end)
end)
end))
and p_refinement : FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Pprint.document  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun aqual_opt binder t phi -> (

let uu____4464 = (FStar_Pprint.optional p_aqual aqual_opt)
in (

let uu____4465 = (

let uu____4466 = (

let uu____4467 = (

let uu____4468 = (p_appTerm t)
in (

let uu____4469 = (

let uu____4470 = (p_noSeqTerm false false phi)
in (soft_braces_with_nesting uu____4470))
in (FStar_Pprint.op_Hat_Hat uu____4468 uu____4469)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4467))
in (FStar_Pprint.op_Hat_Hat binder uu____4466))
in (FStar_Pprint.op_Hat_Hat uu____4464 uu____4465))))
and p_binders : Prims.bool  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Pprint.document = (fun is_atomic bs -> (separate_map_or_flow break1 (p_binder is_atomic) bs))
and p_qlident : FStar_Ident.lid  ->  FStar_Pprint.document = (fun lid -> (

let uu____4476 = (FStar_Ident.text_of_lid lid)
in (str uu____4476)))
and p_quident : FStar_Ident.lid  ->  FStar_Pprint.document = (fun lid -> (

let uu____4478 = (FStar_Ident.text_of_lid lid)
in (str uu____4478)))
and p_ident : FStar_Ident.ident  ->  FStar_Pprint.document = (fun lid -> (

let uu____4480 = (FStar_Ident.text_of_id lid)
in (str uu____4480)))
and p_lident : FStar_Ident.ident  ->  FStar_Pprint.document = (fun lid -> (

let uu____4482 = (FStar_Ident.text_of_id lid)
in (str uu____4482)))
and p_uident : FStar_Ident.ident  ->  FStar_Pprint.document = (fun lid -> (

let uu____4484 = (FStar_Ident.text_of_id lid)
in (str uu____4484)))
and p_tvar : FStar_Ident.ident  ->  FStar_Pprint.document = (fun lid -> (

let uu____4486 = (FStar_Ident.text_of_id lid)
in (str uu____4486)))
and p_lidentOrUnderscore : FStar_Ident.ident  ->  FStar_Pprint.document = (fun id1 -> (match ((FStar_Util.starts_with FStar_Ident.reserved_prefix id1.FStar_Ident.idText)) with
| true -> begin
FStar_Pprint.underscore
end
| uu____4488 -> begin
(p_lident id1)
end))
and paren_if : Prims.bool  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun b -> (match (b) with
| true -> begin
soft_parens_with_nesting
end
| uu____4493 -> begin
(

let id1 = (fun x -> x)
in id1)
end))
and p_term : Prims.bool  ->  Prims.bool  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun ps pb e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Seq (e1, e2) -> begin
(

let uu____4505 = (

let uu____4506 = (

let uu____4507 = (p_noSeqTerm true false e1)
in (FStar_Pprint.op_Hat_Hat uu____4507 FStar_Pprint.semi))
in (FStar_Pprint.group uu____4506))
in (

let uu____4508 = (p_term ps pb e2)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4505 uu____4508)))
end
| FStar_Parser_AST.Bind (x, e1, e2) -> begin
(

let uu____4512 = (

let uu____4513 = (

let uu____4514 = (

let uu____4515 = (p_lident x)
in (

let uu____4516 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.long_left_arrow)
in (FStar_Pprint.op_Hat_Hat uu____4515 uu____4516)))
in (

let uu____4517 = (

let uu____4518 = (p_noSeqTerm true false e1)
in (

let uu____4519 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.semi)
in (FStar_Pprint.op_Hat_Hat uu____4518 uu____4519)))
in (op_Hat_Slash_Plus_Hat uu____4514 uu____4517)))
in (FStar_Pprint.group uu____4513))
in (

let uu____4520 = (p_term ps pb e2)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4512 uu____4520)))
end
| uu____4521 -> begin
(

let uu____4522 = (p_noSeqTerm ps pb e)
in (FStar_Pprint.group uu____4522))
end))
and p_noSeqTerm : Prims.bool  ->  Prims.bool  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun ps pb e -> (with_comment (p_noSeqTerm' ps pb) e e.FStar_Parser_AST.range))
and p_noSeqTerm' : Prims.bool  ->  Prims.bool  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun ps pb e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Ascribed (e1, t, FStar_Pervasives_Native.None) -> begin
(

let uu____4533 = (

let uu____4534 = (p_tmIff e1)
in (

let uu____4535 = (

let uu____4536 = (

let uu____4537 = (p_typ ps pb t)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4537))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4536))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4534 uu____4535)))
in (FStar_Pprint.group uu____4533))
end
| FStar_Parser_AST.Ascribed (e1, t, FStar_Pervasives_Native.Some (tac)) -> begin
(

let uu____4543 = (

let uu____4544 = (p_tmIff e1)
in (

let uu____4545 = (

let uu____4546 = (

let uu____4547 = (

let uu____4548 = (p_typ false false t)
in (

let uu____4549 = (

let uu____4550 = (str "by")
in (

let uu____4551 = (p_typ ps pb tac)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4550 uu____4551)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4548 uu____4549)))
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4547))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4546))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4544 uu____4545)))
in (FStar_Pprint.group uu____4543))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = ".()<-"; FStar_Ident.idRange = uu____4552}, (e1)::(e2)::(e3)::[]) -> begin
(

let uu____4558 = (

let uu____4559 = (

let uu____4560 = (

let uu____4561 = (p_atomicTermNotQUident e1)
in (

let uu____4562 = (

let uu____4563 = (

let uu____4564 = (

let uu____4565 = (p_term false false e2)
in (soft_parens_with_nesting uu____4565))
in (

let uu____4566 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat uu____4564 uu____4566)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4563))
in (FStar_Pprint.op_Hat_Hat uu____4561 uu____4562)))
in (FStar_Pprint.group uu____4560))
in (

let uu____4567 = (

let uu____4568 = (p_noSeqTerm ps pb e3)
in (jump2 uu____4568))
in (FStar_Pprint.op_Hat_Hat uu____4559 uu____4567)))
in (FStar_Pprint.group uu____4558))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = ".[]<-"; FStar_Ident.idRange = uu____4569}, (e1)::(e2)::(e3)::[]) -> begin
(

let uu____4575 = (

let uu____4576 = (

let uu____4577 = (

let uu____4578 = (p_atomicTermNotQUident e1)
in (

let uu____4579 = (

let uu____4580 = (

let uu____4581 = (

let uu____4582 = (p_term false false e2)
in (soft_brackets_with_nesting uu____4582))
in (

let uu____4583 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat uu____4581 uu____4583)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4580))
in (FStar_Pprint.op_Hat_Hat uu____4578 uu____4579)))
in (FStar_Pprint.group uu____4577))
in (

let uu____4584 = (

let uu____4585 = (p_noSeqTerm ps pb e3)
in (jump2 uu____4585))
in (FStar_Pprint.op_Hat_Hat uu____4576 uu____4584)))
in (FStar_Pprint.group uu____4575))
end
| FStar_Parser_AST.Requires (e1, wtf) -> begin
(

let uu____4593 = (

let uu____4594 = (str "requires")
in (

let uu____4595 = (p_typ ps pb e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4594 uu____4595)))
in (FStar_Pprint.group uu____4593))
end
| FStar_Parser_AST.Ensures (e1, wtf) -> begin
(

let uu____4603 = (

let uu____4604 = (str "ensures")
in (

let uu____4605 = (p_typ ps pb e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4604 uu____4605)))
in (FStar_Pprint.group uu____4603))
end
| FStar_Parser_AST.Attributes (es) -> begin
(

let uu____4609 = (

let uu____4610 = (str "attributes")
in (

let uu____4611 = (FStar_Pprint.separate_map break1 p_atomicTerm es)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4610 uu____4611)))
in (FStar_Pprint.group uu____4609))
end
| FStar_Parser_AST.If (e1, e2, e3) -> begin
(match ((is_unit e3)) with
| true -> begin
(

let uu____4615 = (

let uu____4616 = (

let uu____4617 = (str "if")
in (

let uu____4618 = (p_noSeqTerm false false e1)
in (op_Hat_Slash_Plus_Hat uu____4617 uu____4618)))
in (

let uu____4619 = (

let uu____4620 = (str "then")
in (

let uu____4621 = (p_noSeqTerm ps pb e2)
in (op_Hat_Slash_Plus_Hat uu____4620 uu____4621)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4616 uu____4619)))
in (FStar_Pprint.group uu____4615))
end
| uu____4622 -> begin
(

let e2_doc = (match (e2.FStar_Parser_AST.tm) with
| FStar_Parser_AST.If (uu____4624, uu____4625, e31) when (is_unit e31) -> begin
(

let uu____4627 = (p_noSeqTerm false false e2)
in (soft_parens_with_nesting uu____4627))
end
| uu____4628 -> begin
(p_noSeqTerm false false e2)
end)
in (

let uu____4629 = (

let uu____4630 = (

let uu____4631 = (str "if")
in (

let uu____4632 = (p_noSeqTerm false false e1)
in (op_Hat_Slash_Plus_Hat uu____4631 uu____4632)))
in (

let uu____4633 = (

let uu____4634 = (

let uu____4635 = (str "then")
in (op_Hat_Slash_Plus_Hat uu____4635 e2_doc))
in (

let uu____4636 = (

let uu____4637 = (str "else")
in (

let uu____4638 = (p_noSeqTerm ps pb e3)
in (op_Hat_Slash_Plus_Hat uu____4637 uu____4638)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4634 uu____4636)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4630 uu____4633)))
in (FStar_Pprint.group uu____4629)))
end)
end
| FStar_Parser_AST.TryWith (e1, branches) -> begin
(

let uu____4661 = (

let uu____4662 = (

let uu____4663 = (

let uu____4664 = (str "try")
in (

let uu____4665 = (p_noSeqTerm false false e1)
in (prefix2 uu____4664 uu____4665)))
in (

let uu____4666 = (

let uu____4667 = (str "with")
in (

let uu____4668 = (separate_map_last FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4667 uu____4668)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4663 uu____4666)))
in (FStar_Pprint.group uu____4662))
in (

let uu____4677 = (paren_if (ps || pb))
in (uu____4677 uu____4661)))
end
| FStar_Parser_AST.Match (e1, branches) -> begin
(

let uu____4704 = (

let uu____4705 = (

let uu____4706 = (

let uu____4707 = (str "match")
in (

let uu____4708 = (p_noSeqTerm false false e1)
in (

let uu____4709 = (str "with")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____4707 uu____4708 uu____4709))))
in (

let uu____4710 = (separate_map_last FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4706 uu____4710)))
in (FStar_Pprint.group uu____4705))
in (

let uu____4719 = (paren_if (ps || pb))
in (uu____4719 uu____4704)))
end
| FStar_Parser_AST.LetOpen (uid, e1) -> begin
(

let uu____4726 = (

let uu____4727 = (

let uu____4728 = (

let uu____4729 = (str "let open")
in (

let uu____4730 = (p_quident uid)
in (

let uu____4731 = (str "in")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____4729 uu____4730 uu____4731))))
in (

let uu____4732 = (p_term false pb e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4728 uu____4732)))
in (FStar_Pprint.group uu____4727))
in (

let uu____4733 = (paren_if ps)
in (uu____4733 uu____4726)))
end
| FStar_Parser_AST.Let (q, lbs, e1) -> begin
(

let p_lb = (fun q1 uu____4797 is_last -> (match (uu____4797) with
| (a, (pat, e2)) -> begin
(

let attrs = (p_attrs_opt a)
in (

let doc_let_or_and = (match (q1) with
| FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec) -> begin
(

let uu____4830 = (

let uu____4831 = (str "let")
in (

let uu____4832 = (str "rec")
in (FStar_Pprint.op_Hat_Slash_Hat uu____4831 uu____4832)))
in (FStar_Pprint.group uu____4830))
end
| FStar_Pervasives_Native.Some (FStar_Parser_AST.NoLetQualifier) -> begin
(str "let")
end
| uu____4833 -> begin
(str "and")
end)
in (

let doc_pat = (p_letlhs ((pat), (e2)))
in (

let doc_expr = (p_term false false e2)
in (

let uu____4838 = (match (is_last) with
| true -> begin
(

let uu____4839 = (

let uu____4840 = (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") doc_let_or_and doc_pat FStar_Pprint.equals)
in (

let uu____4841 = (str "in")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____4840 doc_expr uu____4841)))
in (FStar_Pprint.group uu____4839))
end
| uu____4842 -> begin
(

let uu____4843 = (

let uu____4844 = (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") doc_let_or_and doc_pat FStar_Pprint.equals)
in (FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "1") uu____4844 doc_expr))
in (FStar_Pprint.group uu____4843))
end)
in (FStar_Pprint.op_Hat_Hat attrs uu____4838))))))
end))
in (

let l = (FStar_List.length lbs)
in (

let lbs_docs = (FStar_List.mapi (fun i lb -> (match ((Prims.op_Equality i (Prims.parse_int "0"))) with
| true -> begin
(

let uu____4890 = (p_lb (FStar_Pervasives_Native.Some (q)) lb (Prims.op_Equality i (l - (Prims.parse_int "1"))))
in (FStar_Pprint.group uu____4890))
end
| uu____4897 -> begin
(

let uu____4898 = (p_lb FStar_Pervasives_Native.None lb (Prims.op_Equality i (l - (Prims.parse_int "1"))))
in (FStar_Pprint.group uu____4898))
end)) lbs)
in (

let lbs_doc = (

let uu____4906 = (FStar_Pprint.separate break1 lbs_docs)
in (FStar_Pprint.group uu____4906))
in (

let uu____4907 = (

let uu____4908 = (

let uu____4909 = (

let uu____4910 = (p_term false pb e1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4910))
in (FStar_Pprint.op_Hat_Hat lbs_doc uu____4909))
in (FStar_Pprint.group uu____4908))
in (

let uu____4911 = (paren_if ps)
in (uu____4911 uu____4907)))))))
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, typ_opt); FStar_Parser_AST.prange = uu____4918})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, branches); FStar_Parser_AST.range = uu____4921; FStar_Parser_AST.level = uu____4922}) when (matches_var maybe_x x) -> begin
(

let uu____4949 = (

let uu____4950 = (

let uu____4951 = (str "function")
in (

let uu____4952 = (separate_map_last FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4951 uu____4952)))
in (FStar_Pprint.group uu____4950))
in (

let uu____4961 = (paren_if (ps || pb))
in (uu____4961 uu____4949)))
end
| FStar_Parser_AST.Quote (e1, FStar_Parser_AST.Dynamic) -> begin
(

let uu____4967 = (

let uu____4968 = (str "quote")
in (

let uu____4969 = (p_noSeqTerm ps pb e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4968 uu____4969)))
in (FStar_Pprint.group uu____4967))
end
| FStar_Parser_AST.Quote (e1, FStar_Parser_AST.Static) -> begin
(

let uu____4971 = (

let uu____4972 = (str "`")
in (

let uu____4973 = (p_noSeqTerm ps pb e1)
in (FStar_Pprint.op_Hat_Hat uu____4972 uu____4973)))
in (FStar_Pprint.group uu____4971))
end
| FStar_Parser_AST.VQuote (e1) -> begin
(

let uu____4975 = (

let uu____4976 = (str "%`")
in (

let uu____4977 = (p_noSeqTerm ps pb e1)
in (FStar_Pprint.op_Hat_Hat uu____4976 uu____4977)))
in (FStar_Pprint.group uu____4975))
end
| FStar_Parser_AST.Antiquote (false, e1) -> begin
(

let uu____4979 = (

let uu____4980 = (str "`#")
in (

let uu____4981 = (p_noSeqTerm ps pb e1)
in (FStar_Pprint.op_Hat_Hat uu____4980 uu____4981)))
in (FStar_Pprint.group uu____4979))
end
| FStar_Parser_AST.Antiquote (true, e1) -> begin
(

let uu____4983 = (

let uu____4984 = (str "`@")
in (

let uu____4985 = (p_noSeqTerm ps pb e1)
in (FStar_Pprint.op_Hat_Hat uu____4984 uu____4985)))
in (FStar_Pprint.group uu____4983))
end
| uu____4986 -> begin
(p_typ ps pb e)
end))
and p_attrs_opt : FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option  ->  FStar_Pprint.document = (fun uu___64_4987 -> (match (uu___64_4987) with
| FStar_Pervasives_Native.None -> begin
FStar_Pprint.empty
end
| FStar_Pervasives_Native.Some (terms) -> begin
(

let uu____4999 = (

let uu____5000 = (

let uu____5001 = (str "[@")
in (

let uu____5002 = (

let uu____5003 = (FStar_Pprint.separate_map break1 p_atomicTerm terms)
in (

let uu____5004 = (str "]")
in (FStar_Pprint.op_Hat_Slash_Hat uu____5003 uu____5004)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____5001 uu____5002)))
in (FStar_Pprint.group uu____5000))
in (FStar_Pprint.op_Hat_Hat uu____4999 break1))
end))
and p_typ : Prims.bool  ->  Prims.bool  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun ps pb e -> (with_comment (p_typ' ps pb) e e.FStar_Parser_AST.range))
and p_typ' : Prims.bool  ->  Prims.bool  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun ps pb e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.QForall (bs, trigger, e1) -> begin
(

let uu____5026 = (

let uu____5027 = (

let uu____5028 = (p_quantifier e)
in (FStar_Pprint.op_Hat_Hat uu____5028 FStar_Pprint.space))
in (

let uu____5029 = (p_binders true bs)
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") uu____5027 uu____5029 FStar_Pprint.dot)))
in (

let uu____5030 = (

let uu____5031 = (p_trigger trigger)
in (

let uu____5032 = (p_noSeqTerm ps pb e1)
in (FStar_Pprint.op_Hat_Hat uu____5031 uu____5032)))
in (prefix2 uu____5026 uu____5030)))
end
| FStar_Parser_AST.QExists (bs, trigger, e1) -> begin
(

let uu____5048 = (

let uu____5049 = (

let uu____5050 = (p_quantifier e)
in (FStar_Pprint.op_Hat_Hat uu____5050 FStar_Pprint.space))
in (

let uu____5051 = (p_binders true bs)
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") uu____5049 uu____5051 FStar_Pprint.dot)))
in (

let uu____5052 = (

let uu____5053 = (p_trigger trigger)
in (

let uu____5054 = (p_noSeqTerm ps pb e1)
in (FStar_Pprint.op_Hat_Hat uu____5053 uu____5054)))
in (prefix2 uu____5048 uu____5052)))
end
| uu____5055 -> begin
(p_simpleTerm ps pb e)
end))
and p_quantifier : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.QForall (uu____5057) -> begin
(str "forall")
end
| FStar_Parser_AST.QExists (uu____5070) -> begin
(str "exists")
end
| uu____5083 -> begin
(failwith "Imposible : p_quantifier called on a non-quantifier term")
end))
and p_trigger : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun uu___65_5084 -> (match (uu___65_5084) with
| [] -> begin
FStar_Pprint.empty
end
| pats -> begin
(

let uu____5096 = (

let uu____5097 = (

let uu____5098 = (str "pattern")
in (

let uu____5099 = (

let uu____5100 = (

let uu____5101 = (p_disjunctivePats pats)
in (jump2 uu____5101))
in (

let uu____5102 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5100 uu____5102)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____5098 uu____5099)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5097))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____5096))
end))
and p_disjunctivePats : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun pats -> (

let uu____5108 = (str "\\/")
in (FStar_Pprint.separate_map uu____5108 p_conjunctivePats pats)))
and p_conjunctivePats : FStar_Parser_AST.term Prims.list  ->  FStar_Pprint.document = (fun pats -> (

let uu____5114 = (FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats)
in (FStar_Pprint.group uu____5114)))
and p_simpleTerm : Prims.bool  ->  Prims.bool  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun ps pb e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Abs (pats, e1) -> begin
(

let uu____5124 = (

let uu____5125 = (

let uu____5126 = (str "fun")
in (

let uu____5127 = (

let uu____5128 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5128 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat uu____5126 uu____5127)))
in (

let uu____5129 = (p_term false pb e1)
in (op_Hat_Slash_Plus_Hat uu____5125 uu____5129)))
in (

let uu____5130 = (paren_if ps)
in (uu____5130 uu____5124)))
end
| uu____5135 -> begin
(p_tmIff e)
end))
and p_maybeFocusArrow : Prims.bool  ->  FStar_Pprint.document = (fun b -> (match (b) with
| true -> begin
(str "~>")
end
| uu____5137 -> begin
FStar_Pprint.rarrow
end))
and p_patternBranch : Prims.bool  ->  (FStar_Parser_AST.pattern * FStar_Parser_AST.term FStar_Pervasives_Native.option * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun pb uu____5139 -> (match (uu____5139) with
| (pat, when_opt, e) -> begin
(

let uu____5155 = (

let uu____5156 = (

let uu____5157 = (

let uu____5158 = (

let uu____5159 = (

let uu____5160 = (p_disjunctivePattern pat)
in (

let uu____5161 = (

let uu____5162 = (p_maybeWhen when_opt)
in (FStar_Pprint.op_Hat_Hat uu____5162 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat uu____5160 uu____5161)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5159))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5158))
in (FStar_Pprint.group uu____5157))
in (

let uu____5163 = (p_term false pb e)
in (op_Hat_Slash_Plus_Hat uu____5156 uu____5163)))
in (FStar_Pprint.group uu____5155))
end))
and p_maybeWhen : FStar_Parser_AST.term FStar_Pervasives_Native.option  ->  FStar_Pprint.document = (fun uu___66_5164 -> (match (uu___66_5164) with
| FStar_Pervasives_Native.None -> begin
FStar_Pprint.empty
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____5168 = (str "when")
in (

let uu____5169 = (

let uu____5170 = (p_tmFormula e)
in (FStar_Pprint.op_Hat_Hat uu____5170 FStar_Pprint.space))
in (op_Hat_Slash_Plus_Hat uu____5168 uu____5169)))
end))
and p_tmIff : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5172}, (e1)::(e2)::[]) -> begin
(

let uu____5177 = (str "<==>")
in (

let uu____5178 = (p_tmImplies e1)
in (

let uu____5179 = (p_tmIff e2)
in (infix0 uu____5177 uu____5178 uu____5179))))
end
| uu____5180 -> begin
(p_tmImplies e)
end))
and p_tmImplies : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5182}, (e1)::(e2)::[]) -> begin
(

let uu____5187 = (str "==>")
in (

let uu____5188 = (p_tmArrow p_tmFormula e1)
in (

let uu____5189 = (p_tmImplies e2)
in (infix0 uu____5187 uu____5188 uu____5189))))
end
| uu____5190 -> begin
(p_tmArrow p_tmFormula e)
end))
and p_tmArrow : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_Tm e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Product (bs, tgt) -> begin
(

let uu____5201 = (

let uu____5202 = (separate_map_or_flow FStar_Pprint.empty (fun b -> (

let uu____5207 = (p_binder false b)
in (

let uu____5208 = (

let uu____5209 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5209))
in (FStar_Pprint.op_Hat_Hat uu____5207 uu____5208)))) bs)
in (

let uu____5210 = (p_tmArrow p_Tm tgt)
in (FStar_Pprint.op_Hat_Hat uu____5202 uu____5210)))
in (FStar_Pprint.group uu____5201))
end
| uu____5211 -> begin
(p_Tm e)
end))
and p_tmFormula : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5213}, (e1)::(e2)::[]) -> begin
(

let uu____5218 = (str "\\/")
in (

let uu____5219 = (p_tmFormula e1)
in (

let uu____5220 = (p_tmConjunction e2)
in (infix0 uu____5218 uu____5219 uu____5220))))
end
| uu____5221 -> begin
(p_tmConjunction e)
end))
and p_tmConjunction : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5223}, (e1)::(e2)::[]) -> begin
(

let uu____5228 = (str "/\\")
in (

let uu____5229 = (p_tmConjunction e1)
in (

let uu____5230 = (p_tmTuple e2)
in (infix0 uu____5228 uu____5229 uu____5230))))
end
| uu____5231 -> begin
(p_tmTuple e)
end))
and p_tmTuple : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_tmTuple' e e.FStar_Parser_AST.range))
and p_tmTuple' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (lid, args) when (is_tuple_constructor lid) -> begin
(

let uu____5248 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map uu____5248 (fun uu____5256 -> (match (uu____5256) with
| (e1, uu____5262) -> begin
(p_tmEq e1)
end)) args))
end
| uu____5263 -> begin
(p_tmEq e)
end))
and paren_if_gt : Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun curr mine doc1 -> (match ((mine <= curr)) with
| true -> begin
doc1
end
| uu____5267 -> begin
(

let uu____5268 = (

let uu____5269 = (FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5269))
in (FStar_Pprint.group uu____5268))
end))
and p_tmEqWith : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_X e -> (

let n1 = (max_level (FStar_List.append ((colon_equals)::(pipe_right)::[]) operatorInfix0ad12))
in (p_tmEqWith' p_X n1 e)))
and p_tmEqWith' : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_X curr e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (((is_operatorInfix0ad12 op) || (

let uu____5310 = (FStar_Ident.text_of_id op)
in (Prims.op_Equality uu____5310 "="))) || (

let uu____5312 = (FStar_Ident.text_of_id op)
in (Prims.op_Equality uu____5312 "|>"))) -> begin
(

let op1 = (FStar_Ident.text_of_id op)
in (

let uu____5314 = (levels op1)
in (match (uu____5314) with
| (left1, mine, right1) -> begin
(

let uu____5324 = (

let uu____5325 = (FStar_All.pipe_left str op1)
in (

let uu____5326 = (p_tmEqWith' p_X left1 e1)
in (

let uu____5327 = (p_tmEqWith' p_X right1 e2)
in (infix0 uu____5325 uu____5326 uu____5327))))
in (paren_if_gt curr mine uu____5324))
end)))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5328}, (e1)::(e2)::[]) -> begin
(

let uu____5333 = (

let uu____5334 = (p_tmEqWith p_X e1)
in (

let uu____5335 = (

let uu____5336 = (

let uu____5337 = (

let uu____5338 = (p_tmEqWith p_X e2)
in (op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5338))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5337))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5336))
in (FStar_Pprint.op_Hat_Hat uu____5334 uu____5335)))
in (FStar_Pprint.group uu____5333))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5339}, (e1)::[]) -> begin
(

let uu____5343 = (levels "-")
in (match (uu____5343) with
| (left1, mine, right1) -> begin
(

let uu____5353 = (p_tmEqWith' p_X mine e1)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5353))
end))
end
| uu____5354 -> begin
(p_tmNoEqWith p_X e)
end))
and p_tmNoEqWith : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_X e -> (

let n1 = (max_level ((colon_colon)::(amp)::(opinfix3)::(opinfix4)::[]))
in (p_tmNoEqWith' p_X n1 e)))
and p_tmNoEqWith' : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_X curr e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (lid, ((e1, uu____5397))::((e2, uu____5399))::[]) when ((FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) && (

let uu____5419 = (is_list e)
in (not (uu____5419)))) -> begin
(

let op = "::"
in (

let uu____5421 = (levels op)
in (match (uu____5421) with
| (left1, mine, right1) -> begin
(

let uu____5431 = (

let uu____5432 = (str op)
in (

let uu____5433 = (p_tmNoEqWith' p_X left1 e1)
in (

let uu____5434 = (p_tmNoEqWith' p_X right1 e2)
in (infix0 uu____5432 uu____5433 uu____5434))))
in (paren_if_gt curr mine uu____5431))
end)))
end
| FStar_Parser_AST.Sum (binders, res) -> begin
(

let op = "&"
in (

let uu____5442 = (levels op)
in (match (uu____5442) with
| (left1, mine, right1) -> begin
(

let p_dsumfst = (fun b -> (

let uu____5458 = (p_binder false b)
in (

let uu____5459 = (

let uu____5460 = (

let uu____5461 = (str op)
in (FStar_Pprint.op_Hat_Hat uu____5461 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5460))
in (FStar_Pprint.op_Hat_Hat uu____5458 uu____5459))))
in (

let uu____5462 = (

let uu____5463 = (FStar_Pprint.concat_map p_dsumfst binders)
in (

let uu____5464 = (p_tmNoEqWith' p_X right1 res)
in (FStar_Pprint.op_Hat_Hat uu____5463 uu____5464)))
in (paren_if_gt curr mine uu____5462)))
end)))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (is_operatorInfix34 op) -> begin
(

let op1 = (FStar_Ident.text_of_id op)
in (

let uu____5471 = (levels op1)
in (match (uu____5471) with
| (left1, mine, right1) -> begin
(

let uu____5481 = (

let uu____5482 = (str op1)
in (

let uu____5483 = (p_tmNoEqWith' p_X left1 e1)
in (

let uu____5484 = (p_tmNoEqWith' p_X right1 e2)
in (infix0 uu____5482 uu____5483 uu____5484))))
in (paren_if_gt curr mine uu____5481))
end)))
end
| FStar_Parser_AST.Record (with_opt, record_fields) -> begin
(

let uu____5503 = (

let uu____5504 = (default_or_map FStar_Pprint.empty p_with_clause with_opt)
in (

let uu____5505 = (

let uu____5506 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (separate_map_last uu____5506 p_simpleDef record_fields))
in (FStar_Pprint.op_Hat_Hat uu____5504 uu____5505)))
in (braces_with_nesting uu____5503))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____5511}, (e1)::[]) -> begin
(

let uu____5515 = (

let uu____5516 = (str "~")
in (

let uu____5517 = (p_atomicTerm e1)
in (FStar_Pprint.op_Hat_Hat uu____5516 uu____5517)))
in (FStar_Pprint.group uu____5515))
end
| uu____5518 -> begin
(p_X e)
end))
and p_tmEqNoRefinement : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_tmEqWith p_appTerm e))
and p_tmEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_tmEqWith p_tmRefinement e))
and p_tmNoEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_tmNoEqWith p_tmRefinement e))
and p_tmRefinement : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.NamedTyp (lid, e1) -> begin
(

let uu____5525 = (

let uu____5526 = (p_lidentOrUnderscore lid)
in (

let uu____5527 = (

let uu____5528 = (p_appTerm e1)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5528))
in (FStar_Pprint.op_Hat_Slash_Hat uu____5526 uu____5527)))
in (FStar_Pprint.group uu____5525))
end
| FStar_Parser_AST.Refine (b, phi) -> begin
(p_refinedBinder b phi)
end
| uu____5531 -> begin
(p_appTerm e)
end))
and p_with_clause : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____5533 = (p_appTerm e)
in (

let uu____5534 = (

let uu____5535 = (

let uu____5536 = (str "with")
in (FStar_Pprint.op_Hat_Hat uu____5536 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5535))
in (FStar_Pprint.op_Hat_Hat uu____5533 uu____5534))))
and p_refinedBinder : FStar_Parser_AST.binder  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun b phi -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (lid, t) -> begin
(

let uu____5541 = (

let uu____5542 = (p_lident lid)
in (p_refinement b.FStar_Parser_AST.aqual uu____5542 t phi))
in (soft_parens_with_nesting uu____5541))
end
| FStar_Parser_AST.TAnnotated (uu____5543) -> begin
(failwith "Is this still used ?")
end
| FStar_Parser_AST.Variable (uu____5548) -> begin
(

let uu____5549 = (

let uu____5550 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" uu____5550))
in (failwith uu____5549))
end
| FStar_Parser_AST.TVariable (uu____5551) -> begin
(

let uu____5552 = (

let uu____5553 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" uu____5553))
in (failwith uu____5552))
end
| FStar_Parser_AST.NoName (uu____5554) -> begin
(

let uu____5555 = (

let uu____5556 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" uu____5556))
in (failwith uu____5555))
end))
and p_simpleDef : Prims.bool  ->  (FStar_Ident.lid * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun ps uu____5558 -> (match (uu____5558) with
| (lid, e) -> begin
(

let uu____5565 = (

let uu____5566 = (p_qlident lid)
in (

let uu____5567 = (

let uu____5568 = (p_noSeqTerm ps false e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____5568))
in (FStar_Pprint.op_Hat_Slash_Hat uu____5566 uu____5567)))
in (FStar_Pprint.group uu____5565))
end))
and p_appTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App (uu____5570) when (is_general_application e) -> begin
(

let uu____5577 = (head_and_args e)
in (match (uu____5577) with
| (head1, args) -> begin
(

let uu____5602 = (

let uu____5613 = (FStar_ST.op_Bang should_print_fs_typ_app)
in (match (uu____5613) with
| true -> begin
(

let uu____5647 = (FStar_Util.take (fun uu____5671 -> (match (uu____5671) with
| (uu____5676, aq) -> begin
(Prims.op_Equality aq FStar_Parser_AST.FsTypApp)
end)) args)
in (match (uu____5647) with
| (fs_typ_args, args1) -> begin
(

let uu____5714 = (

let uu____5715 = (p_indexingTerm head1)
in (

let uu____5716 = (

let uu____5717 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (soft_surround_map_or_flow (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.empty FStar_Pprint.langle uu____5717 FStar_Pprint.rangle p_fsTypArg fs_typ_args))
in (FStar_Pprint.op_Hat_Hat uu____5715 uu____5716)))
in ((uu____5714), (args1)))
end))
end
| uu____5728 -> begin
(

let uu____5729 = (p_indexingTerm head1)
in ((uu____5729), (args)))
end))
in (match (uu____5602) with
| (head_doc, args1) -> begin
(

let uu____5750 = (

let uu____5751 = (FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space)
in (soft_surround_map_or_flow (Prims.parse_int "2") (Prims.parse_int "0") head_doc uu____5751 break1 FStar_Pprint.empty p_argTerm args1))
in (FStar_Pprint.group uu____5750))
end))
end))
end
| FStar_Parser_AST.Construct (lid, args) when ((is_general_construction e) && (

let uu____5771 = (is_dtuple_constructor lid)
in (not (uu____5771)))) -> begin
(match (args) with
| [] -> begin
(p_quident lid)
end
| (arg)::[] -> begin
(

let uu____5789 = (

let uu____5790 = (p_quident lid)
in (

let uu____5791 = (p_argTerm arg)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5790 uu____5791)))
in (FStar_Pprint.group uu____5789))
end
| (hd1)::tl1 -> begin
(

let uu____5808 = (

let uu____5809 = (

let uu____5810 = (

let uu____5811 = (p_quident lid)
in (

let uu____5812 = (p_argTerm hd1)
in (prefix2 uu____5811 uu____5812)))
in (FStar_Pprint.group uu____5810))
in (

let uu____5813 = (

let uu____5814 = (FStar_Pprint.separate_map break1 p_argTerm tl1)
in (jump2 uu____5814))
in (FStar_Pprint.op_Hat_Hat uu____5809 uu____5813)))
in (FStar_Pprint.group uu____5808))
end)
end
| uu____5819 -> begin
(p_indexingTerm e)
end))
and p_argTerm : (FStar_Parser_AST.term * FStar_Parser_AST.imp)  ->  FStar_Pprint.document = (fun arg_imp -> (match (arg_imp) with
| (u, FStar_Parser_AST.UnivApp) -> begin
(p_universe u)
end
| (e, FStar_Parser_AST.FsTypApp) -> begin
((FStar_Errors.log_issue e.FStar_Parser_AST.range ((FStar_Errors.Warning_UnexpectedFsTypApp), ("Unexpected FsTypApp, output might not be formatted correctly.")));
(

let uu____5828 = (p_indexingTerm e)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.langle uu____5828 FStar_Pprint.rangle));
)
end
| (e, FStar_Parser_AST.Hash) -> begin
(

let uu____5830 = (str "#")
in (

let uu____5831 = (p_indexingTerm e)
in (FStar_Pprint.op_Hat_Hat uu____5830 uu____5831)))
end
| (e, FStar_Parser_AST.Nothing) -> begin
(p_indexingTerm e)
end))
and p_fsTypArg : (FStar_Parser_AST.term * FStar_Parser_AST.imp)  ->  FStar_Pprint.document = (fun uu____5833 -> (match (uu____5833) with
| (e, uu____5839) -> begin
(p_indexingTerm e)
end))
and p_indexingTerm_aux : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun exit1 e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____5844}, (e1)::(e2)::[]) -> begin
(

let uu____5849 = (

let uu____5850 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (

let uu____5851 = (

let uu____5852 = (

let uu____5853 = (p_term false false e2)
in (soft_parens_with_nesting uu____5853))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5852))
in (FStar_Pprint.op_Hat_Hat uu____5850 uu____5851)))
in (FStar_Pprint.group uu____5849))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____5854}, (e1)::(e2)::[]) -> begin
(

let uu____5859 = (

let uu____5860 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (

let uu____5861 = (

let uu____5862 = (

let uu____5863 = (p_term false false e2)
in (soft_brackets_with_nesting uu____5863))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5862))
in (FStar_Pprint.op_Hat_Hat uu____5860 uu____5861)))
in (FStar_Pprint.group uu____5859))
end
| uu____5864 -> begin
(exit1 e)
end))
and p_indexingTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_indexingTerm_aux p_atomicTerm e))
and p_atomicTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.LetOpen (lid, e1) -> begin
(

let uu____5869 = (p_quident lid)
in (

let uu____5870 = (

let uu____5871 = (

let uu____5872 = (p_term false false e1)
in (soft_parens_with_nesting uu____5872))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5871))
in (FStar_Pprint.op_Hat_Hat uu____5869 uu____5870)))
end
| FStar_Parser_AST.Name (lid) -> begin
(p_quident lid)
end
| FStar_Parser_AST.Op (op, (e1)::[]) when (is_general_prefix_op op) -> begin
(

let uu____5878 = (

let uu____5879 = (FStar_Ident.text_of_id op)
in (str uu____5879))
in (

let uu____5880 = (p_atomicTerm e1)
in (FStar_Pprint.op_Hat_Hat uu____5878 uu____5880)))
end
| uu____5881 -> begin
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
| uu____5889 -> begin
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

let uu____5896 = (

let uu____5897 = (FStar_Ident.text_of_id op)
in (str uu____5897))
in (

let uu____5898 = (p_atomicTermNotQUident e1)
in (FStar_Pprint.op_Hat_Hat uu____5896 uu____5898)))
end
| FStar_Parser_AST.Op (op, []) -> begin
(

let uu____5902 = (

let uu____5903 = (

let uu____5904 = (

let uu____5905 = (FStar_Ident.text_of_id op)
in (str uu____5905))
in (

let uu____5906 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat uu____5904 uu____5906)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5903))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5902))
end
| FStar_Parser_AST.Construct (lid, args) when (is_dtuple_constructor lid) -> begin
(

let uu____5921 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (

let uu____5922 = (

let uu____5923 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (

let uu____5924 = (FStar_List.map FStar_Pervasives_Native.fst args)
in (FStar_Pprint.separate_map uu____5923 p_tmEq uu____5924)))
in (

let uu____5931 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____5921 uu____5922 uu____5931))))
end
| FStar_Parser_AST.Project (e1, lid) -> begin
(

let uu____5934 = (

let uu____5935 = (p_atomicTermNotQUident e1)
in (

let uu____5936 = (

let uu____5937 = (p_qlident lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5937))
in (FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0") uu____5935 uu____5936)))
in (FStar_Pprint.group uu____5934))
end
| uu____5938 -> begin
(p_projectionLHS e)
end))
and p_projectionLHS : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (lid) -> begin
(p_qlident lid)
end
| FStar_Parser_AST.Projector (constr_lid, field_lid) -> begin
(

let uu____5943 = (p_quident constr_lid)
in (

let uu____5944 = (

let uu____5945 = (

let uu____5946 = (p_lident field_lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5946))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____5945))
in (FStar_Pprint.op_Hat_Hat uu____5943 uu____5944)))
end
| FStar_Parser_AST.Discrim (constr_lid) -> begin
(

let uu____5948 = (p_quident constr_lid)
in (FStar_Pprint.op_Hat_Hat uu____5948 FStar_Pprint.qmark))
end
| FStar_Parser_AST.Paren (e1) -> begin
(

let uu____5950 = (p_term false false e1)
in (soft_parens_with_nesting uu____5950))
end
| uu____5951 when (is_array e) -> begin
(

let es = (extract_from_list e)
in (

let uu____5955 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar)
in (

let uu____5956 = (

let uu____5957 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (separate_map_or_flow_last uu____5957 (fun ps -> (p_noSeqTerm ps false)) es))
in (

let uu____5960 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") uu____5955 uu____5956 uu____5960)))))
end
| uu____5961 when (is_list e) -> begin
(

let uu____5962 = (

let uu____5963 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (

let uu____5964 = (extract_from_list e)
in (separate_map_or_flow_last uu____5963 (fun ps -> (p_noSeqTerm ps false)) uu____5964)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket uu____5962 FStar_Pprint.rbracket))
end
| uu____5969 when (is_lex_list e) -> begin
(

let uu____5970 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket)
in (

let uu____5971 = (

let uu____5972 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (

let uu____5973 = (extract_from_list e)
in (separate_map_or_flow_last uu____5972 (fun ps -> (p_noSeqTerm ps false)) uu____5973)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____5970 uu____5971 FStar_Pprint.rbracket)))
end
| uu____5978 when (is_ref_set e) -> begin
(

let es = (extract_from_ref_set e)
in (

let uu____5982 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace)
in (

let uu____5983 = (

let uu____5984 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (separate_map_or_flow uu____5984 p_appTerm es))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") uu____5982 uu____5983 FStar_Pprint.rbrace))))
end
| FStar_Parser_AST.Labeled (e1, s, b) -> begin
(

let uu____5988 = (str (Prims.strcat "(*" (Prims.strcat s "*)")))
in (

let uu____5989 = (p_term false false e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5988 uu____5989)))
end
| FStar_Parser_AST.Op (op, args) when (

let uu____5996 = (handleable_op op args)
in (not (uu____5996))) -> begin
(

let uu____5997 = (

let uu____5998 = (

let uu____5999 = (FStar_Ident.text_of_id op)
in (

let uu____6000 = (

let uu____6001 = (

let uu____6002 = (FStar_Util.string_of_int (FStar_List.length args))
in (Prims.strcat uu____6002 " arguments couldn\'t be handled by the pretty printer"))
in (Prims.strcat " with " uu____6001))
in (Prims.strcat uu____5999 uu____6000)))
in (Prims.strcat "Operation " uu____5998))
in (failwith uu____5997))
end
| FStar_Parser_AST.Uvar (id1) -> begin
(

let uu____6004 = (str "u#")
in (

let uu____6005 = (str id1.FStar_Ident.idText)
in (FStar_Pprint.op_Hat_Hat uu____6004 uu____6005)))
end
| FStar_Parser_AST.Wild -> begin
(

let uu____6006 = (p_term false false e)
in (soft_parens_with_nesting uu____6006))
end
| FStar_Parser_AST.Const (uu____6007) -> begin
(

let uu____6008 = (p_term false false e)
in (soft_parens_with_nesting uu____6008))
end
| FStar_Parser_AST.Op (uu____6009) -> begin
(

let uu____6016 = (p_term false false e)
in (soft_parens_with_nesting uu____6016))
end
| FStar_Parser_AST.Tvar (uu____6017) -> begin
(

let uu____6018 = (p_term false false e)
in (soft_parens_with_nesting uu____6018))
end
| FStar_Parser_AST.Var (uu____6019) -> begin
(

let uu____6020 = (p_term false false e)
in (soft_parens_with_nesting uu____6020))
end
| FStar_Parser_AST.Name (uu____6021) -> begin
(

let uu____6022 = (p_term false false e)
in (soft_parens_with_nesting uu____6022))
end
| FStar_Parser_AST.Construct (uu____6023) -> begin
(

let uu____6034 = (p_term false false e)
in (soft_parens_with_nesting uu____6034))
end
| FStar_Parser_AST.Abs (uu____6035) -> begin
(

let uu____6042 = (p_term false false e)
in (soft_parens_with_nesting uu____6042))
end
| FStar_Parser_AST.App (uu____6043) -> begin
(

let uu____6050 = (p_term false false e)
in (soft_parens_with_nesting uu____6050))
end
| FStar_Parser_AST.Let (uu____6051) -> begin
(

let uu____6072 = (p_term false false e)
in (soft_parens_with_nesting uu____6072))
end
| FStar_Parser_AST.LetOpen (uu____6073) -> begin
(

let uu____6078 = (p_term false false e)
in (soft_parens_with_nesting uu____6078))
end
| FStar_Parser_AST.Seq (uu____6079) -> begin
(

let uu____6084 = (p_term false false e)
in (soft_parens_with_nesting uu____6084))
end
| FStar_Parser_AST.Bind (uu____6085) -> begin
(

let uu____6092 = (p_term false false e)
in (soft_parens_with_nesting uu____6092))
end
| FStar_Parser_AST.If (uu____6093) -> begin
(

let uu____6100 = (p_term false false e)
in (soft_parens_with_nesting uu____6100))
end
| FStar_Parser_AST.Match (uu____6101) -> begin
(

let uu____6116 = (p_term false false e)
in (soft_parens_with_nesting uu____6116))
end
| FStar_Parser_AST.TryWith (uu____6117) -> begin
(

let uu____6132 = (p_term false false e)
in (soft_parens_with_nesting uu____6132))
end
| FStar_Parser_AST.Ascribed (uu____6133) -> begin
(

let uu____6142 = (p_term false false e)
in (soft_parens_with_nesting uu____6142))
end
| FStar_Parser_AST.Record (uu____6143) -> begin
(

let uu____6156 = (p_term false false e)
in (soft_parens_with_nesting uu____6156))
end
| FStar_Parser_AST.Project (uu____6157) -> begin
(

let uu____6162 = (p_term false false e)
in (soft_parens_with_nesting uu____6162))
end
| FStar_Parser_AST.Product (uu____6163) -> begin
(

let uu____6170 = (p_term false false e)
in (soft_parens_with_nesting uu____6170))
end
| FStar_Parser_AST.Sum (uu____6171) -> begin
(

let uu____6178 = (p_term false false e)
in (soft_parens_with_nesting uu____6178))
end
| FStar_Parser_AST.QForall (uu____6179) -> begin
(

let uu____6192 = (p_term false false e)
in (soft_parens_with_nesting uu____6192))
end
| FStar_Parser_AST.QExists (uu____6193) -> begin
(

let uu____6206 = (p_term false false e)
in (soft_parens_with_nesting uu____6206))
end
| FStar_Parser_AST.Refine (uu____6207) -> begin
(

let uu____6212 = (p_term false false e)
in (soft_parens_with_nesting uu____6212))
end
| FStar_Parser_AST.NamedTyp (uu____6213) -> begin
(

let uu____6218 = (p_term false false e)
in (soft_parens_with_nesting uu____6218))
end
| FStar_Parser_AST.Requires (uu____6219) -> begin
(

let uu____6226 = (p_term false false e)
in (soft_parens_with_nesting uu____6226))
end
| FStar_Parser_AST.Ensures (uu____6227) -> begin
(

let uu____6234 = (p_term false false e)
in (soft_parens_with_nesting uu____6234))
end
| FStar_Parser_AST.Attributes (uu____6235) -> begin
(

let uu____6238 = (p_term false false e)
in (soft_parens_with_nesting uu____6238))
end
| FStar_Parser_AST.Quote (uu____6239) -> begin
(

let uu____6244 = (p_term false false e)
in (soft_parens_with_nesting uu____6244))
end
| FStar_Parser_AST.VQuote (uu____6245) -> begin
(

let uu____6246 = (p_term false false e)
in (soft_parens_with_nesting uu____6246))
end
| FStar_Parser_AST.Antiquote (uu____6247) -> begin
(

let uu____6252 = (p_term false false e)
in (soft_parens_with_nesting uu____6252))
end))
and p_constant : FStar_Const.sconst  ->  FStar_Pprint.document = (fun uu___69_6253 -> (match (uu___69_6253) with
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

let uu____6257 = (FStar_Pprint.doc_of_char x)
in (FStar_Pprint.squotes uu____6257))
end
| FStar_Const.Const_string (s, uu____6259) -> begin
(

let uu____6260 = (str s)
in (FStar_Pprint.dquotes uu____6260))
end
| FStar_Const.Const_bytearray (bytes, uu____6262) -> begin
(

let uu____6267 = (

let uu____6268 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes uu____6268))
in (

let uu____6269 = (str "B")
in (FStar_Pprint.op_Hat_Hat uu____6267 uu____6269)))
end
| FStar_Const.Const_int (repr, sign_width_opt) -> begin
(

let signedness = (fun uu___67_6289 -> (match (uu___67_6289) with
| FStar_Const.Unsigned -> begin
(str "u")
end
| FStar_Const.Signed -> begin
FStar_Pprint.empty
end))
in (

let width = (fun uu___68_6295 -> (match (uu___68_6295) with
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

let ending = (default_or_map FStar_Pprint.empty (fun uu____6306 -> (match (uu____6306) with
| (s, w) -> begin
(

let uu____6313 = (signedness s)
in (

let uu____6314 = (width w)
in (FStar_Pprint.op_Hat_Hat uu____6313 uu____6314)))
end)) sign_width_opt)
in (

let uu____6315 = (str repr)
in (FStar_Pprint.op_Hat_Hat uu____6315 ending)))))
end
| FStar_Const.Const_range_of -> begin
(str "range_of")
end
| FStar_Const.Const_set_range_of -> begin
(str "set_range_of")
end
| FStar_Const.Const_range (r) -> begin
(

let uu____6317 = (FStar_Range.string_of_range r)
in (str uu____6317))
end
| FStar_Const.Const_reify -> begin
(str "reify")
end
| FStar_Const.Const_reflect (lid) -> begin
(

let uu____6319 = (p_quident lid)
in (

let uu____6320 = (

let uu____6321 = (

let uu____6322 = (str "reflect")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6322))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6321))
in (FStar_Pprint.op_Hat_Hat uu____6319 uu____6320)))
end))
and p_universe : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (

let uu____6324 = (str "u#")
in (

let uu____6325 = (p_atomicUniverse u)
in (FStar_Pprint.op_Hat_Hat uu____6324 uu____6325))))
and p_universeFrom : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match (u.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6327}, (u1)::(u2)::[]) -> begin
(

let uu____6332 = (

let uu____6333 = (p_universeFrom u1)
in (

let uu____6334 = (

let uu____6335 = (p_universeFrom u2)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6335))
in (FStar_Pprint.op_Hat_Slash_Hat uu____6333 uu____6334)))
in (FStar_Pprint.group uu____6332))
end
| FStar_Parser_AST.App (uu____6336) -> begin
(

let uu____6343 = (head_and_args u)
in (match (uu____6343) with
| (head1, args) -> begin
(match (head1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (maybe_max_lid) when (FStar_Ident.lid_equals maybe_max_lid FStar_Parser_Const.max_lid) -> begin
(

let uu____6369 = (

let uu____6370 = (p_qlident FStar_Parser_Const.max_lid)
in (

let uu____6371 = (FStar_Pprint.separate_map FStar_Pprint.space (fun uu____6379 -> (match (uu____6379) with
| (u1, uu____6385) -> begin
(p_atomicUniverse u1)
end)) args)
in (op_Hat_Slash_Plus_Hat uu____6370 uu____6371)))
in (FStar_Pprint.group uu____6369))
end
| uu____6386 -> begin
(

let uu____6387 = (

let uu____6388 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" uu____6388))
in (failwith uu____6387))
end)
end))
end
| uu____6389 -> begin
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

let uu____6412 = (FStar_Ident.text_of_id id1)
in (str uu____6412))
end
| FStar_Parser_AST.Paren (u1) -> begin
(

let uu____6414 = (p_universeFrom u1)
in (soft_parens_with_nesting uu____6414))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6415}, (uu____6416)::(uu____6417)::[]) -> begin
(

let uu____6420 = (p_universeFrom u)
in (soft_parens_with_nesting uu____6420))
end
| FStar_Parser_AST.App (uu____6421) -> begin
(

let uu____6428 = (p_universeFrom u)
in (soft_parens_with_nesting uu____6428))
end
| uu____6429 -> begin
(

let uu____6430 = (

let uu____6431 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" uu____6431))
in (failwith uu____6430))
end))


let term_to_document : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_term false false e))


let signature_to_document : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun e -> (p_justSig e))


let decl_to_document : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun e -> (p_decl e))


let pat_to_document : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (p_disjunctivePattern p))


let binder_to_document : FStar_Parser_AST.binder  ->  FStar_Pprint.document = (fun b -> (p_binder true b))


let modul_to_document : FStar_Parser_AST.modul  ->  FStar_Pprint.document = (fun m -> ((FStar_ST.op_Colon_Equals should_print_fs_typ_app false);
(

let res = (match (m) with
| FStar_Parser_AST.Module (uu____6487, decls) -> begin
(

let uu____6493 = (FStar_All.pipe_right decls (FStar_List.map decl_to_document))
in (FStar_All.pipe_right uu____6493 (FStar_Pprint.separate FStar_Pprint.hardline)))
end
| FStar_Parser_AST.Interface (uu____6502, decls, uu____6504) -> begin
(

let uu____6509 = (FStar_All.pipe_right decls (FStar_List.map decl_to_document))
in (FStar_All.pipe_right uu____6509 (FStar_Pprint.separate FStar_Pprint.hardline)))
end)
in ((FStar_ST.op_Colon_Equals should_print_fs_typ_app false);
res;
));
))


let comments_to_document : (Prims.string * FStar_Range.range) Prims.list  ->  FStar_Pprint.document = (fun comments -> (FStar_Pprint.separate_map FStar_Pprint.hardline (fun uu____6566 -> (match (uu____6566) with
| (comment, range) -> begin
(str comment)
end)) comments))


let modul_with_comments_to_document : FStar_Parser_AST.modul  ->  (Prims.string * FStar_Range.range) Prims.list  ->  (FStar_Pprint.document * (Prims.string * FStar_Range.range) Prims.list) = (fun m comments -> (

let decls = (match (m) with
| FStar_Parser_AST.Module (uu____6610, decls) -> begin
decls
end
| FStar_Parser_AST.Interface (uu____6616, decls, uu____6618) -> begin
decls
end)
in ((FStar_ST.op_Colon_Equals should_print_fs_typ_app false);
(match (decls) with
| [] -> begin
((FStar_Pprint.empty), (comments))
end
| (d)::ds -> begin
(

let uu____6667 = (match (ds) with
| ({FStar_Parser_AST.d = FStar_Parser_AST.Pragma (FStar_Parser_AST.LightOff); FStar_Parser_AST.drange = uu____6680; FStar_Parser_AST.doc = uu____6681; FStar_Parser_AST.quals = uu____6682; FStar_Parser_AST.attrs = uu____6683})::uu____6684 -> begin
(

let d0 = (FStar_List.hd ds)
in (

let uu____6690 = (

let uu____6693 = (

let uu____6696 = (FStar_List.tl ds)
in (d)::uu____6696)
in (d0)::uu____6693)
in ((uu____6690), (d0.FStar_Parser_AST.drange))))
end
| uu____6701 -> begin
(((d)::ds), (d.FStar_Parser_AST.drange))
end)
in (match (uu____6667) with
| (decls1, first_range) -> begin
(

let extract_decl_range = (fun d1 -> d1.FStar_Parser_AST.drange)
in ((FStar_ST.op_Colon_Equals comment_stack comments);
(

let initial_comment = (

let uu____6765 = (FStar_Range.start_of_range first_range)
in (place_comments_until_pos (Prims.parse_int "0") (Prims.parse_int "1") uu____6765 FStar_Pprint.empty))
in (

let doc1 = (separate_map_with_comments FStar_Pprint.empty FStar_Pprint.empty decl_to_document decls1 extract_decl_range)
in (

let comments1 = (FStar_ST.op_Bang comment_stack)
in ((FStar_ST.op_Colon_Equals comment_stack []);
(FStar_ST.op_Colon_Equals should_print_fs_typ_app false);
(

let uu____6873 = (FStar_Pprint.op_Hat_Hat initial_comment doc1)
in ((uu____6873), (comments1)));
))));
))
end))
end);
)))




