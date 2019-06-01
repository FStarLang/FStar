
open Prims
open FStar_Pervasives

let min : Prims.int  ->  Prims.int  ->  Prims.int = (fun x y -> (match ((x > y)) with
| true -> begin
y
end
| uu____22 -> begin
x
end))


let max : Prims.int  ->  Prims.int  ->  Prims.int = (fun x y -> (match ((x > y)) with
| true -> begin
x
end
| uu____42 -> begin
y
end))


let map_rev : 'a 'b . ('a  ->  'b)  ->  'a Prims.list  ->  'b Prims.list = (fun f l -> (

let rec aux = (fun l1 acc -> (match (l1) with
| [] -> begin
acc
end
| (x)::xs -> begin
(

let uu____103 = (

let uu____106 = (f x)
in (uu____106)::acc)
in (aux xs uu____103))
end))
in (aux l [])))


let rec map_if_all : 'a 'b . ('a  ->  'b FStar_Pervasives_Native.option)  ->  'a Prims.list  ->  'b Prims.list FStar_Pervasives_Native.option = (fun f l -> (

let rec aux = (fun l1 acc -> (match (l1) with
| [] -> begin
acc
end
| (x)::xs -> begin
(

let uu____173 = (f x)
in (match (uu____173) with
| FStar_Pervasives_Native.Some (r) -> begin
(aux xs ((r)::acc))
end
| FStar_Pervasives_Native.None -> begin
[]
end))
end))
in (

let r = (aux l [])
in (match ((Prims.op_Equality (FStar_List.length l) (FStar_List.length r))) with
| true -> begin
FStar_Pervasives_Native.Some (r)
end
| uu____189 -> begin
FStar_Pervasives_Native.None
end))))


let rec all : 'a . ('a  ->  Prims.bool)  ->  'a Prims.list  ->  Prims.bool = (fun f l -> (match (l) with
| [] -> begin
true
end
| (x)::xs -> begin
(

let uu____229 = (f x)
in (match (uu____229) with
| true -> begin
(all f xs)
end
| uu____233 -> begin
false
end))
end))


let all_explicit : (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  Prims.bool = (fun args -> (FStar_Util.for_all (fun uu___0_262 -> (match (uu___0_262) with
| (uu____268, FStar_Parser_AST.Nothing) -> begin
true
end
| uu____270 -> begin
false
end)) args))


let should_print_fs_typ_app : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let unfold_tuples : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref true)


let with_fs_typ_app : 'Auu____299 'Auu____300 . Prims.bool  ->  ('Auu____299  ->  'Auu____300)  ->  'Auu____299  ->  'Auu____300 = (fun b printer t -> (

let b0 = (FStar_ST.op_Bang should_print_fs_typ_app)
in ((FStar_ST.op_Colon_Equals should_print_fs_typ_app b);
(

let res = (printer t)
in ((FStar_ST.op_Colon_Equals should_print_fs_typ_app b0);
res;
));
)))


let str : Prims.string  ->  FStar_Pprint.document = (fun s -> (FStar_Pprint.doc_of_string s))


let default_or_map : 'Auu____410 'Auu____411 . 'Auu____410  ->  ('Auu____411  ->  'Auu____410)  ->  'Auu____411 FStar_Pervasives_Native.option  ->  'Auu____410 = (fun n1 f x -> (match (x) with
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
| uu____462 -> begin
(prefix2 prefix_ body)
end))


let op_Hat_Slash_Plus_Hat : FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun prefix_ body -> (prefix2 prefix_ body))


let jump2 : FStar_Pprint.document  ->  FStar_Pprint.document = (fun body -> (FStar_Pprint.jump (Prims.parse_int "2") (Prims.parse_int "1") body))


let infix2 : FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (FStar_Pprint.infix (Prims.parse_int "2") (Prims.parse_int "1"))


let infix0 : FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (FStar_Pprint.infix (Prims.parse_int "0") (Prims.parse_int "1"))


let break1 : FStar_Pprint.document = (FStar_Pprint.break_ (Prims.parse_int "1"))


let separate_break_map : 'Auu____524 . FStar_Pprint.document  ->  ('Auu____524  ->  FStar_Pprint.document)  ->  'Auu____524 Prims.list  ->  FStar_Pprint.document = (fun sep f l -> (

let uu____549 = (

let uu____550 = (

let uu____551 = (FStar_Pprint.op_Hat_Hat sep break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____551))
in (FStar_Pprint.separate_map uu____550 f l))
in (FStar_Pprint.group uu____549)))


let precede_break_separate_map : 'Auu____563 . FStar_Pprint.document  ->  FStar_Pprint.document  ->  ('Auu____563  ->  FStar_Pprint.document)  ->  'Auu____563 Prims.list  ->  FStar_Pprint.document = (fun prec sep f l -> (

let uu____593 = (

let uu____594 = (FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space)
in (

let uu____595 = (

let uu____596 = (FStar_List.hd l)
in (FStar_All.pipe_right uu____596 f))
in (FStar_Pprint.precede uu____594 uu____595)))
in (

let uu____597 = (

let uu____598 = (FStar_List.tl l)
in (FStar_Pprint.concat_map (fun x -> (

let uu____604 = (

let uu____605 = (

let uu____606 = (f x)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____606))
in (FStar_Pprint.op_Hat_Hat sep uu____605))
in (FStar_Pprint.op_Hat_Hat break1 uu____604))) uu____598))
in (FStar_Pprint.op_Hat_Hat uu____593 uu____597))))


let concat_break_map : 'Auu____614 . ('Auu____614  ->  FStar_Pprint.document)  ->  'Auu____614 Prims.list  ->  FStar_Pprint.document = (fun f l -> (

let uu____634 = (FStar_Pprint.concat_map (fun x -> (

let uu____638 = (f x)
in (FStar_Pprint.op_Hat_Hat uu____638 break1))) l)
in (FStar_Pprint.group uu____634)))


let parens_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lparen contents FStar_Pprint.rparen))


let soft_parens_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lparen contents FStar_Pprint.rparen))


let braces_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbrace contents FStar_Pprint.rbrace))


let soft_braces_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbrace contents FStar_Pprint.rbrace))


let soft_braces_with_nesting_tight : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbrace contents FStar_Pprint.rbrace))


let brackets_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbracket contents FStar_Pprint.rbracket))


let soft_brackets_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbracket contents FStar_Pprint.rbracket))


let soft_begin_end_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (

let uu____701 = (str "begin")
in (

let uu____703 = (str "end")
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") uu____701 contents uu____703))))


let separate_map_last : 'Auu____716 . FStar_Pprint.document  ->  (Prims.bool  ->  'Auu____716  ->  FStar_Pprint.document)  ->  'Auu____716 Prims.list  ->  FStar_Pprint.document = (fun sep f es -> (

let l = (FStar_List.length es)
in (

let es1 = (FStar_List.mapi (fun i e -> (f (Prims.op_disEquality i (l - (Prims.parse_int "1"))) e)) es)
in (FStar_Pprint.separate sep es1))))


let separate_break_map_last : 'Auu____768 . FStar_Pprint.document  ->  (Prims.bool  ->  'Auu____768  ->  FStar_Pprint.document)  ->  'Auu____768 Prims.list  ->  FStar_Pprint.document = (fun sep f l -> (

let uu____800 = (

let uu____801 = (

let uu____802 = (FStar_Pprint.op_Hat_Hat sep break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____802))
in (separate_map_last uu____801 f l))
in (FStar_Pprint.group uu____800)))


let separate_map_or_flow : 'Auu____812 . FStar_Pprint.document  ->  ('Auu____812  ->  FStar_Pprint.document)  ->  'Auu____812 Prims.list  ->  FStar_Pprint.document = (fun sep f l -> (match (((FStar_List.length l) < (Prims.parse_int "10"))) with
| true -> begin
(FStar_Pprint.separate_map sep f l)
end
| uu____839 -> begin
(FStar_Pprint.flow_map sep f l)
end))


let flow_map_last : 'Auu____850 . FStar_Pprint.document  ->  (Prims.bool  ->  'Auu____850  ->  FStar_Pprint.document)  ->  'Auu____850 Prims.list  ->  FStar_Pprint.document = (fun sep f es -> (

let l = (FStar_List.length es)
in (

let es1 = (FStar_List.mapi (fun i e -> (f (Prims.op_disEquality i (l - (Prims.parse_int "1"))) e)) es)
in (FStar_Pprint.flow sep es1))))


let separate_map_or_flow_last : 'Auu____902 . FStar_Pprint.document  ->  (Prims.bool  ->  'Auu____902  ->  FStar_Pprint.document)  ->  'Auu____902 Prims.list  ->  FStar_Pprint.document = (fun sep f l -> (match (((FStar_List.length l) < (Prims.parse_int "10"))) with
| true -> begin
(separate_map_last sep f l)
end
| uu____936 -> begin
(flow_map_last sep f l)
end))


let separate_or_flow : FStar_Pprint.document  ->  FStar_Pprint.document Prims.list  ->  FStar_Pprint.document = (fun sep l -> (separate_map_or_flow sep FStar_Pervasives.id l))


let surround_maybe_empty : Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun n1 b doc1 doc2 doc3 -> (match ((Prims.op_Equality doc2 FStar_Pprint.empty)) with
| true -> begin
(

let uu____984 = (FStar_Pprint.op_Hat_Slash_Hat doc1 doc3)
in (FStar_Pprint.group uu____984))
end
| uu____985 -> begin
(FStar_Pprint.surround n1 b doc1 doc2 doc3)
end))


let soft_surround_separate_map : 'Auu____1006 . Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  ('Auu____1006  ->  FStar_Pprint.document)  ->  'Auu____1006 Prims.list  ->  FStar_Pprint.document = (fun n1 b void_ opening sep closing f xs -> (match ((Prims.op_Equality xs [])) with
| true -> begin
void_
end
| uu____1063 -> begin
(

let uu____1065 = (FStar_Pprint.separate_map sep f xs)
in (FStar_Pprint.soft_surround n1 b opening uu____1065 closing))
end))


let soft_surround_map_or_flow : 'Auu____1085 . Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  ('Auu____1085  ->  FStar_Pprint.document)  ->  'Auu____1085 Prims.list  ->  FStar_Pprint.document = (fun n1 b void_ opening sep closing f xs -> (match ((Prims.op_Equality xs [])) with
| true -> begin
void_
end
| uu____1142 -> begin
(

let uu____1144 = (separate_map_or_flow sep f xs)
in (FStar_Pprint.soft_surround n1 b opening uu____1144 closing))
end))


let doc_of_fsdoc : (Prims.string * (Prims.string * Prims.string) Prims.list)  ->  FStar_Pprint.document = (fun uu____1163 -> (match (uu____1163) with
| (comment, keywords) -> begin
(

let uu____1197 = (

let uu____1198 = (

let uu____1201 = (str comment)
in (

let uu____1202 = (

let uu____1205 = (

let uu____1208 = (FStar_Pprint.separate_map FStar_Pprint.comma (fun uu____1219 -> (match (uu____1219) with
| (k, v1) -> begin
(

let uu____1232 = (

let uu____1235 = (str k)
in (

let uu____1236 = (

let uu____1239 = (

let uu____1242 = (str v1)
in (uu____1242)::[])
in (FStar_Pprint.rarrow)::uu____1239)
in (uu____1235)::uu____1236))
in (FStar_Pprint.concat uu____1232))
end)) keywords)
in (uu____1208)::[])
in (FStar_Pprint.space)::uu____1205)
in (uu____1201)::uu____1202))
in (FStar_Pprint.concat uu____1198))
in (FStar_Pprint.group uu____1197))
end))


let is_unit : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Const (FStar_Const.Const_unit) -> begin
true
end
| uu____1252 -> begin
false
end))


let matches_var : FStar_Parser_AST.term  ->  FStar_Ident.ident  ->  Prims.bool = (fun t x -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (y) -> begin
(

let uu____1268 = (FStar_Ident.text_of_lid y)
in (Prims.op_Equality x.FStar_Ident.idText uu____1268))
end
| uu____1271 -> begin
false
end))


let is_tuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Parser_Const.is_tuple_data_lid'


let is_dtuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Parser_Const.is_dtuple_data_lid'


let is_list_structure : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun cons_lid1 nil_lid1 -> (

let rec aux = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (lid, []) -> begin
(FStar_Ident.lid_equals lid nil_lid1)
end
| FStar_Parser_AST.Construct (lid, (uu____1322)::((e2, uu____1324))::[]) -> begin
((FStar_Ident.lid_equals lid cons_lid1) && (aux e2))
end
| uu____1347 -> begin
false
end))
in aux))


let is_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Parser_Const.cons_lid FStar_Parser_Const.nil_lid)


let is_lex_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Parser_Const.lexcons_lid FStar_Parser_Const.lextop_lid)


let rec extract_from_list : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (uu____1371, []) -> begin
[]
end
| FStar_Parser_AST.Construct (uu____1382, ((e1, FStar_Parser_AST.Nothing))::((e2, FStar_Parser_AST.Nothing))::[]) -> begin
(

let uu____1403 = (extract_from_list e2)
in (e1)::uu____1403)
end
| uu____1406 -> begin
(

let uu____1407 = (

let uu____1409 = (FStar_Parser_AST.term_to_string e)
in (FStar_Util.format1 "Not a list %s" uu____1409))
in (failwith uu____1407))
end))


let is_array : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (lid); FStar_Parser_AST.range = uu____1423; FStar_Parser_AST.level = uu____1424}, l, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) && (is_list l))
end
| uu____1426 -> begin
false
end))


let rec is_ref_set : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (maybe_empty_lid) -> begin
(FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty)
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_singleton_lid); FStar_Parser_AST.range = uu____1438; FStar_Parser_AST.level = uu____1439}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_addr_of_lid); FStar_Parser_AST.range = uu____1441; FStar_Parser_AST.level = uu____1442}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____1444; FStar_Parser_AST.level = uu____1445}, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals maybe_singleton_lid FStar_Parser_Const.set_singleton) && (FStar_Ident.lid_equals maybe_addr_of_lid FStar_Parser_Const.heap_addr_of_lid))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_union_lid); FStar_Parser_AST.range = uu____1447; FStar_Parser_AST.level = uu____1448}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____1450; FStar_Parser_AST.level = uu____1451}, e2, FStar_Parser_AST.Nothing) -> begin
(((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union) && (is_ref_set e1)) && (is_ref_set e2))
end
| uu____1453 -> begin
false
end))


let rec extract_from_ref_set : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (uu____1465) -> begin
[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (uu____1466); FStar_Parser_AST.range = uu____1467; FStar_Parser_AST.level = uu____1468}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (uu____1469); FStar_Parser_AST.range = uu____1470; FStar_Parser_AST.level = uu____1471}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____1473; FStar_Parser_AST.level = uu____1474}, FStar_Parser_AST.Nothing) -> begin
(e1)::[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (uu____1475); FStar_Parser_AST.range = uu____1476; FStar_Parser_AST.level = uu____1477}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____1479; FStar_Parser_AST.level = uu____1480}, e2, FStar_Parser_AST.Nothing) -> begin
(

let uu____1482 = (extract_from_ref_set e1)
in (

let uu____1485 = (extract_from_ref_set e2)
in (FStar_List.append uu____1482 uu____1485)))
end
| uu____1488 -> begin
(

let uu____1489 = (

let uu____1491 = (FStar_Parser_AST.term_to_string e)
in (FStar_Util.format1 "Not a ref set %s" uu____1491))
in (failwith uu____1489))
end))


let is_general_application : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____1503 = ((is_array e) || (is_ref_set e))
in (not (uu____1503))))


let is_general_construction : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____1512 = ((is_list e) || (is_lex_list e))
in (not (uu____1512))))


let is_general_prefix_op : FStar_Ident.ident  ->  Prims.bool = (fun op -> (

let op_starting_char = (

let uu____1523 = (FStar_Ident.text_of_id op)
in (FStar_Util.char_at uu____1523 (Prims.parse_int "0")))
in (((Prims.op_Equality op_starting_char 33 (*!*)) || (Prims.op_Equality op_starting_char 63 (*?*))) || ((Prims.op_Equality op_starting_char 126 (*~*)) && (

let uu____1533 = (FStar_Ident.text_of_id op)
in (Prims.op_disEquality uu____1533 "~"))))))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun e -> (

let rec aux = (fun e1 acc -> (match (e1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App (head1, arg, imp) -> begin
(aux head1 ((((arg), (imp)))::acc))
end
| uu____1603 -> begin
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
| uu____1623 -> begin
false
end))


let uu___is_Right : associativity  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Right -> begin
true
end
| uu____1634 -> begin
false
end))


let uu___is_NonAssoc : associativity  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NonAssoc -> begin
true
end
| uu____1645 -> begin
false
end))


type token =
(FStar_Char.char, Prims.string) FStar_Util.either


type associativity_level =
(associativity * token Prims.list)


let token_to_string : (FStar_BaseTypes.char, Prims.string) FStar_Util.either  ->  Prims.string = (fun uu___1_1671 -> (match (uu___1_1671) with
| FStar_Util.Inl (c) -> begin
(Prims.op_Hat (FStar_Util.string_of_char c) ".*")
end
| FStar_Util.Inr (s) -> begin
s
end))


let matches_token : Prims.string  ->  (FStar_Char.char, Prims.string) FStar_Util.either  ->  Prims.bool = (fun s uu___2_1706 -> (match (uu___2_1706) with
| FStar_Util.Inl (c) -> begin
(

let uu____1719 = (FStar_String.get s (Prims.parse_int "0"))
in (Prims.op_Equality uu____1719 c))
end
| FStar_Util.Inr (s') -> begin
(Prims.op_Equality s s')
end))


let matches_level : 'Auu____1735 . Prims.string  ->  ('Auu____1735 * (FStar_Char.char, Prims.string) FStar_Util.either Prims.list)  ->  Prims.bool = (fun s uu____1759 -> (match (uu____1759) with
| (assoc_levels, tokens) -> begin
(

let uu____1791 = (FStar_List.tryFind (matches_token s) tokens)
in (Prims.op_disEquality uu____1791 FStar_Pervasives_Native.None))
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

let levels_from_associativity = (fun l uu___3_1963 -> (match (uu___3_1963) with
| Left -> begin
((l), (l), ((l - (Prims.parse_int "1"))))
end
| Right -> begin
(((l - (Prims.parse_int "1"))), (l), (l))
end
| NonAssoc -> begin
(((l - (Prims.parse_int "1"))), (l), ((l - (Prims.parse_int "1"))))
end))
in (FStar_List.mapi (fun i uu____2013 -> (match (uu____2013) with
| (assoc1, tokens) -> begin
(((levels_from_associativity i assoc1)), (tokens))
end)) level_associativity_spec))


let assign_levels : associativity_level Prims.list  ->  Prims.string  ->  (Prims.int * Prims.int * Prims.int) = (fun token_associativity_spec s -> (

let uu____2088 = (FStar_List.tryFind (matches_level s) level_table)
in (match (uu____2088) with
| FStar_Pervasives_Native.Some (assoc_levels, uu____2140) -> begin
assoc_levels
end
| uu____2178 -> begin
(failwith (Prims.op_Hat "Unrecognized operator " s))
end)))


let max_level : 'Auu____2211 . ('Auu____2211 * token Prims.list) Prims.list  ->  Prims.int = (fun l -> (

let find_level_and_max = (fun n1 level -> (

let uu____2260 = (FStar_List.tryFind (fun uu____2296 -> (match (uu____2296) with
| (uu____2313, tokens) -> begin
(Prims.op_Equality tokens (FStar_Pervasives_Native.snd level))
end)) level_table)
in (match (uu____2260) with
| FStar_Pervasives_Native.Some ((uu____2342, l1, uu____2344), uu____2345) -> begin
(max n1 l1)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____2395 = (

let uu____2397 = (

let uu____2399 = (FStar_List.map token_to_string (FStar_Pervasives_Native.snd level))
in (FStar_String.concat "," uu____2399))
in (FStar_Util.format1 "Undefined associativity level %s" uu____2397))
in (failwith uu____2395))
end)))
in (FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l)))


let levels : Prims.string  ->  (Prims.int * Prims.int * Prims.int) = (fun op -> (

let uu____2434 = (assign_levels level_associativity_spec op)
in (match (uu____2434) with
| (left1, mine, right1) -> begin
(match ((Prims.op_Equality op "*")) with
| true -> begin
(((left1 - (Prims.parse_int "1"))), (mine), (right1))
end
| uu____2478 -> begin
((left1), (mine), (right1))
end)
end)))


let operatorInfix0ad12 : associativity_level Prims.list = (opinfix0a)::(opinfix0b)::(opinfix0c)::(opinfix0d)::(opinfix1)::(opinfix2)::[]


let is_operatorInfix0ad12 : FStar_Ident.ident  ->  Prims.bool = (fun op -> (

let uu____2493 = (

let uu____2496 = (

let uu____2502 = (FStar_Ident.text_of_id op)
in (FStar_All.pipe_left matches_level uu____2502))
in (FStar_List.tryFind uu____2496 operatorInfix0ad12))
in (Prims.op_disEquality uu____2493 FStar_Pervasives_Native.None)))


let is_operatorInfix34 : FStar_Ident.ident  ->  Prims.bool = (

let opinfix34 = (opinfix3)::(opinfix4)::[]
in (fun op -> (

let uu____2569 = (

let uu____2584 = (

let uu____2602 = (FStar_Ident.text_of_id op)
in (FStar_All.pipe_left matches_level uu____2602))
in (FStar_List.tryFind uu____2584 opinfix34))
in (Prims.op_disEquality uu____2569 FStar_Pervasives_Native.None))))


let handleable_args_length : FStar_Ident.ident  ->  Prims.int = (fun op -> (

let op_s = (FStar_Ident.text_of_id op)
in (

let uu____2668 = ((is_general_prefix_op op) || (FStar_List.mem op_s (("-")::("~")::[])))
in (match (uu____2668) with
| true -> begin
(Prims.parse_int "1")
end
| uu____2679 -> begin
(

let uu____2681 = (((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) || (FStar_List.mem op_s (("<==>")::("==>")::("\\/")::("/\\")::("=")::("|>")::(":=")::(".()")::(".[]")::[])))
in (match (uu____2681) with
| true -> begin
(Prims.parse_int "2")
end
| uu____2706 -> begin
(match ((FStar_List.mem op_s ((".()<-")::(".[]<-")::[]))) with
| true -> begin
(Prims.parse_int "3")
end
| uu____2717 -> begin
(Prims.parse_int "0")
end)
end))
end))))


let handleable_op : 'Auu____2727 . FStar_Ident.ident  ->  'Auu____2727 Prims.list  ->  Prims.bool = (fun op args -> (match ((FStar_List.length args)) with
| _2743 when (_2743 = (Prims.parse_int "0")) -> begin
true
end
| _2745 when (_2745 = (Prims.parse_int "1")) -> begin
((is_general_prefix_op op) || (

let uu____2747 = (FStar_Ident.text_of_id op)
in (FStar_List.mem uu____2747 (("-")::("~")::[]))))
end
| _2755 when (_2755 = (Prims.parse_int "2")) -> begin
(((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) || (

let uu____2757 = (FStar_Ident.text_of_id op)
in (FStar_List.mem uu____2757 (("<==>")::("==>")::("\\/")::("/\\")::("=")::("|>")::(":=")::(".()")::(".[]")::[]))))
end
| _2779 when (_2779 = (Prims.parse_int "3")) -> begin
(

let uu____2780 = (FStar_Ident.text_of_id op)
in (FStar_List.mem uu____2780 ((".()<-")::(".[]<-")::[])))
end
| uu____2788 -> begin
false
end))

type annotation_style =
| Binders of (Prims.int * Prims.int * Prims.bool)
| Arrows of (Prims.int * Prims.int)


let uu___is_Binders : annotation_style  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Binders (_0) -> begin
true
end
| uu____2834 -> begin
false
end))


let __proj__Binders__item___0 : annotation_style  ->  (Prims.int * Prims.int * Prims.bool) = (fun projectee -> (match (projectee) with
| Binders (_0) -> begin
_0
end))


let uu___is_Arrows : annotation_style  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Arrows (_0) -> begin
true
end
| uu____2886 -> begin
false
end))


let __proj__Arrows__item___0 : annotation_style  ->  (Prims.int * Prims.int) = (fun projectee -> (match (projectee) with
| Arrows (_0) -> begin
_0
end))


let all_binders_annot : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let is_binder_annot = (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (uu____2928) -> begin
true
end
| uu____2934 -> begin
false
end))
in (

let rec all_binders = (fun e1 l -> (match (e1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Product (bs, tgt) -> begin
(

let uu____2967 = (FStar_List.for_all is_binder_annot bs)
in (match (uu____2967) with
| true -> begin
(all_binders tgt (l + (FStar_List.length bs)))
end
| uu____2976 -> begin
((false), ((Prims.parse_int "0")))
end))
end
| uu____2982 -> begin
((true), ((l + (Prims.parse_int "1"))))
end))
in (

let uu____2987 = (all_binders e (Prims.parse_int "0"))
in (match (uu____2987) with
| (b, l) -> begin
(match ((b && (l > (Prims.parse_int "1")))) with
| true -> begin
true
end
| uu____3006 -> begin
false
end)
end)))))


type catf =
FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document


let cat_with_colon : FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun x y -> (

let uu____3026 = (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon y)
in (FStar_Pprint.op_Hat_Hat x uu____3026)))


let comment_stack : (Prims.string * FStar_Range.range) Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

type decl_meta =
{r : FStar_Range.range; has_qs : Prims.bool; has_attrs : Prims.bool; has_fsdoc : Prims.bool; is_fsdoc : Prims.bool}


let __proj__Mkdecl_meta__item__r : decl_meta  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {r = r; has_qs = has_qs; has_attrs = has_attrs; has_fsdoc = has_fsdoc; is_fsdoc = is_fsdoc} -> begin
r
end))


let __proj__Mkdecl_meta__item__has_qs : decl_meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {r = r; has_qs = has_qs; has_attrs = has_attrs; has_fsdoc = has_fsdoc; is_fsdoc = is_fsdoc} -> begin
has_qs
end))


let __proj__Mkdecl_meta__item__has_attrs : decl_meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {r = r; has_qs = has_qs; has_attrs = has_attrs; has_fsdoc = has_fsdoc; is_fsdoc = is_fsdoc} -> begin
has_attrs
end))


let __proj__Mkdecl_meta__item__has_fsdoc : decl_meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {r = r; has_qs = has_qs; has_attrs = has_attrs; has_fsdoc = has_fsdoc; is_fsdoc = is_fsdoc} -> begin
has_fsdoc
end))


let __proj__Mkdecl_meta__item__is_fsdoc : decl_meta  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {r = r; has_qs = has_qs; has_attrs = has_attrs; has_fsdoc = has_fsdoc; is_fsdoc = is_fsdoc} -> begin
is_fsdoc
end))


let dummy_meta : decl_meta = {r = FStar_Range.dummyRange; has_qs = false; has_attrs = false; has_fsdoc = false; is_fsdoc = false}


let with_comment : 'Auu____3175 . ('Auu____3175  ->  FStar_Pprint.document)  ->  'Auu____3175  ->  FStar_Range.range  ->  FStar_Pprint.document = (fun printer tm tmrange -> (

let rec comments_before_pos = (fun acc print_pos lookahead_pos -> (

let uu____3217 = (FStar_ST.op_Bang comment_stack)
in (match (uu____3217) with
| [] -> begin
((acc), (false))
end
| ((c, crange))::cs -> begin
(

let comment = (

let uu____3288 = (str c)
in (FStar_Pprint.op_Hat_Hat uu____3288 FStar_Pprint.hardline))
in (

let uu____3289 = (FStar_Range.range_before_pos crange print_pos)
in (match (uu____3289) with
| true -> begin
((FStar_ST.op_Colon_Equals comment_stack cs);
(

let uu____3331 = (FStar_Pprint.op_Hat_Hat acc comment)
in (comments_before_pos uu____3331 print_pos lookahead_pos));
)
end
| uu____3332 -> begin
(

let uu____3334 = (FStar_Range.range_before_pos crange lookahead_pos)
in ((acc), (uu____3334)))
end)))
end)))
in (

let uu____3337 = (

let uu____3343 = (

let uu____3344 = (FStar_Range.start_of_range tmrange)
in (FStar_Range.end_of_line uu____3344))
in (

let uu____3345 = (FStar_Range.end_of_range tmrange)
in (comments_before_pos FStar_Pprint.empty uu____3343 uu____3345)))
in (match (uu____3337) with
| (comments, has_lookahead) -> begin
(

let printed_e = (printer tm)
in (

let comments1 = (match (has_lookahead) with
| true -> begin
(

let pos = (FStar_Range.end_of_range tmrange)
in (

let uu____3354 = (comments_before_pos comments pos pos)
in (FStar_Pervasives_Native.fst uu____3354)))
end
| uu____3361 -> begin
comments
end)
in (match ((Prims.op_Equality comments1 FStar_Pprint.empty)) with
| true -> begin
printed_e
end
| uu____3364 -> begin
(

let uu____3366 = (FStar_Pprint.op_Hat_Hat comments1 printed_e)
in (FStar_Pprint.group uu____3366))
end)))
end))))


let with_comment_sep : 'Auu____3378 'Auu____3379 . ('Auu____3378  ->  'Auu____3379)  ->  'Auu____3378  ->  FStar_Range.range  ->  (FStar_Pprint.document * 'Auu____3379) = (fun printer tm tmrange -> (

let rec comments_before_pos = (fun acc print_pos lookahead_pos -> (

let uu____3425 = (FStar_ST.op_Bang comment_stack)
in (match (uu____3425) with
| [] -> begin
((acc), (false))
end
| ((c, crange))::cs -> begin
(

let comment = (str c)
in (

let uu____3496 = (FStar_Range.range_before_pos crange print_pos)
in (match (uu____3496) with
| true -> begin
((FStar_ST.op_Colon_Equals comment_stack cs);
(

let uu____3538 = (match ((Prims.op_Equality acc FStar_Pprint.empty)) with
| true -> begin
comment
end
| uu____3540 -> begin
(

let uu____3542 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline comment)
in (FStar_Pprint.op_Hat_Hat acc uu____3542))
end)
in (comments_before_pos uu____3538 print_pos lookahead_pos));
)
end
| uu____3543 -> begin
(

let uu____3545 = (FStar_Range.range_before_pos crange lookahead_pos)
in ((acc), (uu____3545)))
end)))
end)))
in (

let uu____3548 = (

let uu____3554 = (

let uu____3555 = (FStar_Range.start_of_range tmrange)
in (FStar_Range.end_of_line uu____3555))
in (

let uu____3556 = (FStar_Range.end_of_range tmrange)
in (comments_before_pos FStar_Pprint.empty uu____3554 uu____3556)))
in (match (uu____3548) with
| (comments, has_lookahead) -> begin
(

let printed_e = (printer tm)
in (

let comments1 = (match (has_lookahead) with
| true -> begin
(

let pos = (FStar_Range.end_of_range tmrange)
in (

let uu____3569 = (comments_before_pos comments pos pos)
in (FStar_Pervasives_Native.fst uu____3569)))
end
| uu____3576 -> begin
comments
end)
in ((comments1), (printed_e))))
end))))


let rec place_comments_until_pos : Prims.int  ->  Prims.int  ->  FStar_Range.pos  ->  decl_meta  ->  FStar_Pprint.document  ->  Prims.bool  ->  Prims.bool  ->  FStar_Pprint.document = (fun k lbegin pos meta_decl doc1 r init1 -> (

let uu____3622 = (FStar_ST.op_Bang comment_stack)
in (match (uu____3622) with
| ((comment, crange))::cs when (FStar_Range.range_before_pos crange pos) -> begin
((FStar_ST.op_Colon_Equals comment_stack cs);
(

let lnum = (

let uu____3716 = (

let uu____3718 = (

let uu____3720 = (FStar_Range.start_of_range crange)
in (FStar_Range.line_of_pos uu____3720))
in (uu____3718 - lbegin))
in (max k uu____3716))
in (

let lnum1 = (min (Prims.parse_int "2") lnum)
in (

let doc2 = (

let uu____3725 = (

let uu____3726 = (FStar_Pprint.repeat lnum1 FStar_Pprint.hardline)
in (

let uu____3727 = (str comment)
in (FStar_Pprint.op_Hat_Hat uu____3726 uu____3727)))
in (FStar_Pprint.op_Hat_Hat doc1 uu____3725))
in (

let uu____3728 = (

let uu____3730 = (FStar_Range.end_of_range crange)
in (FStar_Range.line_of_pos uu____3730))
in (place_comments_until_pos (Prims.parse_int "1") uu____3728 pos meta_decl doc2 true init1)))));
)
end
| uu____3733 -> begin
(match ((Prims.op_Equality doc1 FStar_Pprint.empty)) with
| true -> begin
FStar_Pprint.empty
end
| uu____3742 -> begin
(

let lnum = (

let uu____3746 = (FStar_Range.line_of_pos pos)
in (uu____3746 - lbegin))
in (

let lnum1 = (min (Prims.parse_int "3") lnum)
in (

let lnum2 = (match ((meta_decl.has_qs || meta_decl.has_attrs)) with
| true -> begin
(lnum1 - (Prims.parse_int "1"))
end
| uu____3756 -> begin
lnum1
end)
in (

let lnum3 = (max k lnum2)
in (

let lnum4 = (match ((meta_decl.has_qs && meta_decl.has_attrs)) with
| true -> begin
(Prims.parse_int "2")
end
| uu____3765 -> begin
lnum3
end)
in (

let lnum5 = (match (((not (r)) && meta_decl.has_fsdoc)) with
| true -> begin
(min (Prims.parse_int "2") lnum4)
end
| uu____3772 -> begin
lnum4
end)
in (

let lnum6 = (match ((r && (meta_decl.is_fsdoc || meta_decl.has_fsdoc))) with
| true -> begin
(Prims.parse_int "1")
end
| uu____3779 -> begin
lnum5
end)
in (

let lnum7 = (match (init1) with
| true -> begin
(Prims.parse_int "2")
end
| uu____3786 -> begin
lnum6
end)
in (

let uu____3788 = (FStar_Pprint.repeat lnum7 FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat doc1 uu____3788))))))))))
end)
end)))


let separate_map_with_comments : 'Auu____3802 . FStar_Pprint.document  ->  FStar_Pprint.document  ->  ('Auu____3802  ->  FStar_Pprint.document)  ->  'Auu____3802 Prims.list  ->  ('Auu____3802  ->  decl_meta)  ->  FStar_Pprint.document = (fun prefix1 sep f xs extract_meta -> (

let fold_fun = (fun uu____3861 x -> (match (uu____3861) with
| (last_line, doc1) -> begin
(

let meta_decl = (extract_meta x)
in (

let r = meta_decl.r
in (

let doc2 = (

let uu____3880 = (FStar_Range.start_of_range r)
in (place_comments_until_pos (Prims.parse_int "1") last_line uu____3880 meta_decl doc1 false false))
in (

let uu____3884 = (

let uu____3886 = (FStar_Range.end_of_range r)
in (FStar_Range.line_of_pos uu____3886))
in (

let uu____3887 = (

let uu____3888 = (

let uu____3889 = (f x)
in (FStar_Pprint.op_Hat_Hat sep uu____3889))
in (FStar_Pprint.op_Hat_Hat doc2 uu____3888))
in ((uu____3884), (uu____3887)))))))
end))
in (

let uu____3891 = (

let uu____3898 = (FStar_List.hd xs)
in (

let uu____3899 = (FStar_List.tl xs)
in ((uu____3898), (uu____3899))))
in (match (uu____3891) with
| (x, xs1) -> begin
(

let init1 = (

let meta_decl = (extract_meta x)
in (

let uu____3917 = (

let uu____3919 = (FStar_Range.end_of_range meta_decl.r)
in (FStar_Range.line_of_pos uu____3919))
in (

let uu____3920 = (

let uu____3921 = (f x)
in (FStar_Pprint.op_Hat_Hat prefix1 uu____3921))
in ((uu____3917), (uu____3920)))))
in (

let uu____3923 = (FStar_List.fold_left fold_fun init1 xs1)
in (FStar_Pervasives_Native.snd uu____3923)))
end))))


let separate_map_with_comments_kw : 'Auu____3950 'Auu____3951 . 'Auu____3950  ->  'Auu____3950  ->  ('Auu____3950  ->  'Auu____3951  ->  FStar_Pprint.document)  ->  'Auu____3951 Prims.list  ->  ('Auu____3951  ->  decl_meta)  ->  FStar_Pprint.document = (fun prefix1 sep f xs extract_meta -> (

let fold_fun = (fun uu____4015 x -> (match (uu____4015) with
| (last_line, doc1) -> begin
(

let meta_decl = (extract_meta x)
in (

let r = meta_decl.r
in (

let doc2 = (

let uu____4034 = (FStar_Range.start_of_range r)
in (place_comments_until_pos (Prims.parse_int "1") last_line uu____4034 meta_decl doc1 false false))
in (

let uu____4038 = (

let uu____4040 = (FStar_Range.end_of_range r)
in (FStar_Range.line_of_pos uu____4040))
in (

let uu____4041 = (

let uu____4042 = (f sep x)
in (FStar_Pprint.op_Hat_Hat doc2 uu____4042))
in ((uu____4038), (uu____4041)))))))
end))
in (

let uu____4044 = (

let uu____4051 = (FStar_List.hd xs)
in (

let uu____4052 = (FStar_List.tl xs)
in ((uu____4051), (uu____4052))))
in (match (uu____4044) with
| (x, xs1) -> begin
(

let init1 = (

let meta_decl = (extract_meta x)
in (

let uu____4070 = (

let uu____4072 = (FStar_Range.end_of_range meta_decl.r)
in (FStar_Range.line_of_pos uu____4072))
in (

let uu____4073 = (f prefix1 x)
in ((uu____4070), (uu____4073)))))
in (

let uu____4075 = (FStar_List.fold_left fold_fun init1 xs1)
in (FStar_Pervasives_Native.snd uu____4075)))
end))))


let rec p_decl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (

let qualifiers = (match (((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d))) with
| ((FStar_Parser_AST.Assumption)::[], FStar_Parser_AST.Assume (id1, uu____5061)) -> begin
(

let uu____5064 = (

let uu____5066 = (FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_All.pipe_right uu____5066 FStar_Util.is_upper))
in (match (uu____5064) with
| true -> begin
(

let uu____5072 = (p_qualifier FStar_Parser_AST.Assumption)
in (FStar_Pprint.op_Hat_Hat uu____5072 FStar_Pprint.space))
end
| uu____5073 -> begin
(p_qualifiers d.FStar_Parser_AST.quals)
end))
end
| uu____5075 -> begin
(p_qualifiers d.FStar_Parser_AST.quals)
end)
in (

let uu____5082 = (FStar_Pprint.optional (fun d1 -> (p_fsdoc d1)) d.FStar_Parser_AST.doc)
in (

let uu____5085 = (

let uu____5086 = (p_attributes d.FStar_Parser_AST.attrs)
in (

let uu____5087 = (

let uu____5088 = (p_rawDecl d)
in (FStar_Pprint.op_Hat_Hat qualifiers uu____5088))
in (FStar_Pprint.op_Hat_Hat uu____5086 uu____5087)))
in (FStar_Pprint.op_Hat_Hat uu____5082 uu____5085)))))
and p_attributes : FStar_Parser_AST.attributes_  ->  FStar_Pprint.document = (fun attrs -> (match (attrs) with
| [] -> begin
FStar_Pprint.empty
end
| uu____5090 -> begin
(

let uu____5091 = (

let uu____5092 = (str "@ ")
in (

let uu____5094 = (

let uu____5095 = (

let uu____5096 = (

let uu____5097 = (

let uu____5098 = (FStar_List.map p_atomicTerm attrs)
in (FStar_Pprint.flow break1 uu____5098))
in (FStar_Pprint.op_Hat_Hat uu____5097 FStar_Pprint.rbracket))
in (FStar_Pprint.align uu____5096))
in (FStar_Pprint.op_Hat_Hat uu____5095 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat uu____5092 uu____5094)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____5091))
end))
and p_fsdoc : FStar_Parser_AST.fsdoc  ->  FStar_Pprint.document = (fun uu____5101 -> (match (uu____5101) with
| (doc1, kwd_args) -> begin
(

let kwd_args_doc = (match (kwd_args) with
| [] -> begin
FStar_Pprint.empty
end
| kwd_args1 -> begin
(

let process_kwd_arg = (fun uu____5149 -> (match (uu____5149) with
| (kwd, arg) -> begin
(

let uu____5162 = (str "@")
in (

let uu____5164 = (

let uu____5165 = (str kwd)
in (

let uu____5166 = (

let uu____5167 = (str arg)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5167))
in (FStar_Pprint.op_Hat_Hat uu____5165 uu____5166)))
in (FStar_Pprint.op_Hat_Hat uu____5162 uu____5164)))
end))
in (

let uu____5168 = (FStar_Pprint.separate_map FStar_Pprint.hardline process_kwd_arg kwd_args1)
in (FStar_Pprint.op_Hat_Hat uu____5168 FStar_Pprint.hardline)))
end)
in (

let uu____5175 = (

let uu____5176 = (

let uu____5177 = (

let uu____5178 = (str doc1)
in (

let uu____5179 = (

let uu____5180 = (

let uu____5181 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____5181))
in (FStar_Pprint.op_Hat_Hat kwd_args_doc uu____5180))
in (FStar_Pprint.op_Hat_Hat uu____5178 uu____5179)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____5177))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____5176))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5175)))
end))
and p_justSig : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (lid, t) -> begin
(

let uu____5185 = (

let uu____5186 = (str "val")
in (

let uu____5188 = (

let uu____5189 = (

let uu____5190 = (p_lident lid)
in (

let uu____5191 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat uu____5190 uu____5191)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5189))
in (FStar_Pprint.op_Hat_Hat uu____5186 uu____5188)))
in (

let uu____5192 = (p_typ false false t)
in (FStar_Pprint.op_Hat_Hat uu____5185 uu____5192)))
end
| FStar_Parser_AST.TopLevelLet (uu____5195, lbs) -> begin
(FStar_Pprint.separate_map FStar_Pprint.hardline (fun lb -> (

let uu____5220 = (

let uu____5221 = (str "let")
in (p_letlhs uu____5221 lb false))
in (FStar_Pprint.group uu____5220))) lbs)
end
| uu____5224 -> begin
FStar_Pprint.empty
end))
and p_list : (FStar_Ident.ident  ->  FStar_Pprint.document)  ->  FStar_Pprint.document  ->  FStar_Ident.ident Prims.list  ->  FStar_Pprint.document = (fun f sep l -> (

let rec p_list' = (fun uu___4_5239 -> (match (uu___4_5239) with
| [] -> begin
FStar_Pprint.empty
end
| (x)::[] -> begin
(f x)
end
| (x)::xs -> begin
(

let uu____5247 = (f x)
in (

let uu____5248 = (

let uu____5249 = (p_list' xs)
in (FStar_Pprint.op_Hat_Hat sep uu____5249))
in (FStar_Pprint.op_Hat_Hat uu____5247 uu____5248)))
end))
in (

let uu____5250 = (str "[")
in (

let uu____5252 = (

let uu____5253 = (p_list' l)
in (

let uu____5254 = (str "]")
in (FStar_Pprint.op_Hat_Hat uu____5253 uu____5254)))
in (FStar_Pprint.op_Hat_Hat uu____5250 uu____5252)))))
and p_rawDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Open (uid) -> begin
(

let uu____5258 = (

let uu____5259 = (str "open")
in (

let uu____5261 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5259 uu____5261)))
in (FStar_Pprint.group uu____5258))
end
| FStar_Parser_AST.Include (uid) -> begin
(

let uu____5263 = (

let uu____5264 = (str "include")
in (

let uu____5266 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5264 uu____5266)))
in (FStar_Pprint.group uu____5263))
end
| FStar_Parser_AST.Friend (uid) -> begin
(

let uu____5268 = (

let uu____5269 = (str "friend")
in (

let uu____5271 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5269 uu____5271)))
in (FStar_Pprint.group uu____5268))
end
| FStar_Parser_AST.ModuleAbbrev (uid1, uid2) -> begin
(

let uu____5274 = (

let uu____5275 = (str "module")
in (

let uu____5277 = (

let uu____5278 = (

let uu____5279 = (p_uident uid1)
in (

let uu____5280 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____5279 uu____5280)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5278))
in (FStar_Pprint.op_Hat_Hat uu____5275 uu____5277)))
in (

let uu____5281 = (p_quident uid2)
in (op_Hat_Slash_Plus_Hat uu____5274 uu____5281)))
end
| FStar_Parser_AST.TopLevelModule (uid) -> begin
(

let uu____5283 = (

let uu____5284 = (str "module")
in (

let uu____5286 = (

let uu____5287 = (p_quident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5287))
in (FStar_Pprint.op_Hat_Hat uu____5284 uu____5286)))
in (FStar_Pprint.group uu____5283))
end
| FStar_Parser_AST.Tycon (true, uu____5288, ((FStar_Parser_AST.TyconAbbrev (uid, tpars, FStar_Pervasives_Native.None, t), FStar_Pervasives_Native.None))::[]) -> begin
(

let effect_prefix_doc = (

let uu____5325 = (str "effect")
in (

let uu____5327 = (

let uu____5328 = (p_uident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5328))
in (FStar_Pprint.op_Hat_Hat uu____5325 uu____5327)))
in (

let uu____5329 = (

let uu____5330 = (p_typars tpars)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") effect_prefix_doc uu____5330 FStar_Pprint.equals))
in (

let uu____5333 = (p_typ false false t)
in (op_Hat_Slash_Plus_Hat uu____5329 uu____5333))))
end
| FStar_Parser_AST.Tycon (false, tc, tcdefs) -> begin
(

let s = (match (tc) with
| true -> begin
(str "class")
end
| uu____5361 -> begin
(str "type")
end)
in (

let uu____5364 = (

let uu____5365 = (FStar_List.hd tcdefs)
in (p_fsdocTypeDeclPairs s uu____5365))
in (

let uu____5378 = (

let uu____5379 = (FStar_List.tl tcdefs)
in (FStar_All.pipe_left (FStar_Pprint.concat_map (fun x -> (

let uu____5417 = (

let uu____5418 = (str "and")
in (p_fsdocTypeDeclPairs uu____5418 x))
in (FStar_Pprint.op_Hat_Hat break1 uu____5417)))) uu____5379))
in (FStar_Pprint.op_Hat_Hat uu____5364 uu____5378))))
end
| FStar_Parser_AST.TopLevelLet (q, lbs) -> begin
(

let let_doc = (

let uu____5435 = (str "let")
in (

let uu____5437 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat uu____5435 uu____5437)))
in (

let uu____5438 = (str "and")
in (separate_map_with_comments_kw let_doc uu____5438 p_letbinding lbs (fun uu____5448 -> (match (uu____5448) with
| (p, t) -> begin
(

let uu____5455 = (FStar_Range.union_ranges p.FStar_Parser_AST.prange t.FStar_Parser_AST.range)
in {r = uu____5455; has_qs = false; has_attrs = false; has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc); is_fsdoc = false})
end)))))
end
| FStar_Parser_AST.Val (lid, t) -> begin
(

let uu____5461 = (

let uu____5462 = (str "val")
in (

let uu____5464 = (

let uu____5465 = (

let uu____5466 = (p_lident lid)
in (

let uu____5467 = (sig_as_binders_if_possible t false)
in (FStar_Pprint.op_Hat_Hat uu____5466 uu____5467)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5465))
in (FStar_Pprint.op_Hat_Hat uu____5462 uu____5464)))
in (FStar_All.pipe_left FStar_Pprint.group uu____5461))
end
| FStar_Parser_AST.Assume (id1, t) -> begin
(

let decl_keyword = (

let uu____5472 = (

let uu____5474 = (FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_All.pipe_right uu____5474 FStar_Util.is_upper))
in (match (uu____5472) with
| true -> begin
FStar_Pprint.empty
end
| uu____5480 -> begin
(

let uu____5482 = (str "val")
in (FStar_Pprint.op_Hat_Hat uu____5482 FStar_Pprint.space))
end))
in (

let uu____5484 = (

let uu____5485 = (p_ident id1)
in (

let uu____5486 = (

let uu____5487 = (

let uu____5488 = (

let uu____5489 = (p_typ false false t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5489))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5488))
in (FStar_Pprint.group uu____5487))
in (FStar_Pprint.op_Hat_Hat uu____5485 uu____5486)))
in (FStar_Pprint.op_Hat_Hat decl_keyword uu____5484)))
end
| FStar_Parser_AST.Exception (uid, t_opt) -> begin
(

let uu____5498 = (str "exception")
in (

let uu____5500 = (

let uu____5501 = (

let uu____5502 = (p_uident uid)
in (

let uu____5503 = (FStar_Pprint.optional (fun t -> (

let uu____5507 = (

let uu____5508 = (str "of")
in (

let uu____5510 = (p_typ false false t)
in (op_Hat_Slash_Plus_Hat uu____5508 uu____5510)))
in (FStar_Pprint.op_Hat_Hat break1 uu____5507))) t_opt)
in (FStar_Pprint.op_Hat_Hat uu____5502 uu____5503)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5501))
in (FStar_Pprint.op_Hat_Hat uu____5498 uu____5500)))
end
| FStar_Parser_AST.NewEffect (ne) -> begin
(

let uu____5514 = (str "new_effect")
in (

let uu____5516 = (

let uu____5517 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5517))
in (FStar_Pprint.op_Hat_Hat uu____5514 uu____5516)))
end
| FStar_Parser_AST.SubEffect (se) -> begin
(

let uu____5519 = (str "sub_effect")
in (

let uu____5521 = (

let uu____5522 = (p_subEffect se)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5522))
in (FStar_Pprint.op_Hat_Hat uu____5519 uu____5521)))
end
| FStar_Parser_AST.Pragma (p) -> begin
(p_pragma p)
end
| FStar_Parser_AST.Fsdoc (doc1) -> begin
(p_fsdoc doc1)
end
| FStar_Parser_AST.Main (uu____5525) -> begin
(failwith "*Main declaration* : Is that really still in use ??")
end
| FStar_Parser_AST.Tycon (true, uu____5527, uu____5528) -> begin
(failwith "Effect abbreviation is expected to be defined by an abbreviation")
end
| FStar_Parser_AST.Splice (ids, t) -> begin
(

let uu____5556 = (str "%splice")
in (

let uu____5558 = (

let uu____5559 = (

let uu____5560 = (str ";")
in (p_list p_uident uu____5560 ids))
in (

let uu____5562 = (

let uu____5563 = (p_term false false t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5563))
in (FStar_Pprint.op_Hat_Hat uu____5559 uu____5562)))
in (FStar_Pprint.op_Hat_Hat uu____5556 uu____5558)))
end))
and p_pragma : FStar_Parser_AST.pragma  ->  FStar_Pprint.document = (fun uu___5_5566 -> (match (uu___5_5566) with
| FStar_Parser_AST.SetOptions (s) -> begin
(

let uu____5569 = (str "#set-options")
in (

let uu____5571 = (

let uu____5572 = (

let uu____5573 = (str s)
in (FStar_Pprint.dquotes uu____5573))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5572))
in (FStar_Pprint.op_Hat_Hat uu____5569 uu____5571)))
end
| FStar_Parser_AST.ResetOptions (s_opt) -> begin
(

let uu____5578 = (str "#reset-options")
in (

let uu____5580 = (FStar_Pprint.optional (fun s -> (

let uu____5586 = (

let uu____5587 = (str s)
in (FStar_Pprint.dquotes uu____5587))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5586))) s_opt)
in (FStar_Pprint.op_Hat_Hat uu____5578 uu____5580)))
end
| FStar_Parser_AST.PushOptions (s_opt) -> begin
(

let uu____5592 = (str "#push-options")
in (

let uu____5594 = (FStar_Pprint.optional (fun s -> (

let uu____5600 = (

let uu____5601 = (str s)
in (FStar_Pprint.dquotes uu____5601))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5600))) s_opt)
in (FStar_Pprint.op_Hat_Hat uu____5592 uu____5594)))
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
and p_fsdocTypeDeclPairs : FStar_Pprint.document  ->  (FStar_Parser_AST.tycon * FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option)  ->  FStar_Pprint.document = (fun kw uu____5632 -> (match (uu____5632) with
| (typedecl, fsdoc_opt) -> begin
(

let uu____5645 = (p_typeDecl ((kw), (fsdoc_opt)) typedecl)
in (match (uu____5645) with
| (comm, decl, body, pre) -> begin
(match ((Prims.op_Equality comm FStar_Pprint.empty)) with
| true -> begin
(

let uu____5670 = (pre body)
in (FStar_Pprint.op_Hat_Hat decl uu____5670))
end
| uu____5671 -> begin
(

let uu____5673 = (

let uu____5674 = (

let uu____5675 = (

let uu____5676 = (pre body)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5676 comm))
in (FStar_Pprint.op_Hat_Hat decl uu____5675))
in (

let uu____5677 = (

let uu____5678 = (

let uu____5679 = (

let uu____5680 = (

let uu____5681 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline body)
in (FStar_Pprint.op_Hat_Hat comm uu____5681))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5680))
in (FStar_Pprint.nest (Prims.parse_int "2") uu____5679))
in (FStar_Pprint.op_Hat_Hat decl uu____5678))
in (FStar_Pprint.ifflat uu____5674 uu____5677)))
in (FStar_All.pipe_left FStar_Pprint.group uu____5673))
end)
end))
end))
and p_typeDecl : (FStar_Pprint.document * FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option)  ->  FStar_Parser_AST.tycon  ->  (FStar_Pprint.document * FStar_Pprint.document * FStar_Pprint.document * (FStar_Pprint.document  ->  FStar_Pprint.document)) = (fun pre uu___6_5684 -> (match (uu___6_5684) with
| FStar_Parser_AST.TyconAbstract (lid, bs, typ_opt) -> begin
(

let uu____5713 = (p_typeDeclPrefix pre false lid bs typ_opt)
in ((FStar_Pprint.empty), (uu____5713), (FStar_Pprint.empty), (FStar_Pervasives.id)))
end
| FStar_Parser_AST.TyconAbbrev (lid, bs, typ_opt, t) -> begin
(

let uu____5730 = (p_typ_sep false false t)
in (match (uu____5730) with
| (comm, doc1) -> begin
(

let uu____5750 = (p_typeDeclPrefix pre true lid bs typ_opt)
in ((comm), (uu____5750), (doc1), (jump2)))
end))
end
| FStar_Parser_AST.TyconRecord (lid, bs, typ_opt, record_field_decls) -> begin
(

let p_recordFieldAndComments = (fun ps uu____5806 -> (match (uu____5806) with
| (lid1, t, doc_opt) -> begin
(

let uu____5823 = (

let uu____5828 = (FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range)
in (with_comment_sep (p_recordFieldDecl ps) ((lid1), (t), (doc_opt)) uu____5828))
in (match (uu____5823) with
| (comm, field) -> begin
(

let sep = (match (ps) with
| true -> begin
FStar_Pprint.semi
end
| uu____5843 -> begin
FStar_Pprint.empty
end)
in (inline_comment_or_above comm field sep))
end))
end))
in (

let p_fields = (

let uu____5846 = (separate_map_last FStar_Pprint.hardline p_recordFieldAndComments record_field_decls)
in (braces_with_nesting uu____5846))
in (

let uu____5855 = (p_typeDeclPrefix pre true lid bs typ_opt)
in ((FStar_Pprint.empty), (uu____5855), (p_fields), ((fun d -> (FStar_Pprint.op_Hat_Hat FStar_Pprint.space d)))))))
end
| FStar_Parser_AST.TyconVariant (lid, bs, typ_opt, ct_decls) -> begin
(

let p_constructorBranchAndComments = (fun uu____5922 -> (match (uu____5922) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let range = (

let uu____5951 = (

let uu____5952 = (FStar_Util.map_opt t_opt (fun t -> t.FStar_Parser_AST.range))
in (FStar_Util.dflt uid.FStar_Ident.idRange uu____5952))
in (FStar_Range.extend_to_end_of_line uu____5951))
in (

let uu____5957 = (with_comment_sep p_constructorBranch ((uid), (t_opt), (doc_opt), (use_of)) range)
in (match (uu____5957) with
| (comm, ctor) -> begin
(inline_comment_or_above comm ctor FStar_Pprint.empty)
end)))
end))
in (

let datacon_doc = (FStar_Pprint.separate_map FStar_Pprint.hardline p_constructorBranchAndComments ct_decls)
in (

let uu____5996 = (p_typeDeclPrefix pre true lid bs typ_opt)
in ((FStar_Pprint.empty), (uu____5996), (datacon_doc), (jump2)))))
end))
and p_typeDeclPrefix : (FStar_Pprint.document * FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option)  ->  Prims.bool  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.knd FStar_Pervasives_Native.option  ->  FStar_Pprint.document = (fun uu____6001 eq1 lid bs typ_opt -> (match (uu____6001) with
| (kw, fsdoc_opt) -> begin
(

let maybe_with_fsdoc = (fun cont -> (

let lid_doc = (p_ident lid)
in (

let kw_lid = (

let uu____6036 = (FStar_Pprint.op_Hat_Slash_Hat kw lid_doc)
in (FStar_Pprint.group uu____6036))
in (match (fsdoc_opt) with
| FStar_Pervasives_Native.None -> begin
(cont kw_lid)
end
| FStar_Pervasives_Native.Some (fsdoc) -> begin
(

let uu____6038 = (

let uu____6041 = (

let uu____6044 = (p_fsdoc fsdoc)
in (

let uu____6045 = (

let uu____6048 = (cont lid_doc)
in (uu____6048)::[])
in (uu____6044)::uu____6045))
in (kw)::uu____6041)
in (FStar_Pprint.separate FStar_Pprint.hardline uu____6038))
end))))
in (

let typ = (

let maybe_eq = (match (eq1) with
| true -> begin
FStar_Pprint.equals
end
| uu____6052 -> begin
FStar_Pprint.empty
end)
in (match (typ_opt) with
| FStar_Pervasives_Native.None -> begin
maybe_eq
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____6055 = (

let uu____6056 = (

let uu____6057 = (p_typ false false t)
in (FStar_Pprint.op_Hat_Slash_Hat uu____6057 maybe_eq))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6056))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6055))
end))
in (match ((Prims.op_Equality bs [])) with
| true -> begin
(maybe_with_fsdoc (fun n1 -> (prefix2 n1 typ)))
end
| uu____6066 -> begin
(

let binders = (p_binders_list true bs)
in (maybe_with_fsdoc (fun n1 -> (

let uu____6077 = (

let uu____6078 = (FStar_Pprint.flow break1 binders)
in (prefix2 n1 uu____6078))
in (prefix2 uu____6077 typ)))))
end)))
end))
and p_recordFieldDecl : Prims.bool  ->  (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option)  ->  FStar_Pprint.document = (fun ps uu____6080 -> (match (uu____6080) with
| (lid, t, doc_opt) -> begin
(

let uu____6097 = (

let uu____6098 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (

let uu____6099 = (

let uu____6100 = (p_lident lid)
in (

let uu____6101 = (

let uu____6102 = (p_typ ps false t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6102))
in (FStar_Pprint.op_Hat_Hat uu____6100 uu____6101)))
in (FStar_Pprint.op_Hat_Hat uu____6098 uu____6099)))
in (FStar_Pprint.group uu____6097))
end))
and p_constructorBranch : (FStar_Ident.ident * FStar_Parser_AST.term FStar_Pervasives_Native.option * FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option * Prims.bool)  ->  FStar_Pprint.document = (fun uu____6104 -> (match (uu____6104) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let sep = (match (use_of) with
| true -> begin
(str "of")
end
| uu____6135 -> begin
FStar_Pprint.colon
end)
in (

let uid_doc = (

let uu____6138 = (

let uu____6139 = (

let uu____6140 = (p_uident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6140))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____6139))
in (FStar_Pprint.group uu____6138))
in (

let uu____6141 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (

let uu____6142 = (default_or_map uid_doc (fun t -> (

let uu____6146 = (

let uu____6147 = (

let uu____6148 = (

let uu____6149 = (

let uu____6150 = (p_typ false false t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6150))
in (FStar_Pprint.op_Hat_Hat sep uu____6149))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6148))
in (FStar_Pprint.op_Hat_Hat uid_doc uu____6147))
in (FStar_Pprint.group uu____6146))) t_opt)
in (FStar_Pprint.op_Hat_Hat uu____6141 uu____6142)))))
end))
and p_letlhs : FStar_Pprint.document  ->  (FStar_Parser_AST.pattern * FStar_Parser_AST.term)  ->  Prims.bool  ->  FStar_Pprint.document = (fun kw uu____6154 inner_let -> (match (uu____6154) with
| (pat, uu____6162) -> begin
(

let uu____6163 = (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat1, (t, FStar_Pervasives_Native.None)) -> begin
((pat1), (FStar_Pervasives_Native.Some (((t), (FStar_Pprint.empty)))))
end
| FStar_Parser_AST.PatAscribed (pat1, (t, FStar_Pervasives_Native.Some (tac))) -> begin
(

let uu____6215 = (

let uu____6222 = (

let uu____6227 = (

let uu____6228 = (

let uu____6229 = (

let uu____6230 = (str "by")
in (

let uu____6232 = (

let uu____6233 = (p_atomicTerm tac)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6233))
in (FStar_Pprint.op_Hat_Hat uu____6230 uu____6232)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6229))
in (FStar_Pprint.group uu____6228))
in ((t), (uu____6227)))
in FStar_Pervasives_Native.Some (uu____6222))
in ((pat1), (uu____6215)))
end
| uu____6244 -> begin
((pat), (FStar_Pervasives_Native.None))
end)
in (match (uu____6163) with
| (pat1, ascr) -> begin
(match (pat1.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (lid, uu____6270); FStar_Parser_AST.prange = uu____6271}, pats) -> begin
(

let ascr_doc = (match (ascr) with
| FStar_Pervasives_Native.Some (t, tac) -> begin
(

let uu____6288 = (sig_as_binders_if_possible t true)
in (FStar_Pprint.op_Hat_Hat uu____6288 tac))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pprint.empty
end)
in (

let uu____6294 = (match (inner_let) with
| true -> begin
(

let uu____6308 = (pats_as_binders_if_possible pats)
in (match (uu____6308) with
| (bs, style) -> begin
(((FStar_List.append bs ((ascr_doc)::[]))), (style))
end))
end
| uu____6329 -> begin
(

let uu____6331 = (pats_as_binders_if_possible pats)
in (match (uu____6331) with
| (bs, style) -> begin
(((FStar_List.append bs ((ascr_doc)::[]))), (style))
end))
end)
in (match (uu____6294) with
| (terms, style) -> begin
(

let uu____6358 = (

let uu____6359 = (

let uu____6360 = (

let uu____6361 = (p_lident lid)
in (

let uu____6362 = (format_sig style terms true true)
in (FStar_Pprint.op_Hat_Hat uu____6361 uu____6362)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6360))
in (FStar_Pprint.op_Hat_Hat kw uu____6359))
in (FStar_All.pipe_left FStar_Pprint.group uu____6358))
end)))
end
| uu____6365 -> begin
(

let ascr_doc = (match (ascr) with
| FStar_Pervasives_Native.Some (t, tac) -> begin
(

let uu____6373 = (

let uu____6374 = (

let uu____6375 = (p_typ_top (Arrows ((((Prims.parse_int "2")), ((Prims.parse_int "2"))))) false false t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6375))
in (FStar_Pprint.group uu____6374))
in (FStar_Pprint.op_Hat_Hat uu____6373 tac))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pprint.empty
end)
in (

let uu____6386 = (

let uu____6387 = (

let uu____6388 = (

let uu____6389 = (p_tuplePattern pat1)
in (FStar_Pprint.op_Hat_Slash_Hat kw uu____6389))
in (FStar_Pprint.group uu____6388))
in (FStar_Pprint.op_Hat_Hat uu____6387 ascr_doc))
in (FStar_Pprint.group uu____6386)))
end)
end))
end))
and p_letbinding : FStar_Pprint.document  ->  (FStar_Parser_AST.pattern * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun kw uu____6391 -> (match (uu____6391) with
| (pat, e) -> begin
(

let doc_pat = (p_letlhs kw ((pat), (e)) false)
in (

let uu____6400 = (p_term_sep false false e)
in (match (uu____6400) with
| (comm, doc_expr) -> begin
(

let doc_expr1 = (inline_comment_or_above comm doc_expr FStar_Pprint.empty)
in (

let uu____6410 = (

let uu____6411 = (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals doc_expr1)
in (FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____6411))
in (

let uu____6412 = (

let uu____6413 = (

let uu____6414 = (

let uu____6415 = (

let uu____6416 = (jump2 doc_expr1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____6416))
in (FStar_Pprint.group uu____6415))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6414))
in (FStar_Pprint.op_Hat_Hat doc_pat uu____6413))
in (FStar_Pprint.ifflat uu____6410 uu____6412))))
end)))
end))
and p_newEffect : FStar_Parser_AST.effect_decl  ->  FStar_Pprint.document = (fun uu___7_6417 -> (match (uu___7_6417) with
| FStar_Parser_AST.RedefineEffect (lid, bs, t) -> begin
(p_effectRedefinition lid bs t)
end
| FStar_Parser_AST.DefineEffect (lid, bs, t, eff_decls) -> begin
(p_effectDefinition lid bs t eff_decls)
end))
and p_effectRedefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun uid bs t -> (

let uu____6442 = (p_uident uid)
in (

let uu____6443 = (p_binders true bs)
in (

let uu____6445 = (

let uu____6446 = (p_simpleTerm false false t)
in (prefix2 FStar_Pprint.equals uu____6446))
in (surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1") uu____6442 uu____6443 uu____6445)))))
and p_effectDefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun uid bs t eff_decls -> (

let binders = (p_binders true bs)
in (

let uu____6461 = (

let uu____6462 = (

let uu____6463 = (

let uu____6464 = (p_uident uid)
in (

let uu____6465 = (p_binders true bs)
in (

let uu____6467 = (

let uu____6468 = (p_typ false false t)
in (prefix2 FStar_Pprint.colon uu____6468))
in (surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1") uu____6464 uu____6465 uu____6467))))
in (FStar_Pprint.group uu____6463))
in (

let uu____6473 = (

let uu____6474 = (str "with")
in (

let uu____6476 = (

let uu____6477 = (

let uu____6478 = (

let uu____6479 = (

let uu____6480 = (

let uu____6481 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi FStar_Pprint.space)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6481))
in (separate_map_last uu____6480 p_effectDecl eff_decls))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6479))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6478))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6477))
in (FStar_Pprint.op_Hat_Hat uu____6474 uu____6476)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____6462 uu____6473)))
in (braces_with_nesting uu____6461))))
and p_effectDecl : Prims.bool  ->  FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun ps d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (false, uu____6485, ((FStar_Parser_AST.TyconAbbrev (lid, [], FStar_Pervasives_Native.None, e), FStar_Pervasives_Native.None))::[]) -> begin
(

let uu____6518 = (

let uu____6519 = (p_lident lid)
in (

let uu____6520 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____6519 uu____6520)))
in (

let uu____6521 = (p_simpleTerm ps false e)
in (prefix2 uu____6518 uu____6521)))
end
| uu____6523 -> begin
(

let uu____6524 = (

let uu____6526 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "Not a declaration of an effect member... or at least I hope so : %s" uu____6526))
in (failwith uu____6524))
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

let p_lift = (fun ps uu____6609 -> (match (uu____6609) with
| (kwd, t) -> begin
(

let uu____6620 = (

let uu____6621 = (str kwd)
in (

let uu____6622 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____6621 uu____6622)))
in (

let uu____6623 = (p_simpleTerm ps false t)
in (prefix2 uu____6620 uu____6623)))
end))
in (separate_break_map_last FStar_Pprint.semi p_lift lifts)))
in (

let uu____6630 = (

let uu____6631 = (

let uu____6632 = (p_quident lift.FStar_Parser_AST.msource)
in (

let uu____6633 = (

let uu____6634 = (str "~>")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6634))
in (FStar_Pprint.op_Hat_Hat uu____6632 uu____6633)))
in (

let uu____6636 = (p_quident lift.FStar_Parser_AST.mdest)
in (prefix2 uu____6631 uu____6636)))
in (

let uu____6637 = (

let uu____6638 = (braces_with_nesting lift_op_doc)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6638))
in (FStar_Pprint.op_Hat_Hat uu____6630 uu____6637)))))
and p_qualifier : FStar_Parser_AST.qualifier  ->  FStar_Pprint.document = (fun uu___8_6639 -> (match (uu___8_6639) with
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
| (q)::[] -> begin
(

let uu____6659 = (p_qualifier q)
in (FStar_Pprint.op_Hat_Hat uu____6659 FStar_Pprint.hardline))
end
| uu____6660 -> begin
(

let uu____6661 = (

let uu____6662 = (FStar_List.map p_qualifier qs)
in (FStar_Pprint.flow break1 uu____6662))
in (FStar_Pprint.op_Hat_Hat uu____6661 FStar_Pprint.hardline))
end))
and p_letqualifier : FStar_Parser_AST.let_qualifier  ->  FStar_Pprint.document = (fun uu___9_6665 -> (match (uu___9_6665) with
| FStar_Parser_AST.Rec -> begin
(

let uu____6666 = (str "rec")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6666))
end
| FStar_Parser_AST.NoLetQualifier -> begin
FStar_Pprint.empty
end))
and p_aqual : FStar_Parser_AST.arg_qualifier  ->  FStar_Pprint.document = (fun uu___10_6668 -> (match (uu___10_6668) with
| FStar_Parser_AST.Implicit -> begin
(str "#")
end
| FStar_Parser_AST.Equality -> begin
(str "$")
end
| FStar_Parser_AST.Meta (t) -> begin
(

let t1 = (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Abs (uu____6673, e) -> begin
e
end
| uu____6679 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((t), ((FStar_Parser_AST.unit_const t.FStar_Parser_AST.range)), (FStar_Parser_AST.Nothing)))) t.FStar_Parser_AST.range FStar_Parser_AST.Expr)
end)
in (

let uu____6680 = (str "#[")
in (

let uu____6682 = (

let uu____6683 = (p_term false false t1)
in (

let uu____6686 = (

let uu____6687 = (str "]")
in (FStar_Pprint.op_Hat_Hat uu____6687 break1))
in (FStar_Pprint.op_Hat_Hat uu____6683 uu____6686)))
in (FStar_Pprint.op_Hat_Hat uu____6680 uu____6682))))
end))
and p_disjunctivePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr (pats) -> begin
(

let uu____6693 = (

let uu____6694 = (

let uu____6695 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space)
in (FStar_Pprint.op_Hat_Hat break1 uu____6695))
in (FStar_Pprint.separate_map uu____6694 p_tuplePattern pats))
in (FStar_Pprint.group uu____6693))
end
| uu____6696 -> begin
(p_tuplePattern p)
end))
and p_tuplePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTuple (pats, false) -> begin
(

let uu____6705 = (

let uu____6706 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map uu____6706 p_constructorPattern pats))
in (FStar_Pprint.group uu____6705))
end
| uu____6707 -> begin
(p_constructorPattern p)
end))
and p_constructorPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (maybe_cons_lid); FStar_Parser_AST.prange = uu____6710}, (hd1)::(tl1)::[]) when (FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid) -> begin
(

let uu____6715 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon)
in (

let uu____6716 = (p_constructorPattern hd1)
in (

let uu____6717 = (p_constructorPattern tl1)
in (infix0 uu____6715 uu____6716 uu____6717))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (uid); FStar_Parser_AST.prange = uu____6719}, pats) -> begin
(

let uu____6725 = (p_quident uid)
in (

let uu____6726 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (prefix2 uu____6725 uu____6726)))
end
| uu____6727 -> begin
(p_atomicPattern p)
end))
and p_atomicPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, (t, FStar_Pervasives_Native.None)) -> begin
(match (((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm))) with
| (FStar_Parser_AST.PatVar (lid, aqual), FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t1); FStar_Parser_AST.brange = uu____6743; FStar_Parser_AST.blevel = uu____6744; FStar_Parser_AST.aqual = uu____6745}, phi)) when (Prims.op_Equality lid.FStar_Ident.idText lid'.FStar_Ident.idText) -> begin
(

let uu____6754 = (

let uu____6755 = (p_ident lid)
in (p_refinement aqual uu____6755 t1 phi))
in (soft_parens_with_nesting uu____6754))
end
| (FStar_Parser_AST.PatWild (aqual), FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t1); FStar_Parser_AST.brange = uu____6758; FStar_Parser_AST.blevel = uu____6759; FStar_Parser_AST.aqual = uu____6760}, phi)) -> begin
(

let uu____6766 = (p_refinement aqual FStar_Pprint.underscore t1 phi)
in (soft_parens_with_nesting uu____6766))
end
| uu____6767 -> begin
(

let uu____6772 = (

let uu____6773 = (p_tuplePattern pat)
in (

let uu____6774 = (

let uu____6775 = (p_tmEqNoRefinement t)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6775))
in (FStar_Pprint.op_Hat_Hat uu____6773 uu____6774)))
in (soft_parens_with_nesting uu____6772))
end)
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let uu____6779 = (separate_break_map FStar_Pprint.semi p_tuplePattern pats)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket uu____6779 FStar_Pprint.rbracket))
end
| FStar_Parser_AST.PatRecord (pats) -> begin
(

let p_recordFieldPat = (fun uu____6798 -> (match (uu____6798) with
| (lid, pat) -> begin
(

let uu____6805 = (p_qlident lid)
in (

let uu____6806 = (p_tuplePattern pat)
in (infix2 FStar_Pprint.equals uu____6805 uu____6806)))
end))
in (

let uu____6807 = (separate_break_map FStar_Pprint.semi p_recordFieldPat pats)
in (soft_braces_with_nesting uu____6807)))
end
| FStar_Parser_AST.PatTuple (pats, true) -> begin
(

let uu____6819 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (

let uu____6820 = (separate_break_map FStar_Pprint.comma p_constructorPattern pats)
in (

let uu____6821 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____6819 uu____6820 uu____6821))))
end
| FStar_Parser_AST.PatTvar (tv, arg_qualifier_opt) -> begin
(p_tvar tv)
end
| FStar_Parser_AST.PatOp (op) -> begin
(

let uu____6832 = (

let uu____6833 = (

let uu____6834 = (

let uu____6835 = (FStar_Ident.text_of_id op)
in (str uu____6835))
in (

let uu____6837 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat uu____6834 uu____6837)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6833))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6832))
end
| FStar_Parser_AST.PatWild (aqual) -> begin
(

let uu____6841 = (FStar_Pprint.optional p_aqual aqual)
in (FStar_Pprint.op_Hat_Hat uu____6841 FStar_Pprint.underscore))
end
| FStar_Parser_AST.PatConst (c) -> begin
(p_constant c)
end
| FStar_Parser_AST.PatVar (lid, aqual) -> begin
(

let uu____6849 = (FStar_Pprint.optional p_aqual aqual)
in (

let uu____6850 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat uu____6849 uu____6850)))
end
| FStar_Parser_AST.PatName (uid) -> begin
(p_quident uid)
end
| FStar_Parser_AST.PatOr (uu____6852) -> begin
(failwith "Inner or pattern !")
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (uu____6856); FStar_Parser_AST.prange = uu____6857}, uu____6858) -> begin
(

let uu____6863 = (p_tuplePattern p)
in (soft_parens_with_nesting uu____6863))
end
| FStar_Parser_AST.PatTuple (uu____6864, false) -> begin
(

let uu____6871 = (p_tuplePattern p)
in (soft_parens_with_nesting uu____6871))
end
| uu____6872 -> begin
(

let uu____6873 = (

let uu____6875 = (FStar_Parser_AST.pat_to_string p)
in (FStar_Util.format1 "Invalid pattern %s" uu____6875))
in (failwith uu____6873))
end))
and is_typ_tuple : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____6880}, uu____6881) -> begin
true
end
| uu____6888 -> begin
false
end))
and is_meta_qualifier : FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option  ->  Prims.bool = (fun aq -> (match (aq) with
| FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta (uu____6894)) -> begin
true
end
| uu____6896 -> begin
false
end))
and p_binder : Prims.bool  ->  FStar_Parser_AST.binder  ->  FStar_Pprint.document = (fun is_atomic b -> (

let uu____6903 = (p_binder' is_atomic b)
in (match (uu____6903) with
| (b', t', catf) -> begin
(match (t') with
| FStar_Pervasives_Native.Some (typ) -> begin
(catf b' typ)
end
| FStar_Pervasives_Native.None -> begin
b'
end)
end)))
and p_binder' : Prims.bool  ->  FStar_Parser_AST.binder  ->  (FStar_Pprint.document * FStar_Pprint.document FStar_Pervasives_Native.option * catf) = (fun is_atomic b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (lid) -> begin
(

let uu____6940 = (

let uu____6941 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (

let uu____6942 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat uu____6941 uu____6942)))
in ((uu____6940), (FStar_Pervasives_Native.None), (cat_with_colon)))
end
| FStar_Parser_AST.TVariable (lid) -> begin
(

let uu____6948 = (p_lident lid)
in ((uu____6948), (FStar_Pervasives_Native.None), (cat_with_colon)))
end
| FStar_Parser_AST.Annotated (lid, t) -> begin
(

let uu____6955 = (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t1); FStar_Parser_AST.brange = uu____6966; FStar_Parser_AST.blevel = uu____6967; FStar_Parser_AST.aqual = uu____6968}, phi) when (Prims.op_Equality lid.FStar_Ident.idText lid'.FStar_Ident.idText) -> begin
(

let uu____6973 = (p_lident lid)
in (p_refinement' b.FStar_Parser_AST.aqual uu____6973 t1 phi))
end
| uu____6974 -> begin
(

let t' = (

let uu____6976 = (is_typ_tuple t)
in (match (uu____6976) with
| true -> begin
(

let uu____6979 = (p_tmFormula t)
in (soft_parens_with_nesting uu____6979))
end
| uu____6980 -> begin
(p_tmFormula t)
end))
in (

let uu____6982 = (

let uu____6983 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (

let uu____6984 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat uu____6983 uu____6984)))
in ((uu____6982), (t'))))
end)
in (match (uu____6955) with
| (b', t') -> begin
(

let catf = (

let uu____7002 = (is_atomic || (is_meta_qualifier b.FStar_Parser_AST.aqual))
in (match (uu____7002) with
| true -> begin
(fun x y -> (

let uu____7009 = (

let uu____7010 = (

let uu____7011 = (cat_with_colon x y)
in (FStar_Pprint.op_Hat_Hat uu____7011 FStar_Pprint.rparen))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____7010))
in (FStar_Pprint.group uu____7009)))
end
| uu____7012 -> begin
(fun x y -> (

let uu____7016 = (cat_with_colon x y)
in (FStar_Pprint.group uu____7016)))
end))
in ((b'), (FStar_Pervasives_Native.Some (t')), (catf)))
end))
end
| FStar_Parser_AST.TAnnotated (uu____7021) -> begin
(failwith "Is this still used ?")
end
| FStar_Parser_AST.NoName (t) -> begin
(match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t1); FStar_Parser_AST.brange = uu____7049; FStar_Parser_AST.blevel = uu____7050; FStar_Parser_AST.aqual = uu____7051}, phi) -> begin
(

let uu____7055 = (p_refinement' b.FStar_Parser_AST.aqual FStar_Pprint.underscore t1 phi)
in (match (uu____7055) with
| (b', t') -> begin
((b'), (FStar_Pervasives_Native.Some (t')), (cat_with_colon))
end))
end
| uu____7076 -> begin
(match (is_atomic) with
| true -> begin
(

let uu____7088 = (p_atomicTerm t)
in ((uu____7088), (FStar_Pervasives_Native.None), (cat_with_colon)))
end
| uu____7093 -> begin
(

let uu____7095 = (p_appTerm t)
in ((uu____7095), (FStar_Pervasives_Native.None), (cat_with_colon)))
end)
end)
end))
and p_refinement : FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Pprint.document  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun aqual_opt binder t phi -> (

let uu____7106 = (p_refinement' aqual_opt binder t phi)
in (match (uu____7106) with
| (b, typ) -> begin
(cat_with_colon b typ)
end)))
and p_refinement' : FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Pprint.document  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term  ->  (FStar_Pprint.document * FStar_Pprint.document) = (fun aqual_opt binder t phi -> (

let is_t_atomic = (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (uu____7122) -> begin
false
end
| FStar_Parser_AST.App (uu____7134) -> begin
false
end
| FStar_Parser_AST.Op (uu____7142) -> begin
false
end
| uu____7150 -> begin
true
end)
in (

let uu____7152 = (p_noSeqTerm false false phi)
in (match (uu____7152) with
| (comm, phi1) -> begin
(

let phi2 = (match ((Prims.op_Equality comm FStar_Pprint.empty)) with
| true -> begin
phi1
end
| uu____7167 -> begin
(

let uu____7169 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline phi1)
in (FStar_Pprint.op_Hat_Hat comm uu____7169))
end)
in (

let jump_break = (match (is_t_atomic) with
| true -> begin
(Prims.parse_int "0")
end
| uu____7175 -> begin
(Prims.parse_int "1")
end)
in (

let uu____7178 = (

let uu____7179 = (FStar_Pprint.optional p_aqual aqual_opt)
in (FStar_Pprint.op_Hat_Hat uu____7179 binder))
in (

let uu____7180 = (

let uu____7181 = (p_appTerm t)
in (

let uu____7182 = (

let uu____7183 = (

let uu____7184 = (

let uu____7185 = (soft_braces_with_nesting_tight phi2)
in (

let uu____7186 = (soft_braces_with_nesting phi2)
in (FStar_Pprint.ifflat uu____7185 uu____7186)))
in (FStar_Pprint.group uu____7184))
in (FStar_Pprint.jump (Prims.parse_int "2") jump_break uu____7183))
in (FStar_Pprint.op_Hat_Hat uu____7181 uu____7182)))
in ((uu____7178), (uu____7180))))))
end))))
and p_binders_list : Prims.bool  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Pprint.document Prims.list = (fun is_atomic bs -> (FStar_List.map (p_binder is_atomic) bs))
and p_binders : Prims.bool  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Pprint.document = (fun is_atomic bs -> (

let uu____7200 = (p_binders_list is_atomic bs)
in (separate_or_flow break1 uu____7200)))
and text_of_id_or_underscore : FStar_Ident.ident  ->  FStar_Pprint.document = (fun lid -> (

let uu____7204 = ((FStar_Util.starts_with lid.FStar_Ident.idText FStar_Ident.reserved_prefix) && (

let uu____7207 = (FStar_Options.print_real_names ())
in (not (uu____7207))))
in (match (uu____7204) with
| true -> begin
FStar_Pprint.underscore
end
| uu____7210 -> begin
(

let uu____7212 = (FStar_Ident.text_of_id lid)
in (str uu____7212))
end)))
and text_of_lid_or_underscore : FStar_Ident.lident  ->  FStar_Pprint.document = (fun lid -> (

let uu____7215 = ((FStar_Util.starts_with lid.FStar_Ident.ident.FStar_Ident.idText FStar_Ident.reserved_prefix) && (

let uu____7218 = (FStar_Options.print_real_names ())
in (not (uu____7218))))
in (match (uu____7215) with
| true -> begin
FStar_Pprint.underscore
end
| uu____7221 -> begin
(

let uu____7223 = (FStar_Ident.text_of_lid lid)
in (str uu____7223))
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
| uu____7237 -> begin
(fun x -> x)
end))
and inline_comment_or_above : FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun comm doc1 sep -> (match ((Prims.op_Equality comm FStar_Pprint.empty)) with
| true -> begin
(

let uu____7244 = (FStar_Pprint.op_Hat_Hat doc1 sep)
in (FStar_Pprint.group uu____7244))
end
| uu____7245 -> begin
(

let uu____7247 = (

let uu____7248 = (

let uu____7249 = (

let uu____7250 = (

let uu____7251 = (FStar_Pprint.op_Hat_Hat break1 comm)
in (FStar_Pprint.op_Hat_Hat sep uu____7251))
in (FStar_Pprint.op_Hat_Hat doc1 uu____7250))
in (FStar_Pprint.group uu____7249))
in (

let uu____7252 = (

let uu____7253 = (

let uu____7254 = (FStar_Pprint.op_Hat_Hat doc1 sep)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7254))
in (FStar_Pprint.op_Hat_Hat comm uu____7253))
in (FStar_Pprint.ifflat uu____7248 uu____7252)))
in (FStar_All.pipe_left FStar_Pprint.group uu____7247))
end))
and p_term : Prims.bool  ->  Prims.bool  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun ps pb e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Seq (e1, e2) -> begin
(

let uu____7262 = (p_noSeqTerm true false e1)
in (match (uu____7262) with
| (comm, t1) -> begin
(

let uu____7271 = (inline_comment_or_above comm t1 FStar_Pprint.semi)
in (

let uu____7272 = (

let uu____7273 = (p_term ps pb e2)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7273))
in (FStar_Pprint.op_Hat_Hat uu____7271 uu____7272)))
end))
end
| FStar_Parser_AST.Bind (x, e1, e2) -> begin
(

let uu____7277 = (

let uu____7278 = (

let uu____7279 = (

let uu____7280 = (p_lident x)
in (

let uu____7281 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.long_left_arrow)
in (FStar_Pprint.op_Hat_Hat uu____7280 uu____7281)))
in (

let uu____7282 = (

let uu____7283 = (p_noSeqTermAndComment true false e1)
in (

let uu____7286 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.semi)
in (FStar_Pprint.op_Hat_Hat uu____7283 uu____7286)))
in (op_Hat_Slash_Plus_Hat uu____7279 uu____7282)))
in (FStar_Pprint.group uu____7278))
in (

let uu____7287 = (p_term ps pb e2)
in (FStar_Pprint.op_Hat_Slash_Hat uu____7277 uu____7287)))
end
| uu____7288 -> begin
(

let uu____7289 = (p_noSeqTermAndComment ps pb e)
in (FStar_Pprint.group uu____7289))
end))
and p_term_sep : Prims.bool  ->  Prims.bool  ->  FStar_Parser_AST.term  ->  (FStar_Pprint.document * FStar_Pprint.document) = (fun ps pb e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Seq (e1, e2) -> begin
(

let uu____7301 = (p_noSeqTerm true false e1)
in (match (uu____7301) with
| (comm, t1) -> begin
(

let uu____7314 = (

let uu____7315 = (

let uu____7316 = (FStar_Pprint.op_Hat_Hat t1 FStar_Pprint.semi)
in (FStar_Pprint.group uu____7316))
in (

let uu____7317 = (

let uu____7318 = (p_term ps pb e2)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7318))
in (FStar_Pprint.op_Hat_Hat uu____7315 uu____7317)))
in ((comm), (uu____7314)))
end))
end
| FStar_Parser_AST.Bind (x, e1, e2) -> begin
(

let uu____7322 = (

let uu____7323 = (

let uu____7324 = (

let uu____7325 = (

let uu____7326 = (p_lident x)
in (

let uu____7327 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.long_left_arrow)
in (FStar_Pprint.op_Hat_Hat uu____7326 uu____7327)))
in (

let uu____7328 = (

let uu____7329 = (p_noSeqTermAndComment true false e1)
in (

let uu____7332 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.semi)
in (FStar_Pprint.op_Hat_Hat uu____7329 uu____7332)))
in (op_Hat_Slash_Plus_Hat uu____7325 uu____7328)))
in (FStar_Pprint.group uu____7324))
in (

let uu____7333 = (p_term ps pb e2)
in (FStar_Pprint.op_Hat_Slash_Hat uu____7323 uu____7333)))
in ((FStar_Pprint.empty), (uu____7322)))
end
| uu____7334 -> begin
(p_noSeqTerm ps pb e)
end))
and p_noSeqTerm : Prims.bool  ->  Prims.bool  ->  FStar_Parser_AST.term  ->  (FStar_Pprint.document * FStar_Pprint.document) = (fun ps pb e -> (with_comment_sep (p_noSeqTerm' ps pb) e e.FStar_Parser_AST.range))
and p_noSeqTermAndComment : Prims.bool  ->  Prims.bool  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun ps pb e -> (with_comment (p_noSeqTerm' ps pb) e e.FStar_Parser_AST.range))
and p_noSeqTerm' : Prims.bool  ->  Prims.bool  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun ps pb e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Ascribed (e1, t, FStar_Pervasives_Native.None) -> begin
(

let uu____7354 = (

let uu____7355 = (p_tmIff e1)
in (

let uu____7356 = (

let uu____7357 = (

let uu____7358 = (p_typ ps pb t)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____7358))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____7357))
in (FStar_Pprint.op_Hat_Slash_Hat uu____7355 uu____7356)))
in (FStar_Pprint.group uu____7354))
end
| FStar_Parser_AST.Ascribed (e1, t, FStar_Pervasives_Native.Some (tac)) -> begin
(

let uu____7364 = (

let uu____7365 = (p_tmIff e1)
in (

let uu____7366 = (

let uu____7367 = (

let uu____7368 = (

let uu____7369 = (p_typ false false t)
in (

let uu____7372 = (

let uu____7373 = (str "by")
in (

let uu____7375 = (p_typ ps pb tac)
in (FStar_Pprint.op_Hat_Slash_Hat uu____7373 uu____7375)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____7369 uu____7372)))
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____7368))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____7367))
in (FStar_Pprint.op_Hat_Slash_Hat uu____7365 uu____7366)))
in (FStar_Pprint.group uu____7364))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = ".()<-"; FStar_Ident.idRange = uu____7376}, (e1)::(e2)::(e3)::[]) -> begin
(

let uu____7383 = (

let uu____7384 = (

let uu____7385 = (

let uu____7386 = (p_atomicTermNotQUident e1)
in (

let uu____7387 = (

let uu____7388 = (

let uu____7389 = (

let uu____7390 = (p_term false false e2)
in (soft_parens_with_nesting uu____7390))
in (

let uu____7393 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat uu____7389 uu____7393)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7388))
in (FStar_Pprint.op_Hat_Hat uu____7386 uu____7387)))
in (FStar_Pprint.group uu____7385))
in (

let uu____7394 = (

let uu____7395 = (p_noSeqTermAndComment ps pb e3)
in (jump2 uu____7395))
in (FStar_Pprint.op_Hat_Hat uu____7384 uu____7394)))
in (FStar_Pprint.group uu____7383))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = ".[]<-"; FStar_Ident.idRange = uu____7396}, (e1)::(e2)::(e3)::[]) -> begin
(

let uu____7403 = (

let uu____7404 = (

let uu____7405 = (

let uu____7406 = (p_atomicTermNotQUident e1)
in (

let uu____7407 = (

let uu____7408 = (

let uu____7409 = (

let uu____7410 = (p_term false false e2)
in (soft_brackets_with_nesting uu____7410))
in (

let uu____7413 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat uu____7409 uu____7413)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7408))
in (FStar_Pprint.op_Hat_Hat uu____7406 uu____7407)))
in (FStar_Pprint.group uu____7405))
in (

let uu____7414 = (

let uu____7415 = (p_noSeqTermAndComment ps pb e3)
in (jump2 uu____7415))
in (FStar_Pprint.op_Hat_Hat uu____7404 uu____7414)))
in (FStar_Pprint.group uu____7403))
end
| FStar_Parser_AST.Requires (e1, wtf) -> begin
(

let uu____7425 = (

let uu____7426 = (str "requires")
in (

let uu____7428 = (p_typ ps pb e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____7426 uu____7428)))
in (FStar_Pprint.group uu____7425))
end
| FStar_Parser_AST.Ensures (e1, wtf) -> begin
(

let uu____7438 = (

let uu____7439 = (str "ensures")
in (

let uu____7441 = (p_typ ps pb e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____7439 uu____7441)))
in (FStar_Pprint.group uu____7438))
end
| FStar_Parser_AST.Attributes (es) -> begin
(

let uu____7445 = (

let uu____7446 = (str "attributes")
in (

let uu____7448 = (FStar_Pprint.separate_map break1 p_atomicTerm es)
in (FStar_Pprint.op_Hat_Slash_Hat uu____7446 uu____7448)))
in (FStar_Pprint.group uu____7445))
end
| FStar_Parser_AST.If (e1, e2, e3) -> begin
(match ((is_unit e3)) with
| true -> begin
(

let uu____7453 = (

let uu____7454 = (

let uu____7455 = (str "if")
in (

let uu____7457 = (p_noSeqTermAndComment false false e1)
in (op_Hat_Slash_Plus_Hat uu____7455 uu____7457)))
in (

let uu____7460 = (

let uu____7461 = (str "then")
in (

let uu____7463 = (p_noSeqTermAndComment ps pb e2)
in (op_Hat_Slash_Plus_Hat uu____7461 uu____7463)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____7454 uu____7460)))
in (FStar_Pprint.group uu____7453))
end
| uu____7464 -> begin
(

let e2_doc = (match (e2.FStar_Parser_AST.tm) with
| FStar_Parser_AST.If (uu____7467, uu____7468, e31) when (is_unit e31) -> begin
(

let uu____7470 = (p_noSeqTermAndComment false false e2)
in (soft_parens_with_nesting uu____7470))
end
| uu____7473 -> begin
(p_noSeqTermAndComment false false e2)
end)
in (

let uu____7476 = (

let uu____7477 = (

let uu____7478 = (str "if")
in (

let uu____7480 = (p_noSeqTermAndComment false false e1)
in (op_Hat_Slash_Plus_Hat uu____7478 uu____7480)))
in (

let uu____7483 = (

let uu____7484 = (

let uu____7485 = (str "then")
in (op_Hat_Slash_Plus_Hat uu____7485 e2_doc))
in (

let uu____7487 = (

let uu____7488 = (str "else")
in (

let uu____7490 = (p_noSeqTermAndComment ps pb e3)
in (op_Hat_Slash_Plus_Hat uu____7488 uu____7490)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____7484 uu____7487)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____7477 uu____7483)))
in (FStar_Pprint.group uu____7476)))
end)
end
| FStar_Parser_AST.TryWith (e1, branches) -> begin
(

let uu____7513 = (

let uu____7514 = (

let uu____7515 = (

let uu____7516 = (str "try")
in (

let uu____7518 = (p_noSeqTermAndComment false false e1)
in (prefix2 uu____7516 uu____7518)))
in (

let uu____7521 = (

let uu____7522 = (str "with")
in (

let uu____7524 = (separate_map_last FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat uu____7522 uu____7524)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____7515 uu____7521)))
in (FStar_Pprint.group uu____7514))
in (

let uu____7533 = (paren_if (ps || pb))
in (uu____7533 uu____7513)))
end
| FStar_Parser_AST.Match (e1, branches) -> begin
(

let uu____7560 = (

let uu____7561 = (

let uu____7562 = (

let uu____7563 = (str "match")
in (

let uu____7565 = (p_noSeqTermAndComment false false e1)
in (

let uu____7568 = (str "with")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____7563 uu____7565 uu____7568))))
in (

let uu____7572 = (separate_map_last FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat uu____7562 uu____7572)))
in (FStar_Pprint.group uu____7561))
in (

let uu____7581 = (paren_if (ps || pb))
in (uu____7581 uu____7560)))
end
| FStar_Parser_AST.LetOpen (uid, e1) -> begin
(

let uu____7588 = (

let uu____7589 = (

let uu____7590 = (

let uu____7591 = (str "let open")
in (

let uu____7593 = (p_quident uid)
in (

let uu____7594 = (str "in")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____7591 uu____7593 uu____7594))))
in (

let uu____7598 = (p_term false pb e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____7590 uu____7598)))
in (FStar_Pprint.group uu____7589))
in (

let uu____7600 = (paren_if ps)
in (uu____7600 uu____7588)))
end
| FStar_Parser_AST.Let (q, lbs, e1) -> begin
(

let p_lb = (fun q1 uu____7665 is_last -> (match (uu____7665) with
| (a, (pat, e2)) -> begin
(

let attrs = (p_attrs_opt a)
in (

let doc_let_or_and = (match (q1) with
| FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec) -> begin
(

let uu____7699 = (

let uu____7700 = (str "let")
in (

let uu____7702 = (str "rec")
in (FStar_Pprint.op_Hat_Slash_Hat uu____7700 uu____7702)))
in (FStar_Pprint.group uu____7699))
end
| FStar_Pervasives_Native.Some (FStar_Parser_AST.NoLetQualifier) -> begin
(str "let")
end
| uu____7705 -> begin
(str "and")
end)
in (

let doc_pat = (p_letlhs doc_let_or_and ((pat), (e2)) true)
in (

let uu____7711 = (p_term_sep false false e2)
in (match (uu____7711) with
| (comm, doc_expr) -> begin
(

let doc_expr1 = (inline_comment_or_above comm doc_expr FStar_Pprint.empty)
in (

let uu____7721 = (match (is_last) with
| true -> begin
(

let uu____7723 = (FStar_Pprint.flow break1 ((doc_pat)::(FStar_Pprint.equals)::[]))
in (

let uu____7724 = (str "in")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____7723 doc_expr1 uu____7724)))
end
| uu____7728 -> begin
(

let uu____7730 = (FStar_Pprint.flow break1 ((doc_pat)::(FStar_Pprint.equals)::(doc_expr1)::[]))
in (FStar_Pprint.hang (Prims.parse_int "2") uu____7730))
end)
in (FStar_Pprint.op_Hat_Hat attrs uu____7721)))
end)))))
end))
in (

let l = (FStar_List.length lbs)
in (

let lbs_docs = (FStar_List.mapi (fun i lb -> (match ((Prims.op_Equality i (Prims.parse_int "0"))) with
| true -> begin
(

let uu____7781 = (p_lb (FStar_Pervasives_Native.Some (q)) lb (Prims.op_Equality i (l - (Prims.parse_int "1"))))
in (FStar_Pprint.group uu____7781))
end
| uu____7784 -> begin
(

let uu____7786 = (p_lb FStar_Pervasives_Native.None lb (Prims.op_Equality i (l - (Prims.parse_int "1"))))
in (FStar_Pprint.group uu____7786))
end)) lbs)
in (

let lbs_doc = (

let uu____7790 = (FStar_Pprint.separate break1 lbs_docs)
in (FStar_Pprint.group uu____7790))
in (

let uu____7791 = (

let uu____7792 = (

let uu____7793 = (

let uu____7794 = (p_term false pb e1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7794))
in (FStar_Pprint.op_Hat_Hat lbs_doc uu____7793))
in (FStar_Pprint.group uu____7792))
in (

let uu____7796 = (paren_if ps)
in (uu____7796 uu____7791)))))))
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, typ_opt); FStar_Parser_AST.prange = uu____7803})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, branches); FStar_Parser_AST.range = uu____7806; FStar_Parser_AST.level = uu____7807}) when (matches_var maybe_x x) -> begin
(

let uu____7834 = (

let uu____7835 = (

let uu____7836 = (str "function")
in (

let uu____7838 = (separate_map_last FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat uu____7836 uu____7838)))
in (FStar_Pprint.group uu____7835))
in (

let uu____7847 = (paren_if (ps || pb))
in (uu____7847 uu____7834)))
end
| FStar_Parser_AST.Quote (e1, FStar_Parser_AST.Dynamic) -> begin
(

let uu____7853 = (

let uu____7854 = (str "quote")
in (

let uu____7856 = (p_noSeqTermAndComment ps pb e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____7854 uu____7856)))
in (FStar_Pprint.group uu____7853))
end
| FStar_Parser_AST.Quote (e1, FStar_Parser_AST.Static) -> begin
(

let uu____7858 = (

let uu____7859 = (str "`")
in (

let uu____7861 = (p_noSeqTermAndComment ps pb e1)
in (FStar_Pprint.op_Hat_Hat uu____7859 uu____7861)))
in (FStar_Pprint.group uu____7858))
end
| FStar_Parser_AST.VQuote (e1) -> begin
(

let uu____7863 = (

let uu____7864 = (str "`%")
in (

let uu____7866 = (p_noSeqTermAndComment ps pb e1)
in (FStar_Pprint.op_Hat_Hat uu____7864 uu____7866)))
in (FStar_Pprint.group uu____7863))
end
| FStar_Parser_AST.Antiquote ({FStar_Parser_AST.tm = FStar_Parser_AST.Quote (e1, FStar_Parser_AST.Dynamic); FStar_Parser_AST.range = uu____7868; FStar_Parser_AST.level = uu____7869}) -> begin
(

let uu____7870 = (

let uu____7871 = (str "`@")
in (

let uu____7873 = (p_noSeqTermAndComment ps pb e1)
in (FStar_Pprint.op_Hat_Hat uu____7871 uu____7873)))
in (FStar_Pprint.group uu____7870))
end
| FStar_Parser_AST.Antiquote (e1) -> begin
(

let uu____7875 = (

let uu____7876 = (str "`#")
in (

let uu____7878 = (p_noSeqTermAndComment ps pb e1)
in (FStar_Pprint.op_Hat_Hat uu____7876 uu____7878)))
in (FStar_Pprint.group uu____7875))
end
| FStar_Parser_AST.CalcProof (rel, init1, steps) -> begin
(

let head1 = (

let uu____7887 = (str "calc")
in (

let uu____7889 = (

let uu____7890 = (

let uu____7891 = (p_noSeqTermAndComment false false rel)
in (

let uu____7894 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.lbrace)
in (FStar_Pprint.op_Hat_Hat uu____7891 uu____7894)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7890))
in (FStar_Pprint.op_Hat_Hat uu____7887 uu____7889)))
in (

let bot = FStar_Pprint.rbrace
in (

let uu____7896 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline bot)
in (

let uu____7897 = (

let uu____7898 = (

let uu____7899 = (

let uu____7900 = (p_noSeqTermAndComment false false init1)
in (

let uu____7903 = (

let uu____7904 = (str ";")
in (

let uu____7906 = (

let uu____7907 = (separate_map_last FStar_Pprint.hardline p_calcStep steps)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7907))
in (FStar_Pprint.op_Hat_Hat uu____7904 uu____7906)))
in (FStar_Pprint.op_Hat_Hat uu____7900 uu____7903)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7899))
in (FStar_All.pipe_left (FStar_Pprint.nest (Prims.parse_int "2")) uu____7898))
in (FStar_Pprint.enclose head1 uu____7896 uu____7897)))))
end
| uu____7909 -> begin
(p_typ ps pb e)
end))
and p_calcStep : Prims.bool  ->  FStar_Parser_AST.calc_step  ->  FStar_Pprint.document = (fun uu____7910 uu____7911 -> (match (uu____7911) with
| FStar_Parser_AST.CalcStep (rel, just, next) -> begin
(

let uu____7916 = (

let uu____7917 = (p_noSeqTermAndComment false false rel)
in (

let uu____7920 = (

let uu____7921 = (

let uu____7922 = (

let uu____7923 = (

let uu____7924 = (p_noSeqTermAndComment false false just)
in (

let uu____7927 = (

let uu____7928 = (

let uu____7929 = (

let uu____7930 = (

let uu____7931 = (p_noSeqTermAndComment false false next)
in (

let uu____7934 = (str ";")
in (FStar_Pprint.op_Hat_Hat uu____7931 uu____7934)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7930))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace uu____7929))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7928))
in (FStar_Pprint.op_Hat_Hat uu____7924 uu____7927)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7923))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____7922))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7921))
in (FStar_Pprint.op_Hat_Hat uu____7917 uu____7920)))
in (FStar_Pprint.group uu____7916))
end))
and p_attrs_opt : FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option  ->  FStar_Pprint.document = (fun uu___11_7936 -> (match (uu___11_7936) with
| FStar_Pervasives_Native.None -> begin
FStar_Pprint.empty
end
| FStar_Pervasives_Native.Some (terms) -> begin
(

let uu____7948 = (

let uu____7949 = (str "[@")
in (

let uu____7951 = (

let uu____7952 = (FStar_Pprint.separate_map break1 p_atomicTerm terms)
in (

let uu____7953 = (str "]")
in (FStar_Pprint.op_Hat_Slash_Hat uu____7952 uu____7953)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____7949 uu____7951)))
in (FStar_Pprint.group uu____7948))
end))
and p_typ : Prims.bool  ->  Prims.bool  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun ps pb e -> (with_comment (p_typ' ps pb) e e.FStar_Parser_AST.range))
and p_typ_sep : Prims.bool  ->  Prims.bool  ->  FStar_Parser_AST.term  ->  (FStar_Pprint.document * FStar_Pprint.document) = (fun ps pb e -> (with_comment_sep (p_typ' ps pb) e e.FStar_Parser_AST.range))
and p_typ' : Prims.bool  ->  Prims.bool  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun ps pb e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.QForall (bs, (uu____7971, trigger), e1) -> begin
(

let binders_doc = (p_binders true bs)
in (

let term_doc = (p_noSeqTermAndComment ps pb e1)
in (match (trigger) with
| [] -> begin
(

let uu____8005 = (

let uu____8006 = (

let uu____8007 = (p_quantifier e)
in (FStar_Pprint.op_Hat_Hat uu____8007 FStar_Pprint.space))
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") uu____8006 binders_doc FStar_Pprint.dot))
in (prefix2 uu____8005 term_doc))
end
| pats -> begin
(

let uu____8015 = (

let uu____8016 = (

let uu____8017 = (

let uu____8018 = (

let uu____8019 = (p_quantifier e)
in (FStar_Pprint.op_Hat_Hat uu____8019 FStar_Pprint.space))
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") uu____8018 binders_doc FStar_Pprint.dot))
in (

let uu____8022 = (p_trigger trigger)
in (prefix2 uu____8017 uu____8022)))
in (FStar_Pprint.group uu____8016))
in (prefix2 uu____8015 term_doc))
end)))
end
| FStar_Parser_AST.QExists (bs, (uu____8024, trigger), e1) -> begin
(

let binders_doc = (p_binders true bs)
in (

let term_doc = (p_noSeqTermAndComment ps pb e1)
in (match (trigger) with
| [] -> begin
(

let uu____8058 = (

let uu____8059 = (

let uu____8060 = (p_quantifier e)
in (FStar_Pprint.op_Hat_Hat uu____8060 FStar_Pprint.space))
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") uu____8059 binders_doc FStar_Pprint.dot))
in (prefix2 uu____8058 term_doc))
end
| pats -> begin
(

let uu____8068 = (

let uu____8069 = (

let uu____8070 = (

let uu____8071 = (

let uu____8072 = (p_quantifier e)
in (FStar_Pprint.op_Hat_Hat uu____8072 FStar_Pprint.space))
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") uu____8071 binders_doc FStar_Pprint.dot))
in (

let uu____8075 = (p_trigger trigger)
in (prefix2 uu____8070 uu____8075)))
in (FStar_Pprint.group uu____8069))
in (prefix2 uu____8068 term_doc))
end)))
end
| uu____8076 -> begin
(p_simpleTerm ps pb e)
end))
and p_typ_top : annotation_style  ->  Prims.bool  ->  Prims.bool  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun style ps pb e -> (with_comment (p_typ_top' style ps pb) e e.FStar_Parser_AST.range))
and p_typ_top' : annotation_style  ->  Prims.bool  ->  Prims.bool  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun style ps pb e -> (p_tmArrow style true p_tmFormula e))
and sig_as_binders_if_possible : FStar_Parser_AST.term  ->  Prims.bool  ->  FStar_Pprint.document = (fun t extra_space -> (

let s = (match (extra_space) with
| true -> begin
FStar_Pprint.space
end
| uu____8095 -> begin
FStar_Pprint.empty
end)
in (

let uu____8097 = (all_binders_annot t)
in (match (uu____8097) with
| true -> begin
(

let uu____8100 = (p_typ_top (Binders ((((Prims.parse_int "4")), ((Prims.parse_int "0")), (true)))) false false t)
in (FStar_Pprint.op_Hat_Hat s uu____8100))
end
| uu____8109 -> begin
(

let uu____8111 = (

let uu____8112 = (

let uu____8113 = (p_typ_top (Arrows ((((Prims.parse_int "2")), ((Prims.parse_int "2"))))) false false t)
in (FStar_Pprint.op_Hat_Hat s uu____8113))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____8112))
in (FStar_Pprint.group uu____8111))
end))))
and collapse_pats : (FStar_Pprint.document * FStar_Pprint.document) Prims.list  ->  FStar_Pprint.document Prims.list = (fun pats -> (

let fold_fun = (fun bs x -> (

let uu____8172 = x
in (match (uu____8172) with
| (b1, t1) -> begin
(match (bs) with
| [] -> begin
((((b1)::[]), (t1)))::[]
end
| (hd1)::tl1 -> begin
(

let uu____8237 = hd1
in (match (uu____8237) with
| (b2s, t2) -> begin
(match ((Prims.op_Equality t1 t2)) with
| true -> begin
((((FStar_List.append b2s ((b1)::[]))), (t1)))::tl1
end
| uu____8275 -> begin
((((b1)::[]), (t1)))::(hd1)::tl1
end)
end))
end)
end)))
in (

let p_collapsed_binder = (fun cb -> (

let uu____8309 = cb
in (match (uu____8309) with
| (bs, typ) -> begin
(match (bs) with
| [] -> begin
(failwith "Impossible")
end
| (b)::[] -> begin
(cat_with_colon b typ)
end
| (hd1)::tl1 -> begin
(

let uu____8328 = (FStar_List.fold_left (fun x y -> (

let uu____8334 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space y)
in (FStar_Pprint.op_Hat_Hat x uu____8334))) hd1 tl1)
in (cat_with_colon uu____8328 typ))
end)
end)))
in (

let binders = (FStar_List.fold_left fold_fun [] (FStar_List.rev pats))
in (map_rev p_collapsed_binder binders)))))
and pats_as_binders_if_possible : FStar_Parser_AST.pattern Prims.list  ->  (FStar_Pprint.document Prims.list * annotation_style) = (fun pats -> (

let all_binders = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, (t, FStar_Pervasives_Native.None)) -> begin
(match (((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm))) with
| (FStar_Parser_AST.PatVar (lid, aqual), FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t1); FStar_Parser_AST.brange = uu____8413; FStar_Parser_AST.blevel = uu____8414; FStar_Parser_AST.aqual = uu____8415}, phi)) when (Prims.op_Equality lid.FStar_Ident.idText lid'.FStar_Ident.idText) -> begin
(

let uu____8424 = (

let uu____8429 = (p_ident lid)
in (p_refinement' aqual uu____8429 t1 phi))
in FStar_Pervasives_Native.Some (uu____8424))
end
| (FStar_Parser_AST.PatVar (lid, aqual), uu____8436) -> begin
(

let uu____8441 = (

let uu____8446 = (

let uu____8447 = (FStar_Pprint.optional p_aqual aqual)
in (

let uu____8448 = (p_ident lid)
in (FStar_Pprint.op_Hat_Hat uu____8447 uu____8448)))
in (

let uu____8449 = (p_tmEqNoRefinement t)
in ((uu____8446), (uu____8449))))
in FStar_Pervasives_Native.Some (uu____8441))
end
| uu____8454 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____8463 -> begin
FStar_Pervasives_Native.None
end))
in (

let all_unbound = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (uu____8476) -> begin
false
end
| uu____8488 -> begin
true
end))
in (

let uu____8490 = (map_if_all all_binders pats)
in (match (uu____8490) with
| FStar_Pervasives_Native.Some (bs) -> begin
(

let uu____8522 = (collapse_pats bs)
in ((uu____8522), (Binders ((((Prims.parse_int "4")), ((Prims.parse_int "0")), (true))))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____8539 = (FStar_List.map p_atomicPattern pats)
in ((uu____8539), (Binders ((((Prims.parse_int "4")), ((Prims.parse_int "0")), (false))))))
end)))))
and p_quantifier : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.QForall (uu____8551) -> begin
(str "forall")
end
| FStar_Parser_AST.QExists (uu____8571) -> begin
(str "exists")
end
| uu____8591 -> begin
(failwith "Imposible : p_quantifier called on a non-quantifier term")
end))
and p_trigger : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun uu___12_8593 -> (match (uu___12_8593) with
| [] -> begin
FStar_Pprint.empty
end
| pats -> begin
(

let uu____8605 = (

let uu____8606 = (

let uu____8607 = (

let uu____8608 = (str "pattern")
in (

let uu____8610 = (

let uu____8611 = (

let uu____8612 = (p_disjunctivePats pats)
in (FStar_Pprint.jump (Prims.parse_int "2") (Prims.parse_int "0") uu____8612))
in (FStar_Pprint.op_Hat_Hat uu____8611 FStar_Pprint.rbrace))
in (FStar_Pprint.op_Hat_Slash_Hat uu____8608 uu____8610)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____8607))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____8606))
in (FStar_Pprint.group uu____8605))
end))
and p_disjunctivePats : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun pats -> (

let uu____8620 = (str "\\/")
in (FStar_Pprint.separate_map uu____8620 p_conjunctivePats pats)))
and p_conjunctivePats : FStar_Parser_AST.term Prims.list  ->  FStar_Pprint.document = (fun pats -> (

let uu____8627 = (

let uu____8628 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (FStar_Pprint.separate_map uu____8628 p_appTerm pats))
in (FStar_Pprint.group uu____8627)))
and p_simpleTerm : Prims.bool  ->  Prims.bool  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun ps pb e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Abs (pats, e1) -> begin
(

let uu____8640 = (p_term_sep false pb e1)
in (match (uu____8640) with
| (comm, doc1) -> begin
(

let prefix1 = (

let uu____8649 = (str "fun")
in (

let uu____8651 = (

let uu____8652 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Slash_Hat uu____8652 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat uu____8649 uu____8651)))
in (

let uu____8653 = (match ((Prims.op_disEquality comm FStar_Pprint.empty)) with
| true -> begin
(

let uu____8655 = (

let uu____8656 = (

let uu____8657 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1)
in (FStar_Pprint.op_Hat_Hat comm uu____8657))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____8656))
in (FStar_Pprint.op_Hat_Hat prefix1 uu____8655))
end
| uu____8658 -> begin
(

let uu____8660 = (op_Hat_Slash_Plus_Hat prefix1 doc1)
in (FStar_Pprint.group uu____8660))
end)
in (

let uu____8661 = (paren_if ps)
in (uu____8661 uu____8653))))
end))
end
| uu____8666 -> begin
(p_tmIff e)
end))
and p_maybeFocusArrow : Prims.bool  ->  FStar_Pprint.document = (fun b -> (match (b) with
| true -> begin
(str "~>")
end
| uu____8671 -> begin
FStar_Pprint.rarrow
end))
and p_patternBranch : Prims.bool  ->  (FStar_Parser_AST.pattern * FStar_Parser_AST.term FStar_Pervasives_Native.option * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun pb uu____8674 -> (match (uu____8674) with
| (pat, when_opt, e) -> begin
(

let one_pattern_branch = (fun p -> (

let branch = (match (when_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____8698 = (

let uu____8699 = (

let uu____8700 = (

let uu____8701 = (p_tuplePattern p)
in (

let uu____8702 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rarrow)
in (FStar_Pprint.op_Hat_Hat uu____8701 uu____8702)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8700))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8699))
in (FStar_Pprint.group uu____8698))
end
| FStar_Pervasives_Native.Some (f) -> begin
(

let uu____8704 = (

let uu____8705 = (

let uu____8706 = (

let uu____8707 = (

let uu____8708 = (

let uu____8709 = (p_tuplePattern p)
in (

let uu____8710 = (str "when")
in (FStar_Pprint.op_Hat_Slash_Hat uu____8709 uu____8710)))
in (FStar_Pprint.group uu____8708))
in (

let uu____8712 = (

let uu____8713 = (

let uu____8716 = (p_tmFormula f)
in (uu____8716)::(FStar_Pprint.rarrow)::[])
in (FStar_Pprint.flow break1 uu____8713))
in (FStar_Pprint.op_Hat_Slash_Hat uu____8707 uu____8712)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8706))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8705))
in (FStar_Pprint.hang (Prims.parse_int "2") uu____8704))
end)
in (

let uu____8718 = (p_term_sep false pb e)
in (match (uu____8718) with
| (comm, doc1) -> begin
(match (pb) with
| true -> begin
(match ((Prims.op_Equality comm FStar_Pprint.empty)) with
| true -> begin
(

let uu____8728 = (op_Hat_Slash_Plus_Hat branch doc1)
in (FStar_Pprint.group uu____8728))
end
| uu____8729 -> begin
(

let uu____8731 = (

let uu____8732 = (

let uu____8733 = (

let uu____8734 = (

let uu____8735 = (FStar_Pprint.op_Hat_Hat break1 comm)
in (FStar_Pprint.op_Hat_Hat doc1 uu____8735))
in (op_Hat_Slash_Plus_Hat branch uu____8734))
in (FStar_Pprint.group uu____8733))
in (

let uu____8736 = (

let uu____8737 = (

let uu____8738 = (inline_comment_or_above comm doc1 FStar_Pprint.empty)
in (jump2 uu____8738))
in (FStar_Pprint.op_Hat_Hat branch uu____8737))
in (FStar_Pprint.ifflat uu____8732 uu____8736)))
in (FStar_Pprint.group uu____8731))
end)
end
| uu____8739 -> begin
(match ((Prims.op_disEquality comm FStar_Pprint.empty)) with
| true -> begin
(

let uu____8742 = (

let uu____8743 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1)
in (FStar_Pprint.op_Hat_Hat comm uu____8743))
in (op_Hat_Slash_Plus_Hat branch uu____8742))
end
| uu____8744 -> begin
(op_Hat_Slash_Plus_Hat branch doc1)
end)
end)
end))))
in (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr (pats) -> begin
(match ((FStar_List.rev pats)) with
| (hd1)::tl1 -> begin
(

let last_pat_branch = (one_pattern_branch hd1)
in (

let uu____8754 = (

let uu____8755 = (

let uu____8756 = (

let uu____8757 = (

let uu____8758 = (

let uu____8759 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space)
in (FStar_Pprint.op_Hat_Hat break1 uu____8759))
in (FStar_Pprint.separate_map uu____8758 p_tuplePattern (FStar_List.rev tl1)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____8757 last_pat_branch))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8756))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8755))
in (FStar_Pprint.group uu____8754)))
end
| [] -> begin
(failwith "Impossible: disjunctive pattern can\'t be empty")
end)
end
| uu____8761 -> begin
(one_pattern_branch pat)
end))
end))
and p_tmIff : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____8763}, (e1)::(e2)::[]) -> begin
(

let uu____8769 = (str "<==>")
in (

let uu____8771 = (p_tmImplies e1)
in (

let uu____8772 = (p_tmIff e2)
in (infix0 uu____8769 uu____8771 uu____8772))))
end
| uu____8773 -> begin
(p_tmImplies e)
end))
and p_tmImplies : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____8775}, (e1)::(e2)::[]) -> begin
(

let uu____8781 = (str "==>")
in (

let uu____8783 = (p_tmArrow (Arrows ((((Prims.parse_int "2")), ((Prims.parse_int "2"))))) false p_tmFormula e1)
in (

let uu____8789 = (p_tmImplies e2)
in (infix0 uu____8781 uu____8783 uu____8789))))
end
| uu____8790 -> begin
(p_tmArrow (Arrows ((((Prims.parse_int "2")), ((Prims.parse_int "2"))))) false p_tmFormula e)
end))
and format_sig : annotation_style  ->  FStar_Pprint.document Prims.list  ->  Prims.bool  ->  Prims.bool  ->  FStar_Pprint.document = (fun style terms no_last_op flat_space -> (

let uu____8804 = (FStar_List.splitAt ((FStar_List.length terms) - (Prims.parse_int "1")) terms)
in (match (uu____8804) with
| (terms', last1) -> begin
(

let uu____8824 = (match (style) with
| Arrows (n1, ln) -> begin
(

let uu____8859 = (

let uu____8860 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8860))
in (

let uu____8861 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow FStar_Pprint.space)
in ((n1), (ln), (terms'), (uu____8859), (uu____8861))))
end
| Binders (n1, ln, parens1) -> begin
(

let uu____8875 = (match (parens1) with
| true -> begin
(FStar_List.map soft_parens_with_nesting terms')
end
| uu____8881 -> begin
terms'
end)
in (

let uu____8883 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.space)
in ((n1), (ln), (uu____8875), (break1), (uu____8883))))
end)
in (match (uu____8824) with
| (n1, last_n, terms'1, sep, last_op) -> begin
(

let last2 = (FStar_List.hd last1)
in (

let last_op1 = (match ((((FStar_List.length terms) > (Prims.parse_int "1")) && (not (no_last_op)))) with
| true -> begin
last_op
end
| uu____8905 -> begin
FStar_Pprint.empty
end)
in (

let one_line_space = (match (((not ((Prims.op_Equality last2 FStar_Pprint.empty))) || (not (no_last_op)))) with
| true -> begin
FStar_Pprint.space
end
| uu____8909 -> begin
FStar_Pprint.empty
end)
in (

let single_line_arg_indent = (FStar_Pprint.repeat n1 FStar_Pprint.space)
in (

let fs = (match (flat_space) with
| true -> begin
FStar_Pprint.space
end
| uu____8914 -> begin
FStar_Pprint.empty
end)
in (match ((FStar_List.length terms)) with
| _8916 when (_8916 = (Prims.parse_int "1")) -> begin
(FStar_List.hd terms)
end
| uu____8917 -> begin
(

let uu____8918 = (

let uu____8919 = (

let uu____8920 = (

let uu____8921 = (FStar_Pprint.separate sep terms'1)
in (

let uu____8922 = (

let uu____8923 = (FStar_Pprint.op_Hat_Hat last_op1 last2)
in (FStar_Pprint.op_Hat_Hat one_line_space uu____8923))
in (FStar_Pprint.op_Hat_Hat uu____8921 uu____8922)))
in (FStar_Pprint.op_Hat_Hat fs uu____8920))
in (

let uu____8924 = (

let uu____8925 = (

let uu____8926 = (

let uu____8927 = (

let uu____8928 = (FStar_Pprint.separate sep terms'1)
in (FStar_Pprint.op_Hat_Hat fs uu____8928))
in (

let uu____8929 = (

let uu____8930 = (

let uu____8931 = (

let uu____8932 = (FStar_Pprint.op_Hat_Hat sep single_line_arg_indent)
in (

let uu____8933 = (FStar_List.map (fun x -> (

let uu____8939 = (FStar_Pprint.hang (Prims.parse_int "2") x)
in (FStar_Pprint.align uu____8939))) terms'1)
in (FStar_Pprint.separate uu____8932 uu____8933)))
in (FStar_Pprint.op_Hat_Hat single_line_arg_indent uu____8931))
in (jump2 uu____8930))
in (FStar_Pprint.ifflat uu____8927 uu____8929)))
in (FStar_Pprint.group uu____8926))
in (

let uu____8941 = (

let uu____8942 = (

let uu____8943 = (FStar_Pprint.op_Hat_Hat last_op1 last2)
in (FStar_Pprint.hang last_n uu____8943))
in (FStar_Pprint.align uu____8942))
in (FStar_Pprint.prefix n1 (Prims.parse_int "1") uu____8925 uu____8941)))
in (FStar_Pprint.ifflat uu____8919 uu____8924)))
in (FStar_Pprint.group uu____8918))
end))))))
end))
end)))
and p_tmArrow : annotation_style  ->  Prims.bool  ->  (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun style flat_space p_Tm e -> (

let terms = (match (style) with
| Arrows (uu____8957) -> begin
(p_tmArrow' p_Tm e)
end
| Binders (uu____8964) -> begin
(collapse_binders p_Tm e)
end)
in (format_sig style terms false flat_space)))
and p_tmArrow' : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document Prims.list = (fun p_Tm e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Product (bs, tgt) -> begin
(

let uu____8987 = (FStar_List.map (fun b -> (p_binder false b)) bs)
in (

let uu____8993 = (p_tmArrow' p_Tm tgt)
in (FStar_List.append uu____8987 uu____8993)))
end
| uu____8996 -> begin
(

let uu____8997 = (p_Tm e)
in (uu____8997)::[])
end))
and collapse_binders : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document Prims.list = (fun p_Tm e -> (

let rec accumulate_binders = (fun p_Tm1 e1 -> (match (e1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Product (bs, tgt) -> begin
(

let uu____9050 = (FStar_List.map (fun b -> (p_binder' false b)) bs)
in (

let uu____9076 = (accumulate_binders p_Tm1 tgt)
in (FStar_List.append uu____9050 uu____9076)))
end
| uu____9099 -> begin
(

let uu____9100 = (

let uu____9111 = (p_Tm1 e1)
in ((uu____9111), (FStar_Pervasives_Native.None), (cat_with_colon)))
in (uu____9100)::[])
end))
in (

let fold_fun = (fun bs x -> (

let uu____9209 = x
in (match (uu____9209) with
| (b1, t1, f1) -> begin
(match (bs) with
| [] -> begin
((((b1)::[]), (t1), (f1)))::[]
end
| (hd1)::tl1 -> begin
(

let uu____9341 = hd1
in (match (uu____9341) with
| (b2s, t2, uu____9370) -> begin
(match (((t1), (t2))) with
| (FStar_Pervasives_Native.Some (typ1), FStar_Pervasives_Native.Some (typ2)) -> begin
(match ((Prims.op_Equality typ1 typ2)) with
| true -> begin
((((FStar_List.append b2s ((b1)::[]))), (t1), (f1)))::tl1
end
| uu____9440 -> begin
((((b1)::[]), (t1), (f1)))::(hd1)::tl1
end)
end
| uu____9472 -> begin
((((b1)::[]), (t1), (f1)))::bs
end)
end))
end)
end)))
in (

let p_collapsed_binder = (fun cb -> (

let uu____9529 = cb
in (match (uu____9529) with
| (bs, t, f) -> begin
(match (t) with
| FStar_Pervasives_Native.None -> begin
(match (bs) with
| (b)::[] -> begin
b
end
| uu____9558 -> begin
(failwith "Impossible")
end)
end
| FStar_Pervasives_Native.Some (typ) -> begin
(match (bs) with
| [] -> begin
(failwith "Impossible")
end
| (b)::[] -> begin
(f b typ)
end
| (hd1)::tl1 -> begin
(

let uu____9569 = (FStar_List.fold_left (fun x y -> (

let uu____9575 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space y)
in (FStar_Pprint.op_Hat_Hat x uu____9575))) hd1 tl1)
in (f uu____9569 typ))
end)
end)
end)))
in (

let binders = (

let uu____9591 = (accumulate_binders p_Tm e)
in (FStar_List.fold_left fold_fun [] uu____9591))
in (map_rev p_collapsed_binder binders))))))
and p_tmFormula : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let conj = (

let uu____9654 = (

let uu____9655 = (str "/\\")
in (FStar_Pprint.op_Hat_Hat uu____9655 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9654))
in (

let disj = (

let uu____9658 = (

let uu____9659 = (str "\\/")
in (FStar_Pprint.op_Hat_Hat uu____9659 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9658))
in (

let formula = (p_tmDisjunction e)
in (FStar_Pprint.flow_map disj (fun d -> (FStar_Pprint.flow_map conj (fun x -> (FStar_Pprint.group x)) d)) formula)))))
and p_tmDisjunction : FStar_Parser_AST.term  ->  FStar_Pprint.document Prims.list Prims.list = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____9679}, (e1)::(e2)::[]) -> begin
(

let uu____9685 = (p_tmDisjunction e1)
in (

let uu____9690 = (

let uu____9695 = (p_tmConjunction e2)
in (uu____9695)::[])
in (FStar_List.append uu____9685 uu____9690)))
end
| uu____9704 -> begin
(

let uu____9705 = (p_tmConjunction e)
in (uu____9705)::[])
end))
and p_tmConjunction : FStar_Parser_AST.term  ->  FStar_Pprint.document Prims.list = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____9715}, (e1)::(e2)::[]) -> begin
(

let uu____9721 = (p_tmConjunction e1)
in (

let uu____9724 = (

let uu____9727 = (p_tmTuple e2)
in (uu____9727)::[])
in (FStar_List.append uu____9721 uu____9724)))
end
| uu____9728 -> begin
(

let uu____9729 = (p_tmTuple e)
in (uu____9729)::[])
end))
and p_tmTuple : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_tmTuple' e e.FStar_Parser_AST.range))
and p_tmTuple' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (lid, args) when ((is_tuple_constructor lid) && (all_explicit args)) -> begin
(

let uu____9746 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map uu____9746 (fun uu____9754 -> (match (uu____9754) with
| (e1, uu____9760) -> begin
(p_tmEq e1)
end)) args))
end
| uu____9761 -> begin
(p_tmEq e)
end))
and paren_if_gt : Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun curr mine doc1 -> (match ((mine <= curr)) with
| true -> begin
doc1
end
| uu____9768 -> begin
(

let uu____9770 = (

let uu____9771 = (FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____9771))
in (FStar_Pprint.group uu____9770))
end))
and p_tmEqWith : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_X e -> (

let n1 = (max_level (FStar_List.append ((colon_equals)::(pipe_right)::[]) operatorInfix0ad12))
in (p_tmEqWith' p_X n1 e)))
and p_tmEqWith' : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_X curr e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (((is_operatorInfix0ad12 op) || (

let uu____9790 = (FStar_Ident.text_of_id op)
in (Prims.op_Equality uu____9790 "="))) || (

let uu____9795 = (FStar_Ident.text_of_id op)
in (Prims.op_Equality uu____9795 "|>"))) -> begin
(

let op1 = (FStar_Ident.text_of_id op)
in (

let uu____9801 = (levels op1)
in (match (uu____9801) with
| (left1, mine, right1) -> begin
(

let uu____9820 = (

let uu____9821 = (FStar_All.pipe_left str op1)
in (

let uu____9823 = (p_tmEqWith' p_X left1 e1)
in (

let uu____9824 = (p_tmEqWith' p_X right1 e2)
in (infix0 uu____9821 uu____9823 uu____9824))))
in (paren_if_gt curr mine uu____9820))
end)))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____9825}, (e1)::(e2)::[]) -> begin
(

let uu____9831 = (

let uu____9832 = (p_tmEqWith p_X e1)
in (

let uu____9833 = (

let uu____9834 = (

let uu____9835 = (

let uu____9836 = (p_tmEqWith p_X e2)
in (op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____9836))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____9835))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9834))
in (FStar_Pprint.op_Hat_Hat uu____9832 uu____9833)))
in (FStar_Pprint.group uu____9831))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____9837}, (e1)::[]) -> begin
(

let uu____9842 = (levels "-")
in (match (uu____9842) with
| (left1, mine, right1) -> begin
(

let uu____9862 = (p_tmEqWith' p_X mine e1)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____9862))
end))
end
| uu____9863 -> begin
(p_tmNoEqWith p_X e)
end))
and p_tmNoEqWith : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_X e -> (

let n1 = (max_level ((colon_colon)::(amp)::(opinfix3)::(opinfix4)::[]))
in (p_tmNoEqWith' false p_X n1 e)))
and p_tmNoEqWith' : Prims.bool  ->  (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun inside_tuple p_X curr e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Construct (lid, ((e1, uu____9911))::((e2, uu____9913))::[]) when ((FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) && (

let uu____9933 = (is_list e)
in (not (uu____9933)))) -> begin
(

let op = "::"
in (

let uu____9938 = (levels op)
in (match (uu____9938) with
| (left1, mine, right1) -> begin
(

let uu____9957 = (

let uu____9958 = (str op)
in (

let uu____9959 = (p_tmNoEqWith' false p_X left1 e1)
in (

let uu____9961 = (p_tmNoEqWith' false p_X right1 e2)
in (infix0 uu____9958 uu____9959 uu____9961))))
in (paren_if_gt curr mine uu____9957))
end)))
end
| FStar_Parser_AST.Sum (binders, res) -> begin
(

let op = "&"
in (

let uu____9980 = (levels op)
in (match (uu____9980) with
| (left1, mine, right1) -> begin
(

let p_dsumfst = (fun bt -> (match (bt) with
| FStar_Util.Inl (b) -> begin
(

let uu____10014 = (p_binder false b)
in (

let uu____10016 = (

let uu____10017 = (

let uu____10018 = (str op)
in (FStar_Pprint.op_Hat_Hat uu____10018 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____10017))
in (FStar_Pprint.op_Hat_Hat uu____10014 uu____10016)))
end
| FStar_Util.Inr (t) -> begin
(

let uu____10020 = (p_tmNoEqWith' false p_X left1 t)
in (

let uu____10022 = (

let uu____10023 = (

let uu____10024 = (str op)
in (FStar_Pprint.op_Hat_Hat uu____10024 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____10023))
in (FStar_Pprint.op_Hat_Hat uu____10020 uu____10022)))
end))
in (

let uu____10025 = (

let uu____10026 = (FStar_Pprint.concat_map p_dsumfst binders)
in (

let uu____10031 = (p_tmNoEqWith' false p_X right1 res)
in (FStar_Pprint.op_Hat_Hat uu____10026 uu____10031)))
in (paren_if_gt curr mine uu____10025)))
end)))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____10033}, (e1)::(e2)::[]) when (FStar_ST.op_Bang unfold_tuples) -> begin
(

let op = "*"
in (

let uu____10063 = (levels op)
in (match (uu____10063) with
| (left1, mine, right1) -> begin
(match (inside_tuple) with
| true -> begin
(

let uu____10083 = (str op)
in (

let uu____10084 = (p_tmNoEqWith' true p_X left1 e1)
in (

let uu____10086 = (p_tmNoEqWith' true p_X right1 e2)
in (infix0 uu____10083 uu____10084 uu____10086))))
end
| uu____10088 -> begin
(

let uu____10090 = (

let uu____10091 = (str op)
in (

let uu____10092 = (p_tmNoEqWith' true p_X left1 e1)
in (

let uu____10094 = (p_tmNoEqWith' true p_X right1 e2)
in (infix0 uu____10091 uu____10092 uu____10094))))
in (paren_if_gt curr mine uu____10090))
end)
end)))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (is_operatorInfix34 op) -> begin
(

let op1 = (FStar_Ident.text_of_id op)
in (

let uu____10103 = (levels op1)
in (match (uu____10103) with
| (left1, mine, right1) -> begin
(

let uu____10122 = (

let uu____10123 = (str op1)
in (

let uu____10124 = (p_tmNoEqWith' false p_X left1 e1)
in (

let uu____10126 = (p_tmNoEqWith' false p_X right1 e2)
in (infix0 uu____10123 uu____10124 uu____10126))))
in (paren_if_gt curr mine uu____10122))
end)))
end
| FStar_Parser_AST.Record (with_opt, record_fields) -> begin
(

let uu____10146 = (

let uu____10147 = (default_or_map FStar_Pprint.empty p_with_clause with_opt)
in (

let uu____10148 = (

let uu____10149 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (separate_map_last uu____10149 p_simpleDef record_fields))
in (FStar_Pprint.op_Hat_Hat uu____10147 uu____10148)))
in (braces_with_nesting uu____10146))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____10154}, (e1)::[]) -> begin
(

let uu____10159 = (

let uu____10160 = (str "~")
in (

let uu____10162 = (p_atomicTerm e1)
in (FStar_Pprint.op_Hat_Hat uu____10160 uu____10162)))
in (FStar_Pprint.group uu____10159))
end
| FStar_Parser_AST.Paren (p) when inside_tuple -> begin
(match (p.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____10164}, (e1)::(e2)::[]) -> begin
(

let op = "*"
in (

let uu____10173 = (levels op)
in (match (uu____10173) with
| (left1, mine, right1) -> begin
(

let uu____10192 = (

let uu____10193 = (str op)
in (

let uu____10194 = (p_tmNoEqWith' true p_X left1 e1)
in (

let uu____10196 = (p_tmNoEqWith' true p_X right1 e2)
in (infix0 uu____10193 uu____10194 uu____10196))))
in (paren_if_gt curr mine uu____10192))
end)))
end
| uu____10198 -> begin
(p_X e)
end)
end
| uu____10199 -> begin
(p_X e)
end))
and p_tmEqNoRefinement : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_tmEqWith p_appTerm e))
and p_tmEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_tmEqWith p_tmRefinement e))
and p_tmNoEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_tmNoEqWith p_tmRefinement e))
and p_tmRefinement : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.NamedTyp (lid, e1) -> begin
(

let uu____10206 = (

let uu____10207 = (p_lident lid)
in (

let uu____10208 = (

let uu____10209 = (p_appTerm e1)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____10209))
in (FStar_Pprint.op_Hat_Slash_Hat uu____10207 uu____10208)))
in (FStar_Pprint.group uu____10206))
end
| FStar_Parser_AST.Refine (b, phi) -> begin
(p_refinedBinder b phi)
end
| uu____10212 -> begin
(p_appTerm e)
end))
and p_with_clause : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____10214 = (p_appTerm e)
in (

let uu____10215 = (

let uu____10216 = (

let uu____10217 = (str "with")
in (FStar_Pprint.op_Hat_Hat uu____10217 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____10216))
in (FStar_Pprint.op_Hat_Hat uu____10214 uu____10215))))
and p_refinedBinder : FStar_Parser_AST.binder  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun b phi -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (lid, t) -> begin
(

let uu____10223 = (p_lident lid)
in (p_refinement b.FStar_Parser_AST.aqual uu____10223 t phi))
end
| FStar_Parser_AST.TAnnotated (uu____10224) -> begin
(failwith "Is this still used ?")
end
| FStar_Parser_AST.Variable (uu____10230) -> begin
(

let uu____10231 = (

let uu____10233 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" uu____10233))
in (failwith uu____10231))
end
| FStar_Parser_AST.TVariable (uu____10236) -> begin
(

let uu____10237 = (

let uu____10239 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" uu____10239))
in (failwith uu____10237))
end
| FStar_Parser_AST.NoName (uu____10242) -> begin
(

let uu____10243 = (

let uu____10245 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" uu____10245))
in (failwith uu____10243))
end))
and p_simpleDef : Prims.bool  ->  (FStar_Ident.lid * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun ps uu____10249 -> (match (uu____10249) with
| (lid, e) -> begin
(

let uu____10257 = (

let uu____10258 = (p_qlident lid)
in (

let uu____10259 = (

let uu____10260 = (p_noSeqTermAndComment ps false e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____10260))
in (FStar_Pprint.op_Hat_Slash_Hat uu____10258 uu____10259)))
in (FStar_Pprint.group uu____10257))
end))
and p_appTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App (uu____10263) when (is_general_application e) -> begin
(

let uu____10270 = (head_and_args e)
in (match (uu____10270) with
| (head1, args) -> begin
(match (args) with
| (e1)::(e2)::[] when (Prims.op_Equality (FStar_Pervasives_Native.snd e1) FStar_Parser_AST.Infix) -> begin
(

let uu____10317 = (p_argTerm e1)
in (

let uu____10318 = (

let uu____10319 = (

let uu____10320 = (

let uu____10321 = (str "`")
in (

let uu____10323 = (

let uu____10324 = (p_indexingTerm head1)
in (

let uu____10325 = (str "`")
in (FStar_Pprint.op_Hat_Hat uu____10324 uu____10325)))
in (FStar_Pprint.op_Hat_Hat uu____10321 uu____10323)))
in (FStar_Pprint.group uu____10320))
in (

let uu____10327 = (p_argTerm e2)
in (FStar_Pprint.op_Hat_Slash_Hat uu____10319 uu____10327)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____10317 uu____10318)))
end
| uu____10328 -> begin
(

let uu____10335 = (

let uu____10346 = (FStar_ST.op_Bang should_print_fs_typ_app)
in (match (uu____10346) with
| true -> begin
(

let uu____10380 = (FStar_Util.take (fun uu____10404 -> (match (uu____10404) with
| (uu____10410, aq) -> begin
(Prims.op_Equality aq FStar_Parser_AST.FsTypApp)
end)) args)
in (match (uu____10380) with
| (fs_typ_args, args1) -> begin
(

let uu____10448 = (

let uu____10449 = (p_indexingTerm head1)
in (

let uu____10450 = (

let uu____10451 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (soft_surround_map_or_flow (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.empty FStar_Pprint.langle uu____10451 FStar_Pprint.rangle p_fsTypArg fs_typ_args))
in (FStar_Pprint.op_Hat_Hat uu____10449 uu____10450)))
in ((uu____10448), (args1)))
end))
end
| uu____10464 -> begin
(

let uu____10466 = (p_indexingTerm head1)
in ((uu____10466), (args)))
end))
in (match (uu____10335) with
| (head_doc, args1) -> begin
(

let uu____10487 = (

let uu____10488 = (FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space)
in (soft_surround_map_or_flow (Prims.parse_int "2") (Prims.parse_int "0") head_doc uu____10488 break1 FStar_Pprint.empty p_argTerm args1))
in (FStar_Pprint.group uu____10487))
end))
end)
end))
end
| FStar_Parser_AST.Construct (lid, args) when ((is_general_construction e) && (

let uu____10510 = (is_dtuple_constructor lid)
in (not (uu____10510)))) -> begin
(match (args) with
| [] -> begin
(p_quident lid)
end
| (arg)::[] -> begin
(

let uu____10529 = (

let uu____10530 = (p_quident lid)
in (

let uu____10531 = (p_argTerm arg)
in (FStar_Pprint.op_Hat_Slash_Hat uu____10530 uu____10531)))
in (FStar_Pprint.group uu____10529))
end
| (hd1)::tl1 -> begin
(

let uu____10548 = (

let uu____10549 = (

let uu____10550 = (

let uu____10551 = (p_quident lid)
in (

let uu____10552 = (p_argTerm hd1)
in (prefix2 uu____10551 uu____10552)))
in (FStar_Pprint.group uu____10550))
in (

let uu____10553 = (

let uu____10554 = (FStar_Pprint.separate_map break1 p_argTerm tl1)
in (jump2 uu____10554))
in (FStar_Pprint.op_Hat_Hat uu____10549 uu____10553)))
in (FStar_Pprint.group uu____10548))
end)
end
| uu____10559 -> begin
(p_indexingTerm e)
end))
and p_argTerm : (FStar_Parser_AST.term * FStar_Parser_AST.imp)  ->  FStar_Pprint.document = (fun arg_imp -> (match (arg_imp) with
| (u, FStar_Parser_AST.UnivApp) -> begin
(p_universe u)
end
| (e, FStar_Parser_AST.FsTypApp) -> begin
((FStar_Errors.log_issue e.FStar_Parser_AST.range ((FStar_Errors.Warning_UnexpectedFsTypApp), ("Unexpected FsTypApp, output might not be formatted correctly.")));
(

let uu____10570 = (p_indexingTerm e)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.langle uu____10570 FStar_Pprint.rangle));
)
end
| (e, FStar_Parser_AST.Hash) -> begin
(

let uu____10574 = (str "#")
in (

let uu____10576 = (p_indexingTerm e)
in (FStar_Pprint.op_Hat_Hat uu____10574 uu____10576)))
end
| (e, FStar_Parser_AST.HashBrace (t)) -> begin
(

let uu____10579 = (str "#[")
in (

let uu____10581 = (

let uu____10582 = (p_indexingTerm t)
in (

let uu____10583 = (

let uu____10584 = (str "]")
in (

let uu____10586 = (p_indexingTerm e)
in (FStar_Pprint.op_Hat_Hat uu____10584 uu____10586)))
in (FStar_Pprint.op_Hat_Hat uu____10582 uu____10583)))
in (FStar_Pprint.op_Hat_Hat uu____10579 uu____10581)))
end
| (e, FStar_Parser_AST.Infix) -> begin
(p_indexingTerm e)
end
| (e, FStar_Parser_AST.Nothing) -> begin
(p_indexingTerm e)
end))
and p_fsTypArg : (FStar_Parser_AST.term * FStar_Parser_AST.imp)  ->  FStar_Pprint.document = (fun uu____10589 -> (match (uu____10589) with
| (e, uu____10595) -> begin
(p_indexingTerm e)
end))
and p_indexingTerm_aux : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun exit1 e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____10600}, (e1)::(e2)::[]) -> begin
(

let uu____10606 = (

let uu____10607 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (

let uu____10608 = (

let uu____10609 = (

let uu____10610 = (p_term false false e2)
in (soft_parens_with_nesting uu____10610))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10609))
in (FStar_Pprint.op_Hat_Hat uu____10607 uu____10608)))
in (FStar_Pprint.group uu____10606))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____10613}, (e1)::(e2)::[]) -> begin
(

let uu____10619 = (

let uu____10620 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (

let uu____10621 = (

let uu____10622 = (

let uu____10623 = (p_term false false e2)
in (soft_brackets_with_nesting uu____10623))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10622))
in (FStar_Pprint.op_Hat_Hat uu____10620 uu____10621)))
in (FStar_Pprint.group uu____10619))
end
| uu____10626 -> begin
(exit1 e)
end))
and p_indexingTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_indexingTerm_aux p_atomicTerm e))
and p_atomicTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.LetOpen (lid, e1) -> begin
(

let uu____10631 = (p_quident lid)
in (

let uu____10632 = (

let uu____10633 = (

let uu____10634 = (p_term false false e1)
in (soft_parens_with_nesting uu____10634))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10633))
in (FStar_Pprint.op_Hat_Hat uu____10631 uu____10632)))
end
| FStar_Parser_AST.Name (lid) -> begin
(p_quident lid)
end
| FStar_Parser_AST.Op (op, (e1)::[]) when (is_general_prefix_op op) -> begin
(

let uu____10642 = (

let uu____10643 = (FStar_Ident.text_of_id op)
in (str uu____10643))
in (

let uu____10645 = (p_atomicTerm e1)
in (FStar_Pprint.op_Hat_Hat uu____10642 uu____10645)))
end
| uu____10646 -> begin
(p_atomicTermNotQUident e)
end))
and p_atomicTermNotQUident : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Wild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.Var (lid) when (FStar_Ident.lid_equals lid FStar_Parser_Const.assert_lid) -> begin
(str "assert")
end
| FStar_Parser_AST.Var (lid) when (FStar_Ident.lid_equals lid FStar_Parser_Const.assume_lid) -> begin
(str "assume")
end
| FStar_Parser_AST.Tvar (tv) -> begin
(p_tvar tv)
end
| FStar_Parser_AST.Const (c) -> begin
(match (c) with
| FStar_Const.Const_char (x) when (Prims.op_Equality x 10) -> begin
(str "0x0Az")
end
| uu____10659 -> begin
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

let uu____10668 = (

let uu____10669 = (FStar_Ident.text_of_id op)
in (str uu____10669))
in (

let uu____10671 = (p_atomicTermNotQUident e1)
in (FStar_Pprint.op_Hat_Hat uu____10668 uu____10671)))
end
| FStar_Parser_AST.Op (op, []) -> begin
(

let uu____10675 = (

let uu____10676 = (

let uu____10677 = (

let uu____10678 = (FStar_Ident.text_of_id op)
in (str uu____10678))
in (

let uu____10680 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat uu____10677 uu____10680)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____10676))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____10675))
end
| FStar_Parser_AST.Construct (lid, args) when (is_dtuple_constructor lid) -> begin
(

let uu____10695 = (all_explicit args)
in (match (uu____10695) with
| true -> begin
(

let uu____10698 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (

let uu____10699 = (

let uu____10700 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (

let uu____10701 = (FStar_List.map FStar_Pervasives_Native.fst args)
in (FStar_Pprint.separate_map uu____10700 p_tmEq uu____10701)))
in (

let uu____10708 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____10698 uu____10699 uu____10708))))
end
| uu____10711 -> begin
(match (args) with
| [] -> begin
(p_quident lid)
end
| (arg)::[] -> begin
(

let uu____10730 = (

let uu____10731 = (p_quident lid)
in (

let uu____10732 = (p_argTerm arg)
in (FStar_Pprint.op_Hat_Slash_Hat uu____10731 uu____10732)))
in (FStar_Pprint.group uu____10730))
end
| (hd1)::tl1 -> begin
(

let uu____10749 = (

let uu____10750 = (

let uu____10751 = (

let uu____10752 = (p_quident lid)
in (

let uu____10753 = (p_argTerm hd1)
in (prefix2 uu____10752 uu____10753)))
in (FStar_Pprint.group uu____10751))
in (

let uu____10754 = (

let uu____10755 = (FStar_Pprint.separate_map break1 p_argTerm tl1)
in (jump2 uu____10755))
in (FStar_Pprint.op_Hat_Hat uu____10750 uu____10754)))
in (FStar_Pprint.group uu____10749))
end)
end))
end
| FStar_Parser_AST.Project (e1, lid) -> begin
(

let uu____10762 = (

let uu____10763 = (p_atomicTermNotQUident e1)
in (

let uu____10764 = (

let uu____10765 = (p_qlident lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10765))
in (FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0") uu____10763 uu____10764)))
in (FStar_Pprint.group uu____10762))
end
| uu____10768 -> begin
(p_projectionLHS e)
end))
and p_projectionLHS : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (lid) -> begin
(p_qlident lid)
end
| FStar_Parser_AST.Projector (constr_lid, field_lid) -> begin
(

let uu____10773 = (p_quident constr_lid)
in (

let uu____10774 = (

let uu____10775 = (

let uu____10776 = (p_lident field_lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10776))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____10775))
in (FStar_Pprint.op_Hat_Hat uu____10773 uu____10774)))
end
| FStar_Parser_AST.Discrim (constr_lid) -> begin
(

let uu____10778 = (p_quident constr_lid)
in (FStar_Pprint.op_Hat_Hat uu____10778 FStar_Pprint.qmark))
end
| FStar_Parser_AST.Paren (e1) -> begin
(

let uu____10780 = (p_term_sep false false e1)
in (match (uu____10780) with
| (comm, t) -> begin
(

let doc1 = (soft_parens_with_nesting t)
in (match ((Prims.op_Equality comm FStar_Pprint.empty)) with
| true -> begin
doc1
end
| uu____10791 -> begin
(

let uu____10793 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1)
in (FStar_Pprint.op_Hat_Hat comm uu____10793))
end))
end))
end
| uu____10794 when (is_array e) -> begin
(

let es = (extract_from_list e)
in (

let uu____10798 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar)
in (

let uu____10799 = (

let uu____10800 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (separate_map_or_flow_last uu____10800 (fun ps -> (p_noSeqTermAndComment ps false)) es))
in (

let uu____10805 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") uu____10798 uu____10799 uu____10805)))))
end
| uu____10808 when (is_list e) -> begin
(

let uu____10809 = (

let uu____10810 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (

let uu____10811 = (extract_from_list e)
in (separate_map_or_flow_last uu____10810 (fun ps -> (p_noSeqTermAndComment ps false)) uu____10811)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket uu____10809 FStar_Pprint.rbracket))
end
| uu____10820 when (is_lex_list e) -> begin
(

let uu____10821 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket)
in (

let uu____10822 = (

let uu____10823 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (

let uu____10824 = (extract_from_list e)
in (separate_map_or_flow_last uu____10823 (fun ps -> (p_noSeqTermAndComment ps false)) uu____10824)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____10821 uu____10822 FStar_Pprint.rbracket)))
end
| uu____10833 when (is_ref_set e) -> begin
(

let es = (extract_from_ref_set e)
in (

let uu____10837 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace)
in (

let uu____10838 = (

let uu____10839 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (separate_map_or_flow uu____10839 p_appTerm es))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") uu____10837 uu____10838 FStar_Pprint.rbrace))))
end
| FStar_Parser_AST.Labeled (e1, s, b) -> begin
(

let uu____10849 = (str (Prims.op_Hat "(*" (Prims.op_Hat s "*)")))
in (

let uu____10852 = (p_term false false e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____10849 uu____10852)))
end
| FStar_Parser_AST.Op (op, args) when (

let uu____10861 = (handleable_op op args)
in (not (uu____10861))) -> begin
(

let uu____10863 = (

let uu____10865 = (

let uu____10867 = (FStar_Ident.text_of_id op)
in (

let uu____10869 = (

let uu____10871 = (

let uu____10873 = (FStar_Util.string_of_int (FStar_List.length args))
in (Prims.op_Hat uu____10873 " arguments couldn\'t be handled by the pretty printer"))
in (Prims.op_Hat " with " uu____10871))
in (Prims.op_Hat uu____10867 uu____10869)))
in (Prims.op_Hat "Operation " uu____10865))
in (failwith uu____10863))
end
| FStar_Parser_AST.Uvar (id1) -> begin
(failwith "Unexpected universe variable out of universe context")
end
| FStar_Parser_AST.Wild -> begin
(

let uu____10880 = (p_term false false e)
in (soft_parens_with_nesting uu____10880))
end
| FStar_Parser_AST.Const (uu____10883) -> begin
(

let uu____10884 = (p_term false false e)
in (soft_parens_with_nesting uu____10884))
end
| FStar_Parser_AST.Op (uu____10887) -> begin
(

let uu____10894 = (p_term false false e)
in (soft_parens_with_nesting uu____10894))
end
| FStar_Parser_AST.Tvar (uu____10897) -> begin
(

let uu____10898 = (p_term false false e)
in (soft_parens_with_nesting uu____10898))
end
| FStar_Parser_AST.Var (uu____10901) -> begin
(

let uu____10902 = (p_term false false e)
in (soft_parens_with_nesting uu____10902))
end
| FStar_Parser_AST.Name (uu____10905) -> begin
(

let uu____10906 = (p_term false false e)
in (soft_parens_with_nesting uu____10906))
end
| FStar_Parser_AST.Construct (uu____10909) -> begin
(

let uu____10920 = (p_term false false e)
in (soft_parens_with_nesting uu____10920))
end
| FStar_Parser_AST.Abs (uu____10923) -> begin
(

let uu____10930 = (p_term false false e)
in (soft_parens_with_nesting uu____10930))
end
| FStar_Parser_AST.App (uu____10933) -> begin
(

let uu____10940 = (p_term false false e)
in (soft_parens_with_nesting uu____10940))
end
| FStar_Parser_AST.Let (uu____10943) -> begin
(

let uu____10964 = (p_term false false e)
in (soft_parens_with_nesting uu____10964))
end
| FStar_Parser_AST.LetOpen (uu____10967) -> begin
(

let uu____10972 = (p_term false false e)
in (soft_parens_with_nesting uu____10972))
end
| FStar_Parser_AST.Seq (uu____10975) -> begin
(

let uu____10980 = (p_term false false e)
in (soft_parens_with_nesting uu____10980))
end
| FStar_Parser_AST.Bind (uu____10983) -> begin
(

let uu____10990 = (p_term false false e)
in (soft_parens_with_nesting uu____10990))
end
| FStar_Parser_AST.If (uu____10993) -> begin
(

let uu____11000 = (p_term false false e)
in (soft_parens_with_nesting uu____11000))
end
| FStar_Parser_AST.Match (uu____11003) -> begin
(

let uu____11018 = (p_term false false e)
in (soft_parens_with_nesting uu____11018))
end
| FStar_Parser_AST.TryWith (uu____11021) -> begin
(

let uu____11036 = (p_term false false e)
in (soft_parens_with_nesting uu____11036))
end
| FStar_Parser_AST.Ascribed (uu____11039) -> begin
(

let uu____11048 = (p_term false false e)
in (soft_parens_with_nesting uu____11048))
end
| FStar_Parser_AST.Record (uu____11051) -> begin
(

let uu____11064 = (p_term false false e)
in (soft_parens_with_nesting uu____11064))
end
| FStar_Parser_AST.Project (uu____11067) -> begin
(

let uu____11072 = (p_term false false e)
in (soft_parens_with_nesting uu____11072))
end
| FStar_Parser_AST.Product (uu____11075) -> begin
(

let uu____11082 = (p_term false false e)
in (soft_parens_with_nesting uu____11082))
end
| FStar_Parser_AST.Sum (uu____11085) -> begin
(

let uu____11096 = (p_term false false e)
in (soft_parens_with_nesting uu____11096))
end
| FStar_Parser_AST.QForall (uu____11099) -> begin
(

let uu____11118 = (p_term false false e)
in (soft_parens_with_nesting uu____11118))
end
| FStar_Parser_AST.QExists (uu____11121) -> begin
(

let uu____11140 = (p_term false false e)
in (soft_parens_with_nesting uu____11140))
end
| FStar_Parser_AST.Refine (uu____11143) -> begin
(

let uu____11148 = (p_term false false e)
in (soft_parens_with_nesting uu____11148))
end
| FStar_Parser_AST.NamedTyp (uu____11151) -> begin
(

let uu____11156 = (p_term false false e)
in (soft_parens_with_nesting uu____11156))
end
| FStar_Parser_AST.Requires (uu____11159) -> begin
(

let uu____11167 = (p_term false false e)
in (soft_parens_with_nesting uu____11167))
end
| FStar_Parser_AST.Ensures (uu____11170) -> begin
(

let uu____11178 = (p_term false false e)
in (soft_parens_with_nesting uu____11178))
end
| FStar_Parser_AST.Attributes (uu____11181) -> begin
(

let uu____11184 = (p_term false false e)
in (soft_parens_with_nesting uu____11184))
end
| FStar_Parser_AST.Quote (uu____11187) -> begin
(

let uu____11192 = (p_term false false e)
in (soft_parens_with_nesting uu____11192))
end
| FStar_Parser_AST.VQuote (uu____11195) -> begin
(

let uu____11196 = (p_term false false e)
in (soft_parens_with_nesting uu____11196))
end
| FStar_Parser_AST.Antiquote (uu____11199) -> begin
(

let uu____11200 = (p_term false false e)
in (soft_parens_with_nesting uu____11200))
end
| FStar_Parser_AST.CalcProof (uu____11203) -> begin
(

let uu____11212 = (p_term false false e)
in (soft_parens_with_nesting uu____11212))
end))
and p_constant : FStar_Const.sconst  ->  FStar_Pprint.document = (fun uu___15_11215 -> (match (uu___15_11215) with
| FStar_Const.Const_effect -> begin
(str "Effect")
end
| FStar_Const.Const_unit -> begin
(str "()")
end
| FStar_Const.Const_bool (b) -> begin
(FStar_Pprint.doc_of_bool b)
end
| FStar_Const.Const_real (r) -> begin
(str (Prims.op_Hat r "R"))
end
| FStar_Const.Const_float (x) -> begin
(str (FStar_Util.string_of_float x))
end
| FStar_Const.Const_char (x) -> begin
(FStar_Pprint.doc_of_char x)
end
| FStar_Const.Const_string (s, uu____11227) -> begin
(

let uu____11230 = (str (FStar_String.escaped s))
in (FStar_Pprint.dquotes uu____11230))
end
| FStar_Const.Const_bytearray (bytes, uu____11232) -> begin
(

let uu____11237 = (

let uu____11238 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes uu____11238))
in (

let uu____11239 = (str "B")
in (FStar_Pprint.op_Hat_Hat uu____11237 uu____11239)))
end
| FStar_Const.Const_int (repr, sign_width_opt) -> begin
(

let signedness = (fun uu___13_11262 -> (match (uu___13_11262) with
| FStar_Const.Unsigned -> begin
(str "u")
end
| FStar_Const.Signed -> begin
FStar_Pprint.empty
end))
in (

let width = (fun uu___14_11269 -> (match (uu___14_11269) with
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

let ending = (default_or_map FStar_Pprint.empty (fun uu____11284 -> (match (uu____11284) with
| (s, w) -> begin
(

let uu____11291 = (signedness s)
in (

let uu____11292 = (width w)
in (FStar_Pprint.op_Hat_Hat uu____11291 uu____11292)))
end)) sign_width_opt)
in (

let uu____11293 = (str repr)
in (FStar_Pprint.op_Hat_Hat uu____11293 ending)))))
end
| FStar_Const.Const_range_of -> begin
(str "range_of")
end
| FStar_Const.Const_set_range_of -> begin
(str "set_range_of")
end
| FStar_Const.Const_range (r) -> begin
(

let uu____11297 = (FStar_Range.string_of_range r)
in (str uu____11297))
end
| FStar_Const.Const_reify -> begin
(str "reify")
end
| FStar_Const.Const_reflect (lid) -> begin
(

let uu____11301 = (p_quident lid)
in (

let uu____11302 = (

let uu____11303 = (

let uu____11304 = (str "reflect")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____11304))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____11303))
in (FStar_Pprint.op_Hat_Hat uu____11301 uu____11302)))
end))
and p_universe : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (

let uu____11307 = (str "u#")
in (

let uu____11309 = (p_atomicUniverse u)
in (FStar_Pprint.op_Hat_Hat uu____11307 uu____11309))))
and p_universeFrom : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (match (u.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____11311}, (u1)::(u2)::[]) -> begin
(

let uu____11317 = (

let uu____11318 = (p_universeFrom u1)
in (

let uu____11319 = (

let uu____11320 = (p_universeFrom u2)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____11320))
in (FStar_Pprint.op_Hat_Slash_Hat uu____11318 uu____11319)))
in (FStar_Pprint.group uu____11317))
end
| FStar_Parser_AST.App (uu____11321) -> begin
(

let uu____11328 = (head_and_args u)
in (match (uu____11328) with
| (head1, args) -> begin
(match (head1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Var (maybe_max_lid) when (FStar_Ident.lid_equals maybe_max_lid FStar_Parser_Const.max_lid) -> begin
(

let uu____11354 = (

let uu____11355 = (p_qlident FStar_Parser_Const.max_lid)
in (

let uu____11356 = (FStar_Pprint.separate_map FStar_Pprint.space (fun uu____11364 -> (match (uu____11364) with
| (u1, uu____11370) -> begin
(p_atomicUniverse u1)
end)) args)
in (op_Hat_Slash_Plus_Hat uu____11355 uu____11356)))
in (FStar_Pprint.group uu____11354))
end
| uu____11371 -> begin
(

let uu____11372 = (

let uu____11374 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" uu____11374))
in (failwith uu____11372))
end)
end))
end
| uu____11377 -> begin
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

let uu____11403 = (FStar_Ident.text_of_id id1)
in (str uu____11403))
end
| FStar_Parser_AST.Paren (u1) -> begin
(

let uu____11406 = (p_universeFrom u1)
in (soft_parens_with_nesting uu____11406))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____11407}, (uu____11408)::(uu____11409)::[]) -> begin
(

let uu____11413 = (p_universeFrom u)
in (soft_parens_with_nesting uu____11413))
end
| FStar_Parser_AST.App (uu____11414) -> begin
(

let uu____11421 = (p_universeFrom u)
in (soft_parens_with_nesting uu____11421))
end
| uu____11422 -> begin
(

let uu____11423 = (

let uu____11425 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" uu____11425))
in (failwith uu____11423))
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
| FStar_Parser_AST.Module (uu____11514, decls) -> begin
(

let uu____11520 = (FStar_All.pipe_right decls (FStar_List.map decl_to_document))
in (FStar_All.pipe_right uu____11520 (FStar_Pprint.separate FStar_Pprint.hardline)))
end
| FStar_Parser_AST.Interface (uu____11529, decls, uu____11531) -> begin
(

let uu____11538 = (FStar_All.pipe_right decls (FStar_List.map decl_to_document))
in (FStar_All.pipe_right uu____11538 (FStar_Pprint.separate FStar_Pprint.hardline)))
end)
in ((FStar_ST.op_Colon_Equals should_print_fs_typ_app false);
res;
));
))


let comments_to_document : (Prims.string * FStar_Range.range) Prims.list  ->  FStar_Pprint.document = (fun comments -> (FStar_Pprint.separate_map FStar_Pprint.hardline (fun uu____11598 -> (match (uu____11598) with
| (comment, range) -> begin
(str comment)
end)) comments))


let extract_decl_range : FStar_Parser_AST.decl  ->  decl_meta = (fun d -> (

let has_qs = (match (((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d))) with
| ((FStar_Parser_AST.Assumption)::[], FStar_Parser_AST.Assume (id1, uu____11620)) -> begin
false
end
| ([], uu____11624) -> begin
false
end
| uu____11628 -> begin
true
end)
in {r = d.FStar_Parser_AST.drange; has_qs = has_qs; has_attrs = (not ((FStar_List.isEmpty d.FStar_Parser_AST.attrs))); has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc); is_fsdoc = (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Fsdoc (uu____11638) -> begin
true
end
| uu____11640 -> begin
false
end)}))


let modul_with_comments_to_document : FStar_Parser_AST.modul  ->  (Prims.string * FStar_Range.range) Prims.list  ->  (FStar_Pprint.document * (Prims.string * FStar_Range.range) Prims.list) = (fun m comments -> (

let decls = (match (m) with
| FStar_Parser_AST.Module (uu____11683, decls) -> begin
decls
end
| FStar_Parser_AST.Interface (uu____11689, decls, uu____11691) -> begin
decls
end)
in ((FStar_ST.op_Colon_Equals should_print_fs_typ_app false);
(match (decls) with
| [] -> begin
((FStar_Pprint.empty), (comments))
end
| (d)::ds -> begin
(

let uu____11743 = (match (ds) with
| ({FStar_Parser_AST.d = FStar_Parser_AST.Pragma (FStar_Parser_AST.LightOff); FStar_Parser_AST.drange = uu____11756; FStar_Parser_AST.doc = uu____11757; FStar_Parser_AST.quals = uu____11758; FStar_Parser_AST.attrs = uu____11759})::uu____11760 -> begin
(

let d0 = (FStar_List.hd ds)
in (

let uu____11766 = (

let uu____11769 = (

let uu____11772 = (FStar_List.tl ds)
in (d)::uu____11772)
in (d0)::uu____11769)
in ((uu____11766), (d0.FStar_Parser_AST.drange))))
end
| uu____11777 -> begin
(((d)::ds), (d.FStar_Parser_AST.drange))
end)
in (match (uu____11743) with
| (decls1, first_range) -> begin
((FStar_ST.op_Colon_Equals comment_stack comments);
(

let initial_comment = (

let uu____11834 = (FStar_Range.start_of_range first_range)
in (place_comments_until_pos (Prims.parse_int "0") (Prims.parse_int "1") uu____11834 dummy_meta FStar_Pprint.empty false true))
in (

let doc1 = (separate_map_with_comments FStar_Pprint.empty FStar_Pprint.empty p_decl decls1 extract_decl_range)
in (

let comments1 = (FStar_ST.op_Bang comment_stack)
in ((FStar_ST.op_Colon_Equals comment_stack []);
(FStar_ST.op_Colon_Equals should_print_fs_typ_app false);
(

let uu____11943 = (FStar_Pprint.op_Hat_Hat initial_comment doc1)
in ((uu____11943), (comments1)));
))));
)
end))
end);
)))




