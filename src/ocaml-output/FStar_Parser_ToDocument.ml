
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

let uu____86 = (

let uu____87 = (FStar_ST.op_Bang should_unparen)
in (not (uu____87)))
in (match (uu____86) with
| true -> begin
t
end
| uu____98 -> begin
(match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t1) -> begin
(unparen t1)
end
| uu____100 -> begin
t
end)
end)))


let str : Prims.string  ->  FStar_Pprint.document = (fun s -> (FStar_Pprint.doc_of_string s))


let default_or_map : 'Auu____115 'Auu____116 . 'Auu____116  ->  ('Auu____115  ->  'Auu____116)  ->  'Auu____115 FStar_Pervasives_Native.option  ->  'Auu____116 = (fun n1 f x -> (match (x) with
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


let separate_break_map : 'Auu____185 . FStar_Pprint.document  ->  ('Auu____185  ->  FStar_Pprint.document)  ->  'Auu____185 Prims.list  ->  FStar_Pprint.document = (fun sep f l -> (

let uu____207 = (

let uu____208 = (

let uu____209 = (FStar_Pprint.op_Hat_Hat sep break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____209))
in (FStar_Pprint.separate_map uu____208 f l))
in (FStar_Pprint.group uu____207)))


let precede_break_separate_map : 'Auu____220 . FStar_Pprint.document  ->  FStar_Pprint.document  ->  ('Auu____220  ->  FStar_Pprint.document)  ->  'Auu____220 Prims.list  ->  FStar_Pprint.document = (fun prec sep f l -> (

let uu____246 = (

let uu____247 = (FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space)
in (

let uu____248 = (

let uu____249 = (FStar_List.hd l)
in (FStar_All.pipe_right uu____249 f))
in (FStar_Pprint.precede uu____247 uu____248)))
in (

let uu____250 = (

let uu____251 = (FStar_List.tl l)
in (FStar_Pprint.concat_map (fun x -> (

let uu____257 = (

let uu____258 = (

let uu____259 = (f x)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____259))
in (FStar_Pprint.op_Hat_Hat sep uu____258))
in (FStar_Pprint.op_Hat_Hat break1 uu____257))) uu____251))
in (FStar_Pprint.op_Hat_Hat uu____246 uu____250))))


let concat_break_map : 'Auu____266 . ('Auu____266  ->  FStar_Pprint.document)  ->  'Auu____266 Prims.list  ->  FStar_Pprint.document = (fun f l -> (

let uu____284 = (FStar_Pprint.concat_map (fun x -> (

let uu____288 = (f x)
in (FStar_Pprint.op_Hat_Hat uu____288 break1))) l)
in (FStar_Pprint.group uu____284)))


let parens_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lparen contents FStar_Pprint.rparen))


let soft_parens_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lparen contents FStar_Pprint.rparen))


let braces_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbrace contents FStar_Pprint.rbrace))


let soft_braces_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbrace contents FStar_Pprint.rbrace))


let brackets_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbracket contents FStar_Pprint.rbracket))


let soft_brackets_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbracket contents FStar_Pprint.rbracket))


let soft_begin_end_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (

let uu____317 = (str "begin")
in (

let uu____318 = (str "end")
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") uu____317 contents uu____318))))


let separate_map_or_flow : 'Auu____327 . FStar_Pprint.document  ->  ('Auu____327  ->  FStar_Pprint.document)  ->  'Auu____327 Prims.list  ->  FStar_Pprint.document = (fun sep f l -> (match (((FStar_List.length l) < (Prims.parse_int "10"))) with
| true -> begin
(FStar_Pprint.separate_map sep f l)
end
| uu____349 -> begin
(FStar_Pprint.flow_map sep f l)
end))


let soft_surround_separate_map : 'Auu____368 . Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  ('Auu____368  ->  FStar_Pprint.document)  ->  'Auu____368 Prims.list  ->  FStar_Pprint.document = (fun n1 b void_ opening sep closing f xs -> (match ((xs = [])) with
| true -> begin
void_
end
| uu____412 -> begin
(

let uu____413 = (FStar_Pprint.separate_map sep f xs)
in (FStar_Pprint.soft_surround n1 b opening uu____413 closing))
end))


let soft_surround_map_or_flow : 'Auu____432 . Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  FStar_Pprint.document  ->  ('Auu____432  ->  FStar_Pprint.document)  ->  'Auu____432 Prims.list  ->  FStar_Pprint.document = (fun n1 b void_ opening sep closing f xs -> (match ((xs = [])) with
| true -> begin
void_
end
| uu____476 -> begin
(

let uu____477 = (separate_map_or_flow sep f xs)
in (FStar_Pprint.soft_surround n1 b opening uu____477 closing))
end))


let doc_of_fsdoc : (Prims.string * (Prims.string * Prims.string) Prims.list)  ->  FStar_Pprint.document = (fun uu____491 -> (match (uu____491) with
| (comment, keywords) -> begin
(

let uu____516 = (

let uu____517 = (

let uu____520 = (str comment)
in (

let uu____521 = (

let uu____524 = (

let uu____527 = (FStar_Pprint.separate_map FStar_Pprint.comma (fun uu____536 -> (match (uu____536) with
| (k, v1) -> begin
(

let uu____543 = (

let uu____546 = (str k)
in (

let uu____547 = (

let uu____550 = (

let uu____553 = (str v1)
in (uu____553)::[])
in (FStar_Pprint.rarrow)::uu____550)
in (uu____546)::uu____547))
in (FStar_Pprint.concat uu____543))
end)) keywords)
in (uu____527)::[])
in (FStar_Pprint.space)::uu____524)
in (uu____520)::uu____521))
in (FStar_Pprint.concat uu____517))
in (FStar_Pprint.group uu____516))
end))


let is_unit : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____558 = (

let uu____559 = (unparen e)
in uu____559.FStar_Parser_AST.tm)
in (match (uu____558) with
| FStar_Parser_AST.Const (FStar_Const.Const_unit) -> begin
true
end
| uu____560 -> begin
false
end)))


let matches_var : FStar_Parser_AST.term  ->  FStar_Ident.ident  ->  Prims.bool = (fun t x -> (

let uu____569 = (

let uu____570 = (unparen t)
in uu____570.FStar_Parser_AST.tm)
in (match (uu____569) with
| FStar_Parser_AST.Var (y) -> begin
(x.FStar_Ident.idText = (FStar_Ident.text_of_lid y))
end
| uu____572 -> begin
false
end)))


let is_tuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Parser_Const.is_tuple_data_lid'


let is_dtuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Parser_Const.is_dtuple_data_lid'


let is_list_structure : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun cons_lid1 nil_lid1 -> (

let rec aux = (fun e -> (

let uu____594 = (

let uu____595 = (unparen e)
in uu____595.FStar_Parser_AST.tm)
in (match (uu____594) with
| FStar_Parser_AST.Construct (lid, []) -> begin
(FStar_Ident.lid_equals lid nil_lid1)
end
| FStar_Parser_AST.Construct (lid, (uu____608)::((e2, uu____610))::[]) -> begin
((FStar_Ident.lid_equals lid cons_lid1) && (aux e2))
end
| uu____633 -> begin
false
end)))
in aux))


let is_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Parser_Const.cons_lid FStar_Parser_Const.nil_lid)


let is_lex_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Parser_Const.lexcons_lid FStar_Parser_Const.lextop_lid)


let rec extract_from_list : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (

let uu____646 = (

let uu____647 = (unparen e)
in uu____647.FStar_Parser_AST.tm)
in (match (uu____646) with
| FStar_Parser_AST.Construct (uu____650, []) -> begin
[]
end
| FStar_Parser_AST.Construct (uu____661, ((e1, FStar_Parser_AST.Nothing))::((e2, FStar_Parser_AST.Nothing))::[]) -> begin
(

let uu____682 = (extract_from_list e2)
in (e1)::uu____682)
end
| uu____685 -> begin
(

let uu____686 = (

let uu____687 = (FStar_Parser_AST.term_to_string e)
in (FStar_Util.format1 "Not a list %s" uu____687))
in (failwith uu____686))
end)))


let is_array : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____694 = (

let uu____695 = (unparen e)
in uu____695.FStar_Parser_AST.tm)
in (match (uu____694) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (lid); FStar_Parser_AST.range = uu____697; FStar_Parser_AST.level = uu____698}, l, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) && (is_list l))
end
| uu____700 -> begin
false
end)))


let rec is_ref_set : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____705 = (

let uu____706 = (unparen e)
in uu____706.FStar_Parser_AST.tm)
in (match (uu____705) with
| FStar_Parser_AST.Var (maybe_empty_lid) -> begin
(FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty)
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_singleton_lid); FStar_Parser_AST.range = uu____709; FStar_Parser_AST.level = uu____710}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_addr_of_lid); FStar_Parser_AST.range = uu____712; FStar_Parser_AST.level = uu____713}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____715; FStar_Parser_AST.level = uu____716}, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals maybe_singleton_lid FStar_Parser_Const.set_singleton) && (FStar_Ident.lid_equals maybe_addr_of_lid FStar_Parser_Const.heap_addr_of_lid))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_union_lid); FStar_Parser_AST.range = uu____718; FStar_Parser_AST.level = uu____719}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____721; FStar_Parser_AST.level = uu____722}, e2, FStar_Parser_AST.Nothing) -> begin
(((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union) && (is_ref_set e1)) && (is_ref_set e2))
end
| uu____724 -> begin
false
end)))


let rec extract_from_ref_set : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (

let uu____731 = (

let uu____732 = (unparen e)
in uu____732.FStar_Parser_AST.tm)
in (match (uu____731) with
| FStar_Parser_AST.Var (uu____735) -> begin
[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (uu____736); FStar_Parser_AST.range = uu____737; FStar_Parser_AST.level = uu____738}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (uu____739); FStar_Parser_AST.range = uu____740; FStar_Parser_AST.level = uu____741}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____743; FStar_Parser_AST.level = uu____744}, FStar_Parser_AST.Nothing) -> begin
(e1)::[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (uu____745); FStar_Parser_AST.range = uu____746; FStar_Parser_AST.level = uu____747}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____749; FStar_Parser_AST.level = uu____750}, e2, FStar_Parser_AST.Nothing) -> begin
(

let uu____752 = (extract_from_ref_set e1)
in (

let uu____755 = (extract_from_ref_set e2)
in (FStar_List.append uu____752 uu____755)))
end
| uu____758 -> begin
(

let uu____759 = (

let uu____760 = (FStar_Parser_AST.term_to_string e)
in (FStar_Util.format1 "Not a ref set %s" uu____760))
in (failwith uu____759))
end)))


let is_general_application : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____767 = ((is_array e) || (is_ref_set e))
in (not (uu____767))))


let is_general_construction : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____772 = ((is_list e) || (is_lex_list e))
in (not (uu____772))))


let is_general_prefix_op : FStar_Ident.ident  ->  Prims.bool = (fun op -> (

let op_starting_char = (FStar_Util.char_at (FStar_Ident.text_of_id op) (Prims.parse_int "0"))
in (((op_starting_char = '!') || (op_starting_char = '?')) || ((op_starting_char = '~') && ((FStar_Ident.text_of_id op) <> "~")))))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun e -> (

let rec aux = (fun e1 acc -> (

let uu____821 = (

let uu____822 = (unparen e1)
in uu____822.FStar_Parser_AST.tm)
in (match (uu____821) with
| FStar_Parser_AST.App (head1, arg, imp) -> begin
(aux head1 ((((arg), (imp)))::acc))
end
| uu____840 -> begin
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
| uu____855 -> begin
false
end))


let uu___is_Right : associativity  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Right -> begin
true
end
| uu____860 -> begin
false
end))


let uu___is_NonAssoc : associativity  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NonAssoc -> begin
true
end
| uu____865 -> begin
false
end))


type token =
(FStar_Char.char, Prims.string) FStar_Util.either


type associativity_level =
(associativity * token Prims.list)


let token_to_string : (FStar_BaseTypes.char, Prims.string) FStar_Util.either  ->  Prims.string = (fun uu___93_883 -> (match (uu___93_883) with
| FStar_Util.Inl (c) -> begin
(Prims.strcat (FStar_Util.string_of_char c) ".*")
end
| FStar_Util.Inr (s) -> begin
s
end))


let matches_token : Prims.string  ->  (FStar_Char.char, Prims.string) FStar_Util.either  ->  Prims.bool = (fun s uu___94_901 -> (match (uu___94_901) with
| FStar_Util.Inl (c) -> begin
(

let uu____907 = (FStar_String.get s (Prims.parse_int "0"))
in (uu____907 = c))
end
| FStar_Util.Inr (s') -> begin
(s = s')
end))


let matches_level : 'Auu____915 . Prims.string  ->  ('Auu____915 * (FStar_Char.char, Prims.string) FStar_Util.either Prims.list)  ->  Prims.bool = (fun s uu____933 -> (match (uu____933) with
| (assoc_levels, tokens) -> begin
(

let uu____958 = (FStar_List.tryFind (matches_token s) tokens)
in (uu____958 <> FStar_Pervasives_Native.None))
end))


let opinfix4 : 'Auu____981 . Prims.unit  ->  (associativity * ('Auu____981, Prims.string) FStar_Util.either Prims.list) = (fun uu____992 -> ((Right), ((FStar_Util.Inr ("**"))::[])))


let opinfix3 : 'Auu____1009 . Prims.unit  ->  (associativity * (FStar_Char.char, 'Auu____1009) FStar_Util.either Prims.list) = (fun uu____1020 -> ((Left), ((FStar_Util.Inl ('*'))::(FStar_Util.Inl ('/'))::(FStar_Util.Inl ('%'))::[])))


let opinfix2 : 'Auu____1045 . Prims.unit  ->  (associativity * (FStar_Char.char, 'Auu____1045) FStar_Util.either Prims.list) = (fun uu____1056 -> ((Left), ((FStar_Util.Inl ('+'))::(FStar_Util.Inl ('-'))::[])))


let minus_lvl : 'Auu____1077 . Prims.unit  ->  (associativity * ('Auu____1077, Prims.string) FStar_Util.either Prims.list) = (fun uu____1088 -> ((Left), ((FStar_Util.Inr ("-"))::[])))


let opinfix1 : 'Auu____1105 . Prims.unit  ->  (associativity * (FStar_Char.char, 'Auu____1105) FStar_Util.either Prims.list) = (fun uu____1116 -> ((Right), ((FStar_Util.Inl ('@'))::(FStar_Util.Inl ('^'))::[])))


let pipe_right : 'Auu____1137 . Prims.unit  ->  (associativity * ('Auu____1137, Prims.string) FStar_Util.either Prims.list) = (fun uu____1148 -> ((Left), ((FStar_Util.Inr ("|>"))::[])))


let opinfix0d : 'Auu____1165 . Prims.unit  ->  (associativity * (FStar_Char.char, 'Auu____1165) FStar_Util.either Prims.list) = (fun uu____1176 -> ((Left), ((FStar_Util.Inl ('$'))::[])))


let opinfix0c : 'Auu____1193 . Prims.unit  ->  (associativity * (FStar_Char.char, 'Auu____1193) FStar_Util.either Prims.list) = (fun uu____1204 -> ((Left), ((FStar_Util.Inl ('='))::(FStar_Util.Inl ('<'))::(FStar_Util.Inl ('>'))::[])))


let equal : 'Auu____1229 . Prims.unit  ->  (associativity * ('Auu____1229, Prims.string) FStar_Util.either Prims.list) = (fun uu____1240 -> ((Left), ((FStar_Util.Inr ("="))::[])))


let opinfix0b : 'Auu____1257 . Prims.unit  ->  (associativity * (FStar_Char.char, 'Auu____1257) FStar_Util.either Prims.list) = (fun uu____1268 -> ((Left), ((FStar_Util.Inl ('&'))::[])))


let opinfix0a : 'Auu____1285 . Prims.unit  ->  (associativity * (FStar_Char.char, 'Auu____1285) FStar_Util.either Prims.list) = (fun uu____1296 -> ((Left), ((FStar_Util.Inl ('|'))::[])))


let colon_equals : 'Auu____1313 . Prims.unit  ->  (associativity * ('Auu____1313, Prims.string) FStar_Util.either Prims.list) = (fun uu____1324 -> ((NonAssoc), ((FStar_Util.Inr (":="))::[])))


let amp : 'Auu____1341 . Prims.unit  ->  (associativity * ('Auu____1341, Prims.string) FStar_Util.either Prims.list) = (fun uu____1352 -> ((Right), ((FStar_Util.Inr ("&"))::[])))


let colon_colon : 'Auu____1369 . Prims.unit  ->  (associativity * ('Auu____1369, Prims.string) FStar_Util.either Prims.list) = (fun uu____1380 -> ((Right), ((FStar_Util.Inr ("::"))::[])))


let level_associativity_spec : (associativity * (FStar_Char.char, Prims.string) FStar_Util.either Prims.list) Prims.list = ((opinfix4 ()))::((opinfix3 ()))::((opinfix2 ()))::((opinfix1 ()))::((pipe_right ()))::((opinfix0d ()))::((opinfix0c ()))::((opinfix0b ()))::((opinfix0a ()))::((colon_equals ()))::((amp ()))::((colon_colon ()))::[]


let level_table : ((Prims.int * Prims.int * Prims.int) * (FStar_Char.char, Prims.string) FStar_Util.either Prims.list) Prims.list = (

let levels_from_associativity = (fun l uu___95_1567 -> (match (uu___95_1567) with
| Left -> begin
((l), (l), ((l - (Prims.parse_int "1"))))
end
| Right -> begin
(((l - (Prims.parse_int "1"))), (l), (l))
end
| NonAssoc -> begin
((l), (l), (l))
end))
in (FStar_List.mapi (fun i uu____1605 -> (match (uu____1605) with
| (assoc1, tokens) -> begin
(((levels_from_associativity i assoc1)), (tokens))
end)) level_associativity_spec))


let assign_levels : associativity_level Prims.list  ->  Prims.string  ->  (Prims.int * Prims.int * Prims.int) = (fun token_associativity_spec s -> (

let uu____1682 = (FStar_List.tryFind (matches_level s) level_table)
in (match (uu____1682) with
| FStar_Pervasives_Native.Some (assoc_levels, uu____1730) -> begin
assoc_levels
end
| uu____1771 -> begin
(failwith (Prims.strcat "Unrecognized operator " s))
end)))


let max : Prims.int  ->  Prims.int  ->  Prims.int = (fun k1 k2 -> (match ((k1 > k2)) with
| true -> begin
k1
end
| uu____1804 -> begin
k2
end))


let max_level : 'Auu____1809 . ('Auu____1809 * (FStar_Char.char, Prims.string) FStar_Util.either Prims.list) Prims.list  ->  Prims.int = (fun l -> (

let find_level_and_max = (fun n1 level -> (

let uu____1865 = (FStar_List.tryFind (fun uu____1903 -> (match (uu____1903) with
| (uu____1920, tokens) -> begin
(tokens = (FStar_Pervasives_Native.snd level))
end)) level_table)
in (match (uu____1865) with
| FStar_Pervasives_Native.Some ((uu____1958, l1, uu____1960), uu____1961) -> begin
(max n1 l1)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____2012 = (

let uu____2013 = (

let uu____2014 = (FStar_List.map token_to_string (FStar_Pervasives_Native.snd level))
in (FStar_String.concat "," uu____2014))
in (FStar_Util.format1 "Undefined associativity level %s" uu____2013))
in (failwith uu____2012))
end)))
in (FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l)))


let levels : Prims.string  ->  (Prims.int * Prims.int * Prims.int) = (assign_levels level_associativity_spec)


let operatorInfix0ad12 : 'Auu____2048 . Prims.unit  ->  (associativity * (FStar_Char.char, 'Auu____2048) FStar_Util.either Prims.list) Prims.list = (fun uu____2061 -> ((opinfix0a ()))::((opinfix0b ()))::((opinfix0c ()))::((opinfix0d ()))::((opinfix1 ()))::((opinfix2 ()))::[])


let is_operatorInfix0ad12 : FStar_Ident.ident  ->  Prims.bool = (fun op -> (

let uu____2136 = (

let uu____2149 = (FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op))
in (FStar_List.tryFind uu____2149 (operatorInfix0ad12 ())))
in (uu____2136 <> FStar_Pervasives_Native.None)))


let is_operatorInfix34 : FStar_Ident.ident  ->  Prims.bool = (

let opinfix34 = ((opinfix3 ()))::((opinfix4 ()))::[]
in (fun op -> (

let uu____2253 = (

let uu____2266 = (FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op))
in (FStar_List.tryFind uu____2266 opinfix34))
in (uu____2253 <> FStar_Pervasives_Native.None))))


let handleable_args_length : FStar_Ident.ident  ->  Prims.int = (fun op -> (

let op_s = (FStar_Ident.text_of_id op)
in (

let uu____2328 = ((is_general_prefix_op op) || (FStar_List.mem op_s (("-")::("~")::[])))
in (match (uu____2328) with
| true -> begin
(Prims.parse_int "1")
end
| uu____2329 -> begin
(

let uu____2330 = (((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) || (FStar_List.mem op_s (("<==>")::("==>")::("\\/")::("/\\")::("=")::("|>")::(":=")::(".()")::(".[]")::[])))
in (match (uu____2330) with
| true -> begin
(Prims.parse_int "2")
end
| uu____2331 -> begin
(match ((FStar_List.mem op_s ((".()<-")::(".[]<-")::[]))) with
| true -> begin
(Prims.parse_int "3")
end
| uu____2332 -> begin
(Prims.parse_int "0")
end)
end))
end))))


let handleable_op : 'Auu____2339 . FStar_Ident.ident  ->  'Auu____2339 Prims.list  ->  Prims.bool = (fun op args -> (match ((FStar_List.length args)) with
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
| uu____2352 -> begin
false
end))


let comment_stack : (Prims.string * FStar_Range.range) Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let with_comment : 'Auu____2386 . ('Auu____2386  ->  FStar_Pprint.document)  ->  'Auu____2386  ->  FStar_Range.range  ->  FStar_Pprint.document = (fun printer tm tmrange -> (

let rec comments_before_pos = (fun acc print_pos lookahead_pos -> (

let uu____2418 = (FStar_ST.op_Bang comment_stack)
in (match (uu____2418) with
| [] -> begin
((acc), (false))
end
| ((comment, crange))::cs -> begin
(

let uu____2480 = (FStar_Range.range_before_pos crange print_pos)
in (match (uu____2480) with
| true -> begin
((FStar_ST.op_Colon_Equals comment_stack cs);
(

let uu____2520 = (

let uu____2521 = (

let uu____2522 = (str comment)
in (FStar_Pprint.op_Hat_Hat uu____2522 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat acc uu____2521))
in (comments_before_pos uu____2520 print_pos lookahead_pos));
)
end
| uu____2523 -> begin
(

let uu____2524 = (FStar_Range.range_before_pos crange lookahead_pos)
in ((acc), (uu____2524)))
end))
end)))
in (

let uu____2525 = (

let uu____2530 = (

let uu____2531 = (FStar_Range.start_of_range tmrange)
in (FStar_Range.end_of_line uu____2531))
in (

let uu____2532 = (FStar_Range.end_of_range tmrange)
in (comments_before_pos FStar_Pprint.empty uu____2530 uu____2532)))
in (match (uu____2525) with
| (comments, has_lookahead) -> begin
(

let printed_e = (printer tm)
in (

let comments1 = (match (has_lookahead) with
| true -> begin
(

let pos = (FStar_Range.end_of_range tmrange)
in (

let uu____2538 = (comments_before_pos comments pos pos)
in (FStar_Pervasives_Native.fst uu____2538)))
end
| uu____2543 -> begin
comments
end)
in (

let uu____2544 = (FStar_Pprint.op_Hat_Hat comments1 printed_e)
in (FStar_Pprint.group uu____2544))))
end))))


let rec place_comments_until_pos : Prims.int  ->  Prims.int  ->  FStar_Range.pos  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun k lbegin pos_end doc1 -> (

let uu____2561 = (FStar_ST.op_Bang comment_stack)
in (match (uu____2561) with
| ((comment, crange))::cs when (FStar_Range.range_before_pos crange pos_end) -> begin
((FStar_ST.op_Colon_Equals comment_stack cs);
(

let lnum = (

let uu____2651 = (

let uu____2652 = (

let uu____2653 = (FStar_Range.start_of_range crange)
in (FStar_Range.line_of_pos uu____2653))
in (uu____2652 - lbegin))
in (max k uu____2651))
in (

let doc2 = (

let uu____2655 = (

let uu____2656 = (FStar_Pprint.repeat lnum FStar_Pprint.hardline)
in (

let uu____2657 = (str comment)
in (FStar_Pprint.op_Hat_Hat uu____2656 uu____2657)))
in (FStar_Pprint.op_Hat_Hat doc1 uu____2655))
in (

let uu____2658 = (

let uu____2659 = (FStar_Range.end_of_range crange)
in (FStar_Range.line_of_pos uu____2659))
in (place_comments_until_pos (Prims.parse_int "1") uu____2658 pos_end doc2))));
)
end
| uu____2660 -> begin
(

let lnum = (

let uu____2668 = (

let uu____2669 = (FStar_Range.line_of_pos pos_end)
in (uu____2669 - lbegin))
in (max (Prims.parse_int "1") uu____2668))
in (

let uu____2670 = (FStar_Pprint.repeat lnum FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat doc1 uu____2670)))
end)))


let separate_map_with_comments : 'Auu____2683 . FStar_Pprint.document  ->  FStar_Pprint.document  ->  ('Auu____2683  ->  FStar_Pprint.document)  ->  'Auu____2683 Prims.list  ->  ('Auu____2683  ->  FStar_Range.range)  ->  FStar_Pprint.document = (fun prefix1 sep f xs extract_range -> (

let fold_fun = (fun uu____2731 x -> (match (uu____2731) with
| (last_line, doc1) -> begin
(

let r = (extract_range x)
in (

let doc2 = (

let uu____2745 = (FStar_Range.start_of_range r)
in (place_comments_until_pos (Prims.parse_int "1") last_line uu____2745 doc1))
in (

let uu____2746 = (

let uu____2747 = (FStar_Range.end_of_range r)
in (FStar_Range.line_of_pos uu____2747))
in (

let uu____2748 = (

let uu____2749 = (

let uu____2750 = (f x)
in (FStar_Pprint.op_Hat_Hat sep uu____2750))
in (FStar_Pprint.op_Hat_Hat doc2 uu____2749))
in ((uu____2746), (uu____2748))))))
end))
in (

let uu____2751 = (

let uu____2758 = (FStar_List.hd xs)
in (

let uu____2759 = (FStar_List.tl xs)
in ((uu____2758), (uu____2759))))
in (match (uu____2751) with
| (x, xs1) -> begin
(

let init1 = (

let uu____2775 = (

let uu____2776 = (

let uu____2777 = (extract_range x)
in (FStar_Range.end_of_range uu____2777))
in (FStar_Range.line_of_pos uu____2776))
in (

let uu____2778 = (

let uu____2779 = (f x)
in (FStar_Pprint.op_Hat_Hat prefix1 uu____2779))
in ((uu____2775), (uu____2778))))
in (

let uu____2780 = (FStar_List.fold_left fold_fun init1 xs1)
in (FStar_Pervasives_Native.snd uu____2780)))
end))))


let rec p_decl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (

let uu____3067 = (

let uu____3068 = (FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc)
in (

let uu____3069 = (

let uu____3070 = (p_attributes d.FStar_Parser_AST.attrs)
in (

let uu____3071 = (

let uu____3072 = (p_qualifiers d.FStar_Parser_AST.quals)
in (

let uu____3073 = (

let uu____3074 = (p_rawDecl d)
in (FStar_Pprint.op_Hat_Hat (match ((d.FStar_Parser_AST.quals = [])) with
| true -> begin
FStar_Pprint.empty
end
| uu____3075 -> begin
break1
end) uu____3074))
in (FStar_Pprint.op_Hat_Hat uu____3072 uu____3073)))
in (FStar_Pprint.op_Hat_Hat uu____3070 uu____3071)))
in (FStar_Pprint.op_Hat_Hat uu____3068 uu____3069)))
in (FStar_Pprint.group uu____3067)))
and p_attributes : FStar_Parser_AST.attributes_  ->  FStar_Pprint.document = (fun attrs -> (

let uu____3077 = (

let uu____3078 = (str "@")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3078))
in (

let uu____3079 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline)
in (soft_surround_map_or_flow (Prims.parse_int "0") (Prims.parse_int "2") FStar_Pprint.empty uu____3077 FStar_Pprint.space uu____3079 p_atomicTerm attrs))))
and p_fsdoc : FStar_Parser_AST.fsdoc  ->  FStar_Pprint.document = (fun uu____3080 -> (match (uu____3080) with
| (doc1, kwd_args) -> begin
(

let kwd_args_doc = (match (kwd_args) with
| [] -> begin
FStar_Pprint.empty
end
| kwd_args1 -> begin
(

let process_kwd_arg = (fun uu____3114 -> (match (uu____3114) with
| (kwd, arg) -> begin
(

let uu____3121 = (str "@")
in (

let uu____3122 = (

let uu____3123 = (str kwd)
in (

let uu____3124 = (

let uu____3125 = (str arg)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3125))
in (FStar_Pprint.op_Hat_Hat uu____3123 uu____3124)))
in (FStar_Pprint.op_Hat_Hat uu____3121 uu____3122)))
end))
in (

let uu____3126 = (

let uu____3127 = (FStar_Pprint.separate_map FStar_Pprint.hardline process_kwd_arg kwd_args1)
in (FStar_Pprint.op_Hat_Hat uu____3127 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3126)))
end)
in (

let uu____3132 = (

let uu____3133 = (

let uu____3134 = (

let uu____3135 = (

let uu____3136 = (str doc1)
in (

let uu____3137 = (

let uu____3138 = (

let uu____3139 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3139))
in (FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3138))
in (FStar_Pprint.op_Hat_Hat uu____3136 uu____3137)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3135))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3134))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3133))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3132)))
end))
and p_rawDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Open (uid) -> begin
(

let uu____3142 = (

let uu____3143 = (str "open")
in (

let uu____3144 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat uu____3143 uu____3144)))
in (FStar_Pprint.group uu____3142))
end
| FStar_Parser_AST.Include (uid) -> begin
(

let uu____3146 = (

let uu____3147 = (str "include")
in (

let uu____3148 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat uu____3147 uu____3148)))
in (FStar_Pprint.group uu____3146))
end
| FStar_Parser_AST.ModuleAbbrev (uid1, uid2) -> begin
(

let uu____3151 = (

let uu____3152 = (str "module")
in (

let uu____3153 = (

let uu____3154 = (

let uu____3155 = (p_uident uid1)
in (

let uu____3156 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____3155 uu____3156)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3154))
in (FStar_Pprint.op_Hat_Hat uu____3152 uu____3153)))
in (

let uu____3157 = (p_quident uid2)
in (op_Hat_Slash_Plus_Hat uu____3151 uu____3157)))
end
| FStar_Parser_AST.TopLevelModule (uid) -> begin
(

let uu____3159 = (

let uu____3160 = (str "module")
in (

let uu____3161 = (

let uu____3162 = (p_quident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3162))
in (FStar_Pprint.op_Hat_Hat uu____3160 uu____3161)))
in (FStar_Pprint.group uu____3159))
end
| FStar_Parser_AST.Tycon (true, ((FStar_Parser_AST.TyconAbbrev (uid, tpars, FStar_Pervasives_Native.None, t), FStar_Pervasives_Native.None))::[]) -> begin
(

let effect_prefix_doc = (

let uu____3195 = (str "effect")
in (

let uu____3196 = (

let uu____3197 = (p_uident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3197))
in (FStar_Pprint.op_Hat_Hat uu____3195 uu____3196)))
in (

let uu____3198 = (

let uu____3199 = (p_typars tpars)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") effect_prefix_doc uu____3199 FStar_Pprint.equals))
in (

let uu____3200 = (p_typ t)
in (op_Hat_Slash_Plus_Hat uu____3198 uu____3200))))
end
| FStar_Parser_AST.Tycon (false, tcdefs) -> begin
(

let uu____3218 = (str "type")
in (

let uu____3219 = (str "and")
in (precede_break_separate_map uu____3218 uu____3219 p_fsdocTypeDeclPairs tcdefs)))
end
| FStar_Parser_AST.TopLevelLet (q, lbs) -> begin
(

let let_doc = (

let uu____3241 = (str "let")
in (

let uu____3242 = (

let uu____3243 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat uu____3243 FStar_Pprint.space))
in (FStar_Pprint.op_Hat_Hat uu____3241 uu____3242)))
in (

let uu____3244 = (

let uu____3245 = (str "and")
in (FStar_Pprint.op_Hat_Hat uu____3245 FStar_Pprint.space))
in (separate_map_with_comments let_doc uu____3244 p_letbinding lbs (fun uu____3253 -> (match (uu____3253) with
| (p, t) -> begin
(FStar_Range.union_ranges p.FStar_Parser_AST.prange t.FStar_Parser_AST.range)
end)))))
end
| FStar_Parser_AST.Val (lid, t) -> begin
(

let uu____3262 = (

let uu____3263 = (str "val")
in (

let uu____3264 = (

let uu____3265 = (

let uu____3266 = (p_lident lid)
in (

let uu____3267 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat uu____3266 uu____3267)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3265))
in (FStar_Pprint.op_Hat_Hat uu____3263 uu____3264)))
in (

let uu____3268 = (p_typ t)
in (op_Hat_Slash_Plus_Hat uu____3262 uu____3268)))
end
| FStar_Parser_AST.Assume (id, t) -> begin
(

let decl_keyword = (

let uu____3272 = (

let uu____3273 = (FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_All.pipe_right uu____3273 FStar_Util.is_upper))
in (match (uu____3272) with
| true -> begin
FStar_Pprint.empty
end
| uu____3274 -> begin
(

let uu____3275 = (str "val")
in (FStar_Pprint.op_Hat_Hat uu____3275 FStar_Pprint.space))
end))
in (

let uu____3276 = (

let uu____3277 = (

let uu____3278 = (p_ident id)
in (

let uu____3279 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat uu____3278 uu____3279)))
in (FStar_Pprint.op_Hat_Hat decl_keyword uu____3277))
in (

let uu____3280 = (p_typ t)
in (op_Hat_Slash_Plus_Hat uu____3276 uu____3280))))
end
| FStar_Parser_AST.Exception (uid, t_opt) -> begin
(

let uu____3287 = (str "exception")
in (

let uu____3288 = (

let uu____3289 = (

let uu____3290 = (p_uident uid)
in (

let uu____3291 = (FStar_Pprint.optional (fun t -> (

let uu____3296 = (str "of")
in (

let uu____3297 = (p_typ t)
in (op_Hat_Slash_Plus_Hat uu____3296 uu____3297)))) t_opt)
in (FStar_Pprint.op_Hat_Hat uu____3290 uu____3291)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3289))
in (FStar_Pprint.op_Hat_Hat uu____3287 uu____3288)))
end
| FStar_Parser_AST.NewEffect (ne) -> begin
(

let uu____3299 = (str "new_effect")
in (

let uu____3300 = (

let uu____3301 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3301))
in (FStar_Pprint.op_Hat_Hat uu____3299 uu____3300)))
end
| FStar_Parser_AST.SubEffect (se) -> begin
(

let uu____3303 = (str "sub_effect")
in (

let uu____3304 = (

let uu____3305 = (p_subEffect se)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3305))
in (FStar_Pprint.op_Hat_Hat uu____3303 uu____3304)))
end
| FStar_Parser_AST.Pragma (p) -> begin
(p_pragma p)
end
| FStar_Parser_AST.Fsdoc (doc1) -> begin
(

let uu____3308 = (p_fsdoc doc1)
in (FStar_Pprint.op_Hat_Hat uu____3308 FStar_Pprint.hardline))
end
| FStar_Parser_AST.Main (uu____3309) -> begin
(failwith "*Main declaration* : Is that really still in use ??")
end
| FStar_Parser_AST.Tycon (true, uu____3310) -> begin
(failwith "Effect abbreviation is expected to be defined by an abbreviation")
end))
and p_pragma : FStar_Parser_AST.pragma  ->  FStar_Pprint.document = (fun uu___96_3327 -> (match (uu___96_3327) with
| FStar_Parser_AST.SetOptions (s) -> begin
(

let uu____3329 = (str "#set-options")
in (

let uu____3330 = (

let uu____3331 = (

let uu____3332 = (str s)
in (FStar_Pprint.dquotes uu____3332))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3331))
in (FStar_Pprint.op_Hat_Hat uu____3329 uu____3330)))
end
| FStar_Parser_AST.ResetOptions (s_opt) -> begin
(

let uu____3336 = (str "#reset-options")
in (

let uu____3337 = (FStar_Pprint.optional (fun s -> (

let uu____3341 = (

let uu____3342 = (str s)
in (FStar_Pprint.dquotes uu____3342))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3341))) s_opt)
in (FStar_Pprint.op_Hat_Hat uu____3336 uu____3337)))
end
| FStar_Parser_AST.LightOff -> begin
((FStar_ST.op_Colon_Equals should_print_fs_typ_app true);
(str "#light \"off\"");
)
end))
and p_typars : FStar_Parser_AST.binder Prims.list  ->  FStar_Pprint.document = (fun bs -> (p_binders true bs))
and p_fsdocTypeDeclPairs : (FStar_Parser_AST.tycon * FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option)  ->  FStar_Pprint.document = (fun uu____3357 -> (match (uu____3357) with
| (typedecl, fsdoc_opt) -> begin
(

let uu____3370 = (FStar_Pprint.optional p_fsdoc fsdoc_opt)
in (

let uu____3371 = (p_typeDecl typedecl)
in (FStar_Pprint.op_Hat_Hat uu____3370 uu____3371)))
end))
and p_typeDecl : FStar_Parser_AST.tycon  ->  FStar_Pprint.document = (fun uu___97_3372 -> (match (uu___97_3372) with
| FStar_Parser_AST.TyconAbstract (lid, bs, typ_opt) -> begin
(

let empty' = (fun uu____3387 -> FStar_Pprint.empty)
in (p_typeDeclPrefix lid bs typ_opt empty'))
end
| FStar_Parser_AST.TyconAbbrev (lid, bs, typ_opt, t) -> begin
(

let f = (fun uu____3403 -> (

let uu____3404 = (p_typ t)
in (prefix2 FStar_Pprint.equals uu____3404)))
in (p_typeDeclPrefix lid bs typ_opt f))
end
| FStar_Parser_AST.TyconRecord (lid, bs, typ_opt, record_field_decls) -> begin
(

let p_recordFieldAndComments = (fun uu____3448 -> (match (uu____3448) with
| (lid1, t, doc_opt) -> begin
(

let uu____3464 = (FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range)
in (with_comment p_recordFieldDecl ((lid1), (t), (doc_opt)) uu____3464))
end))
in (

let p_fields = (fun uu____3478 -> (

let uu____3479 = (

let uu____3480 = (

let uu____3481 = (

let uu____3482 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (FStar_Pprint.separate_map uu____3482 p_recordFieldAndComments record_field_decls))
in (braces_with_nesting uu____3481))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3480))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____3479)))
in (p_typeDeclPrefix lid bs typ_opt p_fields)))
end
| FStar_Parser_AST.TyconVariant (lid, bs, typ_opt, ct_decls) -> begin
(

let p_constructorBranchAndComments = (fun uu____3546 -> (match (uu____3546) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let range = (

let uu____3572 = (

let uu____3573 = (FStar_Util.map_opt t_opt (fun t -> t.FStar_Parser_AST.range))
in (FStar_Util.dflt uid.FStar_Ident.idRange uu____3573))
in (FStar_Range.extend_to_end_of_line uu____3572))
in (

let p_constructorBranch = (fun decl -> (

let uu____3606 = (

let uu____3607 = (

let uu____3608 = (p_constructorDecl decl)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3608))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____3607))
in (FStar_Pprint.group uu____3606)))
in (with_comment p_constructorBranch ((uid), (t_opt), (doc_opt), (use_of)) range)))
end))
in (

let datacon_doc = (fun uu____3628 -> (

let uu____3629 = (FStar_Pprint.separate_map break1 p_constructorBranchAndComments ct_decls)
in (FStar_Pprint.group uu____3629)))
in (p_typeDeclPrefix lid bs typ_opt (fun uu____3644 -> (

let uu____3645 = (datacon_doc ())
in (prefix2 FStar_Pprint.equals uu____3645))))))
end))
and p_typeDeclPrefix : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.knd FStar_Pervasives_Native.option  ->  (Prims.unit  ->  FStar_Pprint.document)  ->  FStar_Pprint.document = (fun lid bs typ_opt cont -> (match (((bs = []) && (typ_opt = FStar_Pervasives_Native.None))) with
| true -> begin
(

let uu____3660 = (p_ident lid)
in (

let uu____3661 = (

let uu____3662 = (cont ())
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3662))
in (FStar_Pprint.op_Hat_Hat uu____3660 uu____3661)))
end
| uu____3663 -> begin
(

let binders_doc = (

let uu____3665 = (p_typars bs)
in (

let uu____3666 = (FStar_Pprint.optional (fun t -> (

let uu____3670 = (

let uu____3671 = (

let uu____3672 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3672))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3671))
in (FStar_Pprint.op_Hat_Hat break1 uu____3670))) typ_opt)
in (FStar_Pprint.op_Hat_Hat uu____3665 uu____3666)))
in (

let uu____3673 = (p_ident lid)
in (

let uu____3674 = (cont ())
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____3673 binders_doc uu____3674))))
end))
and p_recordFieldDecl : (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option)  ->  FStar_Pprint.document = (fun uu____3675 -> (match (uu____3675) with
| (lid, t, doc_opt) -> begin
(

let uu____3691 = (

let uu____3692 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (

let uu____3693 = (

let uu____3694 = (p_lident lid)
in (

let uu____3695 = (

let uu____3696 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3696))
in (FStar_Pprint.op_Hat_Hat uu____3694 uu____3695)))
in (FStar_Pprint.op_Hat_Hat uu____3692 uu____3693)))
in (FStar_Pprint.group uu____3691))
end))
and p_constructorDecl : (FStar_Ident.ident * FStar_Parser_AST.term FStar_Pervasives_Native.option * FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option * Prims.bool)  ->  FStar_Pprint.document = (fun uu____3697 -> (match (uu____3697) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let sep = (match (use_of) with
| true -> begin
(str "of")
end
| uu____3723 -> begin
FStar_Pprint.colon
end)
in (

let uid_doc = (p_uident uid)
in (

let uu____3725 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (

let uu____3726 = (

let uu____3727 = (FStar_Pprint.break_ (Prims.parse_int "0"))
in (

let uu____3728 = (default_or_map uid_doc (fun t -> (

let uu____3733 = (

let uu____3734 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep)
in (FStar_Pprint.op_Hat_Hat uid_doc uu____3734))
in (

let uu____3735 = (p_typ t)
in (op_Hat_Slash_Plus_Hat uu____3733 uu____3735)))) t_opt)
in (FStar_Pprint.op_Hat_Hat uu____3727 uu____3728)))
in (FStar_Pprint.op_Hat_Hat uu____3725 uu____3726)))))
end))
and p_letbinding : (FStar_Parser_AST.pattern * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun uu____3736 -> (match (uu____3736) with
| (pat, e) -> begin
(

let pat_doc = (

let uu____3744 = (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat1, t) -> begin
(

let uu____3755 = (

let uu____3756 = (

let uu____3757 = (

let uu____3758 = (

let uu____3759 = (p_tmArrow p_tmNoEq t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3759))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3758))
in (FStar_Pprint.group uu____3757))
in (FStar_Pprint.op_Hat_Hat break1 uu____3756))
in ((pat1), (uu____3755)))
end
| uu____3760 -> begin
((pat), (FStar_Pprint.empty))
end)
in (match (uu____3744) with
| (pat1, ascr_doc) -> begin
(match (pat1.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____3764); FStar_Parser_AST.prange = uu____3765}, pats) -> begin
(

let uu____3775 = (p_lident x)
in (

let uu____3776 = (

let uu____3777 = (separate_map_or_flow break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Hat uu____3777 ascr_doc))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____3775 uu____3776 FStar_Pprint.equals)))
end
| uu____3778 -> begin
(

let uu____3779 = (

let uu____3780 = (p_tuplePattern pat1)
in (

let uu____3781 = (FStar_Pprint.op_Hat_Slash_Hat ascr_doc FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____3780 uu____3781)))
in (FStar_Pprint.group uu____3779))
end)
end))
in (

let uu____3782 = (p_term e)
in (prefix2 pat_doc uu____3782)))
end))
and p_newEffect : FStar_Parser_AST.effect_decl  ->  FStar_Pprint.document = (fun uu___98_3783 -> (match (uu___98_3783) with
| FStar_Parser_AST.RedefineEffect (lid, bs, t) -> begin
(p_effectRedefinition lid bs t)
end
| FStar_Parser_AST.DefineEffect (lid, bs, t, eff_decls) -> begin
(p_effectDefinition lid bs t eff_decls)
end))
and p_effectRedefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun uid bs t -> (

let uu____3808 = (p_uident uid)
in (

let uu____3809 = (p_binders true bs)
in (

let uu____3810 = (

let uu____3811 = (p_simpleTerm t)
in (prefix2 FStar_Pprint.equals uu____3811))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____3808 uu____3809 uu____3810)))))
and p_effectDefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun uid bs t eff_decls -> (

let uu____3820 = (

let uu____3821 = (

let uu____3822 = (

let uu____3823 = (p_uident uid)
in (

let uu____3824 = (p_binders true bs)
in (

let uu____3825 = (

let uu____3826 = (p_typ t)
in (prefix2 FStar_Pprint.colon uu____3826))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____3823 uu____3824 uu____3825))))
in (FStar_Pprint.group uu____3822))
in (

let uu____3827 = (

let uu____3828 = (str "with")
in (

let uu____3829 = (separate_break_map FStar_Pprint.semi p_effectDecl eff_decls)
in (prefix2 uu____3828 uu____3829)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____3821 uu____3827)))
in (braces_with_nesting uu____3820)))
and p_effectDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (false, ((FStar_Parser_AST.TyconAbbrev (lid, [], FStar_Pervasives_Native.None, e), FStar_Pervasives_Native.None))::[]) -> begin
(

let uu____3859 = (

let uu____3860 = (p_lident lid)
in (

let uu____3861 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____3860 uu____3861)))
in (

let uu____3862 = (p_simpleTerm e)
in (prefix2 uu____3859 uu____3862)))
end
| uu____3863 -> begin
(

let uu____3864 = (

let uu____3865 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "Not a declaration of an effect member... or at least I hope so : %s" uu____3865))
in (failwith uu____3864))
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

let p_lift = (fun uu____3920 -> (match (uu____3920) with
| (kwd, t) -> begin
(

let uu____3927 = (

let uu____3928 = (str kwd)
in (

let uu____3929 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat uu____3928 uu____3929)))
in (

let uu____3930 = (p_simpleTerm t)
in (prefix2 uu____3927 uu____3930)))
end))
in (separate_break_map FStar_Pprint.semi p_lift lifts)))
in (

let uu____3935 = (

let uu____3936 = (

let uu____3937 = (p_quident lift.FStar_Parser_AST.msource)
in (

let uu____3938 = (

let uu____3939 = (str "~>")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3939))
in (FStar_Pprint.op_Hat_Hat uu____3937 uu____3938)))
in (

let uu____3940 = (p_quident lift.FStar_Parser_AST.mdest)
in (prefix2 uu____3936 uu____3940)))
in (

let uu____3941 = (

let uu____3942 = (braces_with_nesting lift_op_doc)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3942))
in (FStar_Pprint.op_Hat_Hat uu____3935 uu____3941)))))
and p_qualifier : FStar_Parser_AST.qualifier  ->  FStar_Pprint.document = (fun uu___99_3943 -> (match (uu___99_3943) with
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

let uu____3945 = (FStar_Pprint.separate_map break1 p_qualifier qs)
in (FStar_Pprint.group uu____3945)))
and p_letqualifier : FStar_Parser_AST.let_qualifier  ->  FStar_Pprint.document = (fun uu___100_3946 -> (match (uu___100_3946) with
| FStar_Parser_AST.Rec -> begin
(

let uu____3947 = (str "rec")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3947))
end
| FStar_Parser_AST.Mutable -> begin
(

let uu____3948 = (str "mutable")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3948))
end
| FStar_Parser_AST.NoLetQualifier -> begin
FStar_Pprint.empty
end))
and p_aqual : FStar_Parser_AST.arg_qualifier  ->  FStar_Pprint.document = (fun uu___101_3949 -> (match (uu___101_3949) with
| FStar_Parser_AST.Implicit -> begin
(str "#")
end
| FStar_Parser_AST.Equality -> begin
(str "$")
end))
and p_disjunctivePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr (pats) -> begin
(

let uu____3954 = (

let uu____3955 = (

let uu____3956 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space)
in (FStar_Pprint.op_Hat_Hat break1 uu____3956))
in (FStar_Pprint.separate_map uu____3955 p_tuplePattern pats))
in (FStar_Pprint.group uu____3954))
end
| uu____3957 -> begin
(p_tuplePattern p)
end))
and p_tuplePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTuple (pats, false) -> begin
(

let uu____3964 = (

let uu____3965 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map uu____3965 p_constructorPattern pats))
in (FStar_Pprint.group uu____3964))
end
| uu____3966 -> begin
(p_constructorPattern p)
end))
and p_constructorPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (maybe_cons_lid); FStar_Parser_AST.prange = uu____3969}, (hd1)::(tl1)::[]) when (FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid) -> begin
(

let uu____3974 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon)
in (

let uu____3975 = (p_constructorPattern hd1)
in (

let uu____3976 = (p_constructorPattern tl1)
in (infix0 uu____3974 uu____3975 uu____3976))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (uid); FStar_Parser_AST.prange = uu____3978}, pats) -> begin
(

let uu____3984 = (p_quident uid)
in (

let uu____3985 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (prefix2 uu____3984 uu____3985)))
end
| uu____3986 -> begin
(p_atomicPattern p)
end))
and p_atomicPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, t) -> begin
(

let uu____3990 = (

let uu____3995 = (

let uu____3996 = (unparen t)
in uu____3996.FStar_Parser_AST.tm)
in ((pat.FStar_Parser_AST.pat), (uu____3995)))
in (match (uu____3990) with
| (FStar_Parser_AST.PatVar (lid, aqual), FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t1); FStar_Parser_AST.brange = uu____4001; FStar_Parser_AST.blevel = uu____4002; FStar_Parser_AST.aqual = uu____4003}, phi)) when (lid.FStar_Ident.idText = lid'.FStar_Ident.idText) -> begin
(

let uu____4009 = (

let uu____4010 = (p_ident lid)
in (p_refinement aqual uu____4010 t1 phi))
in (soft_parens_with_nesting uu____4009))
end
| (FStar_Parser_AST.PatWild, FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t1); FStar_Parser_AST.brange = uu____4012; FStar_Parser_AST.blevel = uu____4013; FStar_Parser_AST.aqual = uu____4014}, phi)) -> begin
(

let uu____4016 = (p_refinement FStar_Pervasives_Native.None FStar_Pprint.underscore t1 phi)
in (soft_parens_with_nesting uu____4016))
end
| uu____4017 -> begin
(

let uu____4022 = (

let uu____4023 = (p_tuplePattern pat)
in (

let uu____4024 = (

let uu____4025 = (FStar_Pprint.break_ (Prims.parse_int "0"))
in (

let uu____4026 = (

let uu____4027 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4027))
in (FStar_Pprint.op_Hat_Hat uu____4025 uu____4026)))
in (FStar_Pprint.op_Hat_Hat uu____4023 uu____4024)))
in (soft_parens_with_nesting uu____4022))
end))
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let uu____4031 = (separate_break_map FStar_Pprint.semi p_tuplePattern pats)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket uu____4031 FStar_Pprint.rbracket))
end
| FStar_Parser_AST.PatRecord (pats) -> begin
(

let p_recordFieldPat = (fun uu____4046 -> (match (uu____4046) with
| (lid, pat) -> begin
(

let uu____4053 = (p_qlident lid)
in (

let uu____4054 = (p_tuplePattern pat)
in (infix2 FStar_Pprint.equals uu____4053 uu____4054)))
end))
in (

let uu____4055 = (separate_break_map FStar_Pprint.semi p_recordFieldPat pats)
in (soft_braces_with_nesting uu____4055)))
end
| FStar_Parser_AST.PatTuple (pats, true) -> begin
(

let uu____4065 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (

let uu____4066 = (separate_break_map FStar_Pprint.comma p_constructorPattern pats)
in (

let uu____4067 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____4065 uu____4066 uu____4067))))
end
| FStar_Parser_AST.PatTvar (tv, arg_qualifier_opt) -> begin
(p_tvar tv)
end
| FStar_Parser_AST.PatOp (op) -> begin
(

let uu____4078 = (

let uu____4079 = (

let uu____4080 = (str (FStar_Ident.text_of_id op))
in (

let uu____4081 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat uu____4080 uu____4081)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4079))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4078))
end
| FStar_Parser_AST.PatWild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.PatConst (c) -> begin
(p_constant c)
end
| FStar_Parser_AST.PatVar (lid, aqual) -> begin
(

let uu____4089 = (FStar_Pprint.optional p_aqual aqual)
in (

let uu____4090 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat uu____4089 uu____4090)))
end
| FStar_Parser_AST.PatName (uid) -> begin
(p_quident uid)
end
| FStar_Parser_AST.PatOr (uu____4092) -> begin
(failwith "Inner or pattern !")
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (uu____4095); FStar_Parser_AST.prange = uu____4096}, uu____4097) -> begin
(

let uu____4102 = (p_tuplePattern p)
in (soft_parens_with_nesting uu____4102))
end
| FStar_Parser_AST.PatTuple (uu____4103, false) -> begin
(

let uu____4108 = (p_tuplePattern p)
in (soft_parens_with_nesting uu____4108))
end
| uu____4109 -> begin
(

let uu____4110 = (

let uu____4111 = (FStar_Parser_AST.pat_to_string p)
in (FStar_Util.format1 "Invalid pattern %s" uu____4111))
in (failwith uu____4110))
end))
and p_binder : Prims.bool  ->  FStar_Parser_AST.binder  ->  FStar_Pprint.document = (fun is_atomic b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (lid) -> begin
(

let uu____4115 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (

let uu____4116 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat uu____4115 uu____4116)))
end
| FStar_Parser_AST.TVariable (lid) -> begin
(p_lident lid)
end
| FStar_Parser_AST.Annotated (lid, t) -> begin
(

let doc1 = (

let uu____4121 = (

let uu____4122 = (unparen t)
in uu____4122.FStar_Parser_AST.tm)
in (match (uu____4121) with
| FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t1); FStar_Parser_AST.brange = uu____4125; FStar_Parser_AST.blevel = uu____4126; FStar_Parser_AST.aqual = uu____4127}, phi) when (lid.FStar_Ident.idText = lid'.FStar_Ident.idText) -> begin
(

let uu____4129 = (p_ident lid)
in (p_refinement b.FStar_Parser_AST.aqual uu____4129 t1 phi))
end
| uu____4130 -> begin
(

let uu____4131 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (

let uu____4132 = (

let uu____4133 = (p_lident lid)
in (

let uu____4134 = (

let uu____4135 = (

let uu____4136 = (FStar_Pprint.break_ (Prims.parse_int "0"))
in (

let uu____4137 = (p_tmFormula t)
in (FStar_Pprint.op_Hat_Hat uu____4136 uu____4137)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4135))
in (FStar_Pprint.op_Hat_Hat uu____4133 uu____4134)))
in (FStar_Pprint.op_Hat_Hat uu____4131 uu____4132)))
end))
in (match (is_atomic) with
| true -> begin
(

let uu____4138 = (

let uu____4139 = (FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4139))
in (FStar_Pprint.group uu____4138))
end
| uu____4140 -> begin
(FStar_Pprint.group doc1)
end))
end
| FStar_Parser_AST.TAnnotated (uu____4141) -> begin
(failwith "Is this still used ?")
end
| FStar_Parser_AST.NoName (t) -> begin
(

let uu____4147 = (

let uu____4148 = (unparen t)
in uu____4148.FStar_Parser_AST.tm)
in (match (uu____4147) with
| FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t1); FStar_Parser_AST.brange = uu____4150; FStar_Parser_AST.blevel = uu____4151; FStar_Parser_AST.aqual = uu____4152}, phi) -> begin
(match (is_atomic) with
| true -> begin
(

let uu____4154 = (

let uu____4155 = (

let uu____4156 = (p_refinement b.FStar_Parser_AST.aqual FStar_Pprint.underscore t1 phi)
in (FStar_Pprint.op_Hat_Hat uu____4156 FStar_Pprint.rparen))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4155))
in (FStar_Pprint.group uu____4154))
end
| uu____4157 -> begin
(

let uu____4158 = (p_refinement b.FStar_Parser_AST.aqual FStar_Pprint.underscore t1 phi)
in (FStar_Pprint.group uu____4158))
end)
end
| uu____4159 -> begin
(match (is_atomic) with
| true -> begin
(p_atomicTerm t)
end
| uu____4160 -> begin
(p_appTerm t)
end)
end))
end))
and p_refinement : FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Pprint.document  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun aqual_opt binder t phi -> (

let uu____4167 = (FStar_Pprint.optional p_aqual aqual_opt)
in (

let uu____4168 = (

let uu____4169 = (

let uu____4170 = (

let uu____4171 = (p_appTerm t)
in (

let uu____4172 = (

let uu____4173 = (p_noSeqTerm phi)
in (soft_braces_with_nesting uu____4173))
in (FStar_Pprint.op_Hat_Hat uu____4171 uu____4172)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4170))
in (FStar_Pprint.op_Hat_Hat binder uu____4169))
in (FStar_Pprint.op_Hat_Hat uu____4167 uu____4168))))
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
| uu____4185 -> begin
(p_lident id)
end))
and p_term : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____4187 = (

let uu____4188 = (unparen e)
in uu____4188.FStar_Parser_AST.tm)
in (match (uu____4187) with
| FStar_Parser_AST.Seq (e1, e2) -> begin
(

let uu____4191 = (

let uu____4192 = (

let uu____4193 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat uu____4193 FStar_Pprint.semi))
in (FStar_Pprint.group uu____4192))
in (

let uu____4194 = (p_term e2)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4191 uu____4194)))
end
| FStar_Parser_AST.Bind (x, e1, e2) -> begin
(

let uu____4198 = (

let uu____4199 = (

let uu____4200 = (

let uu____4201 = (p_lident x)
in (

let uu____4202 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.long_left_arrow)
in (FStar_Pprint.op_Hat_Hat uu____4201 uu____4202)))
in (

let uu____4203 = (

let uu____4204 = (p_noSeqTerm e1)
in (

let uu____4205 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.semi)
in (FStar_Pprint.op_Hat_Hat uu____4204 uu____4205)))
in (op_Hat_Slash_Plus_Hat uu____4200 uu____4203)))
in (FStar_Pprint.group uu____4199))
in (

let uu____4206 = (p_term e2)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4198 uu____4206)))
end
| uu____4207 -> begin
(

let uu____4208 = (p_noSeqTerm e)
in (FStar_Pprint.group uu____4208))
end)))
and p_noSeqTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_noSeqTerm' e e.FStar_Parser_AST.range))
and p_noSeqTerm' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____4211 = (

let uu____4212 = (unparen e)
in uu____4212.FStar_Parser_AST.tm)
in (match (uu____4211) with
| FStar_Parser_AST.Ascribed (e1, t, FStar_Pervasives_Native.None) -> begin
(

let uu____4217 = (

let uu____4218 = (p_tmIff e1)
in (

let uu____4219 = (

let uu____4220 = (

let uu____4221 = (p_typ t)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4221))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4220))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4218 uu____4219)))
in (FStar_Pprint.group uu____4217))
end
| FStar_Parser_AST.Ascribed (e1, t, FStar_Pervasives_Native.Some (tac)) -> begin
(

let uu____4227 = (

let uu____4228 = (p_tmIff e1)
in (

let uu____4229 = (

let uu____4230 = (

let uu____4231 = (

let uu____4232 = (p_typ t)
in (

let uu____4233 = (

let uu____4234 = (str "by")
in (

let uu____4235 = (p_typ tac)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4234 uu____4235)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4232 uu____4233)))
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4231))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4230))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4228 uu____4229)))
in (FStar_Pprint.group uu____4227))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = ".()<-"; FStar_Ident.idRange = uu____4236}, (e1)::(e2)::(e3)::[]) -> begin
(

let uu____4242 = (

let uu____4243 = (

let uu____4244 = (

let uu____4245 = (p_atomicTermNotQUident e1)
in (

let uu____4246 = (

let uu____4247 = (

let uu____4248 = (

let uu____4249 = (p_term e2)
in (soft_parens_with_nesting uu____4249))
in (

let uu____4250 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat uu____4248 uu____4250)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4247))
in (FStar_Pprint.op_Hat_Hat uu____4245 uu____4246)))
in (FStar_Pprint.group uu____4244))
in (

let uu____4251 = (

let uu____4252 = (p_noSeqTerm e3)
in (jump2 uu____4252))
in (FStar_Pprint.op_Hat_Hat uu____4243 uu____4251)))
in (FStar_Pprint.group uu____4242))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = ".[]<-"; FStar_Ident.idRange = uu____4253}, (e1)::(e2)::(e3)::[]) -> begin
(

let uu____4259 = (

let uu____4260 = (

let uu____4261 = (

let uu____4262 = (p_atomicTermNotQUident e1)
in (

let uu____4263 = (

let uu____4264 = (

let uu____4265 = (

let uu____4266 = (p_term e2)
in (soft_brackets_with_nesting uu____4266))
in (

let uu____4267 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat uu____4265 uu____4267)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4264))
in (FStar_Pprint.op_Hat_Hat uu____4262 uu____4263)))
in (FStar_Pprint.group uu____4261))
in (

let uu____4268 = (

let uu____4269 = (p_noSeqTerm e3)
in (jump2 uu____4269))
in (FStar_Pprint.op_Hat_Hat uu____4260 uu____4268)))
in (FStar_Pprint.group uu____4259))
end
| FStar_Parser_AST.Requires (e1, wtf) -> begin
(

let uu____4279 = (

let uu____4280 = (str "requires")
in (

let uu____4281 = (p_typ e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4280 uu____4281)))
in (FStar_Pprint.group uu____4279))
end
| FStar_Parser_AST.Ensures (e1, wtf) -> begin
(

let uu____4291 = (

let uu____4292 = (str "ensures")
in (

let uu____4293 = (p_typ e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4292 uu____4293)))
in (FStar_Pprint.group uu____4291))
end
| FStar_Parser_AST.Attributes (es) -> begin
(

let uu____4297 = (

let uu____4298 = (str "attributes")
in (

let uu____4299 = (FStar_Pprint.separate_map break1 p_atomicTerm es)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4298 uu____4299)))
in (FStar_Pprint.group uu____4297))
end
| FStar_Parser_AST.If (e1, e2, e3) -> begin
(

let uu____4303 = (is_unit e3)
in (match (uu____4303) with
| true -> begin
(

let uu____4304 = (

let uu____4305 = (

let uu____4306 = (str "if")
in (

let uu____4307 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat uu____4306 uu____4307)))
in (

let uu____4308 = (

let uu____4309 = (str "then")
in (

let uu____4310 = (p_noSeqTerm e2)
in (op_Hat_Slash_Plus_Hat uu____4309 uu____4310)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4305 uu____4308)))
in (FStar_Pprint.group uu____4304))
end
| uu____4311 -> begin
(

let e2_doc = (

let uu____4313 = (

let uu____4314 = (unparen e2)
in uu____4314.FStar_Parser_AST.tm)
in (match (uu____4313) with
| FStar_Parser_AST.If (uu____4315, uu____4316, e31) when (is_unit e31) -> begin
(

let uu____4318 = (p_noSeqTerm e2)
in (soft_parens_with_nesting uu____4318))
end
| uu____4319 -> begin
(p_noSeqTerm e2)
end))
in (

let uu____4320 = (

let uu____4321 = (

let uu____4322 = (str "if")
in (

let uu____4323 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat uu____4322 uu____4323)))
in (

let uu____4324 = (

let uu____4325 = (

let uu____4326 = (str "then")
in (op_Hat_Slash_Plus_Hat uu____4326 e2_doc))
in (

let uu____4327 = (

let uu____4328 = (str "else")
in (

let uu____4329 = (p_noSeqTerm e3)
in (op_Hat_Slash_Plus_Hat uu____4328 uu____4329)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4325 uu____4327)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4321 uu____4324)))
in (FStar_Pprint.group uu____4320)))
end))
end
| FStar_Parser_AST.TryWith (e1, branches) -> begin
(

let uu____4352 = (

let uu____4353 = (

let uu____4354 = (str "try")
in (

let uu____4355 = (p_noSeqTerm e1)
in (prefix2 uu____4354 uu____4355)))
in (

let uu____4356 = (

let uu____4357 = (str "with")
in (

let uu____4358 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4357 uu____4358)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4353 uu____4356)))
in (FStar_Pprint.group uu____4352))
end
| FStar_Parser_AST.Match (e1, branches) -> begin
(

let uu____4389 = (

let uu____4390 = (

let uu____4391 = (str "match")
in (

let uu____4392 = (p_noSeqTerm e1)
in (

let uu____4393 = (str "with")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____4391 uu____4392 uu____4393))))
in (

let uu____4394 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4390 uu____4394)))
in (FStar_Pprint.group uu____4389))
end
| FStar_Parser_AST.LetOpen (uid, e1) -> begin
(

let uu____4405 = (

let uu____4406 = (

let uu____4407 = (str "let open")
in (

let uu____4408 = (p_quident uid)
in (

let uu____4409 = (str "in")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____4407 uu____4408 uu____4409))))
in (

let uu____4410 = (p_term e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4406 uu____4410)))
in (FStar_Pprint.group uu____4405))
end
| FStar_Parser_AST.Let (q, lbs, e1) -> begin
(

let let_doc = (

let uu____4427 = (str "let")
in (

let uu____4428 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat uu____4427 uu____4428)))
in (

let uu____4429 = (

let uu____4430 = (

let uu____4431 = (

let uu____4432 = (str "and")
in (precede_break_separate_map let_doc uu____4432 p_letbinding lbs))
in (

let uu____4437 = (str "in")
in (FStar_Pprint.op_Hat_Slash_Hat uu____4431 uu____4437)))
in (FStar_Pprint.group uu____4430))
in (

let uu____4438 = (p_term e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4429 uu____4438))))
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, typ_opt); FStar_Parser_AST.prange = uu____4441})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, branches); FStar_Parser_AST.range = uu____4444; FStar_Parser_AST.level = uu____4445}) when (matches_var maybe_x x) -> begin
(

let uu____4472 = (

let uu____4473 = (str "function")
in (

let uu____4474 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4473 uu____4474)))
in (FStar_Pprint.group uu____4472))
end
| FStar_Parser_AST.Assign (id, e1) -> begin
(

let uu____4485 = (

let uu____4486 = (p_lident id)
in (

let uu____4487 = (

let uu____4488 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow uu____4488))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4486 uu____4487)))
in (FStar_Pprint.group uu____4485))
end
| uu____4489 -> begin
(p_typ e)
end)))
and p_typ : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_typ' e e.FStar_Parser_AST.range))
and p_typ' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____4492 = (

let uu____4493 = (unparen e)
in uu____4493.FStar_Parser_AST.tm)
in (match (uu____4492) with
| FStar_Parser_AST.QForall (bs, trigger, e1) -> begin
(

let uu____4509 = (

let uu____4510 = (

let uu____4511 = (p_quantifier e)
in (FStar_Pprint.op_Hat_Hat uu____4511 FStar_Pprint.space))
in (

let uu____4512 = (p_binders true bs)
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") uu____4510 uu____4512 FStar_Pprint.dot)))
in (

let uu____4513 = (

let uu____4514 = (p_trigger trigger)
in (

let uu____4515 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat uu____4514 uu____4515)))
in (prefix2 uu____4509 uu____4513)))
end
| FStar_Parser_AST.QExists (bs, trigger, e1) -> begin
(

let uu____4531 = (

let uu____4532 = (

let uu____4533 = (p_quantifier e)
in (FStar_Pprint.op_Hat_Hat uu____4533 FStar_Pprint.space))
in (

let uu____4534 = (p_binders true bs)
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") uu____4532 uu____4534 FStar_Pprint.dot)))
in (

let uu____4535 = (

let uu____4536 = (p_trigger trigger)
in (

let uu____4537 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat uu____4536 uu____4537)))
in (prefix2 uu____4531 uu____4535)))
end
| uu____4538 -> begin
(p_simpleTerm e)
end)))
and p_quantifier : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____4540 = (

let uu____4541 = (unparen e)
in uu____4541.FStar_Parser_AST.tm)
in (match (uu____4540) with
| FStar_Parser_AST.QForall (uu____4542) -> begin
(str "forall")
end
| FStar_Parser_AST.QExists (uu____4555) -> begin
(str "exists")
end
| uu____4568 -> begin
(failwith "Imposible : p_quantifier called on a non-quantifier term")
end)))
and p_trigger : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun uu___102_4569 -> (match (uu___102_4569) with
| [] -> begin
FStar_Pprint.empty
end
| pats -> begin
(

let uu____4581 = (

let uu____4582 = (

let uu____4583 = (str "pattern")
in (

let uu____4584 = (

let uu____4585 = (

let uu____4586 = (p_disjunctivePats pats)
in (jump2 uu____4586))
in (

let uu____4587 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4585 uu____4587)))
in (FStar_Pprint.op_Hat_Slash_Hat uu____4583 uu____4584)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4582))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____4581))
end))
and p_disjunctivePats : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun pats -> (

let uu____4593 = (str "\\/")
in (FStar_Pprint.separate_map uu____4593 p_conjunctivePats pats)))
and p_conjunctivePats : FStar_Parser_AST.term Prims.list  ->  FStar_Pprint.document = (fun pats -> (

let uu____4599 = (FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats)
in (FStar_Pprint.group uu____4599)))
and p_simpleTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____4601 = (

let uu____4602 = (unparen e)
in uu____4602.FStar_Parser_AST.tm)
in (match (uu____4601) with
| FStar_Parser_AST.Abs (pats, e1) -> begin
(

let uu____4609 = (

let uu____4610 = (str "fun")
in (

let uu____4611 = (

let uu____4612 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Slash_Hat uu____4612 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat uu____4610 uu____4611)))
in (

let uu____4613 = (p_term e1)
in (op_Hat_Slash_Plus_Hat uu____4609 uu____4613)))
end
| uu____4614 -> begin
(p_tmIff e)
end)))
and p_maybeFocusArrow : Prims.bool  ->  FStar_Pprint.document = (fun b -> (match (b) with
| true -> begin
(str "~>")
end
| uu____4616 -> begin
FStar_Pprint.rarrow
end))
and p_patternBranch : (FStar_Parser_AST.pattern * FStar_Parser_AST.term FStar_Pervasives_Native.option * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun uu____4617 -> (match (uu____4617) with
| (pat, when_opt, e) -> begin
(

let maybe_paren = (

let uu____4636 = (

let uu____4637 = (unparen e)
in uu____4637.FStar_Parser_AST.tm)
in (match (uu____4636) with
| FStar_Parser_AST.Match (uu____4640) -> begin
soft_begin_end_with_nesting
end
| FStar_Parser_AST.TryWith (uu____4655) -> begin
soft_begin_end_with_nesting
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____4671); FStar_Parser_AST.prange = uu____4672})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, uu____4674); FStar_Parser_AST.range = uu____4675; FStar_Parser_AST.level = uu____4676}) when (matches_var maybe_x x) -> begin
soft_begin_end_with_nesting
end
| uu____4703 -> begin
(fun x -> x)
end))
in (

let uu____4705 = (

let uu____4706 = (

let uu____4707 = (

let uu____4708 = (

let uu____4709 = (

let uu____4710 = (p_disjunctivePattern pat)
in (

let uu____4711 = (

let uu____4712 = (p_maybeWhen when_opt)
in (FStar_Pprint.op_Hat_Hat uu____4712 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat uu____4710 uu____4711)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4709))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4708))
in (FStar_Pprint.group uu____4707))
in (

let uu____4713 = (

let uu____4714 = (p_term e)
in (maybe_paren uu____4714))
in (op_Hat_Slash_Plus_Hat uu____4706 uu____4713)))
in (FStar_Pprint.group uu____4705)))
end))
and p_maybeWhen : FStar_Parser_AST.term FStar_Pervasives_Native.option  ->  FStar_Pprint.document = (fun uu___103_4715 -> (match (uu___103_4715) with
| FStar_Pervasives_Native.None -> begin
FStar_Pprint.empty
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____4719 = (str "when")
in (

let uu____4720 = (

let uu____4721 = (p_tmFormula e)
in (FStar_Pprint.op_Hat_Hat uu____4721 FStar_Pprint.space))
in (op_Hat_Slash_Plus_Hat uu____4719 uu____4720)))
end))
and p_tmIff : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____4723 = (

let uu____4724 = (unparen e)
in uu____4724.FStar_Parser_AST.tm)
in (match (uu____4723) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____4725}, (e1)::(e2)::[]) -> begin
(

let uu____4730 = (str "<==>")
in (

let uu____4731 = (p_tmImplies e1)
in (

let uu____4732 = (p_tmIff e2)
in (infix0 uu____4730 uu____4731 uu____4732))))
end
| uu____4733 -> begin
(p_tmImplies e)
end)))
and p_tmImplies : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____4735 = (

let uu____4736 = (unparen e)
in uu____4736.FStar_Parser_AST.tm)
in (match (uu____4735) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____4737}, (e1)::(e2)::[]) -> begin
(

let uu____4742 = (str "==>")
in (

let uu____4743 = (p_tmArrow p_tmFormula e1)
in (

let uu____4744 = (p_tmImplies e2)
in (infix0 uu____4742 uu____4743 uu____4744))))
end
| uu____4745 -> begin
(p_tmArrow p_tmFormula e)
end)))
and p_tmArrow : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_Tm e -> (

let uu____4750 = (

let uu____4751 = (unparen e)
in uu____4751.FStar_Parser_AST.tm)
in (match (uu____4750) with
| FStar_Parser_AST.Product (bs, tgt) -> begin
(

let uu____4758 = (

let uu____4759 = (separate_map_or_flow FStar_Pprint.empty (fun b -> (

let uu____4764 = (p_binder false b)
in (

let uu____4765 = (

let uu____4766 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4766))
in (FStar_Pprint.op_Hat_Hat uu____4764 uu____4765)))) bs)
in (

let uu____4767 = (p_tmArrow p_Tm tgt)
in (FStar_Pprint.op_Hat_Hat uu____4759 uu____4767)))
in (FStar_Pprint.group uu____4758))
end
| uu____4768 -> begin
(p_Tm e)
end)))
and p_tmFormula : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____4770 = (

let uu____4771 = (unparen e)
in uu____4771.FStar_Parser_AST.tm)
in (match (uu____4770) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____4772}, (e1)::(e2)::[]) -> begin
(

let uu____4777 = (str "\\/")
in (

let uu____4778 = (p_tmFormula e1)
in (

let uu____4779 = (p_tmConjunction e2)
in (infix0 uu____4777 uu____4778 uu____4779))))
end
| uu____4780 -> begin
(p_tmConjunction e)
end)))
and p_tmConjunction : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____4782 = (

let uu____4783 = (unparen e)
in uu____4783.FStar_Parser_AST.tm)
in (match (uu____4782) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____4784}, (e1)::(e2)::[]) -> begin
(

let uu____4789 = (str "/\\")
in (

let uu____4790 = (p_tmConjunction e1)
in (

let uu____4791 = (p_tmTuple e2)
in (infix0 uu____4789 uu____4790 uu____4791))))
end
| uu____4792 -> begin
(p_tmTuple e)
end)))
and p_tmTuple : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_tmTuple' e e.FStar_Parser_AST.range))
and p_tmTuple' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____4795 = (

let uu____4796 = (unparen e)
in uu____4796.FStar_Parser_AST.tm)
in (match (uu____4795) with
| FStar_Parser_AST.Construct (lid, args) when (is_tuple_constructor lid) -> begin
(

let uu____4811 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map uu____4811 (fun uu____4819 -> (match (uu____4819) with
| (e1, uu____4825) -> begin
(p_tmEq e1)
end)) args))
end
| uu____4826 -> begin
(p_tmEq e)
end)))
and paren_if : Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun curr mine doc1 -> (match ((mine <= curr)) with
| true -> begin
doc1
end
| uu____4830 -> begin
(

let uu____4831 = (

let uu____4832 = (FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4832))
in (FStar_Pprint.group uu____4831))
end))
and p_tmEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n1 = (max_level (FStar_List.append (((colon_equals ()))::((pipe_right ()))::[]) (operatorInfix0ad12 ())))
in (p_tmEq' n1 e)))
and p_tmEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (

let uu____4877 = (

let uu____4878 = (unparen e)
in uu____4878.FStar_Parser_AST.tm)
in (match (uu____4877) with
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (((is_operatorInfix0ad12 op) || ((FStar_Ident.text_of_id op) = "=")) || ((FStar_Ident.text_of_id op) = "|>")) -> begin
(

let op1 = (FStar_Ident.text_of_id op)
in (

let uu____4885 = (levels op1)
in (match (uu____4885) with
| (left1, mine, right1) -> begin
(

let uu____4895 = (

let uu____4896 = (FStar_All.pipe_left str op1)
in (

let uu____4897 = (p_tmEq' left1 e1)
in (

let uu____4898 = (p_tmEq' right1 e2)
in (infix0 uu____4896 uu____4897 uu____4898))))
in (paren_if curr mine uu____4895))
end)))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____4899}, (e1)::(e2)::[]) -> begin
(

let uu____4904 = (

let uu____4905 = (p_tmEq e1)
in (

let uu____4906 = (

let uu____4907 = (

let uu____4908 = (

let uu____4909 = (p_tmEq e2)
in (op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____4909))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4908))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4907))
in (FStar_Pprint.op_Hat_Hat uu____4905 uu____4906)))
in (FStar_Pprint.group uu____4904))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____4910}, (e1)::[]) -> begin
(

let uu____4914 = (levels "-")
in (match (uu____4914) with
| (left1, mine, right1) -> begin
(

let uu____4924 = (p_tmEq' mine e1)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____4924))
end))
end
| uu____4925 -> begin
(p_tmNoEq e)
end)))
and p_tmNoEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n1 = (max_level (((colon_colon ()))::((amp ()))::((opinfix3 ()))::((opinfix4 ()))::[]))
in (p_tmNoEq' n1 e)))
and p_tmNoEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (

let uu____4980 = (

let uu____4981 = (unparen e)
in uu____4981.FStar_Parser_AST.tm)
in (match (uu____4980) with
| FStar_Parser_AST.Construct (lid, ((e1, uu____4984))::((e2, uu____4986))::[]) when ((FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) && (

let uu____5006 = (is_list e)
in (not (uu____5006)))) -> begin
(

let op = "::"
in (

let uu____5008 = (levels op)
in (match (uu____5008) with
| (left1, mine, right1) -> begin
(

let uu____5018 = (

let uu____5019 = (str op)
in (

let uu____5020 = (p_tmNoEq' left1 e1)
in (

let uu____5021 = (p_tmNoEq' right1 e2)
in (infix0 uu____5019 uu____5020 uu____5021))))
in (paren_if curr mine uu____5018))
end)))
end
| FStar_Parser_AST.Sum (binders, res) -> begin
(

let op = "&"
in (

let uu____5029 = (levels op)
in (match (uu____5029) with
| (left1, mine, right1) -> begin
(

let p_dsumfst = (fun b -> (

let uu____5043 = (p_binder false b)
in (

let uu____5044 = (

let uu____5045 = (

let uu____5046 = (str op)
in (FStar_Pprint.op_Hat_Hat uu____5046 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5045))
in (FStar_Pprint.op_Hat_Hat uu____5043 uu____5044))))
in (

let uu____5047 = (

let uu____5048 = (FStar_Pprint.concat_map p_dsumfst binders)
in (

let uu____5049 = (p_tmNoEq' right1 res)
in (FStar_Pprint.op_Hat_Hat uu____5048 uu____5049)))
in (paren_if curr mine uu____5047)))
end)))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (is_operatorInfix34 op) -> begin
(

let op1 = (FStar_Ident.text_of_id op)
in (

let uu____5056 = (levels op1)
in (match (uu____5056) with
| (left1, mine, right1) -> begin
(

let uu____5066 = (

let uu____5067 = (str op1)
in (

let uu____5068 = (p_tmNoEq' left1 e1)
in (

let uu____5069 = (p_tmNoEq' right1 e2)
in (infix0 uu____5067 uu____5068 uu____5069))))
in (paren_if curr mine uu____5066))
end)))
end
| FStar_Parser_AST.NamedTyp (lid, e1) -> begin
(

let uu____5072 = (

let uu____5073 = (p_lidentOrUnderscore lid)
in (

let uu____5074 = (

let uu____5075 = (p_appTerm e1)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5075))
in (FStar_Pprint.op_Hat_Slash_Hat uu____5073 uu____5074)))
in (FStar_Pprint.group uu____5072))
end
| FStar_Parser_AST.Refine (b, phi) -> begin
(p_refinedBinder b phi)
end
| FStar_Parser_AST.Record (with_opt, record_fields) -> begin
(

let uu____5096 = (

let uu____5097 = (default_or_map FStar_Pprint.empty p_with_clause with_opt)
in (

let uu____5098 = (

let uu____5099 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (FStar_Pprint.separate_map uu____5099 p_simpleDef record_fields))
in (FStar_Pprint.op_Hat_Hat uu____5097 uu____5098)))
in (braces_with_nesting uu____5096))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____5104}, (e1)::[]) -> begin
(

let uu____5108 = (

let uu____5109 = (str "~")
in (

let uu____5110 = (p_atomicTerm e1)
in (FStar_Pprint.op_Hat_Hat uu____5109 uu____5110)))
in (FStar_Pprint.group uu____5108))
end
| uu____5111 -> begin
(p_appTerm e)
end)))
and p_with_clause : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____5113 = (p_appTerm e)
in (

let uu____5114 = (

let uu____5115 = (

let uu____5116 = (str "with")
in (FStar_Pprint.op_Hat_Hat uu____5116 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5115))
in (FStar_Pprint.op_Hat_Hat uu____5113 uu____5114))))
and p_refinedBinder : FStar_Parser_AST.binder  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun b phi -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (lid, t) -> begin
(

let uu____5121 = (

let uu____5122 = (p_lident lid)
in (p_refinement b.FStar_Parser_AST.aqual uu____5122 t phi))
in (soft_parens_with_nesting uu____5121))
end
| FStar_Parser_AST.TAnnotated (uu____5123) -> begin
(failwith "Is this still used ?")
end
| FStar_Parser_AST.Variable (uu____5128) -> begin
(

let uu____5129 = (

let uu____5130 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" uu____5130))
in (failwith uu____5129))
end
| FStar_Parser_AST.TVariable (uu____5131) -> begin
(

let uu____5132 = (

let uu____5133 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" uu____5133))
in (failwith uu____5132))
end
| FStar_Parser_AST.NoName (uu____5134) -> begin
(

let uu____5135 = (

let uu____5136 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" uu____5136))
in (failwith uu____5135))
end))
and p_simpleDef : (FStar_Ident.lid * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun uu____5137 -> (match (uu____5137) with
| (lid, e) -> begin
(

let uu____5144 = (

let uu____5145 = (p_qlident lid)
in (

let uu____5146 = (

let uu____5147 = (p_tmIff e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____5147))
in (FStar_Pprint.op_Hat_Slash_Hat uu____5145 uu____5146)))
in (FStar_Pprint.group uu____5144))
end))
and p_appTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____5149 = (

let uu____5150 = (unparen e)
in uu____5150.FStar_Parser_AST.tm)
in (match (uu____5149) with
| FStar_Parser_AST.App (uu____5151) when (is_general_application e) -> begin
(

let uu____5158 = (head_and_args e)
in (match (uu____5158) with
| (head1, args) -> begin
(

let uu____5183 = (

let uu____5194 = (FStar_ST.op_Bang should_print_fs_typ_app)
in (match (uu____5194) with
| true -> begin
(

let uu____5215 = (FStar_Util.take (fun uu____5239 -> (match (uu____5239) with
| (uu____5244, aq) -> begin
(aq = FStar_Parser_AST.FsTypApp)
end)) args)
in (match (uu____5215) with
| (fs_typ_args, args1) -> begin
(

let uu____5282 = (

let uu____5283 = (p_indexingTerm head1)
in (

let uu____5284 = (

let uu____5285 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (soft_surround_map_or_flow (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.empty FStar_Pprint.langle uu____5285 FStar_Pprint.rangle p_fsTypArg fs_typ_args))
in (FStar_Pprint.op_Hat_Hat uu____5283 uu____5284)))
in ((uu____5282), (args1)))
end))
end
| uu____5296 -> begin
(

let uu____5297 = (p_indexingTerm head1)
in ((uu____5297), (args)))
end))
in (match (uu____5183) with
| (head_doc, args1) -> begin
(

let uu____5318 = (

let uu____5319 = (FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space)
in (soft_surround_map_or_flow (Prims.parse_int "2") (Prims.parse_int "0") head_doc uu____5319 break1 FStar_Pprint.empty p_argTerm args1))
in (FStar_Pprint.group uu____5318))
end))
end))
end
| FStar_Parser_AST.Construct (lid, args) when ((is_general_construction e) && (

let uu____5339 = (is_dtuple_constructor lid)
in (not (uu____5339)))) -> begin
(match (args) with
| [] -> begin
(p_quident lid)
end
| (arg)::[] -> begin
(

let uu____5357 = (

let uu____5358 = (p_quident lid)
in (

let uu____5359 = (p_argTerm arg)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5358 uu____5359)))
in (FStar_Pprint.group uu____5357))
end
| (hd1)::tl1 -> begin
(

let uu____5376 = (

let uu____5377 = (

let uu____5378 = (

let uu____5379 = (p_quident lid)
in (

let uu____5380 = (p_argTerm hd1)
in (prefix2 uu____5379 uu____5380)))
in (FStar_Pprint.group uu____5378))
in (

let uu____5381 = (

let uu____5382 = (FStar_Pprint.separate_map break1 p_argTerm tl1)
in (jump2 uu____5382))
in (FStar_Pprint.op_Hat_Hat uu____5377 uu____5381)))
in (FStar_Pprint.group uu____5376))
end)
end
| uu____5387 -> begin
(p_indexingTerm e)
end)))
and p_argTerm : (FStar_Parser_AST.term * FStar_Parser_AST.imp)  ->  FStar_Pprint.document = (fun arg_imp -> (match (arg_imp) with
| (u, FStar_Parser_AST.UnivApp) -> begin
(p_universe u)
end
| (e, FStar_Parser_AST.FsTypApp) -> begin
((FStar_Util.print_warning "Unexpected FsTypApp, output might not be formatted correctly.\n");
(

let uu____5396 = (p_indexingTerm e)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.langle uu____5396 FStar_Pprint.rangle));
)
end
| (e, FStar_Parser_AST.Hash) -> begin
(

let uu____5398 = (str "#")
in (

let uu____5399 = (p_indexingTerm e)
in (FStar_Pprint.op_Hat_Hat uu____5398 uu____5399)))
end
| (e, FStar_Parser_AST.Nothing) -> begin
(p_indexingTerm e)
end))
and p_fsTypArg : (FStar_Parser_AST.term * FStar_Parser_AST.imp)  ->  FStar_Pprint.document = (fun uu____5401 -> (match (uu____5401) with
| (e, uu____5407) -> begin
(p_indexingTerm e)
end))
and p_indexingTerm_aux : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun exit1 e -> (

let uu____5412 = (

let uu____5413 = (unparen e)
in uu____5413.FStar_Parser_AST.tm)
in (match (uu____5412) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____5414}, (e1)::(e2)::[]) -> begin
(

let uu____5419 = (

let uu____5420 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (

let uu____5421 = (

let uu____5422 = (

let uu____5423 = (p_term e2)
in (soft_parens_with_nesting uu____5423))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5422))
in (FStar_Pprint.op_Hat_Hat uu____5420 uu____5421)))
in (FStar_Pprint.group uu____5419))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____5424}, (e1)::(e2)::[]) -> begin
(

let uu____5429 = (

let uu____5430 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (

let uu____5431 = (

let uu____5432 = (

let uu____5433 = (p_term e2)
in (soft_brackets_with_nesting uu____5433))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5432))
in (FStar_Pprint.op_Hat_Hat uu____5430 uu____5431)))
in (FStar_Pprint.group uu____5429))
end
| uu____5434 -> begin
(exit1 e)
end)))
and p_indexingTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_indexingTerm_aux p_atomicTerm e))
and p_atomicTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____5437 = (

let uu____5438 = (unparen e)
in uu____5438.FStar_Parser_AST.tm)
in (match (uu____5437) with
| FStar_Parser_AST.LetOpen (lid, e1) -> begin
(

let uu____5441 = (p_quident lid)
in (

let uu____5442 = (

let uu____5443 = (

let uu____5444 = (p_term e1)
in (soft_parens_with_nesting uu____5444))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5443))
in (FStar_Pprint.op_Hat_Hat uu____5441 uu____5442)))
end
| FStar_Parser_AST.Name (lid) -> begin
(p_quident lid)
end
| FStar_Parser_AST.Op (op, (e1)::[]) when (is_general_prefix_op op) -> begin
(

let uu____5450 = (str (FStar_Ident.text_of_id op))
in (

let uu____5451 = (p_atomicTerm e1)
in (FStar_Pprint.op_Hat_Hat uu____5450 uu____5451)))
end
| uu____5452 -> begin
(p_atomicTermNotQUident e)
end)))
and p_atomicTermNotQUident : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____5454 = (

let uu____5455 = (unparen e)
in uu____5455.FStar_Parser_AST.tm)
in (match (uu____5454) with
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
| uu____5460 -> begin
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

let uu____5467 = (str (FStar_Ident.text_of_id op))
in (

let uu____5468 = (p_atomicTermNotQUident e1)
in (FStar_Pprint.op_Hat_Hat uu____5467 uu____5468)))
end
| FStar_Parser_AST.Op (op, []) -> begin
(

let uu____5472 = (

let uu____5473 = (

let uu____5474 = (str (FStar_Ident.text_of_id op))
in (

let uu____5475 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat uu____5474 uu____5475)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5473))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5472))
end
| FStar_Parser_AST.Construct (lid, args) when (is_dtuple_constructor lid) -> begin
(

let uu____5490 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (

let uu____5491 = (

let uu____5492 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (

let uu____5493 = (FStar_List.map FStar_Pervasives_Native.fst args)
in (FStar_Pprint.separate_map uu____5492 p_tmEq uu____5493)))
in (

let uu____5500 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____5490 uu____5491 uu____5500))))
end
| FStar_Parser_AST.Project (e1, lid) -> begin
(

let uu____5503 = (

let uu____5504 = (p_atomicTermNotQUident e1)
in (

let uu____5505 = (

let uu____5506 = (p_qlident lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5506))
in (FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0") uu____5504 uu____5505)))
in (FStar_Pprint.group uu____5503))
end
| uu____5507 -> begin
(p_projectionLHS e)
end)))
and p_projectionLHS : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____5509 = (

let uu____5510 = (unparen e)
in uu____5510.FStar_Parser_AST.tm)
in (match (uu____5509) with
| FStar_Parser_AST.Var (lid) -> begin
(p_qlident lid)
end
| FStar_Parser_AST.Projector (constr_lid, field_lid) -> begin
(

let uu____5514 = (p_quident constr_lid)
in (

let uu____5515 = (

let uu____5516 = (

let uu____5517 = (p_lident field_lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5517))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____5516))
in (FStar_Pprint.op_Hat_Hat uu____5514 uu____5515)))
end
| FStar_Parser_AST.Discrim (constr_lid) -> begin
(

let uu____5519 = (p_quident constr_lid)
in (FStar_Pprint.op_Hat_Hat uu____5519 FStar_Pprint.qmark))
end
| FStar_Parser_AST.Paren (e1) -> begin
(

let uu____5521 = (p_term e1)
in (soft_parens_with_nesting uu____5521))
end
| uu____5522 when (is_array e) -> begin
(

let es = (extract_from_list e)
in (

let uu____5526 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar)
in (

let uu____5527 = (

let uu____5528 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (separate_map_or_flow uu____5528 p_noSeqTerm es))
in (

let uu____5529 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") uu____5526 uu____5527 uu____5529)))))
end
| uu____5530 when (is_list e) -> begin
(

let uu____5531 = (

let uu____5532 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (

let uu____5533 = (extract_from_list e)
in (separate_map_or_flow uu____5532 p_noSeqTerm uu____5533)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket uu____5531 FStar_Pprint.rbracket))
end
| uu____5536 when (is_lex_list e) -> begin
(

let uu____5537 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket)
in (

let uu____5538 = (

let uu____5539 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (

let uu____5540 = (extract_from_list e)
in (separate_map_or_flow uu____5539 p_noSeqTerm uu____5540)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") uu____5537 uu____5538 FStar_Pprint.rbracket)))
end
| uu____5543 when (is_ref_set e) -> begin
(

let es = (extract_from_ref_set e)
in (

let uu____5547 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace)
in (

let uu____5548 = (

let uu____5549 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (separate_map_or_flow uu____5549 p_appTerm es))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") uu____5547 uu____5548 FStar_Pprint.rbrace))))
end
| FStar_Parser_AST.Labeled (e1, s, b) -> begin
(

let uu____5553 = (str (Prims.strcat "(*" (Prims.strcat s "*)")))
in (

let uu____5554 = (p_term e1)
in (FStar_Pprint.op_Hat_Slash_Hat uu____5553 uu____5554)))
end
| FStar_Parser_AST.Op (op, args) when (

let uu____5561 = (handleable_op op args)
in (not (uu____5561))) -> begin
(

let uu____5562 = (

let uu____5563 = (

let uu____5564 = (

let uu____5565 = (

let uu____5566 = (FStar_Util.string_of_int (FStar_List.length args))
in (Prims.strcat uu____5566 " arguments couldn\'t be handled by the pretty printer"))
in (Prims.strcat " with " uu____5565))
in (Prims.strcat (FStar_Ident.text_of_id op) uu____5564))
in (Prims.strcat "Operation " uu____5563))
in (failwith uu____5562))
end
| FStar_Parser_AST.Uvar (uu____5567) -> begin
(failwith "Unexpected universe variable out of universe context")
end
| FStar_Parser_AST.Wild -> begin
(

let uu____5568 = (p_term e)
in (soft_parens_with_nesting uu____5568))
end
| FStar_Parser_AST.Const (uu____5569) -> begin
(

let uu____5570 = (p_term e)
in (soft_parens_with_nesting uu____5570))
end
| FStar_Parser_AST.Op (uu____5571) -> begin
(

let uu____5578 = (p_term e)
in (soft_parens_with_nesting uu____5578))
end
| FStar_Parser_AST.Tvar (uu____5579) -> begin
(

let uu____5580 = (p_term e)
in (soft_parens_with_nesting uu____5580))
end
| FStar_Parser_AST.Var (uu____5581) -> begin
(

let uu____5582 = (p_term e)
in (soft_parens_with_nesting uu____5582))
end
| FStar_Parser_AST.Name (uu____5583) -> begin
(

let uu____5584 = (p_term e)
in (soft_parens_with_nesting uu____5584))
end
| FStar_Parser_AST.Construct (uu____5585) -> begin
(

let uu____5596 = (p_term e)
in (soft_parens_with_nesting uu____5596))
end
| FStar_Parser_AST.Abs (uu____5597) -> begin
(

let uu____5604 = (p_term e)
in (soft_parens_with_nesting uu____5604))
end
| FStar_Parser_AST.App (uu____5605) -> begin
(

let uu____5612 = (p_term e)
in (soft_parens_with_nesting uu____5612))
end
| FStar_Parser_AST.Let (uu____5613) -> begin
(

let uu____5626 = (p_term e)
in (soft_parens_with_nesting uu____5626))
end
| FStar_Parser_AST.LetOpen (uu____5627) -> begin
(

let uu____5632 = (p_term e)
in (soft_parens_with_nesting uu____5632))
end
| FStar_Parser_AST.Seq (uu____5633) -> begin
(

let uu____5638 = (p_term e)
in (soft_parens_with_nesting uu____5638))
end
| FStar_Parser_AST.Bind (uu____5639) -> begin
(

let uu____5646 = (p_term e)
in (soft_parens_with_nesting uu____5646))
end
| FStar_Parser_AST.If (uu____5647) -> begin
(

let uu____5654 = (p_term e)
in (soft_parens_with_nesting uu____5654))
end
| FStar_Parser_AST.Match (uu____5655) -> begin
(

let uu____5670 = (p_term e)
in (soft_parens_with_nesting uu____5670))
end
| FStar_Parser_AST.TryWith (uu____5671) -> begin
(

let uu____5686 = (p_term e)
in (soft_parens_with_nesting uu____5686))
end
| FStar_Parser_AST.Ascribed (uu____5687) -> begin
(

let uu____5696 = (p_term e)
in (soft_parens_with_nesting uu____5696))
end
| FStar_Parser_AST.Record (uu____5697) -> begin
(

let uu____5710 = (p_term e)
in (soft_parens_with_nesting uu____5710))
end
| FStar_Parser_AST.Project (uu____5711) -> begin
(

let uu____5716 = (p_term e)
in (soft_parens_with_nesting uu____5716))
end
| FStar_Parser_AST.Product (uu____5717) -> begin
(

let uu____5724 = (p_term e)
in (soft_parens_with_nesting uu____5724))
end
| FStar_Parser_AST.Sum (uu____5725) -> begin
(

let uu____5732 = (p_term e)
in (soft_parens_with_nesting uu____5732))
end
| FStar_Parser_AST.QForall (uu____5733) -> begin
(

let uu____5746 = (p_term e)
in (soft_parens_with_nesting uu____5746))
end
| FStar_Parser_AST.QExists (uu____5747) -> begin
(

let uu____5760 = (p_term e)
in (soft_parens_with_nesting uu____5760))
end
| FStar_Parser_AST.Refine (uu____5761) -> begin
(

let uu____5766 = (p_term e)
in (soft_parens_with_nesting uu____5766))
end
| FStar_Parser_AST.NamedTyp (uu____5767) -> begin
(

let uu____5772 = (p_term e)
in (soft_parens_with_nesting uu____5772))
end
| FStar_Parser_AST.Requires (uu____5773) -> begin
(

let uu____5780 = (p_term e)
in (soft_parens_with_nesting uu____5780))
end
| FStar_Parser_AST.Ensures (uu____5781) -> begin
(

let uu____5788 = (p_term e)
in (soft_parens_with_nesting uu____5788))
end
| FStar_Parser_AST.Assign (uu____5789) -> begin
(

let uu____5794 = (p_term e)
in (soft_parens_with_nesting uu____5794))
end
| FStar_Parser_AST.Attributes (uu____5795) -> begin
(

let uu____5798 = (p_term e)
in (soft_parens_with_nesting uu____5798))
end)))
and p_constant : FStar_Const.sconst  ->  FStar_Pprint.document = (fun uu___106_5799 -> (match (uu___106_5799) with
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

let uu____5803 = (FStar_Pprint.doc_of_char x)
in (FStar_Pprint.squotes uu____5803))
end
| FStar_Const.Const_string (bytes, uu____5805) -> begin
(

let uu____5810 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes uu____5810))
end
| FStar_Const.Const_bytearray (bytes, uu____5812) -> begin
(

let uu____5817 = (

let uu____5818 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes uu____5818))
in (

let uu____5819 = (str "B")
in (FStar_Pprint.op_Hat_Hat uu____5817 uu____5819)))
end
| FStar_Const.Const_int (repr, sign_width_opt) -> begin
(

let signedness = (fun uu___104_5837 -> (match (uu___104_5837) with
| FStar_Const.Unsigned -> begin
(str "u")
end
| FStar_Const.Signed -> begin
FStar_Pprint.empty
end))
in (

let width = (fun uu___105_5841 -> (match (uu___105_5841) with
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

let ending = (default_or_map FStar_Pprint.empty (fun uu____5852 -> (match (uu____5852) with
| (s, w) -> begin
(

let uu____5859 = (signedness s)
in (

let uu____5860 = (width w)
in (FStar_Pprint.op_Hat_Hat uu____5859 uu____5860)))
end)) sign_width_opt)
in (

let uu____5861 = (str repr)
in (FStar_Pprint.op_Hat_Hat uu____5861 ending)))))
end
| FStar_Const.Const_range (r) -> begin
(

let uu____5863 = (FStar_Range.string_of_range r)
in (str uu____5863))
end
| FStar_Const.Const_reify -> begin
(str "reify")
end
| FStar_Const.Const_reflect (lid) -> begin
(

let uu____5865 = (p_quident lid)
in (

let uu____5866 = (

let uu____5867 = (

let uu____5868 = (str "reflect")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5868))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____5867))
in (FStar_Pprint.op_Hat_Hat uu____5865 uu____5866)))
end))
and p_universe : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (

let uu____5870 = (str "u#")
in (

let uu____5871 = (p_atomicUniverse u)
in (FStar_Pprint.op_Hat_Hat uu____5870 uu____5871))))
and p_universeFrom : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (

let uu____5873 = (

let uu____5874 = (unparen u)
in uu____5874.FStar_Parser_AST.tm)
in (match (uu____5873) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____5875}, (u1)::(u2)::[]) -> begin
(

let uu____5880 = (

let uu____5881 = (p_universeFrom u1)
in (

let uu____5882 = (

let uu____5883 = (p_universeFrom u2)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____5883))
in (FStar_Pprint.op_Hat_Slash_Hat uu____5881 uu____5882)))
in (FStar_Pprint.group uu____5880))
end
| FStar_Parser_AST.App (uu____5884) -> begin
(

let uu____5891 = (head_and_args u)
in (match (uu____5891) with
| (head1, args) -> begin
(

let uu____5916 = (

let uu____5917 = (unparen head1)
in uu____5917.FStar_Parser_AST.tm)
in (match (uu____5916) with
| FStar_Parser_AST.Var (maybe_max_lid) when (FStar_Ident.lid_equals maybe_max_lid FStar_Parser_Const.max_lid) -> begin
(

let uu____5919 = (

let uu____5920 = (p_qlident FStar_Parser_Const.max_lid)
in (

let uu____5921 = (FStar_Pprint.separate_map FStar_Pprint.space (fun uu____5929 -> (match (uu____5929) with
| (u1, uu____5935) -> begin
(p_atomicUniverse u1)
end)) args)
in (op_Hat_Slash_Plus_Hat uu____5920 uu____5921)))
in (FStar_Pprint.group uu____5919))
end
| uu____5936 -> begin
(

let uu____5937 = (

let uu____5938 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" uu____5938))
in (failwith uu____5937))
end))
end))
end
| uu____5939 -> begin
(p_atomicUniverse u)
end)))
and p_atomicUniverse : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (

let uu____5941 = (

let uu____5942 = (unparen u)
in uu____5942.FStar_Parser_AST.tm)
in (match (uu____5941) with
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

let uu____5965 = (p_universeFrom u1)
in (soft_parens_with_nesting uu____5965))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____5966}, (uu____5967)::(uu____5968)::[]) -> begin
(

let uu____5971 = (p_universeFrom u)
in (soft_parens_with_nesting uu____5971))
end
| FStar_Parser_AST.App (uu____5972) -> begin
(

let uu____5979 = (p_universeFrom u)
in (soft_parens_with_nesting uu____5979))
end
| uu____5980 -> begin
(

let uu____5981 = (

let uu____5982 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" uu____5982))
in (failwith uu____5981))
end)))


let term_to_document : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_term e))


let decl_to_document : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun e -> (p_decl e))


let pat_to_document : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (p_disjunctivePattern p))


let binder_to_document : FStar_Parser_AST.binder  ->  FStar_Pprint.document = (fun b -> (p_binder true b))


let modul_to_document : FStar_Parser_AST.modul  ->  FStar_Pprint.document = (fun m -> ((FStar_ST.op_Colon_Equals should_print_fs_typ_app false);
(

let res = (match (m) with
| FStar_Parser_AST.Module (uu____6015, decls) -> begin
(

let uu____6021 = (FStar_All.pipe_right decls (FStar_List.map decl_to_document))
in (FStar_All.pipe_right uu____6021 (FStar_Pprint.separate FStar_Pprint.hardline)))
end
| FStar_Parser_AST.Interface (uu____6030, decls, uu____6032) -> begin
(

let uu____6037 = (FStar_All.pipe_right decls (FStar_List.map decl_to_document))
in (FStar_All.pipe_right uu____6037 (FStar_Pprint.separate FStar_Pprint.hardline)))
end)
in ((FStar_ST.op_Colon_Equals should_print_fs_typ_app false);
res;
));
))


let comments_to_document : (Prims.string * FStar_Range.range) Prims.list  ->  FStar_Pprint.document = (fun comments -> (FStar_Pprint.separate_map FStar_Pprint.hardline (fun uu____6080 -> (match (uu____6080) with
| (comment, range) -> begin
(str comment)
end)) comments))


let modul_with_comments_to_document : FStar_Parser_AST.modul  ->  (Prims.string * FStar_Range.range) Prims.list  ->  (FStar_Pprint.document * (Prims.string * FStar_Range.range) Prims.list) = (fun m comments -> (

let decls = (match (m) with
| FStar_Parser_AST.Module (uu____6122, decls) -> begin
decls
end
| FStar_Parser_AST.Interface (uu____6128, decls, uu____6130) -> begin
decls
end)
in ((FStar_ST.op_Colon_Equals should_print_fs_typ_app false);
(match (decls) with
| [] -> begin
((FStar_Pprint.empty), (comments))
end
| (d)::ds -> begin
(

let uu____6166 = (match (ds) with
| ({FStar_Parser_AST.d = FStar_Parser_AST.Pragma (FStar_Parser_AST.LightOff); FStar_Parser_AST.drange = uu____6179; FStar_Parser_AST.doc = uu____6180; FStar_Parser_AST.quals = uu____6181; FStar_Parser_AST.attrs = uu____6182})::uu____6183 -> begin
(

let d0 = (FStar_List.hd ds)
in (

let uu____6189 = (

let uu____6192 = (

let uu____6195 = (FStar_List.tl ds)
in (d)::uu____6195)
in (d0)::uu____6192)
in ((uu____6189), (d0.FStar_Parser_AST.drange))))
end
| uu____6200 -> begin
(((d)::ds), (d.FStar_Parser_AST.drange))
end)
in (match (uu____6166) with
| (decls1, first_range) -> begin
(

let extract_decl_range = (fun d1 -> d1.FStar_Parser_AST.drange)
in ((FStar_ST.op_Colon_Equals comment_stack comments);
(

let initial_comment = (

let uu____6261 = (FStar_Range.start_of_range first_range)
in (place_comments_until_pos (Prims.parse_int "0") (Prims.parse_int "1") uu____6261 FStar_Pprint.empty))
in (

let doc1 = (separate_map_with_comments FStar_Pprint.empty FStar_Pprint.empty decl_to_document decls1 extract_decl_range)
in (

let comments1 = (FStar_ST.op_Bang comment_stack)
in ((FStar_ST.op_Colon_Equals comment_stack []);
(FStar_ST.op_Colon_Equals should_print_fs_typ_app false);
(

let uu____6354 = (FStar_Pprint.op_Hat_Hat initial_comment doc1)
in ((uu____6354), (comments1)));
))));
))
end))
end);
)))




