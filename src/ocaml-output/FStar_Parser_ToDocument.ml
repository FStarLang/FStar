
open Prims

let should_unparen : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref true)


let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (

let uu____7 = (not ((FStar_ST.read should_unparen)))
in (match (uu____7) with
| true -> begin
t
end
| uu____10 -> begin
(match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| uu____12 -> begin
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


let separate_break_map = (fun sep f l -> (FStar_Pprint.group (let _0_325 = (let _0_324 = (FStar_Pprint.op_Hat_Hat sep break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_324))
in (FStar_Pprint.separate_map _0_325 f l))))


let precede_break_separate_map = (fun prec sep f l -> (let _0_334 = (let _0_328 = (FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space)
in (let _0_327 = (let _0_326 = (FStar_List.hd l)
in (FStar_All.pipe_right _0_326 f))
in (FStar_Pprint.precede _0_328 _0_327)))
in (let _0_333 = (let _0_332 = (FStar_List.tl l)
in (FStar_Pprint.concat_map (fun x -> (let _0_331 = (let _0_330 = (let _0_329 = (f x)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_329))
in (FStar_Pprint.op_Hat_Hat sep _0_330))
in (FStar_Pprint.op_Hat_Hat break1 _0_331))) _0_332))
in (FStar_Pprint.op_Hat_Hat _0_334 _0_333))))


let concat_break_map = (fun f l -> (FStar_Pprint.group (FStar_Pprint.concat_map (fun x -> (let _0_335 = (f x)
in (FStar_Pprint.op_Hat_Hat _0_335 break1))) l)))


let parens_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lparen contents FStar_Pprint.rparen))


let soft_parens_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lparen contents FStar_Pprint.rparen))


let braces_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbrace contents FStar_Pprint.rbrace))


let soft_braces_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbrace contents FStar_Pprint.rbrace))


let brackets_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbracket contents FStar_Pprint.rbracket))


let soft_brackets_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.lbracket contents FStar_Pprint.rbracket))


let soft_begin_end_with_nesting : FStar_Pprint.document  ->  FStar_Pprint.document = (fun contents -> (let _0_337 = (str "begin")
in (let _0_336 = (str "end")
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1") _0_337 contents _0_336))))


let separate_map_or_flow = (fun sep f l -> (match (((FStar_List.length l) < (Prims.parse_int "10"))) with
| true -> begin
(FStar_Pprint.separate_map sep f l)
end
| uu____192 -> begin
(FStar_Pprint.flow_map sep f l)
end))


let doc_of_fsdoc : (Prims.string * (Prims.string * Prims.string) Prims.list)  ->  FStar_Pprint.document = (fun uu____200 -> (match (uu____200) with
| (comment, keywords) -> begin
(FStar_Pprint.group (FStar_Pprint.concat (let _0_345 = (str comment)
in (let _0_344 = (let _0_343 = (let _0_342 = (FStar_Pprint.separate_map FStar_Pprint.comma (fun uu____216 -> (match (uu____216) with
| (k, v) -> begin
(FStar_Pprint.concat (let _0_341 = (str k)
in (let _0_340 = (let _0_339 = (let _0_338 = (str v)
in (_0_338)::[])
in (FStar_Pprint.rarrow)::_0_339)
in (_0_341)::_0_340)))
end)) keywords)
in (_0_342)::[])
in (FStar_Pprint.space)::_0_343)
in (_0_345)::_0_344))))
end))


let is_unit : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____224 = (unparen e).FStar_Parser_AST.tm
in (match (uu____224) with
| FStar_Parser_AST.Const (FStar_Const.Const_unit) -> begin
true
end
| uu____225 -> begin
false
end)))


let matches_var : FStar_Parser_AST.term  ->  FStar_Ident.ident  ->  Prims.bool = (fun t x -> (

let uu____232 = (unparen t).FStar_Parser_AST.tm
in (match (uu____232) with
| FStar_Parser_AST.Var (y) -> begin
(x.FStar_Ident.idText = (FStar_Ident.text_of_lid y))
end
| uu____234 -> begin
false
end)))


let is_tuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Syntax_Util.is_tuple_data_lid'


let is_dtuple_constructor : FStar_Ident.lident  ->  Prims.bool = FStar_Syntax_Util.is_dtuple_data_lid'


let is_list_structure : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun cons_lid nil_lid -> (

let rec aux = (fun e -> (

let uu____251 = (unparen e).FStar_Parser_AST.tm
in (match (uu____251) with
| FStar_Parser_AST.Construct (lid, []) -> begin
(FStar_Ident.lid_equals lid nil_lid)
end
| FStar_Parser_AST.Construct (lid, (uu____259)::((e2, uu____261))::[]) -> begin
((FStar_Ident.lid_equals lid cons_lid) && (aux e2))
end
| uu____273 -> begin
false
end)))
in aux))


let is_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Syntax_Const.cons_lid FStar_Syntax_Const.nil_lid)


let is_lex_list : FStar_Parser_AST.term  ->  Prims.bool = (is_list_structure FStar_Syntax_Const.lexcons_lid FStar_Syntax_Const.lextop_lid)


let rec extract_from_list : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (

let uu____282 = (unparen e).FStar_Parser_AST.tm
in (match (uu____282) with
| FStar_Parser_AST.Construct (uu____284, []) -> begin
[]
end
| FStar_Parser_AST.Construct (uu____290, ((e1, FStar_Parser_AST.Nothing))::((e2, FStar_Parser_AST.Nothing))::[]) -> begin
(let _0_346 = (extract_from_list e2)
in (e1)::_0_346)
end
| uu____302 -> begin
(failwith (let _0_347 = (FStar_Parser_AST.term_to_string e)
in (FStar_Util.format1 "Not a list %s" _0_347)))
end)))


let is_array : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____307 = (unparen e).FStar_Parser_AST.tm
in (match (uu____307) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (lid); FStar_Parser_AST.range = uu____309; FStar_Parser_AST.level = uu____310}, l, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals lid FStar_Syntax_Const.array_mk_array_lid) && (is_list l))
end
| uu____312 -> begin
false
end)))


let rec is_ref_set : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (

let uu____316 = (unparen e).FStar_Parser_AST.tm
in (match (uu____316) with
| FStar_Parser_AST.Var (maybe_empty_lid) -> begin
(FStar_Ident.lid_equals maybe_empty_lid FStar_Syntax_Const.tset_empty)
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_singleton_lid); FStar_Parser_AST.range = uu____319; FStar_Parser_AST.level = uu____320}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_ref_lid); FStar_Parser_AST.range = uu____322; FStar_Parser_AST.level = uu____323}, e, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____325; FStar_Parser_AST.level = uu____326}, FStar_Parser_AST.Nothing) -> begin
((FStar_Ident.lid_equals maybe_singleton_lid FStar_Syntax_Const.tset_singleton) && (FStar_Ident.lid_equals maybe_ref_lid FStar_Syntax_Const.heap_ref))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (maybe_union_lid); FStar_Parser_AST.range = uu____328; FStar_Parser_AST.level = uu____329}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____331; FStar_Parser_AST.level = uu____332}, e2, FStar_Parser_AST.Nothing) -> begin
(((FStar_Ident.lid_equals maybe_union_lid FStar_Syntax_Const.tset_union) && (is_ref_set e1)) && (is_ref_set e2))
end
| uu____334 -> begin
false
end)))


let rec extract_from_ref_set : FStar_Parser_AST.term  ->  FStar_Parser_AST.term Prims.list = (fun e -> (

let uu____339 = (unparen e).FStar_Parser_AST.tm
in (match (uu____339) with
| FStar_Parser_AST.Var (uu____341) -> begin
[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (uu____342); FStar_Parser_AST.range = uu____343; FStar_Parser_AST.level = uu____344}, {FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (uu____345); FStar_Parser_AST.range = uu____346; FStar_Parser_AST.level = uu____347}, e, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____349; FStar_Parser_AST.level = uu____350}, FStar_Parser_AST.Nothing) -> begin
(e)::[]
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (uu____351); FStar_Parser_AST.range = uu____352; FStar_Parser_AST.level = uu____353}, e1, FStar_Parser_AST.Nothing); FStar_Parser_AST.range = uu____355; FStar_Parser_AST.level = uu____356}, e2, FStar_Parser_AST.Nothing) -> begin
(let _0_349 = (extract_from_ref_set e1)
in (let _0_348 = (extract_from_ref_set e2)
in (FStar_List.append _0_349 _0_348)))
end
| uu____358 -> begin
(failwith (let _0_350 = (FStar_Parser_AST.term_to_string e)
in (FStar_Util.format1 "Not a ref set %s" _0_350)))
end)))


let is_general_application : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (not (((is_array e) || (is_ref_set e)))))


let is_general_construction : FStar_Parser_AST.term  ->  Prims.bool = (fun e -> (not (((is_list e) || (is_lex_list e)))))


let is_general_prefix_op : Prims.string  ->  Prims.bool = (fun op -> (op <> "~"))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun e -> (

let rec aux = (fun e acc -> (

let uu____395 = (unparen e).FStar_Parser_AST.tm
in (match (uu____395) with
| FStar_Parser_AST.App (head, arg, imp) -> begin
(aux head ((((arg), (imp)))::acc))
end
| uu____406 -> begin
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
| uu____415 -> begin
false
end))


let uu___is_Right : associativity  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Right -> begin
true
end
| uu____419 -> begin
false
end))


let uu___is_NonAssoc : associativity  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NonAssoc -> begin
true
end
| uu____423 -> begin
false
end))


type token =
(FStar_Char.char, Prims.string) FStar_Util.either


type associativity_level =
(associativity * token Prims.list)


let token_to_string : (FStar_BaseTypes.char, Prims.string) FStar_Util.either  ->  Prims.string = (fun uu___115_433 -> (match (uu___115_433) with
| FStar_Util.Inl (c) -> begin
(Prims.strcat (FStar_Util.string_of_char c) ".*")
end
| FStar_Util.Inr (s) -> begin
s
end))


let matches_token : Prims.string  ->  (FStar_Char.char, Prims.string) FStar_Util.either  ->  Prims.bool = (fun s uu___116_445 -> (match (uu___116_445) with
| FStar_Util.Inl (c) -> begin
(let _0_351 = (FStar_String.get s (Prims.parse_int "0"))
in (_0_351 = c))
end
| FStar_Util.Inr (s') -> begin
(s = s')
end))


let matches_level = (fun s uu____466 -> (match (uu____466) with
| (assoc_levels, tokens) -> begin
(let _0_352 = (FStar_List.tryFind (matches_token s) tokens)
in (_0_352 <> None))
end))


let opinfix4 = (fun uu____494 -> ((Right), ((FStar_Util.Inr ("**"))::[])))


let opinfix3 = (fun uu____509 -> ((Left), ((FStar_Util.Inl ('*'))::(FStar_Util.Inl ('/'))::(FStar_Util.Inl ('%'))::[])))


let opinfix2 = (fun uu____528 -> ((Left), ((FStar_Util.Inl ('+'))::(FStar_Util.Inl ('-'))::[])))


let minus_lvl = (fun uu____545 -> ((Left), ((FStar_Util.Inr ("-"))::[])))


let opinfix1 = (fun uu____560 -> ((Right), ((FStar_Util.Inl ('@'))::(FStar_Util.Inl ('^'))::[])))


let pipe_right = (fun uu____577 -> ((Left), ((FStar_Util.Inr ("|>"))::[])))


let opinfix0d = (fun uu____592 -> ((Left), ((FStar_Util.Inl ('$'))::[])))


let opinfix0c = (fun uu____607 -> ((Left), ((FStar_Util.Inl ('='))::(FStar_Util.Inl ('<'))::(FStar_Util.Inl ('>'))::[])))


let equal = (fun uu____626 -> ((Left), ((FStar_Util.Inr ("="))::[])))


let opinfix0b = (fun uu____641 -> ((Left), ((FStar_Util.Inl ('&'))::[])))


let opinfix0a = (fun uu____656 -> ((Left), ((FStar_Util.Inl ('|'))::[])))


let colon_equals = (fun uu____671 -> ((NonAssoc), ((FStar_Util.Inr (":="))::[])))


let amp = (fun uu____686 -> ((Right), ((FStar_Util.Inr ("&"))::[])))


let colon_colon = (fun uu____701 -> ((Right), ((FStar_Util.Inr ("::"))::[])))


let level_associativity_spec : (associativity * (FStar_Char.char, Prims.string) FStar_Util.either Prims.list) Prims.list = ((opinfix4 ()))::((opinfix3 ()))::((opinfix2 ()))::((opinfix1 ()))::((pipe_right ()))::((opinfix0d ()))::((opinfix0c ()))::((opinfix0b ()))::((opinfix0a ()))::((colon_equals ()))::((amp ()))::((colon_colon ()))::[]


let level_table : ((Prims.int * Prims.int * Prims.int) * (FStar_Char.char, Prims.string) FStar_Util.either Prims.list) Prims.list = (

let levels_from_associativity = (fun l uu___117_798 -> (match (uu___117_798) with
| Left -> begin
((l), (l), ((l - (Prims.parse_int "1"))))
end
| Right -> begin
(((l - (Prims.parse_int "1"))), (l), (l))
end
| NonAssoc -> begin
((l), (l), (l))
end))
in (FStar_List.mapi (fun i uu____816 -> (match (uu____816) with
| (assoc, tokens) -> begin
(((levels_from_associativity i assoc)), (tokens))
end)) level_associativity_spec))


let assign_levels : associativity_level Prims.list  ->  Prims.string  ->  (Prims.int * Prims.int * Prims.int) = (fun token_associativity_spec s -> (

let uu____858 = (FStar_List.tryFind (matches_level s) level_table)
in (match (uu____858) with
| Some (assoc_levels, uu____883) -> begin
assoc_levels
end
| uu____904 -> begin
(failwith (Prims.strcat "Unrecognized operator " s))
end)))


let max : Prims.int  ->  Prims.int  ->  Prims.int = (fun k1 k2 -> (match ((k1 > k2)) with
| true -> begin
k1
end
| uu____923 -> begin
k2
end))


let max_level = (fun l -> (

let find_level_and_max = (fun n level -> (

let uu____960 = (FStar_List.tryFind (fun uu____978 -> (match (uu____978) with
| (uu____987, tokens) -> begin
(tokens = (Prims.snd level))
end)) level_table)
in (match (uu____960) with
| Some ((uu____1007, l, uu____1009), uu____1010) -> begin
(max n l)
end
| None -> begin
(failwith (let _0_354 = (let _0_353 = (FStar_List.map token_to_string (Prims.snd level))
in (FStar_String.concat "," _0_353))
in (FStar_Util.format1 "Undefined associativity level %s" _0_354)))
end)))
in (FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l)))


let levels : Prims.string  ->  (Prims.int * Prims.int * Prims.int) = (assign_levels level_associativity_spec)


let operatorInfix0ad12 = (fun uu____1059 -> ((opinfix0a ()))::((opinfix0b ()))::((opinfix0c ()))::((opinfix0d ()))::((opinfix1 ()))::((opinfix2 ()))::[])


let is_operatorInfix0ad12 : Prims.string  ->  Prims.bool = (fun op -> (let _0_355 = (FStar_List.tryFind (matches_level op) (operatorInfix0ad12 ()))
in (_0_355 <> None)))


let is_operatorInfix34 : Prims.string  ->  Prims.bool = (

let opinfix34 = ((opinfix3 ()))::((opinfix4 ()))::[]
in (fun op -> (let _0_356 = (FStar_List.tryFind (matches_level op) opinfix34)
in (_0_356 <> None))))


let comment_stack : (Prims.string * FStar_Range.range) Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let with_comment = (fun printer tm tmrange -> (

let rec comments_before_pos = (fun acc print_pos lookahead_pos -> (

let uu____1200 = (FStar_ST.read comment_stack)
in (match (uu____1200) with
| [] -> begin
((acc), (false))
end
| ((comment, crange))::cs -> begin
(

let uu____1221 = (FStar_Range.range_before_pos crange print_pos)
in (match (uu____1221) with
| true -> begin
((FStar_ST.write comment_stack cs);
(let _0_359 = (let _0_358 = (let _0_357 = (str comment)
in (FStar_Pprint.op_Hat_Hat _0_357 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat acc _0_358))
in (comments_before_pos _0_359 print_pos lookahead_pos));
)
end
| uu____1230 -> begin
(let _0_360 = (FStar_Range.range_before_pos crange lookahead_pos)
in ((acc), (_0_360)))
end))
end)))
in (

let uu____1231 = (let _0_362 = (FStar_Range.end_of_line (FStar_Range.start_of_range tmrange))
in (let _0_361 = (FStar_Range.end_of_range tmrange)
in (comments_before_pos FStar_Pprint.empty _0_362 _0_361)))
in (match (uu____1231) with
| (comments, has_lookahead) -> begin
(

let printed_e = (printer tm)
in (

let comments = (match (has_lookahead) with
| true -> begin
(

let pos = (FStar_Range.end_of_range tmrange)
in (Prims.fst (comments_before_pos comments pos pos)))
end
| uu____1239 -> begin
comments
end)
in (FStar_Pprint.group (FStar_Pprint.op_Hat_Hat comments printed_e))))
end))))


let rec p_decl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (FStar_Pprint.group (let _0_369 = (FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc)
in (let _0_368 = (let _0_367 = (p_attributes d.FStar_Parser_AST.attrs)
in (let _0_366 = (let _0_365 = (p_qualifiers d.FStar_Parser_AST.quals)
in (let _0_364 = (let _0_363 = (p_rawDecl d)
in (FStar_Pprint.op_Hat_Hat (match ((d.FStar_Parser_AST.quals = [])) with
| true -> begin
FStar_Pprint.empty
end
| uu____1481 -> begin
break1
end) _0_363))
in (FStar_Pprint.op_Hat_Hat _0_365 _0_364)))
in (FStar_Pprint.op_Hat_Hat _0_367 _0_366)))
in (FStar_Pprint.op_Hat_Hat _0_369 _0_368)))))
and p_attributes : FStar_Parser_AST.attributes_  ->  FStar_Pprint.document = (fun attrs -> (let _0_372 = (let _0_370 = (str "@")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket _0_370))
in (let _0_371 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline)
in (FStar_Pprint.surround_separate_map (Prims.parse_int "0") (Prims.parse_int "2") FStar_Pprint.empty _0_372 FStar_Pprint.space _0_371 p_atomicTerm attrs))))
and p_fsdoc : FStar_Parser_AST.fsdoc  ->  FStar_Pprint.document = (fun uu____1483 -> (match (uu____1483) with
| (doc, kwd_args) -> begin
(

let kwd_args_doc = (match (kwd_args) with
| [] -> begin
FStar_Pprint.empty
end
| kwd_args -> begin
(

let process_kwd_arg = (fun uu____1504 -> (match (uu____1504) with
| (kwd, arg) -> begin
(let _0_377 = (str "@")
in (let _0_376 = (let _0_375 = (str kwd)
in (let _0_374 = (let _0_373 = (str arg)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_373))
in (FStar_Pprint.op_Hat_Hat _0_375 _0_374)))
in (FStar_Pprint.op_Hat_Hat _0_377 _0_376)))
end))
in (let _0_379 = (let _0_378 = (FStar_Pprint.separate_map FStar_Pprint.hardline process_kwd_arg kwd_args)
in (FStar_Pprint.op_Hat_Hat _0_378 FStar_Pprint.hardline))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline _0_379)))
end)
in (let _0_387 = (let _0_386 = (let _0_385 = (let _0_384 = (let _0_383 = (str doc)
in (let _0_382 = (let _0_381 = (let _0_380 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _0_380))
in (FStar_Pprint.op_Hat_Hat kwd_args_doc _0_381))
in (FStar_Pprint.op_Hat_Hat _0_383 _0_382)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _0_384))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.star _0_385))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _0_386))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline _0_387)))
end))
and p_rawDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Open (uid) -> begin
(FStar_Pprint.group (let _0_389 = (str "open")
in (let _0_388 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat _0_389 _0_388))))
end
| FStar_Parser_AST.Include (uid) -> begin
(FStar_Pprint.group (let _0_391 = (str "include")
in (let _0_390 = (p_quident uid)
in (FStar_Pprint.op_Hat_Slash_Hat _0_391 _0_390))))
end
| FStar_Parser_AST.ModuleAbbrev (uid1, uid2) -> begin
(let _0_398 = (let _0_396 = (str "module")
in (let _0_395 = (let _0_394 = (let _0_393 = (p_uident uid1)
in (let _0_392 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _0_393 _0_392)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_394))
in (FStar_Pprint.op_Hat_Hat _0_396 _0_395)))
in (let _0_397 = (p_quident uid2)
in (op_Hat_Slash_Plus_Hat _0_398 _0_397)))
end
| FStar_Parser_AST.TopLevelModule (uid) -> begin
(FStar_Pprint.group (let _0_401 = (str "module")
in (let _0_400 = (let _0_399 = (p_quident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_399))
in (FStar_Pprint.op_Hat_Hat _0_401 _0_400))))
end
| FStar_Parser_AST.KindAbbrev (uu____1517) -> begin
(failwith "Deprecated, please stop throwing your old stuff at me !")
end
| FStar_Parser_AST.Tycon (true, ((FStar_Parser_AST.TyconAbbrev (uid, tpars, None, t), None))::[]) -> begin
(

let effect_prefix_doc = (let _0_404 = (str "effect")
in (let _0_403 = (let _0_402 = (p_uident uid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_402))
in (FStar_Pprint.op_Hat_Hat _0_404 _0_403)))
in (let _0_407 = (let _0_405 = (p_typars tpars)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") effect_prefix_doc _0_405 FStar_Pprint.equals))
in (let _0_406 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _0_407 _0_406))))
end
| FStar_Parser_AST.Tycon (false, tcdefs) -> begin
(let _0_409 = (str "type")
in (let _0_408 = (str "and")
in (precede_break_separate_map _0_409 _0_408 p_fsdocTypeDeclPairs tcdefs)))
end
| FStar_Parser_AST.TopLevelLet (q, lbs) -> begin
(

let let_doc = (let _0_411 = (str "let")
in (let _0_410 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat _0_411 _0_410)))
in (let _0_412 = (str "and")
in (precede_break_separate_map let_doc _0_412 p_letbinding lbs)))
end
| FStar_Parser_AST.Val (lid, t) -> begin
(let _0_419 = (let _0_417 = (str "val")
in (let _0_416 = (let _0_415 = (let _0_414 = (p_lident lid)
in (let _0_413 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat _0_414 _0_413)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_415))
in (FStar_Pprint.op_Hat_Hat _0_417 _0_416)))
in (let _0_418 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _0_419 _0_418)))
end
| FStar_Parser_AST.Assume (id, t) -> begin
(

let decl_keyword = (

let uu____1568 = (let _0_420 = (FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_All.pipe_right _0_420 FStar_Util.is_upper))
in (match (uu____1568) with
| true -> begin
FStar_Pprint.empty
end
| uu____1569 -> begin
(let _0_421 = (str "val")
in (FStar_Pprint.op_Hat_Hat _0_421 FStar_Pprint.space))
end))
in (let _0_426 = (let _0_424 = (let _0_423 = (p_ident id)
in (let _0_422 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon)
in (FStar_Pprint.op_Hat_Hat _0_423 _0_422)))
in (FStar_Pprint.op_Hat_Hat decl_keyword _0_424))
in (let _0_425 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _0_426 _0_425))))
end
| FStar_Parser_AST.Exception (uid, t_opt) -> begin
(let _0_433 = (str "exception")
in (let _0_432 = (let _0_431 = (let _0_430 = (p_uident uid)
in (let _0_429 = (FStar_Pprint.optional (fun t -> (let _0_428 = (str "of")
in (let _0_427 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _0_428 _0_427)))) t_opt)
in (FStar_Pprint.op_Hat_Hat _0_430 _0_429)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_431))
in (FStar_Pprint.op_Hat_Hat _0_433 _0_432)))
end
| FStar_Parser_AST.NewEffect (ne) -> begin
(let _0_436 = (str "new_effect")
in (let _0_435 = (let _0_434 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_434))
in (FStar_Pprint.op_Hat_Hat _0_436 _0_435)))
end
| FStar_Parser_AST.SubEffect (se) -> begin
(let _0_439 = (str "sub_effect")
in (let _0_438 = (let _0_437 = (p_subEffect se)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_437))
in (FStar_Pprint.op_Hat_Hat _0_439 _0_438)))
end
| FStar_Parser_AST.NewEffectForFree (ne) -> begin
(let _0_442 = (str "new_effect_for_free")
in (let _0_441 = (let _0_440 = (p_newEffect ne)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_440))
in (FStar_Pprint.op_Hat_Hat _0_442 _0_441)))
end
| FStar_Parser_AST.Pragma (p) -> begin
(p_pragma p)
end
| FStar_Parser_AST.Fsdoc (doc) -> begin
(let _0_443 = (p_fsdoc doc)
in (FStar_Pprint.op_Hat_Hat _0_443 FStar_Pprint.hardline))
end
| FStar_Parser_AST.Main (uu____1580) -> begin
(failwith "*Main declaration* : Is that really still in use ??")
end
| FStar_Parser_AST.Tycon (true, uu____1581) -> begin
(failwith "Effect abbreviation is expected to be defined by an abbreviation")
end))
and p_pragma : FStar_Parser_AST.pragma  ->  FStar_Pprint.document = (fun uu___118_1590 -> (match (uu___118_1590) with
| FStar_Parser_AST.SetOptions (s) -> begin
(let _0_446 = (str "#set-options")
in (let _0_445 = (let _0_444 = (FStar_Pprint.dquotes (str s))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_444))
in (FStar_Pprint.op_Hat_Hat _0_446 _0_445)))
end
| FStar_Parser_AST.ResetOptions (s_opt) -> begin
(let _0_449 = (str "#reset-options")
in (let _0_448 = (FStar_Pprint.optional (fun s -> (let _0_447 = (FStar_Pprint.dquotes (str s))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_447))) s_opt)
in (FStar_Pprint.op_Hat_Hat _0_449 _0_448)))
end
| FStar_Parser_AST.LightOff -> begin
(str "#light \"off\"")
end))
and p_typars : FStar_Parser_AST.binder Prims.list  ->  FStar_Pprint.document = (fun bs -> (p_binders true bs))
and p_fsdocTypeDeclPairs : (FStar_Parser_AST.tycon * FStar_Parser_AST.fsdoc Prims.option)  ->  FStar_Pprint.document = (fun uu____1597 -> (match (uu____1597) with
| (typedecl, fsdoc_opt) -> begin
(let _0_451 = (FStar_Pprint.optional p_fsdoc fsdoc_opt)
in (let _0_450 = (p_typeDecl typedecl)
in (FStar_Pprint.op_Hat_Hat _0_451 _0_450)))
end))
and p_typeDecl : FStar_Parser_AST.tycon  ->  FStar_Pprint.document = (fun uu___119_1605 -> (match (uu___119_1605) with
| FStar_Parser_AST.TyconAbstract (lid, bs, typ_opt) -> begin
(

let empty' = (fun uu____1616 -> FStar_Pprint.empty)
in (p_typeDeclPrefix lid bs typ_opt empty'))
end
| FStar_Parser_AST.TyconAbbrev (lid, bs, typ_opt, t) -> begin
(

let f = (fun uu____1628 -> (let _0_452 = (p_typ t)
in (prefix2 FStar_Pprint.equals _0_452)))
in (p_typeDeclPrefix lid bs typ_opt f))
end
| FStar_Parser_AST.TyconRecord (lid, bs, typ_opt, record_field_decls) -> begin
(

let p_recordFieldAndComments = (fun uu____1654 -> (match (uu____1654) with
| (lid, t, doc_opt) -> begin
(let _0_453 = (FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range)
in (with_comment p_recordFieldDecl ((lid), (t), (doc_opt)) _0_453))
end))
in (

let p_fields = (fun uu____1672 -> (let _0_456 = (let _0_455 = (braces_with_nesting (let _0_454 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (FStar_Pprint.separate_map _0_454 p_recordFieldAndComments record_field_decls)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_455))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.equals _0_456)))
in (p_typeDeclPrefix lid bs typ_opt p_fields)))
end
| FStar_Parser_AST.TyconVariant (lid, bs, typ_opt, ct_decls) -> begin
(

let p_constructorBranchAndComments = (fun uu____1708 -> (match (uu____1708) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let range = (FStar_Range.extend_to_end_of_line (let _0_457 = (FStar_Util.map_opt t_opt (fun t -> t.FStar_Parser_AST.range))
in (FStar_Util.dflt uid.FStar_Ident.idRange _0_457)))
in (

let p_constructorBranch = (fun decl -> (FStar_Pprint.group (let _0_459 = (let _0_458 = (p_constructorDecl decl)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_458))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar _0_459))))
in (with_comment p_constructorBranch ((uid), (t_opt), (doc_opt), (use_of)) range)))
end))
in (

let datacon_doc = (fun uu____1752 -> (FStar_Pprint.group (FStar_Pprint.separate_map break1 p_constructorBranchAndComments ct_decls)))
in (p_typeDeclPrefix lid bs typ_opt (fun uu____1759 -> (let _0_460 = (datacon_doc ())
in (prefix2 FStar_Pprint.equals _0_460))))))
end))
and p_typeDeclPrefix : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.knd Prims.option  ->  (Prims.unit  ->  FStar_Pprint.document)  ->  FStar_Pprint.document = (fun lid bs typ_opt cont -> (match (((bs = []) && (typ_opt = None))) with
| true -> begin
(let _0_463 = (p_ident lid)
in (let _0_462 = (let _0_461 = (cont ())
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_461))
in (FStar_Pprint.op_Hat_Hat _0_463 _0_462)))
end
| uu____1770 -> begin
(

let binders_doc = (let _0_468 = (p_typars bs)
in (let _0_467 = (FStar_Pprint.optional (fun t -> (let _0_466 = (let _0_465 = (let _0_464 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_464))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _0_465))
in (FStar_Pprint.op_Hat_Hat break1 _0_466))) typ_opt)
in (FStar_Pprint.op_Hat_Hat _0_468 _0_467)))
in (let _0_470 = (p_ident lid)
in (let _0_469 = (cont ())
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _0_470 binders_doc _0_469))))
end))
and p_recordFieldDecl : (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc Prims.option)  ->  FStar_Pprint.document = (fun uu____1773 -> (match (uu____1773) with
| (lid, t, doc_opt) -> begin
(FStar_Pprint.group (let _0_475 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (let _0_474 = (let _0_473 = (p_lident lid)
in (let _0_472 = (let _0_471 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _0_471))
in (FStar_Pprint.op_Hat_Hat _0_473 _0_472)))
in (FStar_Pprint.op_Hat_Hat _0_475 _0_474))))
end))
and p_constructorDecl : (FStar_Ident.ident * FStar_Parser_AST.term Prims.option * FStar_Parser_AST.fsdoc Prims.option * Prims.bool)  ->  FStar_Pprint.document = (fun uu____1783 -> (match (uu____1783) with
| (uid, t_opt, doc_opt, use_of) -> begin
(

let sep = (match (use_of) with
| true -> begin
(str "of")
end
| uu____1799 -> begin
FStar_Pprint.colon
end)
in (

let uid_doc = (p_uident uid)
in (let _0_480 = (FStar_Pprint.optional p_fsdoc doc_opt)
in (let _0_479 = (default_or_map uid_doc (fun t -> (let _0_478 = (let _0_476 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep)
in (FStar_Pprint.op_Hat_Hat uid_doc _0_476))
in (let _0_477 = (p_typ t)
in (op_Hat_Slash_Plus_Hat _0_478 _0_477)))) t_opt)
in (FStar_Pprint.op_Hat_Hat _0_480 _0_479)))))
end))
and p_letbinding : (FStar_Parser_AST.pattern * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun uu____1802 -> (match (uu____1802) with
| (pat, e) -> begin
(

let pat_doc = (

let uu____1808 = (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, t) -> begin
(let _0_484 = (let _0_483 = (FStar_Pprint.group (let _0_482 = (let _0_481 = (p_tmArrow p_tmNoEq t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_481))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _0_482)))
in (FStar_Pprint.op_Hat_Hat break1 _0_483))
in ((pat), (_0_484)))
end
| uu____1815 -> begin
((pat), (FStar_Pprint.empty))
end)
in (match (uu____1808) with
| (pat, ascr_doc) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____1819); FStar_Parser_AST.prange = uu____1820}, pats) -> begin
(let _0_487 = (p_lident x)
in (let _0_486 = (let _0_485 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Hat _0_485 ascr_doc))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _0_487 _0_486 FStar_Pprint.equals)))
end
| uu____1826 -> begin
(FStar_Pprint.group (let _0_489 = (p_tuplePattern pat)
in (let _0_488 = (FStar_Pprint.op_Hat_Slash_Hat ascr_doc FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _0_489 _0_488))))
end)
end))
in (let _0_490 = (p_term e)
in (prefix2 pat_doc _0_490)))
end))
and p_newEffect : FStar_Parser_AST.effect_decl  ->  FStar_Pprint.document = (fun uu___120_1827 -> (match (uu___120_1827) with
| FStar_Parser_AST.RedefineEffect (lid, bs, t) -> begin
(p_effectRedefinition lid bs t)
end
| FStar_Parser_AST.DefineEffect (lid, bs, t, eff_decls, action_decls) -> begin
(p_effectDefinition lid bs t eff_decls action_decls)
end))
and p_effectRedefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun uid bs t -> (let _0_494 = (p_uident uid)
in (let _0_493 = (p_binders true bs)
in (let _0_492 = (let _0_491 = (p_simpleTerm t)
in (prefix2 FStar_Pprint.equals _0_491))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _0_494 _0_493 _0_492)))))
and p_effectDefinition : FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun uid bs t eff_decls action_decls -> (braces_with_nesting (let _0_504 = (FStar_Pprint.group (let _0_498 = (p_uident uid)
in (let _0_497 = (p_binders true bs)
in (let _0_496 = (let _0_495 = (p_typ t)
in (prefix2 FStar_Pprint.colon _0_495))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _0_498 _0_497 _0_496)))))
in (let _0_503 = (let _0_502 = (let _0_500 = (str "with")
in (let _0_499 = (separate_break_map FStar_Pprint.semi p_effectDecl eff_decls)
in (prefix2 _0_500 _0_499)))
in (let _0_501 = (p_actionDecls action_decls)
in (FStar_Pprint.op_Hat_Hat _0_502 _0_501)))
in (FStar_Pprint.op_Hat_Slash_Hat _0_504 _0_503)))))
and p_actionDecls : FStar_Parser_AST.decl Prims.list  ->  FStar_Pprint.document = (fun uu___121_1856 -> (match (uu___121_1856) with
| [] -> begin
FStar_Pprint.empty
end
| l -> begin
(let _0_507 = (let _0_506 = (str "and actions")
in (let _0_505 = (separate_break_map FStar_Pprint.semi p_effectDecl l)
in (prefix2 _0_506 _0_505)))
in (FStar_Pprint.op_Hat_Hat break1 _0_507))
end))
and p_effectDecl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (false, ((FStar_Parser_AST.TyconAbbrev (lid, [], None, e), None))::[]) -> begin
(let _0_511 = (let _0_509 = (p_lident lid)
in (let _0_508 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _0_509 _0_508)))
in (let _0_510 = (p_simpleTerm e)
in (prefix2 _0_511 _0_510)))
end
| uu____1876 -> begin
(failwith (let _0_512 = (FStar_Parser_AST.decl_to_string d)
in (FStar_Util.format1 "Not a declaration of an effect member... or at least I hope so : %s" _0_512)))
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

let p_lift = (fun uu____1909 -> (match (uu____1909) with
| (kwd, t) -> begin
(let _0_516 = (let _0_514 = (str kwd)
in (let _0_513 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals)
in (FStar_Pprint.op_Hat_Hat _0_514 _0_513)))
in (let _0_515 = (p_simpleTerm t)
in (prefix2 _0_516 _0_515)))
end))
in (separate_break_map FStar_Pprint.semi p_lift lifts)))
in (let _0_524 = (let _0_521 = (let _0_519 = (p_quident lift.FStar_Parser_AST.msource)
in (let _0_518 = (let _0_517 = (str "~>")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_517))
in (FStar_Pprint.op_Hat_Hat _0_519 _0_518)))
in (let _0_520 = (p_quident lift.FStar_Parser_AST.mdest)
in (prefix2 _0_521 _0_520)))
in (let _0_523 = (let _0_522 = (braces_with_nesting lift_op_doc)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_522))
in (FStar_Pprint.op_Hat_Hat _0_524 _0_523)))))
and p_qualifier : FStar_Parser_AST.qualifier  ->  FStar_Pprint.document = (fun uu___122_1916 -> (match (uu___122_1916) with
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
and p_qualifiers : FStar_Parser_AST.qualifiers  ->  FStar_Pprint.document = (fun qs -> (FStar_Pprint.group (FStar_Pprint.separate_map break1 p_qualifier qs)))
and p_letqualifier : FStar_Parser_AST.let_qualifier  ->  FStar_Pprint.document = (fun uu___123_1918 -> (match (uu___123_1918) with
| FStar_Parser_AST.Rec -> begin
(let _0_525 = (str "rec")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_525))
end
| FStar_Parser_AST.Mutable -> begin
(let _0_526 = (str "mutable")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_526))
end
| FStar_Parser_AST.NoLetQualifier -> begin
FStar_Pprint.empty
end))
and p_aqual : FStar_Parser_AST.arg_qualifier  ->  FStar_Pprint.document = (fun uu___124_1919 -> (match (uu___124_1919) with
| FStar_Parser_AST.Implicit -> begin
(str "#")
end
| FStar_Parser_AST.Equality -> begin
(str "$")
end))
and p_disjunctivePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr (pats) -> begin
(FStar_Pprint.group (let _0_528 = (let _0_527 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space)
in (FStar_Pprint.op_Hat_Hat break1 _0_527))
in (FStar_Pprint.separate_map _0_528 p_tuplePattern pats)))
end
| uu____1923 -> begin
(p_tuplePattern p)
end))
and p_tuplePattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTuple (pats, false) -> begin
(FStar_Pprint.group (let _0_529 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map _0_529 p_constructorPattern pats)))
end
| uu____1928 -> begin
(p_constructorPattern p)
end))
and p_constructorPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (maybe_cons_lid); FStar_Parser_AST.prange = uu____1931}, (hd)::(tl)::[]) when (FStar_Ident.lid_equals maybe_cons_lid FStar_Syntax_Const.cons_lid) -> begin
(let _0_532 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon)
in (let _0_531 = (p_constructorPattern hd)
in (let _0_530 = (p_constructorPattern tl)
in (infix0 _0_532 _0_531 _0_530))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (uid); FStar_Parser_AST.prange = uu____1936}, pats) -> begin
(let _0_534 = (p_quident uid)
in (let _0_533 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (prefix2 _0_534 _0_533)))
end
| uu____1940 -> begin
(p_atomicPattern p)
end))
and p_atomicPattern : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat, t) -> begin
(

let uu____1944 = (let _0_535 = (unparen t).FStar_Parser_AST.tm
in ((pat.FStar_Parser_AST.pat), (_0_535)))
in (match (uu____1944) with
| (FStar_Parser_AST.PatVar (lid, aqual), FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t); FStar_Parser_AST.brange = uu____1951; FStar_Parser_AST.blevel = uu____1952; FStar_Parser_AST.aqual = uu____1953}, phi)) when (lid.FStar_Ident.idText = lid'.FStar_Ident.idText) -> begin
(soft_parens_with_nesting (let _0_536 = (p_ident lid)
in (p_refinement aqual _0_536 t phi)))
end
| (FStar_Parser_AST.PatWild, FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t); FStar_Parser_AST.brange = uu____1958; FStar_Parser_AST.blevel = uu____1959; FStar_Parser_AST.aqual = uu____1960}, phi)) -> begin
(soft_parens_with_nesting (p_refinement None FStar_Pprint.underscore t phi))
end
| uu____1962 -> begin
(soft_parens_with_nesting (let _0_541 = (p_tuplePattern pat)
in (let _0_540 = (let _0_539 = (FStar_Pprint.break_ (Prims.parse_int "0"))
in (let _0_538 = (let _0_537 = (p_typ t)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _0_537))
in (FStar_Pprint.op_Hat_Hat _0_539 _0_538)))
in (FStar_Pprint.op_Hat_Hat _0_541 _0_540))))
end))
end
| FStar_Parser_AST.PatList (pats) -> begin
(let _0_542 = (separate_break_map FStar_Pprint.semi p_tuplePattern pats)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket _0_542 FStar_Pprint.rbracket))
end
| FStar_Parser_AST.PatRecord (pats) -> begin
(

let p_recordFieldPat = (fun uu____1976 -> (match (uu____1976) with
| (lid, pat) -> begin
(let _0_544 = (p_qlident lid)
in (let _0_543 = (p_tuplePattern pat)
in (infix2 FStar_Pprint.equals _0_544 _0_543)))
end))
in (soft_braces_with_nesting (separate_break_map FStar_Pprint.semi p_recordFieldPat pats)))
end
| FStar_Parser_AST.PatTuple (pats, true) -> begin
(let _0_547 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (let _0_546 = (separate_break_map FStar_Pprint.comma p_constructorPattern pats)
in (let _0_545 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _0_547 _0_546 _0_545))))
end
| FStar_Parser_AST.PatTvar (tv, arg_qualifier_opt) -> begin
(p_tvar tv)
end
| FStar_Parser_AST.PatOp (op) -> begin
(let _0_551 = (let _0_550 = (let _0_549 = (str op)
in (let _0_548 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat _0_549 _0_548)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_550))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _0_551))
end
| FStar_Parser_AST.PatWild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.PatConst (c) -> begin
(p_constant c)
end
| FStar_Parser_AST.PatVar (lid, aqual) -> begin
(let _0_553 = (FStar_Pprint.optional p_aqual aqual)
in (let _0_552 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat _0_553 _0_552)))
end
| FStar_Parser_AST.PatName (uid) -> begin
(p_quident uid)
end
| FStar_Parser_AST.PatOr (uu____1998) -> begin
(failwith "Inner or pattern !")
end
| (FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (_); FStar_Parser_AST.prange = _}, _)) | (FStar_Parser_AST.PatTuple (_, false)) -> begin
(soft_parens_with_nesting (p_tuplePattern p))
end
| uu____2006 -> begin
(failwith (let _0_554 = (FStar_Parser_AST.pat_to_string p)
in (FStar_Util.format1 "Invalid pattern %s" _0_554)))
end))
and p_binder : Prims.bool  ->  FStar_Parser_AST.binder  ->  FStar_Pprint.document = (fun is_atomic b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (lid) -> begin
(let _0_556 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (let _0_555 = (p_lident lid)
in (FStar_Pprint.op_Hat_Hat _0_556 _0_555)))
end
| FStar_Parser_AST.TVariable (lid) -> begin
(p_lident lid)
end
| FStar_Parser_AST.Annotated (lid, t) -> begin
(

let doc = (

let uu____2014 = (unparen t).FStar_Parser_AST.tm
in (match (uu____2014) with
| FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid', t); FStar_Parser_AST.brange = uu____2017; FStar_Parser_AST.blevel = uu____2018; FStar_Parser_AST.aqual = uu____2019}, phi) when (lid.FStar_Ident.idText = lid'.FStar_Ident.idText) -> begin
(let _0_557 = (p_ident lid)
in (p_refinement b.FStar_Parser_AST.aqual _0_557 t phi))
end
| uu____2021 -> begin
(let _0_564 = (FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual)
in (let _0_563 = (let _0_562 = (p_lident lid)
in (let _0_561 = (let _0_560 = (let _0_559 = (FStar_Pprint.break_ (Prims.parse_int "0"))
in (let _0_558 = (p_tmFormula t)
in (FStar_Pprint.op_Hat_Hat _0_559 _0_558)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _0_560))
in (FStar_Pprint.op_Hat_Hat _0_562 _0_561)))
in (FStar_Pprint.op_Hat_Hat _0_564 _0_563)))
end))
in (match (is_atomic) with
| true -> begin
(FStar_Pprint.group (let _0_565 = (FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _0_565)))
end
| uu____2022 -> begin
(FStar_Pprint.group doc)
end))
end
| FStar_Parser_AST.TAnnotated (uu____2023) -> begin
(failwith "Is this still used ?")
end
| FStar_Parser_AST.NoName (t) -> begin
(

let uu____2027 = (unparen t).FStar_Parser_AST.tm
in (match (uu____2027) with
| FStar_Parser_AST.Refine ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t); FStar_Parser_AST.brange = uu____2029; FStar_Parser_AST.blevel = uu____2030; FStar_Parser_AST.aqual = uu____2031}, phi) -> begin
(match (is_atomic) with
| true -> begin
(FStar_Pprint.group (let _0_567 = (let _0_566 = (p_refinement b.FStar_Parser_AST.aqual FStar_Pprint.underscore t phi)
in (FStar_Pprint.op_Hat_Hat _0_566 FStar_Pprint.rparen))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _0_567)))
end
| uu____2033 -> begin
(FStar_Pprint.group (p_refinement b.FStar_Parser_AST.aqual FStar_Pprint.underscore t phi))
end)
end
| uu____2034 -> begin
(match (is_atomic) with
| true -> begin
(p_atomicTerm t)
end
| uu____2035 -> begin
(p_appTerm t)
end)
end))
end))
and p_refinement : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Pprint.document  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun aqual_opt binder t phi -> (let _0_573 = (FStar_Pprint.optional p_aqual aqual_opt)
in (let _0_572 = (let _0_571 = (let _0_570 = (let _0_569 = (p_appTerm t)
in (let _0_568 = (soft_braces_with_nesting (p_noSeqTerm phi))
in (FStar_Pprint.op_Hat_Hat _0_569 _0_568)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _0_570))
in (FStar_Pprint.op_Hat_Hat binder _0_571))
in (FStar_Pprint.op_Hat_Hat _0_573 _0_572))))
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
| uu____2051 -> begin
(p_lident id)
end))
and p_term : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2053 = (unparen e).FStar_Parser_AST.tm
in (match (uu____2053) with
| FStar_Parser_AST.Seq (e1, e2) -> begin
(let _0_576 = (FStar_Pprint.group (let _0_574 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat _0_574 FStar_Pprint.semi)))
in (let _0_575 = (p_term e2)
in (FStar_Pprint.op_Hat_Slash_Hat _0_576 _0_575)))
end
| uu____2056 -> begin
(FStar_Pprint.group (p_noSeqTerm e))
end)))
and p_noSeqTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_noSeqTerm' e e.FStar_Parser_AST.range))
and p_noSeqTerm' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2059 = (unparen e).FStar_Parser_AST.tm
in (match (uu____2059) with
| FStar_Parser_AST.Ascribed (e, t) -> begin
(FStar_Pprint.group (let _0_580 = (p_tmIff e)
in (let _0_579 = (let _0_578 = (let _0_577 = (p_typ t)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon _0_577))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.langle _0_578))
in (FStar_Pprint.op_Hat_Slash_Hat _0_580 _0_579))))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::(e3)::[]) when (op = ".()<-") -> begin
(FStar_Pprint.group (let _0_587 = (FStar_Pprint.group (let _0_585 = (p_atomicTermNotQUident e1)
in (let _0_584 = (let _0_583 = (let _0_582 = (soft_parens_with_nesting (p_term e2))
in (let _0_581 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat _0_582 _0_581)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _0_583))
in (FStar_Pprint.op_Hat_Hat _0_585 _0_584))))
in (let _0_586 = (jump2 (p_noSeqTerm e3))
in (FStar_Pprint.op_Hat_Hat _0_587 _0_586))))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::(e3)::[]) when (op = ".[]<-") -> begin
(FStar_Pprint.group (let _0_594 = (FStar_Pprint.group (let _0_592 = (p_atomicTermNotQUident e1)
in (let _0_591 = (let _0_590 = (let _0_589 = (soft_brackets_with_nesting (p_term e2))
in (let _0_588 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.larrow)
in (FStar_Pprint.op_Hat_Hat _0_589 _0_588)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _0_590))
in (FStar_Pprint.op_Hat_Hat _0_592 _0_591))))
in (let _0_593 = (jump2 (p_noSeqTerm e3))
in (FStar_Pprint.op_Hat_Hat _0_594 _0_593))))
end
| FStar_Parser_AST.Requires (e, wtf) -> begin
(FStar_Pprint.group (let _0_596 = (str "requires")
in (let _0_595 = (p_typ e)
in (FStar_Pprint.op_Hat_Slash_Hat _0_596 _0_595))))
end
| FStar_Parser_AST.Ensures (e, wtf) -> begin
(FStar_Pprint.group (let _0_598 = (str "ensures")
in (let _0_597 = (p_typ e)
in (FStar_Pprint.op_Hat_Slash_Hat _0_598 _0_597))))
end
| FStar_Parser_AST.Attributes (es) -> begin
(FStar_Pprint.group (let _0_600 = (str "attributes")
in (let _0_599 = (FStar_Pprint.separate_map break1 p_atomicTerm es)
in (FStar_Pprint.op_Hat_Slash_Hat _0_600 _0_599))))
end
| FStar_Parser_AST.If (e1, e2, e3) -> begin
(

let uu____2087 = (is_unit e3)
in (match (uu____2087) with
| true -> begin
(FStar_Pprint.group (let _0_606 = (let _0_602 = (str "if")
in (let _0_601 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat _0_602 _0_601)))
in (let _0_605 = (let _0_604 = (str "then")
in (let _0_603 = (p_noSeqTerm e2)
in (op_Hat_Slash_Plus_Hat _0_604 _0_603)))
in (FStar_Pprint.op_Hat_Slash_Hat _0_606 _0_605))))
end
| uu____2088 -> begin
(

let e2_doc = (

let uu____2090 = (unparen e2).FStar_Parser_AST.tm
in (match (uu____2090) with
| FStar_Parser_AST.If (uu____2091, uu____2092, e3) when (is_unit e3) -> begin
(soft_parens_with_nesting (p_noSeqTerm e2))
end
| uu____2094 -> begin
(p_noSeqTerm e2)
end))
in (FStar_Pprint.group (let _0_615 = (let _0_608 = (str "if")
in (let _0_607 = (p_noSeqTerm e1)
in (op_Hat_Slash_Plus_Hat _0_608 _0_607)))
in (let _0_614 = (let _0_613 = (let _0_609 = (str "then")
in (op_Hat_Slash_Plus_Hat _0_609 e2_doc))
in (let _0_612 = (let _0_611 = (str "else")
in (let _0_610 = (p_noSeqTerm e3)
in (op_Hat_Slash_Plus_Hat _0_611 _0_610)))
in (FStar_Pprint.op_Hat_Slash_Hat _0_613 _0_612)))
in (FStar_Pprint.op_Hat_Slash_Hat _0_615 _0_614)))))
end))
end
| FStar_Parser_AST.TryWith (e, branches) -> begin
(FStar_Pprint.group (let _0_621 = (let _0_617 = (str "try")
in (let _0_616 = (p_noSeqTerm e)
in (prefix2 _0_617 _0_616)))
in (let _0_620 = (let _0_619 = (str "with")
in (let _0_618 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat _0_619 _0_618)))
in (FStar_Pprint.op_Hat_Slash_Hat _0_621 _0_620))))
end
| FStar_Parser_AST.Match (e, branches) -> begin
(FStar_Pprint.group (let _0_626 = (let _0_624 = (str "match")
in (let _0_623 = (p_noSeqTerm e)
in (let _0_622 = (str "with")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _0_624 _0_623 _0_622))))
in (let _0_625 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat _0_626 _0_625))))
end
| FStar_Parser_AST.LetOpen (uid, e) -> begin
(FStar_Pprint.group (let _0_631 = (let _0_629 = (str "let open")
in (let _0_628 = (p_quident uid)
in (let _0_627 = (str "in")
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _0_629 _0_628 _0_627))))
in (let _0_630 = (p_term e)
in (FStar_Pprint.op_Hat_Slash_Hat _0_631 _0_630))))
end
| FStar_Parser_AST.Let (q, lbs, e) -> begin
(

let let_doc = (let _0_633 = (str "let")
in (let _0_632 = (p_letqualifier q)
in (FStar_Pprint.op_Hat_Hat _0_633 _0_632)))
in (let _0_638 = (FStar_Pprint.group (let _0_636 = (let _0_634 = (str "and")
in (precede_break_separate_map let_doc _0_634 p_letbinding lbs))
in (let _0_635 = (str "in")
in (FStar_Pprint.op_Hat_Slash_Hat _0_636 _0_635))))
in (let _0_637 = (p_term e)
in (FStar_Pprint.op_Hat_Slash_Hat _0_638 _0_637))))
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, typ_opt); FStar_Parser_AST.prange = uu____2143})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, branches); FStar_Parser_AST.range = uu____2146; FStar_Parser_AST.level = uu____2147}) when (matches_var maybe_x x) -> begin
(FStar_Pprint.group (let _0_640 = (str "function")
in (let _0_639 = (FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch branches)
in (FStar_Pprint.op_Hat_Slash_Hat _0_640 _0_639))))
end
| FStar_Parser_AST.Assign (id, e) -> begin
(FStar_Pprint.group (let _0_643 = (p_lident id)
in (let _0_642 = (let _0_641 = (p_noSeqTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow _0_641))
in (FStar_Pprint.op_Hat_Slash_Hat _0_643 _0_642))))
end
| uu____2167 -> begin
(p_typ e)
end)))
and p_typ : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (with_comment p_typ' e e.FStar_Parser_AST.range))
and p_typ' : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2170 = (unparen e).FStar_Parser_AST.tm
in (match (uu____2170) with
| (FStar_Parser_AST.QForall (bs, trigger, e1)) | (FStar_Parser_AST.QExists (bs, trigger, e1)) -> begin
(let _0_650 = (let _0_646 = (let _0_644 = (p_quantifier e)
in (FStar_Pprint.op_Hat_Hat _0_644 FStar_Pprint.space))
in (let _0_645 = (p_binders true bs)
in (FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0") _0_646 _0_645 FStar_Pprint.dot)))
in (let _0_649 = (let _0_648 = (p_trigger trigger)
in (let _0_647 = (p_noSeqTerm e1)
in (FStar_Pprint.op_Hat_Hat _0_648 _0_647)))
in (prefix2 _0_650 _0_649)))
end
| uu____2186 -> begin
(p_simpleTerm e)
end)))
and p_quantifier : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2188 = (unparen e).FStar_Parser_AST.tm
in (match (uu____2188) with
| FStar_Parser_AST.QForall (uu____2189) -> begin
(str "forall")
end
| FStar_Parser_AST.QExists (uu____2196) -> begin
(str "exists")
end
| uu____2203 -> begin
(failwith "Imposible : p_quantifier called on a non-quantifier term")
end)))
and p_trigger : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun uu___125_2204 -> (match (uu___125_2204) with
| [] -> begin
FStar_Pprint.empty
end
| pats -> begin
(let _0_656 = (let _0_655 = (let _0_654 = (str "pattern")
in (let _0_653 = (let _0_652 = (jump2 (p_disjunctivePats pats))
in (let _0_651 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1)
in (FStar_Pprint.op_Hat_Slash_Hat _0_652 _0_651)))
in (FStar_Pprint.op_Hat_Slash_Hat _0_654 _0_653)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _0_655))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace _0_656))
end))
and p_disjunctivePats : FStar_Parser_AST.term Prims.list Prims.list  ->  FStar_Pprint.document = (fun pats -> (let _0_657 = (str "\\/")
in (FStar_Pprint.separate_map _0_657 p_conjunctivePats pats)))
and p_conjunctivePats : FStar_Parser_AST.term Prims.list  ->  FStar_Pprint.document = (fun pats -> (FStar_Pprint.group (FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats)))
and p_simpleTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2218 = (unparen e).FStar_Parser_AST.tm
in (match (uu____2218) with
| FStar_Parser_AST.Abs (pats, e) -> begin
(let _0_662 = (let _0_660 = (str "fun")
in (let _0_659 = (let _0_658 = (FStar_Pprint.separate_map break1 p_atomicPattern pats)
in (FStar_Pprint.op_Hat_Slash_Hat _0_658 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat _0_660 _0_659)))
in (let _0_661 = (p_term e)
in (op_Hat_Slash_Plus_Hat _0_662 _0_661)))
end
| uu____2223 -> begin
(p_tmIff e)
end)))
and p_maybeFocusArrow : Prims.bool  ->  FStar_Pprint.document = (fun b -> (match (b) with
| true -> begin
(str "~>")
end
| uu____2225 -> begin
FStar_Pprint.rarrow
end))
and p_patternBranch : (FStar_Parser_AST.pattern * FStar_Parser_AST.term Prims.option * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun uu____2226 -> (match (uu____2226) with
| (pat, when_opt, e) -> begin
(

let maybe_paren = (

let uu____2239 = (unparen e).FStar_Parser_AST.tm
in (match (uu____2239) with
| (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) -> begin
soft_begin_end_with_nesting
end
| FStar_Parser_AST.Abs (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____2245); FStar_Parser_AST.prange = uu____2246})::[], {FStar_Parser_AST.tm = FStar_Parser_AST.Match (maybe_x, uu____2248); FStar_Parser_AST.range = uu____2249; FStar_Parser_AST.level = uu____2250}) when (matches_var maybe_x x) -> begin
soft_begin_end_with_nesting
end
| uu____2264 -> begin
(fun x -> x)
end))
in (FStar_Pprint.group (let _0_669 = (FStar_Pprint.group (let _0_667 = (let _0_666 = (let _0_665 = (p_disjunctivePattern pat)
in (let _0_664 = (let _0_663 = (p_maybeWhen when_opt)
in (FStar_Pprint.op_Hat_Hat _0_663 FStar_Pprint.rarrow))
in (op_Hat_Slash_Plus_Hat _0_665 _0_664)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_666))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar _0_667)))
in (let _0_668 = (maybe_paren (p_term e))
in (op_Hat_Slash_Plus_Hat _0_669 _0_668)))))
end))
and p_maybeWhen : FStar_Parser_AST.term Prims.option  ->  FStar_Pprint.document = (fun uu___126_2266 -> (match (uu___126_2266) with
| None -> begin
FStar_Pprint.empty
end
| Some (e) -> begin
(let _0_672 = (str "when")
in (let _0_671 = (let _0_670 = (p_tmFormula e)
in (FStar_Pprint.op_Hat_Hat _0_670 FStar_Pprint.space))
in (op_Hat_Slash_Plus_Hat _0_672 _0_671)))
end))
and p_tmIff : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2270 = (unparen e).FStar_Parser_AST.tm
in (match (uu____2270) with
| FStar_Parser_AST.Op ("<==>", (e1)::(e2)::[]) -> begin
(let _0_675 = (str "<==>")
in (let _0_674 = (p_tmImplies e1)
in (let _0_673 = (p_tmIff e2)
in (infix0 _0_675 _0_674 _0_673))))
end
| uu____2274 -> begin
(p_tmImplies e)
end)))
and p_tmImplies : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2276 = (unparen e).FStar_Parser_AST.tm
in (match (uu____2276) with
| FStar_Parser_AST.Op ("==>", (e1)::(e2)::[]) -> begin
(let _0_678 = (str "==>")
in (let _0_677 = (p_tmArrow p_tmFormula e1)
in (let _0_676 = (p_tmImplies e2)
in (infix0 _0_678 _0_677 _0_676))))
end
| uu____2280 -> begin
(p_tmArrow p_tmFormula e)
end)))
and p_tmArrow : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun p_Tm e -> (

let uu____2285 = (unparen e).FStar_Parser_AST.tm
in (match (uu____2285) with
| FStar_Parser_AST.Product (bs, tgt) -> begin
(FStar_Pprint.group (let _0_683 = (FStar_Pprint.concat_map (fun b -> (let _0_681 = (p_binder false b)
in (let _0_680 = (let _0_679 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_679))
in (FStar_Pprint.op_Hat_Hat _0_681 _0_680)))) bs)
in (let _0_682 = (p_tmArrow p_Tm tgt)
in (FStar_Pprint.op_Hat_Hat _0_683 _0_682))))
end
| uu____2291 -> begin
(p_Tm e)
end)))
and p_tmFormula : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2293 = (unparen e).FStar_Parser_AST.tm
in (match (uu____2293) with
| FStar_Parser_AST.Op ("\\/", (e1)::(e2)::[]) -> begin
(let _0_686 = (str "\\/")
in (let _0_685 = (p_tmFormula e1)
in (let _0_684 = (p_tmConjunction e2)
in (infix0 _0_686 _0_685 _0_684))))
end
| uu____2297 -> begin
(p_tmConjunction e)
end)))
and p_tmConjunction : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2299 = (unparen e).FStar_Parser_AST.tm
in (match (uu____2299) with
| FStar_Parser_AST.Op ("/\\", (e1)::(e2)::[]) -> begin
(let _0_689 = (str "/\\")
in (let _0_688 = (p_tmConjunction e1)
in (let _0_687 = (p_tmTuple e2)
in (infix0 _0_689 _0_688 _0_687))))
end
| uu____2303 -> begin
(p_tmTuple e)
end)))
and p_tmTuple : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2305 = (unparen e).FStar_Parser_AST.tm
in (match (uu____2305) with
| FStar_Parser_AST.Construct (lid, args) when (is_tuple_constructor lid) -> begin
(let _0_690 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (FStar_Pprint.separate_map _0_690 (fun uu____2316 -> (match (uu____2316) with
| (e, uu____2320) -> begin
(p_tmEq e)
end)) args))
end
| uu____2321 -> begin
(p_tmEq e)
end)))
and paren_if : Prims.int  ->  Prims.int  ->  FStar_Pprint.document  ->  FStar_Pprint.document = (fun curr mine doc -> (match ((mine <= curr)) with
| true -> begin
doc
end
| uu____2325 -> begin
(FStar_Pprint.group (let _0_691 = (FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _0_691)))
end))
and p_tmEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n = (max_level (FStar_List.append (((colon_equals ()))::((pipe_right ()))::[]) (operatorInfix0ad12 ())))
in (p_tmEq' n e)))
and p_tmEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (

let uu____2350 = (unparen e).FStar_Parser_AST.tm
in (match (uu____2350) with
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (((is_operatorInfix0ad12 op) || (op = "=")) || (op = "|>")) -> begin
(

let uu____2355 = (levels op)
in (match (uu____2355) with
| (left, mine, right) -> begin
(let _0_695 = (let _0_694 = (str op)
in (let _0_693 = (p_tmEq' left e1)
in (let _0_692 = (p_tmEq' right e2)
in (infix0 _0_694 _0_693 _0_692))))
in (paren_if curr mine _0_695))
end))
end
| FStar_Parser_AST.Op (":=", (e1)::(e2)::[]) -> begin
(FStar_Pprint.group (let _0_700 = (p_tmEq e1)
in (let _0_699 = (let _0_698 = (let _0_697 = (let _0_696 = (p_tmEq e2)
in (op_Hat_Slash_Plus_Hat FStar_Pprint.equals _0_696))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.colon _0_697))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_698))
in (FStar_Pprint.op_Hat_Hat _0_700 _0_699))))
end
| uu____2365 -> begin
(p_tmNoEq e)
end)))
and p_tmNoEq : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let n = (max_level (((colon_colon ()))::((amp ()))::((opinfix3 ()))::((opinfix4 ()))::[]))
in (p_tmNoEq' n e)))
and p_tmNoEq' : Prims.int  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun curr e -> (

let uu____2395 = (unparen e).FStar_Parser_AST.tm
in (match (uu____2395) with
| FStar_Parser_AST.Construct (lid, ((e1, uu____2398))::((e2, uu____2400))::[]) when ((FStar_Ident.lid_equals lid FStar_Syntax_Const.cons_lid) && (not ((is_list e)))) -> begin
(

let op = "::"
in (

let uu____2411 = (levels op)
in (match (uu____2411) with
| (left, mine, right) -> begin
(let _0_704 = (let _0_703 = (str op)
in (let _0_702 = (p_tmNoEq' left e1)
in (let _0_701 = (p_tmNoEq' right e2)
in (infix0 _0_703 _0_702 _0_701))))
in (paren_if curr mine _0_704))
end)))
end
| FStar_Parser_AST.Sum (binders, res) -> begin
(

let op = "&"
in (

let uu____2423 = (levels op)
in (match (uu____2423) with
| (left, mine, right) -> begin
(

let p_dsumfst = (fun b -> (let _0_708 = (p_binder false b)
in (let _0_707 = (let _0_706 = (let _0_705 = (str "&")
in (FStar_Pprint.op_Hat_Hat _0_705 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_706))
in (FStar_Pprint.op_Hat_Hat _0_708 _0_707))))
in (let _0_711 = (let _0_710 = (FStar_Pprint.concat_map p_dsumfst binders)
in (let _0_709 = (p_tmNoEq' right res)
in (FStar_Pprint.op_Hat_Hat _0_710 _0_709)))
in (paren_if curr mine _0_711)))
end)))
end
| FStar_Parser_AST.Op (op, (e1)::(e2)::[]) when (is_operatorInfix34 op) -> begin
(

let uu____2438 = (levels op)
in (match (uu____2438) with
| (left, mine, right) -> begin
(let _0_715 = (let _0_714 = (str op)
in (let _0_713 = (p_tmNoEq' left e1)
in (let _0_712 = (p_tmNoEq' right e2)
in (infix0 _0_714 _0_713 _0_712))))
in (paren_if curr mine _0_715))
end))
end
| FStar_Parser_AST.Op ("-", (e)::[]) -> begin
(

let uu____2447 = (levels "-")
in (match (uu____2447) with
| (left, mine, right) -> begin
(let _0_716 = (p_tmNoEq' mine e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus _0_716))
end))
end
| FStar_Parser_AST.NamedTyp (lid, e) -> begin
(FStar_Pprint.group (let _0_719 = (p_lidentOrUnderscore lid)
in (let _0_718 = (let _0_717 = (p_appTerm e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon _0_717))
in (FStar_Pprint.op_Hat_Slash_Hat _0_719 _0_718))))
end
| FStar_Parser_AST.Refine (b, phi) -> begin
(p_refinedBinder b phi)
end
| FStar_Parser_AST.Record (with_opt, record_fields) -> begin
(braces_with_nesting (let _0_722 = (default_or_map FStar_Pprint.empty p_with_clause with_opt)
in (let _0_721 = (let _0_720 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (FStar_Pprint.separate_map _0_720 p_simpleDef record_fields))
in (FStar_Pprint.op_Hat_Hat _0_722 _0_721))))
end
| FStar_Parser_AST.Op ("~", (e)::[]) -> begin
(FStar_Pprint.group (let _0_724 = (str "~")
in (let _0_723 = (p_atomicTerm e)
in (FStar_Pprint.op_Hat_Hat _0_724 _0_723))))
end
| uu____2472 -> begin
(p_appTerm e)
end)))
and p_with_clause : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (let _0_728 = (p_appTerm e)
in (let _0_727 = (let _0_726 = (let _0_725 = (str "with")
in (FStar_Pprint.op_Hat_Hat _0_725 break1))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_726))
in (FStar_Pprint.op_Hat_Hat _0_728 _0_727))))
and p_refinedBinder : FStar_Parser_AST.binder  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun b phi -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (lid, t) -> begin
(soft_parens_with_nesting (let _0_729 = (p_lident lid)
in (p_refinement b.FStar_Parser_AST.aqual _0_729 t phi)))
end
| FStar_Parser_AST.TAnnotated (uu____2478) -> begin
(failwith "Is this still used ?")
end
| (FStar_Parser_AST.Variable (_)) | (FStar_Parser_AST.TVariable (_)) | (FStar_Parser_AST.NoName (_)) -> begin
(failwith (let _0_730 = (FStar_Parser_AST.binder_to_string b)
in (FStar_Util.format1 "Imposible : a refined binder ought to be annotated %s" _0_730)))
end))
and p_simpleDef : (FStar_Ident.lid * FStar_Parser_AST.term)  ->  FStar_Pprint.document = (fun uu____2484 -> (match (uu____2484) with
| (lid, e) -> begin
(FStar_Pprint.group (let _0_733 = (p_qlident lid)
in (let _0_732 = (let _0_731 = (p_tmIff e)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals _0_731))
in (FStar_Pprint.op_Hat_Slash_Hat _0_733 _0_732))))
end))
and p_appTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2490 = (unparen e).FStar_Parser_AST.tm
in (match (uu____2490) with
| FStar_Parser_AST.App (uu____2491) when (is_general_application e) -> begin
(

let uu____2495 = (head_and_args e)
in (match (uu____2495) with
| (head, args) -> begin
(let _0_735 = (p_indexingTerm head)
in (let _0_734 = (FStar_Pprint.separate_map FStar_Pprint.space p_argTerm args)
in (op_Hat_Slash_Plus_Hat _0_735 _0_734)))
end))
end
| FStar_Parser_AST.Construct (lid, args) when ((is_general_construction e) && (not ((is_dtuple_constructor lid)))) -> begin
(match (args) with
| [] -> begin
(p_quident lid)
end
| (arg)::[] -> begin
(FStar_Pprint.group (let _0_737 = (p_quident lid)
in (let _0_736 = (p_argTerm arg)
in (FStar_Pprint.op_Hat_Slash_Hat _0_737 _0_736))))
end
| (hd)::tl -> begin
(FStar_Pprint.group (let _0_741 = (FStar_Pprint.group (let _0_739 = (p_quident lid)
in (let _0_738 = (p_argTerm hd)
in (FStar_Pprint.op_Hat_Slash_Hat _0_739 _0_738))))
in (let _0_740 = (jump2 (FStar_Pprint.separate_map break1 p_argTerm tl))
in (FStar_Pprint.op_Hat_Hat _0_741 _0_740))))
end)
end
| uu____2539 -> begin
(p_indexingTerm e)
end)))
and p_argTerm : (FStar_Parser_AST.term * FStar_Parser_AST.imp)  ->  FStar_Pprint.document = (fun arg_imp -> (match (arg_imp) with
| ({FStar_Parser_AST.tm = FStar_Parser_AST.Uvar (uu____2543); FStar_Parser_AST.range = uu____2544; FStar_Parser_AST.level = uu____2545}, FStar_Parser_AST.UnivApp) -> begin
(p_univar (Prims.fst arg_imp))
end
| (u, FStar_Parser_AST.UnivApp) -> begin
(p_universe u)
end
| (e, FStar_Parser_AST.FsTypApp) -> begin
(let _0_742 = (p_indexingTerm e)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") FStar_Pprint.langle _0_742 FStar_Pprint.rangle))
end
| (e, FStar_Parser_AST.Hash) -> begin
(let _0_744 = (str "#")
in (let _0_743 = (p_indexingTerm e)
in (FStar_Pprint.op_Hat_Hat _0_744 _0_743)))
end
| (e, FStar_Parser_AST.Nothing) -> begin
(p_indexingTerm e)
end))
and p_indexingTerm_aux : (FStar_Parser_AST.term  ->  FStar_Pprint.document)  ->  FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun exit e -> (

let uu____2554 = (unparen e).FStar_Parser_AST.tm
in (match (uu____2554) with
| FStar_Parser_AST.Op (".()", (e1)::(e2)::[]) -> begin
(FStar_Pprint.group (let _0_747 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (let _0_746 = (let _0_745 = (soft_parens_with_nesting (p_term e2))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _0_745))
in (FStar_Pprint.op_Hat_Hat _0_747 _0_746))))
end
| FStar_Parser_AST.Op (".[]", (e1)::(e2)::[]) -> begin
(FStar_Pprint.group (let _0_750 = (p_indexingTerm_aux p_atomicTermNotQUident e1)
in (let _0_749 = (let _0_748 = (soft_brackets_with_nesting (p_term e2))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _0_748))
in (FStar_Pprint.op_Hat_Hat _0_750 _0_749))))
end
| uu____2561 -> begin
(exit e)
end)))
and p_indexingTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_indexingTerm_aux p_atomicTerm e))
and p_atomicTerm : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2564 = (unparen e).FStar_Parser_AST.tm
in (match (uu____2564) with
| FStar_Parser_AST.LetOpen (lid, e) -> begin
(let _0_753 = (p_quident lid)
in (let _0_752 = (let _0_751 = (soft_parens_with_nesting (p_term e))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _0_751))
in (FStar_Pprint.op_Hat_Hat _0_753 _0_752)))
end
| FStar_Parser_AST.Name (lid) -> begin
(p_quident lid)
end
| FStar_Parser_AST.Op (op, (e)::[]) when (is_general_prefix_op op) -> begin
(let _0_755 = (str op)
in (let _0_754 = (p_atomicTerm e)
in (FStar_Pprint.op_Hat_Hat _0_755 _0_754)))
end
| uu____2571 -> begin
(p_atomicTermNotQUident e)
end)))
and p_atomicTermNotQUident : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2573 = (unparen e).FStar_Parser_AST.tm
in (match (uu____2573) with
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
(let _0_757 = (str op)
in (let _0_756 = (p_atomicTermNotQUident e)
in (FStar_Pprint.op_Hat_Hat _0_757 _0_756)))
end
| FStar_Parser_AST.Op (op, []) -> begin
(let _0_761 = (let _0_760 = (let _0_759 = (str op)
in (let _0_758 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen)
in (FStar_Pprint.op_Hat_Hat _0_759 _0_758)))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.space _0_760))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen _0_761))
end
| FStar_Parser_AST.Construct (lid, args) when (is_dtuple_constructor lid) -> begin
(let _0_766 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar)
in (let _0_765 = (let _0_763 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (let _0_762 = (FStar_List.map Prims.fst args)
in (FStar_Pprint.separate_map _0_763 p_tmEq _0_762)))
in (let _0_764 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _0_766 _0_765 _0_764))))
end
| FStar_Parser_AST.Project (e, lid) -> begin
(FStar_Pprint.group (let _0_769 = (p_atomicTermNotQUident e)
in (let _0_768 = (let _0_767 = (p_qlident lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _0_767))
in (FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0") _0_769 _0_768))))
end
| uu____2596 -> begin
(p_projectionLHS e)
end)))
and p_projectionLHS : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (

let uu____2598 = (unparen e).FStar_Parser_AST.tm
in (match (uu____2598) with
| FStar_Parser_AST.Var (lid) -> begin
(p_qlident lid)
end
| FStar_Parser_AST.Projector (constr_lid, field_lid) -> begin
(let _0_773 = (p_quident constr_lid)
in (let _0_772 = (let _0_771 = (let _0_770 = (p_lident field_lid)
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _0_770))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark _0_771))
in (FStar_Pprint.op_Hat_Hat _0_773 _0_772)))
end
| FStar_Parser_AST.Discrim (constr_lid) -> begin
(let _0_774 = (p_quident constr_lid)
in (FStar_Pprint.op_Hat_Hat _0_774 FStar_Pprint.qmark))
end
| FStar_Parser_AST.Paren (e) -> begin
(soft_parens_with_nesting (p_term e))
end
| uu____2604 when (is_array e) -> begin
(

let es = (extract_from_list e)
in (let _0_778 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar)
in (let _0_777 = (let _0_775 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (separate_map_or_flow _0_775 p_noSeqTerm es))
in (let _0_776 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket)
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") _0_778 _0_777 _0_776)))))
end
| uu____2607 when (is_list e) -> begin
(let _0_781 = (let _0_780 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (let _0_779 = (extract_from_list e)
in (separate_map_or_flow _0_780 p_noSeqTerm _0_779)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") FStar_Pprint.lbracket _0_781 FStar_Pprint.rbracket))
end
| uu____2608 when (is_lex_list e) -> begin
(let _0_785 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket)
in (let _0_784 = (let _0_783 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1)
in (let _0_782 = (extract_from_list e)
in (separate_map_or_flow _0_783 p_noSeqTerm _0_782)))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1") _0_785 _0_784 FStar_Pprint.rbracket)))
end
| uu____2609 when (is_ref_set e) -> begin
(

let es = (extract_from_ref_set e)
in (let _0_788 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace)
in (let _0_787 = (let _0_786 = (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1)
in (separate_map_or_flow _0_786 p_appTerm es))
in (FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0") _0_788 _0_787 FStar_Pprint.rbrace))))
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Op (_)) | (FStar_Parser_AST.Tvar (_)) | (FStar_Parser_AST.Uvar (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) | (FStar_Parser_AST.Construct (_)) | (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.App (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.LetOpen (_)) | (FStar_Parser_AST.Seq (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Ascribed (_)) | (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Project (_)) | (FStar_Parser_AST.Product (_)) | (FStar_Parser_AST.Sum (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Refine (_)) | (FStar_Parser_AST.NamedTyp (_)) | (FStar_Parser_AST.Requires (_)) | (FStar_Parser_AST.Ensures (_)) | (FStar_Parser_AST.Assign (_)) | (FStar_Parser_AST.Attributes (_)) -> begin
(soft_parens_with_nesting (p_term e))
end
| FStar_Parser_AST.Labeled (uu____2640) -> begin
(failwith "Not valid in universe")
end)))
and p_constant : FStar_Const.sconst  ->  FStar_Pprint.document = (fun uu___129_2644 -> (match (uu___129_2644) with
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
(FStar_Pprint.squotes (FStar_Pprint.doc_of_char x))
end
| FStar_Const.Const_string (bytes, uu____2649) -> begin
(FStar_Pprint.dquotes (str (FStar_Util.string_of_bytes bytes)))
end
| FStar_Const.Const_bytearray (bytes, uu____2653) -> begin
(let _0_790 = (FStar_Pprint.dquotes (str (FStar_Util.string_of_bytes bytes)))
in (let _0_789 = (str "B")
in (FStar_Pprint.op_Hat_Hat _0_790 _0_789)))
end
| FStar_Const.Const_int (repr, sign_width_opt) -> begin
(

let signedness = (fun uu___127_2667 -> (match (uu___127_2667) with
| FStar_Const.Unsigned -> begin
(str "u")
end
| FStar_Const.Signed -> begin
FStar_Pprint.empty
end))
in (

let width = (fun uu___128_2671 -> (match (uu___128_2671) with
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

let ending = (default_or_map FStar_Pprint.empty (fun uu____2675 -> (match (uu____2675) with
| (s, w) -> begin
(let _0_792 = (signedness s)
in (let _0_791 = (width w)
in (FStar_Pprint.op_Hat_Hat _0_792 _0_791)))
end)) sign_width_opt)
in (let _0_793 = (str repr)
in (FStar_Pprint.op_Hat_Hat _0_793 ending)))))
end
| FStar_Const.Const_range (r) -> begin
(str (FStar_Range.string_of_range r))
end
| FStar_Const.Const_reify -> begin
(str "reify")
end
| FStar_Const.Const_reflect (lid) -> begin
(let _0_797 = (p_quident lid)
in (let _0_796 = (let _0_795 = (let _0_794 = (str "reflect")
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot _0_794))
in (FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark _0_795))
in (FStar_Pprint.op_Hat_Hat _0_797 _0_796)))
end))
and p_universe : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (let _0_799 = (str "u#")
in (let _0_798 = (p_atomicUniverse u)
in (FStar_Pprint.op_Hat_Hat _0_799 _0_798))))
and p_universeFrom : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (

let uu____2684 = (unparen u).FStar_Parser_AST.tm
in (match (uu____2684) with
| FStar_Parser_AST.Op ("+", (u1)::(u2)::[]) -> begin
(FStar_Pprint.group (let _0_802 = (p_universeFrom u1)
in (let _0_801 = (let _0_800 = (p_universeFrom u2)
in (FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus _0_800))
in (FStar_Pprint.op_Hat_Slash_Hat _0_802 _0_801))))
end
| FStar_Parser_AST.App (uu____2688) -> begin
(

let uu____2692 = (head_and_args u)
in (match (uu____2692) with
| (head, args) -> begin
(

let uu____2706 = (unparen head).FStar_Parser_AST.tm
in (match (uu____2706) with
| FStar_Parser_AST.Var (maybe_max_lid) when (FStar_Ident.lid_equals maybe_max_lid FStar_Syntax_Const.max_lid) -> begin
(FStar_Pprint.group (let _0_804 = (p_qlident FStar_Syntax_Const.max_lid)
in (let _0_803 = (FStar_Pprint.separate_map FStar_Pprint.space (fun uu____2710 -> (match (uu____2710) with
| (u, uu____2714) -> begin
(p_atomicUniverse u)
end)) args)
in (op_Hat_Slash_Plus_Hat _0_804 _0_803))))
end
| uu____2715 -> begin
(failwith (let _0_805 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" _0_805)))
end))
end))
end
| uu____2716 -> begin
(p_atomicUniverse u)
end)))
and p_atomicUniverse : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (

let uu____2718 = (unparen u).FStar_Parser_AST.tm
in (match (uu____2718) with
| FStar_Parser_AST.Wild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (r, sw)) -> begin
(p_constant (FStar_Const.Const_int (((r), (sw)))))
end
| FStar_Parser_AST.Uvar (uu____2730) -> begin
(p_univar u)
end
| FStar_Parser_AST.Paren (u) -> begin
(soft_parens_with_nesting (p_universeFrom u))
end
| (FStar_Parser_AST.Op ("+", (_)::(_)::[])) | (FStar_Parser_AST.App (_)) -> begin
(soft_parens_with_nesting (p_universeFrom u))
end
| uu____2736 -> begin
(failwith (let _0_806 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Invalid term in universe context %s" _0_806)))
end)))
and p_univar : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun u -> (

let uu____2738 = (unparen u).FStar_Parser_AST.tm
in (match (uu____2738) with
| FStar_Parser_AST.Uvar (id) -> begin
(str (FStar_Ident.text_of_id id))
end
| uu____2740 -> begin
(failwith (let _0_807 = (FStar_Parser_AST.term_to_string u)
in (FStar_Util.format1 "Not a universe variable %s" _0_807)))
end)))


let term_to_document : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun e -> (p_term e))


let decl_to_document : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun e -> (p_decl e))


let modul_to_document : FStar_Parser_AST.modul  ->  FStar_Pprint.document = (fun m -> (match (m) with
| (FStar_Parser_AST.Module (_, decls)) | (FStar_Parser_AST.Interface (_, decls, _)) -> begin
(let _0_808 = (FStar_All.pipe_right decls (FStar_List.map decl_to_document))
in (FStar_All.pipe_right _0_808 (FStar_Pprint.separate FStar_Pprint.hardline)))
end))


let comments_to_document : (Prims.string * FStar_Range.range) Prims.list  ->  FStar_Pprint.document = (fun comments -> (FStar_Pprint.separate_map FStar_Pprint.hardline (fun uu____2772 -> (match (uu____2772) with
| (comment, range) -> begin
(str comment)
end)) comments))


let modul_with_comments_to_document : FStar_Parser_AST.modul  ->  (Prims.string * FStar_Range.range) Prims.list  ->  (FStar_Pprint.document * (Prims.string * FStar_Range.range) Prims.list) = (fun m comments -> (

let rec aux = (fun uu____2811 decl -> (match (uu____2811) with
| (previous_range_end, comments, doc) -> begin
(

let current_range = (FStar_Range.extend_to_end_of_line decl.FStar_Parser_AST.drange)
in (

let max = (fun x y -> (match ((x < y)) with
| true -> begin
y
end
| uu____2842 -> begin
x
end))
in (

let rec process_preceding_comments = (fun doc last_line end_pos n uu___130_2866 -> (match (uu___130_2866) with
| ((comment, range))::comments when (let _0_809 = (FStar_Range.start_of_range range)
in (FStar_Range.pos_geq end_pos _0_809)) -> begin
(

let l = (let _0_811 = (let _0_810 = (FStar_Range.line_of_pos (FStar_Range.start_of_range range))
in (_0_810 - last_line))
in (max (Prims.parse_int "1") _0_811))
in (

let doc = (let _0_814 = (let _0_813 = (FStar_Pprint.repeat l FStar_Pprint.hardline)
in (let _0_812 = (str comment)
in (FStar_Pprint.op_Hat_Hat _0_813 _0_812)))
in (FStar_Pprint.op_Hat_Hat doc _0_814))
in (let _0_815 = (FStar_Range.line_of_pos (FStar_Range.end_of_range range))
in (process_preceding_comments doc _0_815 end_pos (Prims.parse_int "1") comments))))
end
| comments -> begin
(

let l = (let _0_817 = (let _0_816 = (FStar_Range.line_of_pos end_pos)
in (_0_816 - last_line))
in (max n _0_817))
in (let _0_819 = (let _0_818 = (FStar_Pprint.repeat l FStar_Pprint.hardline)
in (FStar_Pprint.op_Hat_Hat doc _0_818))
in ((_0_819), (comments))))
end))
in (

let uu____2893 = (let _0_821 = (FStar_Range.line_of_pos previous_range_end)
in (let _0_820 = (FStar_Range.end_of_line (FStar_Range.start_of_range current_range))
in (process_preceding_comments doc _0_821 _0_820 (Prims.parse_int "0") comments)))
in (match (uu____2893) with
| (doc, comments) -> begin
(

let uu____2913 = (FStar_Util.take (fun uu___131_2924 -> (match (uu___131_2924) with
| (uu____2927, range) -> begin
(FStar_Range.range_contains_range current_range range)
end)) comments)
in (match (uu____2913) with
| (inner_comments, comments) -> begin
((FStar_ST.write comment_stack inner_comments);
(

let doc = (let _0_822 = (decl_to_document decl)
in (FStar_Pprint.op_Hat_Hat doc _0_822))
in (

let inner_comments_doc = (

let uu____2957 = (let _0_823 = (FStar_ST.read comment_stack)
in (_0_823 = []))
in (match (uu____2957) with
| true -> begin
FStar_Pprint.empty
end
| uu____2968 -> begin
((let _0_826 = (let _0_825 = (let _0_824 = (FStar_ST.read comment_stack)
in (FStar_List.map Prims.fst _0_824))
in (FStar_String.concat " ; " _0_825))
in (FStar_Util.print1_warning "Leftover comments : %s\n" _0_826));
(comments_to_document (FStar_ST.read comment_stack));
)
end))
in (let _0_828 = (FStar_Range.end_of_range decl.FStar_Parser_AST.drange)
in (let _0_827 = (FStar_Pprint.op_Hat_Hat doc inner_comments_doc)
in ((_0_828), (comments), (_0_827))))));
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
| (d)::uu____3005 -> begin
(

let uu____3007 = (FStar_List.fold_left aux ((FStar_Range.zeroPos), (comments), (FStar_Pprint.empty)) decls)
in (match (uu____3007) with
| (uu____3028, comments, doc) -> begin
((doc), (comments))
end))
end))))




